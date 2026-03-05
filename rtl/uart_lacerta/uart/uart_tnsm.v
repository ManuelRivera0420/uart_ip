//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_tnsm
//
// Description:
// this module is a state machine to drive the serial output data through tx
//////////////////////////////////////////////////////////////////////////////////

module uart_tnsm(
	input wire clk,
	input wire arst_n,
	input wire active,
	input wire tnsm,
	input wire [7:0] data,
	input wire [1:0] frame_type,  // 2'b00 : 5 bits, 2'b01 : 6 bits, 2'b10 : 7 bits, 2'b11 : 8 bits
	input wire [1:0] parity_type, // 2'b00 : no parity, 2'b01: even parity, 2'b10: odd parity, 2'b11: no parity
	input wire stop_type,         // 1'b0 : 1 stop bit, 1'b1 : 2 stop bits
	input wire tnsm_clk_en,
	output wire busy,
	output reg tnsm_clr,
	output reg tx
);

// state machine states parameters
localparam STATE_TNSM_IDLE = 3'b000;
localparam STATE_TNSM_DATA = 3'b001;
localparam STATE_TNSM_PARITY = 3'b010;
localparam STATE_TNSM_STOP1 = 3'b011;
localparam STATE_TNSM_STOP2 = 3'b100;

// internal variables
reg [3:0] bitcnt;
reg [7:0] data_r;
reg [3:0] frame_size;
reg parity;
reg [2:0] curr_state;

// UART frame size - this only consider data
always@(*) begin
    case(frame_type)
        2'b00 : frame_size = 5;
        2'b01 : frame_size = 6;
        2'b10 : frame_size = 7;
        2'b11 : frame_size = 8;
    endcase
end

always@(posedge clk, negedge arst_n) begin
	if(!arst_n) begin
		tx <= 1'b1; // tx is 1 at reset
		bitcnt <= 4'd0;
		tnsm_clr <= 1'b0;
		data_r <= 8'd0;
		parity <= 1'b0;
		curr_state <= STATE_TNSM_IDLE;
	end	else begin
		tnsm_clr <= 1'b0; // transmission flag clearing signal is a pulse
		case(curr_state)
		    
		STATE_TNSM_IDLE: begin
			tx <= 1'b1;
			if(tnsm && active && tnsm_clk_en) begin // if uart ip is active, transmission flag is asserted, and clock generator asserts synchronization flag
				parity <= 1'b0;
				bitcnt <= 4'd0;
				tnsm_clr <= 1'b1;
				data_r <= data;
				tx <= 1'b0;              // start bit
				curr_state <= STATE_TNSM_DATA;
			end
		end
		    
		STATE_TNSM_DATA: begin
			if(tnsm_clk_en) begin // we only do something if clock generator asserts synchronization flag
				tx <= data_r[0]; // uart is lsb first
				data_r <= {1'b0, data_r[7:1]}; // shift to the right
				parity <= parity^tx; // Parity is computed this way in case frame_size < 8 and input data is larger than expected
				bitcnt <= bitcnt + 4'd1;
				if(bitcnt == frame_size) begin // if the whole frame was transmitted
					if(^parity_type) begin // if parity is enabled
						tx <= parity_type == 2'b01 ? parity^tx /*even*/ : ~parity^tx /*odd*/; // parity bit
						curr_state <= STATE_TNSM_PARITY;
					end else begin
						tx <= 1'b1;       // stop bit 1
						curr_state <= STATE_TNSM_STOP1;
					end
				end 
			end
		end
		              
		STATE_TNSM_PARITY: begin
			if(tnsm_clk_en) begin // we only do something if clock generator asserts synchronization flag
				tx <= 1'b1;       // stop bit 1
				curr_state <= STATE_TNSM_STOP1;
			end
		end
		              
		STATE_TNSM_STOP1: begin
			if(tnsm_clk_en) begin // we only do something if clock generator asserts synchronization flag
				tx <= 1'b1;       // stop bit 2 or idle tx state
				curr_state <= stop_type ? STATE_TNSM_STOP2 : STATE_TNSM_IDLE;
			end
		end
		
		STATE_TNSM_STOP2: begin
			if(tnsm_clk_en) begin // we only do something if clock generator asserts synchronization flag
				tx <= 1'b1;
				curr_state <= STATE_TNSM_IDLE;
			end
		end
		    
		endcase
	end
end

assign busy = curr_state != STATE_TNSM_IDLE;

endmodule
