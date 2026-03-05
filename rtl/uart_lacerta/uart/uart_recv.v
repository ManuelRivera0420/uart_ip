//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_recv
//
// Description:
// this module is a state machine to sample the serial data coming from rx input
//////////////////////////////////////////////////////////////////////////////////

module uart_recv(
	input wire clk,
	input wire arst_n,
	input wire active,
	input wire rx,
	input wire rx_negedge_det,
	input wire [1:0] frame_type,  // 2'b00 : 5 bits, 2'b01 : 6 bits, 2'b10 : 7 bits, 2'b11 : 8 bits
	input wire [1:0] parity_type, // 2'b00 : no parity, 2'b01: even parity, 2'b10: odd parity, 2'b11: no parity
	input wire stop_type,         // 1'b0 : 1 stop bit, 1'b1 : 2 stop bits
	input wire recv_clk_en,
	output wire [7:0] data,
	output reg recv,
	output reg error,
	output wire busy
);

localparam OVERSAMPLE_COUNT = 16 - 1; // we oversample 16x, -1 as we start the oversampling counter at 0

// state machine states parameters
localparam STATE_RECV_IDLE = 3'b000;
localparam STATE_RECV_START = 3'b001;
localparam STATE_RECV_RECEIVE = 3'b010;
localparam STATE_RECV_PARITY = 3'b011;
localparam STATE_RECV_STOP1 = 3'b100;
localparam STATE_RECV_STOP2 = 3'b101;

// internal variables
reg [2:0] curr_state;
reg [3:0] bitcnt;
reg [4:0] ovsample_cnt;
reg [7:0] data_r;
reg parity_exp;
reg parity;
reg [3:0] frame_size;
reg [1:0] data_shift;

// Expected parity bit
always@(*) begin
	case(parity_type)
		2'b00: parity_exp = 1'b0;     // no parity
		2'b01: parity_exp = ^data;  // even parity
		2'b10: parity_exp = ~^data; // odd parity
		default: parity_exp = 1'b0;
	endcase
end

// UART frame size - this only consider data and parity bit
always@(*) begin
	case(frame_type)
		2'b00 : begin frame_size = 5; data_shift = 3; end
		2'b01 : begin frame_size = 6; data_shift = 2; end
		2'b10 : begin frame_size = 7; data_shift = 1; end
		2'b11 : begin frame_size = 8; data_shift = 0; end
	endcase
end

always@(posedge clk, negedge arst_n) begin
	if(!arst_n) begin
		bitcnt <= 4'd0;
		data_r <= 8'd0;
		recv <= 1'b0;
		error <= 1'b0;
		ovsample_cnt <= 5'd0;
		parity <= 1'b0;
		curr_state <= STATE_RECV_IDLE;
	end	else begin
		recv <= 1'b0;
		case(curr_state)
		
		STATE_RECV_IDLE: begin
			data_r <= 8'd0;
			if(active && rx_negedge_det) begin // if uart ip is active and start bit is detected
				curr_state <= STATE_RECV_START;
			end
		end
		
		STATE_RECV_START: begin
			if(recv_clk_en) begin // we only do jump to next state if clock generator asserts synchronization flag
				bitcnt <= 1'b1; // put to 1, so we dont need to use a -1 in if(bitcnt == frame_size) begin comparison in next state
				ovsample_cnt <= ovsample_cnt == (OVERSAMPLE_COUNT>>1) ? 6'd0 : ovsample_cnt + 1'b1; // if we are jumping to the next state, we reset ovsample_cnt to zero
				curr_state <= ovsample_cnt == (OVERSAMPLE_COUNT>>1) ? STATE_RECV_RECEIVE : STATE_RECV_START; // we move to the next state when ovsample_cnt is 7 (at the middle of start bit transmission)
			end
		end
		
		STATE_RECV_RECEIVE: begin
			if(recv_clk_en) begin // we only do something if clock generator asserts synchronization flag
				ovsample_cnt <= ovsample_cnt + 1'b1;
				if(ovsample_cnt == OVERSAMPLE_COUNT) begin // we sample and move to next state when ovsample_cnt gets to OVERSAMPLE_COUNT (15)
					ovsample_cnt <= 4'd0;
					data_r <= {rx, data_r[7:1]}; // uart is lsb first
					if(bitcnt == frame_size) begin // if the whole frame was received, we calculate parity if active, or go to stop state
						curr_state <= (^parity_type) ? STATE_RECV_PARITY : STATE_RECV_STOP1;
					end else begin // if frame is not done, we increment the bit counter
						bitcnt <= bitcnt + 1'b1;
					end
				end
			end
		end
		            
		STATE_RECV_PARITY: begin
			if(recv_clk_en) begin // we only do something if clock generator asserts synchronization flag
				ovsample_cnt <= ovsample_cnt + 1'b1;
				if(ovsample_cnt == OVERSAMPLE_COUNT) begin // capture the parity bit
					ovsample_cnt <= 4'd0;
					parity <= rx;
					curr_state <= STATE_RECV_STOP1;
				end
			end
		end
		            
		STATE_RECV_STOP1: begin
			if(recv_clk_en) begin // we only do something if clock generator asserts synchronization flag
				ovsample_cnt <= ovsample_cnt + 1'b1;
				if(ovsample_cnt == OVERSAMPLE_COUNT) begin // capture the stop bit
					ovsample_cnt <= 4'd0;
					error <= (rx != 1'b1) || ((^parity_type) && (parity_exp != parity)); // if rx does not go high, or parity is active and does not match, we set error flag
					recv <= stop_type ? 1'b0 : 1'b1; // if the uart ip is configured with two stop bits, we do not set the receive flag yet
					curr_state <= stop_type ? STATE_RECV_STOP2 : STATE_RECV_IDLE; // if the uart ip is configured with two stop bits, we jump to the second stop bit receiving state, otherwise, we go to idle
				end
			end
		end
		            
		STATE_RECV_STOP2: begin
			if(recv_clk_en) begin // we only do something if clock generator asserts synchronization flag
				ovsample_cnt <= ovsample_cnt + 1'b1;
				if(ovsample_cnt == OVERSAMPLE_COUNT) begin // capture the second stop bit
					ovsample_cnt <= 4'd0;
					recv <= 1'b1;
					error <= (error) || (rx != 1'b1); // we set the error flag if rx do not stays high
					curr_state <= STATE_RECV_IDLE;
				end
			end
		end

		default: begin
			error <= 1'b1; // we set error flag if unkown state is seen
			curr_state <= STATE_RECV_IDLE;
		end
		
		endcase
	end
end

assign busy = (curr_state != STATE_RECV_IDLE);
assign data = data_r>>data_shift;

endmodule
