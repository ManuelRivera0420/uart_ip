//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
// 
// Design Name: uart_ip
// Module Name: uart_ip_memory_mapped_ctrl_fsm
//
//////////////////////////////////////////////////////////////////////////////////

module uart_ip_memory_mapped_ctrl_fsm #(parameter NUM_BYTES_DATA = 4, parameter NUM_BYTES_ADDRESS = 1, parameter NUM_BYTES_COMMAND = 1 ) (
	input clk,
	input arst_n,
	output reg mem_we,
	output reg [NUM_BYTES_DATA*8-1:0] mem_wdata,
	output reg [NUM_BYTES_ADDRESS*8-1:0] mem_waddr,
	output reg mem_re,
	input [NUM_BYTES_DATA*8-1:0] mem_rdata,
	input mem_rdy,
	output wire [NUM_BYTES_ADDRESS*8-1:0] mem_raddr,

	output reg ctl_reg_we,
	output reg [18:0] ctl_reg_wdata,
	output reg [18:0] ctl_reg_wmask,
	input [18:0]  ctl_reg_rdata,

	output reg st_reg_re,
	output reg [11:0] st_reg_rmask,
	input [11:0] st_reg_rdata
);

	localparam STATE_IDLE = 3'b000;
	localparam STATE_RECV_ADDRESS = 3'b001;
	localparam STATE_WAIT_MEM_DATA = 3'b010;
	localparam STATE_WRITE_TNSM_DATA = 3'b011;
	localparam STATE_RECV_TNSM_DATA = 3'b100;
	localparam COMMAND_RANGE_MSB = (NUM_BYTES_COMMAND * 8) - 1;
	localparam ADDR_RANGE_MSB = (NUM_BYTES_ADDRESS * 8)  - 1;
	localparam DATA_RANGE_MSB = (NUM_BYTES_DATA * 8)  - 1;
	localparam PACKET_RANGE_MSB = COMMAND_RANGE_MSB + ADDR_RANGE_MSB + DATA_RANGE_MSB + 2;

	// Commands codes for controlling SPI-based memory mapped slave
	localparam COMMAND_READ = 8'b0000_0000;
	localparam COMMAND_WRITE = 8'b0000_0001;
	localparam COMMAND_CONFIGURE = 8'b0000_0010;
	localparam COMMAND_STATUS = 8'b0000_0011;

	logic recv_error;
	logic recv_busy;
	logic tnsm_busy;
	logic recv_int;
	logic [7:0] recv_data;

	assign recv_error = st_reg_rdata[11];
	assign recv_busy = st_reg_rdata[10];
	assign tnsm_busy = st_reg_rdata[9];
	assign recv_int = st_reg_rdata[8];
	assign recv_data = st_reg_rdata[7:0];

	logic [2:0] state;
	logic [$clog2(PACKET_RANGE_MSB) : 0] inc_bytes_cnt;
	logic [COMMAND_RANGE_MSB : 0] command_r;
	logic [ADDR_RANGE_MSB : 0] addr_bytes;
	logic [DATA_RANGE_MSB : 0] data_bytes;
	logic [DATA_RANGE_MSB : 0] mem_rdata_r;

	assign mem_raddr = addr_bytes;

	always@(posedge clk, negedge arst_n) begin
		if(~arst_n) begin
			state <= STATE_IDLE;
			mem_we <= 1'b0;
			mem_wdata <= {NUM_BYTES_DATA*8{1'b0}};
			mem_waddr <= {NUM_BYTES_ADDRESS*8{1'b0}};
			mem_re <= 1'b0;
			mem_rdata_r <= {NUM_BYTES_DATA*8{1'b0}};
	
			ctl_reg_we <= 1'b0;
			ctl_reg_wdata <= 19'd0;
			ctl_reg_wmask <= 19'd0;
	
			st_reg_re <= 1'b0;
			st_reg_rmask <= 12'd0;
	
			inc_bytes_cnt <= {($clog2(PACKET_RANGE_MSB)+1){1'b0}};
			data_bytes <= {NUM_BYTES_DATA*8{1'b0}};
			addr_bytes <= {NUM_BYTES_ADDRESS*8{1'b0}};
			command_r <= {(NUM_BYTES_COMMAND*8){1'b0}};
	
		end else begin

			ctl_reg_we <= 1'b0;
			ctl_reg_wdata <= 19'd0;
			ctl_reg_wmask <= 19'd0;

			mem_re <= 1'b0;
			st_reg_re <= 1'b0;
			st_reg_rmask <= 12'd0;

			mem_we <= 1'b0;
			//mem_wdata <= {NUM_BYTES_DATA*8{1'b0}};
			//mem_waddr <= {NUM_BYTES_ADDRESS*8{1'b0}};

			case(state)

				STATE_IDLE: begin
					if(recv_int) begin
						inc_bytes_cnt <= {($clog2(PACKET_RANGE_MSB)+1){1'b0}};
						command_r <= recv_data;
						state <= STATE_RECV_ADDRESS;
						data_bytes <= {NUM_BYTES_DATA*8{1'b0}};
						st_reg_re <= 1'b1;
						st_reg_rmask <= 12'b0001_0000_0000;
						mem_rdata_r <= {ctl_reg_rdata, st_reg_rdata}; // Used when command is COMMAND_STATUS or COMMAND_CONFIGURE
					end
				end

				STATE_RECV_ADDRESS: begin
					if(inc_bytes_cnt == NUM_BYTES_ADDRESS) begin
						mem_re <= 1'b1;
						inc_bytes_cnt <= {($clog2(PACKET_RANGE_MSB)+1){1'b0}};
						state <= ( (command_r == COMMAND_STATUS) || (command_r == COMMAND_CONFIGURE) ) ? STATE_WRITE_TNSM_DATA : STATE_WAIT_MEM_DATA;
					end else if(recv_int) begin
						st_reg_re <= 1'b1;
						st_reg_rmask <= 12'b0001_0000_0000;
						inc_bytes_cnt <= inc_bytes_cnt + 1'd1;
    	           //if(NUM_BYTES_ADDRESS == 1)
							addr_bytes <= recv_data;
    	           //else
  						//  addr_bytes <= {recv_data, addr_bytes[ADDR_RANGE_MSB:8]};
					end
				end

				STATE_WAIT_MEM_DATA: begin
					if(mem_rdy) begin
						mem_rdata_r <= mem_rdata;
						state <= STATE_WRITE_TNSM_DATA;
					end
				end

				STATE_WRITE_TNSM_DATA: begin
					if(inc_bytes_cnt == NUM_BYTES_DATA) begin
						if(command_r == COMMAND_READ) begin
							state <= STATE_IDLE;
						end if(command_r == COMMAND_WRITE) begin
							state <= STATE_IDLE;
							mem_we <= 1'b1;
							mem_wdata <= data_bytes;
							mem_waddr <= addr_bytes;
						end else if(command_r == COMMAND_CONFIGURE) begin
							state <= STATE_IDLE;
							ctl_reg_we <= 1'b1;
							ctl_reg_wdata <= data_bytes[15:0];
							ctl_reg_wmask <= addr_bytes;
						end else if(command_r == COMMAND_STATUS) begin
							state <= STATE_IDLE;
							st_reg_re <= 1'b1;
							st_reg_rmask <= addr_bytes;
						end
					end else begin
						ctl_reg_we <= 1'b1;
						ctl_reg_wdata <= {mem_rdata_r[7:0],1'b1,4'b0000,1'b0,2'b00,2'b00,1'b0};
						ctl_reg_wmask <= 19'b111_1111_1100_0000_0000;
						mem_rdata_r <= {8'd0, mem_rdata_r[DATA_RANGE_MSB:8]};
						inc_bytes_cnt <= inc_bytes_cnt + 1'd1;
						state <= STATE_RECV_TNSM_DATA;
					end
				end

				STATE_RECV_TNSM_DATA: begin
					if(recv_int) begin
						st_reg_re <= 1'b1;
						st_reg_rmask <= 12'b0001_0000_0000;
						data_bytes <= {recv_data, data_bytes[DATA_RANGE_MSB:8]};
						state <= STATE_WRITE_TNSM_DATA;
					end
				end

			endcase
	
		end
	end

endmodule
