module uart_debug(
	input logic clk,
	input logic arst_n,
	input rx,
	output tx,
	// Debug
	output [6:0] HEX0,
	output [6:0] HEX1,
	output [6:0] HEX2,
	output [6:0] HEX3,
	output [6:0] HEX4,
	output [6:0] HEX5,
	output [6:0] HEX6,
	output [6:0] HEX7
);
	localparam NUM_BYTES_DATA = 4;
	localparam NUM_BYTES_ADDRESS = 1;

	logic [NUM_BYTES_DATA*8-1:0] mem_wdata;
	logic [NUM_BYTES_ADDRESS*8-1:0] mem_waddr;
	logic mem_re;
	logic [NUM_BYTES_ADDRESS*8-1:0] mem_raddr;
	logic [NUM_BYTES_DATA*8-1:0] mem_rdata;

  wire [31:0] seg_data;
  // Debug
  de2_115_7seg de2_115_7seg_i(
  .oSEG0(HEX0),
  .oSEG1(HEX1),
  .oSEG2(HEX2),
  .oSEG3(HEX3),
  .oSEG4(HEX4),
  .oSEG5(HEX5),
  .oSEG6(HEX6),
  .oSEG7(HEX7),
  .iDIG(seg_data) );

uart_ip_memory_mapped #(NUM_BYTES_DATA, NUM_BYTES_ADDRESS) uart_ip_memory_mapped_i (
	.debug(seg_data),
	.clk(clk),
	.arst_n(arst_n),
	// Memory related signals
	.mem_we(mem_we),
	.mem_wdata(mem_wdata),
	.mem_waddr(mem_waddr),
	.mem_re(mem_re),
	.mem_raddr(mem_raddr),
	.mem_rdata(mem_rdata),
	.mem_rdy(mem_rdy),
	// UART related signals
	.rx(rx),
	.tx(tx)
);

endmodule
