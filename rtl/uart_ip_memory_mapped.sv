`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip_memory_mapped
// Module Name: uart_ip_memory_mapped
//
//////////////////////////////////////////////////////////////////////////////////

module uart_ip_memory_mapped #(parameter NUM_BYTES_DATA = 4, parameter NUM_BYTES_ADDRESS = 1)(
	input clk,
	input arst_n,
	// Memory related signals
	output wire mem_we,
	output wire [NUM_BYTES_DATA*8-1:0] mem_wdata,
	output wire [NUM_BYTES_ADDRESS*8-1:0] mem_waddr,
	output wire mem_re,
	output wire [NUM_BYTES_ADDRESS*8-1:0] mem_raddr,
	input [NUM_BYTES_DATA*8-1:0] mem_rdata,
	input mem_rdy,
	// UART related signals
	input rx,
	output tx
);

	wire ctl_reg_we;
	wire [18:0] ctl_reg_wdata;
	wire [18:0] ctl_reg_wmask;
	wire [18:0] ctl_reg_rdata;
	wire st_reg_re;
	wire [11:0] st_reg_rmask;
	wire [11:0] st_reg_rdata;

	uart_ip_memory_mapped_ctrl_fsm uart_ip_memory_mapped_ctrl_fsm_i(
		.clk(clk),
		.arst_n(arst_n),
		.mem_we(mem_we),
		.mem_wdata(mem_wdata),
		.mem_waddr(mem_waddr),
		.mem_re(mem_re),
		.mem_rdata(mem_rdata),
		.mem_rdy(mem_rdy),
		.mem_raddr(mem_raddr),
		.ctl_reg_we(ctl_reg_we),
		.ctl_reg_wdata(ctl_reg_wdata),
		.ctl_reg_wmask(ctl_reg_wmask),
		.ctl_reg_rdata(ctl_reg_rdata),
		.st_reg_re(st_reg_re),
		.st_reg_rmask(st_reg_rmask),
		.st_reg_rdata(st_reg_rdata)
	);

	uart_ip uart_ip_i(
		.clk(clk),
		.arst_n(arst_n),
		.ctl_reg_we(ctl_reg_we),
		.ctl_reg_wdata(ctl_reg_wdata),
		.ctl_reg_wmask(ctl_reg_wmask),
		.ctl_reg_rdata(ctl_reg_rdata),
		.st_reg_re(st_reg_re),
		.st_reg_rmask(st_reg_rmask),
		.st_reg_rdata(st_reg_rdata),
		.rx(rx),
		.tx(tx)
	);

endmodule
