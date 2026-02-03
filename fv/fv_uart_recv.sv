module fv_uart_ip (
	input logic clk,
	input logic arst_n,
	// Writting Ports //
	input logic ctl_reg_we,
 	input logic [18:0] ctl_reg_wdata,
	input logic [18:0] ctl_reg_wmask,
	input logic [18:0] ctl_reg_rdata,
	input logic st_reg_re,
	input logic [11:0] st_reg_rmask,
	input logic [11:0] st_reg_rdata,
	input logic rx,
	input logic tx
);


endmodule: fv_uart_ip
