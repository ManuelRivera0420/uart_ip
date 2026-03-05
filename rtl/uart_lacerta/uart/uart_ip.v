//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_ip
//
// Description:
// this module wraps the uart transeiver modules
//////////////////////////////////////////////////////////////////////////////////

module uart_ip(
	input wire clk,
	input wire arst_n,
	
	input wire ctl_reg_we,
	input wire [18:0] ctl_reg_wdata,
	input wire [18:0] ctl_reg_wmask,
	output wire [18:0] ctl_reg_rdata,
	
	input wire st_reg_re,
	input wire [11:0] st_reg_rmask,
	output wire [11:0] st_reg_rdata,
	
	input wire rx,
	output wire tx
);

// Transmitter-related signals
wire tnsm_clk_en;
wire tnsm;
wire tnsm_clr;
wire tnsm_busy;
wire [7:0] tnsm_data;

// Clock generator
wire [3:0] baud_rate;

// Receiver-related signals
wire rx_sync;
wire recv_clk_en;
wire rx_negedge_det;
wire [7:0] recv_data;
wire recv_int;
wire recv_error;
wire recv_busy;

// Control register related signals
wire active;
wire [1:0] frame_type;  // 2'b00 : 5 bits, 2'b01 : 6 bits, 2'b10 : 7 bits, 2'b11 : 8 bits
wire [1:0] parity_type; // 2'b00 : no parity, 2'b01: even parity, 2'b10: odd parity, 2'b11: no parity
wire stop_type;         // 1'b0 : 1 stop bit, 1'b1 : 2 stop bits

// basic two flip-flop synchronizer for rx asynchronous input
uart_two_ff_synchronizer rx_2ff_sync(
  .clk(clk),
  .arst_n(arst_n),
  .async_data(rx),
  .sync_data(rx_sync)
);

// status register
uart_status_reg uart_status_reg_i(
	.clk(clk),
	.arst_n(arst_n),
	.recv_error(recv_error),              // Receiver error
	.recv_busy(recv_busy),                // Receiver busy
	.tnsm_busy(tnsm_busy),                // Transmitter busy
	.recv_int(recv_int),                  // received data interrupt
	.recv_data(recv_data),                // received data
	.re(st_reg_re),                       // read enable
	.rmask(st_reg_rmask),                 // read mask used for read on clear (when rmask bit === 1)
	.status_data(st_reg_rdata)            // Status output data
);

// control register
uart_control_reg uart_control_reg_i(
	.clk(clk),
	.arst_n(arst_n),
	.we(ctl_reg_we), // write enable
	.wmask(ctl_reg_wmask), // write mask
	.datain(ctl_reg_wdata),
	.tnsm_clr(tnsm_clr), // clear tnsm bit
	.frame_type(frame_type),
	.parity_type(parity_type),
	.stop_type(stop_type),
	.active(active),
	.baud_rate(baud_rate),
	.tnsm(tnsm),
	.tnsm_data(tnsm_data),
	.ctl_reg_rdata(ctl_reg_rdata)
);

// clock generator
uart_clk_gen uart_clk_gen_i(
	.clk(clk),
	.arst_n(arst_n),
	.active(active),
	.baud_rate(baud_rate),
	.tx_clk_en(tnsm_clk_en),
	.rx_clk_en(recv_clk_en)
);

// edge detector
uart_edge_detector uart_edge_detector_i(
	.clk(clk),
	.arst_n(arst_n),
	.rx(rx_sync),
	.rx_negedge_det(rx_negedge_det)
);

// transmitter
uart_tnsm uart_tnsm_i(
	.clk(clk),
	.arst_n(arst_n),
	.active(active),
	.tnsm(tnsm),
	.data(tnsm_data),
	.frame_type(frame_type),
	.parity_type(parity_type),
	.stop_type(stop_type),
	.tnsm_clk_en(tnsm_clk_en),
	.busy(tnsm_busy),
	.tnsm_clr(tnsm_clr),
	.tx(tx)
);

// receiver
uart_recv uart_recv_i(
	.clk(clk),
	.arst_n(arst_n),
	.active(active),
	.rx(rx_sync),
	.rx_negedge_det(rx_negedge_det),
	.frame_type(frame_type),
	.parity_type(parity_type),
	.stop_type(stop_type),
	.recv_clk_en(recv_clk_en),
	.data(recv_data),
	.recv(recv_int),
	.error(recv_error),
	.busy(recv_busy)
);

endmodule
