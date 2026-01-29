module uart_ip_tb();

bit clk;
bit arst_n;

<<<<<<< Updated upstream
localparam N_OF_TESTS = 100;
// UART SIGNALS //
logic rx;
logic tx;
=======
uart_ip_interface intf(clk, arst_n);
>>>>>>> Stashed changes

logic [7:0] tx_data;

logic rx_tx_wire;
assign rx = rx_tx_wire;
assign tx = rx_tx_wire;

always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

logic [7:0] byte_data;

initial begin
<<<<<<< Updated upstream
    ctl_reg_wdata = '0;
    ctl_reg_wmask = '0;
    ctl_reg_we = '0;
    tx_data = '0;
    wait(arst_n);
    @(posedge clk);
    repeat(N_OF_TESTS) begin
    	ctl_reg_wdata = {tx_data, 1'b1, 4'd7, 1'b0, 2'b00, 2'b11, 1'b1};
    	ctl_reg_wmask = {19{1'b1}};
    	ctl_reg_we = 1'b1;
	#1500us;
=======
    wait(arst_n);
    @(posedge clk);
    repeat(100) begin
        std::randomize(byte_data);
        intf.set_default_config();
        @(posedge clk);
        intf.write_tnsm_data(byte_data);
        wait(uart_ip_i.uart_tnsm_i.busy);
        #1200us;
>>>>>>> Stashed changes
    end
    $finish;
end

always @(negedge uart_ip_i.recv_busy) begin
  tx_data = $urandom_range(0, 255);
end

uart_ip uart_ip_i(
.clk(clk),
.arst_n(arst_n),
.ctl_reg_we(intf.ctl_reg_we),
.ctl_reg_wdata(intf.ctl_reg_wdata),
.ctl_reg_wmask(intf.ctl_reg_wmask),
.ctl_reg_rdata(intf.ctl_reg_rdata),
.st_reg_re(intf.st_reg_re),
.st_reg_rmask(intf.st_reg_rmask),
.st_reg_rdata(intf.st_reg_rdata),
// UART SIGNALS //
<<<<<<< Updated upstream
.rx(rx_tx_wire),
.tx(rx_tx_wire)
=======
.rx(intf.rx_tx_wire),
.tx(intf.rx_tx_wire)
>>>>>>> Stashed changes
);


initial begin
    $shm_open("shm_db");
    $shm_probe("ASMTR");
end

endmodule;
