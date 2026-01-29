module uart_ip_tb();

bit clk;
bit arst_n;

localparam N_OF_TESTS = 100;

uart_ip_interface intf(clk, arst_n);

logic [7:0] tx_data;

logic rx_tx_wire;
assign rx = rx_tx_wire;
assign tx = rx_tx_wire;

always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

logic [7:0] byte_data;

initial begin
    wait(arst_n);
    @(posedge clk);
    repeat(100) begin
        std::randomize(byte_data);
        intf.set_default_config();
        @(posedge clk);
        intf.write_tnsm_data(byte_data);
        wait(uart_ip_i.uart_tnsm_i.busy);
        #1200us;
    end
    $finish;
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
.rx(intf.rx_tx_wire),
.tx(intf.rx_tx_wire)
);

assert property(
	 @(posedge clk);
 	disable iff(!arst_n)
);

initial begin
    $shm_open("shm_db");
    $shm_probe("ASMTR");
end

endmodule;
