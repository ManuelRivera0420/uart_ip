module uart_ip_tb();

bit clk;
bit arst_n;
logic ctl_reg_we;
logic [18:0] ctl_reg_wdata;
logic [18:0] ctl_reg_wmask;
logic [18:0] ctl_reg_rdata;
logic st_reg_re;
logic [11:0] st_reg_rmask;
logic [11:0] st_reg_rdata;

localparam N_OF_TESTS = 100;
// UART SIGNALS //
logic rx;
logic tx;

logic [7:0] tx_data;

logic rx_tx_wire;
assign rx = rx_tx_wire;
assign tx = rx_tx_wire;

always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

initial begin
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
    end
    $finish;
end

always @(negedge uart_ip_i.recv_busy) begin
  tx_data = $urandom_range(0, 255);
end

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
// UART SIGNALS //
.rx(rx_tx_wire),
.tx(rx_tx_wire)
);

initial begin
    $shm_open("shm_db");
    $shm_probe("ASMTR");
end

endmodule;
