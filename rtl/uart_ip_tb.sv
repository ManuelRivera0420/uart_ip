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

// UART SIGNALS //
logic rx;
logic tx;

always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

initial begin
    wait(arst_n);
    @(posedge clk);
    #10ms;
    $finish;
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
.rx(rx),
.tx(tx)
);

endmodule;
