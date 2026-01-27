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
    ctl_reg_wdata = '0;
    ctl_reg_wmask = '0;
    ctl_reg_we = 1'b0;
    wait(arst_n);
    @(posedge clk);
    ctl_reg_wdata = {8'd43, 1'b1, 4'd7, 1'b0, 2'b00, 2'b11, 1'b1};
    ctl_reg_wmask = {19{1'b1}};
    ctl_reg_we = 1'b1;
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

initial begin
    $shm_open("shm_db");
    $shm_probe("ASMTR");
end

endmodule;
