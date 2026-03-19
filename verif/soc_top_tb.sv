module soc_top_tb;

bit clk;
bit arst_n;
logic data_sel;
logic [DW - 1 : 0] data;
logic [DW - 1 : 0] rsp_rdata_m0;
logic rsp_valid_m0;
logic [DW - 1 : 0] rsp_rdata_m1;
logic rsp_valid_m1;
logic uart_out_flag;
logic uc_out_flag;

always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

initial begin
    wait(arst_n);
    wait(soc_top_i.microprocessor_top_i.uc_out_ready);
    repeat(10) @(posedge clk);
    $finish;
end

soc_top soc_top_i(
    .clk(clk),
    .arst_n(arst_n),
    .data_sel(data_sel),
    .data(data),
    .rsp_rdata_m0(rsp_rdata_m0),
    .rsp_valid_m0(rsp_valid_m0),
    .rsp_rdata_m1(rsp_rdata_m1),
    .rsp_valid_m1(rsp_valid_m1),
    .uart_out_flag(uart_out_flag),
    .uc_out_flag(uc_out_flag)
);

endmodule
