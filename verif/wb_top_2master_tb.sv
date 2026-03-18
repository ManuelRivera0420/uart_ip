module tb_wb_top_2master;

parameter AW = 16;
parameter DW = 32;

logic clk;
logic arst_n;

// MASTER 0 COMMAND INTERFACE
logic [AW-1:0] cmd_addr_m0;
logic [DW-1:0] cmd_wdata_m0;
logic          cmd_we_m0;
logic          cmd_valid_m0;
logic          cmd_ready_m0;

// MASTER 0 RESPONSE INTERFACE
logic [DW-1:0] rsp_rdata_m0;
logic          rsp_valid_m0;

// MASTER 1 COMMAND INTERFACE
logic [AW-1:0] cmd_addr_m1;
logic [DW-1:0] cmd_wdata_m1;
logic          cmd_we_m1;
logic          cmd_valid_m1;
logic          cmd_ready_m1;

// MASTER 1 RESPONSE INTERFACE
logic [DW-1:0] rsp_rdata;
logic          rsp_valid;



always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

initial begin
    cmd_valid_m1 = 1'b0;
    cmd_we_m1 = 1'b0;
    cmd_addr_m1 = '0;
    cmd_wdata_m1 = '0;

    cmd_valid_m0 = 1'b0;
    cmd_we_m0 = 1'b0;
    cmd_addr_m0 = '0;
    cmd_wdata_m0 = '0;

    wait(arst_n);
    @(posedge clk);
    cmd_addr_m1 = 16'h00FF;
    cmd_wdata_m1 = 32'h800000AA;
    cmd_we_m1 = 1'b1;
    cmd_valid_m1 = 1'b1;
    @(posedge clk);
    cmd_valid_m1 = 1'b0;

    cmd_we_m1 = 1'b0;
    @(posedge clk);
    cmd_valid_m1 = 1'b1;
    @(posedge clk);
    cmd_valid_m1 = 1'b0;

    repeat(20) @(posedge clk);
    $finish;
end


wb_top_2master_debug #(
    .AW(AW),
    .DW(DW)
) dut (
    .clk(clk),
    .arst_n(arst_n),

    // MASTER 0 COMMAND INTERFACE
    .cmd_addr_m0(cmd_addr_m0),
    .cmd_wdata_m0(cmd_wdata_m0),
    .cmd_we_m0(cmd_we_m0),
    .cmd_valid_m0(cmd_valid_m0),
    .cmd_ready_m0(cmd_ready_m0),

    // MASTER 0 RESPONSE INTERFACE
    .rsp_rdata_m0(rsp_rdata_m0),
    .rsp_valid_m0(rsp_valid_m0),

    // MASTER 1 COMMAND INTERFACE
    .cmd_addr_m1(cmd_addr_m1),
    .cmd_wdata_m1(cmd_wdata_m1),
    .cmd_we_m1(cmd_we_m1),
    .cmd_valid_m1(cmd_valid_m1),
    .cmd_ready_m1(cmd_ready_m1),

    // MASTER 1 RESPONSE INTERFACE
    .rsp_rdata(rsp_rdata),
    .rsp_valid(rsp_valid)
);

endmodule
