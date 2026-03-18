module cmd_control_fsm_tb;

parameter AW = 16;
parameter DW = 32;

parameter N_OF_TESTS = 100;

bit clk;
bit arst_n;
logic uc_out_valid;
logic [DW - 1 : 0] uc_data;
logic [AW - 1 : 0] cmd_addr_fsm;
logic [DW - 1 : 0] cmd_wdata_fsm;
logic cmd_ready_in;
logic cmd_we_fsm;
logic cmd_valid_fsm;

always #5ns clk = ~clk;
assign #50ns arst_n = 1'b1;

initial begin
    cmd_ready_in = 1'b1;
    uc_data = '0;
    uc_out_valid = 1'b0;
    wait(arst_n);
    @(posedge clk);
    repeat(N_OF_TESTS) begin
    
        std::randomize(uc_data);
        
        repeat(5) @(posedge clk);
        uc_out_valid = 1'b1;
        @(posedge clk);
        uc_out_valid = 1'b0;
        repeat(1) @(posedge clk);
        
        std::randomize(uc_data);
        
        repeat(1) @(posedge clk);
        uc_out_valid = 1'b1;
        @(posedge clk);
        uc_out_valid = 1'b0;
        repeat(1) @(posedge clk);
        uc_data = 32'd1;
        @(posedge clk);
        uc_out_valid = 1'b1;
        @(posedge clk);
        uc_out_valid = 1'b0;

        repeat(5) @(posedge clk);
    end
    $finish;
end

cmd_control_fsm cmd_control_fsm_i(
    .clk(clk),
    .arst_n(arst_n),
    .uc_out_valid(uc_out_valid),
    .uc_data(uc_data),
    .cmd_ready_in(cmd_ready_in),
    .cmd_addr_fsm(cmd_addr_fsm),
    .cmd_wdata_fsm(cmd_wdata_fsm),
    .cmd_we_fsm(cmd_we_fsm),
    .cmd_valid_fsm(cmd_valid_fsm)
);

endmodule
