module soc_top #(parameter AW = 16, parameter DW = 32, parameter BYTE = 8)(
    input logic clk,
    input logic arst_n,
    input logic data_sel,
    output logic [DW - 1 : 0] data,
    output logic [DW - 1 : 0] rsp_rdata_m0,
    output logic rsp_valid_m0,
    output logic [DW - 1 : 0] rsp_rdata_m1,
    output logic rsp_valid_m1,
    output logic uart_out_flag,
    output logic uc_out_flag
);

// UART INTERNAL WIRES //
logic [31:0] uart_out;
logic uart_out_valid;
logic uart_out_ready;

// MICROPROCESSOR INTERNAL WIRES //
logic [31:0] uc_out;
logic uc_out_valid;
logic uc_out_ready;

microprocessor_top microprocessor_top_i(
    .clk(clk),
    .arst_n(arst_n),
    .imem_wr_en(1'b0),
    .imem_wr_addr('0),
    .imem_wr_data('0),
    .prog_rdy(1'b1),
    .uc_out(uc_out),
    .uc_out_valid(uc_out_valid),
    .uc_out_ready(uc_out_ready)
);

logic cmd_ready_m1;
logic [AW - 1 : 0] cmd_addr_m1;
logic [DW - 1 : 0] cmd_wdata_m1;
logic cmd_we_m1;
logic cmd_valid_m1;

cmd_control_fsm cmd_control_fsm_i(
    .clk(clk),
    .arst_n(arst_n),
    .uc_out_valid(uc_out_valid),
    .uc_data(uc_out),
    .cmd_ready_in(cmd_ready_m1),
    .cmd_addr_fsm(cmd_addr_m1),
    .cmd_wdata_fsm(cmd_wdata_m1),
    .cmd_we_fsm(cmd_we_m1),
    .cmd_valid_fsm(cmd_valid_m1)
);

logic [AW - 1 : 0] cmd_addr_m0;
logic [DW - 1 : 0] cmd_wdata_m0;
logic cmd_we_m0;
logic cmd_valid_m0;
logic cmd_ready_m0;

wb_top_2master_debug wb_top_2master_debug_i(
    .clk(clk),
    .arst_n(arst_n),
    .cmd_addr_m0(cmd_addr_m0),
    .cmd_wdata_m0(cmd_wdata_m0),
    .cmd_we_m0(cmd_we_m0),
    .cmd_valid_m0(cmd_valid_m0),
    .cmd_ready_m0(cmd_ready_m0),
    .rsp_rdata_m0(rsp_rdata_m0),
    .rsp_valid_m0(rsp_valid_m0),

    .cmd_addr_m1(cmd_addr_m1),
    .cmd_wdata_m1(cmd_wdata_m1),
    .cmd_we_m1(cmd_we_m1),
    .cmd_valid_m1(cmd_valid_m1),
    .cmd_ready_m1(cmd_ready_m1),
    .rsp_rdata_m1(rsp_rdata_m1),
    .rsp_valid_m1(rsp_valid_m1)
);

assign data = data_sel ? uc_out : uart_out;

endmodule
