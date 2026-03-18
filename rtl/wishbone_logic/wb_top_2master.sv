module wb_top_2master #(parameter AW = 16, parameter DW = 32)
(
    input logic clk,
    input logic arst_n,

    // MASTER 0 COMMAND INTERFACE //
    input logic [AW-1:0] cmd_addr_m0,
    input logic [DW-1:0] cmd_wdata_m0,
    input logic cmd_we_m0,
    input logic cmd_valid_m0,
    output logic cmd_ready_m0,

    // MASTER 0 RESPONSE INTERFACE //
    output logic [DW-1:0] rsp_rdata_m0,
    output logic rsp_valid_m0,

    // MASTER 1 COMMAND INTERFACE //
    input logic [AW-1:0] cmd_addr_m1,
    input logic [DW-1:0] cmd_wdata_m1,
    input logic cmd_we_m1,
    input logic cmd_valid_m1,
    output logic cmd_ready_m1,

    // MASTER 1 RESPONSE INTERFACE //
    output logic [DW-1:0] rsp_rdata,
    output logic rsp_valid,

    // ERIKA SIGNALS //
    input logic signed [10:0]   temp_entrada,
    input logic                 sensor_valid,
    output logic                 calefactor,
    output logic                 alerta,
    output logic                 ventilador,
    output logic [1:0]           estado_actual,
    output logic [2:0]           cont_bajo,
    output logic [2:0]           cont_alto
);

// --------------------------------------------------
// SLAVE 0 (instruction_memory - SRAM)
// --------------------------------------------------
logic [AW-1:0] s0_adr_o;
logic [DW-1:0] s0_dat_o;
logic [DW-1:0] s0_dat_i;
logic          s0_we_o;
logic [3:0]    s0_sel_o;
logic          s0_stb_o;
logic          s0_cyc_o;
logic          s0_ack_i;
logic          s0_err_i;

// --------------------------------------------------
// SLAVE 1 (dbg module)
// --------------------------------------------------
logic [AW-1:0] s1_adr_o;
logic [DW-1:0] s1_dat_o;
logic [DW-1:0] s1_dat_i;
logic          s1_we_o;
logic [3:0]    s1_sel_o;
logic          s1_stb_o;
logic          s1_cyc_o;
logic          s1_ack_i;
logic          s1_err_i;

// --------------------------------------------------
// SLAVE 2 (temp_mon - Erika)
// --------------------------------------------------
logic [AW-1:0]        s2_adr_o;
logic [DW-1:0]        s2_dat_o;
logic [DW-1:0]        s2_dat_i;
logic                 s2_we_o;
logic [3:0]           s2_sel_o;
logic                 s2_stb_o;
logic                 s2_cyc_o;
logic                 s2_ack_i;
logic                 s2_err_i;

// --------------------------------------------------
// SLAVE 3 (servo - Ramon)
// --------------------------------------------------
logic [AW-1:0] s3_adr_o;
logic [DW-1:0] s3_dat_o;
logic [DW-1:0] s3_dat_i;
logic          s3_we_o;
logic [3:0]    s3_sel_o;
logic          s3_stb_o;
logic          s3_cyc_o;
logic          s3_ack_i;
logic          s3_err_i;

// --------------------------------------------------
// SLAVE 4 (uart_tx_rx - Manuel)
// --------------------------------------------------
logic [AW-1:0] s4_adr_o;
logic [DW-1:0] s4_dat_o;
logic [DW-1:0] s4_dat_i;
logic          s4_we_o;
logic [3:0]    s4_sel_o;
logic          s4_stb_o;
logic          s4_cyc_o;
logic          s4_ack_i;
logic          s4_err_i;

// --------------------------------------------------
// SLAVE 5 (wb_gpio - leds/switches)
// --------------------------------------------------
logic [AW-1:0] s5_adr_o;
logic [DW-1:0] s5_dat_o;
logic [DW-1:0] s5_dat_i;
logic          s5_we_o;
logic [3:0]    s5_sel_o;
logic          s5_stb_o;
logic          s5_cyc_o;
logic          s5_ack_i;
logic          s5_err_i;

// WISHBONE MASTER PORT M1 //
logic [AW-1:0] wbm_adr_o_m1;
logic [DW-1:0] wbm_dat_o_m1;
logic [DW-1:0] wbm_dat_i_m1;
logic          wbm_we_o_m1;
logic [3:0]    wbm_sel_o_m1;
logic          wbm_stb_o_m1;
logic          wbm_cyc_o_m1;
logic          wbm_ack_i_m1;
logic          wbm_err_i_m1;

// WISHBONE MASTER PORT M0 //
logic [AW-1:0] wbm_adr_o_m0;
logic [DW-1:0] wbm_dat_o_m0;
logic [DW-1:0] wbm_dat_i_m0;
logic          wbm_we_o_m0;
logic [3:0]    wbm_sel_o_m0;
logic          wbm_stb_o_m0;
logic          wbm_cyc_o_m0;
logic          wbm_ack_i_m0;
logic          wbm_err_i_m0;

wb_interconnect wb_interconnect_i (
    .clk(clk),
    .rst_n(arst_n),

    // ---- Master 0 (higher priority) ----
    .m0_adr_i(wbm_adr_o_m0),
    .m0_dat_i(wbm_dat_o_m0),
    .m0_dat_o(wbm_dat_i_m0),
    .m0_we_i(wbm_we_o_m0),
    .m0_sel_i(wbm_sel_o_m0),
    .m0_stb_i(wbm_stb_o_m0),
    .m0_cyc_i(wbm_cyc_o_m0),
    .m0_ack_o(wbm_ack_i_m0),
    .m0_err_o(wbm_err_i_m0),

    // ---- Master 1 (lower priority) ----
    .m1_adr_i(wbm_adr_o_m1),
    .m1_dat_i(wbm_dat_o_m1),
    .m1_dat_o(wbm_dat_i_m1),
    .m1_we_i(wbm_we_o_m1),
    .m1_sel_i(wbm_sel_o_m1),
    .m1_stb_i(wbm_stb_o_m1),
    .m1_cyc_i(wbm_cyc_o_m1),
    .m1_ack_o(wbm_ack_i_m1),
    .m1_err_o(wbm_err_i_m1),

    // ---- Slave 0 (instruction_memory - SRAM) ----
    .s0_adr_o(s0_adr_o),
    .s0_dat_o(s0_dat_o),
    .s0_dat_i(s0_dat_i),
    .s0_we_o(s0_we_o),
    .s0_sel_o(s0_sel_o),
    .s0_stb_o(s0_stb_o),
    .s0_cyc_o(s0_cyc_o),
    .s0_ack_i(s0_ack_i),
    .s0_err_i(s0_err_i),

    // ---- Slave 1 (dbg module - ?) ----
    .s1_adr_o(s1_adr_o),
    .s1_dat_o(s1_dat_o),
    .s1_dat_i(s1_dat_i),
    .s1_we_o(s1_we_o),
    .s1_sel_o(s1_sel_o),
    .s1_stb_o(s1_stb_o),
    .s1_cyc_o(s1_cyc_o),
    .s1_ack_i(s1_ack_i),
    .s1_err_i(s1_err_i),

    // ---- Slave 2 (temp_mon - Erika) ----
    .s2_adr_o(s2_adr_o),
    .s2_dat_o(s2_dat_o),
    .s2_dat_i(s2_dat_i),
    .s2_we_o(s2_we_o),
    .s2_sel_o(s2_sel_o),
    .s2_stb_o(s2_stb_o),
    .s2_cyc_o(s2_cyc_o),
    .s2_ack_i(s2_ack_i),
    .s2_err_i(s2_err_i),

    // ---- Slave 3 (servo - ramon) ----
    .s3_adr_o(s3_adr_o),
    .s3_dat_o(s3_dat_o),
    .s3_dat_i(s3_dat_i),
    .s3_we_o(s3_we_o),
    .s3_sel_o(s3_sel_o),
    .s3_stb_o(s3_stb_o),
    .s3_cyc_o(s3_cyc_o),
    .s3_ack_i(s3_ack_i),
    .s3_err_i(s3_err_i),

    // ---- Slave 4 (uart_tx_rx - manuel) ----
    .s4_adr_o(s4_adr_o),
    .s4_dat_o(s4_dat_o),
    .s4_dat_i(s4_dat_i),
    .s4_we_o(s4_we_o),
    .s4_sel_o(s4_sel_o),
    .s4_stb_o(s4_stb_o),
    .s4_cyc_o(s4_cyc_o),
    .s4_ack_i(s4_ack_i),
    .s4_err_i(s4_err_i),

    // ---- Slave 5 (wb_gpio - leds/switches) ----
    .s5_adr_o(s5_adr_o),
    .s5_dat_o(s5_dat_o),
    .s5_dat_i(s5_dat_i),
    .s5_we_o(s5_we_o),
    .s5_sel_o(s5_sel_o),
    .s5_stb_o(s5_stb_o),
    .s5_cyc_o(s5_cyc_o),
    .s5_ack_i(s5_ack_i),
    .s5_err_i(s5_err_i)
);

wb_mem wb_slave0_i(
    .clk(clk),
    .rst_n(arst_n),
    .wbs_adr_i(s0_adr_o),
    .wbs_dat_i(s0_dat_o),
    .wbs_dat_o(s0_dat_i),
    .wbs_we_i(s0_we_o),
    .wbs_sel_i(s0_sel_o),
    .wbs_stb_i(s0_stb_o),
    .wbs_cyc_i(s0_cyc_o),
    .wbs_ack_o(s0_ack_i),
    .wbs_err_o(s0_err_i)
);

wb_slave1 wb_slave1_i(
    .clk(clk),
    .rst_n(arst_n),
    .wbs_adr_i(s1_adr_o),
    .wbs_dat_i(s1_dat_o),
    .wbs_dat_o(s1_dat_i),
    .wbs_we_i(s1_we_o),
    .wbs_sel_i(s1_sel_o),
    .wbs_stb_i(s1_stb_o),
    .wbs_cyc_i(s1_cyc_o),
    .wbs_ack_o(s1_ack_i),
    .wbs_err_o(s1_err_i)
);

wb_slave2 wb_slave2_i (
    .clk(clk),
    .rst_n(arst_n),
    .wbs_adr_i(s2_adr_o),
    .wbs_dat_i(s2_dat_o),
    .wbs_dat_o(s2_dat_i),
    .wbs_we_i(s2_we_o),
    .wbs_sel_i(s2_sel_o),
    .wbs_stb_i(s2_stb_o),
    .wbs_cyc_i(s2_cyc_o),
    .wbs_ack_o(s2_ack_i),
    .wbs_err_o(s2_err_i),

    .temp_entrada(temp_entrada),
    .sensor_valid(sensor_valid),
    .calefactor(calefactor),
    .alerta(alerta),
    .ventilador(ventilador),
    .estado_actual(estado_actual),
    .cont_bajo(cont_bajo),
    .cont_alto(cont_alto)
);

wb_slave3 wb_slave3_i(
    .clk(clk),
    .rst_n(arst_n),
    .adr_i(s3_adr_o),
    .dat_i(s3_dat_o),
    .dat_o(s3_dat_i),
    .we_i(s3_we_o),
    .sel_i(s3_sel_o),
    .stb_i(s3_stb_o),
    .ack_o(s3_ack_i),
    .cyc_i(s3_cyc_o),
    .err_o(s3_err_i)
);

wb_slave4 wb_slave4_i(
    .clk(clk),
    .rst_n(arst_n),
    .adr_i(s4_adr_o),
    .dat_i(s4_dat_o),
    .dat_o(s4_dat_i),
    .we_i(s4_we_o),
    .sel_i(s4_sel_o),
    .stb_i(s4_stb_o),
    .ack_o(s4_ack_i),
    .cyc_i(s4_cyc_o),
    .err_o(s4_err_i)
);

wb_slave5 wb_slave5_i(
    .clk(clk),
    .rst_n(arst_n),
    .adr_i(s5_adr_o),
    .dat_i(s5_dat_o),
    .dat_o(s5_dat_i),
    .we_i(s5_we_o),
    .sel_i(s5_sel_o),
    .stb_i(s5_stb_o),
    .ack_o(s5_ack_i),
    .cyc_i(s5_cyc_o),
    .err_o(s5_err_i)
);


wb_master wb_master_m0_i(
    .clk(clk),
    .rst_n(arst_n),
    .cmd_addr(cmd_addr_m0),
    .cmd_wdata(cmd_wdata_m0),
    .cmd_we(cmd_we_m0),
    .cmd_valid(cmd_valid_m0),
    .cmd_ready(cmd_ready_m0),
    .rsp_rdata(rsp_rdata_m0),
    .rsp_valid(rsp_valid_m0),

    .wbm_adr_o(wbm_adr_o_m0),
    .wbm_dat_o(wbm_dat_o_m0),
    .wbm_dat_i(wbm_dat_i_m0),
    .wbm_we_o(wbm_we_o_m0),
    .wbm_sel_o(wbm_sel_o_m0),
    .wbm_stb_o(wbm_stb_o_m0),
    .wbm_cyc_o(wbm_cyc_o_m0),
    .wbm_ack_i(wbm_ack_i_m0),
    .wbm_err_i(wbm_err_i_m0)
);

wb_master wb_master_m1_i(
    .clk(clk),
    .rst_n(arst_n),
    .cmd_addr(cmd_addr_m1),
    .cmd_wdata(cmd_wdata_m1),
    .cmd_we(cmd_we_m1),
    .cmd_valid(cmd_valid_m1),
    .cmd_ready(cmd_ready_m1),
    .rsp_rdata(rsp_rdata_m1),
    .rsp_valid(rsp_valid_m1),

    .wbm_adr_o(wbm_adr_o_m1),
    .wbm_dat_o(wbm_dat_o_m1),
    .wbm_dat_i(wbm_dat_i_m1),
    .wbm_we_o(wbm_we_o_m1),
    .wbm_sel_o(wbm_sel_o_m1),
    .wbm_stb_o(wbm_stb_o_m1),
    .wbm_cyc_o(wbm_cyc_o_m1),
    .wbm_ack_i(wbm_ack_i_m1),
    .wbm_err_i(wbm_err_i_m1)
);

endmodule


