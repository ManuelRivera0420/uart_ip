// =============================================================================
// wb_interconnect.sv
// 2-master / 3-slave Wishbone B4 shared-bus interconnect
//
// Arbitration : fixed priority  M0 > M1
//               Grant held for the duration of one complete CYC assertion.
//               When no master is active the bus is idle.
//
// Address map (parameterisable):
//   Slave 0  instruction_memory - SRAM : MEM_BASE .. MEM_BASE+MEM_SIZE-1  (default 0x0000-0x0400)
//   Slave 1  data_memory : REG_BASE .. REG_BASE+REG_SIZE-1  (default 0x0400-0x04FF)
//   Slave 2  wb_ram : WB2_BASE .. WB2_BASE+WB2_SIZE-1  (default 0x2000-0x20FF)
//   Slave 3
//   Slave 4
//   Slave 5
//
// Block diagram:
//
//  M0 ─┐                          ┌─ S0 (wb_mem)
//       ├─[Arbiter]─[Master Mux]──┼─ S1 (wb_reg)
//  M1 ─┘           [Addr Decode]  └─ S2 (wb_ram)
//              [Response Mux back to granted master]
// =============================================================================

`timescale 1ns/1ps

module wb_interconnect #(
    parameter AW       = 16,
    parameter DW       = 32,
    // slave 0
    parameter MEM_BASE = 16'h0000,
    parameter MEM_SIZE = 16'h1000,    // 1 KB
    // slave 1
    parameter REG_BASE = 16'h1000,
    parameter REG_SIZE = 16'h1000,    // 1 word
    // slave 2
    parameter WB2_BASE = 16'h2000,
    parameter WB2_SIZE = 16'h1000     // 256 bytes (64 x 32-bit words)
    // slave 3
    parameter S3_BASE = 16'h3000,
    parameter S3_SIZE = 16'h1000,
    // slave 4
    parameter S4_BASE = 16'h4000,
    parameter S4_SIZE = 16'h1000,
    // slave 5
    parameter S5_BASE = 16'h5000,
    parameter S5_SIZE = 16'h1000
) (
    input  logic         clk,
    input  logic         rst_n,

    // ---- Master 0 (higher priority) ----
    input  logic [AW-1:0] m0_adr_i,
    input  logic [DW-1:0] m0_dat_i,
    output logic [DW-1:0] m0_dat_o,
    input  logic           m0_we_i,
    input  logic [3:0]     m0_sel_i,
    input  logic           m0_stb_i,
    input  logic           m0_cyc_i,
    output logic           m0_ack_o,
    output logic           m0_err_o,

    // ---- Master 1 (lower priority) ----
    input  logic [AW-1:0] m1_adr_i,
    input  logic [DW-1:0] m1_dat_i,
    output logic [DW-1:0] m1_dat_o,
    input  logic           m1_we_i,
    input  logic [3:0]     m1_sel_i,
    input  logic           m1_stb_i,
    input  logic           m1_cyc_i,
    output logic           m1_ack_o,
    output logic           m1_err_o,

    // ---- Slave 0 (instruction_memory - SRAM) ----
    output logic [AW-1:0] s0_adr_o,
    output logic [DW-1:0] s0_dat_o,   // write data  IC -> slave
    input  logic [DW-1:0] s0_dat_i,   // read  data  slave -> IC
    output logic           s0_we_o,
    output logic [3:0]     s0_sel_o,
    output logic           s0_stb_o,
    output logic           s0_cyc_o,
    input  logic           s0_ack_i,
    input  logic           s0_err_i,

    // ---- Slave 1 (dbg module - ?) ----
    output logic [AW-1:0] s1_adr_o,
    output logic [DW-1:0] s1_dat_o,   // write data  IC -> slave
    input  logic [DW-1:0] s1_dat_i,   // read  data  slave -> IC
    output logic           s1_we_o,
    output logic [3:0]     s1_sel_o,
    output logic           s1_stb_o,
    output logic           s1_cyc_o,
    input  logic           s1_ack_i,
    input  logic           s1_err_i,

    // ---- Slave 2 (temp_mon - Erika)
    output logic [AW-1:0] s2_adr_o,
    output logic [DW-1:0] s2_dat_o,   // write data  IC -> slave
    input  logic [DW-1:0] s2_dat_i,   // read  data  slave -> IC
    output logic           s2_we_o,
    output logic [3:0]     s2_sel_o,
    output logic           s2_stb_o,
    output logic           s2_cyc_o,
    input  logic           s2_ack_i,

    // ---- Slave 3 (servo - ramon)
    output logic [AW-1:0] s3_adr_o,
    output logic [DW-1:0] s3_dat_o,   // write data  IC -> slave
    input  logic [DW-1:0] s3_dat_i,   // read  data  slave -> IC
    output logic           s3_we_o,
    output logic [3:0]     s3_sel_o,
    output logic           s3_stb_o,
    output logic           s3_cyc_o,
    input  logic           s2_ack_i,

    // ---- Slave 4 (uart_tx_rx - manuel)
    output logic [AW-1:0] s4_adr_o,
    output logic [DW-1:0] s4_dat_o,   // write data  IC -> slave
    input  logic [DW-1:0] s4_dat_i,   // read  data  slave -> IC
    output logic           s4_we_o,
    output logic [3:0]     s4_sel_o,
    output logic           s4_stb_o,
    output logic           s4_cyc_o,
    input  logic           s4_ack_i,

    // ---- Slave 5 (wb_gpio - leds/switches)
    output logic [AW-1:0] s5_adr_o,
    output logic [DW-1:0] s5_dat_o,   // write data  IC -> slave
    input  logic [DW-1:0] s5_dat_i,   // read  data  slave -> IC
    output logic           s5_we_o,
    output logic [3:0]     s5_sel_o,
    output logic           s5_stb_o,
    output logic           s5_cyc_o,
    input  logic           s5_ack_i

);

    // ------------------------------------------------------------------
    // Arbiter — fixed priority: M0 > M1
    //
    // grant       : 0 = M0 holds bus, 1 = M1 holds bus
    // grant_valid : a master currently holds the bus
    //
    // A new grant is issued only when the bus is idle.
    // The grant is released when the active master deasserts CYC.
    // ------------------------------------------------------------------
    logic grant;
    logic grant_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            grant       <= 1'b0;
            grant_valid <= 1'b0;
        end else begin
            if (!grant_valid) begin
                // Bus idle — grant to highest-priority requesting master
                if (m0_cyc_i) begin
                    grant       <= 1'b0;
                    grant_valid <= 1'b1;
                end else if (m1_cyc_i) begin
                    grant       <= 1'b1;
                    grant_valid <= 1'b1;
                end
            end else begin
                // Bus busy — release when the granted master drops CYC
                if (grant == 1'b0 && !m0_cyc_i)
                    grant_valid <= 1'b0;
                else if (grant == 1'b1 && !m1_cyc_i)
                    grant_valid <= 1'b0;
            end
        end
    end

    // ------------------------------------------------------------------
    // Master mux — forward signals from the granted master onto the bus
    // ------------------------------------------------------------------
    logic [AW-1:0] mx_adr;
    logic [DW-1:0] mx_dat;
    logic           mx_we;
    logic [3:0]     mx_sel;
    logic           mx_stb;
    logic           mx_cyc;

    always_comb begin
        if (grant_valid && grant == 1'b1) begin
            // M1 is granted
            mx_adr = m1_adr_i;
            mx_dat = m1_dat_i;
            mx_we  = m1_we_i;
            mx_sel = m1_sel_i;
            mx_stb = m1_stb_i;
            mx_cyc = m1_cyc_i;
        end else begin
            // M0 is granted (or bus is idle — mux defaults to M0 but
            // grant_valid gates all slave-facing STB/CYC so no transaction
            // can start when the bus is idle)
            mx_adr = m0_adr_i;
            mx_dat = m0_dat_i;
            mx_we  = m0_we_i;
            mx_sel = m0_sel_i;
            mx_stb = m0_stb_i;
            mx_cyc = grant_valid ? m0_cyc_i : 1'b0;
        end
    end

    // ------------------------------------------------------------------
    // Address decoder — one hit signal per slave, mutually exclusive
    // ------------------------------------------------------------------
    localparam [AW-1:0] MEM_LIMIT = MEM_BASE + MEM_SIZE;
    localparam [AW-1:0] REG_LIMIT = REG_BASE + REG_SIZE;
    localparam [AW-1:0] WB2_LIMIT = WB2_BASE + WB2_SIZE;
    localparam [AW-1:0] S3_LIMIT = S3_BASE + S3_SIZE;
    localparam [AW-1:0] S4_LIMIT = S4_BASE + S4_SIZE;
    localparam [AW-1:0] S5_LIMIT = S5_BASE + S5_SIZE;

    logic s0_hit, s1_hit, s2_hit, s3_hit, s4_hit, s5_hit;
    logic addr_hit;

    always_comb begin
        s0_hit   = 1'b0;
        s1_hit   = 1'b0;
        s2_hit   = 1'b0;
        s3_hit   = 1'b0;
        s4_hit   = 1'b0;
        s5_hit   = 1'b0;
        addr_hit = 1'b0;
        if (mx_adr >= MEM_BASE && mx_adr < MEM_LIMIT) begin
            s0_hit   = 1'b1;
            addr_hit = 1'b1;
        end else if (mx_adr >= REG_BASE && mx_adr < REG_LIMIT) begin
            s1_hit   = 1'b1;
            addr_hit = 1'b1;
        end else if (mx_adr >= WB2_BASE && mx_adr < WB2_LIMIT) begin
            s2_hit   = 1'b1;
            addr_hit = 1'b1;
        end else if (mx_adr >= S3_BASE && mx_adr < S3_LIMIT) begin
            s3_hit   = 1'b1;
            addr_hit = 1'b1;
        end else if (mx_adr >= S4_BASE && mx_adr < S4_LIMIT) begin
            s4_hit   = 1'b1;
            addr_hit = 1'b1;
        end else if (mx_adr >= S5_BASE && mx_adr < S5_LIMIT) begin
            s5_hit   = 1'b1;
            addr_hit = 1'b1;
        end
    end

    // ------------------------------------------------------------------
    // Drive slaves
    // STB is gated by grant_valid + this slave's hit + valid address
    // CYC is gated by grant_valid + this slave's hit
    // ------------------------------------------------------------------
    assign s0_adr_o = mx_adr;
    assign s0_dat_o = mx_dat;
    assign s0_we_o  = mx_we;
    assign s0_sel_o = mx_sel;
    assign s0_stb_o = mx_stb & grant_valid & s0_hit & addr_hit;
    assign s0_cyc_o = mx_cyc & grant_valid & s0_hit;

    assign s1_adr_o = mx_adr;
    assign s1_dat_o = mx_dat;
    assign s1_we_o  = mx_we;
    assign s1_sel_o = mx_sel;
    assign s1_stb_o = mx_stb & grant_valid & s1_hit & addr_hit;
    assign s1_cyc_o = mx_cyc & grant_valid & s1_hit;

    assign s2_adr_o = mx_adr;
    assign s2_dat_o = mx_dat;
    assign s2_we_o  = mx_we;
    assign s2_sel_o = mx_sel;
    assign s2_stb_o = mx_stb & grant_valid & s2_hit & addr_hit;
    assign s2_cyc_o = mx_cyc & grant_valid & s2_hit;

    assign s3_adr_o = mx_adr;
    assign s3_dat_o = mx_dat;
    assign s3_we_o  = mx_we;
    assign s3_sel_o = mx_sel;
    assign s3_stb_o = mx_stb & grant_valid & s3_hit & addr_hit;
    assign s3_cyc_o = mx_cyc & grant_valid & s3_hit;

    assign s4_adr_o = mx_adr;
    assign s4_dat_o = mx_dat;
    assign s4_we_o  = mx_we;
    assign s4_sel_o = mx_sel;
    assign s4_stb_o = mx_stb & grant_valid & s4_hit & addr_hit;
    assign s4_cyc_o = mx_cyc & grant_valid & s4_hit;

    assign s5_adr_o = mx_adr;
    assign s5_dat_o = mx_dat;
    assign s5_we_o  = mx_we;
    assign s5_sel_o = mx_sel;
    assign s5_stb_o = mx_stb & grant_valid & s5_hit & addr_hit;
    assign s5_cyc_o = mx_cyc & grant_valid & s5_hit;

    // ------------------------------------------------------------------
    // Response mux — route ACK/DAT from the selected slave back to the
    // master that currently holds the grant
    // ------------------------------------------------------------------
    logic           rsp_ack;
    logic [DW-1:0] rsp_dat;
    logic           rsp_err;

    always_comb begin
        if (s5_hit) begin
            rsp_ack = s5_ack_i;
            rsp_data = s5_dat_i;
            rsp_err = s5_err_i;
        end else if (s4_hit) begin
            rsp_ack = s4_ack_i;
            rsp_dat = s4_dat_i;
            rsp_err = s4_err_i;
        end else if (s3_hit) begin
            rsp_ack = s3_ack_i;
            rsp_dat = s3_dat_i;
            rsp_err = s3_err_i; 
        end else if (s2_hit) begin
            rsp_ack = s2_ack_i;
            rsp_dat = s2_dat_i;
            rsp_err = s2_err_i; 
        end else if (s1_hit) begin
            rsp_ack = s1_ack_i;
            rsp_dat = s1_dat_i;
            rsp_err = s1_err_i;
        end else begin
            rsp_ack = s0_ack_i;
            rsp_dat = s0_dat_i;
            rsp_err = s0_err_i;
        end
    end

    // Deliver response only to the master that holds the grant
    assign m0_ack_o = (grant_valid && grant == 1'b0) ? rsp_ack : 1'b0;
    assign m0_dat_o = (grant_valid && grant == 1'b0) ? rsp_dat : '0;
    assign m0_err_o = (grant_valid && grant == 1'b0) ? rsp_err : 1'b0;

    assign m1_ack_o = (grant_valid && grant == 1'b1) ? rsp_ack : 1'b0;
    assign m1_dat_o = (grant_valid && grant == 1'b1) ? rsp_dat : '0;
    assign m1_err_o = (grant_valid && grant == 1'b1) ? rsp_err : 1'b0;

    wb_slave0 wb_slave0_i(
        .clk(clk),
        .rst_n(rst_n),
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
        .rst_n(rst_n),
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


    wb_slave2 wb_slave2_i(
        .clk(clk),
        .rst_n(rst_n),
        .wbs_adr_i(s2_adr_o),
        .wbs_dat_i(s2_dat_o),
        .wbs_dat_o(s2_dat_i),
        .wbs_we_i(s2_we_o),
        .wbs_sel_i(s2_sel_o),
        .wbs_stb_i(s2_stb_o),
        .wbs_cyc_i(s2_cyc_o),
        .wbs_ack_o(s2_ack_i),
        .wbs_err_o(s2_err_i)
    );

    wb_slave3 wb_slave3_i(
        .clk(clk),
        .adr_i(s3_adr_o),
        .dat_i(s3_dat_o),
        .dat_o(s3_dat_i),
        .we_i(s3_we_o),
        .sel_i(s3_sel_o),
        .stb_i(s3_stb_o),
        .ack_o(s3_ack_i),
        .cyc_i(s3_cyc_o)
    );

    wb_slave4 wb_slave4_i(
        .clk(clk),
        .adr_i(s4_adr_o),
        .dat_i(s4_dat_o),
        .dat_o(s4_dat_i),
        .we_i(s4_we_o),
        .sel_i(s4_sel_o),
        .stb_i(s4_stb_o),
        .ack_o(s4_ack_i),
        .cyc_i(s4_cyc_o)
    );

    wb_slave5 wb_slave5_i(
        .clk(clk),
        .adr_i(s5_adr_o),
        .dat_i(s5_dat_o),
        .dat_o(s5_dat_i),
        .we_i(s5_we_o),
        .sel_i(s5_sel_o),
        .stb_i(s5_stb_o),
        .ack_o(s5_ack_i),
        .cyc_i(s5_cyc_o)
    );

endmodule
