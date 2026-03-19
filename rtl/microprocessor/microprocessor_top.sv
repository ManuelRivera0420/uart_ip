`timescale 1ns / 1ps
import riscv_params_pkg::*;
//------------------------------------------------------------------------------
// Module: microprocessor_top
// Description:
//   Top-level integration for a single-cycle RV32-style microprocessor datapath.
//   Contains:
//     - PC register and next-PC selection (sequential vs redirect)
//     - Instruction fetch (instruction memory)
//     - Register file read/write-back
//     - Immediate generation
//     - ALU execute
//     - Data memory (stores/loads when implemented)
//     - Control unit decode and branch decision
//
// Notes:
//   - Signal naming follows datapath intent: pc_* , if_* , id_* , ex_* , mem_* , wb_*
//   - This module is structural (wires + instantiations) and contains no state
//     besides submodules (PC, RF, memories).
//------------------------------------------------------------------------------
module microprocessor_top (
    input logic                    clk,
    input logic                    arst_n,
    //input logic                    instr_en,
    //input logic [DATA_WIDTH-1:0]   driven_instr,

    input  logic                    imem_wr_en,
    input  logic [AW-1:0]           imem_wr_addr,
    input  logic [DATA_WIDTH-1:0]   imem_wr_data,
    input  logic                    prog_rdy,
    output logic [DATA_WIDTH-1:0]   uc_out,
    output logic                    uc_out_valid,
    output logic                    uc_out_ready
);


    //--------------------------------------------------------------------------
    // IF: Program Counter and Instruction Fetch
    //--------------------------------------------------------------------------

    logic [DATA_WIDTH-1:0] pc_q;            // current PC (byte address)
    logic [DATA_WIDTH-1:0] pc_next;         // next PC selected by pc_next mux
    logic [DATA_WIDTH-1:0] pc_plus_inc;     // sequential next PC (PC + inc)
    logic                  pc_inc_sel;      // +4 vs +2 selector (future)
    logic [2:0]            pc_inc;          // increment constant (2 or 4)
    logic [DATA_WIDTH-1:0] instruction;
    logic [DATA_WIDTH-1:0] mem_instruction;           // fetched instruction

    // Next-PC select:
    //   - branch_taken=0 -> sequential PC+4
    //   - branch_taken=1 -> redirect target (computed in EX path)
    logic                  branch_taken;
    logic [DATA_WIDTH-1:0] branch_target;   // target address (PC + imm), produced in EX

    // PC next mux: select sequential or redirect target
    mux #(.WIDTH(DATA_WIDTH)) upc_next_mux_i (
        .in1(branch_target),     // sel=1 -> redirect
        .in2(pc_plus_inc),       // sel=0 -> sequential
        .sel(branch_taken),
        .out(pc_next)
    );

    // PC register
    program_counter pc_i (
        .clk   (clk),
        .arst_n(arst_n),
        .pc_en(prog_rdy),
        .pc_in (pc_next),
        .pc_out(pc_q)
    );

    // PC increment select (+4 now; +2 reserved for future compressed support)
    plus_4_or_2_mux pc_inc_sel_i (
        .sel            (pc_inc_sel),
        .instruction_add(pc_inc)
    );

    // PC + increment
    adder #(.DATA_WIDTH(DATA_WIDTH)) pc_adder_i (
        .constant_operand(pc_inc),
        .instruction_addr(pc_q),
        .next_instruction (pc_plus_inc)
    );

    // Instruction memory (word-indexed; PC is byte-addressed)
    instruction_memory #(.DATA_WIDTH(DATA_WIDTH), .DEPTH(DEPTH)) instr_mem_i (
        .clk              (clk),
        .pc               (pc_q),
        .instr            (instruction),
        .we               (imem_wr_en),
        .wr_addr          (imem_wr_addr),
        .wr_data          (imem_wr_data)
    );

    //--------------------------------------------------------------------------
    // ID: Decode and Register File Read
    //--------------------------------------------------------------------------

    logic                  rf_we;
    logic [DATA_WIDTH-1:0] rs1_data;
    logic [DATA_WIDTH-1:0] rs2_data;

    // Write-back data (selected later)
    logic [DATA_WIDTH-1:0] mac_result;
    logic [DATA_WIDTH-1:0] wb_data;

    physical_register_file #(.DIR_WIDTH(DIR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) prf_i (
        .clk       (clk),
        .arst_n    (arst_n),
        .write_en  (rf_we),
        .read_dir1 (instruction[19:15]),   // rs1
        .read_dir2 (instruction[24:20]),   // rs2
        .write_dir (instruction[11:7]),    // rd
        .write_data(wb_data),
        .read_data1(rs1_data),
        .read_data2(rs2_data)
    );

    //--------------------------------------------------------------------------
    // ID/EX: Immediate Generation and Operand Select
    //--------------------------------------------------------------------------

    logic [2:0]            imm_sel;
        logic [DATA_WIDTH-1:0] imm;

    imm_gen imm_gen_i (
        .instr   (instruction),
        .imm_sel (imm_sel),
        .imm_out (imm)
    );

    // ALU operand mux controls
    logic [1:0]             op1_sel_pc;     // 00: use zero as operand 1, 01: use PC as operand 1, 10: use rs1 as operand 1
    logic                   op2_sel_imm;    // 1: use imm, 0: use rs2 as operand 2

    logic [DATA_WIDTH-1:0] alu_op1;               // ALU operand 1
    logic [DATA_WIDTH-1:0] alu_op2;               // ALU operand 2
    logic [DATA_WIDTH-1:0] zero_operand = 32'd0;  // Zero operand for LUI operation 
    // Operand1: PC vs rs1
    mux_operand_1 alu_op1_mux_i (
    .in1(zero_operand),   // Zero operand as operand 1
    .in2(pc_q),           // PC as operand 1
    .in3(rs1_data),       // rs1 as operand 1
    .sel(op1_sel_pc),     // 00: use zero as operand 1, 01: use PC as operand 1, 10: use rs1 as operand 1
    .data_out(alu_op1)    // data_out as operand_1
    );

    // Operand2: imm vs rs2
    mux #(.WIDTH(DATA_WIDTH)) alu_op2_mux_i (
        .in1(imm),         // sel=1 -> imm
        .in2(rs2_data),    // sel=0 -> rs2
        .sel(op2_sel_imm),
        .out(alu_op2)
    );

    //--------------------------------------------------------------------------
    // EX: ALU and Branch Decision
    //--------------------------------------------------------------------------

    logic [3:0]            alu_ctrl;
    logic [DATA_WIDTH-1:0] alu_result;

    alu #(.OPERAND_WIDTH(DATA_WIDTH)) alu_i (
        .operand1   (alu_op1),
        .operand2   (alu_op2),
        .alucontrol (alu_ctrl),
        .alu_result (alu_result)
    );

    // For branches/jumps in this single-cycle design, branch_target is produced by ALU
    // when operand1=PC and operand2=imm and alu_ctrl=ADD.
    assign branch_target = alu_result;

    // Comparator for TYPE-B conditions 
    logic b_condition_rs1_rs2;

    branch #(.DATA_WIDTH_BRANCH(DATA_WIDTH)) branch_cmp_i (
        .rs_1           (rs1_data),
        .rs_2           (rs2_data),
        .opcode         (instruction[6:0]),
        .funct_3        (instruction[14:12]),
        .branch_taken   (b_condition_rs1_rs2)
    );

    //--------------------------------------------------------------------------
    // MEM: Data Memory (store/load datapath)
    //--------------------------------------------------------------------------

    logic                  dmem_we;
    logic [DATA_WIDTH-1:0] dmem_rdata;

    data_memory #(.DATA_WIDTH(DATA_WIDTH), .DEPTH(DEPTH)) data_mem_i (
        .clk     (clk),
        .wr_en   (dmem_we),
        .addr    (alu_result),    // byte address from ALU
        .data_in (rs2_data),      // store data
        .data_out(dmem_rdata)     // load data
    );

    //--------------------------------------------------------------------------
    // WB: Write-back Mux (ALU vs MEM vs PC+4)
    //--------------------------------------------------------------------------

    logic [1:0] wb_sel;

    mux_3_to_1 wb_mux_i (
        .data_out_to_pc   (pc_plus_inc),  // PC+4 (link address)
        .alu_to_mem_addr  (alu_result
),   // ALU result
        .data_out_to_mux  (dmem_rdata),   // memory read data
        .mac_to_prf       (mac_result),
        .sel              (wb_sel),
        .data_out         (wb_data)
    );

    //--------------------------------------------------------------------------
    // Control Unit: Decode instruction -> drive control signals
    //--------------------------------------------------------------------------
    
    logic mac_en;

    control_unit cu_i (
        .opcode            (instruction[6:0]),
        .funct_3           (instruction[14:12]),
        .funct_7           (instruction[31:25]),
        .zero              (b_condition_rs1_rs2),     // B condition
        
        .pc_en             (pc_en),
        .prf_wr_en         (rf_we),
        .cu_imm_sel        (imm_sel),
        .prf_pc_mux_ctrl   (op1_sel_pc),
        .prf_imm_mux_ctrl  (op2_sel_imm),
        .cu_alu_ctrl       (alu_ctrl),
        .cu_mem_out_mux_sel(wb_sel),
        .cu_data_mem_wr_en (dmem_we),
        .cu_pc_add_sel     (pc_inc_sel),
        .branch_taken      (branch_taken),

        //MUL signlas
        .mac_en            (mac_en),
        .mac_done          (mac_done)  
    );

    //---------------------------------------------------------------------------
    // MAC for MUL operations
    // --------------------------------------------------------------------------

    mac_top mac_top_i (
      .clk(clk),
      .rst_n(arst_n),
      .start(mac_en),
      .m_in(alu_op1),
      .q_in(alu_op2),
      .product(mac_result),
      .ready(mac_done)
    );

    //assign instruction = instr_en ? driven_instr : mem_instruction;
    assign uc_out_ready = (pc_q == pc_next) ? 1'b1 : 1'b0;
    assign uc_out = wb_data;
    assign uc_out_valid = (instruction[6:0] == 7'b000_0011) ? 1'b1 : 1'b0;
endmodule
