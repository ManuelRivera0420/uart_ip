// rtl/riscv_params_pkg.sv
package riscv_params_pkg;
  //	------------------------
  //	WISHBONE
  //-	-----------------------
  localparam AW = 32;
  localparam DW = 32;
  // -----------------------------
  // Datapath sizing
  // -----------------------------
  localparam int DIR_WIDTH  = 5;
  localparam int DATA_WIDTH = 32;
  localparam int DEPTH      = 1024;

  // Memory indexing
  localparam int MEM_ADDR_W = 10; // log2(DEPTH)
  localparam int BYTE_WIDTH = 8;

  // -----------------------------
  // RV32I opcodes
  // -----------------------------
  localparam logic [6:0] OPCODE_R_TYPE     = 7'b0110011;
  localparam logic [6:0] OPCODE_I_TYPE     = 7'b0010011;
  localparam logic [6:0] OPCODE_L_TYPE     = 7'b0000011;
  localparam logic [6:0] OPCODE_S_TYPE     = 7'b0100011;
  localparam logic [6:0] OPCODE_B_TYPE     = 7'b1100011;
  localparam logic [6:0] OPCODE_U_LUI      = 7'b0110111;
  localparam logic [6:0] OPCODE_U_AUIPC    = 7'b0010111;
  localparam logic [6:0] OPCODE_JAL_TYPE   = 7'b1101111;

  // -----------------------------
  // funct3 (grouped)
  // -----------------------------
  localparam logic [2:0] F3_ADD_SUB_MUL = 3'b000;
  localparam logic [2:0] F3_SLL         = 3'b001;
  localparam logic [2:0] F3_SLT         = 3'b010;
  localparam logic [2:0] F3_SLTU        = 3'b011;
  localparam logic [2:0] F3_XOR         = 3'b100;
  localparam logic [2:0] F3_SRL_SRA     = 3'b101;
  localparam logic [2:0] F3_OR          = 3'b110;
  localparam logic [2:0] F3_AND         = 3'b111;
  localparam logic [2:0] F3_MULH        = 3'b001;

  localparam logic [2:0] F3_BEQ     = 3'b000;
  localparam logic [2:0] F3_BNE     = 3'b001;
  localparam logic [2:0] F3_BLT     = 3'b100;
  localparam logic [2:0] F3_BGE     = 3'b101;
  localparam logic [2:0] F3_BLTU    = 3'b110;
  localparam logic [2:0] F3_BGEU    = 3'b111;

  localparam logic [2:0] F3_LB      = 3'b000;
  localparam logic [2:0] F3_LH      = 3'b001;
  localparam logic [2:0] F3_LW      = 3'b010;
  localparam logic [2:0] F3_LBU     = 3'b100;
  localparam logic [2:0] F3_LHU     = 3'b101;

  localparam logic [2:0] F3_SB      = 3'b000;
  localparam logic [2:0] F3_SH      = 3'b001;
  localparam logic [2:0] F3_SW      = 3'b010;


  // -----------------------------
  // ALU control encodings
  // -----------------------------
  localparam logic [3:0] ALU_ADD  = 4'b0000;
  localparam logic [3:0] ALU_SUB  = 4'b0001;
  localparam logic [3:0] ALU_AND  = 4'b0010;
  localparam logic [3:0] ALU_OR   = 4'b0011;
  localparam logic [3:0] ALU_XOR  = 4'b0100;
  localparam logic [3:0] ALU_EQ   = 4'b0101;
  localparam logic [3:0] ALU_SLT  = 4'b0110;
  localparam logic [3:0] ALU_SLTU = 4'b0111;
  localparam logic [3:0] ALU_SLL  = 4'b1000;
  localparam logic [3:0] ALU_SRL  = 4'b1001;
  localparam logic [3:0] ALU_SRA  = 4'b1010;

  // -----------------------------
  // Immediate select encodings
  // -----------------------------
  localparam logic [2:0] IMM_I = 3'b000;
  localparam logic [2:0] IMM_S = 3'b001;
  localparam logic [2:0] IMM_B = 3'b010;
  localparam logic [2:0] IMM_U = 3'b011;
  localparam logic [2:0] IMM_J = 3'b100;

  // -----------------------------
  // Writeback mux select
  // -----------------------------
  localparam logic [1:0] ALU_TO_PRF         = 2'b00;
  localparam logic [1:0] DATA_OUT_TO_PRF    = 2'b01;
  localparam logic [1:0] INSTRUCTION_TO_PRF = 2'b10;
  localparam logic [1:0] MAC_TO_PRF         = 2'b11;

  // -----------------------------
  // PC add select
  // -----------------------------
  localparam logic [1:0] PC_4      = 2'b00;
  localparam logic [1:0] PC_BRANCH = 2'b01;
  localparam logic [1:0] PC_JAL    = 2'b10;

// =========================================================
// Raíz jerárquica del DUT
// =========================================================
`define DUT dut
// =========================================================
// IF
// =========================================================
`define PC_Q          `DUT.pc_i.pc_out
`define PC_NEXT       `DUT.pc_i.pc_in
`define PC_PLUS_INC   `DUT.pc_adder_i.next_instruction
`define BR_TAKEN      `DUT.cu_i.branch_taken
`define BR_TARGET     `DUT.upc_next_mux_i.sel

`define OPCODE        `DUT.cu_i.opcode
`define FUNCT3        `DUT.cu_i.funct_3
`define FUNCT7        `DUT.cu_i.funct_7
`define INSTR_WORD    `DUT.instruction
`define INSTR_SEL      drive_if.instr_en

// =========================================================
// ID/WB
// =========================================================
`define RF_WE         `DUT.prf_i.write_en
`define X0            `DUT.prf_i.prf[0]
`define RS1           `DUT.prf_i.read_dir1
`define RS2           `DUT.prf_i.read_dir2
`define RD            `DUT.prf_i.write_dir
`define RS1_DATA      `DUT.prf_i.read_data1
`define RS2_DATA      `DUT.prf_i.read_data2
`define WB_DATA       `DUT.prf_i.write_data
`define WB_SEL        `DUT.wb_mux_i.sel

// =========================================================
// IMM/EX
// =========================================================
`define IMM_SEL       `DUT.imm_gen_i.imm_sel
`define IMM           `DUT.imm_gen_i.imm_out

`define OP1_SEL_PC    `DUT.alu_op1_mux_i.sel
`define OP2_SEL_IMM   `DUT.alu_op2_mux_i.sel

`define ALU_CTRL      `DUT.alu_i.alucontrol
`define ALU_OP1       `DUT.alu_i.operand1
`define ALU_OP2       `DUT.alu_i.operand2
`define ALU_RES       `DUT.alu_i.alu_result

`define BCOND         `DUT.branch_cmp_i.branch_taken

// =========================================================
// MEM
// =========================================================
`define DMEM_WE       `DUT.data_mem_i.wr_en
`define DMEM_ADDR     `DUT.data_mem_i.addr
`define DMEM_WDATA    `DUT.data_mem_i.data_in
`define DMEM_RDATA    `DUT.data_mem_i.data_out
  
endpackage

