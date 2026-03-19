`timescale 1ns / 1ps
//------------------------------------------------------------------------------
// Module: control_unit
// Description:
//   Combinational control unit for a single-cycle RV32I-style datapath.
//   Decodes {opcode, funct3, funct7} and generates control signals for:
//     - Register file write-back enable and write-back source selection
//     - Immediate format selection (imm_gen control)
//     - ALU operation selection
//     - Data memory write enable (stores)
//     - PC update decision (sequential vs branch/jump target)
//
// Supported instructions (current):
//   - I-type: ADDI, SLTI, SLTIU, XORI, ORI, ANDI
//   - R-type: ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
//   - B-type: BEQ (branch decision uses input 'zero')
//   - J-type: JAL (unconditional)
//
// Assumptions:
//   - 'zero' is asserted when rs1 == rs2 (BEQ compare evaluated externally).
//   - Control encodings (IMM_*, ALU_*, mux selects, opcodes) are defined in defines.svh.
//   - PC-target computation (PC + imm) and PC muxing are implemented outside this module.
//
// Notes:
//   - Default assignments implement the common I-type ALU-immediate path.
//     Opcode decoding below overrides only what differs per instruction class.
//   - Assertions for illegal/unsupported encodings can be added in a later stage.
//------------------------------------------------------------------------------
import riscv_params_pkg::*;
module control_unit(
    input  logic [6:0]  opcode,              // instr[6:0]
    input  logic [2:0]  funct_3,             // instr[14:12]
    input  logic [6:0]  funct_7,             // instr[31:25]
    input  logic        zero,                // 1 when rs1 == rs2 (BEQ condition)
    output logic        prf_wr_en,           // register file write enable
    output logic [2:0]  cu_imm_sel,          // immediate format select (imm_gen)
    output logic [1:0]  prf_pc_mux_ctrl,     // ALU operand1 select (rs1 vs PC)
    output logic        prf_imm_mux_ctrl,    // ALU operand2 select (rs2 vs imm)
    output logic [3:0]  cu_alu_ctrl,         // ALU operation select
    output logic [1:0]  cu_mem_out_mux_sel,  // write-back mux select (to PRF)
    output logic        cu_data_mem_wr_en,   // data memory write enable (stores)
    output logic        cu_pc_add_sel,       // PC increment select (+4 now; +2 reserved)
    output logic        branch_taken,        // PC redirect request (branch/jump)
    output logic        mac_en,              // Enable for MAC operations (MUL)
    input  logic        mac_done,            // 1 when mac has finished the operation  
    output logic        pc_en                // Run/stop the count in MUL operations

);

    always_comb begin
        //-------------------------------------------------------------------------
        // Defaults: I-type ALU-immediate behavior
        //   - rd write enabled
        //   - ALU computes rs1 + imm
        //   - PC advances sequentially (+4)
        // Opcode decode below overrides these defaults as required.
        //-------------------------------------------------------------------------
        prf_wr_en          = 1'b1;
        cu_data_mem_wr_en  = 1'b0;
        cu_imm_sel         = IMM_I;
        prf_pc_mux_ctrl    = 2'b10;       // operand1 = rs1
        prf_imm_mux_ctrl   = 1'b1;        // operand2 = imm
        cu_pc_add_sel      = 1'b0;        // +4 in RV32; +2 reserved for future compressed support
        cu_mem_out_mux_sel = ALU_TO_PRF;  // write-back = ALU result
        cu_alu_ctrl        = ALU_ADD;
        branch_taken       = 1'b0;        // default: no PC redirect
        mac_en             = 1'b0;        // disable the MAC
        pc_en              = 1'b1;        // enable pc count 

        unique case (opcode)

            // I-type ALU-immediate ops: rd <- rs1 op imm
            OPCODE_I_TYPE: begin
                unique case (funct_3)
                    F3_ADD_SUB_MUL:   cu_alu_ctrl = ALU_ADD;
                    F3_SLL:           cu_alu_ctrl = ALU_SLT;
                    F3_SLTU:          cu_alu_ctrl = ALU_SLTU;
                    F3_XOR:           cu_alu_ctrl = ALU_XOR;
                    F3_OR:            cu_alu_ctrl = ALU_OR;
                    F3_AND:           cu_alu_ctrl = ALU_AND;
                    default:          cu_alu_ctrl = ALU_ADD;
                endcase
            end

            // B-type branch: no write-back; PC redirected when branch_taken=1
            OPCODE_B_TYPE: begin
                prf_wr_en       = 1'b0;   // branches do not write rd
                cu_imm_sel      = IMM_B;  // branch offset immediate
                prf_pc_mux_ctrl = 2'b01;   // operand1 = rs1 (as defined by your datapath for target calc)
                cu_alu_ctrl   = ALU_ADD; // used for target computation elsewhere (PC + imm path)
                branch_taken  = zero;    // redirect request when condition is true
                unique case (funct_3)
                    // BEQ: take branch when rs1 == rs2 (zero=1)
                    F3_BEQ: ;
                    // BNE: take branch when rs1 != rs2 (zero=1)
                    F3_BNE: ;
                    // BLT: take branch when rs1 < rs2 (zero=1)
                    F3_BLT: ;
                    // BGE: take branch when rs1 >= rs2 (zero=1)
                    F3_BGE: ;
                    // BLTU: take branch when rs1 < rs2 (zero=1)
                    F3_BLTU: ;
                    // BGEU: take branch when rs1 >= rs2 (zero=1)
                    F3_BGEU: ; 
                    default: begin
                        cu_alu_ctrl  = ALU_ADD;
                        branch_taken = 1'b0;
                    end
                endcase
            end

            // R-type ALU-register ops: rd <- rs1 op rs2
            OPCODE_R_TYPE: begin
                prf_imm_mux_ctrl = 1'b0; // operand2 = rs2 (not immediate)

                // funct7 selects ADD/SUB and SRL/SRA families in RV32I
                if (funct_7 == 7'b0000_000) begin
                    unique case (funct_3)
                        F3_ADD_SUB_MUL:   cu_alu_ctrl = ALU_ADD;
                        F3_SLL:   cu_alu_ctrl = ALU_SLL;
                        F3_SLT:   cu_alu_ctrl = ALU_SLT;
                        F3_SLTU:  cu_alu_ctrl = ALU_SLTU;
                        F3_XOR:  cu_alu_ctrl = ALU_XOR;
                        F3_SRL_SRA:   cu_alu_ctrl = ALU_SRL;
                        F3_OR:   cu_alu_ctrl = ALU_OR;
                        F3_AND:  cu_alu_ctrl = ALU_AND;
                        default:cu_alu_ctrl = ALU_ADD;
                    endcase
                end else if (funct_7 == 7'b0100_000) begin
                    unique case (funct_3)
                        F3_ADD_SUB_MUL: cu_alu_ctrl = ALU_SUB;
                        F3_SRL_SRA:     cu_alu_ctrl = ALU_SRA;
                        default:        cu_alu_ctrl = ALU_ADD;
                    endcase
                end else if (funct_7 == 7'b0000_001) begin
                    unique case (funct_3)
                    F3_ADD_SUB_MUL: begin
                      prf_wr_en   = 1'b0;
                      if (mac_done) begin
                        cu_mem_out_mux_sel = MAC_TO_PRF;  // write-back = MAC result
                        prf_wr_en = 1'b1;
                        pc_en  = 1'b1;
                        mac_en = 1'b0;
                      end else begin 
                        pc_en  = 1'b0;
                        mac_en = 1'b1;
                      end
                    end
                    F3_MULH: begin
                      prf_wr_en   = 1'b0;
                      if (mac_done) begin
                        cu_mem_out_mux_sel = MAC_TO_PRF;  // write-back = MAC result
                        prf_wr_en = 1'b1;
                        pc_en  = 1'b1;
                        mac_en = 1'b0;
                      end else begin 
                        pc_en  = 1'b0;
                        mac_en = 1'b1;
                      end
                    end
                    default: begin 
                      prf_wr_en = 1'b1;
                      mac_en = 1'b0;
                      pc_en  = 1'b1;
                      cu_mem_out_mux_sel = ALU_TO_PRF;  // write-back = ALU result
                      cu_alu_ctrl = ALU_ADD;
                    end
                    endcase    
                end
            end

            // JAL: rd <- PC+4, PC <- PC + imm (unconditional redirect)
            OPCODE_JAL_TYPE: begin
                cu_imm_sel         = IMM_J;               // jump offset immediate
                prf_pc_mux_ctrl    = 2'b01;                // operand1 = PC (for target calc path)
                cu_mem_out_mux_sel = INSTRUCTION_TO_PRF;  // write-back selects PC+4 (per your datapath naming)
                cu_alu_ctrl        = ALU_ADD;
                branch_taken       = 1'b1;                // unconditional redirect  
            end 
            // load-word 
            OPCODE_L_TYPE: begin
                cu_mem_out_mux_sel = DATA_OUT_TO_PRF;
                unique case (funct_3)
                    F3_LB:     ;
                    F3_LH:     ;
                    F3_LW:     ;
                    F3_LBU:    ;
                    F3_LHU:    ;
                    default: prf_wr_en = 1'b1;
                endcase  
            end
            // write-word
            OPCODE_S_TYPE: begin 
                prf_wr_en = 1'b0;
                cu_mem_out_mux_sel = ALU_TO_PRF;
                cu_imm_sel         = IMM_S;
                cu_data_mem_wr_en  = 1'b1;
                unique case (funct_3)
                    F3_SB:     ;
                    F3_SH:     ;
                    F3_SW:     ;
                    default: prf_wr_en = 1'b0;
                endcase 
            end
            // LUI operation
            OPCODE_U_LUI: begin
                prf_pc_mux_ctrl    = 2'b00;                // operand1 = ZERO
                cu_imm_sel         = IMM_U;               // Extend the width of imm
            end
            // AUIPC operation
            OPCODE_U_AUIPC: begin
                prf_pc_mux_ctrl    = 2'b01;                // operand1 = PC
                cu_imm_sel         = IMM_U;               // Extend the width of imm
            end
            // Default: NOP
            default: begin
                prf_wr_en    = 1'b0;
                cu_alu_ctrl  = ALU_ADD;
                branch_taken = 1'b0;
            end
        endcase
    end

endmodule
