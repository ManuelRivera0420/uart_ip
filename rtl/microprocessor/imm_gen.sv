`timescale 1ns / 1ps
import riscv_params_pkg::*;
//------------------------------------------------------------------------------
// Module: imm_gen
// Description:
//   RISC-V RV32I immediate generator. Extracts and sign/zero-extends the
//   immediate field from a 32-bit instruction according to imm_sel.
//
// Assumptions:
//   - instr is a valid RV32I instruction word.
//   - imm_sel is provided by the control unit and selects the immediate format:
//       IMM_I: I-type   (sign-extended 12-bit immediate)
//       IMM_S: S-type   (sign-extended 12-bit store immediate)
//       IMM_B: B-type   (sign-extended branch offset, LSB forced to 0)
//       IMM_U: U-type   (upper immediate, lower 12 bits are 0)
//       IMM_J: J-type   (sign-extended jump offset, LSB forced to 0)
//
// Notes:
//   - Branch/jump immediates are instruction-aligned; therefore bit[0] is 0.
//   - This block performs field extraction/extension only. Target address
//     computation (PC + imm) is performed elsewhere.
//------------------------------------------------------------------------------
module imm_gen(
    input  logic [31:0] instr,
    input  logic [2:0]  imm_sel,
    output logic [31:0] imm_out
);

    always_comb begin
        imm_out = '0; // default

        unique case (imm_sel)

            // I-type immediate: imm[11:0] = instr[31:20], sign-extended to 32b
            IMM_I: imm_out = {{20{instr[31]}}, instr[31:20]};

            // S-type immediate: imm[11:5]=instr[31:25], imm[4:0]=instr[11:7], sign-extended
            IMM_S: imm_out = {{20{instr[31]}}, instr[31:25], instr[11:7]};

            // B-type immediate (branch offset):
            // imm[12]=instr[31], imm[11]=instr[7], imm[10:5]=instr[30:25], imm[4:1]=instr[11:8], imm[0]=0
            IMM_B: imm_out = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};

            // U-type immediate: imm[31:12]=instr[31:12], lower 12 bits are zero
            IMM_U: imm_out = {instr[31:12], 12'b0};

            // J-type immediate (jump offset):
            // imm[20]=instr[31], imm[19:12]=instr[19:12], imm[11]=instr[20], imm[10:1]=instr[30:21], imm[0]=0
            IMM_J: imm_out = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};

            default: imm_out = '0;
        endcase
    end

endmodule

