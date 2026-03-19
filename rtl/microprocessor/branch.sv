`timescale 1ns / 1ps
import riscv_params_pkg::*;
//------------------------------------------------------------------------------
// Module: branch
// Description:
//   Branch decision logic for equality-based branch instructions.
//   Determines whether a branch should be taken based on register comparison.
//
// Assumptions:
//   - rs_1 and rs_2 are valid register operands provided by the register file.
//   - This module currently supports equality comparison only (BEQ).
//
// Notes:
//   - Branch type decoding (BEQ/BNE/BLT/etc.) is expected to be handled
//     by the control unit or extended logic.
//   - This block performs comparison only; branch target calculation
//     is handled elsewhere.
//------------------------------------------------------------------------------

module branch #(parameter DATA_WIDTH_BRANCH = 32)(
    input logic [DATA_WIDTH_BRANCH - 1: 0]	rs_1,
    input logic [DATA_WIDTH_BRANCH - 1: 0]	rs_2,
    input logic [6:0]               opcode,
    input logic [2:0]               funct_3,        
    output logic			        branch_taken
    );

    always_comb begin 
    branch_taken = 1'b0;
        if (opcode == OPCODE_B_TYPE) begin 
            unique case (funct_3)
                F3_BEQ: begin 
                    branch_taken = (rs_1 == rs_2);
                end
                F3_BNE: begin 
                    branch_taken = (rs_1 != rs_2);
                end
                F3_BLT: begin 
                    branch_taken = ($signed(rs_1) < $signed(rs_2));
                end
                F3_BGE: begin 
                    branch_taken = ($signed(rs_1) >= $signed(rs_2));
                end
                F3_BLTU: begin 
                    branch_taken = (rs_1 < rs_2);
                end
                F3_BGEU: begin 
                    branch_taken = (rs_1 >= rs_2);
                end
                default: begin 
                    branch_taken = 1'b0;
                end
            endcase
        end else begin
            branch_taken = 1'b0; 
        end
    end   
endmodule
