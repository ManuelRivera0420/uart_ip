`timescale 1ns / 1ps
import riscv_params_pkg::*;
//------------------------------------------------------------------------------
// Module: alu
// Description:
//   RV32I ALU. Produces DATA_WIDTH-wide results for arithmetic/logic operations.
//   "Set" operations (EQ/SLT/SLTU) return 0x0 or 0x1 (LSB=1, others 0).
//
// Assumptions:
//   - alucontrol encoding is defined in defines.svh.
//   - Shift amount follows RV32I semantics (shamt = operand2[4:0]).
// Notes:
//   - Width casts are explicit to avoid implicit 1-bit to DATA_WIDTH expansion.
//------------------------------------------------------------------------------

module alu #(
	parameter OPERAND_WIDTH = 32
)(
	input logic [OPERAND_WIDTH-1:0]     operand1,    // First operand, sourced from a register 
	input logic [OPERAND_WIDTH-1:0]     operand2,    // Second operand sourced from a register
	input logic [3:0]		            alucontrol,  // Use 4 bits for the opcode at the moment 
	output logic [OPERAND_WIDTH-1:0]	alu_result   // ALU result, destiny is another register
    );


    
    //logic [4:0] shamt;	
    //assign shamt = operand2[4:0];

    always_comb begin
        unique case(alucontrol)
            ALU_ADD: begin  
                alu_result = operand1 + operand2;
            end
            ALU_SUB: begin
                alu_result = operand1 - operand2;
            end
            ALU_AND: begin
                alu_result = operand1 & operand2;
            end
            ALU_OR: begin
                alu_result = operand1 | operand2;
            end
            ALU_XOR: begin
                alu_result = operand1 ^ operand2;
            end
	    //------------------------------------------------------------------------------
	    //results zero-extended 
	    //------------------------------------------------------------------------------
            ALU_EQ: begin
                alu_result = OPERAND_WIDTH'(operand1 == operand2);
            end
            ALU_SLT: begin 
		        alu_result = OPERAND_WIDTH'($signed(operand1) < $signed(operand2));
            end
            ALU_SLTU: begin
                alu_result = OPERAND_WIDTH'(operand1 < operand2);
            end
            ALU_SLL: begin
                alu_result = operand1 << operand2[4:0];
            end
            ALU_SRL: begin
                alu_result = operand1 >> operand2[4:0];
            end
            ALU_SRA: begin
                alu_result = $signed(operand1) >>> operand2[4:0];
	    end
            // Send zero as a default case
            default: alu_result = '0;
        endcase
    end
endmodule


