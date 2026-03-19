`timescale 1ns / 1ps
//-------------------------------------------------------------------------------
//Module: adder
//Description
//	Computes the next instruction address by adding +4 or +2 to the
//	current instrucction address.
//
//Assumptions: 
//	-constant_operant represent a small unsigned increment +4 or +2
//	-constant_operand is zero-extended to DATA_WIDTH before addition 
//-------------------------------------------------------------------------------
module adder # (parameter DATA_WIDTH = 32)(
    input logic [2:0] constant_operand,
    input logic [DATA_WIDTH - 1:0] instruction_addr,
    output logic [DATA_WIDTH - 1:0] next_instruction 
    );
    //width cast to avoid implicit width expansion during addition 
    assign next_instruction = instruction_addr + DATA_WIDTH'(constant_operand);
endmodule
