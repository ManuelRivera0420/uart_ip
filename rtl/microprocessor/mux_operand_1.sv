`timescale 1ns / 1ps
//------------------------------------------------------------------------------
// Module: mux_operand_1
// Description:
//   Write-back data multiplexer for the CPU datapath. Selects the value
//   to be written into the register file based on control logic.
//
// Inputs:
//   - data_out_to_pc     : PC-related value.
//   - alu_to_mem_addr   : ALU computation result or address.
//   - data_out_to_mux   : Data read from memory or auxiliary datapath.
//
// Control:
//   - sel is driven by the control unit and encoded in defines.svh.
//
// Notes:
//   - Selection logic only; no arithmetic is performed.
//   - sel encodings are expected to be mutually exclusive.
//------------------------------------------------------------------------------
module mux_operand_1 (
    input logic [31:0]	in1,
    input logic [31:0]	in2,
    input logic [31:0]	in3,
    input logic [1:0]	  sel,
    output logic [31:0]	data_out
    );

always_comb begin   
    unique case (sel)
        2'b00: begin	
            data_out = in1;	//Zero to operand_1
        end
        2'b01: begin 
            data_out = in2;	//PC to operand_1
        end
        2'b10: begin
            data_out = in3;	// rs1 to operand_1
        end
        default: data_out = '0;
    endcase
end
endmodule

