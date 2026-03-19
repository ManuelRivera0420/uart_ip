`timescale 1ns / 1ps
//------------------------------------------------------------------------------------------
//Module: plus_4_or_2_mux
//Description:
//	Selects the instruction address increment value based on control
//	logic.
//	The output represents a small unsigned constant used to advance the
//	PC. 
//
//Assumptions:
//	- sel is driven by the control unit 
//	- sel = 0 selects a +4 increment 
//	- sel = 1 selects a +2 increment 
//
//Notes:
//	- this module only selects the increment value; the actual addition is
//	performed elsewhere in the datapath.
//------------------------------------------------------------------------------------------

module plus_4_or_2_mux(
    input logic sel,
    output logic [2:0] instruction_add
    );
    
always_comb begin   
    case (sel)
        1'b0: begin 
            instruction_add = 3'b100; // +4 increment
        end
        1'b1: begin 
            instruction_add = 3'b010; // +2 increment 
        end
        default: instruction_add = 3'b000;
    endcase
end
endmodule
