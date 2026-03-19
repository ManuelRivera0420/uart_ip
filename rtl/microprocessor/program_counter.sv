`timescale 1ns / 1ps
//------------------------------------------------------------------------------
// Module: program_counter
// Description:
//   Program counter (PC) register. Captures the next PC value on each rising
//   clock edge and provides the current PC to the instruction fetch path.
//
// Assumptions:
//    - arst_n is an active-low asynchronous reset.
//
// Notes:
//   - Reset initializes PC to 0x0000_0000.
//   - This block is purely sequential storage; PC update selection is handled
//     elsewhere in the datapath/control.
//------------------------------------------------------------------------------
module program_counter #(	
	parameter DATA_WIDTH = 32,
	parameter [DATA_WIDTH-1:0] RESET_PC = '0
)(
	input logic                     clk,
	input logic                     arst_n,
  input logic                     pc_en,
	input logic  [DATA_WIDTH - 1:0] pc_in,
	output logic [DATA_WIDTH - 1:0] pc_out
);
    //Secuential logic 
    always_ff @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            pc_out <= RESET_PC; //Reset PC to boot address
        end else if (pc_en)  begin   
            pc_out <= pc_in;
       end
    end
endmodule
