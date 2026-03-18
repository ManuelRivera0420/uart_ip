//*****************************************
// Memory cell
//*****************************************

module sram_cell (
	input  real row_wr,	// When is enable, the data is writed in the cell
	input  real bl_wr,	// Used to write the right bit line 
	input  real blb_wr,	// Used to write the left bit line
	output real bl_rd,	// Is the value of the writed right bit line
	output real blb_rd	// Is the value of the writed left bit line
);

//   ________________________________
//  |              VDD   |    VSS    |
//  |--------------------------------|
//  |Typ Voltage|  1.5   |    0.0    |
//  |________________________________|

const real VDD =  1.5;
const real VSS =  0.0;
const real VTH =  0.8; 

	always_comb begin
		if (row_wr >= VTH) begin
			bl_rd = bl_wr;
			blb_rd = blb_wr;
		end else begin
			bl_rd = bl_rd;
			blb_rd = blb_rd;
		end
	end

endmodule
