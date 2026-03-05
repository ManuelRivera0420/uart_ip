//*****************************************
// Memory array
//*****************************************

module cell_array (
	input  real row_wr [0:ROWS-1],				//Each row has an enable to save the word
	input  real bl_wr [0:0][0:COLS-1],			//Each column has a right bit line, and it is shared with the others rows
	input  real blb_wr [0:0][0:COLS-1],			//Each column has a left bit line, and it is shared with the others rows
	output  real bl_rd [0:ROWS-1][0:COLS-1],	//Each bit in the memory array must be had a single right bit line
	output  real blb_rd [0:ROWS-1][0:COLS-1]	//Each bit in the memory array must be had a single left bit line
);

//   ________________________________
//  |              VDD   |    VSS    |
//  |--------------------------------|
//  |Typ Voltage|  1.5   |    0.0    |
//  |________________________________|

const real VDD =  1.5;
const real VSS =  0.0;
const real VTH =  0.8;

	// Real to logic converter of value of the row selected
	logic [ROWS-1:0] l_wr;
	genvar a;
	generate
		for (a=0;a<ROWS;a++) begin: LASSIGN
			assign l_wr [a] = row_wr [a] >= VTH ? 1'b1 : 1'b0;
		end
	endgenerate

	//Rows and columns variables
	genvar r,c;
	//Generate memory array
	generate
		for(r=0;r<ROWS;r++) begin: ROW
			for(c=0;c<COLS;c++) begin: COL
				sram_cell cell1(
				.row_wr (row_wr[r]),
				.bl_wr (bl_wr [0][c]),
				.blb_wr (blb_wr [0][c]),
				.bl_rd (bl_rd [r][c]),
				.blb_rd (blb_rd [r][c])
				);
			end
		end
	endgenerate

endmodule
