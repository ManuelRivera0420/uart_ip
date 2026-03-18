//*****************************************
// Array of differential amplifiers
//*****************************************

module sense_amp(
	input  real row_rd [0:ROWS-1],				//The row selected enables only the amplifiers of selected row
	input  real bl_rd [0:ROWS-1][0:COLS-1],		//Right bit lines to be compared
	input  real blb_rd [0:ROWS-1][0:COLS-1],	//Left bit lines to be compared
	output real preout [0:0][0:COLS-1]			//Shows the data readed
);

//   ________________________________
//  |              VDD   |    VSS    |
//  |--------------------------------|
//  |Typ Voltage|  1.5   |    0.0    |
//  |________________________________|

const real VDD =  1.5;
const real VSS =  0.0;
const real VTH =  0.8;

//Real to logic convertion of selector
	logic [ROWS-1:0] row_sensed;
	genvar s;
	generate
		for(s=0;s<ROWS;s++) begin: SEL1
			assign row_sensed [s] = row_rd [s] >= VTH ? 1'b1 : 1'b0;
		end
	endgenerate

//Real data stored assignment to logic
	logic data_mem [0:ROWS-1][0:COLS-1];
	genvar r,c;
	generate
		for(r=0;r<ROWS;r++) begin: ROW1
			for(c=0;c<COLS;c++) begin: COL1
				assign data_mem [r] [c]= (bl_rd [r][c] >= VTH) & (blb_rd [r][c] < VTH) ? 1'b1 : ((bl_rd [r][c] < VTH) & (blb_rd [r][c] >= VTH) ? 1'b0 : 'z);
			end
		end
	endgenerate

//Select data to show
	logic data_sensed [0:0] [0:COLS-1];
	genvar i;
	generate
		for(i=0;i<COLS;i++) begin: COL2
			assign data_sensed [0] [i]= data_mem [($clog2(row_sensed))][i];
		end
	endgenerate

//Logic to real assignment
	genvar c_o;
	generate
		for(c_o=0;c_o<COLS;c_o++) begin: COL3
			assign preout [0][c_o]= data_sensed [0][c_o] == 1'b1 ? VDD : VSS;
		end
	endgenerate

endmodule
