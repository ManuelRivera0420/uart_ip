//*****************************************
// Decoder
// One Hot
//*****************************************

module decoder (
	input logic enable,						//When its enable, the output shows the row selected in (1) and the others in (0)
	input  real row_sel [0:$clog2(ROWS)-1],	//Address to select the row
	output real row_out [0:ROWS-1]			//Output of onehot decoder
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
	logic [$clog2(ROWS)-1:0] row_selected;
	genvar s;
	generate
		for(s=0;s<($clog2(ROWS));s++) begin: SEL1
			assign row_selected [s] = row_sel [s] >= VTH ? 1'b1 : 1'b0;
		end
	endgenerate

//Onehot decoder
	logic [ROWS-1:0] row;
	assign row = enable ? '0 + (1'b1 << (row_selected)) : '0;
	
//Logic to real convertion
	genvar o;
	generate
		for(o=0;o<ROWS;o++) begin: OUT1
			assign row_out [o] = row [o] == 1'b1 ? VDD : VSS;
		end
	endgenerate

endmodule
