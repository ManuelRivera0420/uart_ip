//*****************************************
// Shift register
// Serial Input, Parallel Output
//*****************************************

module sipo(
	input logic clk,						//Clock signal
	input logic arst_n,						//Reset signal, enable when its false (0)
	input logic serial_in,					//Pin of serial data reception 
	input logic load,						//When is enable, the data captured is show in the Parallel Output
	input logic shift,						//When is enable, the shift register captures the value in the pin serial_in
	output logic [COLS-1:0] parallel_out	//Shows the data captured by the shift register
	);

	logic [COLS-1:0] shift_reg;		//Shift register declaration

	always_ff@(posedge clk, negedge arst_n) begin
		if(!arst_n) begin
			shift_reg <= '0;		//Reset clear the shift register
		end else begin
			if(shift)				//When shift, capture the serial_in value
				shift_reg <= {shift_reg, serial_in};
			else if(load)			//When load, show the shift register in the output
				parallel_out <= shift_reg;
		end
	end

endmodule