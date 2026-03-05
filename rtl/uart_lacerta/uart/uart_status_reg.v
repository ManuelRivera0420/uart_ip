//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_status_reg
//
// Description:
// this module is used to store the status flags of the uart ip
//////////////////////////////////////////////////////////////////////////////////

module uart_status_reg(
	input wire clk,
	input wire arst_n,
	input wire recv_error,        // Receiver error
	input wire recv_busy,         // Receiver busy
	input wire tnsm_busy,         // Transmitter busy
	input wire recv_int,          // received data interrupt
	input wire [7:0] recv_data,   // received data
	input wire re,                // read enable
	input wire [11:0] rmask,      // read mask used for clear on read (when rmask bit === 1)
	output wire [11:0] status_data // Status output data
);

reg [11:0] reg_;
integer idx;

always@(posedge clk, negedge arst_n) begin
	if(!arst_n) begin
		reg_ <= 12'd0;
	end else begin
		// clear on read logic
		if(re) begin
			for(idx = 0; idx < 12; idx = idx + 1) begin
				reg_[idx] <= rmask[idx] ? 1'b0 : reg_[idx];
			end
		end

		// receiver error flag has priority over clear on read
		if(recv_error)
			reg_[11] <= recv_error;

			reg_[10] <= recv_busy;
			reg_[9] <= tnsm_busy;

		// receiver new packet flag has priority over clear on read
		if(recv_int) begin
			reg_[8] <= 1'b1;
			reg_[7:0] <= recv_data;
		end
	end
end

assign status_data = reg_ & ~({12{re}} & rmask); // we combinationaly mask the status output data if the clear on read will happen on the status flops

endmodule
