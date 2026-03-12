`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
// 
// Design Name: uart_ip
// Module Name: uart_status_reg
//
//////////////////////////////////////////////////////////////////////////////////

module uart_status_reg(
    input clk,
    input arst_n,
    input recv_error,               // Receiver error
    input recv_busy,                // Receiver busy
    input tnsm_busy,                // Transmitter busy
    input recv_int,                 // received data interrupt
    input [7:0] recv_data,          // received data
    input re,                       // read enable
    input [11:0] rmask,             // read mask used for read on clear (when rmask bit === 1)
    output logic [11:0] status_data // Status output data
);

    logic [11:0] reg_;

    always_ff@(posedge clk, negedge arst_n) begin
        if(!arst_n) begin
            reg_ <= '0;
        end else begin
            if(re) begin
                for(int idx = 0; idx < 12; idx = idx + 1)
                    reg_[idx] <= rmask[idx] ? 1'b0 : reg_[idx];
            end
            if(recv_error)
                reg_[11] <= recv_error;
            reg_[10] <= recv_busy;
            reg_[9] <= tnsm_busy;
            if(recv_int) begin
                reg_[8] <= 1'b1;
                reg_[7:0] <= recv_data;
            end
        end
    end

	always_comb begin
		for(int idx = 0; idx < 12; idx = idx + 1)
			status_data[idx] = rmask[idx] && re ? 1'b0 : reg_[idx];
	end

endmodule: uart_status_reg
