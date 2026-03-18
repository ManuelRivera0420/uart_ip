//************************************************************************
// Module top of sram arquitecture for integration proyect using wishbone
//************************************************************************

`timescale 1ns/1ps

module wb_sram (
	input logic clk,
	input logic rst_n,

	// ---- Wishbone slave port ----
	input  logic [AW-1:0]   wbs_adr_i,
	input  logic [DW-1:0]   wbs_dat_i,
	output logic [DW-1:0]   wbs_dat_o,
	input  logic             wbs_we_i,
	input  logic [3:0]       wbs_sel_i,
	input  logic             wbs_stb_i,
	input  logic             wbs_cyc_i,
	output logic             wbs_ack_o,
	output logic             wbs_err_o
);

	logic [DW-1:0] dat_input;
	logic [DW-1:0] dat_output;
	logic valid;

	sram_ip slave_sram(
	.data_in (dat_input),		//Data input
	.w_en (wbs_we_i),					//Write enable
	.r_en (!wbs_we_i),					//Read enable
	.addr (wbs_adr_i),	//Address of the row in memory array
	.data_valid (valid),			//When is enable, shows that the data in the output is the value readed
	.data_out (dat_output)		//Shows the data readed
	);



	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			wbs_ack_o <= 1'b0;
			wbs_dat_o <= '0;
		end else begin
			wbs_ack_o <= 1'b0;   // default: no ack

			if (wbs_cyc_i && wbs_stb_i && !wbs_ack_o) begin
				wbs_ack_o <= 1'b1;

				if (wbs_we_i) begin
					dat_input <= wbs_dat_i;
				end else begin
					wbs_dat_o <= dat_output;
				end
			end
		end
	end

	assign wbs_err_o = 1'b0;

endmodule
