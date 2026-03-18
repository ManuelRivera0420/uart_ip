module wb_gpio#(
    parameter AW = 16,
    parameter DW = 32
)(
    input logic clk,
    input logic rst_n,
    input logic [AW - 1 : 0] wbs_adr_i,
    input logic [DW - 1 : 0] wbs_dat_i,
    output logic [DW - 1 : 0] wbs_dat_o,
    input logic wbs_we_i,
    input logic [3 : 0] wbs_sel_i,
    input logic wbs_stb_i,
    input logic wbs_cyc_i,
    output logic wbs_ack_o,
    output logic wbs_err_o,
    output logic [7:0] gpios_out
);
    
    logic [7:0] leds_output;
    logic [7:0] gpios_out_reg;
    logic active;

    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            wbs_ack_o <= 1'b0;
            wbs_dat_o <= '0;
            leds_output <= '0;
            active <= 1'b0;
        end else begin
            wbs_ack_o <= 1'b0;

            if(wbs_cyc_i && wbs_stb_i && !wbs_ack_o) begin
                wbs_ack_o <= 1'b1;

                if(wbs_we_i) begin
                    leds_output <= wbs_dat_i[7:0];
                    active <= wbs_dat_i[DW - 1];
                end else begin
                    wbs_dat_o <= {active, 23'd0, leds_output};
                end
            end
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            gpios_out_reg <= '0;
        end else if(active) begin
            gpios_out_reg <= leds_output;
        end else begin
            gpios_out_reg <= '0;
        end
    end

    assign gpios_out = gpios_out_reg;
    assign wbs_err_o = 1'b0;

endmodule
