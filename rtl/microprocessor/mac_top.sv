/*******************************************************************************
 * NIVEL 1: TOP LEVEL - UNIDAD MAC COMPLETA
 * Este módulo integra el Multiplicador de Booth y la Unidad de Acumulación.
 ******************************************************************************/
`timescale 1ns/1ps
module mac_top (
    input logic clk, rst_n, start,
    input logic signed [`MAC_DATA_WIDTH-1:0] m_in, q_in,
    output logic signed  [`MAC_ACC_WIDTH:0] product,
    output logic ready
);
    logic signed [`MAC_ACC_WIDTH-1:0] internal_product;
    logic mult_done;

    booth_multiplier multiplicador_inst (
        .clk(clk), .rst_n(rst_n), .start(start),
        .m_in(m_in), .q_in(q_in),
        .result(internal_product), .ready(mult_done) 
    );

    accumulator_unit acumulador_inst (
        .clk(clk), .rst_n(rst_n), .acc_en(mult_done),
        .product_in(internal_product), 
        .acc_out(product)
    );

    assign ready = mult_done;
endmodule
