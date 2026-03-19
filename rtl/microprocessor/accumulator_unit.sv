`timescale 1ns/1ps

module accumulator_unit (
    input  logic clk, rst_n, acc_en,
    input  logic signed [2*`MAC_DATA_WIDTH-1:0] product_in,
    output logic signed [`MAC_ACC_WIDTH:0] acc_out
);
    logic [`MAC_ACC_WIDTH:0] current_sum, acc_reg;
    logic [`MAC_ACC_WIDTH:0] product_ext;

    // Extensión de signo segura (toma el bit MSB del producto)
    assign product_ext = product_in;

    // Instancia del sumador de 40 bits
    adder_40bit mac_adder (.a(product_ext), .b(acc_reg), .sum(current_sum));

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)         acc_reg <= '0;
        else if (acc_en)    acc_reg <= current_sum;
    end

    assign acc_out = acc_reg;
endmodule
