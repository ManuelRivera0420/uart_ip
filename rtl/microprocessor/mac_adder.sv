`timescale 1ns/1ps

module adder_40bit (
    input  logic signed [`MAC_ACC_WIDTH:0] a,
    input  logic signed [`MAC_ACC_WIDTH:0] b,
    output logic signed [`MAC_ACC_WIDTH:0] sum
);
    assign sum = a + b;
endmodule