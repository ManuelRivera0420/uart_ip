`timescale 1ns / 1ps
//------------------------------------------------------------------------------
// Module: mux
// Description:
//   Parameterized 2-to-1 combinational multiplexer.
//
// Assumptions:
//   - sel is a stable control signal.
//   - in1 and in2 have the same width (WIDTH).
//
// Notes:
//   - When sel = 0, output selects in2.
//   - When sel = 1, output selects in1.
//------------------------------------------------------------------------------
module mux #(
    parameter int WIDTH = 32
)(
    input  logic [WIDTH-1:0] in1,
    input  logic [WIDTH-1:0] in2,
    input  logic             sel,
    output logic [WIDTH-1:0] out
);

    // sel = 0 -> in2
    // sel = 1 -> in1
    assign out = sel ? in1 : in2;

endmodule

