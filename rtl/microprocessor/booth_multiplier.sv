`timescale 1ns/1ps

module booth_multiplier (
    input  logic clk, rst_n, start,
    input  logic [`MAC_DATA_WIDTH-1:0] m_in, q_in,
    output logic [`MAC_ACC_WIDTH-1:0] result,
    output logic ready
);
    // Señales de interconexión interna
    logic load, shift, op_sel;

    // Instancia de la FSM (Unidad de Control)
    booth_fsm control_unit (
        .clk(clk), .rst_n(rst_n), .start(start),
        .load(load), .shift(shift), .op_sel(op_sel), .ready(ready)
    );

    // Instancia del Datapath (Unidad Aritmética)
    booth_datapath arithmetic_unit (
        .clk(clk), .rst_n(rst_n), .m_in(m_in), .q_in(q_in),
        .load(load), .shift(shift), .op_sel(op_sel), .product(result)
    );
endmodule