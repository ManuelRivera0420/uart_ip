`timescale 1ns/1ps

module booth_datapath (
    input  logic clk, rst_n,
    input  logic [`MAC_DATA_WIDTH-1:0] m_in, q_in,
    input  logic load, shift, op_sel,
    output logic [2*`MAC_ACC_WIDTH-1:0] product
);
    logic signed [`MAC_DATA_WIDTH-1:0] A, M;
    logic [`MAC_DATA_WIDTH-1:0] Q;
    logic q_prev;

    // ALU DE 18 BITS (Para evitar el desbordamiento del signo)
    logic signed [`MAC_DATA_WIDTH+1:0] ext_A;
    logic signed [`MAC_DATA_WIDTH+1:0] ext_M;
    logic signed [`MAC_DATA_WIDTH+1:0] alu_out;
    
    // Extendemos el signo copiando el bit más significativo (MSB) DOS VECES
    assign ext_A = {{2{A[`MAC_DATA_WIDTH-1]}}, A};
    assign ext_M = {{2{M[`MAC_DATA_WIDTH-1]}}, M};

    // Multiplexor de suma/resta (Pura combinacional)
    always_comb begin
        case ({Q[1], Q[0], q_prev})
            3'b001, 3'b010: alu_out = ext_A + ext_M;
            3'b101, 3'b110: alu_out = ext_A - ext_M;
            3'b011:         alu_out = ext_A + (ext_M <<< 1);
            3'b100:         alu_out = ext_A - (ext_M <<< 1);
            default:        alu_out = ext_A;
        endcase
    end

    // SHIFT DE 34 BITS
    // Unimos los 18 bits de la ALU, los 16 de Q y 1 de q_prev = 35 bits
    logic signed [`MAC_ACC_WIDTH+2:0] shift_reg;
    assign shift_reg = {alu_out, Q, q_prev};

    // REGISTROS SECUENCIALES ---
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            {A, Q, q_prev} <= '0;
            M <= '0;
        end else if (load) begin
            A <= '0;
            M <= m_in;
            Q <= q_in;
            q_prev <= 1'b0;
        end else if (op_sel && shift) begin
            // Shift aritmético seguro. 
            // Tomamos los 33 bits inferiores [32:0] para guardarlos en {A, Q, q_prev}
            {A, Q, q_prev} <= (shift_reg >>> 2); 
        end
    end

    assign product = {A, Q};

endmodule