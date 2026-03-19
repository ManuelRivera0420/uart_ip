`timescale 1ns/1ps

module booth_fsm (
    input  logic clk, rst_n, start,
    output logic load, shift, op_sel, ready
);
    typedef enum logic [1:0] {IDLE, LOAD, CALC, DONE} state_t;
    state_t state, next_state;
    logic [$clog2(`MAC_DATA_WIDTH)-1:0] bit_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= IDLE;
            bit_cnt <= '0;
        end else begin
            state <= next_state;
            if (state == CALC) bit_cnt <= bit_cnt + 1'b1;
            else if (state == IDLE) bit_cnt <= '0;
        end
    end

    always_comb begin
        {load, shift, op_sel, ready} = '0;
        case (state)
            IDLE: next_state = start ? LOAD : IDLE;
            LOAD: begin
                load = 1'b1;
                next_state = CALC;
            end
            CALC: begin
                op_sel = 1'b1;
                shift  = 1'b1;
                // Condición Radix-4: DATA_WIDTH / 2
                next_state = (bit_cnt == (`MAC_DATA_WIDTH/2)-1) ? DONE : CALC;
            end
            DONE: begin
                ready = 1'b1;
                next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end
endmodule
