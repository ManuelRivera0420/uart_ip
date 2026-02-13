module fv_uart_recv(
    input clk,
    input arst_n,
    input active,
    input rx,
    input rx_negedge_det,
    input [1:0] frame_type,  // 2'b00 : 5 bits, 2'b01 : 6 bits, 2'b10 : 7 bits, 2'b11 : 8 bits
    input [1:0] parity_type, // 2'b00 : no parity, 2'b01: even parity, 2'b10: odd parity, 2'b11: no parity
    input stop_type,         // 1'b0 : 1 stop bit, 1'b1 : 2 stop bits
    input recv_clk_en,
    input logic [7:0] data,
    input logic recv,
    input logic error,
    input logic busy
);

`define RECEIVER uart_recv

`AST(UART_RECV, receiver_not_starting_when_active_is_low,
    !(active) |->,
    (`RECEIVER.state == STATE_RECV_IDLE)
)

`AST(UART_RECV, receiver_starts_when_active_and_negedge_detected,
    ((active) && $rose((rx_negedge_det)) && (`RECEIVER.state == STATE_RECV_IDLE)) |=>,
    (`RECEIVER.state == STATE_RECV_START)
)

`AST(UART_RECV, receiver_busy_when_not_idle,
    (busy) |->,
    (`RECEIVER.state != STATE_RECV_IDLE)
)

`AST(UART_RECV, when_reset_not_busy,
    !arst_n |->,
    !busy
)

`AST(UART_RECV, if_recv_not_busy_anymore,
    recv |->,
    !busy
)

`AST(UART_RECV, recv_is_active_one_cycle,
    recv |-> ##1,
    !recv
)

`COV(UART_RECV, is_busy, , busy)

`COV(UART_RECV, recv_data, , recv)

`COV(UART_RECV, was_active, , active)

`COV(UART_RECV, negedge_detected, , rx_negedge_det)

`COV(UART_RECV, stop_type_s, , stop_type)

`COV(UART_RECV, busy_then_recv, $rose(busy) |->, ##[0:$] recv |-> ##[0:$] !busy)

covergroup all_flags_cg @(posedge clk);
    option.per_instance = 1;
    busy: coverpoint busy;
    recv: coverpoint recv;
    active: coverpoint active;
    rx_negedge_det: coverpoint rx_negedge_det;
    stop_type: coverpoint stop_type;
    frame_type: coverpoint frame_type {bins frame_type_bins [] = {[0:1]}; }
    parity_type: coverpoint parity_type {bins parity_type_bins [] = {[0:1]}; }
endgroup: all_flags_cg

all_flags_cg all_flags_cg_i = new();

endmodule:fv_uart_recv

bind uart_recv fv_uart_recv fv_uart_recv_inst (.*);

