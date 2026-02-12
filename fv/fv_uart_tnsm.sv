module fv_uart_tnsm(
    input clk,
    input arst_n,
    input active,
    input tnsm,
    input [7:0] data,
    input [1:0] frame_type,
    input [1:0] parity_type,
    input stop_type,
    input tnsm_clk_en,
    input logic busy,
    input logic tnsm_clr,
    input logic tx
);

`define TRANSMITTER fv_uart_tnsm_inst

`AST(UART_TX, tx_startbit,
    $rose(tnsm && active && tnsm_clk_en) && !busy |=>,
    !(tx)
)

`AST(UART_TX, tx_idle,
    (!busy) |->,
    (tx)
)

`AST(UART_TX, tx_idle_when_active_is_low,
    !(active) |->,
    (uart_tnsm.state == STATE_TNSM_IDLE)
)

`AST(UART_TX, tx_high_when_stop_bit_state,
    ((uart_tnsm.state == STATE_TNSM_STOP1) || (uart_tnsm.state == STATE_TNSM_STOP2)) |->,
    (tx)
)

`AST(UART_TX, tx_not_busy_when_reset,
    (!arst_n) |->,
    !busy
)

`AST(UART_TX, tx_busy_when_tnsm,
    $rose(tnsm && active && tnsm_clk_en) && !busy |-> ##1,
    (busy)
)

`COV(UART_TX, tx_busy, , busy)

`COV(UART_TX, tx_active, , active)

`COV(UART_TX, tnsm_set, , tnsm)

`COV(UART_TX, tnsm_stop_type, , stop_type)

covergroup tx_signals_cg @(posedge clk);
	option.per_instance = 1;
	busy: coverpoint busy;
	active: coverpoint active;
	tnsm: coverpoint tnsm;
	stop_type: coverpoint stop_type;
endgroup: tx_signals_cg

tx_signals_cg tx_signals_cg_i = new();

endmodule:fv_uart_tnsm

bind uart_tnsm fv_uart_tnsm fv_uart_tnsm_inst (.*);

