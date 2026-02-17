module fv_uart_clk_gen(
    input logic clk,
    input logic arst_n,
    input logic active,
    input logic [3:0] baud_rate,
    input logic tx_clk_en,
    input logic rx_clk_en
);

localparam int N_FBAUDS = 5208;
localparam int N_SBAUDS = 500_000;

`AST (UART_CLK_GEN, clk_not_active, 
    !active && $past(!active) |->,
    (!tx_clk_en && !rx_clk_en)
)

`AST (UART_CLK_GEN, reset_disables_all,
    !arst_n |->,
    (!tx_clk_en && !rx_clk_en)
)

`AST (UART_CLK_GEN, rx_en_one_cycle,
    $rose(rx_clk_en) |->,
    rx_clk_en ##1 !rx_clk_en
)

`AST (UART_CLK_GEN, tx_en_one_cycle,
    $rose(tx_clk_en) |->,
    tx_clk_en ##1 !tx_clk_en
)

`AST (UART_CLK_GEN, active_fall_disables_en,
    $fell(active) |=>,
    (!tx_clk_en && !rx_clk_en)
)


`COV (UART_CLK_GEN, was_active, , active)

`COV (UART_CLK_GEN, tx_clk_was_set, , tx_clk_en)

`COV (UART_CLK_GEN, rx_clk_was_set, , rx_clk_en)

covergroup clk_gen_active_cg @(posedge clk iff arst_n);
    option.per_instance = 1;
    active: coverpoint active;
    tx_clk_en: coverpoint tx_clk_en;
    rx_clk_en: coverpoint rx_clk_en;
    baud_rate: coverpoint baud_rate;

    active_all_bauds: cross active, baud_rate;
endgroup: clk_gen_active_cg

clk_gen_active_cg clk_gen_active_cg_i = new();

endmodule

bind clk_gen fv_uart_clk_gen fv_uart_clk_gen_inst (.*);

