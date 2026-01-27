`timescale 1ns/1ps;

module uart_clk_gen_tb();

bit clk;
bit arst_n;
logic active;
logic [3:0] baud_rate;
logic tx_clk_en;
logic rx_clk_en;

always #10ns clk = ~clk;

time bit_time;

initial begin
    active = 1'b0;
    baud_rate = '0;
    #50ns;
    arst_n = 1'b1;
    @(posedge clk);
    baud_rate = 4'd0;
    active = 1'b1;
    @(posedge clk)
    repeat(16) begin
        bit_time = 1s / (clk_gen_i.BAUD_RATES[baud_rate]);
        #bit_time;
        std::randomize(baud_rate);
        #(5*bit_time);
        @(posedge clk);
        baud_rate = baud_rate + 1'b1;
        arst_n = 1'b0;
        #bit_time;
        @(posedge clk);
        arst_n = 1'b1;
    end
    #10ms;
    $finish;
end

time t_tx1, t_tx2, t_rx1, t_rx2;
time period_tx, period_rx;

initial begin
    period_tx = 0;
    period_rx = 0;
end

always begin
     @(posedge tx_clk_en);
     t_tx1 = $time;
     @(posedge tx_clk_en);
     t_tx2 = $time;
     period_tx = t_tx2 - t_tx1;
end

always begin
    @(posedge rx_clk_en);
    t_rx1 = $time;
    @(posedge rx_clk_en);
    t_rx2 = $time;
    period_rx = t_rx2 - t_rx1;
end

clk_gen clk_gen_i(
	.clk(clk),
	.arst_n(arst_n),
	.active(active),
	.baud_rate(baud_rate),
	.tx_clk_en(tx_clk_en),
    .rx_clk_en(rx_clk_en)
);

logic [3:0] cnt;
always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        cnt <= '0;
    end else begin
        if(clk_gen_i.rx_clk_en) begin
            cnt <= cnt + 1'b1;
        end
    end
end

endmodule
