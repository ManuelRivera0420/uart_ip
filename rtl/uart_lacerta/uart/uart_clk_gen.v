//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_clk_gen
//
// Description: 
// this module generates pulses on tx_clk_en, and rx_clk_en, to enable the
// synchronization of transmitter and receiver to the baud rate
//////////////////////////////////////////////////////////////////////////////////

module uart_clk_gen(
  input wire clk,
  input wire arst_n,
  input wire active,         // uart ip is active, this comes from control register
  input wire [3:0] baud_rate,// selection baud rate, comes from control register
  output wire tx_clk_en,      // enabling pulse for transmitter
  output wire rx_clk_en       // enabling pulse for receiver
);

localparam TX_CNT_SIZE = $clog2((CLOCK_FREQUENCY / 200) - 1); // using 200 bps as this is the longest period
localparam RX_CNT_SIZE = $clog2(((CLOCK_FREQUENCY / 200) >> 4) - 1); // using 200 bps as this is the longest period
reg [TX_CNT_SIZE - 1 : 0] baud_counter_target; // using TX_CNT_SIZE as it is the largest
reg [TX_CNT_SIZE - 1 : 0] tx_clk_cnt;
reg [RX_CNT_SIZE - 1 : 0] rx_clk_cnt;

always @(*) begin
  case(baud_rate) // subtracting 1, as counters below starts at 0
    4'd0: baud_counter_target = (CLOCK_FREQUENCY / 200) - 1;      // 200 bps
    4'd1: baud_counter_target = (CLOCK_FREQUENCY / 300) - 1;      // 300 bps
    4'd2: baud_counter_target = (CLOCK_FREQUENCY / 600) - 1;      // 600 bps
    4'd3: baud_counter_target = (CLOCK_FREQUENCY / 1200) - 1;     // 1200 bps
    4'd4: baud_counter_target = (CLOCK_FREQUENCY / 1800) - 1;     // 1800 bps
    4'd5: baud_counter_target = (CLOCK_FREQUENCY / 2400) - 1;     // 2400 bps
    4'd6: baud_counter_target = (CLOCK_FREQUENCY / 4800) - 1;     // 4800 bps
    4'd7: baud_counter_target = (CLOCK_FREQUENCY / 9600) - 1;     // 9600 bps
    4'd8: baud_counter_target = (CLOCK_FREQUENCY / 19200) - 1;    // 19200 bps
    4'd9: baud_counter_target = (CLOCK_FREQUENCY / 28800) - 1;    // 28800 bps
    4'd10: baud_counter_target = (CLOCK_FREQUENCY / 38400) - 1;   // 38400 bps
    4'd11: baud_counter_target = (CLOCK_FREQUENCY / 57600) - 1;   // 57600 bps
    4'd12: baud_counter_target = (CLOCK_FREQUENCY / 76800) - 1;   // 76800 bps
    4'd13: baud_counter_target = (CLOCK_FREQUENCY / 115200) - 1;  // 115200 bps
    4'd14: baud_counter_target = (CLOCK_FREQUENCY / 230400) - 1;  // 230400 bps
    4'd15: baud_counter_target = (CLOCK_FREQUENCY / 460800) - 1;  // 460800 bps
    default: baud_counter_target = (CLOCK_FREQUENCY / 9600) - 1;  // default 9600 bps
  endcase
end

always @(posedge clk, negedge arst_n) begin
  if(~arst_n) begin
    tx_clk_cnt <= {TX_CNT_SIZE{1'b0}};
  end else if(active) begin
    if(tx_clk_en)
      tx_clk_cnt <= {TX_CNT_SIZE{1'b0}};
    else
      tx_clk_cnt <= tx_clk_cnt + 1'b1;
  end else begin
    tx_clk_cnt <= {TX_CNT_SIZE{1'b0}};
  end
end

always @(posedge clk, negedge arst_n) begin
  if(~arst_n) begin
    rx_clk_cnt <= {RX_CNT_SIZE{1'b0}};
  end else if(active) begin
    if(rx_clk_en)
      rx_clk_cnt <= {RX_CNT_SIZE{1'b0}};
    else
      rx_clk_cnt <= rx_clk_cnt + 1'b1;
  end else begin
    rx_clk_cnt <= {RX_CNT_SIZE{1'b0}};
  end
end

assign tx_clk_en = tx_clk_cnt == baud_counter_target; // 1x driving on transmitter
assign rx_clk_en = rx_clk_cnt == (baud_counter_target >> 4); // 16x oversampling on receiver

`ifdef VERIF
  
time tperiod;
time t1, t2;
reg check;
time t1_minus_t2;
time tmin, tmax;
real tolerance = 1; // 1% tolerance

always@(posedge tx_clk_cnt, negedge arst_n) begin
  if(!arst_n) begin
    check <= 1'b0;
  end else begin
    t2 = t1;
    t1 = $time;
    t1_minus_t2 = t1 - t2;
    tmin = tperiod * (100 - tolerance) / 100;
    tmax = tperiod * (100 + tolerance) / 100;
    check <= 1'b1;
    if(check)
      assert( (t1_minus_t2 >= tmin) && (t1_minus_t2 <= tmax) );
  end
end

always @(*) begin
  case(baud_rate) // subtracting 1, as counters below starts at 0
    4'd0: tperiod = (CLOCK_FREQUENCY / 200) * CLOCK_PERIOD;      // 200 bps
    4'd1: tperiod = (CLOCK_FREQUENCY / 300) * CLOCK_PERIOD;      // 300 bps
    4'd2: tperiod = (CLOCK_FREQUENCY / 600) * CLOCK_PERIOD;      // 600 bps
    4'd3: tperiod = (CLOCK_FREQUENCY / 1200) * CLOCK_PERIOD;     // 1200 bps
    4'd4: tperiod = (CLOCK_FREQUENCY / 1800) * CLOCK_PERIOD;     // 1800 bps
    4'd5: tperiod = (CLOCK_FREQUENCY / 2400) * CLOCK_PERIOD;     // 2400 bps
    4'd6: tperiod = (CLOCK_FREQUENCY / 4800) * CLOCK_PERIOD;     // 4800 bps
    4'd7: tperiod = (CLOCK_FREQUENCY / 9600) * CLOCK_PERIOD;     // 9600 bps
    4'd8: tperiod = (CLOCK_FREQUENCY / 19200) * CLOCK_PERIOD;    // 19200 bps
    4'd9: tperiod = (CLOCK_FREQUENCY / 28800) * CLOCK_PERIOD;    // 28800 bps
    4'd10: tperiod = (CLOCK_FREQUENCY / 38400) * CLOCK_PERIOD;   // 38400 bps
    4'd11: tperiod = (CLOCK_FREQUENCY / 57600) * CLOCK_PERIOD;   // 57600 bps
    4'd12: tperiod = (CLOCK_FREQUENCY / 76800) * CLOCK_PERIOD;   // 76800 bps
    4'd13: tperiod = (CLOCK_FREQUENCY / 115200) * CLOCK_PERIOD;  // 115200 bps
    4'd14: tperiod = (CLOCK_FREQUENCY / 230400) * CLOCK_PERIOD;  // 230400 bps
    4'd15: tperiod = (CLOCK_FREQUENCY / 460800) * CLOCK_PERIOD;  // 460800 bps
    default: tperiod = (CLOCK_FREQUENCY / 9600) * CLOCK_PERIOD;  // default 9600 bps
  endcase
end

`endif

endmodule 
