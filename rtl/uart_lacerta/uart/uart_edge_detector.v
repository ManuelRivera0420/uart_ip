//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_edge_detector
//
// Description:
// this module detects a debounced negative edge (high to low transition) on the
// rx uart input signal, so we can detect the start bit
//////////////////////////////////////////////////////////////////////////////////

module uart_edge_detector (
  input clk,
  input arst_n,
  input rx,
  output rx_negedge_det
);

localparam SCK_DEBOUNCE_SIZE = 2; // debounce depth, Note: 0, and 1 are not valid values
localparam DEBOUNCE_REGISTER_DEPTH = SCK_DEBOUNCE_SIZE * 2 - 1; // as we concatenate rx on comparison, we need 1 few flop, that is why I use -2

reg [DEBOUNCE_REGISTER_DEPTH - 1 : 0] rx_r;

// rx edge detector logic //
always @(posedge clk, negedge arst_n) begin
  if(!arst_n) begin
    rx_r <= {DEBOUNCE_REGISTER_DEPTH{1'b1}}; // reset to all 1s as rx is pulled up
  end else begin
    rx_r <= {rx_r[DEBOUNCE_REGISTER_DEPTH - 2 : 0], rx};
  end
end

assign rx_negedge_det = {rx_r, rx} == {{SCK_DEBOUNCE_SIZE{1'b1}},{SCK_DEBOUNCE_SIZE{1'b0}}}; // negative edge pattern detection

endmodule
