//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_two_ff_synchronizer
//
// Description:
// this module is a classic two flip flop synchronizer, used for rx
// asynchronous input
//////////////////////////////////////////////////////////////////////////////////

module uart_two_ff_synchronizer (
  input wire clk,
  input wire arst_n,
  input wire async_data,
  output wire sync_data
);

reg ff1, ff2;

always@(posedge clk, negedge arst_n) begin
  if(!arst_n) begin
    ff1 <= 1'b1; // reset to 1'b1, as rx is pulled up
    ff2 <= 1'b1; // reset to 1'b1, as rx is pulled up
  end else begin
    ff1 <= async_data;
    ff2 <= ff1;
  end
end
  
assign sync_data = ff2;

endmodule
