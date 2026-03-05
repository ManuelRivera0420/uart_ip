//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer: Miguel Rivera
// 
// Design Name: uart_ip
// Module Name: uart_control_reg
//
// Description:
// this module is used to store the control flags of the uart ip
///////////////////////////////////////////////////////////////////////////////////

module uart_control_reg(
  input wire clk,
  input wire arst_n,
  input wire we,               // write enable
  input wire [18:0] wmask,           // write mask
  input wire [18:0] datain,
  input wire tnsm_clr,         // clear tnsm bit
  output wire [1:0] frame_type,
  output wire [1:0] parity_type,
  output wire stop_type,
  output wire active,
  output wire [3:0] baud_rate,
  output wire tnsm,
  output wire [7:0] tnsm_data,
  output wire [18:0] ctl_reg_rdata
);

reg [18:0] reg_;

always @(posedge clk, negedge arst_n) begin
  if (!arst_n) begin
    reg_[0] <= 1'b1;     // Active by default
    reg_[2:1] <= 2'b11;  // 8-bit packet default
    reg_[5] <= 1'b0;     // 1 stop bit default
    reg_[4:3] <= 2'b00;  // No parity default
    reg_[18:10] <= 9'd0; // tnsm flag + data cleared
    reg_[9:6] <= 4'd14;  // 230400 baud rate by default
  end else begin
    if (we) begin
      reg_ <= (reg_ & ~wmask) | (datain & wmask); // only write when wmask is set
    end else if (tnsm_clr) begin
      reg_[10] <= 1'b0;
    end
  end
end

assign active = reg_[0];
assign frame_type = reg_[2:1];
assign parity_type = reg_[4:3];
assign stop_type = reg_[5];
assign baud_rate = reg_[9:6];
assign tnsm = reg_[10];
assign tnsm_data = reg_[18:11];
assign ctl_reg_rdata = reg_;

endmodule 
