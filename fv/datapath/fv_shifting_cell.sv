module fv_shifting_cell #(parameter DATA_WIDTH = 8)(
input logic clk,
input logic arst_n,
input logic shifting_enable,
input logic [DATA_WIDTH-1:0] shifting_data,
input logic [DATA_WIDTH-1:0] shifted_data
);

  `ifdef SHIFTING_CELL_TOP
    `define SHIFTING_CELL_ASM 1
  `else
    `define SHIFTING_CELL_ASM 0
  `endif

  //The shifting_data must not be unknown always
  `REUSE(`SHIFTING_CELL_ASM, shifting_cell, x_propation, 1'b1 |->, !$isunknown(shifting_data))

  //The shifting_data must to be the same value of shifted_data when shifting_enable rises
  `AST(shifting_cell, data_shift, $rose(shifting_enable) |=>, shifted_data == $past(shifting_data))
  
  //The shifted_data must to be the same value of shifting_data when shifting_enable falls
  `AST(shifting_cell, not_shifting, $fell(shifting_enable) |=>, $stable(shifted_data))
  
endmodule

bind shifting_cell fv_shifting_cell fv_shifting_cell_i(.*);

