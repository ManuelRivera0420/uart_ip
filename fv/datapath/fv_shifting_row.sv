module fv_shifting_row #(parameter DATA_WIDTH = 8, ROW_WIDTH = 5) (
input logic clk,
input logic arst_n,
input logic shifting_enable,
input logic [DATA_WIDTH-1:0] shifting_data,
input logic [DATA_WIDTH-1:0] parallel_odata [ROW_WIDTH]
);

  `ifdef SHIFTING_ROW_TOP
    `define SHIFTING_ROW_ASM 1
  `else
    `define SHIFTING_ROW_ASM 0
  `endif

  //The shifting_data must not be unknown
  `REUSE(`SHIFTING_ROW_ASM, shifting_row, shifting_data_x_propation,
    1'b1 |->,
    !$isunknown(shifting_data)
  )

  for (genvar k = 0; k < ROW_WIDTH - 1; k++) begin : gen_shifting
    // The shifting_data must to be the same of parallel_odata[i] on the next i time 
    // when shifting_enable is high for i times
    `AST(shifting_row, data_shift,
      shifting_enable == 1'b1 |=>,
      parallel_odata[k+1] == $past(parallel_odata[k])
    )

  // The parallel_odata must to be stable when shifting_enable is low for i times
  `AST(shifting_row, not_shifting,
    shifting_enable == 1'b0 |=>,
    $stable(parallel_odata[k]))
  end


endmodule

bind shifting_row
  fv_shifting_row #(
    .DATA_WIDTH($bits(shifting_data)),
    .ROW_WIDTH ($size(parallel_odata))
  ) fv_shifting_row_i (
    .clk           (clk),
    .arst_n        (arst_n),
    .shifting_enable(shifting_enable),
    .shifting_data (shifting_data),
    .parallel_odata(parallel_odata)
  );

