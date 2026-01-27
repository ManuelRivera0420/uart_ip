module fv_shifting_parallel_row #(parameter DATA_WIDTH = 8, ROW_WIDTH = 5) (
input logic clk,
input logic arst_n,
input logic parallel_load_en,
input logic [DATA_WIDTH-1:0] parallel_idata [ROW_WIDTH],
input logic shifting_enable,
input logic [DATA_WIDTH-1:0] parallel_odata [ROW_WIDTH]
);
  `ifdef SHIFTING_PARALLEL_ROW_TOP
    `define SHIFTING_PARALLEL_ROW_ASM 1
  `else
    `define SHIFTING_PARALLEL_ROW_ASM 0
  `endif

  // shifting_enable and parallel_load_en should not be high at the same time
  `REUSE(`SHIFTING_PARALLEL_ROW_ASM, shifting_parallel_cell, control,
    1'b1 |->,
    !((shifting_enable == 1'b1) && (parallel_load_en == 1'b1))
  )

  for (genvar k = 0; k < ROW_WIDTH; k++) begin : gen__parallel
    //The parallel_idata[k] must not be unknown
    `REUSE(`SHIFTING_PARALLEL_ROW_ASM, shifting_parallel_row, parallel_idata_x_propation,
      1'b1 |->,
      !$isunknown(parallel_idata[k])
    )
    // The parallel_idata[k] must to be the same value of parallel_odata[k] on the next time when
    // parallel_load_en is high
    if (k < ROW_WIDTH - 1) begin
      `AST(shifting_parallel_row, shifting_data_shift,
        (shifting_enable == 1'b1) && (parallel_load_en == 1'b0) |=>,
        parallel_odata[k+1] == $past(parallel_odata[k])
      )
    end else begin
      `AST(shifting_parallel_row, shifting_data_shift,
        (shifting_enable == 1'b1) && (parallel_load_en == 1'b0) |=>,
        parallel_odata[0] == $past(parallel_odata[ROW_WIDTH - 1])
      )
    end
  end

  // The parallel_idata must to be the same value of parallel_odata on the next time when
  `AST(shifting_parallel_row, parallel_data_shift,
    (shifting_enable == 1'b0) && (parallel_load_en == 1'b1) |=>,
    parallel_odata == $past(parallel_idata)
  )

endmodule

bind shifting_parallel_row fv_shifting_parallel_row fv_shifting_parallel_row_i(.*);

