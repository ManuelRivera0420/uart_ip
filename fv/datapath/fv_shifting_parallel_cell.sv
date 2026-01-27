module fv_shifting_parallel_cell #(parameter DATA_WIDTH = 8) (
input logic clk,
input logic arst_n,
input logic parallel_load_en,
input logic [DATA_WIDTH-1:0] parallel_data,
input logic shifting_enable,
input logic [DATA_WIDTH-1:0] shifting_data,
input logic [DATA_WIDTH-1:0] shifted_data
);

  `ifdef SHIFTING_PARALLEL_CELL_TOP
    `define SHIFTING_PARALLEL_CELL_ASM 1
  `else
    `define SHIFTING_PARALLEL_CELL_ASM 0
  `endif

  // shifting_enable and parallel_load_en should not be high at the same time
  `REUSE(`SHIFTING_PARALLEL_CELL_ASM, shifting_parallel_cell, control,
    1'b1 |->,
    !((shifting_enable == 1'b1) && (parallel_load_en == 1'b1))
  )

  // The shifting_data must not be unknown
  `REUSE(`SHIFTING_PARALLEL_CELL_ASM, shifting_parallel_cell, shifting_data_x_propation,
   1'b1 |->,
   !$isunknown(shifting_data)
  )

  // The parallel_data must not be unknown
  `REUSE(`SHIFTING_PARALLEL_CELL_ASM, shifting_parallel_cell, parallel_data_x_propation,
   1'b1 |->,
   !$isunknown(parallel_data)
  )

  // The shifting_data must to be the same value of shifthed_data on the next time when
  // shifting_enable is high and parallel_load_en is low
  `AST(shifting_parallel_cell, shifting_data_shift,
    (shifting_enable == 1'b1) && (parallel_load_en == 1'b0) |=>,
    shifted_data == $past(shifting_data)
  )

  // The parallel_data must to be the same value of shifted_data on the next time when
  // shifting_enable is low and parallel_load_en is high
  `AST(shifting_parallel_cell, parallel_data_shift,
    (shifting_enable == 1'b0) && (parallel_load_en == 1'b1) |=>,
    shifted_data == $past(parallel_data)
  )


  // The shifted_data must to be stable when shifting_enable and parallel_load_en are low
  `AST(shifting_parallel_cell, data_static,
    (shifting_enable == 1'b0) && (parallel_load_en == 1'b0) |=>,
    $stable(shifted_data)
  )
  
endmodule

bind shifting_parallel_cell fv_shifting_parallel_cell fv_shifting_parallel_cell_i(.*);

