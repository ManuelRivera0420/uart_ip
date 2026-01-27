module fv_data_matrix #(parameter DATA_WIDTH = 8, ROW_WIDTH = 5, COL_HEIGHT = 3, KERNEL_WIDTH = 3, KERNEL_HEIGHT = COL_HEIGHT) (
input logic clk,
input logic arst_n,
input logic processing,
input logic parallel_load_en,
input logic shifting_enable,
input logic [DATA_WIDTH-1:0] shifting_data,
input logic [DATA_WIDTH-1:0] odata [COL_HEIGHT][KERNEL_WIDTH]
);
  
  `ifdef DATA_MATRIX_TOP
    `define DATA_MATRIX_ASM 1
  `else
    `define DATA_MATRIX_ASM 0
  `endif
  
  // shifting_enable and parallel_load_en should not be high at the same time
  `REUSE(`DATA_MATRIX_ASM, data_matrix, control,
    1'b1 |->,
    !((shifting_enable == 1'b1) && (parallel_load_en == 1'b1))
  )

  // The shifting_data must not be unknown
  `REUSE(`DATA_MATRIX_ASM, data_matrix, shifting_data_x_propation,
   1'b1 |->,
   !$isunknown(shifting_data)
  )
  
  // when not processing, shifting_enable or parallel_load_en should not rise at the same time
  `REUSE(`DATA_MATRIX_ASM, data_matrix, processing_control,
    processing == 1'b0 |->,
    !($rose(shifting_enable) || $rose(parallel_load_en))
  )

endmodule

bind data_matrix fv_data_matrix fv_data_matrix_i(.*);

