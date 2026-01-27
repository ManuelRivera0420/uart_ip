module fv_data_feeder #(parameter DATA_WIDTH = 8, ROW_WIDTH = 5, COL_HEIGHT = 3, KERNEL_WIDTH = 3, KERNEL_HEIGHT = COL_HEIGHT) (
input logic clk,
input logic arst_n,
input logic processing,
input logic dm_parallel_load_en,
input logic in_shifting_start,
input logic wg_shifting_start,
input logic processing_stall,
input logic [DATA_WIDTH-1:0] in_buffer_data [PARALLEL_IFM],
input logic wg_buffer_empty [PARALLEL_OFM][PARALLEL_IFM],
input logic [DATA_WIDTH-1:0] wg_buffer_data [PARALLEL_OFM][PARALLEL_IFM],
input logic pofm_active [PARALLEL_OFM], 
input logic pifm_active [PARALLEL_IFM], 
input logic wg_ds_done,
input logic wg_ds_shift_en,
input logic dm_ds_done,
input logic dm_ds_shift_en,
input logic [$clog2(ROW_WIDTH):0] dm_shift_cnt,
input logic [DATA_WIDTH-1:0] odata [PARALLEL_IFM][COL_HEIGHT][KERNEL_WIDTH],
input logic [DATA_WIDTH-1:0] oweight [PARALLEL_OFM][PARALLEL_IFM][KERNEL_HEIGHT][KERNEL_WIDTH]
);

  `ifdef DATA_FEEDER_TOP
    `define DATA_FEEDER_ASM 1
  `else
    `define DATA_FEEDER_ASM 0
  `endif

endmodule

bind data_feeder fv_data_feeder fv_data_feeder_i(.*);


