module fv_data_shifter #(parameter SHIFTING_DEPTH = 8) (
input logic clk,
input logic arst_n,
input logic start,
input logic en,
input logic done,
input logic [$clog2(SHIFTING_DEPTH):0] shift_cnt,
input logic shift_en
);

  `ifdef DATA_SHIFTER_TOP
    `define DATA_SHIFTER_ASM 1
  `else
    `define DATA_SHIFTER_ASM 0
  `endif

  // en should be high always
  `REUSE(`DATA_SHIFTER_ASM, data_shifter, en_done_control,
    1'b1 |->,
    en == 1'b1
  )
  // start and shift_en should not change at the same time
  `REUSE(`DATA_SHIFTER_ASM, data_shifter, start_0,
    1'b1 |->,
    !($rose(start) && $fell(shift_en))
  )
  // start should not rise when shift_en is high
  `REUSE(`DATA_SHIFTER_ASM, data_shifter, start_1,
    1'b1 |->,
    !($rose(start) && (shift_en == 1'b1))
  )

  // shift_en should be high only when started
  `AST(data_shifter, shift_en_high_after_start,
    $rose(start) |=>, 
    $rose(shift_en)
  )

  // done should be high when shift_cnt reaches SHIFTING_DEPTH
  `AST(data_shifter, waiting_done,
    $rose(shift_en) |-> ##SHIFTING_DEPTH,
    $rose(done)
  )

  // shift_en should be low after done is high
  `AST(data_shifter, shift_en_low_after_done,
    $rose(done) |->, 
    $fell(shift_en)
  )


endmodule

bind data_shifter fv_data_shifter fv_data_shifter_i(.*);

