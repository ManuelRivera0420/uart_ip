clear -all

set_proofgrid_bridge off

set fv_analyze_options { -sv12 }
set design_top shifting_cell

if {[info exists SHIFTING_CELL_TOP]} {
  lappend fv_analyze_options " +define+SHIFTING_CELL_TOP"
  set design_top shifting_cell
}

if {[info exists SHIFTING_ROW_TOP]} {
  lappend fv_analyze_options " +define+SHIFTING_ROW_TOP"
  set design_top shifting_row
}

if {[info exists SHIFTING_PARALLEL_CELL_TOP]} {
  lappend fv_analyze_options " +define+SHIFTING_PARALLEL_CELL_TOP"
  set design_top shifting_parallel_cell
}

if {[info exists SHIFTING_PARALLEL_ROW_TOP]} {
  lappend fv_analyze_options " +define+SHIFTING_PARALLEL_ROW_TOP"
  set design_top shifting_parallel_row
}

if {[info exists DATA_SHIFTER_TOP]} {
  lappend fv_analyze_options " +define+DATA_SHIFTER_TOP"
  set design_top data_shifter
}

if {[info exists DATA_MATRIX_TOP]} {
  lappend fv_analyze_options " +define+DATA_MATRIX_TOP"
  set design_top data_matrix
}

if {[info exists DATA_FEEDER_TOP]} {
  lappend fv_analyze_options " +define+DATA_FEEDER_TOP"
  set design_top data_feeder
}

analyze [join $fv_analyze_options] -f datapath.flist

elaborate -bbox_a 65535 -bbox_mul 65535 -non_constant_loop_limit 2000 -top $design_top

clock clk
reset -expression !arst_n
set_engineJ_max_trace_length 2000

prove -all