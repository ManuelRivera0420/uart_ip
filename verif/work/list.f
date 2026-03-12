    ../property_defines.svh
    ../../rtl/defines.svh
# ============================ SRAM
    ../../rtl/rtl_mixedsram/sram_cell.sv
    ../../rtl/rtl_mixedsram/write_driver.sv
    ../../rtl/rtl_mixedsram/decoder.sv
    ../../rtl/rtl_mixedsram/sense_amp.sv
    ../../rtl/rtl_mixedsram/cell_array.sv
    ../../rtl/rtl_mixedsram/sipo.sv
    ../../rtl/rtl_mixedsram/sram_ip.sv
    ../../rtl/rtl_mixedsram/wb/wb_sram.sv
    ../../rtl/wishbone_logic/wb_mem.sv
# ================================= Monitoreo de temperatura
    ../../third_party/monitoreo-de-temperatura/rtl/comparador_temp.sv
    ../../third_party/monitoreo-de-temperatura/rtl/persistencia_ctr.sv
    ../../third_party/monitoreo-de-temperatura/rtl/estado_temp.sv
    ../../third_party/monitoreo-de-temperatura/rtl/wb_slave2.sv
# ================================= PWM Ramon
  # ============================ rtl UART
    ../../rtl/uart_clk_gen.sv
    ../../rtl/uart_edge_detector.sv
    ../../rtl/uart_control_reg.sv
    ../../rtl/uart_tnsm.sv
    ../../rtl/uart_recv.sv
    ../../rtl/fsm_instruction_loader.sv
    ../../rtl/wishbone_logic/wb_master.sv
    ../../rtl/uart_ip.sv 
# ============================ verification
    ../uart_ip_interface.sv
    ../uart_ip_tb.sv
