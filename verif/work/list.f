    ../property_defines.svh
    ../../rtl/defines.svh

# ============================ Microprocessor
# ========== MICROPROCESSOR(m0) ================
# ============================ pckg, svh, rtl
../../rtl/microprocessor/riscv_params_pkg.sv
../../rtl/microprocessor/mac_defs.svh
../../rtl/microprocessor/mux.sv
../../rtl/microprocessor/mux_operand_1.sv
../../rtl/microprocessor/program_counter.sv
../../rtl/microprocessor/plus_4_or_2_mux.sv
../../rtl/microprocessor/adder.sv
../../rtl/microprocessor/instruction_memory.sv
../../rtl/microprocessor/physical_register_file.sv
../../rtl/microprocessor/imm_gen.sv
../../rtl/microprocessor/alu.sv
../../rtl/microprocessor/branch.sv
../../rtl/microprocessor/data_memory.sv
../../rtl/microprocessor/mux_3_to_1.sv
../../rtl/microprocessor/control_unit.sv
#============================ MAC
../../rtl/microprocessor/accumulator_unit.sv
../../rtl/microprocessor/mac_adder.sv
../../rtl/microprocessor/booth_datapath.sv
../../rtl/microprocessor/booth_fsm.sv
../../rtl/microprocessor/booth_multiplier.sv
../../rtl/microprocessor/mac_top.sv
#============================== TOP
../../rtl/microprocessor/microprocessor_top.sv

# ============================= CMD Control
../../rtl/cmd_control/cmd_control_fsm.sv

# ============================ RTL
    ../../rtl/gpio_slave1/wb_gpio.sv
    ../../rtl/wishbone_logic/wb_master.sv
    ../../rtl/wishbone_logic/wb_interconnect.sv
    ../../rtl/wishbone_logic/wb_top_2master_debug.sv

    ../../rtl/soc_top.sv
# ============================ verification
    ../wb_top_2master_debug_tb.sv
    ../soc_top_tb.sv
