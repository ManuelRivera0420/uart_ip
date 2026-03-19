`timescale 1ns / 1ps
//------------------------------------------------------------------------------
// Module: physical_register_file
// Description:
//   2-read / 1-write register file for an RV32-style datapath.
//   Provides two combinational read ports and one synchronous write port.
//   Register index 0 implements architectural x0 semantics (always reads as zero).
//
// Interface:
//   - write_en / write_dir / write_data : synchronous write port
//   - read_dir1 / read_dir2              : read addresses
//   - read_data1 / read_data2            : combinational read outputs
//
// Assumptions:
//   - Register addresses are 5 bits wide (32 registers total).
//   - Write address and data are stable around the rising clock edge.
//   - x0 must always read as zero, regardless of write attempts.
//
// Notes:
//   - Writes to register 0 are explicitly blocked.
//   - Reset initializes only register 0. Other registers are left unchanged
//     until written (architecturally acceptable for RV32).
//------------------------------------------------------------------------------
module physical_register_file #(
    parameter DIR_WIDTH  = 5,   // 5 bits -> 32 registers
    parameter DATA_WIDTH = 32
)(
    input  logic                  clk,
    input  logic                  arst_n,
    input  logic                  write_en,
    input  logic [DIR_WIDTH-1:0]   read_dir1,
    input  logic [DIR_WIDTH-1:0]   read_dir2,
    input  logic [DIR_WIDTH-1:0]   write_dir,
    input  logic [DATA_WIDTH-1:0]  write_data,
    output logic [DATA_WIDTH-1:0]  read_data1,
    output logic [DATA_WIDTH-1:0]  read_data2
);

    // Register storage: 32 entries of 32 bits each
    logic [DATA_WIDTH-1:0] prf [0:(2**DIR_WIDTH)-1];

    //-------------------------------------------------------------------------
    // Synchronous write port
    //-------------------------------------------------------------------------
    // - Active-low asynchronous reset initializes x0
    // - Writes to x0 are blocked to preserve architectural semantics
    //-------------------------------------------------------------------------
    always_ff @(posedge clk, negedge arst_n) begin
        if (!arst_n) begin
            prf[0] <= '0;  // x0 hard-wired to zero
        end else if (write_en == 1'b1 && (write_dir != 5'b00000)) begin
            prf[write_dir] <= write_data;
        end
    end

    //-------------------------------------------------------------------------
    // Combinational read ports
    //-------------------------------------------------------------------------
    // Reads from register 0 always return zero
    assign read_data1 = (read_dir1 == '0) ? '0 : prf[read_dir1];
    assign read_data2 = (read_dir2 == '0) ? '0 : prf[read_dir2];

endmodule

