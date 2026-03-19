import riscv_params_pkg::*;

module instruction_memory #(
    parameter MEM_SIZE = 4096
)(
    input  logic                  clk,

    // fetch
    input  logic [DATA_WIDTH-1:0] pc,
    output logic [31:0]           instr,

    // write port (loader / wishbone)
    input  logic                  we,
    input  logic [DATA_WIDTH-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data
);

    // MEM_SIZE está en bytes, por eso se divide entre 4
    logic [31:0] mem [0:(MEM_SIZE/4)-1];

    // ----------------------------
    // INIT FROM HEX
    // ----------------------------
    initial begin
    for (int i = 0; i < (MEM_SIZE/4); i = i + 1) begin
        mem[i] = 32'h00000000;
    end
        $readmemh("/home/manuelrivera/git_repositories/dd_cuatri2_sect2/SoC_final/rtl/microprocessor/test_3.hex", mem);
    end

    // -----------------------------
    // WRITE (word-aligned)
    // -----------------------------
    always_ff @(posedge clk) begin
        if (we) begin
            mem[wr_addr[DATA_WIDTH-1:2]] <= wr_data;
        end
    end

    // -----------------------------
    // READ (word-aligned)
    // -----------------------------
    assign instr = mem[pc[DATA_WIDTH-1:2]];

endmodule
