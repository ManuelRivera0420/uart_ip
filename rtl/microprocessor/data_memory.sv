module data_memory #(
    parameter DATA_WIDTH = 32,
    parameter DEPTH      = 1024
)(
    input  logic                  clk,
    input  logic                  wr_en,
    input  logic [DATA_WIDTH-1:0] addr,      // byte address
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out
);

    logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
    logic [$clog2(DEPTH)-1:0] word_addr;

    // byte → word
    assign word_addr = addr[$clog2(DEPTH)+1:2];

    // Write
    always_ff @(posedge clk) begin
        if (wr_en) begin
            mem[word_addr] <= data_in;
        end
    end

    // Read 
    assign data_out = mem[word_addr];

endmodule
