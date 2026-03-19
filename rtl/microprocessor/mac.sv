module mac #(parameter RESULT_WIDTH = 32, parameter OPERAND_WIDTH = 5)(
  input logic                       clk,
  input logic                       arst_n,
  input logic                       start,
  input logic   [OPERAND_WIDTH-1:0] operand_1,
  input logic   [OPERAND_WIDTH-1:0] operand_2,
  output logic  [DATA_WIDTH-1:0]    result,
  output logic                      ready
);

logic done;

  always_ff @(posedge clk, negedge arst_n) begin 
    

    if(!arst_n) begin 
      result <= '0;
    end else if(start) begin
      result <= operand_1 * operand_2;
      done <= 1'b1;
    end else begin 
      done <= 1'b0;
    end
  end

  always_comb begin   
    if (done) begin 
      ready = 1'b1;
    end else begin 
      ready = 1'b0;
    end
  end
  
endmodule
