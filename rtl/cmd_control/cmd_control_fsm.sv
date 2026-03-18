module cmd_control_fsm #
(parameter AW = 16,
 parameter DW = 32)
(
    input logic clk,
    input logic arst_n,
    input logic uc_out_valid,
    input logic [DW - 1 : 0] uc_data,
    input logic cmd_ready_in,
    output logic [AW - 1 : 0] cmd_addr_fsm,
    output logic [DW - 1 : 0] cmd_wdata_fsm,
    output logic cmd_we_fsm,
    output logic cmd_valid_fsm
);

logic [AW - 1 : 0] cmd_addr_reg;
logic [DW - 1 : 0] cmd_wdata_reg;
logic cmd_we_reg;
logic cmd_valid_reg;

typedef enum logic [2:0] 
{   IDLE, 
    WAIT_ADDR, 
    WAIT_DATA,
    WAIT_WRITE_READ, 
    SEND_VALID} state_dtype;

state_dtype state;

always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        cmd_addr_reg <= '0;
        cmd_wdata_reg <= '0;
        cmd_we_reg <= 1'b0;
        cmd_valid_reg <= 1'b0;
        state <= IDLE;
    end else begin
        case(state)

            IDLE: begin
                cmd_addr_reg <= '0;
                cmd_wdata_reg <= '0;
                cmd_we_reg <= 1'b0;
                cmd_valid_reg <= 1'b0;
                state <= WAIT_ADDR;
            end

            WAIT_ADDR: begin
                if(uc_out_valid) begin
                    cmd_addr_reg <= uc_data;
                    state <= WAIT_DATA;
                end
            end

            WAIT_DATA: begin
                if(uc_out_valid) begin
                    cmd_wdata_reg <= uc_data;
                    state <= WAIT_WRITE_READ;
                end
            end

            WAIT_WRITE_READ: begin
                if(uc_out_valid) begin
                    cmd_we_reg <= uc_data[0];
                    state <= SEND_VALID;
                end
            end

            SEND_VALID: begin
                cmd_valid_reg <= 1'b1;
                state <= IDLE;
            end

        endcase
    end
end

assign cmd_valid_fsm = cmd_valid_reg;

assign cmd_addr_fsm = cmd_addr_reg;
assign cmd_wdata_fsm = cmd_wdata_reg;
assign cmd_we_fsm = cmd_we_reg;

endmodule
