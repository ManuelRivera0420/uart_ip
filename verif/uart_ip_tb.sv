module uart_ip_tb();

bit clk;
bit arst_n;

//`define FAST_BAUDS

parameter int BAUD_RATES [16] = '{200, 300, 600, 1200, 1800, 2400, 4800, 9600, 19200, 28800, 38400, 57600,
76800, 115200, 230400, 460800};

// UART RECEIVER STATES //
localparam STATE_RECV_IDLE = 3'b000;
localparam STATE_RECV_START = 3'b001;
localparam STATE_RECV_RECEIVE = 3'b010;
localparam STATE_RECV_PARITY = 3'b011;
localparam STATE_RECV_STOP1 = 3'b100;
localparam STATE_RECV_STOP2 = 3'b101;

// UART TRANSMITTER STATES //
localparam STATE_TNSM_IDLE = 3'b000;
localparam STATE_TNSM_DATA = 3'b001;
localparam STATE_TNSM_PARITY = 3'b010;
localparam STATE_TNSM_STOP1 = 3'b011;
localparam STATE_TNSM_STOP2 = 3'b100;

// TIMING LOCAL PARAMETERS USED FOR TESTING //
localparam time CLK_PERIOD = 20ns;
localparam time BIT_TIME = 1s / 9600;
localparam int BIT_CYCLES = BIT_TIME / CLK_PERIOD;
localparam time SAMPLING_TIME = 1s / (9600 * 16);
localparam time HALF_BIT = BIT_TIME / 2;
localparam int HALF_BIT_CYCLES = HALF_BIT / CLK_PERIOD;

// NUMBER OF TESTS FOR THE TESTBENCH //
localparam N_OF_TESTS = 100;
localparam N_OF_TESTS_PER_BAUD = 3;
// INTERFACE INSTANTIATION //
uart_ip_interface intf(clk, arst_n);

// DUT INSTANTIATION //
uart_ip uart_ip_i(
.clk(clk),
.arst_n(arst_n),
.ctl_reg_we(intf.ctl_reg_we),
.ctl_reg_wdata(intf.ctl_reg_wdata),
.ctl_reg_wmask(intf.ctl_reg_wmask),
.ctl_reg_rdata(intf.ctl_reg_rdata),
.st_reg_re(intf.st_reg_re),
.st_reg_rmask(intf.st_reg_rmask),
.st_reg_rdata(intf.st_reg_rdata),
.rx(intf.tx_test),
.tx(intf.rx_test)
);

`define RECEIVER uart_ip_i.uart_recv_i
`define TRANSMITTER uart_ip_i.uart_tnsm_i 
`define UART_CLK_GEN uart_ip_i.clk_gen_i

// GENERATING CLK AND ARST_N STIMULUS //
always #10ns clk = ~clk;
assign #50ns arst_n = 1'b1;

int frame_bits;
logic [7:0] data_in;

logic stop_type;
logic [3:0] baud_rate;
logic [1:0] parity_type;
logic [1:0] frame_size;
logic [7:0] expected_data;

class baud_sel;
    rand bit [3:0] baud_rate;
    constraint c {baud_rate inside {[4'd0:4'd14]};}
endclass

class uart_config;

    bit [3:0] baud_rate;
    rand bit stop_type;
    rand bit [1:0] parity_type;
    rand int unsigned frame_bits;
    rand bit [7:0] data_in;

    constraint c_frame_bits {frame_bits inside {[5:8]};}
    constraint c_parity {parity_type inside {2'b00};}

endclass

uart_config cfg;
baud_sel baud;

time bit_time;
int bit_cycles = 5208; //default value for 9600 baud rate
int half_bit_cycles = 2604;
always @(posedge clk) begin
    if($rose(`RECEIVER.rx_negedge_det)) begin
        bit_time = 1s / BAUD_RATES[baud_rate];
        bit_cycles = (bit_time / CLK_PERIOD);
        half_bit_cycles = bit_cycles >> 1;
    end
end


initial begin
    wait(arst_n);
    @(posedge clk);
    intf.set_default_config();
    cfg = new();
    baud = new();

    repeat(N_OF_TESTS) begin

        intf.set_default_config();

  //      `ifdef FAST_BAUDS
        assert(baud.randomize() with {baud_rate inside {[7:14]}; });
  //      `else
  //          assert(baud.randomize() with {baud_rate inside {[0:6]}; });
  //      `endif

        cfg.baud_rate = baud.baud_rate;
        repeat(bit_cycles) @(posedge clk);

        repeat(N_OF_TESTS_PER_BAUD) begin

            assert(cfg.randomize());
        
            case(cfg.frame_bits)
                5: frame_size = 2'b00;
                6: frame_size = 2'b01;
                7: frame_size = 2'b10;
                8: frame_size = 2'b11;
            endcase
        
            expected_data = cfg.data_in;
        
            repeat(1000) @(posedge clk);

            intf.set_config(cfg.baud_rate, cfg.stop_type, cfg.parity_type, frame_size, 1'b1);
            intf.set_config_global(cfg.baud_rate, cfg.stop_type, cfg.parity_type, frame_size);

            repeat(bit_cycles) @(posedge clk);

            intf.transfer(cfg.data_in, cfg.frame_bits);
            repeat(10) @(posedge clk);

            wait(`RECEIVER.recv);

            intf.write_tnsm_data(cfg.data_in);
            repeat(10) @(posedge clk);
            
            wait(!`TRANSMITTER.busy);
        end
    end
    $finish;
end


logic [7:0] data_tmp;
always @(posedge uart_ip_i.recv_busy) begin
    case(frame_size)
        2'b00: data_tmp = {3'b000, expected_data[4:0]};
        2'b01: data_tmp = {2'b00, expected_data[5:0]};
        2'b10: data_tmp = {1'b0, expected_data[6:0]};
        2'b11: data_tmp = expected_data;
    endcase
end

`AST(UART_TX, tx_startbit,
    $rose(`TRANSMITTER.tnsm && `TRANSMITTER.active && `TRANSMITTER.tnsm_clk_en) && !`TRANSMITTER.busy |=>,
    !(`TRANSMITTER.tx)
)

`AST(UART_TX, tx_idle,
    (!`TRANSMITTER.busy) |->,
    (`TRANSMITTER.tx)
)

`AST(UART_TX, tx_idle_when_active_is_low,
    (!(`TRANSMITTER.active) && !(`TRANSMITTER.busy)) |->,
    (`TRANSMITTER.state == STATE_TNSM_IDLE)
)

`AST(UART_TX, tx_high_when_stop_bit_state,
    ((`TRANSMITTER.state == STATE_TNSM_STOP1) || (`TRANSMITTER.state == STATE_TNSM_STOP2)) |->,
    (`TRANSMITTER.tx)
)

`AST(UART_RECV, receiver_not_starting_when_active_is_low,
    (!(`RECEIVER.active) && !(`RECEIVER.busy)) |->,
    (`RECEIVER.state == STATE_RECV_IDLE)
)

`AST(UART_RECV, receiver_starts_when_active_and_negedge_detected,
    ((`RECEIVER.active) && $rose((`RECEIVER.rx_negedge_det)) && (`RECEIVER.state == STATE_RECV_IDLE)) |=>,
    (`RECEIVER.state == STATE_RECV_START)
)

`AST(UART_RECV, receiver_busy_when_not_idle,
    (`RECEIVER.busy) |->,
    (`RECEIVER.state != STATE_RECV_IDLE)
)

`AST(UART_RECV, data_timing,
    $rose(`RECEIVER.recv) |->,
    (`RECEIVER.data == data_tmp)   
)

`AST(UART_RECV, when_reset_not_busy,
    !`RECEIVER.arst_n |->,
    !`RECEIVER.busy
)

`AST(UART_RECV, if_recv_not_busy_anymore,
    `RECEIVER.recv |->,
    !`RECEIVER.busy
)

`AST(UART_RECV, recv_is_active_one_cycle,
    `RECEIVER.recv |-> ##1,
    !`RECEIVER.recv
)

always @(posedge `RECEIVER.busy) begin
    if(`RECEIVER.active) begin
	repeat(half_bit_cycles) @(posedge clk);
	assert (`RECEIVER.rx == 1'b0);
    end
end

/*
initial begin
    $shm_open("shm_db");
    $shm_probe("ASMTR");
end
*/
endmodule
