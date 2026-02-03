`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company:
// Engineer:
//
// Design Name:
// Module Name: uart_ip_interface
//
//////////////////////////////////////////////////////////////////////////////////

interface uart_ip_interface(input logic clk, input logic arst_n);

// Declaration of signals used by user tile
logic ctl_reg_we;
logic [18:0] ctl_reg_wdata;
logic [18:0] ctl_reg_wmask;
logic [18:0] ctl_reg_rdata;
logic st_reg_re;
logic [11:0] st_reg_rmask;
logic [11:0] st_reg_rdata;

logic rx;
logic tx;
logic tx_test;

assign rx = tx_test;

assign st_reg_rmask = '1;
assign st_reg_re = 1'b1;
////////////////////////////////////// BFM ///////////////////////////	

localparam COMMAND_WRITE = 8'h01;
localparam COMMAND_READ = 8'h00;
localparam BAUD_RATE_DEFAULT = 4'b0111; // 9600 baud rate by default
localparam FRAME_TYPE_DEFAULT = 2'b01; // 8-bits packet by default
localparam PARITY_TYPE_DEFAULT = 3'b000; // no parity bit by default
localparam STOP_TYPE_DEFAULT = 1'b0; // 1 stop bit by default
event drive_ev;
event sample_ev;
parameter int BAUD_RATES [16] = '{200, 300, 600, 1200, 1800, 2400, 4800, 9600, 19200, 28800, 38400, 57600,
76800, 115200, 230400, 460800};
logic [7:0] recv_data_test;
logic [1:0] frame_type;
/*
logic [1:0] frame_type;
modport user_tile_modport(
	input ctl_reg_we, ctl_reg_wdata, ctl_reg_wmask, st_reg_re, st_reg_rmask, rx,
	output ctl_reg_rdata, st_reg_rdata, tx
);
*/

function logic [18:0] read_ctl_reg();
    return ctl_reg_rdata;
endfunction

task set_default_config();
    @(posedge clk);
    ctl_reg_wdata <= {9'd0, 4'd7, 1'b0, 2'b00, FRAME_TYPE_DEFAULT, 1'b1};
    ctl_reg_wmask <= {19{1'b1}};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_wmask <= {19{1'b0}};
    ctl_reg_we <= 1'b0;
endtask

task change_baud_rate(logic [3:0] baud_sel);
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:10], baud_sel, ctl_reg_wdata[5:0]};
    ctl_reg_wmask <= {9'h0, 4'b1111, 6'h0};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
    ctl_reg_wmask <= 19'h0;
endtask

task write_tnsm_data(logic [7:0] data);
    @(posedge clk);
    ctl_reg_wdata <= {data, 1'b1, ctl_reg_wdata[9:1], 1'b1}; // Update the data and set transmission to active
    ctl_reg_wmask <= {{9{1'b1}}, 9'h0, 1'b1};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
    ctl_reg_wmask <= 19'h0;
endtask

task set_active();
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:1], 1'b1};
    ctl_reg_wmask <= {18'h0, 1'b1};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
    ctl_reg_wmask <= 19'h0;    
endtask

task set_frame_size(logic [1:0] frame_size);
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:3], frame_size, ctl_reg_wdata[0]};
    ctl_reg_wmask <= {16'd0, 2'b11, 1'b0};
    ctl_reg_we <= 1'b1;
    frame_type <= frame_size;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
    ctl_reg_wmask <= 19'd0;    
endtask

task set_stop_bit(bit stop_bit);
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:6], stop_bit, ctl_reg_wdata[4:0]};
    ctl_reg_wmask <= {13'd0, 1'b1, 5'd0};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
endtask

task set_parity_bit(logic [1:0] parity_config);
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:5], parity_config, ctl_reg_wdata[2:0]};
    ctl_reg_wmask <= {14'd0, 2'b11, 3'd0};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
    ctl_reg_wmask <= 19'h0;    
endtask

task tnsm_enable();
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:11], 1'b1, ctl_reg_wdata[9:0]};
    ctl_reg_wmask <= {8'h0, 1'b1, 10'h0};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_we <= 1'b0;
    ctl_reg_wmask <= 19'h0;    
endtask

/////////////////////////////////////////////////////// 
int total_packet_bits;
int frame_bits;
int timesteps_per_toggle;
logic [3:0] baud_rate;
logic [1:0] parity_type;
logic stop_type;

task initialize();
    baud_rate <= BAUD_RATE_DEFAULT;
    frame_type <= FRAME_TYPE_DEFAULT;
    parity_type <= PARITY_TYPE_DEFAULT;
    stop_type <= STOP_TYPE_DEFAULT;
    tx_test <= 1'b1;
endtask

function calculate_packet_bits();
    total_packet_bits = 1; //startbit;
    total_packet_bits = total_packet_bits + stop_type ? 2 : 1; //stop_bits
    case(frame_type)
        2'b00: frame_bits = 5;
        2'b01: frame_bits = 6;
        2'b10: frame_bits = 7;
        2'b11: frame_bits = 8;
        default: frame_bits = frame_bits; // should never happen
    endcase
    total_packet_bits = total_packet_bits + frame_bits; // multiplied by 2, 1 for posedge, 1 for negedge
    timesteps_per_toggle = 1_000_000_000/BAUD_RATES[baud_rate]; // assuming timestep of 1ns
endfunction

task gen_drive_ev();
    calculate_packet_bits();
    repeat(total_packet_bits) begin // Every transaction requires 1 (start bit), frame_type data bits, stop_type bits toggles
    ->drive_ev;
    repeat(timesteps_per_toggle) #1;
    end
endtask
	
task wait_recv_data(output logic [7:0] recv_data);
    @(negedge rx); // start bit from rx wire
    calculate_packet_bits();
    fork receive(recv_data); join_none
    repeat(timesteps_per_toggle/2) #1; // sample at the middle of the event
    repeat(total_packet_bits) begin // Every transaction requires 1 (start bit), frame_type data bits, stop_type bits toggles
        ->sample_ev;
        repeat(timesteps_per_toggle) #1;
    end
endtask

task receive(output logic [7:0] recv_data);
    calculate_packet_bits();
    //recv_data = new[total_packet_bits];
    repeat(total_packet_bits) begin
        wait(sample_ev.triggered);
        for(int i = 0; i < total_packet_bits; i++)
            recv_data[i] = i == (total_packet_bits-1) ? rx : recv_data[i+1]; // data is shifted from msb to lsb
    end
endtask

task transmit(input logic data []);
    logic data_tmp [];
    calculate_packet_bits();
    data_tmp = new[total_packet_bits];
    data_tmp = '{default:'1};
    data_tmp[0] = 1'b0; // start bit
    for(int i = 0; i < frame_bits; i++) begin
        data_tmp[i+1] = data[i];
    end
    repeat(total_packet_bits) begin
        //wait(drive_ev.triggered);
        repeat(1_000_000_000/9600) #1;
        tx_test = data_tmp[0];
	for (int i = 0; i < total_packet_bits-1; i++)
	  data_tmp[i] = data_tmp[i+1];
    end
endtask

task transfer(logic [7:0] data);
    logic data_tmp [];
    data_tmp = new[frame_bits];
    //data_tmp = new[frame_bits];
    for (int i = 0; i < frame_bits; i++) data_tmp[i] = data[i];
        repeat(10) @(posedge clk);
    fork
      gen_drive_ev();
      transmit(data_tmp);
    join_none
        repeat(10) @(posedge clk);
endtask
/*
always begin
    wait_recv_data(recv_data_test);
end
*/
endinterface

