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
logic rx_test;

//assign rx_test = tx;
//assign rx = tx_test;

assign st_reg_rmask = '1;
assign st_reg_re = 1'b1;

////////////////////////////////////// BFM ///////////////////////////	
event drive_ev;
event sample_ev;
logic [7:0] recv_data_test;

parameter int BAUD_RATES [16] = '{200, 300, 600, 1200, 1800, 2400, 4800, 9600, 19200, 28800, 38400, 57600,
76800, 115200, 230400, 460800};

logic [1:0] frame_type;
logic stop_type;
logic [1:0] parity_type;
logic [3:0] baud_rate;
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

task set_config(input logic [3:0] baud_rate_sel, input logic stop_type_sel, input logic [1:0] parity_type_sel, input logic [1:0] frame_type_sel, input logic on_sel);
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:11], 1'b1, baud_rate_sel, stop_type_sel, parity_type_sel, frame_type_sel, on_sel};
    ctl_reg_wmask <= {19{1'b1}};
    ctl_reg_we <= 1'b1;
    @(posedge clk);
    ctl_reg_wmask <= {19{1'b0}};
    ctl_reg_we <= 1'b0;
endtask


task set_default_config();
    @(posedge clk);
    ctl_reg_wdata <= {9'd0, 4'd7, 1'b0, 2'b00, 2'b11, 1'b0};
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

task set_active(bit on);
    @(posedge clk);
    ctl_reg_wdata <= {ctl_reg_wdata[18:1], on};
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
int frame_bits_debug;
int timesteps_per_toggle;

task set_config_global(
  input logic [3:0] baud_rate_s,
  input logic stop_type_s,
  input logic [1:0] parity_type_s,
  input logic [1:0] packet_size
);
  frame_type  <= packet_size;
  stop_type   <= stop_type_s;
  baud_rate   <= baud_rate_s;
  parity_type <= parity_type_s;
endtask

task initialize();
  tx_test <= 1'b1;
endtask

int parity_add;
function calculate_packet_bits();
    total_packet_bits = 1; //startbit;
    total_packet_bits = total_packet_bits + stop_type ? 2 : 1; //stop_bits
    case(frame_type)
        2'b00: frame_bits_debug = 5;
        2'b01: frame_bits_debug = 6;
        2'b10: frame_bits_debug = 7;
        2'b11: frame_bits_debug = 8;
        default: frame_bits_debug = frame_bits_debug; // should never happen
    endcase
    case(parity_type)
        2'b00: parity_add = 0;
        2'b01: parity_add = 1;
        2'b10: parity_add = 1;
        2'b11: parity_add = 0;
    endcase

    total_packet_bits = total_packet_bits + frame_bits_debug; // multiplied by 2, 1 for posedge, 1 for negedge
    total_packet_bits = total_packet_bits + parity_add;
    timesteps_per_toggle = 1_000_000_000/BAUD_RATES[baud_rate]; // assuming timestep of 1ns
endfunction

task gen_drive_ev();
    calculate_packet_bits();
    repeat(total_packet_bits) begin // Every transaction requires 1 (start bit), frame_type data bits, stop_type bits toggles
    ->drive_ev;
    repeat(timesteps_per_toggle) #1;
    end
endtask

logic [7:0] data_debug;
logic rx_intf_busy;
// DEBUG ! SHOULD REPLACE RX_TEST FOR RX
task wait_recv_data(output logic [7:0] recv_data);
    recv_data = '0;
    data_debug = 'x;
    @(negedge rx_test); // start bit from rx wire
    rx_intf_busy = 1'b1;
    calculate_packet_bits();
    repeat(timesteps_per_toggle/2) #1; // sample at the middle of the event
    
    for (int i = 0; i < frame_bits_debug; i++) begin
        repeat(1_000_000_000/BAUD_RATES[baud_rate]) #1;
        recv_data = {rx_test, recv_data[7:1]};
        data_debug = {rx_test, data_debug[7:1]};
    end

    case(frame_bits_debug)
        5: recv_data = recv_data >> 3;
        6: recv_data = recv_data >> 2;
        7: recv_data = recv_data >> 1;
        default: recv_data = recv_data;
    endcase 

    data_debug = recv_data;

    if(!stop_type) begin
        repeat(1_000_000_000/BAUD_RATES[baud_rate]) #1;
        rx_intf_busy = 1'b0;
    end else begin
        repeat((1_000_000_000/BAUD_RATES[baud_rate]) * 2) #1;
        rx_intf_busy = 1'b0;
    end
endtask

logic start_bit;
task transmit(input logic data [], input int frame_bits);
    logic data_tmp [];
    start_bit = 1'b0;
    calculate_packet_bits();
    data_tmp = new[total_packet_bits];
    foreach (data_tmp[i])
	data_tmp[i] = 1'b1;
    data_tmp[0] = 1'b0; // start bit

    for(int i = 0; i < frame_bits; i++) begin
        data_tmp[i+1] = data[i];
    end
    repeat(total_packet_bits) begin
	if(start_bit)
           repeat(1_000_000_000/BAUD_RATES[baud_rate]) #1;
   	else
           repeat((1_000_000_000/BAUD_RATES[baud_rate])/2) #1;
	tx_test = data_tmp[0];
	start_bit = 1'b1;
	for (int i = 0; i < total_packet_bits-1; i++)
	   data_tmp[i] = data_tmp[i+1];
    end
endtask

task transfer(logic [7:0] data, input int frame_bits);
    logic data_tmp [];
    logic [1:0] size;
    data_tmp = new[frame_bits];
    initialize();
    for (int i = 0; i < frame_bits; i++) data_tmp[i] = data[i];
        repeat(10) @(posedge clk);
    fork
      gen_drive_ev();
      transmit(data_tmp, frame_bits);
    join_none
        repeat(10) @(posedge clk);
endtask

always begin
    wait_recv_data(recv_data_test);
end

endinterface

