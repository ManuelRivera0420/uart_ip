interface uart_ip_bfm(input clk, input arst_n);
	// `include "../../rtl/spi-slave/spi_slave_definitions.v" // TODO: do I need to add definitions file?
	
	logic tx;
	logic rx;

	localparam COMMAND_WRITE = 8'h01;
	localparam COMMAND_READ = 8'h00;
	localparam BAUD_RATE_DEFAULT = 4'b0111; // 9600 baud rate by default
	localparam FRAME_TYPE_DEFAULT = 2'b11; // 8-bits packet by default
	localparam PARITY_TYPE_DEFAULT = 3'b000; // no parity bit by default
	localparam STOP_TYPE_DEFAULT = 1'b0; // 1 stop bit by default
	event drive_ev;
	event sample_ev;
	parameter int BAUD_RATES [16] = '{200,
																		300,
																		600,
																		1200,
																		1800,
																		2400,
																		4800,
																		9600,
																		19200,
																		28800,
																		38400,
																		57600,
																		76800,
																		115200,
																		230400,
																		460800};
	int total_packet_bits;
	int frame_bits;
	int timesteps_per_toggle;
	logic [3:0] baud_rate;
	logic [1:0] frame_type;
	logic [1:0] parity_type;
	logic stop_type;

	task initialize();
		baud_rate <= BAUD_RATE_DEFAULT;
		frame_type <= FRAME_TYPE_DEFAULT;
		parity_type <= PARITY_TYPE_DEFAULT;
		stop_type <= STOP_TYPE_DEFAULT;
		tx <= 1'b1;
	endtask
	
	function calculate_packet_bits();
		total_packet_bits = 1/*start bit*/;
		total_packet_bits = total_packet_bits + stop_type ? 2 : 1; /*stop bits*/
		case(frame_type)
			2'b00: frame_bits = 5;
			2'b01: frame_bits = 6;
			2'b10: frame_bits = 7;
			2'b11: frame_bits = 8;
			default: frame_bits = frame_bits; // should never happen
		endcase
		total_packet_bits = total_packet_bits + frame_bits/* * 2*/; // multiplied by 2, 1 for posedge, 1 for negedge
		timesteps_per_toggle = 1_000_000_000/BAUD_RATES[baud_rate]; // assuming timestep of 1ns
	endfunction

		task gen_drive_ev();
		calculate_packet_bits();
		repeat(total_packet_bits) begin // Every transaction requires 1 (start bit), frame_type data bits, stop_type bits toggles
			->drive_ev;
			repeat(timesteps_per_toggle) #1;
		end
	endtask
	
	task wait_recv_data(output logic recv_data []);
		@(negedge rx); // start bit from rx wire
		calculate_packet_bits();
		fork receive(recv_data); join_none
		repeat(timesteps_per_toggle/2) #1; // sample at the middle of the event
		repeat(total_packet_bits) begin // Every transaction requires 1 (start bit), frame_type data bits, stop_type bits toggles
			->sample_ev;
			repeat(timesteps_per_toggle) #1;
		end
	endtask

	task receive(output logic recv_data []);
		calculate_packet_bits();
		recv_data = new[total_packet_bits];
		repeat(total_packet_bits) begin
			wait(clk_sample_ev.triggered);
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
			wait(clk_drive_ev.triggered);
			tx = data_tmp[0];
			for(int i = 0; i < (total_packet_bits-1); i++)
				data_tmp[i] = data_tmp[i+1];
		end
	endtask

	task transfer(logic [7:0] data);
		logic data_tmp [frame_bits];
		for(int i = 0; i < frame_bits; i++) data_tmp[i] = data[i];
    		repeat(10) @(posedge clk);
		fork
		  gen_drive_ev();
		  transmit(data_tmp);
		join_none
    		repeat(10) @(posedge clk);
	endtask
	
	always begin
		wait_recv_data();
	end

endinterface
