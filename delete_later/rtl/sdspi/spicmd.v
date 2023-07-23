////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spicmd.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Issues commands and collects responses from the lower level
//		SPI processor.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023, Gisselquist Technology, LLC
// {{{
// This file is part of the ETH10G project.
//
// The ETH10G project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, files
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	spicmd (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		i_cmd_stb,
		input	wire	[1:0]	i_cmd_type,
		input	wire	[5:0]	i_cmd,
		input	wire	[31:0]	i_cmd_data,
		output	reg		o_busy,
		//
		output	wire		o_ll_stb,
		output	wire	[7:0]	o_ll_byte,
		input	wire		i_ll_busy,
		//
		input	wire		i_ll_stb,
		input	wire	[7:0]	i_ll_byte,
		//
		output	reg		o_cmd_sent,
		output	reg		o_rxvalid,
		output	reg	[39:0]	o_response
		// }}}
	);

	// Signal declarations
	// {{{
	reg		almost_sent;
	reg	[4:0]	crc_valid_sreg;
	reg		crc_busy;
	reg	[4:0]	crc_bit_counter;
	reg	[39:0]	crc_shift_reg, shift_data;
	reg	[7:0]	crc_byte;
	reg		rx_r1_byte, rx_check_busy, rxvalid;
	reg	[2:0]	rx_counter;
	localparam	CRC_POLYNOMIAL = 7'h09; // Was 8'h12
	reg	[6:0]	next_crc_byte;
	// }}}

	// o_busy
	// {{{
	initial	o_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_busy <= 1'b0;
	else if (!o_busy && i_cmd_stb)
		o_busy <= 1'b1;
	// else if (o_rxvalid)
	else if (rxvalid && !rx_check_busy)
		o_busy <= 1'b0;
	// }}}

	// shift_data
	// {{{
	initial	shift_data = -1;
	always @(posedge i_clk)
	if (!o_busy && i_cmd_stb)
		shift_data <= { 2'b01, i_cmd, i_cmd_data };
	else if (!i_ll_busy)
	begin
		shift_data <= { shift_data[31:0], 8'hff };
		if (crc_valid_sreg[0])
			shift_data[39:32] <= crc_byte;
	end
	// }}}

	assign	o_ll_stb  = o_busy;
	assign	o_ll_byte = shift_data[39:32];

	// o_cmd_sent
	// {{{
	initial	o_cmd_sent = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		{ o_cmd_sent, almost_sent } <= 2'b00;
	else if (!o_cmd_sent && !i_ll_busy)
		{ o_cmd_sent, almost_sent } <= { almost_sent, crc_valid_sreg[0] };
	// }}}

	// crc_valid_sreg
	// {{{
	initial	crc_valid_sreg = 5'b10000;
	always @(posedge i_clk)
	if (!o_busy)
		crc_valid_sreg <= 5'b10000;
	else if (!i_ll_busy)
		crc_valid_sreg <= crc_valid_sreg >> 1;
	// }}}

	// crc_busy, crc_bit_counter
	// {{{
	initial crc_busy = 1'b0;
	initial	crc_bit_counter = 20;
	always @(posedge i_clk)
	if (!o_busy)
	begin
		crc_bit_counter <= 20;
		crc_busy <= (i_cmd_stb);
	end else if (crc_busy)
	begin
		crc_bit_counter <= crc_bit_counter - 1;
		crc_busy <= (crc_bit_counter > 1);
	end
	// }}}

	// crc_shift_reg
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
		crc_shift_reg <= { 2'b01, i_cmd, i_cmd_data };
	else if (crc_busy)
		crc_shift_reg <= crc_shift_reg << 2;
	// }}}

	// next_crc_byte
	// {{{
	always @(*)
	begin
		next_crc_byte = { crc_byte[6:1], 1'b0 };
		if (crc_byte[7] ^ crc_shift_reg[39])
			next_crc_byte = next_crc_byte ^ CRC_POLYNOMIAL;
		if (next_crc_byte[6] ^ crc_shift_reg[38])
			next_crc_byte = (next_crc_byte<<1) ^ CRC_POLYNOMIAL;
		else
			next_crc_byte = (next_crc_byte<<1);
	end
	// }}}

	// crc_byte
	// {{{
	initial	crc_byte = 0;
	always @(posedge i_clk)
	if (!o_busy)
		crc_byte <= 1;
	else if (crc_busy)
		crc_byte <= { next_crc_byte, 1'b1 };
	// }}}

	// rx_r1_byte, rx_counter, rxvalid, rx_check_busy
	// {{{
	initial	rxvalid = 1'b0;
	initial	rx_counter = 1;
	always @(posedge i_clk)
	if (!o_busy)
	begin
		rx_r1_byte <= 1'b0;
		rx_counter <= (i_cmd_type[1]) ? 5 : 1;
		rx_check_busy <= (i_cmd_type == 2'b01);
		rxvalid <= 1'b0;
	end else if (o_cmd_sent && i_ll_stb)
	begin
		if (!rx_r1_byte)
			rx_r1_byte <= (!i_ll_byte[7]);

		if ((rx_r1_byte || !i_ll_byte[7]) && !rxvalid)
		begin
			rx_counter <= rx_counter - 1;
			rxvalid <= (rx_counter <= 1);
		end

		if (rx_r1_byte && i_ll_byte != 0)
			rx_check_busy <= 1'b0;
	end
	// }}}

	// o_rxvalid
	// {{{
	initial	o_rxvalid = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		o_rxvalid <= 0;
	else if (rxvalid && !rx_check_busy)
		o_rxvalid <= 1;
	// }}}

	// o_response
	// {{{
	initial	o_response = -1;
	always @(posedge i_clk)
	if (!o_busy)
		o_response <= -1;
	else if (i_ll_stb)
	begin
		if (!rx_r1_byte)
			o_response[39:32] <= i_ll_byte;
		else
			o_response[31:0] <= { o_response[23:0], i_ll_byte };
	end
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`ifdef	SPICMD
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	reg		f_past_valid;
	reg [2:0]	f_send_seq;
	reg [3:0]	f_rcv_seq;
	reg [5:0]	f_cmd;
	reg	[31:0]	f_data;
	reg	[1:0]	f_type;
	reg	[39:0]	f_rcv_data;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!o_cmd_sent)
	begin
		assert(!o_rxvalid);
		assert(!rxvalid || !o_busy);
	end else
		assert(&shift_data);

	always @(*)
	if (!rxvalid)
		assert(!o_rxvalid);

	initial	f_send_seq = 0;
	always @(posedge i_clk)
	if (i_reset || (o_busy && rxvalid && !rx_check_busy))
		f_send_seq <= 0;
	else if (!o_busy)
		f_send_seq <= (i_cmd_stb) ? 1:0;
	else if (o_busy && !o_cmd_sent && (f_send_seq < 7))
		f_send_seq <= f_send_seq + (i_ll_busy ? 0:1);

	always @(posedge i_clk)
	if (!o_busy)
		{ f_cmd, f_data, f_type } <= { i_cmd, i_cmd_data, i_cmd_type };

	always @(*)
	if (i_reset || !o_busy)
	begin
		if (!o_busy)
			assert(f_send_seq == 0);
	end else case(f_send_seq)
	1: begin
		assert(shift_data == { 2'b01, f_cmd, f_data });
		assert(o_busy);
		assert({ o_cmd_sent, almost_sent } == 2'b00);
		assert(crc_valid_sreg == 5'b1_0000);
		end
	2: begin
		assert(shift_data == { f_data, 8'hff });
		assert(o_busy);
		assert({ o_cmd_sent, almost_sent } == 2'b00);
		assert(crc_valid_sreg == 5'b1000);
		end
	3: begin
		assert(shift_data == { f_data[23:0], 16'hffff });
		assert(o_busy);
		assert({ o_cmd_sent, almost_sent } == 2'b00);
		assert(crc_valid_sreg == 5'b100);
		end
	4: begin
		assert(shift_data == { f_data[15:0], 24'hffffff });
		assert(o_busy);
		assert({ o_cmd_sent, almost_sent } == 2'b00);
		assert(crc_valid_sreg == 5'b10);
		end
	5: begin
		assert(shift_data == { f_data[7:0], 32'hffffffff });
		assert(o_busy);
		assert({ o_cmd_sent, almost_sent } == 2'b00);
		assert(crc_valid_sreg == 5'b1);
		end
	6: begin
		assert(shift_data == { crc_byte, 32'hffffffff });
		assert(o_busy);
		assert({ o_cmd_sent, almost_sent } == 2'b01);
		assert(crc_valid_sreg == 5'b0);
		end
	7: begin
		assert(shift_data == 40'hff_ffff_ffff);
		assert(crc_valid_sreg == 5'b0);
		assert(o_cmd_sent);
		end
	endcase

	always @(*)
	if (o_busy)
	begin
		assert(f_send_seq != 0);
		assert(f_rcv_seq != 0);
	end

	always @(*)
		assert(crc_bit_counter <= 20);

	always @(*)
	if (o_busy)
		assert(crc_busy == (crc_bit_counter > 0));

	// Got to give the CRC enough time to work
	always @(*)
	if (!o_cmd_sent)
	begin
		// if (crc_bit_counter > 4)
		//	`ASSUME(f_send_seq < 3);
		if (crc_bit_counter > 2)
			`ASSUME(f_send_seq < 4);
		if (crc_bit_counter > 0)
			`ASSUME(f_send_seq < 5);
	end

	always @(*)
	if (o_busy && !o_cmd_sent)
		assume(i_ll_byte == 8'hff);

	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (o_busy && !o_cmd_sent)
	begin
		assert(f_rcv_seq == 1);
		assert(&o_response);
	end

	initial	f_rcv_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_rcv_seq <= 0;
	else if (!o_busy)
		f_rcv_seq <= (i_cmd_stb) ? 1 : 0;
	else if (o_cmd_sent && i_ll_stb)
	begin
		assert(f_rcv_seq != 0);
		if (!rx_r1_byte)
		begin
			if (!i_ll_byte[7]) casez(f_type)
			2'b00: f_rcv_seq <= 3;	// R1 response
			2'b01: f_rcv_seq <= 2;	// R1b response
			2'b1?: f_rcv_seq <= 4;	// R3/R7 response
			endcase
		end else case(f_rcv_seq)
		1: begin assert(0); end // Should never be here
		2: begin
			if (i_ll_byte != 0)
				f_rcv_seq <= 3;
			end
		3: begin end // We'll stop here with R1b
		4: f_rcv_seq <= f_rcv_seq + 1;
		5: f_rcv_seq <= f_rcv_seq + 1;
		6: f_rcv_seq <= f_rcv_seq + 1;
		7: f_rcv_seq <= f_rcv_seq + 1;
		default: begin end
		endcase
	end

	always @(posedge i_clk)
	if (i_ll_stb)
	begin
		if (!rx_r1_byte)
			f_rcv_data[39:32] <= i_ll_byte;
		else
			f_rcv_data[31:0] <= { f_rcv_data[23:0], i_ll_byte };
	end

	always @(*)
	if (!i_reset && o_busy && f_rcv_seq > 0)
	case(f_rcv_seq)
	1: begin
		assert(!rx_r1_byte);
		assert(rx_counter == ((f_type[1]) ? 5 : 1));
		assert(rx_check_busy == (f_type == 2'b01));
		assert(!rxvalid);
		assert(f_send_seq != 0);
		assert(&o_response[31:0]);
		end
	2: begin
		assert(o_cmd_sent);
		assert(rx_r1_byte);
		assert(rx_counter == 0);
		assert(rx_check_busy);
		assert(rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		// assert(&o_response[31:0]);
		end
	3: begin
		assert(o_cmd_sent);
		assert(rx_r1_byte);
		assert(rx_counter == 0);
		assert(!rx_check_busy);
		assert(rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		// assert(&o_response[31:8]);
		end
	4: begin
		assert(rx_r1_byte);
		assert(rx_counter == 4);
		assert(!rx_check_busy);
		assert(!rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		assert(&o_response[31:0]);
		end
	5: begin
		assert(rx_r1_byte);
		assert(rx_counter == 3);
		assert(!rx_check_busy);
		assert(!rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		assert(o_response[7:0] == f_rcv_data[7:0]);
		assert(&o_response[31:8]);
		end
	6: begin
		assert(rx_r1_byte);
		assert(rx_counter == 2);
		assert(!rx_check_busy);
		assert(!rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		assert(o_response[15:0] == f_rcv_data[15:0]);
		assert(&o_response[31:16]);
		end
	7: begin
		assert(rx_r1_byte);
		assert(rx_counter == 1);
		assert(!rx_check_busy);
		assert(!rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		assert(o_response[23:0] == f_rcv_data[23:0]);
		assert(&o_response[31:24]);
		end
	8: begin
		assert(rx_r1_byte);
		assert(rx_counter == 0);
		assert(!rx_check_busy);
		assert(rxvalid);
		assert(o_response[39:32] == f_rcv_data[39:32]);
		end
	default: assert(f_rcv_seq <= 8);
	endcase

	always @(*)
		assert(rxvalid == (rx_counter == 0));
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	begin
		cover(o_cmd_sent);
		cover(f_rcv_seq == 1);
		cover(f_rcv_seq == 2);
		cover(f_rcv_seq == 3);
		cover(f_rcv_seq == 4);
		cover(f_rcv_seq == 5);
		cover(f_rcv_seq == 6);
		cover(f_rcv_seq == 7);
		cover(f_rcv_seq == 8);
	end

	always @(posedge i_clk)
		cover(o_rxvalid && f_cmd == 0 && f_data == 0);

	always @(posedge i_clk)
		cover(o_rxvalid && f_cmd == 0 && f_data == 0
			&& crc_byte == 8'h95);
`endif
// }}}
endmodule
