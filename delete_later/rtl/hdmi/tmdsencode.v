////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tmdsencode.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Take pixel/packet data, and encode them into a TMDS signal
//		for HDMI transport.
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
module	tmdsencode (
		input	wire		i_clk,
		input	wire	[1:0]	i_dtype,
		input	wire	[1:0]	i_ctl,
		input	wire	[3:0]	i_aux,
		input	wire	[7:0]	i_data,
		output	wire	[9:0]	o_word
	);

	parameter [1:0]	CHANNEL = 2'b00;

	// Data Types:
	//	2'b00	Guard band
	//	2'b01	Control period
	//	2'b10	Data Island
	//	2'b11	Pixel Data
	//

	///////////////////////////////
	//
	// Guard band
	//
	reg	[9:0]	guard_word;
	always @(*)
		case(CHANNEL)
		2'b00:   guard_word = 10'b1011001100;
		2'b01:   guard_word = 10'b0100110011;
		default: guard_word = 10'b1011001100;
		endcase

	reg	[1:0]	r_dtype;
	always @(posedge i_clk)
		r_dtype <= i_dtype[1:0];

	///////////////////////////////
	//
	// Control signal encoding
	reg	[9:0]	ctrl_word;
	reg	[1:0]	r_ctl;

	always @(posedge i_clk)
		r_ctl <= i_ctl;


	always @(posedge i_clk)
	case(r_ctl[1:0])
	2'b00: ctrl_word <= 10'b11_0101_0100;
	2'b01: ctrl_word <= 10'b00_1010_1011;
	2'b10: ctrl_word <= 10'b01_0101_0100;
	2'b11: ctrl_word <= 10'b10_1010_1011;
	endcase

	///////////////////////////////
	//
	// Auxilliary encoding
	//
	reg	[9:0]	aux_word;
	reg	[3:0]	r_aux;

	always @(posedge i_clk)
		r_aux <= i_aux;

	always @(posedge i_clk)
	case(r_aux)
	4'b0000: aux_word <= 10'b10_1001_1100;
	4'b0001: aux_word <= 10'b10_0110_0011;
	4'b0010: aux_word <= 10'b10_1110_0100;
	4'b0011: aux_word <= 10'b10_1110_0010;
	//
	4'b0100: aux_word <= 10'b01_0111_0001;
	4'b0101: aux_word <= 10'b01_0001_1110;
	4'b0110: aux_word <= 10'b01_1000_1110;
	4'b0111: aux_word <= 10'b01_0011_1100;
	//
	4'b1000: aux_word <= 10'b10_1100_1100;
	4'b1001: aux_word <= 10'b01_0011_1001;
	4'b1010: aux_word <= 10'b01_1001_1100;
	4'b1011: aux_word <= 10'b10_1100_0110;
	//
	4'b1100: aux_word <= 10'b10_1000_1110;
	4'b1101: aux_word <= 10'b10_0111_0001;
	4'b1110: aux_word <= 10'b01_0110_0011;
	4'b1111: aux_word <= 10'b10_1100_0011;
	endcase

	///////////////////////////////
	//
	// Pixel data encoding
	//
	reg	[3:0]	ones, ones_counter;
	reg	[3:0]	qm_ones, qm_ones_counter;
	reg	[8:0]	q_m;
	reg	[9:0]	pix_word;

	integer	k;

	always @(*)
	begin
		ones_counter = 0;
		for(k=0; k<8; k=k+1)
		if (i_data[k])
			ones_counter = ones_counter + 1;
		ones = ones_counter;
	end

	always @(*)
	begin
		qm_ones_counter = 0;
		for(k=0; k<8; k=k+1)
		if (q_m[k])
			qm_ones_counter = qm_ones_counter + 1;
		qm_ones = ones_counter;
	end

	wire	[3:0]	qm_zeros;
	// assign	zeros    = 4'h8-ones;
	assign	qm_zeros = 4'h8-qm_ones;

	// Take one always block to generate q_m
	// This is q_m(pre)
	reg	[8:0]	q_mp;

	always @(*)
	// 8-bit pixel data
	if ((ones > 4)||((ones == 4)&&(i_data[7])))
	begin
		q_mp[0] = i_data[0];
		q_mp[1] = !(q_mp[0] ^ i_data[1]);
		q_mp[2] = !(q_mp[1] ^ i_data[2]);
		q_mp[3] = !(q_mp[2] ^ i_data[3]);
		q_mp[4] = !(q_mp[3] ^ i_data[4]);
		q_mp[5] = !(q_mp[4] ^ i_data[5]);
		q_mp[6] = !(q_mp[5] ^ i_data[6]);
		q_mp[7] = !(q_mp[6] ^ i_data[7]);
		q_mp[8] = 1'b0;
	end else begin
		q_mp[0] = i_data[0];
		q_mp[1] = q_mp[0] ^ i_data[1];
		q_mp[2] = q_mp[1] ^ i_data[2];
		q_mp[3] = q_mp[2] ^ i_data[3];
		q_mp[4] = q_mp[3] ^ i_data[4];
		q_mp[5] = q_mp[4] ^ i_data[5];
		q_mp[6] = q_mp[5] ^ i_data[6];
		q_mp[7] = q_mp[6] ^ i_data[7];
		q_mp[8] = 1'b1;
	end

	always @(posedge i_clk)
		q_m <= q_mp;

	reg	signed	[4:0]	count;
	initial	count = 0;

	always @(posedge i_clk)
	if ((count == 0)||(qm_ones == qm_zeros))
	begin
		pix_word[9]  <= !q_m[8];
		pix_word[8]  <=  q_m[8];
		pix_word[7:0]<=  (q_m[8] ? q_m[7:0] : (~q_m[7:0]));
		if (q_m[8])
			count <= count + (qm_ones - qm_zeros);
		else
			count <= count + (qm_zeros - qm_ones);
	end else if (((count > 0)&&(qm_ones > qm_zeros))
			||((count < 0)&&(qm_zeros > qm_ones)))
	begin
		pix_word[9]   <=   1'b1;
		pix_word[8]   <=  q_m[8];
		pix_word[7:0] <= ~q_m[7:0];
		count <= count + (q_m[8] ? 5'h2 : 0)
				+(qm_zeros - qm_ones);
	end else begin
		pix_word[9] <= 1'b0;
		pix_word[8] <= q_m[8];
		pix_word[7:0] <= q_m[7:0];
		count <= count - (q_m[8] ? 0 : 5'h2)
			+ (qm_ones - qm_zeros);
	end

	reg	[1:0]	s_dtype;
	always @(posedge i_clk)
		s_dtype <= r_dtype;

	//	2'b00	Guard band
	//	2'b01	Control period
	//	2'b10	Data Island
	//	2'b11	Pixel Data
	//
	reg	[9:0]	brv_word;
	always @(posedge i_clk)
	case(s_dtype)
	2'b00: brv_word <= guard_word;
	2'b01: brv_word <=  ctrl_word;
	2'b10: brv_word <=   aux_word;
	2'b11: brv_word <=   pix_word;
	endcase

	genvar	gk;
	generate for(gk=0; gk<10; gk=gk+1)
		assign	o_word[gk] = brv_word[9-gk];
	endgenerate

`ifdef	FORMAL
	initial	assert(CHANNEL < 2'b11);

	always @(*)
		assert(count <  5'sd10);
	always @(*)
		assert(count > -5'sd10);
`endif
endmodule
