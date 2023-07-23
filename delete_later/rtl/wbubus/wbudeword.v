////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbudeword.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Once a word has come from the bus, undergone compression, had
//		idle cycles and interrupts placed in it, this routine converts
//	that word form a 36-bit single word into a series of 6-bit words
//	that can head to the output routine.  Hence, it 'deword's the value:
//	unencoding the 36-bit word encoding.
//
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
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	wbudeword (
		// {{{
		input	wire		i_clk, i_reset, i_stb,
		input	wire	[35:0]	i_word,
		input	wire		i_tx_busy,
		output	reg		o_stb,
		output	reg	[6:0]	o_nl_hexbits,
		output	wire		o_busy,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	wire	[2:0]	w_len;
	reg	[2:0]	r_len;
	reg	[29:0]	r_word;
	// }}}

	// r_word, o_nl_hexbits
	// {{{
	initial	o_nl_hexbits = 7'h40;
	always @(posedge i_clk)
	if (i_stb && !o_busy) // Only accept when not busy
	begin
		r_word <= i_word[29:0];
		o_nl_hexbits <= { 1'b0, i_word[35:30] }; // No newline ... yet
	end else if (!i_tx_busy)
	begin
		if (r_len > 1)
		begin
			o_nl_hexbits <= { 1'b0, r_word[29:24] };
			r_word[29:6] <= r_word[23:0];
		end else if (!o_nl_hexbits[6])
		begin
			// Place a 7'h40 between every pair of words
			o_nl_hexbits <= 7'h40;
		end
	end
	// }}}

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (i_stb && !o_busy)
		o_stb <= 1'b1;
	else if (r_len == 0 && !i_tx_busy)
		o_stb <= 1'b0;
	// }}}

	// r_len
	// {{{
	assign w_len = (i_word[35:33]==3'b000)? 3'b001
			: (i_word[35:32]==4'h2)? 3'b110
			: (i_word[35:32]==4'h3)? (3'b010+{1'b0,i_word[31:30]})
			: (i_word[35:34]==2'b01)? 3'b010
			: (i_word[35:34]==2'b10)? 3'b001
			:  3'b110;

	initial	r_len = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_len <= 0;
	else if (i_stb && !o_busy)
		r_len <= w_len;
	else if (!i_tx_busy && (r_len > 0))
		r_len <= r_len - 1;
	// }}}

	assign	o_busy   = o_stb;
	assign	o_active = i_stb || o_stb;
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
	reg	[35:0]	fvword;
	reg	[6:0]	six_seq;
	reg	[5:0]	five_seq;
	reg	[4:0]	four_seq;
	reg	[3:0]	three_seq;
	reg	[2:0]	two_seq;
	reg	[1:0]	one_seq;

	always @(*)
		assert(o_busy == o_stb);
	always @(posedge i_clk)
	if (!o_busy)
		fvword <= i_word;

	initial	six_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		six_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b110)
		six_seq <= 1;
	else if (!i_tx_busy)
		six_seq <= six_seq << 1;

	always @(*)
	case(six_seq)
	0: begin end // This is the idle state, no assertions required
	7'b000_0001: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[35:30] });
		assert(r_len == 3'b110);
		assert(r_word == fvword[29:0]);
		assert(o_busy);
		end
	7'b000_0010: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[29:24] });
		assert(r_len == 3'b101);
		assert(r_word == { fvword[23:0], fvword[5:0] });
		assert(o_busy);
		end
	7'b000_0100: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[23:18] });
		assert(r_len == 3'b100);
		assert(r_word == { fvword[17:0], {(2){fvword[5:0]}} });
		assert(o_busy);
		end
	7'b000_1000: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[17:12] });
		assert(r_len == 3'b011);
		assert(r_word == { fvword[11:0], {(3){fvword[5:0]}} });
		assert(o_busy);
		end
	7'b001_0000: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[11:6] });
		assert(r_len == 3'b010);
		assert(r_word == { fvword[5:0], {(4){fvword[5:0]}} });
		assert(o_busy);
		end
	7'b010_0000: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[5:0] });
		assert(r_len == 3'b001);
		assert(o_busy);
		end
	7'b100_0000: begin
		assert(o_stb);
		assert(o_nl_hexbits == 7'h40);
		assert(r_len == 3'b000);
		assert(o_busy);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	five_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		five_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b101)
		five_seq <= 1;
	else if (!i_tx_busy)
		five_seq <= five_seq << 1;

	always @(*)
	case(five_seq)
	0: begin end // This is the idle state, no assertions required
	6'b00_0001: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[35:30] });
		assert(r_len == 3'b101);
		assert(r_word == fvword[29:0]);
		assert(o_busy);
		end
	6'b00_0010: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[29:24] });
		assert(r_len == 3'b100);
		assert(r_word == { fvword[23:0], fvword[5:0] });
		assert(o_busy);
		end
	6'b00_0100: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[23:18] });
		assert(r_len == 3'b011);
		assert(r_word == { fvword[17:0], {(2){fvword[5:0]}} });
		assert(o_busy);
		end
	6'b00_1000: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[17:12] });
		assert(r_len == 3'b010);
		assert(r_word == { fvword[11:0], {(3){fvword[5:0]}} });
		assert(o_busy);
		end
	6'b01_0000: begin
		assert(o_stb);
		assert(o_nl_hexbits == { 1'b0, fvword[11:6] });
		assert(r_len == 3'b001);
		assert(r_word == { fvword[5:0], {(4){fvword[5:0]}} });
		assert(o_busy);
		end
	6'b10_0000: begin
		assert(o_stb);
		assert(o_nl_hexbits == 7'h40);
		assert(r_len == 3'b000);
		assert(o_busy);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	four_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		four_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b100)
		four_seq <= 1;
	else if (!i_tx_busy)
		four_seq <= four_seq << 1;

	always @(*)
	case(four_seq)
	0: begin end // This is the idle state, no assertions required
	5'b0_0001: begin
		assert(o_nl_hexbits == { 1'b0, fvword[35:30] });
		assert(r_len == 3'b100);
		assert(r_word == fvword[29:0]);
		assert(o_busy && o_stb);
		end
	5'b0_0010: begin
		assert(o_nl_hexbits == { 1'b0, fvword[29:24] });
		assert(r_len == 3'b011);
		assert(r_word == { fvword[23:0], fvword[5:0] });
		assert(o_busy && o_stb);
		end
	5'b0_0100: begin
		assert(o_nl_hexbits == { 1'b0, fvword[23:18] });
		assert(r_len == 3'b010);
		assert(r_word == { fvword[17:0], {(2){fvword[5:0]}} });
		assert(o_busy && o_stb);
		end
	5'b0_1000: begin
		assert(o_nl_hexbits == { 1'b0, fvword[17:12] });
		assert(r_len == 3'b001);
		assert(r_word == { fvword[11:0], {(3){fvword[5:0]}} });
		assert(o_busy && o_stb);
		end
	5'b1_0000: begin
		assert(o_nl_hexbits == 7'h40);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	three_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		three_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b011)
		three_seq <= 1;
	else if (!i_tx_busy)
		three_seq <= three_seq << 1;

	always @(*)
	case(three_seq)
	0: begin end // This is the idle state, no assertions required
	4'b0001: begin
		assert(o_nl_hexbits == { 1'b0, fvword[35:30] });
		assert(r_len == 3'b011);
		assert(r_word == fvword[29:0]);
		assert(o_busy && o_stb);
		end
	4'b0010: begin
		assert(o_nl_hexbits == { 1'b0, fvword[29:24] });
		assert(r_len == 3'b010);
		assert(r_word == { fvword[23:0], fvword[5:0] });
		assert(o_busy && o_stb);
		end
	4'b0100: begin
		assert(o_nl_hexbits == { 1'b0, fvword[23:18] });
		assert(r_len == 3'b001);
		assert(r_word == { fvword[17:0], {(2){fvword[5:0]}} });
		assert(o_busy && o_stb);
		end
	4'b1000: begin
		assert(o_nl_hexbits == 7'h40);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	two_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		two_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b010)
		two_seq <= 1;
	else if (!i_tx_busy)
		two_seq <= two_seq << 1;

	always @(*)
	case(two_seq)
	0: begin end // This is the idle state, no assertions required
	3'b001: begin
		assert(o_nl_hexbits == { 1'b0, fvword[35:30] });
		assert(r_len == 3'b010);
		assert(r_word == fvword[29:0]);
		assert(o_busy && o_stb);
		end
	3'b010: begin
		assert(o_nl_hexbits == { 1'b0, fvword[29:24] });
		assert(r_len == 3'b001);
		assert(r_word == { fvword[23:0], fvword[5:0] });
		assert(o_busy && o_stb);
		end
	3'b100: begin
		assert(o_nl_hexbits == 7'h40);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase


	////////////////////////////////////////////////////////////////////////

	initial	one_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		one_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b001)
		one_seq <= 1;
	else if (!i_tx_busy)
		one_seq <= one_seq << 1;

	always @(*)
	case(one_seq)
	2'b00: begin end // This is the idle state, no assertions required
	2'b01: begin
		assert(o_nl_hexbits == { 1'b0, fvword[35:30] });
		assert(r_len == 3'b001);
		assert(o_busy && o_stb);
		end
	2'b10: begin
		assert(o_nl_hexbits == 7'h40);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////
	always @(*)
	assert(o_busy == (|{ six_seq, five_seq, four_seq, three_seq, two_seq, one_seq }));

`endif
// }}}
endmodule

