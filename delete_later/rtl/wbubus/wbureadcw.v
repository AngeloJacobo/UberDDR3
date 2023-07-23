////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbureadcw.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Read bytes from a serial port (i.e. the jtagser) and translate
//		those bytes into a 6-byte codeword.  This codeword may specify
//	a number of values to be read, the value to be written, or an address
//	to read/write from, or perhaps the end of a write sequence.
//
//	See the encoding documentation file for more information.
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
//
// Goal: single clock pipeline, 50 slices or less
// }}}
module	wbureadcw #(
		parameter	OPT_SKIDBUFFER = 1'b0
	) (
		// {{{
		input	wire		i_clk, i_reset, i_stb,
		output	wire		o_busy,
		input	wire		i_valid,
		input	wire	[5:0]	i_hexbits,
		output	reg		o_stb,
		input	wire		i_busy,
		output	reg	[35:0]	o_codword,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	// Timing:
	//	Clock 0:	i_stb is high, i_valid is low
	//	Clock 1:	shiftreg[5:0] is valid, cw_len is valid
	//				r_len = 1
	//	Clock 2:	o_stb = 1, for cw_len = 1;
	//				o_codword is 1-byte valid
	//			i_stb may go high again on this clock as well.
	//	Clock 3:	o_stb = 0 (cw_len=1),
	//			cw_len = 0,
	//			r_len = 0 (unless i_stb)
	//			Ready for next word
	reg	[2:0]	r_len, cw_len;
	reg	[1:0]	lastcw;

	wire	w_stb;
	reg	[35:0]	shiftreg;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// A quick skid buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire		skd_stb, skd_valid;
	wire	[5:0]	skd_hexbits;
	reg		skd_busy;

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER
		// {{{
		reg		skd_full;
		reg	[6:0]	skd_data, skd_result;

		initial	skd_full = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			skd_full <= 1'b0;
		else if (i_stb && !o_busy && skd_stb && skd_busy)
			skd_full <= 1'b1;
		else if (!skd_busy)
			skd_full <= 1'b0;

		always @(posedge i_clk)
		if (skd_stb && skd_busy)
			skd_data <= { i_valid, i_hexbits };

		always @(*)
		if (skd_full)
			skd_result = skd_data;
		else
			skd_result = { i_valid, i_hexbits };

		assign	{ skd_valid, skd_hexbits } = skd_result;
		assign	skd_stb = skd_full || i_stb;
		assign	o_busy  = skd_full;
		// }}}
	end else begin : NO_SKIDBUFFER
		// {{{
		assign	skd_stb = i_stb;
		assign	{ skd_valid, skd_hexbits } = { i_valid, i_hexbits };
		assign	o_busy   = skd_busy;
		// }}}
	end endgenerate
	// }}}

	// w_stb will be true if o_stb is about to be true on the next clock
	assign	w_stb = ((r_len == cw_len)&&(cw_len != 0))
			||( skd_stb && !skd_busy && !skd_valid &&(lastcw == 2'b01));

	always @(*)
	begin
		skd_busy = o_stb && i_busy && (r_len == cw_len && cw_len != 0);

		if (o_stb && i_busy && !skd_valid && lastcw == 2'b01)
			skd_busy = 1'b1;
		if (!skd_valid && lastcw == 2'b01 && cw_len != 0 && r_len == cw_len)
			skd_busy = 1'b1;
	end

	// r_len
	// {{{
	// r_len is the length of the codeword as it exists
	// in our register
	initial r_len = 3'h0;
	always @(posedge i_clk)
	if (i_reset)
		r_len <= 0;
	else if (!o_stb || !i_busy || !w_stb)
	begin
		if (skd_stb && !skd_busy && !skd_valid) // Newline reset
			r_len <= 0;
		else if (r_len == cw_len && cw_len != 0)
			// We've achieved a full length code word.
			// reset/restart or counter w/o the newline
			r_len <= (skd_stb && !skd_busy) ? 3'h1 : 0;
		else if (skd_stb && !skd_busy) //in middle of word
			r_len <= r_len + 3'h1;
	end
	// }}}

	// shiftreg -- assemble a code word, 6-bits at a time
	// {{{
	initial	shiftreg = 0;
	always @(posedge i_clk)
	if (skd_stb && !skd_busy)
	begin
		if (r_len == cw_len && cw_len != 0)
			shiftreg[35:30] <= skd_hexbits;
		else case(r_len)
		3'b000: shiftreg[35:30] <= skd_hexbits;
		3'b001: shiftreg[29:24] <= skd_hexbits;
		3'b010: shiftreg[23:18] <= skd_hexbits;
		3'b011: shiftreg[17:12] <= skd_hexbits;
		3'b100: shiftreg[11: 6] <= skd_hexbits;
		3'b101: shiftreg[ 5: 0] <= skd_hexbits;
		default: begin end
		endcase
	end
	// }}}

	// lastcw
	// {{{
	initial	lastcw = 2'b00;
	always @(posedge i_clk)
	if (i_reset)
		lastcw <= 2'b00;
	else if (o_stb && !i_busy)
		lastcw <= o_codword[35:34];
	// }}}

	// o_codword
	// {{{
	always @(posedge i_clk)
	if (!o_stb || !i_busy)
	begin
		o_codword <= shiftreg;

		if (skd_stb && !skd_busy && !skd_valid && lastcw == 2'b01)
			// End of write signal
			o_codword[35:30] <= 6'h2e;
	end
	// }}}

	// cw_len
	// {{{
	// How long do we expect this codeword to be?
	initial	cw_len = 3'b000;
	always @(posedge i_clk)
	if (i_reset)
		cw_len <= 0;
	else if (skd_stb && !skd_busy && !skd_valid)
		cw_len <= 0;
	else if (skd_stb && !skd_busy && ((cw_len == 0)|| w_stb))
	begin
		if (skd_hexbits[5:4] == 2'b11) // 2b vector read
			cw_len <= 3'h2;
		else if (skd_hexbits[5:4] == 2'b10) // 1b vector read
			cw_len <= 3'h1;
		else if (skd_hexbits[5:3] == 3'b010) // 2b compressed wr
			cw_len <= 3'h2;
		else if (skd_hexbits[5:3] == 3'b001) // 2b compressed addr
			cw_len <= 3'b010 + { 1'b0, skd_hexbits[2:1] };
		else // long write or set address
			cw_len <= 3'h6;
	end else if ((!o_stb || !i_busy) && (r_len == cw_len) && (cw_len != 0))
		cw_len <= 0;
	// }}}

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (!o_stb || !i_busy)
		o_stb <= w_stb;
	// }}}

	assign	o_active = skd_stb || r_len > 0;
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
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!skd_stb);
	else if ($past(skd_stb && skd_busy))
	begin
		assume(skd_stb);
		assume($stable(skd_valid));
		assume($stable(skd_hexbits));
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!o_stb);
	else if ($past(o_stb && i_busy))
	begin
		assume(o_stb);
		assume($stable(o_codword));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (o_stb && i_busy && w_stb)
		assert(skd_busy);

	always @(*)
		assert(r_len <= 6);

	always @(*)
		assert(r_len <= cw_len);

	always @(*)
	if (r_len > 0)
	begin
		casez(shiftreg[35:30])
		6'b11????: assert(cw_len == 3'h2);
		6'b10????: assert(cw_len == 3'h1);
		6'b010???: assert(cw_len == 3'h2);
		6'b001???: assert(cw_len == 3'h2 + { 1'b0, shiftreg[32:31] });
		default:	assert(cw_len == 3'h6);
		endcase
	end else
		assert(cw_len == 0);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin end
	else if ($past(skd_stb && !skd_busy && !skd_valid && lastcw == 2'b01))
		assert(o_stb && o_codword[35:30] == 6'h2e);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin end
	else if ($past(!o_stb || !i_busy) && $past(cw_len > 0 && r_len == cw_len))
		assert(o_stb && o_codword == $past(shiftreg));

`endif
// }}}
endmodule

