////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbucompactlines.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Removes 'end of line' characters placed at the end of every
//		deworded word, unless we're idle or the line is too long.
//	This helps to format the output nicely to fit in an 80-character
//	display, should you need to do so for debugging.
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
//
// When to apply a new line?
//	When no prior new line exists
//		or when prior line length exceeds (72)
//	Between codewords (need inserted newline)
//	When bus has become idle (~wb_cyc)&&(~busys)
//
// So, if every codeword ends in a newline, what we
// really need to do is to remove newlines.  Thus, if
// i_stb goes high while i_tx_busy, we skip the newline
// unless the line is empty.  ... But i_stb will always
// go high while i_tx_busy.  How about if the line
// length exceeds 72, we do nothing, but record the
// last word.  If the last word was a  <incomplete-thought>
//
`default_nettype none
// }}}
module	wbucompactlines (
		// {{{
		input	wire		i_clk, i_reset, i_stb,
		input	wire	[6:0]	i_nl_hexbits,
		output	reg		o_stb,
		output	reg	[6:0]	o_nl_hexbits,
		input	wire		i_bus_busy,
		input	wire		i_tx_busy,
		output	wire		o_busy,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[6:0]	MAX_LINE_LENGTH = 79;
	localparam	[6:0]	TRIGGER_LENGTH = (MAX_LINE_LENGTH-6);
	reg		last_out_nl, last_in_nl, full_line, r_busy;
	reg	[6:0]	linelen;
	// }}}

	// last_out_nl
	// {{{
	initial	last_out_nl = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		last_out_nl <= 1'b1;
	else if (!i_tx_busy && o_stb)
		last_out_nl <= o_nl_hexbits[6];
	// }}}

	// last_in_nl
	// {{{
	initial	last_in_nl = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		last_in_nl <= 1'b1;
	else if (i_stb && !o_busy)
		last_in_nl <= i_nl_hexbits[6];
	// }}}

	// linelen
	// {{{
	// Now, let's count how long our lines are
	initial	linelen = 7'h00;
	always @(posedge i_clk)
	if (i_reset)
		linelen <= 0;
	else if (!i_tx_busy && o_stb)
	begin
		if (o_nl_hexbits[6])
			linelen <= 0;
		else
			linelen <= linelen + 7'h1;
	end
	// }}}

	// full_line
	// {{{
	initial	full_line = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		full_line <= 0;
	else if (!i_tx_busy && o_stb)
	begin
		if (o_nl_hexbits[6])
			full_line <= 0;
		else
			full_line <= (linelen >= TRIGGER_LENGTH);
	end
	// }}}


	// o_stb, o_nl_hexbits
	// {{{
	// Now that we know whether or not the last character was a newline,
	// and indeed how many characters we have in any given line, we can
	// selectively remove newlines from our output stream.
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	begin
		if (i_stb && !o_busy)
		begin
			// Only accept incoming newline requests if our line is
			// already full, otherwise quietly suppress them
			o_stb <= (full_line)||(!i_nl_hexbits[6]);
			o_nl_hexbits <= i_nl_hexbits;
		end else if (!o_busy)
		begin // Send an EOL if we are idle

			// Without a request, we'll add a newline, but only if
			//	1. There's nothing coming down the channel
			//		(!bus_busy)
			//	2. What we last sent wasn't a new-line
			//	3. The last thing that came in was a newline
			// In otherwords, we can resurrect one of the newlines
			// we squashed above
			o_stb <= (!i_tx_busy)&&(!i_bus_busy)&&(!last_out_nl)&&(last_in_nl);
			o_nl_hexbits <= 7'h40;
		end else if (!i_tx_busy)
			o_stb <= 1'b0;

		if (i_reset)
			o_stb <= 1'b0;
	end
	// }}}

	// o_busy
	// {{{
	initial	r_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_busy <= 1'b0;
	else
		r_busy <= o_stb && i_tx_busy;

	assign	o_busy = (r_busy)||(o_stb);
	// }}}

	assign	o_active = i_stb || (i_tx_busy && !last_out_nl && last_in_nl);
	/*
	output	wire	[27:0]	o_dbg;
	assign o_dbg = { o_stb, o_nl_hexbits, o_busy, r_busy, full_line,
			i_bus_busy, linelen, i_tx_busy, i_stb, i_nl_hexbits };
	*/
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
	localparam	F_MAX_WORD_LENGTH = 6;
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[2:0]	f_nonnl_count;

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!i_stb);
	end else if (f_past_valid && $past(i_stb && o_busy))
	begin
		assume(i_stb);

		// Our protocol actually allows i_nl_hexbits to change
		// while i_stb is true
	end

	always @(*)
	if (i_stb && i_nl_hexbits[6])
		assume(i_nl_hexbits[5:0] == 0);

	initial	f_nonnl_count = 0;
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	begin
		if (i_nl_hexbits[6])
			f_nonnl_count <= 0;
		else
			f_nonnl_count <= f_nonnl_count + 1;;
	end

	always @(*)
		assume(f_nonnl_count <= F_MAX_WORD_LENGTH);

	////////////////////////////////////////////////////////////////////////
	//
	// The contract
	//	- All incoming data must go out
	//		(if incoming[6], incoming == 7'h40)
	//	- save that newlines may be suppressed
	//	- Prove that the output will always be less than 80 characters
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_pending_nl;


	always @(*)
		assert(linelen <= MAX_LINE_LENGTH);

	// The outgoing channel doesn't change unless/until it has been
	// accepted
	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && o_stb && i_tx_busy))
		assert(o_stb && $stable(o_nl_hexbits));

	// Requested (non-newline) incoming data always goes to the outgoing
	// channel unmolested
	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && i_stb
				&& !o_busy && !i_nl_hexbits[6]))
		assert(o_stb && (o_nl_hexbits == $past(i_nl_hexbits)));

	always @(*)
		assert(full_line == (linelen > TRIGGER_LENGTH));

	always @(*)
	if (o_stb && !o_nl_hexbits[6])
		assert(linelen + 1 <= MAX_LINE_LENGTH);

	always @(*)
	if (!o_stb || !o_nl_hexbits[6])
		assert((F_MAX_WORD_LENGTH - f_nonnl_count) + linelen
			+ ((o_busy&&!o_nl_hexbits[6]) ? 1:0) <=MAX_LINE_LENGTH);

	always @(*)
	if (o_stb && o_nl_hexbits[6])
		assert(o_nl_hexbits[5:0] == 0);

	initial	f_pending_nl = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_pending_nl <= 0;
	else if (i_stb && !o_busy)
		f_pending_nl <= (i_nl_hexbits[6]) && !last_out_nl;
	else if (o_stb && o_nl_hexbits[6])
		f_pending_nl <= 0;

	always @(*)
	if (!last_in_nl)
		assert(!o_stb || !o_nl_hexbits[6]);

	always @(*)
	if (last_in_nl && !last_out_nl)
		assert(f_pending_nl || (o_stb && o_nl_hexbits[6]));
	else if (!o_stb || !o_nl_hexbits[6])
		assert(f_pending_nl == 1'b0);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(!o_stb || !i_tx_busy))
	begin
		if (o_stb && o_nl_hexbits[6])
			assert(f_pending_nl);
	end

	always @(*)
	if (last_in_nl)
		assert(!o_stb || o_nl_hexbits[6]);

	always @(*)
	if (last_out_nl)
		assert(last_in_nl || (o_stb && !o_nl_hexbits[6]));

	always @(*)
	if (last_out_nl)
	begin
		assert(linelen == 0);
		assert(!o_stb || !o_nl_hexbits[6]);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg		f_cvr_valid;
	reg	[5:0]	f_cvr_counter;

	initial	f_cvr_counter = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_cvr_counter <= 0;
	else if (i_stb && !o_busy && !i_nl_hexbits[6])
		f_cvr_counter <= f_cvr_counter + 1;

	initial	f_cvr_valid = 1;
	always @(posedge i_clk)
	if (i_reset)
		f_cvr_valid <= 0;
	else if (i_stb && !i_nl_hexbits[6]
			&& (i_nl_hexbits[5:0] != f_cvr_counter))
		f_cvr_valid <= 0;

	always @(*)
		cover(f_cvr_valid && (linelen == MAX_LINE_LENGTH));
	always @(*)
		cover(f_cvr_valid && o_stb && !i_tx_busy && o_nl_hexbits[6]);
`endif
// }}}
endmodule
