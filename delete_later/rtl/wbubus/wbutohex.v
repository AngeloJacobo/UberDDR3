////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbutohex.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Supports a printable character conversion from a printable
//		ASCII character to six bits of valid data.  The encoding is
//		as follows:
//
//		0-9	->	0-9
//		A-Z	->	10-35
//		a-z	->	36-61
//		@	->	62
//		%	->	63
//
//		Note that decoding is stateless, yet requires one clock.
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
module	wbutohex (
		// {{{
		input	wire		i_clk, i_reset, i_stb,
		output	wire		o_busy,
		input	wire	[7:0]	i_byte,
		output	reg		o_soft_reset,
		output	reg		o_stb, o_valid,
		input	wire		i_busy,
		output	reg	[5:0]	o_hexbits
		// }}}
	);

	// Local declarations
	// {{{
	reg	[6:0]	remap	[0:127];
	integer	k;
	reg	[6:0]	newv;
	// }}}

	assign	o_busy = o_stb && i_busy;

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (!o_stb || !i_busy)
		o_stb <= i_stb;
	// }}}

	// newv, remap
	// {{{
	always @(*)
	// initial
	begin
		for(k=0; k<128; k=k+1)
		begin
			newv = 7'h40;
			// verilator lint_off WIDTH
			if ((k >= 48)&&(k <= 57)) // A digit
			begin
				newv = k;
				newv[6:4] = 3'b100;
			end else if ((k >= 65)&&(k <= 90)) // Upper case
			begin
				newv[5:0] = ((k&8'h3f) + 6'h09);// -'A'+10
				newv[6] = 1'b1;
			end else if ((k >= 97)&&(k <= 122))
				newv[5:0] = ((k&8'h3f) + 6'h03);	// -'a'+(10+26)
			// verilator lint_on WIDTH
			else if (k == 64) // An '@' sign
				newv[5:0] = 6'h3e;
			else if (k == 37) // A '%' sign
				newv[5:0] = 6'h3f;
			else
				newv = 0;

			remap[k] = newv;
		end
	end
	// }}}

	// o_valid
	// {{{
	always @(posedge i_clk)
	if (!o_stb || !i_busy)
	begin
		{ o_valid, o_hexbits } <= remap[i_byte[6:0]];
		if (i_byte[7])
			o_valid <= 0;
	end
	// }}}

	// o_soft_reset
	// {{{
	initial	o_soft_reset = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_soft_reset <= 1;
	else if (!o_stb || !i_busy)
		o_soft_reset <= i_stb && (i_byte[6:0] == 7'h3);
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
	reg		f_past_valid;
	reg		f_valid;
	reg	[5:0]	f_hexbits;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	// always @(*)
	//	assume((i_byte >= 8'h30) && (i_byte <= 8'h39));

	initial	f_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		f_valid   <= 1'b0;
		f_hexbits <= 6'h0;
	end else if (!o_stb || !i_busy)
	begin
		// These are the defaults, to be overwridden by the ifs below
		f_valid <= 1'b1;
		f_hexbits <= 6'h00;

		if ((i_byte >= 8'h30)&&(i_byte <= 8'h39)) // A digit
			f_hexbits <= { 2'b0, i_byte[3:0] };
		else if ((i_byte >= 8'h41)&&(i_byte <= 8'h5a)) // Upper case
			f_hexbits <= (i_byte[5:0] - 6'h01 + 6'h0a);// -'A'+10
		else if ((i_byte >= 8'h61)&&(i_byte <= 8'h7a))
			f_hexbits <= (i_byte[5:0] +6'h03);	// -'a'+(10+26)
		else if (i_byte == 8'h40) // An '@' sign
			f_hexbits <= 6'h3e;
		else if (i_byte == 8'h25) // A '%' sign
			f_hexbits <= 6'h3f;
		else
			f_valid <= 1'b0;
	end

	always @(*)
	if (o_stb)
	begin
		assert(f_valid == o_valid);
		if (o_valid)
			assert(f_hexbits == o_hexbits);
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_stb);
	else if ($past(i_stb && o_busy))
	begin
		assume(i_stb);
		assume($stable(i_byte));
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(i_stb && !o_busy))
		assert(o_stb);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_stb);
	else if ($past(o_stb && i_busy))
	begin
		assert(o_stb);
		assert($stable(o_valid));
		assert($stable(o_hexbits));
	end

`endif
// }}}
endmodule

