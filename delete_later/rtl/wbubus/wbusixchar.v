////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbusixchar.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Supports a conversion from a six digit bus to a printable
//		ASCII character representing those six bits.  The encoding is
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
module	wbusixchar(
		// {{{
		input	wire		i_clk, i_reset,
		input	wire		i_stb,
		input	wire	[6:0]	i_bits,
		output	reg		o_stb,
		output	reg	[7:0]	o_char,
		output	wire		o_busy,
		input	wire		i_busy
		// }}}
	);

	// Local declarations
	// {{{
	reg	[6:0]	remap	[0:127];
	reg	[6:0]	newv;
	// }}}

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (!o_stb || !i_busy)
		o_stb <= i_stb;
	// }}}

	// newv
	// {{{
	integer	k;
	always @(*) begin
		for(k=0; k<128; k=k+1)
		begin
			newv = 0;
			// verilator lint_off WIDTH
			if (k >= 64)
				newv = 7'h0a;
			else if (k <= 6'h09) // A digit, WORKS
				newv = "0" + { 3'h0, k[3:0] };
			else if (k[5:0] <= 6'd35) // Upper case
				newv[6:0] = 7'h41 + { 1'h0, k[5:0] } - 7'd10; // -'A'+10
			else if (k[5:0] <= 6'd61)
				newv = 7'h61 + { 1'h0, k[5:0] } - 7'd36;// -'a'+(10+26)
			// verilator lint_on WIDTH
			else if (k[5:0] == 6'd62) // An '@' sign
				newv = 7'h40;
			else // if (i_char == 6'h63) // A '%' sign
				newv = 7'h25;

			remap[k] = newv;
		end
	end
	// }}}

	// o_char
	// {{{
	initial	o_char = 8'h00;
	always @(posedge i_clk)
	if (!o_busy)
		o_char <= { 1'b0, remap[i_bits] };
	// }}}

	assign	o_busy = o_stb && i_busy;
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
	reg	[7:0]	f_char;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	//
	// Here's the old encoding that "worked"
	//
	initial	f_char = 8'h00;
	always @(posedge i_clk)
	if ((i_stb)&&(!o_busy))
	begin
		if (i_bits[6])
			f_char <= 8'h0a;
		else if (i_bits[5:0] <= 6'h09) // A digit, WORKS
			f_char <= "0" + { 4'h0, i_bits[3:0] };
		else if (i_bits[5:0] <= 6'd35) // Upper case
			f_char <= "A" + { 2'h0, i_bits[5:0] } - 8'd10; // -'A'+10
		else if (i_bits[5:0] <= 6'd61)
			f_char <= "a" + { 2'h0, i_bits[5:0] } - 8'd36;// -'a'+(10+26)
		else if (i_bits[5:0] == 6'd62) // An '@' sign
			f_char <= 8'h40;
		else // if (i_char == 6'h63) // A '%' sign
			f_char <= 8'h25;
	end

	//
	// Now let's prove that the two encodings are equivalent
	always @(*)
	if (o_stb)
		assert(f_char == o_char);

	always @(posedge i_clk)
	if (f_past_valid && $past(o_stb && i_busy))
		assert($stable(o_char));
`endif
// }}}
endmodule

