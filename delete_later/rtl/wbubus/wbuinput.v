////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbuinput.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Coordinates the receiption of bytes, which are then translated
//		into codewords describing postential bus transactions.  This
//	includes turning the human readable bytes into more compact bits,
//	forming those bits into codewords, and decompressing any that reference
//	addresses within a compression table.
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
module	wbuinput #(
		parameter OPT_COMPRESSION = 1'b1
	) (
		// {{{
		input	wire		i_clk, i_reset,
					i_stb,
		output	wire		o_busy,
		input	wire	[7:0]	i_byte,
		output	wire		o_soft_reset,
		output	wire		o_stb,
		input	wire		i_busy,
		output	wire	[35:0]	o_codword,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	wire		hx_stb, hx_valid;
	wire	[5:0]	hx_hexbits;

	wire		cw_stb, cw_busy, cw_active;
	wire	[35:0]	cw_word;

	wire		cod_busy, cod_active;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Turn our human-readable characters to raw 6-bit words
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbutohex
	tobits(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(i_stb), .o_busy(o_busy), .i_byte(i_byte),
		.o_soft_reset(o_soft_reset),
		.o_stb(hx_stb), .o_valid(hx_valid), .i_busy(cw_busy),
			.o_hexbits(hx_hexbits)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assemble the 6-bit words into 36-bit code words
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbureadcw
	formcw(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(hx_stb), .o_busy(cw_busy),
		.i_valid(hx_valid), .i_hexbits(hx_hexbits),
			.o_stb(cw_stb), .i_busy(cod_busy), .o_codword(cw_word),
			.o_active(cw_active)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// If using compression, uncompress the sent word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_COMPRESSION)
	begin : GEN_COMPRESSION

		wbudecompress
		unpack(
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_stb(cw_stb), .o_busy(cod_busy), .i_word(cw_word),
			.o_stb(o_stb),  .i_busy(i_busy),   .o_word(o_codword),
				.o_active(cod_active)
			// }}}
		);

	end else begin : NO_COMPRESSION
		// {{{
		assign	o_stb     = cw_stb;
		assign	o_codword = cw_word;
		assign	cod_busy  = i_busy;
		// }}}
	end endgenerate
	// }}}

	assign	o_active = i_stb || hx_stb || cw_active || cod_active;
endmodule
