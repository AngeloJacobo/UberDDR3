////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbuoutput.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Converts 36-bit codewords into bytes to be placed on the serial
//		output port.  The codewords themselves are the results of bus
//	transactions, which are then (hopefully) compressed within here and
//	carefully arranged into "lines" for visual viewing (if necessary).
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
module	wbuoutput #(
		parameter [0:0]	OPT_COMPRESSION = 1'b1,
		parameter [0:0]	OPT_IDLES = 1'b1
	) (
		// {{{
		input	wire		i_clk, i_reset, i_soft_reset,
		input	wire		i_stb,
		output	wire		o_busy,
		input	wire	[35:0]	i_codword,
		// Not Idle indicators
		input	wire		i_wb_cyc, i_int, i_bus_busy,
		// Outputs to our UART transmitter
		output	wire		o_stb, o_active,
		output	wire	[7:0]	o_char,
		//
		input	wire		i_tx_busy
		// }}}
	);

	// Local declarations
	// {{{
	wire		dw_busy;

	wire		cw_stb, cw_busy, cp_stb, dw_stb, ln_stb, ln_busy,
			cp_busy, byte_busy;
	wire		cp_active, dw_active, ln_active;
	wire	[35:0]	cw_codword, cp_word;
	wire	[6:0]	dw_bits, ln_bits;

	reg		r_active;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Insert interrupt notifications and idle words
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_IDLES)
	begin : GEN_IDLES
		wbuidleint
		buildcw(
			// {{{
			.i_clk(i_clk), .i_reset(i_soft_reset),
			.i_stb(i_stb), .i_codword(i_codword),
			.i_cyc(i_wb_cyc), .i_busy(i_bus_busy), .i_int(i_int),
			.o_stb(cw_stb), .o_codword(cw_codword),
				.o_busy(cw_busy), .i_tx_busy(cp_stb && cp_busy)
			// }}}
		);

		assign	o_busy = cw_busy;

	end else begin : NO_IDLE_INSERTION

		assign	cw_stb = i_stb;
		assign	cw_codword = i_codword;
		assign	o_busy  = cp_busy;
		assign	cw_busy = cp_busy;

		// Verilator lint_off UNUSED
		wire	unused_idle;
		assign	unused_idle = &{ 1'b0, i_int };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Compression
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// cw_busy & cw_stb, not cp_stb, but dw_busy
	//

	generate if (OPT_COMPRESSION)
	begin : GEN_COMPRESSION

		wbucompress
		packit(
			// {{{
			.i_clk(i_clk), .i_reset(i_soft_reset),
			.i_stb(cw_stb), .i_codword(cw_codword),
			.i_busy(dw_busy), .o_active(cp_active),
			.o_stb(cp_stb), .o_cword(cp_word), .o_busy(cp_busy)
			// }}}
		);

	end else begin : NO_COMPRESSION

		assign	cp_stb = cw_stb;
		assign	cp_word = cw_codword;
		assign	cp_busy = dw_busy;
		assign	cp_active = cw_stb;

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Split the 36-bits words into a stream of 6 bit serial words
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbudeword
	deword(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(cp_stb), .i_word(cp_word), .i_tx_busy(ln_busy),
		.o_stb(dw_stb), .o_nl_hexbits(dw_bits), .o_busy(dw_busy),
			.o_active(dw_active)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Remove line feeds, compacting things into 80-char lines
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbucompactlines
	linepacker(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(dw_stb), .i_nl_hexbits(dw_bits),
		.o_stb(ln_stb), .o_nl_hexbits(ln_bits),
			.o_active(ln_active),
		.i_bus_busy(i_wb_cyc||i_bus_busy||cw_busy),
		.i_tx_busy(byte_busy), .o_busy(ln_busy)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Convert the binary outputs to readable characters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbusixchar
	mkbytes(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(ln_stb), .i_bits(ln_bits),
		.o_stb(o_stb), .o_char(o_char), .o_busy(byte_busy),
		.i_busy(i_tx_busy)
		// }}}
	);

	// }}}

	// Try to determine the last value:
	//	o_last = o_stb || !r_active
	always @(posedge i_clk)
	if (i_reset)
		r_active <= 0;
	else if (i_stb || dw_active || cp_active || cw_stb || cp_stb || dw_stb
			|| ln_active)
		r_active <= 1;
	else if (!i_tx_busy)
		r_active <= 0;

	assign	o_active = r_active || ln_stb;
endmodule
