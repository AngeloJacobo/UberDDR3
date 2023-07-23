////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xhdmiin.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
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
//
`default_nettype	none
// }}}
module	xhdmiin #(
		parameter	DC = 0
	) (
		// {{{
		input	wire		i_clk,		// Pixel clock
					i_hsclk,	// 10x pixel clock
					i_ce,
		input	wire	[4:0]	i_delay,
		output	wire	[4:0]	o_delay,
		input	wire	[1:0]	i_hs_wire,
		output	wire	[9:0]	o_word
		// }}}
	);

	// Local declarations
	// {{{
	wire		w_ignored;
	wire	[9:0]	w_word;

	wire	w_hs_wire, w_hs_delayed_wire;
	// }}}

	// Convert from differential to internal
	// {{{
	IBUFDS
	hdmibuf(
		.I(i_hs_wire[1]), .IB(i_hs_wire[0]),
		.O(w_hs_wire)
	);
	// }}}

	// Now separate us into the various bits
	// {{{
	xhdmiin_deserdes
	the_deserdes(
		.i_clk(i_clk),
		.i_hsclk(i_hsclk),
		.i_ce(i_ce),
		.i_delay(i_delay),
		.o_delay(o_delay),
		.i_pin(w_hs_wire),
		.o_wire(w_ignored),
		.o_word(o_word)		// Decoded data to send to 10B/8B decode
	);
	// }}}
endmodule
