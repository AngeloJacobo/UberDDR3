////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmibitsync.v
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
`default_nettype none
// }}}
module	hdmibitsync (
		// {{{
		input	wire		i_pix_clk, i_reset,
		//
		input	wire	[9:0]	i_r, i_g, i_b,
		output	reg	[9:0]	o_r, o_g, o_b,
		//
		output	wire	[31:0]	o_sync_word
		// }}}
	);

	// Register/net declarations
	// {{{
	wire	[9:0]	auto_r,   auto_g,   auto_b;
	wire	[4:0]	auto_bitslip_r, auto_bitslip_g, auto_bitslip_b;
	reg		all_locked;
	// }}}

	// Automatically synchronize to each color stream.
	// {{{
	// It is possible that we'll lock up to one color on one word and
	// another word on another cut.  Hence, we may still need to lock
	// the words together afterwards.
	hdmipixelsync	rasync(i_pix_clk, i_reset, i_r, auto_bitslip_r, auto_r);
	hdmipixelsync	gasync(i_pix_clk, i_reset, i_g, auto_bitslip_g, auto_g);
	hdmipixelsync	basync(i_pix_clk, i_reset, i_b, auto_bitslip_b, auto_b);
	// }}}

	// all_locked
	// {{{
	// True if all channels are locked.
	initial	all_locked = 0;
	always @(posedge i_pix_clk)
		all_locked <= ((auto_bitslip_r[4])
				&&(auto_bitslip_g[4])&&(auto_bitslip_b[4]));
	// }}}

	// o_r, o_g, o_b --- our bit-synchronized output channels
	// {{{
	always @(*)
	begin
		o_r = auto_r;
		o_g = auto_g;
		o_b = auto_b;
	end
	// }}}

	// o_sync_word
	// {{{
	// For reporting on the control bus: are we locked?  And if so, how?
	assign	o_sync_word = { 7'h0, !all_locked,
				3'h0, auto_bitslip_r,
				3'h0, auto_bitslip_g,
				3'h0, auto_bitslip_b };
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
