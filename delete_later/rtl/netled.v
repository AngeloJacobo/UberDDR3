////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	netled
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Produce an LED sequence onto the Ethernet 10Gb LEDs which can
//		be used to demonstrate that the LEDs work as desired.  This
//	is scaffolding IP, and will be tossed rather than used in operation.
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
`default_nettype	none
// }}}
module	netled #(
		parameter	NLINKS=4
	) (
		input	wire	i_clk,
		output	reg	[NLINKS-1:0]	o_linkup,
		output	reg	[NLINKS-1:0]	o_activity
	);

	reg		r_pps;
	reg	[39:0]	rtl_counter;
	reg	[6:0]	s_counter;

	initial	rtl_counter = 0;
	always @(posedge i_clk)
		{ r_pps, rtl_counter } <= rtl_counter + 40'd10_995;

	always @(posedge i_clk)
	if (r_pps)
		{ s_counter } <= s_counter + 1;


	always @(posedge i_clk)
	case(s_counter[6:4])
	3'h0: begin
		o_linkup[0] <= s_counter[2:0] == 3'h0;
		o_linkup[1] <= s_counter[2:0] == 3'h1;
		o_linkup[2] <= s_counter[2:0] == 3'h2;
		o_linkup[3] <= s_counter[2:0] == 3'h3;

		o_activity <= 4'h0;
		end
	3'h1: begin
		o_linkup <= 4'h0;

		o_activity[0] <= s_counter[2:0] == 3'h0;
		o_activity[1] <= s_counter[2:0] == 3'h1;
		o_activity[2] <= s_counter[2:0] == 3'h2;
		o_activity[3] <= s_counter[2:0] == 3'h3;
		end
	3'h2: begin
		o_linkup[0] <= s_counter[2:0] == 3'h0;
		o_linkup[1] <= s_counter[2:0] == 3'h1;
		o_linkup[2] <= s_counter[2:0] == 3'h2;
		o_linkup[3] <= s_counter[2:0] == 3'h3;

		o_activity[0] <= s_counter[2:0] == 3'h0;
		o_activity[1] <= s_counter[2:0] == 3'h1;
		o_activity[2] <= s_counter[2:0] == 3'h2;
		o_activity[3] <= s_counter[2:0] == 3'h3;
		end
	3'h3: begin
		o_linkup[0] <= rtl_counter[37];
		o_linkup[1] <= rtl_counter[37];
		o_linkup[2] <= rtl_counter[37];
		o_linkup[3] <= rtl_counter[37];

		o_activity[0] <= rtl_counter[37] ^ s_counter[3];
		o_activity[1] <= rtl_counter[37] ^ s_counter[3];
		o_activity[2] <= rtl_counter[37] ^ s_counter[3];
		o_activity[3] <= rtl_counter[37] ^ s_counter[3];
		end
	3'h4: begin
		o_linkup[0] <= rtl_counter[38];
		o_linkup[1] <= rtl_counter[38];
		o_linkup[2] <= rtl_counter[38];
		o_linkup[3] <= rtl_counter[38];

		o_activity[0] <= rtl_counter[38] ^ s_counter[3];
		o_activity[1] <= rtl_counter[38] ^ s_counter[3];
		o_activity[2] <= rtl_counter[38] ^ s_counter[3];
		o_activity[3] <= rtl_counter[38] ^ s_counter[3];
		end
	3'h5: begin
		o_linkup[0] <= rtl_counter[39];
		o_linkup[1] <= rtl_counter[39];
		o_linkup[2] <= rtl_counter[39];
		o_linkup[3] <= rtl_counter[39];

		o_activity[0] <= rtl_counter[39] ^ s_counter[3];
		o_activity[1] <= rtl_counter[39] ^ s_counter[3];
		o_activity[2] <= rtl_counter[39] ^ s_counter[3];
		o_activity[3] <= rtl_counter[39] ^ s_counter[3];
		end
	3'h6: begin
		case({ s_counter[2:0], rtl_counter[39:38] })
		5'h00: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h01: { o_linkup, o_activity } <= { 4'h2, 4'h1 };
		5'h02: { o_linkup, o_activity } <= { 4'h4, 4'h2 };
		5'h03: { o_linkup, o_activity } <= { 4'h8, 4'h4 };
		5'h04: { o_linkup, o_activity } <= { 4'h4, 4'h8 };
		5'h05: { o_linkup, o_activity } <= { 4'h2, 4'h4 };
		5'h06: { o_linkup, o_activity } <= { 4'h1, 4'h2 };
		5'h07: { o_linkup, o_activity } <= { 4'h0, 4'h1 };
		//
		5'h08: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h09: { o_linkup, o_activity } <= { 4'h2, 4'h0 };
		5'h0a: { o_linkup, o_activity } <= { 4'h4, 4'h1 };
		5'h0b: { o_linkup, o_activity } <= { 4'h8, 4'h2 };
		5'h0c: { o_linkup, o_activity } <= { 4'h4, 4'h4 };
		5'h0d: { o_linkup, o_activity } <= { 4'h2, 4'h8 };
		5'h0e: { o_linkup, o_activity } <= { 4'h1, 4'h4 };
		5'h0f: { o_linkup, o_activity } <= { 4'h0, 4'h2 };
		//
		5'h10: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h11: { o_linkup, o_activity } <= { 4'h2, 4'h0 };
		5'h12: { o_linkup, o_activity } <= { 4'h4, 4'h0 };
		5'h13: { o_linkup, o_activity } <= { 4'h8, 4'h0 };
		5'h14: { o_linkup, o_activity } <= { 4'h8, 4'h1 };
		5'h15: { o_linkup, o_activity } <= { 4'h8, 4'h2 };
		5'h16: { o_linkup, o_activity } <= { 4'h8, 4'h4 };
		5'h17: { o_linkup, o_activity } <= { 4'h8, 4'h8 };
		//
		5'h18: { o_linkup, o_activity } <= { 4'h8, 4'h4 };
		5'h19: { o_linkup, o_activity } <= { 4'h8, 4'h2 };
		5'h1a: { o_linkup, o_activity } <= { 4'h8, 4'h1 };
		5'h1b: { o_linkup, o_activity } <= { 4'h8, 4'h0 };
		5'h1c: { o_linkup, o_activity } <= { 4'h4, 4'h0 };
		5'h1d: { o_linkup, o_activity } <= { 4'h2, 4'h0 };
		5'h1e: { o_linkup, o_activity } <= { 4'h1, 4'h0 };
		5'h1f: { o_linkup, o_activity } <= { 4'h0, 4'h0 };
		//
		endcase end
	default: begin
		o_linkup <= 0;
		o_activity <= 0;
		end
	endcase

endmodule
