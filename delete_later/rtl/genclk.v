////////////////////////////////////////////////////////////////////////////////
//
// Filename:	genclk.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To generate a clock using digital logic, but one that switches
//		at the right speed overall.
//
//	This particular component takes the desired clock stepping word
//	(2^32 / desired_frequency) and uses it to generate a clock at the
//	desired_frequency rate.
//
//	The output itself is 8 steps of that clock, necessitating an 8x
//	output serdes to create a clock from this output word.  As a result,
//	the phase error on the output of this routine will be (at a maximum)
//	1/16th the duration of i_clk--allowing more flexibility in clock
//	generation.
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
module	genclk #(
		parameter	BW=32,		// The bus width
		localparam	UPSAMPLE=8	// Upsample factor
	) (
		// {{{
		input	wire				i_clk,
		input	wire	[(BW-1):0]		i_delay,
		output	reg	[(UPSAMPLE-1):0]	o_word,
		output	reg				o_stb
		// }}}
	);

	// Local declarations
	// {{{
	reg	[(BW-1):0]	counter [0:(UPSAMPLE-1)];
	reg	[(BW-1):0] r_delay;

	reg	[(BW-1):0] times_three;
	reg	[(BW-1):0] times_five;
	reg	[(BW-1):0] times_seven;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Helpers: times_three, five, and seven
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
		times_three <= { i_delay[(BW-2):0], 1'b0 } + i_delay;

	always @(posedge i_clk)
		times_five  <= { i_delay[(BW-3):0], 2'b0 } + i_delay;

	always @(posedge i_clk)
		times_seven <= { i_delay[(BW-4):0], 3'b0 } - i_delay;

	// Keep these all aligned.
	always @(posedge i_clk)
		r_delay <= i_delay;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate 8-phases of a counter that adds i_delay on each 8th clock
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)	// Times one
		counter[1] <= counter[0] + r_delay;

	always @(posedge i_clk)	// Times two
		counter[2] <= counter[0] + { r_delay[(BW-2):0], 1'b0 };

	always @(posedge i_clk) // Times three
		counter[3] <= counter[0] + times_three;

	always @(posedge i_clk) // Times four
		counter[4] <= counter[0] + { r_delay[(BW-3):0], 2'b0 };

	always @(posedge i_clk) // Times five
		counter[5]  <= counter[0] + times_five;

	always @(posedge i_clk)
		counter[6]  <= counter[0] + { times_three[(BW-2):0], 1'b0 };

	always @(posedge i_clk)
		counter[7] <= counter[0] + times_seven;

	always @(posedge i_clk) // Times eight---and generating the next clk wrd
		{ o_stb, counter[0] }  <= counter[0] + { r_delay[(BW-4):0], 3'h0 };

	always @(posedge i_clk)
		o_word <= {	// High order bit is "first"
			counter[1][(BW-1)],
			counter[2][(BW-1)],
			counter[3][(BW-1)],
			counter[4][(BW-1)],
			counter[5][(BW-1)],
			counter[6][(BW-1)],
			counter[7][(BW-1)],
			counter[0][(BW-1)]
		};
	// }}}
endmodule
