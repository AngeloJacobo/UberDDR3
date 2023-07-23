////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	clkcounter.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Given a clock, asynchronous to the main or system clock, and
//		given a PPS strobe that is synchronous to the main clock, count
//	the number of clock ticks that take place between system clocks.
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
`default_nettype	none
// }}}
module	clkcounter #(
		parameter	LGNAVGS = 4,
				BUSW=32,
		parameter	CLOCKFREQ_HZ = 100_000_000
	) (
		// {{{
		input	wire			i_sys_clk,
						i_tst_clk,
		input	wire			i_sys_pps,
		output	wire	[(BUSW-1):0]	o_sys_counts
		// }}}
	);

	// Local declarations
	// {{{
	reg	[(LGNAVGS-1):0]		avgs;
	(* ASYNC_REG = "TRUE" *)
	reg				q_v, qq_v;
	reg				tst_posedge;

	reg	[(BUSW-LGNAVGS-1):0]	counter;
	reg	[(BUSW-LGNAVGS-1):0]	r_sys_counts;
	wire				sys_pps;
	// }}}

	// Move the clock across clock domains
	// {{{
	always @(posedge i_tst_clk)
		avgs <= avgs + 1'b1;

	always @(posedge i_sys_clk)
		{ qq_v, q_v } <= { q_v, avgs[(LGNAVGS-1)] };

	always @(posedge i_sys_clk)
		tst_posedge <= (!qq_v)&&(q_v);
	// }}}

	// Generate a once per second pulse
	// {{{
	generate if (CLOCKFREQ_HZ > 0)
	begin : GEN_PPS
		localparam	CWID = $clog2(CLOCKFREQ_HZ+1);
		reg	[CWID-1:0]	pps_counter;
		reg			r_sys_pps;

		initial	pps_counter = 0;
		always @(posedge i_sys_clk)
		if (pps_counter >= CLOCKFREQ_HZ-1)
		begin
			pps_counter <= 0;
			r_sys_pps <= 1;
		end else begin
			pps_counter <= pps_counter + 1;
			r_sys_pps <= 0;
		end

		assign	sys_pps = r_sys_pps;

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_sys_pps };
		// Verilator lint_on  UNUSED
	end else begin : COPY_PPS
		assign	sys_pps = i_sys_pps;
	end endgenerate
	// }}}

	// Now count edges between PPS signals
	// {{{
	always @(posedge i_sys_clk)
	if (sys_pps)
		counter <= 0;
	else if (tst_posedge)
		counter <= counter + 1'b1;

	always @(posedge i_sys_clk)
	if (sys_pps)
		r_sys_counts <= counter;
	// }}}

	assign	o_sys_counts = { r_sys_counts, {(LGNAVGS){1'b0}} };
endmodule
