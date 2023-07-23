////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xsdddr.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	An 2:1 OSERDES followed by an (optional) 1:2 ISERDES implemented
//		via the Xilinx ODDR and IDDR elements.  That simple, nothing
//	more.  This implementation is specific to Xilinx FPGAs.  It's designed,
//	however, so that there may be a minimum number of components that
//	need replacing when switching hardware platforms.
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
`ifdef	VERILATOR
`define	OPENSIM
`endif
`ifdef	IVERILOG
`define	OPENSIM
`endif
// }}}
module	xsdddr #(
		parameter [0:0]		OPT_BIDIR = 1'b1
	) (
		// {{{
		input	wire		i_clk,
		//
		input	wire		i_en,
		input	wire	[1:0]	i_data,
		output	wire		io_pin_tristate,
		input	wire		i_pin,
		output	wire		o_pin,
		output	wire	[1:0]	o_wide
		// }}}
	);

	wire	w_in, w_out;
	reg	high_z;

	initial	high_z = OPT_BIDIR;
	always @(posedge i_clk)
		high_z <= !i_en && OPT_BIDIR;

`ifdef	OPENSIM
	// {{{
	reg	[1:0]	r_out;

	always @(posedge i_clk)
		r_out <= i_data;

	assign	w_out = (i_clk) ? r_out[1] : r_out[0];
	assign	io_pin_tristate = high_z;
	assign	o_pin = w_out;

	assign	w_in  = (high_z) ? i_pin : w_out;
	// }}}
`else
	ODDR #(
		// {{{
		.DDR_CLK_EDGE("SAME_EDGE"),
		.INIT(1'b1),
		.SRTYPE("SYNC")
		// }}}
	) u_oddr (
		// {{{
		.CE(1'b1), .R(1'b0), .S(1'b0),
		//
		.C(i_clk),
		.Q(w_out), .D1(i_data[1]), .D2(i_data[0])
		// }}}
	);

	assign	io_pin_tristate = high_z;
	assign	o_pin = w_out;
	assign	w_in  = i_pin;
`endif

	generate if (OPT_BIDIR)
	begin : GEN_BIDIRECTIONAL
		// {{{
`ifdef	OPENSIM
		reg		r_p, r_n;
		reg	[1:0]	r_in;

		always @(posedge i_clk)
			r_p <= w_in;
		always @(negedge i_clk)
			r_n <= w_in;
		always @(posedge i_clk)
			r_in <= { r_p, r_n };

		assign	o_wide = r_in;
`else
		IDDR #(
			.DDR_CLK_EDGE("SAME_EDGE_PIPELINED"),
			.INIT_Q1(1'b1),
			.INIT_Q2(1'b1),
			.SRTYPE("SYNC")
		) u_iddr (
			.Q1(o_wide[1]), .Q2(o_wide[0]),
			.C(i_clk), .CE(1'b1), .D(i_pin),
			.R(1'b0), .S(1'b0)
		);
`endif
		// }}}
	end else begin : GEN_OUTPUT

		assign	o_wide = 2'b11;

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0,
`ifdef	VERILATOR
				i_pin,
`endif
				w_in };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	end endgenerate
endmodule
