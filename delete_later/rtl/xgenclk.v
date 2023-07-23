////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xgenclk.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This module works in conjunction with the genclk module to
//		generate  clock with an arbitrary frequency.  The genclk
//	module creates an 8-bit word.
//
//	The module is nominally designed for a 100MHz clock input.  Using a
//	100 MHz clock input, the maximum clock speed that can be created is
//	about 166MHz.
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
//
// `define	DIFFERENTIAL
// }}}
module	xgenclk #(
		parameter [0:0]	OPT_LCLCLOCK = 1'b0
	) (
		// {{{
		input	wire		i_clk, i_ce,
		input	wire		i_hsclk,	// @ 4x i_clk frequency
		input	wire	[7:0]	i_word,
		output	wire	[1:0]	o_pin,
		output	wire		o_clk
		// }}}
	);

	// Local declarations
	// {{{
	wire	[5:0]	ignored_data;
	wire	[1:0]	slave_to_master;

	wire		pll_input, w_pin, high_z;
	reg	[7:0]	r_word;
	reg	[1:0]	r_ce;
	// }}}

	initial	r_ce = 2'b00;
	always @(posedge i_clk)
		r_ce <= { r_ce[0], i_ce };
	always @(posedge i_clk)
		r_word <= i_word;

	OSERDESE2	#(
		// {{{
		.DATA_RATE_OQ("DDR"), // DDR goes up to 950MHz, SDR only to 600
		.DATA_RATE_TQ("SDR"),
		.DATA_WIDTH(8),
		.SERDES_MODE("MASTER"),
		.TRISTATE_WIDTH(1)	// Really ... this is unused
		// }}}
	) u_lowserdes(
		// {{{
		// Verilator lint_off PINCONNECTEMPTY
		.OCE(r_ce[1]),
		.TCE(1'b1),	.TFB(), .TQ(high_z),
		.CLK(i_hsclk),	// HS clock
		.CLKDIV(i_clk),	// Divided clock input (lowspeed clock)
		.OQ(w_pin),	// Data path to IOB *only*
		.OFB(),	// Data path output feedback to ISERDESE2 or ODELAYE2
		.D1(r_word[7]),
		.D2(r_word[6]),
		.D3(r_word[5]),
		.D4(r_word[4]),
		.D5(r_word[3]),
		.D6(r_word[2]),
		.D7(r_word[1]),
		.D8(r_word[0]),
		.RST(1'b0), // .RST(!r_ce[1]),
		.TBYTEIN(1'b0), .TBYTEOUT(),
		.T1(1'b0), .T2(1'b0), .T3(1'b0), .T4(1'b0),
		.SHIFTIN1(), .SHIFTIN2(),
		.SHIFTOUT1(), .SHIFTOUT2()
		// Verilator lint_on  PINCONNECTEMPTY
		// }}}
	);

	generate if (OPT_LCLCLOCK)
	begin : GEN_CLK_REFLECTION
		// {{{
		wire	w_clk;

		// IOBUFDS
		// u_genclkio(
		//	.T(high_z),.I(w_pin),.IO(o_pin[1]), .IOB(o_pin[0]),
		//	.O(w_clk)
		// );

		IOBUF u_genclkio_p(.T(high_z),.I(w_pin),.IO(o_pin[1]),
				.O(w_clk));
		// OBUF u_genclkio_n(.T(high_z),.I(w_pin),.IO(!o_pin[0]));
		assign o_pin[0] = 1'b0;
		// OBUF u_genclkio_n(.T(high_z),.I(w_pin),.IO(!o_pin[0]));

		// BUFG	clkgen_buf(.I(w_clk), .O(o_clk));
		// BUFR	#(.BUFR_DIVIDE("BYPASS"), .SIM_DEVICE("7SERIES")) clkgen_buf(.I(w_clk), .O(o_clk));
		// BUFH	clkgen_buf(.I(w_clk), .O(o_clk));
		// wire tmp; BUFMR	clkgen_buf(.I(w_clk), .O(tmp)); BUFR aux(.I(tmp), .O(o_clk));
		assign	o_clk = w_clk;
		// }}}
	end else begin : NO_REFLECTION
		OBUFDS
		u_genclkio(
			.I(w_pin), .O(o_pin[1]), .OB(o_pin[0])
		);

		assign	o_clk = 1'b0;
	end endgenerate

endmodule
