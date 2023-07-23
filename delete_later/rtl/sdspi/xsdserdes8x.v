////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xsdserdes8x.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	An 8:1 OSERDES followed by an (optional) 1:8 ISERDES.  That
//		simple, nothing more.  This implementation is specific to
//	Xilinx FPGAs.  It's designed, however, so that it may be the only
//	component needing replacing when switching hardware platforms.
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
module	xsdserdes8x #(
		parameter [0:0]		OPT_BIDIR = 1'b1
	) (
		// {{{
		input	wire		i_clk, i_hsclk,
		// input	wire		i_reset,
		//
		input	wire		i_en,
		input	wire	[7:0]	i_data,
		//
		output	wire		io_tristate,
		output	wire		o_pin,
		input	wire		i_pin,
		//
		output	wire		o_raw,
		output	wire	[7:0]	o_wide
		// }}}
	);

`ifdef VERILATOR
	assign	io_tristate = 1'b1;
	assign	o_pin = 1'b1;
	assign	o_wide = 8'h0;
	assign	o_raw = i_pin;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = i_pin;
	// Verilator lint_on  UNUSED
`else
	wire	w_pin, w_in, w_reset, high_z, fabric_return;
	assign	w_reset = 1'b0;	// Active high reset

	OSERDESE2 #(
		// {{{
		.DATA_RATE_OQ("DDR"),
		.DATA_RATE_TQ("SDR"),
		.DATA_WIDTH(8),
		.SERDES_MODE("MASTER"),
		.TRISTATE_WIDTH(1)
		// }}}
	) u_oserdes (
		// {{{
		// Verilator lint_off PINCONNECTEMPTY
		.OCE(1'b1), .TCE(1'b1), .TFB(), .TQ(high_z),
		.CLK(i_hsclk), .CLKDIV(i_clk), .OQ(w_pin), .OFB(fabric_return),
		.D1(i_data[7]),	.D2(i_data[6]),
		.D3(i_data[5]),	.D4(i_data[4]),
		.D5(i_data[3]),	.D6(i_data[2]),
		.D7(i_data[1]),	.D8(i_data[0]),
		.RST(w_reset), .TBYTEIN(1'b0), // .TBYTEOUT(),
		.T1(!i_en && OPT_BIDIR), .T2(1'b0), .T3(1'b0), .T4(1'b0)
		// .SHIFTIN1(), .SHIFTIN2(), .SHIFTOUT1(), .SHIFTOUT2()
		// Verilator lint_on  PINCONNECTEMPTY
		// }}}
	);

	// Actual buffers are held externally
	assign	io_tristate = high_z;
	assign	o_pin = w_pin;
	assign	w_in  = i_pin;

	generate if (OPT_BIDIR)
	begin : GEN_BIDIRECTIONAL

		ISERDESE2 #(
		// {{{
		.SERDES_MODE("MASTER"),
		.DATA_RATE("DDR"),
		.DATA_WIDTH(8),
		.INTERFACE_TYPE("NETWORKING"),
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.SYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		// }}}
		) u_iserdes (
		// {{{
		.BITSLIP(1'b0), .CE(1'b1), // .CE2(),
		.CLK(i_hsclk), .CLKB(!i_hsclk), .CLKDIV(i_clk), .CLKDIVP(1'b0),
		.D(w_in), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0), // .DDLY()
		.OCLK(1'b0), .OCLKB(1'b0), .O(o_raw), // .OFB(),
		.Q1(o_wide[0]),	.Q2(o_wide[1]),
		.Q3(o_wide[2]),	.Q4(o_wide[3]),
		.Q5(o_wide[4]),	.Q6(o_wide[5]),
		.Q7(o_wide[6]),	.Q8(o_wide[7]),
		.RST(w_reset)
		// .SHIFTIN1(), .SHIFTIN2(), .SHIFTOUT1(), .SHIFTOUT2()
		// }}}
		);
	end else begin : GEN_OUTPUT

		assign	o_wide = 8'h0;
		assign	o_raw  = fabric_return;

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, w_in };
		// Verilator lint_on  UNUSED
	end endgenerate
`endif	// VERILATOR
endmodule
