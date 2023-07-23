////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xhdmiin_deserdes.v
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
module	xhdmiin_deserdes #(
		parameter	DELAYSRC = "IDATAIN", IOBDELAY="IFD"
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_hsclk,
		input	wire		i_ce,
		input	wire	[4:0]	i_delay,
		output	wire	[4:0]	o_delay,
		input	wire		i_pin,
		output	wire		o_wire,
		output	reg	[9:0]	o_word
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[0:0]	OPT_BITREVERSE = 1'b0; // (Not required)

	wire	[5:0]	ignored_data;
	wire	[1:0]	master_to_slave;
	wire		ignored_output_hi;

	wire	w_hs_delayed_wire, w_hs_wire;
	wire	[9:0]	w_word;

	wire		async_reset;
	reg	[2:0]	reset_pipe;

	wire		lcl_ce;
	reg	[1:0]	syncd_ce;
	wire	[9:0]	w_use_this_word;
	// }}}

	// Turn i_ce into an async reset
	// {{{
	always @(posedge i_clk, negedge i_ce)
	if (!i_ce)
		reset_pipe[2:0] <= 3'h7;
	else
		reset_pipe[2:0] <= { reset_pipe[1:0], 1'b0 };
	assign	async_reset = reset_pipe[2];
	// }}}

	// Make sure i_ce is properly synchronized to the pixel clock
	// {{{
	always @(posedge i_clk)
		syncd_ce <= { syncd_ce[0], i_ce };
	assign	lcl_ce = syncd_ce[1];
	// }}}

	// Optionally delay the incoming signal
	// {{{
	generate if (IOBDELAY == "NONE")
	begin

		assign w_hs_wire         = i_pin;
		assign w_hs_delayed_wire = 1'b0;

	end else begin

		assign w_hs_wire = 1'b0;

		IDELAYE2	#(
			.CINVCTRL_SEL("FALSE"),
			.DELAY_SRC(DELAYSRC),
			.HIGH_PERFORMANCE_MODE("TRUE"),
			.REFCLK_FREQUENCY(300.0),
			.IDELAY_TYPE("VAR_LOAD")
		) delay(
			.C(i_clk), 
			.CE(1'b1),
			.CINVCTRL(1'b0),
			//
			.CNTVALUEIN(i_delay),
			.CNTVALUEOUT(o_delay),
			.LD(1'b1),
			.LDPIPEEN(1'b0),
			.REGRST(1'b0),
			.DATAIN(),
			.DATAOUT(w_hs_delayed_wire),
			.INC(1'b0),
			.IDATAIN(i_pin)
		);

	end endgenerate
	// }}}

	ISERDESE2	#(	// Master ISERDES for lower bits
		// {{{
		.SERDES_MODE("MASTER"),
		//
		.DATA_RATE("DDR"),
		.DATA_WIDTH(10),
		.INTERFACE_TYPE("NETWORKING"),
		.IOBDELAY(IOBDELAY),
		//
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.DYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		// }}}
	) lowserdes(
		// {{{
		.BITSLIP(1'b0),
		.CE1(lcl_ce), .CE2(),
		.CLK(i_hsclk), .CLKB(!i_hsclk),	// HS clocks
		.CLKDIV(i_clk), .CLKDIVP(1'b0),
		.D(w_hs_wire), .DDLY(w_hs_delayed_wire), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0),
		.O(o_wire), .OCLK(1'b0), .OCLKB(1'b0), .OFB(1'b0),
		.Q1(w_word[0]),
		.Q2(w_word[1]),
		.Q3(w_word[2]),
		.Q4(w_word[3]),
		.Q5(w_word[4]),
		.Q6(w_word[5]),
		.Q7(w_word[6]),
		.Q8(w_word[7]),
		.RST(async_reset),
		.SHIFTIN1(1'h0), .SHIFTIN2(1'h0),
		.SHIFTOUT1(master_to_slave[0]), .SHIFTOUT2(master_to_slave[1])
		// }}}
	);

	ISERDESE2	#(	// Slave ISERDES for the upper bits
		// {{{
		.SERDES_MODE("SLAVE"),
		//
		.DATA_RATE("DDR"),
		.DATA_WIDTH(10),
		.INTERFACE_TYPE("NETWORKING"),
		.IOBDELAY("NONE"),
		//
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.DYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		// }}}
	) hiserdes(
		// {{{
		.BITSLIP(1'b0),
		.CE1(lcl_ce), .CE2(),
		.CLK(i_hsclk), .CLKB(!i_hsclk),	// HS clocks
		.CLKDIV(i_clk), .CLKDIVP(1'b0),
		.D(), .DDLY(), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0),
		.O(ignored_output_hi), .OCLK(1'b0), .OCLKB(1'b0), .OFB(1'b0),
		.Q1(),
		.Q2(),
		.Q3(w_word[8]),
		.Q4(w_word[9]),
		.Q5(),
		.Q6(),
		.Q7(),
		.Q8(),
		// .Q7(w_word[8]),
		// .Q8(w_word[9]),
		.RST(async_reset),
		.SHIFTIN1(master_to_slave[0]), .SHIFTIN2(master_to_slave[1]),
		.SHIFTOUT1(), .SHIFTOUT2()
		// }}}
	);

	// (Optionally) bit reverse our incoming data (we don't need to do this)
	// {{{
	generate if (OPT_BITREVERSE)
	begin
		wire	[9:0]	w_brev;

		assign	w_brev[9] = w_word[0];
		assign	w_brev[8] = w_word[1];
		assign	w_brev[7] = w_word[2];
		assign	w_brev[6] = w_word[3];
		assign	w_brev[5] = w_word[4];
		assign	w_brev[4] = w_word[5];
		assign	w_brev[3] = w_word[6];
		assign	w_brev[2] = w_word[7];
		assign	w_brev[1] = w_word[8];
		assign	w_brev[0] = w_word[9];

		assign	w_use_this_word = w_brev;
	end else begin
		assign	w_use_this_word = w_word; // w_brev;
	end endgenerate
	// }}}

	// Optionally delay align these bits.
	// {{{
	// Turns out ... we don't need to do this here.
	localparam	[3:0]	DLY = 0;
	generate if (DLY != 0)
	begin
		reg	[(DLY-1):0]	r_word;
		always @(posedge i_clk)
			r_word <= w_use_this_word[(DLY-1):0];
		always @(posedge i_clk)
			o_word <= { r_word[(DLY-1):0],w_use_this_word[9:(DLY)]};
	end else
		always @(posedge i_clk)
			o_word <= w_use_this_word;
	endgenerate
	// }}}
endmodule
