////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xclksw.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A fault tolerant clock switch.
//
//	Xilinx provides BUFGCTRL elements which we use here.  We want a
//	capability similar to a BUFGMUX, save that we want to be able to switch
//	clocks even when one (or both) clocks are not present.  Hence a system
//	clock is required to drive a state machine and help guarantee a switch.
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
// }}}
module	xclksw #(
		parameter [0:0] DEF_CLK = 1'b0
	) (
		// {{{
		input	wire	i_sys_clk,
		input	wire	i_clk_sel,
		input	wire	i_ck0, i_ck1,
		output	wire	o_clk
		// }}}
	);

	// Local declarations
	// {{{
	localparam [2:0]	CK_SET0   = 3'h0,
				CK_REQ1   = 3'h1,
				CK_FORCE1 = 3'h2,
				CK_SET1   = 3'h3,
				CK_REQ0   = 3'h4,
				CK_FORCE0 = 3'h5;
	reg	[2:0]	state;
	reg	[3:0]	ctr;
	reg		hard_0, hard_1, r_sel;
	// }}}

	BUFGCTRL #(
		// {{{
		.INIT_OUT(1'b0),
		.PRESELECT_I0(DEF_CLK ? "FALSE" : "TRUE"),
		.PRESELECT_I1(DEF_CLK ? "TRUE"  : "FALSE"),
		.SIM_DEVICE("7SERIES")
		// }}}
	) u_bufg (
		// {{{
		// Clock zero
		.CE0(1'b1), // could also force w/ (!r_sel || !hard_0),
		.IGNORE0(hard_0),
		.S0(!r_sel),
		.I0(i_ck0),
		//
		// Clock one
		.CE1(1'b1), // could also force w/ ( r_sel || !hard_1),
		.IGNORE1(hard_1),
		.S1(r_sel),
		.I1(i_ck1),
		//
		// Result
		.O(o_clk)
		// }}}
	);

	// State machine
	// {{{
	initial	begin
		state  = (DEF_CLK) ? CK_SET1 : CK_SET0;
		r_sel  = DEF_CLK;
		hard_0 = 1'b0;
		hard_1 = 1'b0;
		ctr    = 4'h0;
	end

	always @(posedge i_sys_clk)
	case(state)
	CK_SET0: begin
		// {{{
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		if (ctr != 0)
			ctr <= ctr - 1;
		else if (i_clk_sel)
		begin
			state  <= CK_REQ1;
			r_sel  <= 1'b1;
			ctr    <= 4'hf;
		end else begin
			state  <= CK_SET0;
			r_sel  <= 1'b0;
			ctr    <= 4'h0;
		end end
		// }}}
	CK_REQ1: begin
		// {{{
		r_sel <= 1'b1;
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		ctr <= ctr - 1;
		if (ctr == 0)
		begin
			state  <= CK_FORCE1;
		end end
		// }}}
	CK_FORCE1: begin
		// {{{
		r_sel  <= 1'b1;
		hard_0 <= 1'b1;
		hard_1 <= 1'b0;
		ctr <= ctr - 1;

		if (ctr == 0)
			state  <= CK_SET1;
		end
		// }}}
	CK_SET1: begin
		// {{{
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		if (ctr != 0)
			ctr <= ctr - 1;
		else if (!i_clk_sel)
		begin
			// Transition to clock 0
			state  <= CK_REQ0;
			r_sel  <= 1'b0;
			ctr    <= 4'hf;
		end else begin
			// Stay at clock 1
			state  <= CK_SET1;
			r_sel  <= 1'b1;
			ctr    <= 4'h0;
		end end
		// }}}
	CK_REQ0: begin
		// {{{
		r_sel <= 1'b0;
		hard_0 <= 1'b0;
		hard_1 <= 1'b0;
		ctr <= ctr - 1;
		if (ctr == 0)
		begin
			state  <= CK_FORCE0;
		end end
		// }}}
	CK_FORCE0: begin
		// {{{
		r_sel  <= 1'b0;
		hard_0 <= 1'b0;
		hard_1 <= 1'b1;

		ctr <= ctr - 1;
		if (ctr == 0)
			state  <= CK_SET0;
		end
		// }}}
	default: begin
		// {{{
		state  <= (i_clk_sel) ? CK_SET1 : CK_SET0;
		hard_0 <= 1'b1;
		hard_1 <= 1'b1;
		ctr    <= 4'hf;
		end
		// }}}
	endcase
	// }}}
endmodule
