////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spio.v
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
module	spio #(
		// {{{
		parameter	NLEDS=8, NBTN=8, NSW=8, NFF=2
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[31:0]		i_wb_data,
		input	wire	[3:0]		i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	wire	[31:0]		o_wb_data,
		//
		input	wire	[(NSW-1):0]	i_sw,
		input	wire	[(NBTN-1):0]	i_btn,
		output	reg	[(NLEDS-1):0]	o_led,
		output	reg			o_int
		// }}}
	);

	// Local declarations
	// {{{
	reg			led_demo;
	reg	[(8-1):0]	r_led;
	wire	[(8-1):0]	w_btn;
	wire	[(NLEDS-1):0]	bounced;
	wire	[(8-1):0]	r_sw;
	reg			sw_int;
	wire			btn_int;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// LED handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_led
	// {{{
	initial	r_led = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_led <= 0;
	else if (i_wb_stb && i_wb_we && i_wb_sel[0])
	begin
		if (!i_wb_sel[1])
			r_led[NLEDS-1:0] <= i_wb_data[(NLEDS-1):0];
		else
			r_led[NLEDS-1:0] <= (r_led[NLEDS-1:0]&(~i_wb_data[(8+NLEDS-1):8]))
				|(i_wb_data[(NLEDS-1):0]&i_wb_data[(8+NLEDS-1):8]);
	end
	// }}}

	initial	led_demo = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		led_demo <= 1'b1;
	else if (i_wb_stb && i_wb_we && i_wb_sel[3])
		led_demo <= i_wb_data[24];

	ledbouncer	#(NLEDS, 25)
		knightrider(i_clk, bounced);

	always @(posedge i_clk)
	if (led_demo)
		o_led <= bounced;
	else
		o_led <= r_led[NLEDS-1:0];

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Buttons
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Let's make buttons sticky: once any button is pressed, the bit
	// will get set and then stay high until acknowledged.

	generate if (NBTN > 0)
	begin : GEN_BUTTON
		// {{{
		reg	[NBTN-1:0]	next_btn, s_btn, r_btn;
		(* ASYNC_REG *) reg	[NFF*NBTN-1:0]	btn_pipe;
		reg	r_btn_int, next_int;

		always @(posedge i_clk)
		if (i_reset)
			{ s_btn, btn_pipe } <= 0;
		else
			{ s_btn, btn_pipe } <= { btn_pipe, i_btn };

		// r_btn rises on i_btn, and falls on a write

		// next_btn
		// {{{
		always @(*)
		begin
			next_btn = r_btn;

			if (i_wb_stb && i_wb_we && i_wb_sel[2])
				next_btn = next_btn & (~i_wb_data[16 +: NBTN]);

			next_btn = next_btn | s_btn;
			next_int = |next_btn;
		end
		// }}}

		// r_btn
		// {{{
		always @(posedge i_clk)
		if (i_reset)
			r_btn <= 0;
		else
			r_btn <= next_btn;
		// }}}

		always @(posedge i_clk)
		if (i_reset)
			r_btn_int <= 1'b0;
		else
			r_btn_int <= next_int;

		assign	btn_int = r_btn_int;
		assign	w_btn[NBTN-1:0]  = r_btn;
		// }}}
	end else begin : NO_BUTTONS

		assign	btn_int = 1'b0;

	end endgenerate

	generate if (NBTN < 8)
	begin : GEN_UNUSED_BUTTONS
		assign	w_btn[7:NBTN] = 0;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Switches
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// 2FF synchronizer for our switches
	generate if (NSW > 0)
	begin : GEN_SWITCHES
		(* ASYNC_REG *) reg	[NFF*NSW-1:0]	sw_pipe;
		reg	[NSW-1:0]	rr_sw;

		initial	rr_sw    = 0;
		initial	sw_pipe = 0;
		always @(posedge i_clk)
		begin
			rr_sw <= 0;
			{ rr_sw[NSW-1:0], sw_pipe } <= { sw_pipe, i_sw };

			sw_int <= (rr_sw != sw_pipe[(NFF-1)*NSW-1 +: NSW]);
		end

		assign	r_sw = { {(8-NSW){1'b0}}, rr_sw };

	end else begin : NO_SWITCHES

		assign	r_sw = 0;

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	o_wb_data = { 7'h0, led_demo, w_btn, r_sw, r_led };

	always @(posedge i_clk)
	if (i_reset)
		o_int <= 0;
	else
		o_int <= sw_int || btn_int;

	assign	o_wb_stall = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= (i_wb_stb);
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_on  UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data, i_wb_sel[2] };
	// verilator lint_off UNUSED
	// }}}
endmodule
