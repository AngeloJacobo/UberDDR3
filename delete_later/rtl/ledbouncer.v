////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ledbouncer.v
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
module	ledbouncer #(
		parameter	NLEDS=8, CTRBITS=25
	) (
		input	wire		i_clk,
		output reg[(NLEDS-1):0]	o_leds
	);

	// Local declarations
	// {{{
	genvar	k;

	reg	[(NLEDS-1):0]	led_owner;
	reg			led_dir;

	reg	[(CTRBITS-1):0]	led_ctr;
	reg			led_clk;

	wire	[4:0]		br_ctr;
	// }}}

	// led_clk/led_counter -- Controls overall speed
	// {{{
	always @(posedge i_clk)
		{ led_clk, led_ctr } <= led_ctr + {{(CTRBITS-2){1'b0}},2'b11};

	// Bit reverse the bottom five bits of this counter as well.
	assign	br_ctr = { led_ctr[0], led_ctr[1], led_ctr[2], led_ctr[3],
			led_ctr[4] };
	// }}}

	// led_owner (strongest LED), led_dir(ection)
	// {{{
	initial	led_owner = { {(NLEDS-1){1'b0}}, 1'b1};
	always @(posedge i_clk)
	if (led_owner == 0)
	begin
		led_owner <= { {(NLEDS-1){1'b0}}, 1'b1 };
		led_dir   <= 1'b1; // Left, or shift up
	end else if ((led_clk)&&(led_dir)) // Go left
	begin
		if (led_owner == { 1'b1, {(NLEDS-1){1'b0}} })
			led_dir <= !led_dir;
		else
			led_owner <= { led_owner[(NLEDS-2):0], 1'b0 };
	end else if (led_clk)
	begin
		if (led_owner == { {(NLEDS-1){1'b0}}, 1'b1 })
			led_dir <= !led_dir;
		else
			led_owner <= { 1'b0, led_owner[(NLEDS-1):1] };
	end
	// }}}

	// per_LED: o_led and Brightness calculation
	// {{{
	generate for(k=0; k<(NLEDS); k=k+1)
	begin : GEN_BRIGHTNESS
		reg	[4:0]	brightness;

		always@(posedge i_clk)
		if (led_clk)
		begin
			if (led_owner[k])		brightness <= 5'h1f;
			else if (brightness > 5'h1c)	brightness <= 5'h1c;
			else if (brightness > 5'h17)	brightness <= 5'h17;
			else if (brightness > 5'h0f)	brightness <= 5'h0f;
			else if (brightness > 5'h0b)	brightness <= 5'h0b;
			else if (brightness > 5'h07)	brightness <= 5'h07;
			else if (brightness > 5'h05)	brightness <= 5'h05;
			else if (brightness > 5'h03)	brightness <= 5'h03;
			else if (brightness > 5'h01)	brightness <= 5'h01;
			else
				brightness <= 5'h00;
		end

		always @(posedge i_clk)
		if (brightness == 5'h1f)
			o_leds[k] <= 1'b1;
		else if (brightness == 5'h0)
			o_leds[k] <= 1'b0;
		else
			o_leds[k] <= (br_ctr[4:0] <= brightness[4:0]);
	end endgenerate
	// }}}
endmodule

