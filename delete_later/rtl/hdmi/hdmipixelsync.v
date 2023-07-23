////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmipixelsync.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generate automatic synchronization information to sync to one of
//		the three HDMI color channels.  The output is a bit-synchronized
//	channel word.
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
module	hdmipixelsync (
		// {{{
		input	wire		i_clk, i_reset,
		input	wire	[9:0]	i_px,
		output	wire	[4:0]	o_sync,
		output	reg	[9:0]	o_pix
		// }}}
	);

	// Register/wire declarations
	// {{{
	integer	ik;
	genvar	gk;
	reg [2*10-2:0]	pre_match_win;
	wire	[18:0]	pre_pix;
	//
	reg		valid_match;
	reg	[3:0]	match_loc, w_match_loc;
	//
	wire	[3:0]	chosen_match_loc;
	reg		sync_valid;
	reg	[15:0]	lost_sync_counter;
	reg	[9:0]	sync;
	// }}}

	always @(posedge i_clk)
		pre_match_win <= { pre_match_win[8:0], i_px };

	// Test all possible synchronizations for a match
	// {{{
	generate for(gk=0; gk<10; gk=gk+1)
	begin
		reg		control_word;
		reg	[5:0]	control_matches;

		always @(posedge i_clk)
		begin
			control_word <= 1'b0;
			if((pre_match_win[gk+9:gk]== 10'h0ab) // 354
				    ||(pre_match_win[gk+9:gk]==10'h354) //0ab
				    ||(pre_match_win[gk+9:gk]==10'h0aa) //154
				    ||(pre_match_win[gk+9:gk]==10'h355))//2ab
				control_word <= 1'b1;

			if (control_word)
			begin
				if (!control_matches[5])
					control_matches <= control_matches + 1;
			end else
				control_matches <= 0;

			sync[gk] <= (control_matches >= 12);
		end
	end endgenerate
	// }}}

	// w_match_loc
	// {{{
	always @(*)
	begin
		w_match_loc = 0;
		for(ik=0; ik<10; ik=ik+1)
		if (sync[ik])
			w_match_loc = w_match_loc | ik[3:0];
	end
	// }}}

	// valid_match, match_log
	// {{{
	always @(posedge i_clk)
	begin
		// valid_match, match_loc
		valid_match <= (!i_reset);
		match_loc <= w_match_loc;
		case(sync)
		10'h001: begin end // match_loc <= 4'h0;
		10'h002: begin end // match_loc <= 4'h1;
		10'h004: begin end // match_loc <= 4'h2;
		10'h008: begin end // match_loc <= 4'h3;
		10'h010: begin end // match_loc <= 4'h4;
		10'h020: begin end // match_loc <= 4'h5;
		10'h040: begin end // match_loc <= 4'h6;
		10'h080: begin end // match_loc <= 4'h7;
		10'h100: begin end // match_loc <= 4'h8;
		10'h200: begin end // match_loc <= 4'h9;
		default: valid_match <= 1'b0;
		endcase
	end
	// }}}

	// Declare no synch when ... we don't see anything for a long time
	// {{{
	initial	lost_sync_counter = 16'hffff; // Start with a lost synch
	always @(posedge i_clk)
	if (i_reset)
		lost_sync_counter <= 16'hffff;
	else if (valid_match && match_loc == chosen_match_loc)
		lost_sync_counter <= 0;
	else if (!(&lost_sync_counter))
		lost_sync_counter <= lost_sync_counter + 1'b1;

	initial	sync_valid = 1'b0;
	always @(posedge i_clk)
	if (&lost_sync_counter)
		sync_valid <= 1'b0;
	else if (valid_match)
		sync_valid <= (match_loc == chosen_match_loc);
	// }}}

	// Check for and remove any glitches
	// {{{
	synccount	#(.NBITS(4), .OPT_BYPASS_TEST(1'b0))
	pixloc(i_clk, i_reset, valid_match, match_loc, chosen_match_loc);
	// }}}

	assign	o_sync = { (sync_valid), chosen_match_loc };
	assign	pre_pix = pre_match_win >> chosen_match_loc;

	always @(posedge i_clk)
		o_pix <= pre_pix[9:0];

	// Make Verilator happy
	// {{{
	// verilog lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, pre_pix[18:10] };
	// verilog lint_on  UNUSED
	// }}}
endmodule
