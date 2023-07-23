////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdckgen.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generate a digitally divided pre-serdes clock.  The serdes this
//		will feed is an 8:1 serdes.  Hence, we generate 8 outputs per
//	clock period.  This allows us to generate a clock with a 90 degree
//	offset, without needing to actually offset the clock by 90 degrees.
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
module	sdckgen #(
		// {{{
		// To hit 100kHz from a 100MHz clock, we'll need to divide by
		// 4, and then by another 250.  Hence, we'll need Lg(256)-2
		// bits.  (The first three are special)
		localparam	LGMAXDIV = 8
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_cfg_clk90,
		input	wire	[LGMAXDIV-1:0]	i_cfg_ckspd,
		input	wire			i_cfg_shutdown,
		//
		output	reg			o_ckstb,
		output	reg			o_hlfck,
		output	reg	[7:0]		o_ckwide,
		output	reg	[LGMAXDIV-1:0]	o_ckspd
		// }}}
	);

	// Local declarations
	// {{{
	localparam		NCTR = LGMAXDIV+2;
	reg			nxt_stb, nxt_clk;
	reg	[NCTR-1:0]	nxt_counter, counter;
	reg			clk90;
	reg	[LGMAXDIV-1:0]	ckspd;
	wire			w_clk90;
	wire	[LGMAXDIV-1:0]	w_ckspd;
	// }}}

	// nxt_stb, nxt_clk, nxt_counter
	// {{{
	always @(*)
	begin
		nxt_stb = 1'b0;
		nxt_clk = 1'b0;
		nxt_counter = counter;

		{ nxt_stb, nxt_counter[NCTR-3:0] } = counter[NCTR-3:0] - 1;

		if (nxt_stb)
		begin
			// Advance the top two bits
			{ nxt_clk, nxt_counter[NCTR-1:NCTR-2] }
						= nxt_counter[NCTR-1:NCTR-2] +1;

			if (ckspd <= 1)
			begin
				nxt_clk = 1;
				nxt_counter[NCTR-3:0] = 0;
			end else if (ckspd == 2)
			begin
				nxt_clk = counter[NCTR-1];
				nxt_counter[NCTR-3:0] = 0;
			end else
				nxt_counter[NCTR-3:0] = ckspd-3;
		end

		if (nxt_clk)
		begin
			if (i_cfg_ckspd <= 1)
				nxt_counter = {2'b11, {(NCTR-2){1'b0}} };
			else if (i_cfg_ckspd == 2)
				nxt_counter = { 2'b01, {(NCTR-2){1'b0}} };
			else
				nxt_counter[NCTR-3:0] = i_cfg_ckspd-3;
		end
	end

	always @(posedge i_clk)
	if (i_reset)
		counter <= 0;
	else if (nxt_clk && i_cfg_shutdown)
		counter <= { 2'b11, {(NCTR-2){1'b0}} };
	else
		counter <= nxt_counter;
	// }}}

	// w_clk90, w_ckspd: Register the requested clock speed
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		clk90 <= 0;
	else
		clk90 <= w_clk90;

	always @(posedge i_clk)
	if (i_reset)
		ckspd <= 0;
	else
		ckspd <= w_ckspd;


	assign	w_clk90 = (nxt_clk) ? i_cfg_clk90 : clk90;
	assign	w_ckspd = (nxt_clk) ? i_cfg_ckspd : ckspd;
	// }}}

	// o_ckstb, o_ckwide
	// {{{
	initial	o_ckstb  = 1;
	initial	o_hlfck  = 1;
	initial	o_ckwide = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_ckstb  <= 1;
		o_hlfck  <= 1;
		o_ckwide <= 0;
	end else if ((nxt_clk && i_cfg_shutdown) || (w_ckspd == 0))
	begin
		o_ckstb  <= 1'b1;	// Or should this be !i_cfg_shutdown?
		o_hlfck  <= 1'b1;
		o_ckwide <= (i_cfg_shutdown) ? 8'h00
				: (i_cfg_clk90) ? 8'h66 : 8'h33;
	end else if (w_ckspd == 1)
	begin
		o_ckstb  <= 1'b1;
		o_hlfck  <= 1'b1;
		o_ckwide <= (w_clk90) ? 8'h3c : 8'h0f;
	end else if (w_ckspd == 2)
	begin
		{ o_ckstb, o_hlfck } <= (!nxt_counter[NCTR-1]) ? 2'b10 : 2'b01;
		if (w_clk90)
			o_ckwide <= (!nxt_counter[NCTR-1]) ? 8'h0f : 8'hf0;
		else
			o_ckwide <= (!nxt_counter[NCTR-1]) ? 8'h00 : 8'hff;
	end else begin
		o_ckstb <= nxt_clk;
		o_hlfck <= (counter == {2'b01, {(NCTR-2){1'b0}} });
		if (w_clk90)
			o_ckwide <= {(8){nxt_counter[NCTR-1]
						^ nxt_counter[NCTR-2]}};
		else
			o_ckwide <= {(8){nxt_counter[NCTR-1]}};
	end
	// }}}

	always @(posedge i_clk)
		o_ckspd <= w_ckspd;
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
	if (i_cfg_ckspd == 0)
		assume(i_cfg_clk90);

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if (ckspd == 0)
		begin
			assert(o_ckstb);
			assert(counter == 0
				||counter == {2'b11,{(NCTR-2){1'b0}} });
		end
		if (ckspd == 1)
			assert(counter == {2'b11,{(NCTR-2){1'b0}} });
		if (ckspd == 2)
			assert(counter == 0
				|| counter == {2'b01,{(NCTR-2){1'b0}} }
				|| counter == {2'b10,{(NCTR-2){1'b0}} }
				|| counter == {2'b11,{(NCTR-2){1'b0}} });
		if (ckspd >= 3)
			assert(counter[NCTR-3:0] <= (ckspd-3));
	end

	always @(*)
	if (!i_reset && o_ckstb && o_hlfck)
		assert(ckspd <= 1 || (o_ckwide == 0 && nxt_clk));

	always @(*)
	if (!i_reset)
	case(o_ckwide)
	8'h00: if (nxt_clk)
		begin
			assert(counter == {2'b11,{(NCTR-2){1'b0}} } || ckspd == 0);
		end else if(!clk90)
		begin
			assert(counter[NCTR-1] == 1'b0);
		end else if(clk90)
		begin
			assert(counter[NCTR-1:NCTR-2] == 2'b00
				||counter[NCTR-1:NCTR-2] == 2'b11);
		end
	8'h0f: assert((!clk90 && ckspd == 1 && o_ckstb && o_hlfck)
			||(clk90 && ckspd == 2 && o_ckstb));
	8'hf0: assert(clk90 && ckspd == 2 && !o_ckstb && o_hlfck);
	8'hff: if(!clk90) assert(counter[NCTR-1] == 1'b1);
		else
			assert(counter[NCTR-1:NCTR-2] == 2'b01
				|| counter[NCTR-1:NCTR-2] == 2'b10);
	8'h3c: assert( clk90 && ckspd == 1 && o_ckstb && o_hlfck);
	8'h33: assert(!clk90 && ckspd == 0 && o_ckstb && o_hlfck);
	8'h66: assert( clk90 && ckspd == 0 && o_ckstb && o_hlfck);
	default: assert(0);
	endcase
`endif	// FORMAL
// }}}
endmodule

