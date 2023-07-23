////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/p64bscrambler.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
//
// ETHERNET is an LSB first protocol.  Bit 0 of byte 0 is always "first".
// This scrambler preserves that ordering, but does expect bit 0 of byte 0
// to be found in position [0].
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
module	p64bscrambler #(
		// {{{
		localparam	POLYNOMIAL_BITS=58,
		// Poly = (1<<38) ^ (1<<57)
		localparam [POLYNOMIAL_BITS-1:0]	POLYNOMIAL
				= 58'h200_0040_0000_0000,
		localparam	DATA_WIDTH=66,
		parameter	[0:0]	OPT_RX = 0
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset_n,
		//
		input	wire				i_valid,
		output	wire				o_ready,
		input	wire	[DATA_WIDTH-1:0]	i_data,
		//
		output	reg				o_valid,
		input	wire				i_ready,
		output	reg	[DATA_WIDTH-1:0]	o_data
		// }}}
	);

	// Local declarations
	// {{{
	localparam	PB = POLYNOMIAL_BITS;
	localparam	DW = DATA_WIDTH;

	reg	[PB-1:0]	r_fill;
	wire	[PB-1:0]	next_fill;
	wire	[DW-1:0]	scrambled;
	// }}}

	assign	{ next_fill, scrambled } = SCRAMBLE(r_fill, i_data);

	// r_fill
	// {{{
	always @(posedge i_clk)
	if (!i_reset_n)
		r_fill <= 0;
	else if (i_ready)
		// Self synchronizing
		r_fill <= next_fill;
	// }}}

	// o_valid
	// {{{
	always @(posedge i_clk)
	if (!i_reset_n)
		o_valid <= 0;
	else if (i_valid)
		o_valid <= 1'b1;
	else if (o_ready)
		o_valid <= 1'b0;
	// }}}

	// o_data
	// {{{
	always @(posedge i_clk)
	if (!i_reset_n)
		o_data <= 0;
	else if (i_ready)
		o_data <= scrambled;
	// }}}

	assign	o_ready = !o_valid || i_ready;

	function automatic [PB+DW-1:0] SCRAMBLE(
		// {{{
			input [PB-1:0]	s_fill,
			input [DW-1:0]	s_data);

		integer ik;
		reg	[DW-1:0]	data_out;
		reg	[PB-1:0]	state;
	begin
		data_out = 0;
		data_out[1:0] = s_data[1:0];
		state = s_fill;
		for(ik=2; ik<DW; ik=ik+1)
		begin
			data_out[ik] = s_data[ik] ^ (^(POLYNOMIAL & state));
			if (OPT_RX)
			begin
				state = { state[PB-2:0], s_data[ik] };
			end else begin
				state = { state[PB-2:0], data_out[ik] };
			end
		end

		SCRAMBLE = { state, data_out };
	end endfunction
// }}}
endmodule
