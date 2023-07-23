////////////////////////////////////////////////////////////////////////////////
//
// Filename:	txgetports.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Stall an incoming packet stream long enough to request a
//		MAC port lookup, then forward the packet to the port
//	returned, or broadcast it to all if no port was found (i.e. the
//	port bit mask returned).
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
module txgetports #(
		// {{{
		parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		parameter [0:0]	OPT_LOWPOWER     = 1'b0,
		parameter [0:0]	OPT_LITTLE_ENDIAN= 1'b0,
		// parameter [0:0]	OPT_DEFBROADCAST = 1'b0
		// parameter [0:0]	OPT_ONE_TO_MANY  = 1'b0
		parameter	NETH = 4,	// Total number of ports
		parameter	DW = 128,	// Bits per beat
		parameter	WBITS = $clog2(DW/8),	// Bits for bytes/beat
		parameter	MACW = 48	// Bits in a MAC address
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Incoming packet header data from all interfaces
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[DW-1:0]	S_DATA,
		input	wire [WBITS-1:0]	S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,	// == 0 on TX
		// }}}
		// Table lookup interface
		// {{{
		output	reg				TBL_REQUEST,
		input	wire				TBL_VALID,
		output	wire	[MACW-1:0]		TBL_MAC,
		input	wire	[NETH-1:0]		TBL_PORT,
		// }}}
		// Outgoing packet data, following destination lookup
		// {{{
		output	reg				M_VALID,
		input	wire				M_READY,
		output	reg	[DW-1:0]		M_DATA,
		output	reg	[WBITS-1:0]		M_BYTES,
		output	reg				M_LAST,
		output	reg				M_ABORT,
		output	reg	[NETH-1:0]		M_PORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg			known_ports;
	wire			skd_valid, skd_ready;
	wire	[DW-1:0]	skd_data;
	wire	[WBITS-1:0]	skd_bytes;
	wire			skd_last, skd_abort;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) skidbuffer
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		netskid #(
			.DW(WBITS+DW)
		) u_skidbuffer (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.S_AXIN_VALID(S_VALID), .S_AXIN_READY(S_READY),
			.S_AXIN_DATA({ S_BYTES, S_DATA }),
			.S_AXIN_LAST(S_LAST), .S_AXIN_ABORT(S_ABORT),
			//
			.M_AXIN_VALID(skd_valid), .M_AXIN_READY(skd_ready),
			.M_AXIN_DATA({ skd_bytes, skd_data }),
			.M_AXIN_LAST(skd_last), .M_AXIN_ABORT(skd_abort)
			// }}}
		);

	end else begin : NO_SKIDBUFFER
		assign	skd_valid = S_VALID;
		assign	S_READY   = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_last  = S_LAST;
		assign	skd_abort = S_ABORT;
	end endgenerate

	assign	skd_ready = (!M_VALID || M_READY) && known_ports;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Extract the port
	// {{{

	// assert(MACW < DW)

	always @(posedge i_clk)
	if (i_reset)
		known_ports <= 1'b0;
	else if (!known_ports && skd_valid && TBL_REQUEST && TBL_VALID)
		known_ports <= 1'b1;
	else if (skd_valid && skd_ready && skd_last)
		known_ports <= 1'b0;

	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		M_PORT <= 0;
	else if (TBL_REQUEST && TBL_VALID)
		M_PORT <= TBL_PORT;
	else if (OPT_LOWPOWER && M_VALID && M_READY && M_LAST)
		M_PORT <= 0;

	always @(posedge i_clk)
	if (i_reset)
		TBL_REQUEST <= 1'b0;
	else if (skd_valid)
		TBL_REQUEST <= (!known_ports && !TBL_VALID && !skd_abort);

	// WARNING: This requires at least 48*2 bits per beat, so a minimum
	// of 128 bits per beat once rounded to a power of two
	if (OPT_LITTLE_ENDIAN)
	begin
		// The first MACW bits are the source, so we grab the second
		// set of MACW bits
		assign	TBL_MAC = skd_data[2*MACW-1:MACW];
	end else begin
		// Same thing, but the "first" bits are in the MSBs
		assign	TBL_MAC = skd_data[DW-MACW-1:DW-2*MACW];
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate our output port
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 1'b0;
	else if (skd_valid && known_ports)
		M_VALID <= 1'b1;
	else if (M_READY)
		M_VALID <= 1'b0;

	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		{ M_LAST, M_BYTES, M_DATA } <= 0;
	else if (!M_VALID || M_READY)
	begin
		{ M_LAST, M_BYTES, M_DATA }<= { skd_last, skd_bytes, skd_data };
		if (OPT_LOWPOWER && (!skd_valid || skd_abort))
			{ M_LAST, M_BYTES, M_DATA } <= 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		M_ABORT <= 0;
	else if (M_VALID && !M_READY && M_LAST && !M_ABORT)
		M_ABORT <= 0;
	else if (skd_abort && (!skd_valid || skd_ready))
		M_ABORT <= 1'b1;
	else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
