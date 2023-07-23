////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rxgetsrcmac.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Given an incoming packet, copy the source MAC address and
//		forward it to the routing table.
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
module rxgetsrcmac #(
		// {{{
		parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		parameter [0:0]	OPT_LOWPOWER     = 1'b0,
		parameter [0:0]	OPT_LITTLE_ENDIAN= 1'b0,
		parameter	DW=64,		// Bits per incoming beat
		parameter	WBITS = $clog2(DW/8),	// Bits to desc # bytes
		parameter	MACW = 48	// Bits in a MAC address
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Incoming packet data from one interface
		// {{{
		input	wire				S_VALID,
		output	wire				S_READY,
		input	wire	[DW-1:0]		S_DATA,
		input	wire	[WBITS-1:0]	S_BYTES,
		input	wire				S_ABORT,
		input	wire				S_LAST,
		// }}}
		// Outgoing packet data
		// {{{
		output	reg				M_VALID,
		input	wire				M_READY,
		output	reg	[DW-1:0]		M_DATA,
		output	reg	[WBITS-1:0]	M_BYTES,
		output	reg				M_ABORT,
		output	reg				M_LAST,
		// }}}
		// Outgoing packet data, needing destination lookup
		// {{{
		output	reg				TBL_VALID,
		input	wire				TBL_READY,
		output	reg	[MACW-1:0]		TBL_SRCMAC
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	MAXPOSN = (MACW+(DW-1))/DW;
	localparam	LGPOSN = $clog2(MAXPOSN);

	wire			skd_valid, skd_ready,
				skd_abort, skd_last;
	wire	[DW-1:0]	skd_data;
	wire	[WBITS-1:0]	skd_bytes;

	reg	[LGPOSN:0]	pkt_posn;
	reg			m_active;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Skidbuffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		netskid #(
			.DW(DW + WBITS)
		) u_skidbuffer (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.S_AXIN_VALID( S_VALID),
			.S_AXIN_READY( S_READY),
			.S_AXIN_DATA({ S_BYTES, S_DATA }),
			.S_AXIN_LAST(  S_LAST),
			.S_AXIN_ABORT( S_ABORT),
			//
			.M_AXIN_VALID( skd_valid),
			.M_AXIN_READY( skd_ready),
			.M_AXIN_DATA({ skd_bytes, skd_data }),
			.M_AXIN_LAST(  skd_last),
			.M_AXIN_ABORT( skd_abort)
			// }}}
		);

	end else begin : NO_SKIDBUFFER

		assign	skd_valid = S_VALID;
		assign	S_READY = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_abort = S_ABORT;
		assign	skd_last  = S_LAST;

	end endgenerate

	assign	skd_ready= ((!TBL_VALID || TBL_READY) && (!M_VALID || M_READY));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Extract MACs
	// {{{

	always @(posedge i_clk)
	if (i_reset)
		pkt_posn  <= 0;
	else if (skd_abort && (!skd_valid || skd_ready))
		pkt_posn  <= 0;
	else if (skd_valid && skd_ready)
	begin
		if (!pkt_posn[LGPOSN])
			pkt_posn <= pkt_posn + 1;
		if (skd_last)
			pkt_posn <= 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		TBL_VALID <= 0;
	else if (skd_valid && skd_ready && skd_last) // pkt_posn == MAXPOSN-1)
		// Require a full, non-aborted, packet before forwarding the
		// MAC address to the table.  This will guarantee that the
		// packet CRC is good, and therefore that the MAC address is
		// a valid one.
		TBL_VALID <= !skd_abort;
	else if (TBL_READY)
		TBL_VALID <= 0;

	generate if (MACW <= DW)
	begin : GEN_SMALL_MAC
		// {{{
		always @(posedge i_clk)
		if (OPT_LOWPOWER && i_reset)
			TBL_SRCMAC <= 0;
		else if (!TBL_VALID || TBL_READY)
		begin
			if (skd_valid && skd_ready && pkt_posn == 0)
			begin
				if (OPT_LITTLE_ENDIAN)
					TBL_SRCMAC <= skd_data[MACW-1:0];
				else
					TBL_SRCMAC <= skd_data[DW-1:DW-MACW];
			end
		end
		// }}}
	end else begin : GEN_WIDE_MAC
		// {{{
		reg	[DW*MAXPOSN-1:0]	last_data;

		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || skd_abort))
			last_data <= 0;
		else if (skd_valid && skd_ready)
		begin
			if (MAXPOSN <= 1)
				last_data <= skd_data;
			else if (OPT_LITTLE_ENDIAN)
				last_data <= { skd_data, last_data[DW*MAXPOSN-1:DW] };
			else
				last_data <= { last_data[DW*(MAXPOSN-1)-1:0], skd_data };
		end

		always @(posedge i_clk)
		if (OPT_LOWPOWER && i_reset)
			TBL_SRCMAC <= 0;
		else if (!TBL_VALID || TBL_READY)
		begin
			if (skd_valid && skd_ready && pkt_posn == MAXPOSN-1)
			begin
				if (OPT_LITTLE_ENDIAN)
					TBL_SRCMAC <= { skd_data[MACW-DW-1:0], last_data };
				else
					TBL_SRCMAC <= { last_data, skd_data[DW-1:DW-MACW] };
			end
		end
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Copy packets forward
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	M_VALID = 0;
	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 0;
	else if (!M_VALID || M_READY)
		M_VALID <= skd_valid && !skd_abort;

	initial	{ M_BYTES, M_DATA } = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
	begin
		M_DATA <= 0;
		M_BYTES <= 0;
	end else if (!M_VALID || M_READY)
	begin
		M_DATA  <= skd_data;
		M_BYTES <= skd_bytes;

		if (OPT_LOWPOWER && (!skd_valid || !skd_ready || skd_abort))
			{ M_DATA, M_BYTES } <= 0;
	end

	initial	m_active = 0;
	always @(posedge i_clk)
	if (i_reset)
		m_active <= 0;
	else if (skd_abort && (!skd_valid || skd_ready))
		m_active <= 0;
	else if (skd_valid && skd_ready)
		m_active <= !skd_last;

	initial	M_LAST = 0;
	always @(posedge i_clk)
	if (i_reset)
		M_LAST <= 0;
	else if (!M_VALID || M_READY)
	begin
		M_LAST <= skd_last;
		if (OPT_LOWPOWER && (!skd_valid || !skd_ready))
			M_LAST <= 1'b0;
	end

	initial	M_ABORT = 0;
	always @(posedge i_clk)
	if (i_reset)
		M_ABORT <= 0;
	else if (skd_abort && m_active)
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
