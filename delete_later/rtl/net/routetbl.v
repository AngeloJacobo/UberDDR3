////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/routetbl.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is intended to be the core of the network router: the
//		routing table.  When a packet is received, from any interface,
//	it is registered in this table together with the interface it comes
//	from.  Then, when we later want to transmit a packet, the table can be
//	queried for which port the given MAC address was last seen on.
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
module routetbl #(
		// {{{
		// parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		// parameter [0:0]	OPT_LOWPOWER     = 1'b0
		// parameter [0:0]	OPT_DEFBROADCAST = 1'b0
		// parameter [0:0]	OPT_ONE_TO_MANY  = 1'b0
		parameter	NETH = 4,	// Number of incoming eth ports
		parameter  [NETH-1:0]	BROADCAST_PORT = {(NETH){1'b1}},
		parameter  [NETH-1:0]	DEFAULT_PORT = BROADCAST_PORT,
		parameter	LGTBL = 6,	// Log_2(NTBL entries)
		localparam	NTBL = (1<<LGTBL), // Number of table entries
		parameter	LGTIMEOUT = 64-MACW-1,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter	MACW = 48	// Bits in a MAC address
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Incoming packet header data from all interfaces
		// {{{
		input	wire	[NETH-1:0]		RX_VALID,
		output	wire	[NETH-1:0]		RX_READY,
		input	wire	[NETH*MACW-1:0]		RX_SRCMAC,
		// }}}
		// Outgoing packet data, needing destination lookup
		// {{{
		input	wire				TX_VALID,
		output	reg				TX_ACK,
		input	wire	[MACW-1:0]		TX_DSTMAC,
		output	reg	[NETH-1:0]		TX_PORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	integer	ik;
	genvar	gk, galt;

	wire	[NETH-1:0]	rxgrant;
	wire			rxarb_valid;
	wire			rxarb_ready;
	reg	[MACW-1:0]	rxarb_srcmac;
	reg [$clog2(NETH)-1:0]	rxarb_port;

	reg	[NTBL-1:0]		tbl_valid;
	reg	[NTBL-1:0]		prematch, oldest;
	wire	[NTBL-1:0]		tbl_write;
	reg	[LGTIMEOUT-1:0]		tbl_age		[NTBL-1:0];
	reg	[$clog2(NETH)-1:0]	tbl_port	[NTBL-1:0];
	reg	[MACW-1:0]		tbl_mac		[NTBL-1:0];
	wire				tbl_full;

	wire	[NTBL-1:0]	lkup_tblmatch;
	reg	[NETH-1:0]	lkup_port;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate among inputs
	// {{{
	pktarbiter #(
		.W(NETH)
	) u_arbiter (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(RX_VALID), .i_stall(!rxarb_ready),
		.o_grant(rxgrant)
	);

	assign	rxarb_valid = |(RX_VALID & rxgrant);
	assign	RX_READY    = rxarb_ready ? rxgrant : 0;

	assign	rxarb_ready = 1;

	always @(*)
	begin
		rxarb_port = 0;
		for(ik=0; ik<NETH; ik=ik+1)
		if (rxgrant[ik])
			rxarb_port = rxarb_port | (1<<ik);
	end

	always @(*)
	begin
		rxarb_srcmac = 0;
		for(ik=0; ik<NETH; ik=ik+1)
		if (rxgrant[ik])
			rxarb_srcmac = rxarb_srcmac
					| RX_SRCMAC[rxgrant * MACW +: MACW];
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Log incoming packets into our table
	// {{{

	assign	tbl_full = (&tbl_valid);
	generate for(gk=0; gk<NTBL; gk=gk+1)
	begin
		wire			first_invalid;
		wire	[NTBL-1:0]	is_older;

		always @(*)
			prematch[gk] = tbl_valid[gk] && rxarb_valid
				&& tbl_mac[gk] == rxarb_srcmac;

		if (gk == 0)
		begin
			assign	first_invalid = !tbl_valid[gk];
		end else begin
			assign	first_invalid = !tbl_valid[gk]
					&& (&tbl_valid[gk]-1);
		end

		// Find what's older
		for(galt=0; galt<NTBL; galt=galt + 1)
		begin
			if (galt == gk)
			begin
				assign	is_older[galt] = 1'b0;
			end else begin
				reg	r_is_older;

				always @(posedge i_clk)
				if (i_reset)
					r_is_older <= 1'b0;
				else if (tbl_write[gk])
					r_is_older <= tbl_valid[galt];
				else if (tbl_write[galt])
					r_is_older <= 1'b0;

				assign	is_older[galt] = r_is_older;
			end
		end

		// OLDEST: True if this element is the oldest in the table
		always @(*)
		if (!tbl_full)
		begin
			oldest[gk] = first_invalid;
		end else begin
			oldest[gk] = (is_older == 0);
		end

		assign	tbl_write[gk] = rxarb_valid && (prematch[gk]
					|| (prematch == 0 && oldest[gk]));

		always @(posedge i_clk)
		if (i_reset)
		begin
			tbl_valid[gk] <= 1'b0;
			tbl_age[gk]   <= 0;
		end else if (tbl_write[gk])
		begin
			tbl_valid[gk] <= 1'b1;
			tbl_age[gk]   <= {(LGTIMEOUT){1'b1}};
		end else if (tbl_valid[gk])
		begin
			tbl_valid[gk] <= (tbl_age[gk] > 1);
			tbl_age[gk]   <= tbl_age[gk] - 1;
		end

		always @(posedge i_clk)
		if (tbl_write[gk])
		begin
			tbl_mac[gk]  <= rxarb_srcmac;
			tbl_port[gk] <= rxarb_port;
		end

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Look up which request a transmit port should get sent to
	// {{{

	generate for(gk=0; gk<NTBL; gk=gk+1)
	begin

		assign	lkup_tblmatch[gk] = tbl_valid[gk]
				&& tbl_mac[gk] == TX_DSTMAC;
	end endgenerate

	always @(*)
	begin
		lkup_port = 0;
		for(ik=0; ik<NTBL; ik=ik+1)
		if (lkup_tblmatch[ik])
			lkup_port = lkup_port | (1<<tbl_port[ik]);
	end

	always @(posedge i_clk)
	if (i_reset || (OPT_LOWPOWER && !TX_VALID))
		TX_PORT <= 0;
	else if (TX_VALID && !TX_ACK)
	begin
		if (&TX_DSTMAC)
			TX_PORT <= BROADCAST_PORT;
		else if (lkup_tblmatch == 0)
			TX_PORT <= DEFAULT_PORT;	// Could be broadcast
		else
			TX_PORT <= lkup_port;
	end

	always @(posedge i_clk)
	if (i_reset)
		TX_ACK <= 1'b0;
	else
		TX_ACK <= TX_VALID && (!TX_ACK);
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
