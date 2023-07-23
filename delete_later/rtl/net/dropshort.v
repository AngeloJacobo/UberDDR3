////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dropshort.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Drops short packets by raising the ABORT flag if LAST arrives
//		too early.
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
module dropshort #(
		// {{{
		parameter	DW=32,		// Bits per beat
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter	MINBYTES = 64
		// }}}
	) (
		// {{{
		input	wire				S_CLK, S_ARESETN,
		//
		// Incoming packet data
		// {{{
		input	wire				S_VALID,
		output	wire				S_READY,
		input	wire	[DW-1:0]		S_DATA,
		input	wire	[$clog2(DW/8)-1:0]	S_BYTES,
		input	wire				S_ABORT,
		input	wire				S_LAST,
		// }}}
		// Outgoing packet data
		// {{{
		output	reg				M_VALID,
		input	wire				M_READY,
		output	reg	[DW-1:0]		M_DATA,
		output	reg	[$clog2(DW/8)-1:0]	M_BYTES,
		output	reg				M_ABORT,
		output	reg				M_LAST
		// }}}
		// }}}
	);

	localparam	LENBITS = $clog2(MINBYTES+1)+1,
			MSB = LENBITS-1,
			BW = $clog2(DW/8);
	reg	[MSB:0]	pktlen;
	reg		midpacket;
	reg	[$clog2(DW/8):0]	i_bytes;

	// pktlen
	// {{{
	always @(posedge S_CLK)
	if (!S_ARESETN)
		pktlen <= 0;
	else if (S_ABORT && (!S_VALID || S_READY))
		pktlen <= 0;
	else if (S_VALID && S_READY)
	begin
		if (S_LAST)
			pktlen <= 0;
		else if (!pktlen[MSB])
			pktlen <= pktlen + 1;
	end
	// }}}

	// midpacket
	// {{{
	always @(posedge S_CLK)
	if (!S_ARESETN)
		midpacket <= 0;
	else if (S_ABORT && (!S_VALID || S_READY))
		midpacket <= 0;
	else if (S_VALID && S_READY)
	begin
		if (S_LAST)
			midpacket <= 0;
		else
			midpacket <= 1;
	end
	// }}}

	// i_bytes
	// {{{
	always @(*)
	if (S_BYTES[$clog2(DW/8)-1] == 0)
		i_bytes = { 1'b1, {($clog2(DW/8)){1'b0}} };
	else
		i_bytes = { 1'b0, S_BYTES };
	// }}}

	// M_VALID
	// {{{
	initial	M_VALID = 1'b0;
	always @(posedge S_CLK)
	if (!S_ARESETN)
		M_VALID <= 0;
	else if (!M_VALID || M_READY)
		M_VALID <= S_VALID && !S_ABORT;
	// }}}

	// M_DATA, M_BYTES, M_LAST
	// {{{
	always @(posedge S_CLK)
	if (OPT_LOWPOWER && !S_ARESETN)
		{ M_DATA, M_BYTES, M_LAST } <= 0;
	else if (!M_VALID || M_READY)
	begin
		M_DATA  <= S_DATA;
		M_BYTES <= S_BYTES;
		M_LAST  <= S_LAST;
		if (OPT_LOWPOWER && (!S_VALID || S_ABORT))
			{ M_DATA, M_BYTES, M_LAST } <= 0;
	end
	// }}}

	// M_ABORT
	// {{{
	initial	M_ABORT = 1'b0;
	always @(posedge S_CLK)
	if (!S_ARESETN)
		M_ABORT <= 0;
	else if (S_ABORT && midpacket && (!M_VALID || !M_LAST))
		M_ABORT <= 1;
	else if (!M_VALID || M_READY)
	begin
		M_ABORT <= 0;
		// Verilator lint_off WIDTH
		if (S_VALID && S_READY && S_LAST && !pktlen[MSB])
			M_ABORT <= ({ pktlen,{(BW){1'b0}} } + i_bytes
								< MINBYTES);
		// Verilator lint_on  WIDTH
	end
	// }}}

	assign	S_READY = (!M_VALID || M_READY);

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
	wire	[12-1:0]		fslv_packets, fmst_packets;
	wire	[11-1:0]		fslv_word, fmst_word;
	(* anyconst *) reg	[DW:0]	fnvr_data;
	(* anyconst *) reg		f_nvr_abort;

	////////////////////////////////////////////////////////////////////////
	//
	// Interface checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxin_slave #(
		.DATA_WIDTH(DW),
		.MIN_LENGTH(0)
	) fslv (
		// {{{
		.S_AXI_ACLK(S_CLK), .S_AXI_ARESETN(S_ARESETN),
		.S_AXIN_VALID(S_VALID),
		.S_AXIN_READY(S_READY),
		.S_AXIN_DATA(S_DATA),
		.S_AXIN_BYTES(S_BYTES),
		.S_AXIN_LAST(S_LAST),
		.S_AXIN_ABORT(S_ABORT),
		.f_stream_word(fslv_word),
		.f_packets_rcvd(fslv_packets)
		// }}}
	);

	faxin_master #(
		.DATA_WIDTH(DW),
		.MIN_LENGTH(0)
	) fmst (
		// {{{
		.S_AXI_ACLK(S_CLK), .S_AXI_ARESETN(S_ARESETN),
		.S_AXIN_VALID(M_VALID),
		.S_AXIN_READY(M_READY),
		.S_AXIN_DATA(M_DATA),
		.S_AXIN_BYTES(M_BYTES),
		.S_AXIN_LAST(M_LAST),
		.S_AXIN_ABORT(M_ABORT),
		.f_stream_word(fmst_word),
		.f_packets_rcvd(fmst_packets)
		// }}}
	);

	always @(*)
	if (S_ARESETN && !M_ABORT && (!M_VALID || !M_LAST))
	begin
		assert(fslv_word == fmst_word + (M_VALID ? 1:0));
	end

	always @(*)
	if (S_ARESETN)
	begin
		if (M_ABORT || (M_VALID && M_LAST))
		begin
			assert(fslv_word == 0);
			if (!S_VALID || !S_ABORT)
				assert(!midpacket);
		end else if (M_VALID)
		begin
			assert(fslv_word > 0);
			assert(midpacket);
		end

		if (!pktlen[MSB])
		begin
			assert(M_ABORT || pktlen == fslv_word);
		end else begin
			assert(M_ABORT || pktlen <= fslv_word);
		end

		assert(midpacket == (pktlen != 0));
	end

	always @(*)
	if (S_VALID && !S_ABORT)
		assume({ S_LAST, S_DATA } != fnvr_data);

	always @(*)
	if (S_ARESETN && M_VALID && !M_ABORT)
		assert({ M_LAST, M_DATA } != fnvr_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never abort checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	always @(*)
	if (f_nvr_abort)
		assume(!midpacket || !S_ABORT);

	always @(*)
	if (S_ARESETN && f_nvr_abort)
		assume(!S_VALID || !S_LAST || (S_BYTES + pktlen >= MINBYTES));

	always @(*)
	if (S_ARESETN && f_nvr_abort)
		assert(!M_ABORT);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Lowpower checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (S_ARESETN && OPT_LOWPOWER && !M_VALID)
	begin
		assert(M_DATA  == 0);
		assert(M_BYTES == 0);
		assert(M_LAST  == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	always @(*)
	if (S_ARESETN)
	begin
		cover(M_ABORT);
		cover(M_ABORT &&  M_VALID);
		cover(M_ABORT && !M_VALID);
		cover(M_VALID && M_LAST && M_READY);
	end

	always @(posedge S_CLK)
	if (S_ARESETN)
	begin
		cover($rose(M_ABORT) && !$past(S_ABORT));
		cover($rose(M_ABORT) &&  $past(S_ABORT && !S_LAST));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" (?) assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		assume(fmst_packets < 12'h3fe);
		assume(!fslv_word[10]);
	end

	// }}}
`endif // FORMAL
// }}}
endmodule
