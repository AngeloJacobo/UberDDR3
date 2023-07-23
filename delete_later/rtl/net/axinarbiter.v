////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axinarbiter.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Arbitrates from among NIN packet sources to select and forward
//		one of those sources forward.
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
module axinarbiter #(
		// {{{
		parameter	NIN = 4,	// Number of incoming eth ports
		parameter	DW = 64,	// Bits per clock cycle
		parameter	WBITS = $clog2(DW/8),
		parameter [0:0]	OPT_SKIDBUFFER = 1,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		// Incoming packets from all interfaces
		// {{{
		input	wire	[NIN-1:0]		S_VALID,
		output	wire	[NIN-1:0]		S_READY,
		input	wire	[NIN*DW-1:0]		S_DATA,
		input	wire	[NIN*WBITS-1:0]	S_BYTES,
		input	wire	[NIN-1:0]		S_LAST,
		input	wire	[NIN-1:0]		S_ABORT,
		// }}}
		// Outgoing packet
		// {{{
		output	reg			M_VALID,
		input	wire			M_READY,
		output	reg	[DW-1:0]	M_DATA,
		output	reg [WBITS-1:0]	M_BYTES,
		output	reg			M_LAST,
		output	reg			M_ABORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	genvar			gk;
	integer			ik;

	wire	[NIN-1:0]	grant;
	wire	[NIN-1:0]	midpkt;
	reg	[DW-1:0]	merged_data;
	reg [WBITS-1:0]	merged_bytes;
	reg			merged_last;
	wire			stalled;

	wire	[NIN-1:0]	skd_valid, skd_ready;
	wire	[NIN*DW-1:0]	skd_data;
	wire	[NIN*WBITS-1:0]	skd_bytes;
	wire	[NIN-1:0]	skd_last, skd_abort;
	// }}}

	pktarbiter #(
		.W(NIN)
	) u_arbiter (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(S_VALID), .i_stall(stalled),
		.o_grant(grant)
		// }}}
	);

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		for(gk=0; gk<NIN; gk=gk+1)
		begin : NETSKID

			netskid #(
				.DW(DW+WBITS)
			) u_netskid (
				.i_clk(i_clk), .i_reset(i_reset),
				//
				.S_AXIN_VALID(S_VALID[gk]),
				.S_AXIN_READY(S_READY[gk]),
				.S_AXIN_DATA({ S_BYTES[gk*WBITS +: WBITS],
						S_DATA[gk*DW +: DW] }),
				.S_AXIN_LAST(S_LAST[gk]),
				.S_AXIN_ABORT(S_ABORT[gk]),
				//
				.M_AXIN_VALID(skd_valid[gk]),
				.M_AXIN_READY(skd_ready[gk]),
				.M_AXIN_DATA({ skd_bytes[gk*WBITS +: WBITS],
						skd_data[gk*DW +: DW] }),
				.M_AXIN_LAST(skd_last[gk]),
				.M_AXIN_ABORT(skd_abort[gk])
			);
		end
	end else begin : NO_SKID

		assign	skd_valid = S_VALID;
		assign	S_READY   = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_last  = S_LAST;
		assign	skd_abort = S_ABORT;

	end endgenerate

	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : GEN_MIDPKT
		reg	r_midpkt;

		always @(posedge i_clk)
		if (i_reset)
			r_midpkt <= 0;
		else if (skd_abort[gk] && (!skd_valid[gk] || skd_ready[gk]))
			r_midpkt <= 1'b0;
		else if (skd_valid[gk] && skd_ready[gk])
			r_midpkt <= !skd_last[gk];

		assign	midpkt[gk] = r_midpkt;
	end endgenerate

	assign	stalled = |midpkt || |(skd_valid & skd_ready);
	assign	skd_ready = (!M_VALID || M_READY) ? grant : 0;

	// M_VALID
	// {{{
	initial	M_VALID = 0;
	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 0;
	else if (!M_VALID || M_READY)
		M_VALID <= |(skd_valid & skd_ready & (~skd_abort | midpkt));
	// }}}

	// merged_data, merged_bytes, merged_last
	// {{{
	always @(*)
	begin
		merged_data  = 0;
		merged_bytes = 0;
		merged_last  = 0;

		for(ik=0; ik<NIN; ik=ik+1)
		if (grant[ik])
		begin
			merged_data  = merged_data  | skd_data[ik * DW +: DW];
			merged_bytes = merged_bytes
				| skd_bytes[ik * WBITS +: WBITS];
			merged_last  = merged_last  | skd_last[ik];
		end
	end
	// }}}

	// M_DATA, M_BYTES, M_LAST
	// {{{
	always @(posedge i_clk)
	if (i_reset && OPT_LOWPOWER)
	begin
		M_DATA  <= 0;
		M_BYTES <= 0;
		M_LAST  <= 0;
	end else if (!M_VALID || M_READY)
	begin
		M_DATA  <= merged_data;
		M_BYTES <= merged_bytes;
		M_LAST  <= merged_last;

		if (OPT_LOWPOWER && (skd_valid & skd_ready & ~skd_abort) == 0)
		begin
			M_DATA  <= 0;
			M_BYTES <= 0;
			M_LAST  <= 0;
		end
	end
	// }}}

	// M_ABORT
	// {{{
	initial	M_ABORT = 0;
	always @(posedge i_clk)
	if (i_reset)
		M_ABORT <= 0;
	else if (M_VALID && !M_READY && M_LAST && !M_ABORT)
		M_ABORT <= 0;
	else if (|(skd_abort & grant & midpkt))
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
	wire	[10:0]	fmst_word;
	wire	[11:0]	fmst_packets;
	(* anyconst *)	reg	[DW:0]	fnvr_data;

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : F_SLAVE
		wire	[10:0]	fslv_word;
		wire	[11:0]	fslv_packets;

		faxin_slave #(
			.DATA_WIDTH(DW), .WBITS(WBITS)
		) fslv (
			// {{{
			.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
			//
			.S_AXIN_VALID(S_VALID[gk]),
			.S_AXIN_READY(S_READY[gk]),
			.S_AXIN_DATA(S_DATA[gk*DW +: DW]),
			.S_AXIN_BYTES(S_BYTES[gk*WBITS +: WBITS]),
			.S_AXIN_LAST(S_LAST[gk]),
			.S_AXIN_ABORT(S_ABORT[gk]),
			//
			.f_stream_word(fslv_word),
			.f_packets_rcvd(fslv_packets)
			// }}}
		);

		always @(*)
		if (!i_reset && !grant[gk])
			assert(fslv_word == 0);

		always @(*)
		if (!i_reset && fslv_word > 0)
		begin
			assert(grant[gk]);
			assert(midpkt[gk]);
		end

		always @(*)
		if (!i_reset && grant[gk])
		begin
			if (M_VALID && !M_ABORT)
				assert(M_LAST || fslv_word != 0);

			if (M_ABORT || (M_VALID && M_LAST))
			begin
				assert(fslv_word == 0);
				assert(!midpkt[gk] || (S_VALID && S_ABORT));
			end else begin
				assert(midpkt[gk] == (fslv_word != 0));
				assert(fslv_word
					== (fmst_word + (M_VALID ? 1:0)));
			end
		end

		always @(*)
		if (!i_reset && S_VALID[gk])
			assume({ S_LAST[gk],S_DATA[DW*gk +: DW] } != fnvr_data);
	end endgenerate

	faxin_master #(
		.DATA_WIDTH(DW), .WBITS(WBITS)
	) fslv (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(M_VALID),
		.S_AXIN_READY(M_READY),
		.S_AXIN_DATA(M_DATA),
		.S_AXIN_BYTES(M_BYTES),
		.S_AXIN_LAST(M_LAST),
		.S_AXIN_ABORT(M_ABORT),
		//
		.f_stream_word(fmst_word),
		.f_packets_rcvd(fmst_packets)
		// }}}
	);

	always @(*)
	if (!i_reset && grant == 0)
		assert(!M_VALID && fmst_word == 0);

	always @(posedge i_clk)
	if (!i_reset && $rose(M_VALID) && fmst_word == 0)
		assert(!M_ABORT);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	(* anyconst *)	reg	fnvr_abort;

	always @(*)
	if (!i_reset && fnvr_abort)
		assume(0 == ((S_VALID | midpkt) & S_ABORT));

	always @(*)
	if (!i_reset && fnvr_abort)
		assert(!M_ABORT);

	always @(*)
	if (!i_reset && M_VALID && !M_ABORT)
		assert({ M_LAST,M_DATA } != fnvr_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Low power checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!i_reset && OPT_LOWPOWER && !M_VALID)
	begin
		assert(M_DATA  == 0);
		assert(M_BYTES == 0);
		assert(M_LAST  == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		cover(!i_reset && M_VALID && M_READY && M_LAST && !M_ABORT);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
`endif
// }}}
endmodule
