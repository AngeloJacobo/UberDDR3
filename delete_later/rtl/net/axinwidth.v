////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/axinwidth.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Convert an abortable AXI network stream from one width to
//		another.
//
// Challenges are twofold:
//	1. AXI-Network signaling
//	2. Shift register (not much of a challenge)
//	3. Formal properties
//
// Question: How would you verify this?
// Answer:
//	1. Pick two bytes (like a FIFO). Let them be arbitrary and adjacent.
//		Also, pick their location in the input stream.
//	2. Assume those two bytes arrive on an incoming packet, one after the
//		other.
//	3. *Prove* those same two bytes leave in an outgoing packet, one after
//		the other.
//		Also, *prove* those same two bytes occupy the same locations
//		(byte-wise) in the output stream.
//	4. Assume !S_AXIN_ABORT, *PROVE* !M_AXIN_ABORT
//
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
module	axinwidth #(
		// {{{
		parameter	IW = 64,    // Incoming data path width
		parameter	OW = 32	    // Outgoing data path width
		// Reminder: come back and add these parameters in later
		// parameter [0:0] OPT_LITTLE_ENDIAN
		// parameter [0:0] OPT_LOWPOWER
		// }}}
	) (
		// {{{
		input	wire			ACLK, ARESETN,
		// S_AXIN_*
		input	wire			S_AXIN_VALID,
		output	wire			S_AXIN_READY,
		input	wire	[IW-1:0]	S_AXIN_DATA,
		input	wire [$clog2(IW/8):0]	S_AXIN_BYTES,
		input	wire			S_AXIN_LAST,
		input	wire			S_AXIN_ABORT,
		// M_AXIN_*
		output	reg			M_AXIN_VALID,
		input	wire			M_AXIN_READY,
		output	wire	[OW-1:0]	M_AXIN_DATA,
		output	reg [$clog2(OW/8):0]	M_AXIN_BYTES,
		output	reg			M_AXIN_LAST,
		output  reg			M_AXIN_ABORT
		// }}}
	);

`ifdef FORMAL
	localparam MIN_LENGTH =   64*8;	//   64 Bytes
	localparam MAX_LENGTH = 2048*8;	// 2048 Bytes
	localparam MIN_LENGTH_I = MIN_LENGTH/IW;
	localparam MAX_LENGTH_I = MAX_LENGTH/IW;
	localparam MIN_LENGTH_O = MIN_LENGTH/OW;
	localparam MAX_LENGTH_O = MAX_LENGTH/OW;
	localparam LGMX = (MAX_LENGTH > 0) ? $clog2(MAX_LENGTH+1):1;

	// Pick two arbitrary values
	(* anyconst *) reg	[7:0]	fc_first, fc_next;
	wire	[7:0]	fm_first, fm_next;
	// Pick an arbitrary position
	(* anyconst *) reg	[LGMX-1:0]	fc_posn;
	wire	[LGMX-1:0]	fc_nxtposn;

	(* keep *) wire [LGMX-$clog2(OW/8)-1:0] fm_first_word_cnt, fm_next_word_cnt;
	(* keep *) wire [$clog2(OW/8)-1:0] fm_first_byte, fm_next_byte;
	(* keep *) wire [LGMX-$clog2(IW/8)-1:0] fs_first_word_cnt, fs_next_word_cnt;
	(* keep *) wire [$clog2(IW/8)-1:0] fs_first_byte, fs_next_byte;

	wire	[LGMX-1:0] f_s_stream_word, f_m_stream_word;
	wire	[12-1:0]   f_s_packets_rcvd, f_m_packets_rcvd;
`endif

	generate if (IW == OW)
	begin : EQUAL
		// {{{
		assign	S_AXIN_READY = M_AXIN_READY;
		assign	M_AXIN_DATA  = S_AXIN_DATA;

		always @(posedge ACLK)
		if (!ARESETN)
		begin
			M_AXIN_VALID <= 0;
			M_AXIN_LAST  <= 0;
			M_AXIN_BYTES <= 0;
			M_AXIN_ABORT <= 0;
		end else begin
			M_AXIN_VALID <= S_AXIN_VALID;
			M_AXIN_LAST  <= S_AXIN_LAST;
			M_AXIN_BYTES <= S_AXIN_BYTES;
			M_AXIN_ABORT <= S_AXIN_ABORT;
		end
		// }}}
	end else if (IW < OW)
	begin : IW_SMALLER
		// {{{
		// Try IW = 8, OW = 32		(You need this for verification)
		// Also try IW = 32, OW = 64	(I need this for project)
		// Also try IW = 64, OW = 512	(I need this for project)
		// localparam	SHIFT = IW;
		localparam	WIDE_COUNT = (OW/IW);
		localparam	LGWIDE_COUNT = $clog2(WIDE_COUNT);

		integer		i;
		reg [OW-1:0]	data_concat;
		reg [LGWIDE_COUNT-1:0] wide_counter;
		reg		mid_packet;

		initial	mid_packet = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			mid_packet <= 0;
		else if (S_AXIN_ABORT && !S_AXIN_VALID)
			mid_packet <= 0;
		else if (S_AXIN_VALID && S_AXIN_READY)
			mid_packet <= !S_AXIN_LAST && !S_AXIN_ABORT;

		// M_AXIN_ABORT
		initial M_AXIN_ABORT = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			M_AXIN_ABORT <= 0;
		else if (M_AXIN_VALID && !M_AXIN_READY
				&& (M_AXIN_ABORT || (S_AXIN_ABORT && mid_packet)))
			M_AXIN_ABORT <= 1;
		else if (S_AXIN_ABORT && mid_packet)
			M_AXIN_ABORT <= 1;
		else if (!M_AXIN_VALID || M_AXIN_READY)
			M_AXIN_ABORT <= 0;

		// M_AXIN_DATA, S_AXIN_READY
		assign S_AXIN_READY = !M_AXIN_VALID || M_AXIN_READY || S_AXIN_ABORT;
		assign M_AXIN_DATA  = data_concat;

		// M_AXIN_VALID
		initial M_AXIN_VALID = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			M_AXIN_VALID <= 0;
		else if (!S_AXIN_ABORT && (S_AXIN_VALID && S_AXIN_READY)
				// Verilator lint_off WIDTH
				&&((wide_counter == WIDE_COUNT-1)||S_AXIN_LAST))
				// Verilator lint_on  WIDTH
			M_AXIN_VALID <= 1;
		else if (M_AXIN_READY)
			M_AXIN_VALID <= 0;

		// M_AXIN_BYTES, M_AXIN_LAST, wide_counter, data_concat
		initial M_AXIN_BYTES = 0;
		initial M_AXIN_LAST  = 0;
		initial wide_counter = 0;
		initial data_concat  = 0;
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			M_AXIN_BYTES <= 0;
			M_AXIN_LAST  <= 0;
			wide_counter <= 0;
			data_concat  <= 0;
		end else begin
			if (M_AXIN_VALID && M_AXIN_READY)
				data_concat <= 0;

			if (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
			begin
				M_AXIN_LAST <= S_AXIN_LAST;

				// *_VALID and *_READY can be set at the same time
				// Verilator lint_off WIDTH
				if (M_AXIN_VALID && M_AXIN_READY)
					M_AXIN_BYTES <= S_AXIN_BYTES;
				else
					M_AXIN_BYTES <= M_AXIN_BYTES + S_AXIN_BYTES;
				// Verilator lint_on  WIDTH

				for(i=0; i < OW/IW; i=i+1)
				begin
					// Verilator lint_off WIDTH
					if (wide_counter == i)
						// Verilator lint_on  WIDTH
						data_concat[i*IW +: IW]
							<= S_AXIN_DATA;
				end

				if (!S_AXIN_LAST)
					wide_counter <= wide_counter + 1;
				else
					wide_counter <= 0;
			end else if ((M_AXIN_VALID && M_AXIN_READY)
				|| (!M_AXIN_VALID
					&& (M_AXIN_ABORT || S_AXIN_ABORT)))
			begin
				M_AXIN_BYTES <= 0;
				M_AXIN_LAST  <= 0;
				wide_counter <= 0;
				data_concat  <= 0;
			end
		end
		////////////////////////////////////////////////////////////////
		//
		// Formal properties
		// {{{
		////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		always @(*)
		if (ARESETN)
		begin
			if (M_AXIN_VALID && M_AXIN_LAST)
				assert(f_s_stream_word == 0);
			assert(f_m_stream_word < (MAX_LENGTH / (OW/IW)));
			assert(mid_packet == (f_s_stream_word != 0));
			if (!M_AXIN_LAST && !M_AXIN_ABORT)
			begin
				assert(f_m_stream_word <= f_s_stream_word);
				assert(f_s_stream_word
					== ((f_m_stream_word + (M_AXIN_VALID ? 1:0)) * WIDE_COUNT)
						+ wide_counter);
			end
			assert(!M_AXIN_LAST || M_AXIN_VALID); // ?
			assert(M_AXIN_BYTES <= OW/8);
			if (M_AXIN_BYTES == OW/8)
				assert(M_AXIN_VALID);
			if (!M_AXIN_LAST && !M_AXIN_VALID)
				assert(wide_counter * IW/8 == M_AXIN_BYTES);
			if (M_AXIN_VALID)
				assert(wide_counter == 0);
			assert(data_concat == M_AXIN_DATA);
		end

		assign fm_first = M_AXIN_DATA >> (8*fc_posn[$clog2(OW/8)-1:0]);
		assign fm_next  = M_AXIN_DATA >> (8*fc_nxtposn[$clog2(OW/8)-1:0]);
		always @(*)
		if (ARESETN && !M_AXIN_ABORT
				&& ((f_s_stream_word > fs_first_word_cnt)
								|| M_AXIN_LAST)
				&& (f_m_stream_word * (OW/8) <= fc_posn)
				&& (fc_posn < (f_m_stream_word * (OW/8))
					+ (wide_counter*IW/8)
					+ (M_AXIN_VALID ? M_AXIN_BYTES : 0)))
		begin
			// Assert the first data
			assert(fm_first == fc_first);
		end

		always @(*)
		if (ARESETN && !M_AXIN_ABORT
				&& ((f_s_stream_word > fs_next_word_cnt)
								|| M_AXIN_LAST)
				&& (f_m_stream_word * (OW/8) <= fc_nxtposn)
				&& (fc_nxtposn < (f_m_stream_word * (OW/8))
					+ (wide_counter*IW/8)
					+ (M_AXIN_VALID ? M_AXIN_BYTES : 0)))
		begin
			// Assert the next data
			assert(fm_next == fc_next);
		end

`endif
		// }}}
		// }}}
	end else begin : IW_GREATER
		// {{{
		// Try IW=64, OW=32		(I need this for the project)
		// Verilator lint_off WIDTH
		localparam [$clog2(IW/8):0]	FULL_OUTWORD = OW/8;
		// Verilator lint_on  WIDTH

		reg	[IW-OW-1:0]	data_parse;
		reg	[$clog2(IW/8):0] remaining_bytes;
		reg			remaining_last, mid_packet;
		reg	[OW-1:0]	mdata;

		initial mid_packet = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			mid_packet <= 0;
		else if (S_AXIN_ABORT && !S_AXIN_VALID)
			mid_packet <= 0;
		else if (S_AXIN_VALID && S_AXIN_READY)
			mid_packet <= !S_AXIN_LAST && !S_AXIN_ABORT;

		// M_AXIN_ABORT
		initial M_AXIN_ABORT = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			M_AXIN_ABORT <= 0;
		else if (M_AXIN_VALID && !M_AXIN_READY
				&& (M_AXIN_ABORT || (S_AXIN_ABORT && mid_packet)))
			M_AXIN_ABORT <= 1;
		else if (S_AXIN_ABORT && mid_packet)
			M_AXIN_ABORT <= 1;
		else if (!M_AXIN_VALID || M_AXIN_READY)
			M_AXIN_ABORT <= 0;

		// S_AXIN_READY
		// We shouldn't get the data unless we convey all the
		//   incoming data from slave (check!)

		// Don't register s_ready !!!
		assign S_AXIN_READY = S_AXIN_ABORT || (!M_AXIN_ABORT &&
			(!M_AXIN_VALID
				|| (M_AXIN_READY && remaining_bytes == 0)));

		// Which word (32-bit) should we send first ?
		// Little endian => sends 0 first
		always @(posedge ACLK)
		if (!ARESETN)
			mdata <= 0;
		else if (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
			mdata <= S_AXIN_DATA[0 +: OW];
		else if (M_AXIN_VALID && M_AXIN_READY && !M_AXIN_ABORT)
			mdata <= data_parse[0 +: OW];

		assign M_AXIN_DATA = mdata;

		// M_AXIN_VALID
		initial M_AXIN_VALID = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			M_AXIN_VALID <= 0;
		else if (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
			M_AXIN_VALID <= 1;
		else if (M_AXIN_READY && (remaining_bytes == 0 || M_AXIN_LAST || M_AXIN_ABORT))
			M_AXIN_VALID <= 0;

		// M_AXIN_BYTES, M_AXIN_LAST, data_parse, remaining_*
		// {{{
		initial remaining_last  = 0;
		initial remaining_bytes = 0;
		initial M_AXIN_BYTES    = 0;
		initial M_AXIN_LAST     = 0;
		initial data_parse      = 0;
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			remaining_last  <= 0;
			remaining_bytes <= 0;
			M_AXIN_BYTES    <= 0;
			M_AXIN_LAST     <= 0;
			data_parse      <= 0;
		end else if (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
		begin
			// Verilator lint_off WIDTH
			remaining_bytes <= (S_AXIN_BYTES > FULL_OUTWORD) ? (S_AXIN_BYTES - FULL_OUTWORD) : 0;
			M_AXIN_BYTES    <= (S_AXIN_BYTES > FULL_OUTWORD) ? FULL_OUTWORD : S_AXIN_BYTES[$clog2(OW/8):0];
			M_AXIN_LAST     <= S_AXIN_LAST && (S_AXIN_BYTES <= FULL_OUTWORD);
			remaining_last  <= (S_AXIN_LAST && S_AXIN_BYTES > FULL_OUTWORD);
			// Verilator lint_on  WIDTH
			data_parse      <= S_AXIN_DATA[IW-1 : OW];
		end else if (M_AXIN_ABORT && (!M_AXIN_VALID || M_AXIN_READY))
		begin
			remaining_bytes <= 0;
			M_AXIN_BYTES    <= 0;
			M_AXIN_LAST     <= 0;
			remaining_last  <= 0;
			data_parse      <= 0;
		end else if (M_AXIN_VALID && M_AXIN_READY)
		begin
			// Verilator lint_off WIDTH
			remaining_bytes <= (remaining_bytes <= FULL_OUTWORD) ? 0 : (remaining_bytes - FULL_OUTWORD);
			M_AXIN_BYTES    <= (remaining_bytes > FULL_OUTWORD) ? FULL_OUTWORD : remaining_bytes;
			M_AXIN_LAST     <= (remaining_bytes > FULL_OUTWORD) ? 0 : remaining_last;
			remaining_last  <= (remaining_bytes <= FULL_OUTWORD) ? 0 : remaining_last;
			data_parse      <= data_parse >> OW;
			// Verilator lint_on  WIDTH
		end
		// }}}

		////////////////////////////////////////////////////////////////
		//
		// Formal properties
		// {{{
		////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		always @(*)
		if (ARESETN)
		begin
			assert(FULL_OUTWORD == OW/8);
			if (M_AXIN_VALID && M_AXIN_LAST)
			begin
				assert(f_s_stream_word == 0);
				assert(remaining_bytes == 0);
			end else begin
				if (!M_AXIN_ABORT)
					assert(mid_packet == (f_s_stream_word > 0));
				if (remaining_last)
					assert(f_s_stream_word == 0);
				else begin
					if (!M_AXIN_ABORT)
						assert((f_s_stream_word * IW/OW) == (f_m_stream_word + remaining_bytes/(OW/8) + (M_AXIN_VALID ? 1:0)));
				end
			end

			assert(remaining_bytes <= (IW-OW)/8);
			assert(f_m_stream_word < (MAX_LENGTH * (IW/OW)));
			if (M_AXIN_ABORT)
				assert(!mid_packet || (S_AXIN_VALID && S_AXIN_ABORT));
			if (!M_AXIN_ABORT)
				assert(mid_packet == (f_s_stream_word != 0));
			if (!mid_packet)
				assert(f_s_stream_word == 0);
			if (!mid_packet && !remaining_last && !M_AXIN_LAST && !M_AXIN_ABORT)
				assert(f_m_stream_word == 0);
			assert(f_s_stream_word <= f_m_stream_word + 1); // +1 is for first word of slave
			assert(!M_AXIN_LAST || M_AXIN_VALID);   // !!!
			assert(M_AXIN_BYTES <= OW/8);
			if (M_AXIN_BYTES == OW/8)
				assert(M_AXIN_VALID);
			if (remaining_bytes > 0 && !S_AXIN_ABORT)
				assert(!S_AXIN_READY);
			if (mid_packet)
				assert(remaining_last == 0);
			if(!mid_packet && !M_AXIN_VALID && !M_AXIN_ABORT)
				assert(f_m_stream_word == 0);
			if(!remaining_last && (OW > 8))
				assert(remaining_bytes[$clog2(OW/8)-1:0] == 0);
			if (remaining_bytes > 0) 
				assert(M_AXIN_VALID);
			if (M_AXIN_VALID && remaining_last)
				assert(f_m_stream_word + 1 >= (MIN_LENGTH * (IW/OW)));
			if(remaining_bytes == 0)
				assert(!remaining_last);
			if(M_AXIN_VALID && remaining_last)
				assert(((f_m_stream_word[$clog2(IW/OW)-1 : 0] * OW/8) + (OW/8 * ((remaining_bytes + (M_AXIN_VALID ? OW/8 : 0) + (OW/8)-1) / (OW/8)))) <= (IW/8));
		end

		always @(*)
		if (ARESETN && !M_AXIN_ABORT
			&& ((f_s_stream_word > fs_first_word_cnt)
					|| M_AXIN_LAST || remaining_last)
			&& (f_m_stream_word <= fm_first_word_cnt)
			&& ((fm_first_word_cnt * (OW/8)) < f_m_stream_word * (OW/8) + remaining_bytes + (M_AXIN_VALID ? OW/8 : 0)))
		begin
		// Assert the first data
		assert(fm_first == fc_first);
		end

		always @(*)
		if (ARESETN && !M_AXIN_ABORT
			&& ((f_s_stream_word > fs_next_word_cnt)
					|| M_AXIN_LAST || remaining_last)
			&& (f_m_stream_word <= fm_next_word_cnt)
			&& ((fm_next_word_cnt * (OW/8)) < f_m_stream_word * (OW/8) + remaining_bytes + (M_AXIN_VALID ? OW/8 : 0)))
		begin
			// Assert the next data
			assert(fm_next == fc_next);
		end

		assign fm_first = { data_parse, M_AXIN_DATA }
			>> ((8*fc_posn[$clog2(IW/8)-1:0])
				- (f_m_stream_word[$clog2(IW/OW)-1:0]*OW));
		assign fm_next  = { data_parse, M_AXIN_DATA }
			>> ((8*fc_nxtposn[$clog2(IW/8)-1:0])
				- (f_m_stream_word[$clog2(IW/OW)-1:0]*OW));
`endif
		// }}}
		// }}}
	end endgenerate

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

	// Let the solver pick whether or not we allow aborts
	(* anyconst *) reg	fc_allow_aborts;
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge ACLK)
		f_past_valid <= 1;

	always @(posedge ACLK)
	if (!f_past_valid)
		assume(!ARESETN);

	// fc_first_word_cnt, fc_next_word_cnt
	// fc_first_byte, fc_next_byte
	assign fs_first_word_cnt = fc_posn[$clog2(MAX_LENGTH):$clog2(IW/8)];
	assign fs_next_word_cnt = fc_nxtposn[$clog2(MAX_LENGTH):$clog2(IW/8)];
	assign fs_first_byte = (IW <= 8) ? 0 : fc_posn[$clog2(IW/8)-1:0];
	assign fs_next_byte = (IW <= 8) ? 0 : fc_nxtposn[$clog2(IW/8)-1:0];
	assign fm_first_word_cnt = fc_posn[$clog2(MAX_LENGTH):$clog2(OW/8)];
	assign fm_next_word_cnt = fc_nxtposn[$clog2(MAX_LENGTH):$clog2(OW/8)];
	assign fm_first_byte = (OW <= 8) ? 0 : fc_posn[$clog2(OW/8)-1:0];
	assign fm_next_byte  = (OW <= 8) ? 0 : fc_nxtposn[$clog2(OW/8)-1:0];

	// fc_nxtposn
	assign	fc_nxtposn = fc_posn + 1;
	always @(*)
		assume(fc_nxtposn != 0);

	////////////////////////////////////////////////////////////////////////
	//
	// Slave stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	// assume properties of the inputs

	// faxin_slave
	// {{{
	faxin_slave #(
		.DATA_WIDTH(IW),
		.MIN_LENGTH(MIN_LENGTH_I),
		.MAX_LENGTH(MAX_LENGTH_I),
		.LGMX(LGMX),
		.WBITS($clog2(IW+1))
	) fslave (
		.S_AXI_ACLK(ACLK), .S_AXI_ARESETN(ARESETN),
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA),
		.S_AXIN_BYTES(S_AXIN_BYTES),
		.S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		.f_stream_word(f_s_stream_word),
		.f_packets_rcvd(f_s_packets_rcvd)
	);
	// }}}

	// S_AXIN_BYTES
	// {{{
	always @(*)
	if (ARESETN && S_AXIN_VALID)
	begin
		assume(S_AXIN_BYTES > 0);
		assume(S_AXIN_BYTES <= IW/8);
		if (!S_AXIN_LAST)
			assume(S_AXIN_BYTES == (IW/8));
	end
	// }}}

	// MIN_LENGTH & S_AXIN_LAST
	// {{{
	always @(*)
	if (f_s_stream_word < MIN_LENGTH)
		assume(!S_AXIN_LAST);
	// }}}

	// S_AXIN_ABORT
	always @(*)
	if (ARESETN && !fc_allow_aborts)
		assume(!S_AXIN_ABORT);

	always @(*)
	if (ARESETN && S_AXIN_VALID && f_s_stream_word == fs_first_word_cnt)
	begin
		// Assume the first data
		if (IW == 8)
		begin
			assume(S_AXIN_DATA == fc_first);
		end else begin
			assume(S_AXIN_DATA[fs_first_byte*8 +: 8] == fc_first);
		end
	end

	always @(*)
	if (ARESETN && S_AXIN_VALID && f_s_stream_word == fs_next_word_cnt)
	begin
		// Assume the next data
		if (IW == 8)
		begin
			assume(S_AXIN_DATA == fc_next);
		end else begin
			assume(S_AXIN_DATA[fs_next_byte*8 +: 8] == fc_next);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Master stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	// assert properties of the outputs

	// faxin_master
	faxin_master #(
		.DATA_WIDTH(OW),
		.MIN_LENGTH(MIN_LENGTH_O),
		.MAX_LENGTH(MAX_LENGTH_O),
		.LGMX(LGMX),
		.WBITS($clog2(OW+1))
	) fmaster (
		.S_AXI_ACLK(ACLK), .S_AXI_ARESETN(ARESETN),
		.S_AXIN_VALID(M_AXIN_VALID),
		.S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA),
		.S_AXIN_BYTES(M_AXIN_BYTES),
		.S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		.f_stream_word(f_m_stream_word),
		.f_packets_rcvd(f_m_packets_rcvd)
	);

	// M_AXIN_ABORT
	always @(*)
	if (ARESETN && !fc_allow_aborts)
		assert(!M_AXIN_ABORT);

	always @(*)
	if (ARESETN && M_AXIN_ABORT)
		assert(f_s_stream_word == 0);

	always @(*)
	if (ARESETN && !M_AXIN_ABORT && ((f_s_stream_word > fs_first_word_cnt) || M_AXIN_LAST)
			&& (f_m_stream_word * (OW/8) <= fc_posn)
			&& (fc_posn < (f_m_stream_word * (OW/8)) + (M_AXIN_VALID ? M_AXIN_BYTES : 0)))
	begin
		// Assert the first data
		assert(fm_first == fc_first);
	end

	always @(*)
	if (ARESETN && !M_AXIN_ABORT
			&& ((f_s_stream_word > fs_next_word_cnt)
							|| M_AXIN_LAST)
			&& (f_m_stream_word * (OW/8) <= fc_nxtposn)
			&& (fc_nxtposn < (f_m_stream_word * (OW/8)) + (M_AXIN_VALID ? M_AXIN_BYTES : 0)))
	begin
		// Assert the next data
		assert(fm_next == fc_next);
	end

	// M_AXIN_BYTES
	// {{{
	always @(*)
	if (M_AXIN_VALID)
	begin
		assert(M_AXIN_BYTES > 0);
		assert(M_AXIN_BYTES <= OW/8);
		if (!M_AXIN_LAST)
			assert(M_AXIN_BYTES == OW/8);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Low power rules (if we wish to use them)
    // {{{
    ////////////////////////////////////////////////////////////////////////

    /*
    // Power is used every time a register toggles
    // So, if OPT_LOWPOWER is set -- we keep registers from toggling
    //	(by pinning them to zero)
    always @(*)
    if (OPT_LOWPOWER && !M_AXIN_VALID)
    begin
        // Can't assert these first two, since you are building
        // in M_AXIN_DATA while !M_AXIN_VALID, so we won't assert
        // these at all.
        //
        // assert(M_AXIN_DATA  == 0);
        // assert(M_AXIN_BYTES == 0);
        //

        if (WIDE_COUNT == 0)
            assert(M_AXIN_DATA == 0);

        assert(M_AXIN_LAST  == 0);
    end

    always @(*)
    if (OPT_LOWPOWER && M_AXIN_VALID)
    begin
        for(i=0; i<OW/8; i=i+1)
        if (i >= M_AXIN_BYTES)
            assert(M_AXIN_DATA[8*i +: 8] == 0);
    end
    */
    // }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// }}}
`endif
// }}}
endmodule
