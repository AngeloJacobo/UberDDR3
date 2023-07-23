////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbucompress.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	When reading many words that are identical, it makes no sense
//		to spend the time transmitting the same thing over and over
//	again, especially on a slow channel.  Hence this routine uses a table
//	lookup to see if the word to be transmitted was one from the recent
//	past.  If so, the word is replaced with an address of the recently
//	transmitted word.  Mind you, the table lookup takes one clock per table
//	entry, so even if a word is in the table it might not be found in time.
//	If the word is not in the table, or if it isn't found due to a lack of
//	time, the word is placed into the table while incrementing every other
//	table address.
//
//	Oh, and on a new address--the table is reset and starts over.  This way,
//	any time the host software changes, the host software will always start
//	by issuing a new address--hence the table is reset for every new piece
//	of software that may wish to communicate.
//
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
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
//
// All input words are valid codewords.  If we can, we make them
// better here.
// }}}
module	wbucompress #(
		parameter	DW=32, CW=36, TBITS=10
	) (
		// {{{
		input	wire			i_clk, i_reset, i_stb,
		input	wire	[(CW-1):0]	i_codword,
		input	wire			i_busy,
		output	reg			o_stb,
		output	wire	[(CW-1):0]	o_cword,
		output	wire			o_busy,
		output	wire			o_active
		// }}}
	);

	// Local declarations
	// {{{
	// First stage is to compress the address.
	// This stage requires one clock.
	//
	//	ISTB,ICODWORD
	//	ISTB2,IWRD2	ASTB,AWORD
	//	ISTB3,IWRD3	ASTB2,AWRD2	I_BUSY(1)
	//	ISTB3,IWRD3	ASTB2,AWRD2	I_BUSY(1)
	//	ISTB3,IWRD3	ASTB2,AWRD2	I_BUSY(1)
	//	ISTB3,IWRD3	ASTB2,AWRD2
	//	ISTB4,IWRD4	ASTB3,AWRD3	I_BUSY(2)
	//	ISTB4,IWRD4	ASTB3,AWRD3	I_BUSY(2)
	//	ISTB4,IWRD4	ASTB3,AWRD3	I_BUSY(2)
	reg		aword_valid;
	reg	[35:0]	a_addrword;
	wire	[31:0]	w_addr;
	wire	[3:0]	addr_zcheck;
	wire		tbl_busy;

	wire			w_accepted;
	reg	[35:0]		r_word;
	reg	[(TBITS-1):0]	tbl_addr;
	reg			tbl_filled;
	reg	[31:0]		compression_tbl	[0:((1<<TBITS)-1)];
	reg	[(TBITS-1):0]	rd_addr;
	reg			pmatch;
	reg			dmatch, // Match, on clock 'd'
				vaddr;	// Was the address valid then?
	reg	[(DW-1):0]	cword;
	reg	[(TBITS-1):0]	maddr;
	reg			matched;	// Have we matched already?
	reg			zmatch, hmatch;
	reg	[9:0]		adr_dbld;
	reg	[2:0]		adr_hlfd;
	reg	[(CW-1):0]	r_cword; // Record our result
	reg	[TBITS-1:0]	dffaddr;
	reg			clear_table;
	reg			addr_within_table;
	wire			w_match;

	integer	k;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Address compression stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	w_addr = i_codword[31:0];
	assign	addr_zcheck[0] = (w_addr[11: 6] == 0);
	assign	addr_zcheck[1] = (w_addr[17:12] == 0);
	assign	addr_zcheck[2] = (w_addr[23:18] == 0);
	assign	addr_zcheck[3] = (w_addr[31:24] == 0);

	assign	o_busy = aword_valid && tbl_busy;

	always @(posedge i_clk)
	if (!o_busy)
	begin
		if (i_codword[35:32] != 4'h2)
			a_addrword <= i_codword;
		else casez(addr_zcheck)
		4'b1111: a_addrword <= { 6'hc, w_addr[ 5:0], 24'h00 };
		4'b1110: a_addrword <= { 6'hd, w_addr[11:0], 18'h00 };
		4'b110?: a_addrword <= { 6'he, w_addr[17:0], 12'h00 };
		4'b10??: a_addrword <= { 6'hf, w_addr[23:0],  6'h00 };
		default: a_addrword <= i_codword;
		endcase
	end

	// aword_valid is the output of the address compression stage
	initial	aword_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		aword_valid <= 1'b0;
	else if (i_stb && !o_busy)
		aword_valid <= 1'b1;
	else if (!tbl_busy)
		aword_valid <= 1'b0;
	// }}}
	////////////////////////////////////////////////////////////////////////

	//
	//
	// The next stage attempts to replace data codewords with previous
	// codewords that may have been sent.  The memory is only allowed
	// to be as old as the last new address command.  In this fashion,
	// any program that wishes to talk to the device can start with a
	// known compression table by simply setting the address and then
	// reading from the device.
	//

	// We start over any time a new value shows up, and
	// the follow-on isn't busy and can take it.  Likewise,
	// we reset the writer on the compression any time a
	// i_clr value comes through (i.e., ~i_cyc or new
	// address)

	assign	w_accepted = (o_stb && !tbl_busy);
	assign	tbl_busy = (o_stb && i_busy);

	always @(posedge i_clk)
	if (!tbl_busy)
		r_word <= a_addrword;

	//
	// First step of the compression is keeping track of a compression
	// table.  And the first part of that is keeping track of what address
	// to write into the compression table, and whether or not the entire
	// table is full or not.  This logic follows:
	//
	// First part, write the compression table

	// clear_table
	// {{{
	always @(*)
	if (i_reset)
		clear_table = 1;
	else begin
		// If we send a new address, then reset the table to empty
		//
		//
		// Reset on new address (0010xx) and on new compressed
		// addresses (0011ll).

		clear_table = (o_stb && !i_busy && (o_cword[35:33] == 3'b001));
	end
	// }}}

	// tbl_addr (Table write address)
	// {{{
	initial	tbl_addr = 0;
	always @(posedge i_clk)
	if (clear_table)
		tbl_addr <= 0;
	else if (w_accepted)
	begin
		// Otherwise, on any valid return result that wasn't
		// from our table, for whatever reason (such as didn't
		// have the clocks to find it, etc.), increment the
		// address to add another value into our table
		if (o_cword[35:33] == 3'b111)
			tbl_addr <= tbl_addr + {{(TBITS-1){1'b0}},1'b1};
	end
	// }}}

	// tbl_filled
	// {{{
	initial	tbl_filled = 1'b0;
	always @(posedge i_clk)
	if (clear_table)
		tbl_filled <= 1'b0;
	else if (tbl_addr == 10'h3ff)
		tbl_filled <= 1'b1;
	// }}}

	// compression_tbl[] -- write to the table
	// {{{
	// Now that we know where we are writing into the table, and what
	// values of the table are valid, we need to actually write into
	// the table.
	//
	// We can keep this logic really simple by writing on every clock
	// and writing junk on many of those clocks, but we'll need to remember
	// that the value of the table at tbl_addr is unreliable until tbl_addr
	// changes.
	//
	initial begin
		for(k=0; k<(1<<TBITS); k=k+1)
			compression_tbl[k] = 0;
	end

	// Write new values into the compression table
	always @(posedge i_clk)
		compression_tbl[tbl_addr] <= { r_word[32:31], r_word[29:0] };
	// }}}

	// Now that we have a working table, can we use it?
	// On any new word, we'll start looking through our codewords.
	// If we find any that matches, we're there.  We might (or might not)
	// make it through the table first.  That's irrelevant.  We just look
	// while we can.

	// rd_addr
	// {{{
	initial	rd_addr = 0;
	always @(posedge i_clk)
	if (clear_table)
	begin
		rd_addr <= -1;
	end else if (!o_stb || !i_busy)
	begin
		rd_addr <= tbl_addr-((o_stb && o_cword[35:33] == 3'b111)? 0:1);
	end else begin
		rd_addr <= rd_addr - 1;
	end
	// }}}

	initial	dmatch = 0;
	always @(posedge i_clk)
	begin
		// First clock, read the value from the compression table
		cword <= compression_tbl[rd_addr];

		// Second clock, check for a match
		dmatch <= (cword == { r_word[32:31], r_word[29:0] })
				&& pmatch && !matched && vaddr;
		maddr  <= dffaddr;

		if (!o_stb || !i_busy)
			dmatch <= 1'b0;
	end

	// dffaddr -- what we encode when we find a match
	// {{{
	// The address difference is what we'll use to encode our table
	// address.  It's designed to match tbl_addr - rd_addr.  The smallest
	// valid dffaddr is 1, since tbl_addr is a junk address written on
	// every clock.
	initial	dffaddr = 0;
	always @(posedge i_clk)
	if (clear_table || !o_stb || !i_busy)
		dffaddr <= 1;
	else
		dffaddr <= dffaddr + 1;
	// }}}

	// vaddr -- is our value, from within the table, now, a valid entry?
	// {{{
	// Is the value within the table even valid?  Let's check that here.
	// It will be valid if the read address is strictly less than the
	// table address (in an unsigned way).  However, our table address
	// wraps.  Therefore we used tbl_filled to tell us if the table
	// address has wrapped, and in that case the address will always
	// have valid information within it.
	initial	vaddr = 0;
	always @(posedge i_clk)
	if (i_reset || !i_busy)
		vaddr <= 0;
	else
		vaddr <= ( {1'b0, rd_addr} < {tbl_filled, tbl_addr} );
	// }}}

	// addr_within_table
	// {{{
	// Is our address (indicated by the address difference, dffaddr),
	// within the realm of what we can represent/return?  Likewise, if we
	// wander outside of the realms of our table, make sure we don't
	// come back in and declare a success.
	initial	addr_within_table = 1;
	always @(posedge i_clk)
	if (i_reset || !i_busy)
		addr_within_table <= 1;
	else if (addr_within_table)
		addr_within_table <= (dffaddr <= 10'd521);
	// }}}

	// pmatch -- is the match even *possible*
	// {{{
	// pmatch indicates a *possible* match.  It's basically a shift
	// register indicating what/when things are valid--or at least it
	// was.  As of the last round of editing, pmatch is now only a single
	// valid bit.
	//
	initial	pmatch = 0;
	always @(posedge i_clk)
	if (i_reset)
		pmatch <= 0;
	else if (!tbl_busy)
		pmatch <= 0; // rd_addr is set on this clock
	else
		// cword is set on the next clock, pmatch = 3'b001
		// dmatch is set on the next clock, pmatch = 3'b011
		pmatch <= 1;
	// }}}

	assign	w_match = (addr_within_table && dmatch && r_word[35:33]==3'b111);

	// matched -- have we found a match yet?
	// {{{
	// matched records whether or not we've already matched, and so we
	// shouldn't therefore match again.
	//
	initial	matched = 0;
	always @(posedge i_clk)
	if (i_reset)
		matched <= 0;
	else if (!i_busy || !o_stb)	// Reset upon any write
		matched <= 1'b0;
	else if (!matched)
		// To be a match, the table must not be empty,
		matched <= w_match;
	// }}}

	// zmatch, hmatch
	// {{{
	// zmatch and hmatch are address helper values.  They tell us if the
	// current item we are matching is the last item written (zmatch), one
	// of the last nine items written (hmatch), or none of the above--since
	// each of these have different encodings
	initial	{ zmatch, hmatch } = 0;
	always @(posedge i_clk)
	if (i_reset || (!o_stb || !i_busy) || !pmatch)
		{ zmatch, hmatch } <= 0;
	else begin
		zmatch    <= (dffaddr == 10'h2);
		hmatch    <= (dffaddr < 10'd11);
	end
	// }}}

	//
	// matchaddr holds the value we intend to encode into the table
	//
	always @(posedge i_clk)
	if (!matched && !w_match)
	begin
		// Since optimizing the core, it's no longer needed.  We'll
		// reconstruct it in the formal properties as f_matchaddr
		// matchaddr <= maddr;

		// Calcualte our encodings
		adr_hlfd <= maddr[2:0]- 3'd2;
		adr_dbld <= maddr - 10'd10;
	end

	// r_cword -- the final code word output
	// {{{
	always @(posedge i_clk)
	if (!tbl_busy)		// Reset whenever word gets written
		r_cword <= a_addrword;
	else if (!matched && w_match)
	begin
		r_cword <= r_word;
		if (zmatch) // matchaddr == 1
			r_cword[35:30] <= { 5'h3, r_word[30] };
		else if (hmatch) // 2 <= matchaddr <= 9
			r_cword[35:30] <= { 2'b10, adr_hlfd, r_word[30] };
		else // if (adr_diff < 10'd521)
			r_cword[35:24] <= { 2'b01, adr_dbld[8:6],
					r_word[30], adr_dbld[5:0] };
	end
	// }}}

	// o_stb
	// {{{
	initial	o_stb = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 0;
	else if (aword_valid)
		o_stb <= 1;
	else if (!i_busy)
		o_stb <= 0;
	// }}}

	assign	o_cword  = r_cword;
	assign	o_active = i_stb || o_stb || aword_valid;
	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = adr_dbld[9];
	// verilator lint_on  UNUSED
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
	reg			f_past_valid;
	reg	[TBITS-1:0]	f_daddr, f_match_addr;
	reg	[9:0]		f_adr_dbld;
	reg	[2:0]		f_adr_hlfd;
	reg	[TBITS-1:0]	f_rd_diff;
	reg	[(TBITS-1):0]	f_caddr;
	reg	[(TBITS-1):0]	f_matchaddr;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	//
	////////////////////////////////////////////////////////////////////////
	//
	always @(*)
	if (i_stb)
	begin
		assume(i_codword[35:31] != 5'h3);
		assume(i_codword[35:34] != 2'b01);
		assume(i_codword[35:34] != 2'b10);
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(i_stb && i_busy))
	begin
		assume(i_stb);
		assume($stable(i_codword));
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Contract assertions (i.e. ... is the compression working?)
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Address compression check
	always @(posedge i_clk)
	if (f_past_valid && !$past(aword_valid && tbl_busy) && aword_valid)
	begin
		if ($past(i_codword[35:32] != 4'h2))
			assert(a_addrword == $past(i_codword));
		else if ($past(i_codword[31:6]) == 26'h00)
			assert(a_addrword == { 6'hc, $past(i_codword[ 5:0]), 24'h00 });
		else if ($past(i_codword[31:12]) == 20'h00)
			assert(a_addrword == { 6'hd, $past(i_codword[11:0]), 18'h00 });
		else if ($past(i_codword[31:18]) == 14'h00)
			assert(a_addrword == { 6'he, $past(i_codword[17:0]), 12'h00 });
		else if ($past(i_codword[31:24]) == 8'h00)
			assert(a_addrword == { 6'hf, $past(i_codword[23:0]),  6'h00 });
		else
			assert(a_addrword == $past(i_codword));
	end

	//
	// Check compression words against the table
	//

	always @(*)
		f_adr_dbld = (f_matchaddr - 10);
	always @(*)
		f_adr_hlfd = (f_matchaddr[2:0] - 3'd2);

	always @(*)
	if (o_stb)
	begin
		if (r_word[35:33] == 3'b111)
			assert(matched || r_cword[35:33] == 3'b111);

		// If the codeword is the result of a match, the match
		// must match what's in the table
		if (o_cword[35:31] == 5'h3)
		begin
			assert(r_cword[30] == r_word[30]);
			assert(compression_tbl[f_match_addr] == { r_word[32:31], r_word[29:0] });
			assert(f_matchaddr == 1);
		end else if (o_cword[35:34] == 2'b10)
		begin
			assert(compression_tbl[f_match_addr] == { r_word[32:31], r_word[29:0] });
			assert(r_cword[33:31] == f_adr_hlfd);
			assert(f_matchaddr < 10);
			assert(f_matchaddr > 1);
		end else if (o_cword[35:34] == 2'b01)
		begin
			assert(compression_tbl[f_match_addr] == { r_word[32:31], r_word[29:0] });
			assert(r_cword[33:31] == f_adr_dbld[8:6]);
			assert(r_cword[30] == r_word[30]);
			assert(r_cword[29:24] == f_adr_dbld[5:0]);
			assert(f_matchaddr >= 10);
			assert(f_matchaddr -10 <= 10'h1ff);
		end else
			assert(o_cword == r_word);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_reset && o_stb && i_busy)))
	begin
		assert(o_stb);

		// Once a match has taken place, or similarly if this codeword
		// isn't a matchable one, then it should be stable
		if ($past(o_cword[35:33]) != 3'b111)
			assert($stable(o_cword));
	end

`ifdef	VERIFIC
	reg	[4:0]	r_seq_counter;
	always @(posedge i_clk)
		r_seq_counter <= r_seq_counter + 1;

	assert property (@(posedge i_clk)
		// This complicated sequence makes sure we abort the test
		// if i_busy drops too early
		disable iff (i_reset
			|| (r_seq_counter > 1)&&(r_seq_counter < 7)&&(!i_busy))
		//
		// Two setup clocks
		//
		(o_stb && !i_busy && o_cword[35:33] == 3'b111)
			&&(r_seq_counter == 0)
		##1 o_stb && $stable(o_cword) && i_busy
		|-> (rd_addr == $past(tbl_addr))
			##1 (cword == $past({ r_word[32:31], r_word[29:0] }))
			##1 dmatch && w_match
			##1 o_stb && o_cword[35:31] == 5'h3);

	assert property (@(posedge i_clk)
		disable iff (i_reset
			|| (r_seq_counter > 2)&&(r_seq_counter < 7)&&(!i_busy))
		//
		// Accept two words
		(o_stb && !i_busy && o_cword[35:33] == 3'b111)
			&&(r_seq_counter == 0)
		##1 (o_stb && !i_busy && $changed({o_cword[32:31], o_cword[29:0]})
			&& (o_cword[35:33] == 3'b111))
		// Receive a third, identical to the first
		##1 (o_stb && o_cword == $past(o_cword,2))&&(i_busy)
		|=> ##1 (cword == $past({ r_word[32:31], r_word[29:0] },2))
				&&(r_seq_counter == 4)
			##1 dmatch && w_match && hmatch
			##1 o_stb && (o_cword[35:34] == 2'b10)
				&& (o_cword[33:31] == 3'b000));
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// Induction assertions
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (aword_valid)
	begin
		assert(a_addrword[35:31] != 5'h3);
		assert(a_addrword[35:34] != 2'b01);
		assert(a_addrword[35:34] != 2'b10);
	end

	always @(posedge i_clk)
	if (!matched && !w_match)
		f_matchaddr <= maddr;

	always @(*)
		f_rd_diff = tbl_addr - rd_addr;

	always @(*)
	if (o_stb)
		assert(f_rd_diff == dffaddr);


	always @(posedge i_clk)
		f_caddr <= rd_addr;
	always @(posedge i_clk)
		f_daddr <= f_caddr;

	always @(*)
		f_match_addr = tbl_addr - f_matchaddr;

	always @(*)
	if (matched)
	begin
		assert(adr_dbld == f_adr_dbld);
		assert(adr_hlfd == f_adr_hlfd);
	end

	always @(*)
	if (o_stb && dmatch)
	begin
		assert(compression_tbl[f_daddr] == { r_word[32:31], r_word[29:0] });
		// assert(maddr == tbl_addr - f_daddr);
	end

	always @(*)
	if (o_stb && matched)
	begin
		assert(compression_tbl[f_match_addr] == { r_word[32:31], r_word[29:0] });
	end

	always @(*)
	if (matched)
	begin
		assert({ 1'b0, f_match_addr } < { tbl_filled, tbl_addr });
		assert(f_match_addr != tbl_addr );
		assert(compression_tbl[f_match_addr]
				== { r_word[32:31], r_word[29:0] });
	end

	always @(*)
	if (r_word[35:33] != 3'b111)
		assert(!matched);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[1:0]	f_cvr_repeat_values, f_cvr_half_codewords, f_cvr_full_codewords;
	reg	[35:0]	f_last_codeword;
	reg		f_set_last;
	reg	[4:0]	f_time_since_last;


	initial { f_cvr_repeat_values, f_cvr_half_codewords, f_cvr_full_codewords } = 0;
	always @(posedge i_clk)
	if (i_reset)
		{ f_cvr_repeat_values, f_cvr_half_codewords, f_cvr_full_codewords } <= 0;
	else if (o_stb && !i_busy)
	begin
		if ((o_cword[35:31] == 5'h3)&&(!(&f_cvr_repeat_values)))
			f_cvr_repeat_values <= f_cvr_repeat_values + 1;
		if ((o_cword[35:34] == 2'b10)&&(!(&f_cvr_half_codewords)))
			f_cvr_half_codewords <= f_cvr_half_codewords + 1;
		if ((o_cword[35:34] == 2'b01)&&(!(&f_cvr_full_codewords)))
			f_cvr_full_codewords <= f_cvr_full_codewords + 1;
	end

	always @(*)
		cover(o_stb && !i_busy);

	always @(*)
		cover(cword == { r_word[32:31], r_word[29:0] });

	always @(*)
		cover(cword == { r_word[32:31], r_word[29:0] } && pmatch);

	always @(posedge i_clk)
		cover(cword == { r_word[32:31], r_word[29:0] } && pmatch);

	always @(*)
		cover((cword == { r_word[32:31], r_word[29:0] }) && pmatch
			&& (tbl_addr == 1) && (rd_addr == 10'h3ff));

	always @(*)
		cover((cword == { r_word[32:31], r_word[29:0] }) && pmatch
			&& (tbl_addr == 1));

	always @(posedge i_clk)
		cover((tbl_addr == 1) && o_stb &&i_busy);

	always @(*)
		cover(cword == { r_word[32:31], r_word[29:0] } && pmatch && vaddr);

	always @(*)
		cover(dmatch);

	always @(*)
		cover(w_match);

	always @(*)
		cover(!matched && w_match);

	always @(*)
		cover(o_stb && !i_busy && o_cword[35:31] == 5'h3);

	initial	f_set_last = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_set_last <= 0;
	else if (o_stb && !i_busy && o_cword[35:33] == 3'b111)
		f_set_last <= 1;

	initial	f_time_since_last = 0;
	always @(posedge i_clk)
	if (!o_stb || !i_busy)
		f_time_since_last <= 0;
	else if (f_set_last && !(&(f_time_since_last)))
		f_time_since_last <= f_time_since_last + 1;

	always @(posedge i_clk)
	if (o_stb && !i_busy && o_cword[35:33] == 3'b111)
		f_last_codeword <= o_cword;

	always @(*)
		cover(o_stb && !i_busy && f_set_last);

	always @(*)
		cover(o_stb && !i_busy && f_set_last && f_time_since_last > 4
			&&(r_word == f_last_codeword));


	always @(*)
	begin
		cover(f_cvr_full_codewords != 0);
		cover(f_cvr_half_codewords != 0);
		cover(f_cvr_repeat_values != 0);
		//
		cover(f_cvr_full_codewords == 0);
		cover(f_cvr_full_codewords == 1);
		cover(f_cvr_full_codewords == 2);
		//
		cover(&f_cvr_full_codewords);
		cover(&f_cvr_half_codewords);
		cover(&f_cvr_repeat_values);
		//
		cover((&f_cvr_repeat_values) && (&f_cvr_half_codewords));
		cover((&f_cvr_repeat_values) && (&f_cvr_full_codewords));
		//
		cover((&f_cvr_repeat_values) && (&f_cvr_half_codewords)
				&&(&f_cvr_full_codewords));
	end


`endif
// }}}
endmodule

