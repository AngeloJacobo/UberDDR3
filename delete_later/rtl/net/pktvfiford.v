////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfiford.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the second half, the *read* half of the Virtual Packet
//		FIFO.  Packets are defined by some number of bytes, with both
//	start and LAST (i.e. end).  Packets are assumed to be stored in memory,
//	starting with a 32-bit word containing the number of bytes in the
//	packet, followed by the packet data and then the 32-bit length word of
//	the next packet.  A length word of zero is evidence there are no (more)
//	packets present in memory.  The memory region is circular, so packets
//	may start before the end of the memory, and end after wrapping around
//	from the beginning.  This IP depends upon knowing where the write
//	pointer is (from the write half of the Virtual Packet FIFO) know when
//	to read the packet length from memory.  Hence, the write pointer must
//	always point to a valid (or empty) packet length word.
//
// Configuration:
//	i_cfg_reset_fifo	True if/when the FIFO is being reconfigured,
//			or the base address or memory size are not (yet)
//			valid.
//
//	i_cfg_baseaddr	Points to the word address (bus aligned) of the
//			beginning of the memory region.
//
//	i_cfg_memsize	This size of the allocated memory region, in bus words.
//			(Not bytes)  The memory region must be bus aligned.
//			The base address plus the memory size shall point to
//			one word past the end of memory.  Hence, if memory has
//			only two words (really too small), the base address
//			might be zero and the memsize two.
//
// Operation:
//	o_readptr	A memory pointer to a 32-bit word in memory.  The 2 LSBs
//			are inferred, but not included.  The pointer is used by
//			the other half (the write half) of the FIFO to
//			determine when/if the FIFO is full.  Hence, the write
//			half will never pass the read pointer.  The two
//			pointers, o_readptr and i_writeptr, will only ever be
//			equal when the FIFO is empty.
//
//	i_writeptr	Points to the length word the virtual packet FIFO
//			write half is looking at.  This length word will be
//			zero.  A new packet may be read if ever 1) the read
//			half is idle, and waiting to read a new packet length,
//			and 2) the write pointer is not equal to the read
//			pointer.
//
//	o_fifo_err	This is a check on the packet length.  Should an invalid
//			packet length ever be read, this FIFO error flag will
//			be set.  Examples of invalid lengths include zero length
//			packets, packet lengths longer than the memory size,
//			or even packet lengths longer than the distance to the
//			write pointer.
//
//	WB		A Wishbone master interface, used to read from memory.
//
//	M_*		The outgoing AXI network packet stream interface.
//			Unlike a full featured network packet stream, this
//			interface does not support READY, nor does it ever
//			generate an ABORT.
//
//	i_fifo_rd	The output of this module goes directly into a FIFO.
//			Since Wishbone has no ability to handle back pressure,
//			we have to guarantee (internally) that we never issue
//			more WB requests than the FIFO can hold.  Hence, we
//			keep track of how much space is available in the FIFO.
//			When a read request is issued, we decrement from the
//			space available, and when *i_fifo_rd* is true we add
//			one to the space available.
//
//			Incidentally, when i_cfg_reset_fifo is true, the FIFO
//			will be cleared and partial packets ABORTed (further
//			down in the pipeline.)
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
module	pktvfiford #(
		// {{{
		parameter	BUSDW = 512,
		parameter	AW = 30-$clog2(BUSDW/8),
		parameter	LGFIFO = 5,
		parameter	LGPIPE = 6,
		// MINLEN: A minimum packet length.  Packets lengths shorter
		// than MINLEN will generate a FIFO error.
		parameter	MINLEN = 64,	// Must be > 0
		// MAXLEN: A maximum packet length.  Packets lengths greater
		// than MAXLEN will generate a FIFO error.
		parameter	MAXLEN = 256, // (1<<(AW+$clog2(BUSDW/8))),
		parameter [0:0]	OPT_LOWPOWER = 1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0,
		localparam	WBLSB = $clog2(BUSDW/8)
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Control port
		// {{{
		input	wire			i_cfg_reset_fifo,
		input	wire	[AW-1:0]	i_cfg_baseaddr,
		input	wire	[AW-1:0]	i_cfg_memsize,
		input	wire	[AW+WBLSB-3:0]	i_writeptr,
		output	wire	[AW+WBLSB-3:0]	o_readptr,
		output	reg			o_fifo_err,
		// }}}
		// DMA bus interface
		// {{{
		output	reg			o_wb_cyc, o_wb_stb,
		output	wire			o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	wire	[BUSDW-1:0]	o_wb_data,
		output	reg	[BUSDW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		//
		input	wire			i_wb_ack,
		input	wire	[BUSDW-1:0]	i_wb_data,
		input	wire			i_wb_err,
		// }}}
		// Outgoing packet
		// {{{
		output	reg			M_VALID,
		// input wire			M_READY, // No backpressure supt
		output	reg	[BUSDW-1:0]	M_DATA,
		output	reg [$clog2(BUSDW/8)-1:0] M_BYTES,
		output	reg			M_LAST,
		// output wire			M_ABORT, // No ABORT support
		input	wire			i_fifo_rd
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// Local parameters
	// {{{
	localparam	[1:0]	RD_IDLE      = 2'h0,
				RD_SIZE      = 2'h1,
				RD_PACKET    = 2'h2,
				RD_CLEARBUS  = 2'h3;
	// }}}

	// Because we work with so many different types of pointers here,
	// the units are different all over the place, those with the wide_*
	// prefix are *octet* (i.e. 8-bit) pointers.
	reg	[AW+WBLSB-1:0]	wide_baseaddr, wide_memsize, // wide_writeptr
				wide_readptr;

	// The end of memory may require an extra bit, to capture the case where
	// we run right up to the last word in memory.
	reg	[AW+WBLSB:0]	end_of_memory;

	// The following three pointers are 32-bit word pointers, so the
	// bottom 2-LSBs are assumed to be zero, and not included in the
	// pointer.
	reg	[AW+(WBLSB-2)-1:0]	r_readptr, rd_wb_addr, r_endptr;

	reg	[LGPIPE:0]	rd_outstanding;
	reg			r_lastack, lastack;

	reg	[LGFIFO:0]	fifo_space;

	reg	[AW+WBLSB-1:0]	rd_pktlen;
	reg	[31:0]		next_rdlen;
	reg	[1:0]		rd_state;
	reg	[BUSDW-1:0]	wide_next_rdlen;

	reg	[AW+WBLSB:0]	next_rdaddr, next_rdptr,
				next_endptr, step_rdptr;

	reg			dly_check, dly_fifo_err;
	reg	[AW+WBLSB-1:0]	mem_fill;

	wire			full_return, false_ack;
	reg	[AW+WBLSB-1:0]	return_len, next_return_len;
	wire	[BUSDW/8-1:0]	ptrsel;

	wire	fifo_commit;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Most of our control logic is found in the parent module.  Expanding
	// our pointers to full byte-addresses is all that's left for us to do
	// here.  This just converts us to a common set of units, for following
	// pointer arithmetic.
	//

	always @(*)
	begin
		wide_baseaddr = 0;
		wide_baseaddr = { i_cfg_baseaddr, {(WBLSB){1'b0}} };

		wide_memsize  = 0;
		wide_memsize  = { i_cfg_memsize, {(WBLSB){1'b0}} };

		wide_readptr  = 0;
		wide_readptr  = { r_readptr, 2'b00 };
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read packets back out from memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// This is our main read-from-memory FSM handling section.  We start
	// with some combinatorial pointer math, before getting to the FSM
	// itself.

	generate if (BUSDW == 3)
	begin
		always @(*)
			wide_next_rdlen = i_wb_data;
	end else if (OPT_LITTLE_ENDIAN)
	begin
		always @(*)
			wide_next_rdlen = i_wb_data >> (32*r_readptr[WBLSB-3:0]);
	end else begin
		always @(*)
			wide_next_rdlen = i_wb_data << (32*r_readptr[WBLSB-3:0]);
	end endgenerate

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		next_rdlen = wide_next_rdlen[31:0];
	else
		next_rdlen = wide_next_rdlen[BUSDW-32 +: 32];

	// next_rdaddr = rd_wb_addr + BUSDW/8
	// {{{
	// This is a full (octet) address width pointer to the read address
	// plus one bus word (i.e. BUSDW/8 octets).  As with all of the pointers
	// used here, this pointer wraps around the end of memory if necessary.
	// Unlike the next_rdptr, which is very similar, this one is based
	// off of the current read request address, rd_wb_addr, from which we
	// grab the top AW bits to get o_wb_addr.
	always @(*)
	begin
		next_rdaddr = { rd_wb_addr, 2'b00 } + BUSDW/8;

		if (next_rdaddr >= end_of_memory)
			next_rdaddr = next_rdaddr - { i_cfg_memsize, {(WBLSB){1'b0}} };
	end
	// }}}

	// next_rdptr = r_readptr + BUSDW/8
	// {{{
	// A full (octet) address width pointer for the next address in memory,
	// following r_readptr, plus one (full) bus word.  The read pointer will
	// either be set to this address (while reading through packets), or its
	// address plus 4 (via step_rdptr).  Either way, the read pointer wraps
	// around the end of memory in (what should be) an operation transparent
	// to any user.
	always @(*)
	begin
		next_rdptr = { 1'b0, r_readptr, 2'b00 } + BUSDW/8;

		if (next_rdptr >= end_of_memory)
			next_rdptr = next_rdptr
					- { i_cfg_memsize, {(WBLSB){1'b0}} };
		if (next_rdptr[WBLSB +: AW] == r_endptr[WBLSB-2 +: AW])
			next_rdptr = { 1'b0, r_endptr, 2'b00 };
	end
	// }}}

	// r_endptr, next_endptr
	// {{{
	// A helper to calculate the full byte pointer, pointing to the last
	// valid 32-bit word of the packet in memory.  Since next_rdlen is
	// only valid when (rd_state == RD_SIZE && o_wb_cyc && i_wb_ack),
	// this value will also only be valid at the same time.
	always @(*)
	begin
		next_endptr = { r_readptr, 2'b00 } + next_rdlen[0+: AW+WBLSB]
				+ 3;	// Plus the size of the pointer,-1
		next_endptr[1:0] = 2'b00;
		if (next_endptr >= end_of_memory)
			next_endptr = next_endptr
					- { i_cfg_memsize, {(WBLSB){1'b0}} };
	end

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || (o_wb_cyc && i_wb_err))
		r_endptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
	else if (rd_state == RD_IDLE)
		r_endptr <= r_readptr;
	else if (rd_state == RD_SIZE && i_wb_ack)
		r_endptr <= next_endptr[AW+WBLSB-1:2];
	// }}}

	// step_rdptr = r_readptr + 4
	// {{{
	// step_rdptr is a full (octet) address width.  Here, we calculate
	// the circular pointer address to add one 32-bit value to r_readptr.
	// This can move us from the end of the packet to the length pointer
	// of the packet, or again from the length to the first word of the
	// packet.
	always @(*)
	begin
		step_rdptr = { r_readptr, 2'b00 } + 4;

		if (step_rdptr >= end_of_memory)
			step_rdptr = step_rdptr - { i_cfg_memsize, {(WBLSB){1'b0}} };
	end
	// }}}

	// ptrsel = (first o_wb_sel)
	// {{{
	generate if (BUSDW==32)
	begin
		assign	ptrsel = 4'hf;
	end else if (OPT_LITTLE_ENDIAN)
	begin
		assign	ptrsel = { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (4*r_readptr[WBLSB-3:0]);
	end else begin
		assign	ptrsel = { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (4*r_readptr[WBLSB-3:0]);
	end endgenerate
	// }}}

	initial	{ o_wb_cyc, o_wb_stb } = 2'b0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || o_fifo_err || (o_wb_cyc && i_wb_err))
	begin
		// {{{
		o_wb_cyc  <= 0;
		o_wb_stb  <= 0;
		rd_wb_addr <= 0;
		o_wb_sel  <= 0;
		r_readptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
		rd_state  <= RD_IDLE;
		rd_pktlen <= 0;
		// }}}
	end else case(rd_state)
	RD_IDLE: begin
		// {{{
		o_wb_cyc  <= 1'b0;
		o_wb_stb  <= 1'b0;
		rd_wb_addr <= r_readptr;
		rd_pktlen  <= 0;

		o_wb_sel <= ptrsel;

		if (i_writeptr != r_readptr)
		begin
			// Issue a read command to capture the packet length
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			rd_state <= RD_SIZE;
		end end
		// }}}
	RD_SIZE: begin
		// {{{
		rd_pktlen  <= 0;

		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (i_wb_ack)
		begin
			o_wb_cyc <= 1'b0;
			rd_state <= RD_PACKET;

			rd_pktlen  <= next_rdlen[AW+WBLSB-1:0];

			r_readptr  <= step_rdptr[AW+WBLSB-1:2];
			rd_wb_addr <= step_rdptr[AW+WBLSB-1:2];
		end end
		// }}}
	RD_PACKET: begin
		// {{{
		o_wb_sel <= {(BUSDW/8){1'b1}};
		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (lastack)
			o_wb_cyc <= 1'b0;

		// Don't increment the read pointer until the data comes back.
		// That way the writer will know it has clear access to this
		// data, now that it's been fully read and acknowledge.
		if (i_wb_ack)
			r_readptr <= next_rdptr[2 +: AW+(WBLSB-2)];

		if (o_wb_stb && !i_wb_stall)
		begin
			// This address may go too far, stepping once too
			// many times after the last address is corrected.
			// We'll come back and fix this in RD_IDLE later.
			rd_wb_addr   <= next_rdaddr[AW+WBLSB-1:2];
		end

		if (o_wb_stb && o_wb_addr == r_endptr[WBLSB-2 +: AW])
		begin
			rd_state <= RD_CLEARBUS;
		end else if (!o_wb_stb || !i_wb_stall)
		begin
			if (!rd_outstanding[LGPIPE]
					&& (fifo_space > (o_wb_stb ? 1:0)))
				{ o_wb_cyc, o_wb_stb } <= 2'b11;

		end end
		// }}}
	RD_CLEARBUS: begin
		// {{{
		// We come in here with the last request on the bus, either
		// with o_wb_stb high or it having already been issued.  Our
		// goal here is to deactivate the bus once the entire packet
		// has been requested, and then to go back to wait for the
		// next packet.
		o_wb_sel <= {(BUSDW/8){1'b1}};
		if (!i_wb_stall)
			o_wb_stb <= 1'b0;
		if (lastack)
		begin
			o_wb_cyc  <= 1'b0;
			rd_state  <= RD_IDLE;
			r_readptr <= step_rdptr[AW+WBLSB-1:2];
		end end
		// }}}
	default: begin end
	endcase
`ifdef	FORMAL
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || (o_wb_cyc && i_wb_err))
	begin
	end else case(rd_state)
	RD_IDLE: begin
		assert(!o_wb_cyc);
		assert(rd_outstanding == 0);
		// assert(!i_wb_ack);
		end
	RD_SIZE: begin
		assert(rd_outstanding + (o_wb_stb ? 1:0) == 1);
		if (i_wb_ack)
		begin
			// We don't need to assume a valid length here.
			// The FIFO error logic following will validate
			// it, and generate an error if it's not a valid
			// length.
			//
			// assume(next_rdlen[31:0] > 0);
			// assume(next_rdlen[31:0] + 8
			//		<= { fc_memsize, {(WBLSB){1'b0}} });
		end end
	RD_PACKET: begin end
	RD_CLEARBUS: begin
		assert(o_wb_addr == r_endptr[WBLSB-2 +: AW]);
		end
	endcase
	// }}}
`endif

	// rd_outstanding
	// {{{
	initial	rd_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || !o_wb_cyc)
		rd_outstanding <= 0;
	else case ({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: rd_outstanding <= rd_outstanding + 1;
	2'b01: rd_outstanding <= rd_outstanding - 1;
	default: begin end
	endcase
	// }}}

	// fifo_space
	// {{{
	generate if (BUSDW == 32)
	begin : NO_LAST_COMMIT
		assign	fifo_commit = (o_wb_stb && !i_wb_stall)
					&&(rd_state == RD_PACKET);
	end else begin : GEN_LAST_COMMIT
		assign	fifo_commit = (o_wb_stb && !i_wb_stall)
			&&((rd_state == RD_CLEARBUS&& r_readptr[WBLSB-3:0] != 0)
				||(rd_state == RD_PACKET));
	end endgenerate

	initial	fifo_space = 1<<LGFIFO;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		fifo_space <= 1<<LGFIFO;
	else case({ fifo_commit, i_fifo_rd })
	2'b10: fifo_space <= fifo_space - 1;
	2'b01: fifo_space <= fifo_space + 1;
	default: begin end
	endcase
`ifdef	FORMAL
	// {{{
	always @(*)
	if (fifo_space >= (1<<LGFIFO))
		assume(!i_fifo_rd);

	always @(*)
	if (!i_reset)
		assert(fifo_space <= (1<<LGFIFO));

	always @(*)
	if (!i_reset && o_wb_stb
			&& (rd_state == RD_PACKET || rd_state == RD_CLEARBUS))
		assert(fifo_space > 0);
	// }}}
`endif
	// }}}

	assign	o_wb_we   = 1'b0;
	assign	o_wb_data = {(BUSDW){1'b0}};
	assign	o_wb_addr = rd_wb_addr[AW+(WBLSB-2)-1:(WBLSB-2)];

	assign	o_readptr = r_readptr;

	// Last ack -- true when we need to drop CYC
	// {{{
	// We drop CYC for 3 reasons (other than memory errors, resets, etc.)
	// 1. We've read the packet size (CYC is dropped for one cycle)
	// 2. We've reached the end of the packet, and may need to wait for
	//	another packet
	// 3. The FIFO has no space left in it
	//
	// Here, we judge whether we've reached the last acknowledgment
	// before one of these reasons.
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || !o_wb_cyc)
		r_lastack <= 1;
	else
		r_lastack <= (rd_outstanding + ((o_wb_stb && !i_wb_stall) ? 1:0)
				<= (i_wb_ack ? 2:1));
	always @(*)
		lastack = r_lastack && (rd_outstanding[0] + (o_wb_stb ? 1:0)
					== (i_wb_ack ? 1:0));
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory size handling/checking, fifo error generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_fifo_err
	// {{{
	//	Two causes of FIFO errors:
	//	1. A zero length, after we've been told there's something there
	//	2. A packet that passes the write pointer
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		o_fifo_err <= 1'b0;
	else begin
		o_fifo_err <= 1'b0;
		if (dly_fifo_err)
			o_fifo_err <= 1'b1;
		if (o_wb_cyc && i_wb_ack && rd_state == RD_SIZE)
		begin
			if (next_rdlen + 1 >= wide_memsize)
				o_fifo_err <= 1'b1;
			if (next_rdlen < MINLEN)
				o_fifo_err <= 1'b1;
			if (next_rdlen >= MAXLEN)
				o_fifo_err <= 1'b1;
		end
	end
	// }}}

	// dly_check
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		dly_check <= 1'b0;
	else if (i_wb_ack && rd_state == RD_SIZE)
	begin
		dly_check <= 1'b1;
	end else
		dly_check <= 1'b0;
`ifdef	FORMAL
	always @(*)
	if (!i_reset && (rd_state == RD_IDLE || rd_state == RD_SIZE))
		assert(!dly_check);
`endif
	// }}}

	// mem_fill
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		mem_fill <= 0;
	else if (i_writeptr < r_readptr)
		mem_fill <= { i_writeptr, 2'b00 } - { r_readptr, 2'b00 }
							+ wide_memsize;
	else
		mem_fill <= { i_writeptr, 2'b00 } - { r_readptr, 2'b00 };
	// }}}

	// dly_fifo_err
	// {{{
	// Packet length verification check: Packets may not be larger than
	// the memory size available to them.  If they are, we declare an
	// error (o_fifo_err), and the controller will cause both write and
	// reader to abort and reset.
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || !dly_check)
		dly_fifo_err <= 1'b0;
	else
		dly_fifo_err <= (mem_fill < rd_pktlen + 4);
	// }}}

	always @(posedge i_clk)
		end_of_memory <= wide_baseaddr + wide_memsize;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Realign data, push return results out
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// M_VALID
	// {{{
	initial	M_VALID = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE)
		M_VALID <= 1'b0;
	else if ((i_wb_ack && full_return) || false_ack)
		M_VALID <= 1'b1;
	else // if (M_READY) -- backpressure not supported
		M_VALID <= 1'b0;
	// }}}

	generate if (BUSDW == 32)
	begin : NO_REALIGNMENT
		assign	full_return = 1'b1;	// All returns are full
		assign	false_ack   = 1'b0;	// No flushing returns

		// M_DATA (and sreg)
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
						|| rd_state == RD_SIZE)
			M_DATA <= 0;
		else if (!OPT_LOWPOWER || i_wb_ack)
			M_DATA <= i_wb_data;
		// }}}

		// next_return_len -- how many bytes are left?
		// {{{
		always @(*)
		if (return_len >= BUSDW/8)
			next_return_len = return_len - BUSDW/8;
		else
			next_return_len = 0;
		// }}}

	end else begin: GEN_REALIGNMENT
		reg			r_full_return, r_false_ack;
		reg	[BUSDW-1:0]	sreg;

		// full_return: Should an ACK trigger a full DW/8 output?
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
							|| rd_state == RD_SIZE)
			// We only generate a FIFO write on the first return
			// if the lower bits of the read pointer are zero.
			// HOWEVER ... the readptr in both IDLE and RD_SIZE
			// states points to the length word, not the first
			// data word, so we really need to add one, hence
			// we check for all bits being one here.
			r_full_return <= (&r_readptr[WBLSB-3:2]);
		else if (i_wb_ack)
			r_full_return <= 1'b1;

		assign	full_return = r_full_return;
		// }}}

		// false_ack: When do we flush our shift register?
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE
								|| !i_wb_ack)
			// Wrong time to flush, so ... don't
			r_false_ack <= 0;
		else if (!lastack || o_wb_addr != r_endptr[WBLSB-2 +: AW])
			// Can't flush yet, we're not done
			r_false_ack <= 0;
		else
			// NOW.  Flush is there's more data to return.
			r_false_ack <= (next_return_len != 0)
					&& (next_return_len < BUSDW/8);

		assign	false_ack = r_false_ack;
		// }}}

		// M_DATA (and sreg)
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE
							|| rd_state == RD_SIZE)
			{ M_DATA, sreg } <= 0;
		else if (i_wb_ack)
		begin
			if (r_readptr[WBLSB-3:0] == 0)
				{ sreg, M_DATA } <= { {(BUSDW){1'b0}}, i_wb_data };
			else if (OPT_LITTLE_ENDIAN)
				{ sreg, M_DATA }
					<= ({ {(BUSDW){1'b0}}, i_wb_data }
						<< (32*r_readptr[WBLSB-3:0]))
					| { {(BUSDW){1'b0}}, sreg };
			else // if (!OPT_LITTLE_ENDIAN)
				{ M_DATA, sreg }
					<= ({ i_wb_data, {(BUSDW){1'b0}} }
						>> (32*r_readptr[WBLSB-3:0]))
					| { sreg, {(BUSDW){1'b0}} };

			if (!full_return && OPT_LOWPOWER)
				M_DATA <= 0;
		end else if (false_ack)
		begin
			M_DATA <= sreg;
			sreg   <= {(BUSDW){1'b0}};
		end
`ifdef	FORMAL
		// {{{
		reg	[BUSDW-1:0]	f_chkzero;

		always @(*)
		if (OPT_LITTLE_ENDIAN)
		begin
			f_chkzero = (sreg >> (32*r_readptr[WBLSB-3:0]));
		end else begin
			f_chkzero = (sreg << (32*r_readptr[WBLSB-3:0]));
		end

		always @(*)
		if (!i_reset && (rd_state == RD_PACKET || rd_state == RD_CLEARBUS))
		begin
			assert(0 == f_chkzero);
		end else if (!i_reset && rd_state == RD_SIZE)
			assert(sreg == 0);
		// }}}
`endif
		// }}}

		// next_return_len -- how many bytes are left?
		// {{{
		always @(*)
		if (!full_return)
			next_return_len = return_len - (BUSDW/8)
				+ { {(AW){1'b0}}, r_readptr[WBLSB-3:0],2'b0 };
		else if (return_len >= BUSDW/8)
			next_return_len = return_len - BUSDW/8;
		else
			next_return_len = 0;
		// }}}

	end endgenerate

	// return_len: How many more bytes are to be expected?
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_IDLE)
		return_len <= 0;
	else if (o_wb_cyc && i_wb_ack && rd_state == RD_SIZE)
		return_len <= next_rdlen[AW+WBLSB-1:0];
	else if (o_wb_cyc && i_wb_ack)
		return_len <= next_return_len;
`ifdef	FORMAL
	// {{{
	// Relate return_len to the difference between r_readptr and r_endptr
	reg	[AW+WBLSB-1:0]	f_endptr, f_startptr;

	// f_startptr -- points to the length word's address of the current pkt
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		f_startptr <= { i_cfg_baseaddr, {(WBLSB){1'b0}} };
	else if (rd_state == RD_IDLE || rd_state == RD_SIZE)
		f_startptr <= { r_readptr, 2'b00 };
	// }}}

	always @(*)
	begin
		f_endptr = { r_readptr, 2'b00 } + return_len - 1;
		if (full_return && r_readptr[WBLSB-3:0] != 0)
		begin
			f_endptr = f_endptr
				+ (BUSDW/8) - { r_readptr[WBLSB-3:0], 2'b00 };
		end

		if (f_endptr >= end_of_memory)
		begin
			f_endptr = f_endptr- { i_cfg_memsize, {(WBLSB){1'b0}} };
		end

		f_endptr[1:0] = 2'b00;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && !o_fifo_err && !dly_fifo_err)
	case(rd_state)
	RD_IDLE: begin end
	RD_SIZE: begin
		assert(return_len == 0);
		assert(r_endptr == r_readptr);
		end
	default: begin
		assert(dly_check || { r_endptr, 2'b00 } == f_endptr);
		end
	endcase
	// }}}
`endif
	// }}}

	// M_BYTE
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || rd_state == RD_SIZE)
		M_BYTES <= 0;
	else if (return_len >= BUSDW/8)
		M_BYTES <= 0;
	else
		M_BYTES <= return_len[WBLSB-1:0];
	// }}}

	// M_LAST
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo)
		M_LAST <= 0;
	else
		M_LAST <= (return_len <= BUSDW/8);
	// }}}

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, wide_readptr, rd_wb_addr, wide_next_rdlen,
				next_endptr };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
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
	localparam	F_LGDEPTH = LGPIPE+1;
	reg	f_past_valid;
	wire	[F_LGDEPTH-1:0]	frd_nreqs, frd_nacks, frd_outstanding;
	(* anyconst *)	reg	[AW-1:0]	fc_baseaddr, fc_memsize;
	reg	[AW+WBLSB:0]	wide_end_of_packet, wide_committed,
				wide_writeptr;;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Configuration interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		assume({ 1'b0, fc_baseaddr } + { 1'b0, fc_memsize } <= (1<<AW));
		if (BUSDW == 32)
		begin
			assume(fc_memsize >= 8);
		end else if (BUSDW == 64)
		begin
			assume(fc_memsize >= 4);
		end else begin
			assume(fc_memsize >= 2);
		end
	end

	always @(*)
	begin
		wide_writeptr = 0;
		wide_writeptr = { i_writeptr, 2'b00 };
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assume(i_cfg_baseaddr == fc_baseaddr);
		assume(i_cfg_memsize  == fc_memsize);

		assume(wide_writeptr >= wide_baseaddr);
		assume(wide_writeptr < wide_baseaddr + wide_memsize);
	end

	always @(*)
	if (i_reset)
		assume(i_cfg_reset_fifo);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset))
	begin
		if ($past(o_fifo_err) || $past(o_wb_cyc && i_wb_err))
		begin
			assume(i_cfg_reset_fifo);
		end
	end


	always @(posedge i_clk)
	if (f_past_valid && $past(i_cfg_reset_fifo) && !i_cfg_reset_fifo)
	begin
		assume($stable(i_cfg_baseaddr));
		assume($stable(i_cfg_memsize));
	end

	always @(*)
	begin
		wide_committed = wide_writeptr - wide_readptr;
		if (i_writeptr < r_readptr)
			wide_committed = wide_committed
					+ { fc_memsize, {(WBLSB){1'b0}} };
		assume(wide_committed <= { fc_memsize, {(WBLSB){1'b0}} });

		wide_end_of_packet = { 1'b0, r_endptr, 2'b00 } + 4;
		if (wide_end_of_packet >= end_of_memory)
			wide_end_of_packet = wide_end_of_packet - wide_memsize;

		// f_wide_pktfill = wide_writeptr - wide_end_of_packet;
		// if (wide_writeptr < wide_end_of_packet)
			// f_wide_pktfill = f_wide_pktfill
					// + { fc_memsize, {(WBLSB){1'b0}} };
	end

	always @(posedge i_clk)
	if (f_past_valid && !i_cfg_reset_fifo && !$past(i_cfg_reset_fifo))
	begin
		assert(end_of_memory == wide_baseaddr + wide_memsize);

		assert(wide_end_of_packet >= wide_baseaddr);
		assert(wide_end_of_packet <  end_of_memory);

		// assert(f_wide_pktfill <= wide_committed);

		if ($stable(r_readptr))
		begin
			assume($past(wide_committed) <= wide_committed);
		end else begin
			assume($past(wide_committed) <= wide_committed - (BUSDW/8));
		end
	end

	always @(posedge i_clk)
	if (f_past_valid && !i_cfg_reset_fifo && !$past(i_cfg_reset_fifo))
		assert($stable(end_of_memory));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone properties
	// {{{

	fwb_master #(
		.AW(AW), .DW(BUSDW), .F_LGDEPTH(F_LGDEPTH)
	) fwb (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		//
		.i_wb_cyc( o_wb_cyc),
		.i_wb_stb( o_wb_stb),
		.i_wb_we(  1'b0 ),
		.i_wb_addr( o_wb_addr),
		.i_wb_data( o_wb_data),
		.i_wb_sel(  o_wb_sel ),
		.i_wb_stall(i_wb_stall),
		.i_wb_ack(  i_wb_ack),
		.i_wb_idata(i_wb_data),
		.i_wb_err(  i_wb_err),
		//
		.f_nreqs(frd_nreqs),
		.f_nacks(frd_nacks),
		.f_outstanding(frd_outstanding)
		// }}}
	);

	always @(*)
	if (!i_reset && o_wb_cyc)
		assert(frd_outstanding == rd_outstanding);

	always @(*)
	if (!i_reset && o_wb_stb)
		assert(rd_outstanding <= (1<<LGPIPE));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_LGMAX = $clog2((MAXLEN*8/BUSDW)+1);

	wire	[F_LGMAX-1:0]	fs_word;
	wire	[12-1:0]	fs_packet;
	reg	[AW+WBLSB:0]	fwb_bytes_requested, fwb_bytes_outstanding,
				fwb_next_addr, fwb_wide_request;

	faxin_master #(
		.DATA_WIDTH(BUSDW),
		.MIN_LENGTH(MINLEN*8/BUSDW),
		.MAX_LENGTH((MAXLEN*8 + BUSDW-1)/BUSDW),
		.WBITS($clog2(BUSDW/8)),
		.LGMX(F_LGMAX)
	) faxin (
		// {{{
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(M_VALID),
		.S_AXIN_READY(1'b1),
		.S_AXIN_DATA(M_DATA),
		.S_AXIN_BYTES(M_BYTES),
		.S_AXIN_LAST(M_LAST),
		.S_AXIN_ABORT(1'b0),
		//
		.f_stream_word(fs_word),
		.f_packets_rcvd(fs_packet)
		// }}}
	);

	always @(*)
	if (!i_reset && M_VALID)
		assert(M_LAST == (return_len == 0));

	// Verify relationship between r_readptr && rd_wb_addr
	// {{{
	always @(*)
	if (i_reset || rd_outstanding == 0)
		fwb_next_addr = { r_readptr, 2'b00 };
	else begin
		fwb_next_addr = { r_readptr, 2'b00 }
					+ { rd_outstanding, {(WBLSB){1'b0}} };
		if (fwb_next_addr >= end_of_memory)
			fwb_next_addr = fwb_next_addr - wide_memsize;
		fwb_next_addr[1:0] = 2'b00;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && rd_state != RD_IDLE
				&& rd_state != RD_SIZE && !o_fifo_err)
	begin
		assert(fwb_next_addr[AW+WBLSB-1:2] == rd_wb_addr);
		assert(r_readptr[WBLSB-3:0] == rd_wb_addr[WBLSB-3:0]);
	end
	// }}}

	// Verify relationship between f_startptr, r_readptr && return_len
	// {{{

	// fwb_bytes_requested
	// {{{
	// These are bytes that have been requested, ackd, and so returned,
	// and may have even been sent across the bus
	always @(*)
	if (i_reset || rd_state == RD_IDLE || rd_state == RD_SIZE
			|| r_readptr[WBLSB-3 +: AW] == f_startptr[WBLSB +: AW])
	begin
		fwb_bytes_requested = 0;
	end else if (r_readptr[WBLSB-3 +: AW] >= f_startptr[WBLSB +: AW])
	begin
		fwb_bytes_requested =
			{ r_readptr[WBLSB-3 +: AW], {(WBLSB){1'b0}} }
				- f_startptr - 4;
	end else begin
		fwb_bytes_requested = wide_memsize
			+ { o_wb_addr, {(WBLSB){1'b0}} } - f_startptr - 4;
	end
	// }}}

	// fwb_wide_request : Packet length rounded up to the last word
	// {{{
	always @(*)
	if (i_reset || rd_pktlen == 0)
		fwb_wide_request = 0;
	else begin
		fwb_wide_request = {r_endptr, 2'b00 } - f_startptr;
		fwb_wide_request[WBLSB-1:0] = 0;
		fwb_wide_request = fwb_wide_request
				+ BUSDW/8 - f_startptr[WBLSB-3:0];
	end
	// }}}

	// fwb_bytes_outstanding : Bytes that have been requested, but not ackd
	// {{{
	// These bytes are those that haven't yet been returned on the bus.
	always @(*)
	if (rd_outstanding == 0)
		fwb_bytes_outstanding = 0;
	else if (!full_return)
	begin
		fwb_bytes_outstanding = BUSDW/8 - rd_wb_addr[WBLSB-3:0];
		fwb_bytes_outstanding = fwb_bytes_requested
				+ { rd_outstanding, {(WBLSB){1'b0}} }
				- (BUSDW/8);
	end else begin
		fwb_bytes_outstanding = { rd_outstanding, {(WBLSB){1'b0}} };
	end
	// }}}

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo
			&& (rd_state == RD_PACKET || rd_state == RD_CLEARBUS)
			&& !o_fifo_err && !dly_check && !dly_fifo_err)
	begin
		assert(fwb_bytes_requested   <= wide_memsize);
		assert(fwb_bytes_outstanding <= wide_memsize);
		assert(fwb_bytes_requested + fwb_bytes_outstanding
						<= wide_memsize);

		assert(fwb_bytes_requested + fwb_bytes_outstanding
				+ return_len >= rd_pktlen);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// (* anyconst *) reg	[AW+WBLSB-1:0]	fc_posn;
	// (* anyconst *) reg	[7:0]		fc_byte;
	//	reg	[BUSDW-1:0]	f_byte_wide;

	// Pick a byte position within a packet.
	// always @(*)
	// if (rd_state == RD_PACKET || rd_state == RD_CLEARBUS)
	//	assume(fc_posn < rd_pktlen);
	//

	// Pick a value to be at that byte.
	// Assume that value gets returned, when i_wb_ack is high
	// {{{

	// ... ??
	// bus_byte =
	// always @(*)
	// if (!i_reset && o_wb_cyc && i_wb_ack &&
	//	assume(bus_byte == fc_byte);
	// }}}

	// *PROVE* that value is set in M_DATA when the byte is sent.
	// {{{
	// generate if (OPT_LITTLE_ENDIAN)
	// begin
	//
	//	always @(*)
	//		f_byte_wide = M_DATA >> (fc_posn[WBLSB-1:0] * 8);
	//	assign	f_byte = f_byte_wide[7:0];
	//
	// end else begin
	//	always @(*)
	//		f_byte_wide = M_DATA << (fc_posn[WBLSB-1:0] * 8);
	//	assign	f_byte = f_byte_wide[BUSDW-8 +: 8];
	// end endgenerate

	// always @(*)
	// if (!i_reset && M_VALID && { fs_word, {(WBLSB){1'b0}} } <= fc_posn
	//		&& fc_posn < { fs_word, {(WBLSB){1'b0}} })
	//	assert(f_byte == fc_byte);
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)	assume(fc_baseaddr == 0);
	always @(*)	assume(fc_memsize == { 1'b1, {(AW-1){1'b0}} });
	// }}}
`endif
// }}}
endmodule
