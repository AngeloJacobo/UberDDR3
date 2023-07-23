////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pktvfifowr.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	The is the first half, the *write* half, of the Virtual Packet
//		FIFO.  Packets enter into here as an AXI network packet stream,
//	and may be aborted at any time up until the end of the packet.
//	Operation works as follows:
//	1. A 32-bit zero (null packet length) is written to memory.
//	2. As a packet arrives, it is written to memory, following the null
//		packet length word.  The packet length is accumulated.
//	3. If the packet is aborted, the pointers are returned to the beginning
//		of step 2, and we start over with the next packet.
//
//		If there's no room for the packet in memory (currently), the
//		incoming network SLAVE path will be stalled.  If it stalls too
//		long, the master will abort the packet.  Similarly, if the
//		memory is empty and the packet currently being written to
//		memory would overflow it, then the packet is aborted internally.
//	4. Once LAST is received, and the beat associated with LAST written to
//		memory, the packet is complete and may no more be aborted.
//	5. A 32-bit null is written to the 32-bit word following the packet.
//	6. The length of the packet is then written to the original packet
//		length position.
//	7. At this point, the FSM moves forward by one packet, and we go back
//		to step two--this time from a new memory location.
//
//	It is understood that packets will not be read until they have been
//	entirely written to memory.
//
// Configuration:
//	i_cfg_reset_fifo
//
//	i_cfg_mem_err
//
//	i_cfg_baseaddr	The first (valid) address of memory.  This is a word
//			address, and must be bus aligned.  (An associated
//			wide_baseaddr, used internally, is a byte address.)
//
//	i_cfg_memsize	The number of words available for writing to memory.
//			This size must be bus aligned.  This number may be
//			as large as the number of words in memory.  This
//			size is unconstrained, but must be greater than zero.
//			(Practically, it must be greater than about 4-5 or so,
//			and is assumed to be greater than (or equal to) a
//			reference to 1500 Bytes.)
//
// Operation:
//	i_readptr	This is the address of the next word to be read
//			from memory.  It is the address of a 32-bit word,
//			and may be the address of a word within a bus word.
//			The bottom two LSB's are not included, and are assumed
//			to be zero.
//
//	o_writeptr	The address of a 32-bit word, where the bottom two
//			address bits are assumed to be zero, that points to
//			a null packet address.  This is our indication, to the
//			read half of the FIFO, of where we are at working
//			through memory.
//
//	S_AXIN_*	An incoming (slave) AXI stream network packet interface.
//			(AXI stream w/ BYTES and ABORT fields.)
//
//	WB		Wishbone bus interface, used to write packets to memory.
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
module	pktvfifowr #(
		// {{{
		parameter	BUSDW = 512,
		parameter	AW = 30-$clog2(BUSDW/8),
		parameter	LGPIPE = 6,
		parameter [0:0]	OPT_LOWPOWER = 1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Control port
		// {{{
		input	wire			i_cfg_reset_fifo, i_cfg_mem_err,
		input	wire	[AW-1:0]	i_cfg_baseaddr,
		input	wire	[AW-1:0]	i_cfg_memsize,
		input	wire	[AW+WBLSB-3:0]	i_readptr,
		output	wire	[AW+WBLSB-3:0]	o_writeptr,
		// output	wire			o_pktwr_stb,
		// }}}
		// Incoming packet
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[BUSDW-1:0]	S_DATA,
		input	wire [$clog2(BUSDW/8)-1:0] S_BYTES,
		input	wire			S_LAST,
		input	wire			S_ABORT,
		// }}}
		// DMA bus interface
		// {{{
		output	reg			o_wb_cyc, o_wb_stb,
		output	wire			o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	reg	[BUSDW-1:0]	o_wb_data,
		output	reg	[BUSDW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		// input wire	[BUSDW-1:0]	i_wb_data,
		input	wire			i_wb_err
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// Local parameters
	// {{{
	localparam	WBLSB = $clog2(BUSDW/8);

	localparam	[2:0]	WR_CLEARPTR = 3'h0,
				WR_PUSH     = 3'h1,
				WR_FLUSH    = 3'h2,
				WR_NULL     = 3'h3,
				WR_LENGTH   = 3'h4,
				WR_CLEARBUS = 3'h5,
				WR_OVERFLOW = 3'h6;
	// }}}

	reg	[AW+WBLSB-1:0]	wide_baseaddr, wide_memsize,
				wide_writeptr, wide_bytes;
	reg	[AW+WBLSB:0]	wide_end_of_memory;
	reg	[31:0]		wide_pktlen;

	// r_writeptr always points to the length word of a packet, minus
	//   the last two bits (which are assumed to be zero, as the length
	//   is guaranteed to be 32b aligned).
	reg	[AW+(WBLSB-2)-1:0]	r_writeptr;

	reg	[AW:0]		end_of_memory;

	reg	[LGPIPE:0]	wr_outstanding;
	reg	[2*BUSDW-1:0]	next_dblwide_data;
	reg	[(2*BUSDW/8)-1:0]	next_dblwide_sel;
	reg	[BUSDW-1:0]	next_wr_data;
	reg	[BUSDW/8-1:0]	next_wr_sel;
	reg	[$clog2(BUSDW/8)-1:0]	wide_words, wide_shift;

	wire			lastack;

	reg	[AW+WBLSB-3:0]	wr_wb_addr;

	reg	[AW+WBLSB:0]	next_wbaddr, next_wbfirst, next_wbnull;
	reg	[AW+WBLSB-1:0]	wr_pktlen;
	reg	[2:0]		wr_state;
	reg			wr_midpkt;

	reg	[AW+WBLSB:0]	wide_mem_fill;
	reg			mem_full, mem_overflow;
	reg			syncd;
	wire	[((WBLSB<3) ? 0 : (WBLSB-3)):0]	dshift;
	reg	r_lastack;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		// Base address and memsize are both bus word aligned
		wide_baseaddr = 0;
		wide_baseaddr = { i_cfg_baseaddr, {(WBLSB){1'b0}} };

		wide_memsize  = 0;
		wide_memsize  = { i_cfg_memsize, {(WBLSB){1'b0}} };

		// Write and read pointers are 32-bit aligned
		wide_writeptr = 0;
		wide_writeptr = { r_writeptr, 2'b00 };
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write incoming packets to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		wide_words = (S_BYTES + 3) >> 2;
		wide_shift = -wide_words;
		wide_shift[$clog2(BUSDW/8)-1:0] = 0;
	end

	// next_wbaddr
	// {{{
	// Full ADDRESS_WIDTH, AW + WBLSB
	always @(*)
	begin
		next_wbaddr = { wr_wb_addr, 2'b00 } + (BUSDW/8);
		if (next_wbaddr[WBLSB +: AW] >= (i_cfg_baseaddr+i_cfg_memsize))
			next_wbaddr = { wr_wb_addr, 2'b00 }
						+ (BUSDW/8) - wide_memsize;
		next_wbaddr[WBLSB-1:0] = { wr_wb_addr[WBLSB-3:0], 2'b00 };
	end
	// }}}

	// next_wbnull
	// {{{
	always @(*)
	begin
		// Points to the length word following the current packet.
		//	Given that writeptr points to the length word of the
		//	current packet, we need to add both the packet length
		//	and the 4-byte length word to get to this location.
		next_wbnull = wide_writeptr + wr_pktlen + 4 + 3;
		next_wbnull[1:0] = 2'b00;
		if (next_wbnull[WBLSB +: AW+1]>=wide_end_of_memory[WBLSB +: AW+1])
			next_wbnull[WBLSB +: AW+1] = next_wbnull[WBLSB +: AW+1]
						- { 1'b0, i_cfg_memsize };
	end
	// }}}

	// next_wbfirst
	// {{{
	// Full byte address
	always @(*)
	begin
		// r_writeptr points to the length word of a packet, so we
		// need something to point us to the first data word of
		// the packet.  That's next_wbfirst.
		next_wbfirst = wide_writeptr + 4;
		next_wbfirst[1:0] = 2'b00;	// Shouldn't need saying
		if (next_wbfirst >= wide_end_of_memory)
			next_wbfirst = { 1'b0, i_cfg_baseaddr, {(WBLSB){1'b0}} };
	end
	// }}}

	// next_dblwide_data, next_dblwide_sel
	// {{{
	generate if (WBLSB < 3)
	begin
		assign	dshift = 0;
	end else begin
		assign	dshift = r_writeptr[WBLSB-3:0] + 1;
	end endgenerate

	generate if (WBLSB == 2)
	begin : NO_ALIGNMENT
		// {{{
		always @(*)
		begin
			next_dblwide_data = {{(BUSDW){1'b0}}, S_DATA };
			next_dblwide_sel={{(BUSDW/8){1'b0}},{(BUSDW/8){1'b1}} };
		end
		// }}}
	end else if (OPT_LITTLE_ENDIAN)
	begin : GEN_LITTLE_ENDIAN_ALIGNMENT
		// {{{
		always @(*)
		if (OPT_LITTLE_ENDIAN)
		begin
			next_dblwide_data = { {(BUSDW){1'b0}}, S_DATA }
						<< (wr_wb_addr[WBLSB-3:0] * 32);
			if (S_BYTES == 0)
				next_dblwide_sel = { {(BUSDW/8){1'b0}},
							{(BUSDW/8){1'b1}} };
			else
				next_dblwide_sel[BUSDW/8-1:0]
					= {(BUSDW/8){1'b1}} >> (4*wide_shift);
			next_dblwide_sel = next_dblwide_sel << (dshift * 4);

			next_dblwide_data[BUSDW-1:0]
				= next_dblwide_data[BUSDW-1:0]	| next_wr_data;

			next_dblwide_sel[BUSDW/8-1:0]
				= next_dblwide_sel[BUSDW/8-1:0]	| next_wr_sel;
		end
		// }}}
	end else begin : GEN_ALIGNMENT
		always @(*)
		begin
			next_dblwide_data = { S_DATA, {(BUSDW){1'b0}} }
						>> (dshift * 32);

			next_dblwide_sel = {(BUSDW/4){1'b0}};
			if (S_BYTES == 0)
				next_dblwide_sel = { {(BUSDW/8){1'b1}},
							{(BUSDW/8){1'b0}} };
			else
				next_dblwide_sel[2*BUSDW/8-1:BUSDW/8]
					= {(BUSDW/8){1'b1}} << (4*wide_shift);
			next_dblwide_sel = next_dblwide_sel >> (dshift * 4);

			next_dblwide_data[BUSDW-1:0]
				= next_dblwide_data[BUSDW-1:0]	| next_wr_data;

			next_dblwide_sel[2*BUSDW/8-1:BUSDW/8]
				= next_dblwide_sel[2*BUSDW/8-1:BUSDW/8]	| next_wr_sel;
		end
	end endgenerate
	// }}}

	// wr_pktlen
	// {{{
	always @(*)
	begin
		wide_bytes = 0;
		wide_bytes[$clog2(BUSDW/8)-1:0] = S_BYTES;
	end

	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err
					|| (wr_state == WR_OVERFLOW))
	begin
		wr_pktlen <= 0;
	end else if (S_ABORT && (!S_VALID || S_READY))
	begin
		wr_pktlen <= 0;
	end else if (S_VALID && S_READY)
	begin
		if (!wr_midpkt)
			wr_pktlen <= (BUSDW/8);
		else if (S_BYTES == 0)
			wr_pktlen <= wr_pktlen + (BUSDW/8);
		else
			wr_pktlen <= wr_pktlen + wide_bytes;
	end

	always @(*)
	begin
		wide_pktlen = 0;
		wide_pktlen[AW+WBLSB-1:0] = wr_pktlen;
	end
	// }}}

	// syncd
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		syncd <= 1'b1;
	else if (S_ABORT && (!S_VALID || S_READY))
		syncd <= 1'b1;
	else if (S_VALID && S_READY)
		syncd <= S_LAST;
	// }}}

	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err
						|| (o_wb_cyc && i_wb_err))
	begin
		// {{{
		o_wb_cyc  <= 0;
		o_wb_stb  <= 0;
		wr_wb_addr <= 0;
		o_wb_data <= 0;
		o_wb_sel  <= 0;
		r_writeptr <= { i_cfg_baseaddr, {(WBLSB-2){1'b0}} };
		wr_state <= WR_CLEARPTR;
		wr_midpkt <= 1'b0;
		// wr_pktstart <= i_cfg_baseaddr;
		// }}}
	end else case(wr_state)
	WR_CLEARPTR: begin
		// {{{
		wr_midpkt <= 1'b0;
		if (!o_wb_stb || !i_wb_stall)
		begin
			// Write a NULL word to the beginning of memory
			o_wb_cyc  <= 1'b1;
			o_wb_stb  <= 1'b1;
			wr_wb_addr <= r_writeptr;
			// r_pktstart <= r_writeptr;
			o_wb_data <= 0;
			if (BUSDW < 64)
			begin
				o_wb_sel <= {(BUSDW/8){1'b1}};
			end else if (OPT_LITTLE_ENDIAN)
			begin
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (4*r_writeptr[WBLSB-3:0]);
			end else begin
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (4*r_writeptr[WBLSB-3:0]);
			end
			wr_state   <= WR_PUSH;
			next_wr_data <= 0;
			next_wr_sel <= 0;
		end end
		// }}}
	WR_PUSH: begin
		// {{{
		if (S_ABORT && (!S_VALID || S_READY))
			wr_midpkt <= 1'b0;

		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;

			if (S_ABORT || !wr_midpkt)
			begin
				wr_wb_addr <= next_wbfirst[AW+WBLSB-1:2];
				wr_midpkt <= 1'b0;
			end else if (o_wb_stb)
				wr_wb_addr <= next_wbaddr[AW+WBLSB-1:2];
		end

		if ((!o_wb_stb || !i_wb_stall) && (wr_midpkt || syncd)
			&& S_VALID && S_READY && !S_ABORT)
		begin
			wr_midpkt <= 1'b1;
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;

			if (BUSDW < 64 || OPT_LITTLE_ENDIAN)
			begin
				{ next_wr_data, o_wb_data} <= next_dblwide_data;
				{ next_wr_sel,  o_wb_sel } <= next_dblwide_sel;
			end else begin
				{ o_wb_data, next_wr_data }<=next_dblwide_data;
				{ o_wb_sel,  next_wr_sel  }<=next_dblwide_sel;
			end

			if (S_LAST)
				wr_state <= WR_FLUSH;
		end else if (mem_overflow)
			wr_state <= WR_OVERFLOW;
		end
		// }}}
	WR_FLUSH: begin
		// {{{
		wr_midpkt <= 1'b1;

		if (!o_wb_stb || !i_wb_stall)
		begin
			if (o_wb_stb)
				wr_wb_addr <= next_wbaddr[AW+WBLSB-1:2];

			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;

			if (BUSDW < 64)
			begin
				o_wb_data   <= {(BUSDW  ){1'b0}};
				o_wb_sel    <= {(BUSDW/8){1'b0}};
			end else begin
				if (!mem_full && next_wr_sel != 0)
					{ o_wb_cyc, o_wb_stb } <= 2'b11;

				o_wb_data   <= next_wr_data;
				o_wb_sel    <= next_wr_sel;
			end
			next_wr_data <= {(BUSDW  ){1'b0}};
			next_wr_sel  <= {(BUSDW/8){1'b0}};

			wr_state <= WR_NULL;
		end end
		// }}}
	WR_NULL: begin // Write a concluding 32-bit NULL word
		// {{{
		wr_midpkt <= 1'b1;
		next_wr_data <= {(BUSDW  ){1'b0}};
		next_wr_sel  <= {(BUSDW/8){1'b0}};

		if (!o_wb_stb || !i_wb_stall)
		begin
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			wr_wb_addr <= next_wbnull[AW+WBLSB-1:2];
			o_wb_data   <= {(BUSDW){1'b0}};
			if (BUSDW < 64)
			begin
				o_wb_sel <= {(BUSDW/8){1'b1}};
			end else if (OPT_LITTLE_ENDIAN)
			begin
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (4*next_wbnull[WBLSB-1:2]);
			end else begin
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (4*next_wbnull[WBLSB-1:2]);
			end
			next_wr_data <= {(BUSDW  ){1'b0}};
			next_wr_sel  <= {(BUSDW/8){1'b0}};

			wr_state <= WR_LENGTH;
		end end
		// }}}
	WR_LENGTH: begin // Write the length word for the packet
		// {{{
		wr_midpkt <= 1'b1;
		next_wr_data <= {(BUSDW  ){1'b0}};
		next_wr_sel  <= {(BUSDW/8){1'b0}};

		if (!o_wb_stb || !i_wb_stall)
		begin
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			wr_wb_addr <= r_writeptr;

			if (!OPT_LOWPOWER || BUSDW < 64)
				o_wb_data   <= {(BUSDW/32){wide_pktlen}};
			else if (OPT_LITTLE_ENDIAN)
				o_wb_data   <= { {(BUSDW-32){1'b0}}, wide_pktlen } << (32*r_writeptr[WBLSB-3:0]);
			else
				o_wb_data   <= { wide_pktlen, {(BUSDW-32){1'b0}} } >> (32*r_writeptr[WBLSB-3:0]);

			if (BUSDW < 64)
			begin
				o_wb_sel <= {(BUSDW/8){1'b1}};
			end else if (OPT_LITTLE_ENDIAN)
			begin
				o_wb_sel <= { {(BUSDW/8-4){1'b0}}, 4'hf }
					<< (r_writeptr[WBLSB-3:0] * 4);
			end else begin
				o_wb_sel <= { 4'hf, {(BUSDW/8-4){1'b0}} }
					>> (r_writeptr[WBLSB-3:0] * 4);
			end

			wr_state <= WR_CLEARBUS;
		end end
		// }}}
	WR_CLEARBUS: begin // Write for last ACK to know the packet was written
		// {{{
		wr_midpkt <= 1'b1;
		next_wr_data <= {(BUSDW  ){1'b0}};
		next_wr_sel  <= {(BUSDW/8){1'b0}};
		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;

			if (OPT_LOWPOWER)
			begin
				o_wb_data <= {(BUSDW  ){1'b0}};
				o_wb_sel  <= {(BUSDW/8){1'b0}};
			end
		end
		if (!o_wb_stb && (wr_outstanding == (i_wb_ack ? 1:0)))
		begin
			wr_state <= WR_PUSH;
			wr_midpkt <= 1'b0;
			r_writeptr <= next_wbnull[AW+WBLSB-1:2];
		end end
		// }}}
	WR_OVERFLOW: begin // No room in memory.  Wait for the pkt to complete
		// {{{
		next_wr_data <= {(BUSDW  ){1'b0}};
		next_wr_sel  <= {(BUSDW/8){1'b0}};
		if (S_VALID && S_READY && S_LAST)
			wr_midpkt <= 1'b0;
		if (S_ABORT && (!S_VALID || S_READY))
			wr_midpkt <= 1'b0;
		if (!o_wb_stb || !i_wb_stall)
		begin
			if (lastack)
				o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end

		if (!wr_midpkt && !o_wb_stb
					&& (wr_outstanding == (i_wb_ack ? 1:0)))
			wr_state <= WR_PUSH;
		end
		// }}}
	default: begin
		// {{{
`ifdef	FORMAL
		assert(0);
`endif
		end
		// }}}
	endcase

	// lastack
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err || !o_wb_cyc)
		r_lastack <= 1;
	else
		r_lastack <= (wr_outstanding + (o_wb_stb && !i_wb_stall ? 1:0)
					<= (i_wb_ack ? 2:1));

	assign	lastack = r_lastack
		//	&& ((wr_outstanding[0] && !o_wb_stb && i_wb_ack)
		//	||(!wr_outstanding[0]
		//		&& (!o_wb_stb || (!i_wb_stall && i_wb_ack))));
		&& (wr_outstanding[0] + (o_wb_stb ? 1:0) == (i_wb_ack ? 1:0));
`ifdef	FORMAL
	// Should always be true when we need to drop CYC, on the cycle
	//   containing the last acknowledgment associated with all of our
	//   requests.
	always @(*)
	if (o_wb_cyc && i_wb_ack)
		assert(lastack == (wr_outstanding + (o_wb_stb ? 1:0)
			<= (i_wb_ack ? 1:0)));
	always @(*)
	if (!i_reset && wr_outstanding == 0 && o_wb_cyc)
	begin
		if (!o_wb_stb)
		begin
			assert(lastack);
		end else if (i_wb_ack && !i_wb_stall)
		begin
			assert(lastack);
		end else begin
			assert(!lastack);
		end
	end
	always @(*) if (o_wb_cyc) assert(r_lastack == (wr_outstanding <= 1));
`endif
	// }}}

	// wr_outstanding
	// {{{
	initial	wr_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_cfg_mem_err || !o_wb_cyc)
		wr_outstanding <= 0;
	else case ({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b10: wr_outstanding <= wr_outstanding + 1;
	2'b01: wr_outstanding <= wr_outstanding - 1;
	default: begin end
	endcase
`ifdef	FORMAL
	always @(*)
	if (!o_wb_stb && wr_outstanding == 0)
		assert(!o_wb_cyc);
`endif
	// }}}

	assign	S_READY = ((wr_state == WR_PUSH)
				&& (!o_wb_stb || !i_wb_stall)
				&& !mem_full && !wr_outstanding[LGPIPE])
			|| (wr_state == WR_OVERFLOW && wr_midpkt);

	assign	o_wb_addr = wr_wb_addr[AW+(WBLSB-2)-1:(WBLSB-2)];
	assign	o_wb_we = 1'b1;
	assign	o_writeptr = r_writeptr;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory fill tracking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
		end_of_memory <= i_cfg_baseaddr + i_cfg_memsize;

	always @(*)
		wide_end_of_memory = { end_of_memory, {(WBLSB){1'b0}} };

	always @(*)
	begin
		// Calculate memory fill in bytes
		wide_mem_fill = ({r_writeptr, 2'b00 }-{ i_readptr, 2'b00 });
		if (r_writeptr < i_readptr)
			wide_mem_fill = wide_mem_fill + wide_memsize;
		// Add two pointer words, 4-bytes each, and round up to the
		//   nearest 4-byte boundary
		wide_mem_fill = wide_mem_fill + 11;
		if (wr_midpkt && wr_state != WR_OVERFLOW)
			wide_mem_fill = wide_mem_fill + wr_pktlen;
		wide_mem_fill[1:0] = 2'b00;
		if (S_VALID && S_READY)
			wide_mem_fill = wide_mem_fill + BUSDW/8;
		// if (o_wb_stb)
		//	wide_mem_fill = wide_mem_fill + BUSDW/8;
		// Make sure we always have room for one more word
		//   since it will take at least one clock cycle for this
		//   to take effect
		wide_mem_fill = wide_mem_fill + (BUSDW/8);
		wide_mem_fill[WBLSB-1:0] = 0;
	end

	always @(posedge i_clk)
	if (i_cfg_reset_fifo)
		mem_full <= 0;
	else
		mem_full <= (wide_mem_fill[WBLSB +: AW+1] >= { 1'b0, i_cfg_memsize });

	// always @(posedge i_clk)
	// if (i_reset || i_cfg_reset_fifo || wr_state != WR_PUSH)
		// mem_overflow <= 1'b0;
	// else
		// mem_overflow <= mem_full && S_VALID;
	always @(*)
		mem_overflow = mem_full && S_VALID;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Count available packets in memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// No longer needed
	// assign	o_pktwr_stb = (wr_state == WR_CLEARBUS && !o_wb_stb)
	//		&& (wr_outstanding == (i_wb_ack ? 1:0));

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, wide_baseaddr, next_wbaddr,
				next_wbnull[AW+WBLSB] };
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
	localparam	F_LGDEPTH = LGPIPE+1;
	reg	f_past_valid;
	reg	[AW+WBLSB-1:0]	wide_readptr;
	wire	[F_LGDEPTH-1:0]	fwr_nreqs, fwr_nacks,
				frd_nreqs, frd_nacks,
				fwr_outstanding, frd_outstanding;
	(* anyconst *)	reg	[AW-1:0]	fc_baseaddr, fc_memsize;
	reg	[AW+WBLSB:0]	wide_committed, f_wide_pktfill;
	reg	[AW:0]		f_end_of_memory;
	wire	[WBLSB-3:0]	f_pkt_alignment;

	localparam	LGMX = 11;
	wire	[LGMX-1:0]	fs_word;
	wire	[12-1:0]	fs_packets;
	wire	[BUSDW/8-1:0]	full_sel;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
	begin
		wide_readptr  = 0;
		wide_readptr  = { i_readptr, 2'b00 };
	end
	////////////////////////////////////////////////////////////////////////
	//
	// Config: Base address, memsize, memfull
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (i_reset)
		assume(i_cfg_reset_fifo);

	always @(posedge i_clk)
	if (i_reset || $past(i_reset))
	begin
		assume(!i_cfg_mem_err);
	end else if ($past(i_cfg_reset_fifo))
	begin
		assume(i_cfg_reset_fifo || !i_cfg_mem_err);
		assume(!$rose(i_cfg_mem_err));
	end else if ($past(i_cfg_mem_err))
		assume(i_cfg_reset_fifo);


	always @(*)
		assert(BUSDW >= 32);

	always @(*)
	begin
		assume({ 1'b0, fc_baseaddr } + { 1'b0, fc_memsize } <= (1<<AW));
		if (BUSDW == 32)
			assume(fc_memsize >= 8);
		else if (BUSDW == 64)
			assume(fc_memsize >= 4);
		else
			assume(fc_memsize >= 2);

		wide_committed = wide_writeptr - wide_readptr;
		if (wide_writeptr < wide_readptr)
			wide_committed = wide_committed
					+ { fc_memsize, {(WBLSB){1'b0}} };

		f_wide_pktfill = wide_writeptr - wide_readptr;
		if (wide_readptr > wide_writeptr)
			f_wide_pktfill = f_wide_pktfill + wide_memsize;
		if ((wr_state != WR_PUSH || wr_midpkt)
						&& wr_state != WR_OVERFLOW)
			f_wide_pktfill = f_wide_pktfill + wr_pktlen;
		if (wr_state != WR_CLEARBUS)
			f_wide_pktfill = f_wide_pktfill + 4;
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assume(i_cfg_baseaddr == fc_baseaddr);
		assume(i_cfg_memsize  == fc_memsize);
		assume(wide_readptr >= wide_baseaddr);
		assume(wide_readptr <  wide_baseaddr + wide_memsize);
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(i_cfg_reset_fifo) && !i_cfg_reset_fifo)
	begin
		assume($stable(i_cfg_baseaddr));
		assume($stable(i_cfg_memsize));
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(i_cfg_reset_fifo))
	begin
		assume(wide_readptr == wide_baseaddr);
	end else if (!i_reset && !i_cfg_reset_fifo && !$past(i_cfg_reset_fifo))
	begin
		assume(wide_readptr <= $past(wide_readptr) + (BUSDW/8));
		if ($past(wide_readptr)+(BUSDW/8) >= wide_baseaddr+wide_memsize)
		begin
			assume((wide_readptr >= $past(wide_readptr))
				|| wide_readptr <= $past(wide_readptr) + (BUSDW/8)
							- wide_memsize);
		end else begin
			assume(wide_readptr >= $past(wide_readptr));
		end

		assert(wide_committed <= wide_memsize);
		assert(mem_full || (f_wide_pktfill <= wide_memsize));
		assert(f_wide_pktfill >= wide_committed);

		if ($past(wide_readptr == wide_writeptr))
			assume($stable(wide_readptr));

		if ($past(wide_readptr) < $past(wide_writeptr))
		begin
			assume($past(wide_readptr) <= wide_readptr);
			assume(wide_readptr <= $past(wide_writeptr));
		end else begin
			assume((wide_readptr >= $past(wide_readptr)
					&& wide_readptr < wide_end_of_memory)
				|| wide_readptr <= $past(wide_writeptr));
		end

		if ($past(o_wb_cyc && i_wb_err))
			assume(i_cfg_mem_err);
	end

	always @(posedge i_clk)
	if (!i_reset && $past(i_reset || i_cfg_reset_fifo) && !i_cfg_reset_fifo)
	begin
		assume(wide_readptr  == wide_baseaddr);
		assert(wide_writeptr == wide_baseaddr);
		assert(wide_committed  == 0);
	end

	// Always need at least 8-bytes of room for two packet pointers.
	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && wr_state != WR_OVERFLOW)
	begin
		assert(wr_pktlen + 8 <= wide_memsize);
		if (wr_pktlen + wide_writeptr < wide_end_of_memory
				&& wr_state != WR_CLEARPTR)
		begin
			if (wr_midpkt)
			assert(1 || { wr_wb_addr, 2'b00 } == wr_pktlen+ wide_writeptr
					+ 4 - (BUSDW/8));
		end
		if (wr_midpkt && wr_state == WR_PUSH && !S_ABORT)
			assert({ fs_word, {(WBLSB){1'b0}} } == wr_pktlen);
	end

	always @(*)
	if (i_cfg_mem_err)
		assume(i_cfg_reset_fifo);

	always @(*)
	if (!i_reset && ((i_cfg_baseaddr == 0) || (i_cfg_memsize == 0)))
		assume(i_cfg_mem_err);

	always @(*)
		f_end_of_memory = i_cfg_baseaddr + i_cfg_memsize;

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assert(f_end_of_memory[AW-1:0] == end_of_memory);
		if (f_end_of_memory[AW])
			assert(f_end_of_memory[AW-1:0] == 0);
	end

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		assert(wide_writeptr >= wide_baseaddr);
		assert(wide_writeptr <  wide_end_of_memory);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packet stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxin_slave #(
		.DATA_WIDTH(BUSDW),
		.MIN_LENGTH(2),
		.MAX_LENGTH(1<<(LGMX-1)),
		.LGMX(LGMX)
	) faxin (
		.S_AXI_ACLK(i_clk),
		.S_AXI_ARESETN(!i_reset),
		.S_AXIN_VALID(S_VALID),
		.S_AXIN_READY(S_READY),
		.S_AXIN_DATA(S_DATA),
		.S_AXIN_BYTES(S_BYTES),
		.S_AXIN_LAST(S_LAST),
		.S_AXIN_ABORT(S_ABORT),
		//
		.f_stream_word(fs_word),
		.f_packets_rcvd(fs_packets)
	);

	always @(posedge i_clk)
	if (!i_reset && !S_ABORT)
		assert(syncd == (fs_word == 0));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// WB
	// {{{

	fwb_master #(
		.AW(AW), .DW(BUSDW), .F_LGDEPTH(F_LGDEPTH)
	) fwb_wr (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		//
		.i_wb_cyc( o_wb_cyc),
		.i_wb_stb( o_wb_stb),
		.i_wb_we(  1'b1 ),
		.i_wb_addr( o_wb_addr),
		.i_wb_data( o_wb_data),
		.i_wb_sel(  o_wb_sel ),
		.i_wb_stall(i_wb_stall),
		.i_wb_ack(  i_wb_ack),
		.i_wb_idata({(BUSDW){1'b0}}),
		.i_wb_err(  i_wb_err),
		//
		.f_nreqs(fwr_nreqs),
		.f_nacks(fwr_nacks),
		.f_outstanding(fwr_outstanding)
		// }}}
	);

	always @(*)
	if (!i_reset && o_wb_cyc)
		assert(wr_outstanding == fwr_outstanding);

	always @(*)
	if (!i_reset && o_wb_stb)
		assert(o_wb_sel != 0);

	generate if (OPT_LITTLE_ENDIAN)
	begin : FGEN_FULL_SELLE
		wire	[2*BUSDW/8-1:0]	fdbl_sel;
		assign	fdbl_sel = { {(BUSDW/8){1'b0}}, {(BUSDW/8){1'b1}} }
						>> (dshift[WBLSB-3:0]*4);

		assign	full_sel = fdbl_sel[2*BUSDW/8-1:BUSDW/8];
	end else begin : FGEN_FULL_SEL
		assign	full_sel = { {(BUSDW/8){1'b1}}, {(BUSDW/8){1'b0}} }
						>> (dshift[WBLSB-3:0]*4);
	end endgenerate

	always @(*)
	if (!i_reset)
	begin
		if (&r_writeptr[WBLSB-3:0])
			assert(next_wr_sel == 0);
		else if (wr_midpkt && wr_state == WR_PUSH && fs_word > 1)
			assert(next_wr_sel == full_sel);	// !!!
	end

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo
				&& (o_wb_stb || wr_state != WR_CLEARPTR))
	begin
		assert(o_wb_addr >= i_cfg_baseaddr);		// !!!
		assert(o_wb_addr < (i_cfg_baseaddr + i_cfg_memsize));
	end

	assign	f_pkt_alignment = r_writeptr + 1;
	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo && o_wb_stb && wr_state == WR_PUSH)
	begin
		if (wr_midpkt && fs_word > 0 && (f_pkt_alignment == 0))
			assert(&o_wb_sel);
	end

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo)
	case(wr_state)
	WR_CLEARPTR:	begin
		assert(!wr_midpkt);
		assert(!o_wb_cyc);
		assert(!o_wb_stb);
		assert(o_wb_addr == 0);
		assert(o_wb_data == 0);
		assert(o_wb_sel  == 0);
		assert(r_writeptr == { i_cfg_baseaddr, {(WBLSB-2){1'b0}} });
		assert(i_readptr == r_writeptr);
		assert(wr_pktlen == 0);
		// assert(fs_word == 0);
		end
	WR_PUSH:	assert(!wr_midpkt || !syncd);
	WR_FLUSH:	begin
			assert(fs_word == 0);
			assert(wr_midpkt);
			end
	WR_NULL:	begin
			assert(fs_word == 0);
			assert(wr_midpkt);
			end
	WR_LENGTH:	begin
			assert(fs_word == 0);
			assert(wr_midpkt);
			end
	WR_CLEARBUS:	begin
			assert(fs_word == 0);
			assert(wr_midpkt);
			end
	WR_OVERFLOW: begin end
	default: assert(0);
	endcase

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo && wr_midpkt && wr_state == WR_PUSH)
	begin
		assert(next_wr_sel == next_dblwide_sel[BUSDW/8-1:0]);
	end

	always @(*)
	if (!i_reset && !i_cfg_reset_fifo
			&& wr_state != WR_PUSH && wr_state != WR_OVERFLOW)
	begin
		assert(wide_committed <= wide_memsize);
		assert(wr_pktlen + 8  <= wide_memsize);
		assert(wide_committed + wr_pktlen + 8 <= wide_memsize);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_packets;

	initial	cvr_packets = 0;
	always @(posedge i_clk)
	if (i_reset || i_cfg_reset_fifo || i_wb_err || i_cfg_mem_err)
		cvr_packets <= 0;
	else if (!cvr_packets[3] && wr_state == WR_CLEARBUS && !o_wb_stb
					&& (wr_outstanding == (i_wb_ack ? 1:0)))
		cvr_packets <= cvr_packets + 1;

	always @(posedge i_clk)
	if (!i_reset && !i_cfg_reset_fifo)
	begin
		cover(cvr_packets == 1);
		cover(cvr_packets == 2);
		cover(cvr_packets == 3);
		//
		cover(wr_state == WR_NULL && mem_full);
		cover(wr_state == WR_LENGTH && mem_full);
		cover(wr_state == WR_CLEARBUS && mem_full);
		cover(wr_state == WR_OVERFLOW);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{

	// always @(*) assume(!mem_full);
	// }}}
`endif
// }}}
endmodule
