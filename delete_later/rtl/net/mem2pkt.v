////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	mem2pkt.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This module is designed to allow a CPU to send packets from
//		a circular buffer region in memory.  To use:
//
//	1. Allocate a region in memory.  Make sure the base address and the
//		size of the region are both word aligned.
//	2. Write this base address and memory size to the controller, followed
//		by a "write address" equal to the base address (at first).
//	3. The memory size available is given by the write address minus the
//		read address, modulo the memory size.
//
//		if (write_address > read_address)
//			space_available = write_address - read_address;
//		else
//			space_available = memsize + write_address - read_address
//
//	4. If there's no space available, you can poll the device and wait for
//		sufficient space to become available, or wait for an interrupt.
//		On an interrupt, the entire memory should be available.
//
//	5. Once you have sufficient memory to send a packet plus its length,
//		write the packet to memory and determine its length:
//
//		if (space_available > size(word) + packet_length)
//			pkt_length = generate_packet(write_address);
//
//	6. Follow the packet with a null pointer
//
//		writeptr[pkt_length / sizeof(word)] = 0
//
//	7. Write the packet length to memory
//
//		*writeptr = pkt_length
//
//	8. Go back to step 3 and repeat.
//
//	An error will be generated if the DMA attempts to access an invalid
//	memory region.  The module will then stop and wait for its memory
//	region to be updated.  Once a valid region is given to it, packets
//	may start flowing into memory again.
//
//	Either a base address of zero or a memory size of zero will disable
//	the module.
//
//	If circular addressing is too cumbersome, you can always:
//	1. Wait for the readptr to equal the writeptr.  The interrupt will be
//		set at this time, so you can also wait for an interrupt.
//	2. Set memsize to zero
//	3. Set the write pointer to the base address
//	4. Restore memsize
//	.. and then start working from the base pointer again.
//
// Registers:
//	 0:	Base address
//			Will be rounded up to the nearest word
//			A base address of zero will turn the packet DMA off
//	 4:	{ERR, Memory size }
//			Will be rounded down to the nearest word size
//			A size of zero will turn the packet DMA off
//			A Wishbone (bus) error will also turn the packet DMA
//			off.  Errors may be cleared and the DMA restarted by
//			writing a new base address or size.
//	 8:	Write pointer (Read/write, controlled by the CPU)
//	12:	Read pointer (Read/write, controlled by CPU)
//			Set to zero on error or when idle.  At all other times,
//			the read pointer will be somewhere between the base
//			address and the base address plus the allocated memory
//			size.
//
//	All addresses must be word aligned--not 32b aligned, but word aligned
//	to whatever the bus size is.  To discover word alignment, write an
//	unaligned word, and see what alignment it is given.
//
// Status:
//	Has not (yet) been attempted in simulation or hardware.  Has also just
//	been rewritten for a pkt data width greater than 32 bits.
//
//	QUESTION: What will happen if the user adjusts the write pointer so that
//		it is inside the (current) read packet?  Will this be caught?
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
`default_nettype	none
// }}}
module	mem2pkt #(
		// {{{
		parameter	DW = 512,
		parameter	AW = 31-$clog2(DW/8),
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter	LGFIFO = 7,
		parameter	PKTDW = 128,
		parameter	BURSTSZ = (1<<(LGFIFO-1))	// In bus words
		// parameter [0:0]	OPT_ABORT_ON_EMPTY = 1'b1,
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Incoming bus (slave) control interface
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[1:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		//
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		// }}}
		// Outgoing bus (master) DMA interface
		// {{{
		output	reg		o_dma_cyc,
		output	reg		o_dma_stb,
		output	wire		o_dma_we,
		output	reg [AW-1:0]	o_dma_addr,
		output	wire [DW-1:0]	o_dma_data,
		output	wire [DW/8-1:0]	o_dma_sel,
		input	wire		i_dma_stall,
		input	wire		i_dma_ack,
		input	wire [DW-1:0]	i_dma_data,
		input	wire		i_dma_err,
		// }}}
		// Outgoing packets
		// {{{
		output	wire				M_AXIN_VALID,
		input	wire				M_AXIN_READY,
		output	wire [PKTDW-1:0]		M_AXIN_DATA,
		output	wire [$clog2(PKTDW/8)-1:0]	M_AXIN_BYTES,
		output	wire 				M_AXIN_LAST,
		output	wire 				M_AXIN_ABORT,
		// }}}
		output	reg		o_int
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[2:0]	S_IDLE      = 3'b000,
				S_LENGTH    = 3'b001,
				S_PKTACTIVE = 3'b010,
				S_PKTPAUSED = 3'b011,
				S_RUNDOWN   = 3'b100;

	localparam	[1:0]	ADR_BASEADDR = 2'b00,
				ADR_SIZE     = 2'b01,
				ADR_WRITEPTR = 2'b10,
				ADR_READPTR  = 2'b11;

	localparam	BLSB = $clog2(DW/8),	// Bus LSB
			LSB = $clog2(DW/32),	// Bits between BLSB & 32b words
			WBLSB=2,
			FULL_LOAD = DW/PKTDW;

	wire	[AW-1:0]		i_bus_addr;
	wire	[AW+LSB-1:0]		i_word_addr;
	wire	[AW+BLSB-1:0]		full_baseaddr,
					full_writeptr, full_readptr;
	wire	[AW+BLSB:0]		full_lastaddr;
	wire	[AW-1:0]		bus_readptr; // bus_writeptr;


	reg			r_err, r_dma_reset, r_validptr;
	reg	[AW-1:0]	r_baseaddr, r_memsize, next_dma_addr;
	reg [AW+LSB-1:0]	r_writeptr, r_readptr;
	reg [AW+LSB:0]		next_rdptr, w_next_rdptr;
	reg	[AW:0]		r_lastaddr;

	wire			w_dma_abort;
	reg			dma_abort;

	reg	[LGFIFO:0]	wb_outstanding;

	reg	[2:0]		rd_state;

	wire			sfifo_reset;
	wire			sfifo_read, sfifo_full, sfifo_empty;
	wire	[DW-1:0]	sfifo_data;
	wire	[LGFIFO:0]	sfifo_fill;

	reg	[LGFIFO:0]	fifo_committed;

	reg	[AW-1:0]	pkt_words;

	reg	[AW+BLSB-1:0]	space_committed;
	reg	[31:0]		i_dma_pktlen;
	reg	[DW-1:0]	wide_pktlen;
	wire			w_invalid_packet;

	reg	[AW-1:0]	w_pkt_words;

	reg			pkd_valid, pkd_last;
	wire			pkd_ready;
	reg	[$clog2(DW/PKTDW):0]	pkd_load;
	reg	[AW+BLSB-1:0]	pkd_len, pkd_remaining;
	reg	[$clog2(PKTDW/8)-1:0]	pkd_bytes;
	reg	[DW-1:0]	pkd_wide;
	wire	[PKTDW-1:0]	pkd_data;

	reg			release_packet;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone control handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_dma_reset, r_baseaddr, r_memsize, r_lastaddr, r_err, r_writeptr
	// {{{
	assign	i_bus_addr  = i_wb_data[AW+BLSB-1:BLSB];
	assign	i_word_addr = i_wb_data[AW+BLSB-1:WBLSB];

	assign	full_baseaddr = { r_baseaddr, {(BLSB){1'b0}} };
	assign	full_lastaddr = { r_lastaddr, {(BLSB){1'b0}} };
	assign	full_writeptr = { r_writeptr, {(WBLSB){1'b0}} };
	assign	full_readptr  = { r_readptr,  {(WBLSB){1'b0}} };
	// assign	bus_writeptr  = full_writeptr[AW+BLSB-1:BLSB];
	assign	bus_readptr   = full_readptr[AW+BLSB-1:BLSB];

	initial	r_dma_reset = 1;
	initial	r_baseaddr  = 0;
	initial	r_memsize   = 0;
	initial	r_lastaddr  = 0;
	initial	r_validptr  = 0;
	always @(posedge i_clk)
	begin
		r_dma_reset <= r_err || (r_baseaddr == 0)||(r_memsize == 0);
		if (full_writeptr < full_baseaddr)
			r_dma_reset <= 1'b1;
		if ({ 1'b0, full_writeptr } >= full_lastaddr)
			r_dma_reset <= 1'b1;
		if (r_lastaddr > (1<<AW))
			r_dma_reset <= 1'b1;

		if (r_dma_reset)
			r_writeptr <= { r_baseaddr, {(LSB){1'b0}} };
		r_validptr <= (r_writeptr[AW+LSB-1:LSB] >= r_baseaddr)
				&& ({ 1'b0, r_writeptr[AW+LSB-1:LSB] } < r_lastaddr);

		if (i_wb_stb && i_wb_we)
		begin
			case(i_wb_addr)
			ADR_BASEADDR: begin
				// {{{
				if (i_wb_sel == 4'hf)
				begin
					r_baseaddr <= i_bus_addr;
					r_lastaddr <= i_bus_addr
						+ r_memsize;
				end else if (i_wb_sel != 0)
				begin
					r_baseaddr <= 0;
					r_lastaddr <= { 1'b0, r_memsize };
				end
				r_dma_reset <= 1'b1;
				r_err <= 0;
				end
				// }}}
			ADR_SIZE: begin
				// {{{
				if (i_wb_sel == 4'hf)
				begin
					r_memsize  <= i_bus_addr;
					r_lastaddr <= r_baseaddr + i_bus_addr;
				end else if (i_wb_sel != 0)
				begin
					r_memsize  <= 0;
					r_lastaddr <= { 1'b0, r_baseaddr };
				end
				r_dma_reset <= 1'b1;
				r_err <= 0;
				end
				// }}}
			ADR_WRITEPTR: begin
				// {{{
				// Word accesses, round down to nearest word
				if (i_wb_sel == 4'hf)
				begin
					r_writeptr <=  i_word_addr;
					r_validptr <= (i_bus_addr >= r_baseaddr)
						&& ({ 1'b0, i_bus_addr } < r_lastaddr);
				end end
				// }}}
			ADR_READPTR: begin end // Read only register
			endcase
		end

		if (o_dma_cyc && i_dma_err)
			r_err <= 1'b1;

		if (release_packet && (r_dma_reset || dma_abort))
			r_dma_reset <= 1'b1;

		if (i_reset)
		begin
			// {{{
			r_dma_reset <= 1'b1;
			r_baseaddr   <= 0;
			r_memsize    <= 0;
			r_lastaddr   <= 0;
			r_err <= 0;
			r_validptr   <= 0;
			// }}}
		end
	end
	// }}}

	// o_wb_data
	// {{{
	initial	o_wb_data = 0;
	always @(posedge i_clk)
	if (i_wb_stb && !i_wb_we)
	begin
		o_wb_data <= 0;
		case(i_wb_addr)
		ADR_BASEADDR:	o_wb_data[AW+BLSB-1:BLSB] <= r_baseaddr;
		ADR_SIZE: begin
				o_wb_data[31] <= r_err;
				o_wb_data[AW+BLSB-1:BLSB] <= r_memsize;
			end
		ADR_WRITEPTR:	o_wb_data[AW+BLSB-1:WBLSB] <= r_writeptr;
		ADR_READPTR:	o_wb_data[AW+BLSB-1:WBLSB] <= r_readptr;
		endcase
	end
	// }}}

	assign	o_wb_stall = 1'b0;

	// o_wb_ack
	// {{{
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb && !o_wb_stall;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read packets from memory into our local buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// 1. Issue a single read, get packet length
	// 2. If packet length is believable, start decomposing the packet
	//	No further reads issue until this read returns
	// 3. Issue additional reads, up to the full packet length
	//	Issue burst of (half FIFO length) reads, whenever the FIFO
	//	(+ outstanding) is less than half full, and the full packet
	//	has no (yet) been read.
	//
	//	First burst will be of the whole FIFO length (up to the
	//	packet length).
	// 4. Read results go into a FIFO
	// 5. FIFO reads go into the decomposition circuit, breaking packets
	//	into 32-bit words
	// 6. 32-bit words (packet length first) go into a pkt2stream interface
	// 7. Then into an ASYNC FIFO (in the network controller)
	//

	// next_dma_addr -- circular buffer addressing
	// {{{
	// We make this slightly more complex by allowing the base address
	// to start on any word boundary, and by allowing the memory size
	// to be anything
	always @(*)
	begin
		next_dma_addr = o_dma_addr + 1;
		if (o_dma_addr + 1 >= r_lastaddr)
			next_dma_addr = r_baseaddr;
	end
	// }}}


	// i_dma_pktlen
	// {{{
	wire	w_pkt_extra;

	generate if (DW == 32)
	begin : SAME_WIDTH
		always @(*)
		begin
			i_dma_pktlen = i_dma_data;
			wide_pktlen  = i_dma_data;
			w_pkt_words  = i_dma_pktlen[31:2]
					+ (|i_dma_pktlen[1:0]) - 1;
		end

		assign	w_pkt_extra  = 1'b0;

	end else begin : FIND_PKT_LEN

		reg	[AW+BLSB:0]	w_pkt_end;
		wire	[LSB-1:0]	w_readptr_plus_one;

		always @(*)
		begin
			wide_pktlen = i_dma_data;
			if (OPT_LITTLE_ENDIAN)
			begin
				wide_pktlen = i_dma_data >> (32*r_readptr[LSB-1:0]);
				i_dma_pktlen = wide_pktlen[31:0];
			end else begin
				wide_pktlen = i_dma_data << (32*r_readptr[LSB-1:0]);
				i_dma_pktlen = wide_pktlen[DW-1:DW-32];
			end

			// Verilator lint_off WIDTH
			w_pkt_end  = i_dma_pktlen - 1
			    + { {(AW){1'b0}}, r_readptr[LSB-1:0], {(WBLSB){1'b0}} };
			// Verilator lint_on  WIDTH

			w_pkt_words = w_pkt_end[AW+BLSB-1:BLSB];
		end

		assign	w_readptr_plus_one = r_readptr[LSB-1:0] + 1;

		assign	w_pkt_extra = !(&r_readptr[LSB-1:0])
			&& (w_pkt_end[LSB-1:0] >= w_readptr_plus_one);


		// Verilator lint_off UNUSED
		wire	unused_pktlen;
		assign	unused_pktlen = &{ 1'b0, w_pkt_end,
					wide_pktlen[DW-1:32] };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	assign	w_invalid_packet = (i_dma_pktlen <= 4)
			|| (|i_dma_pktlen[31:AW+BLSB])
			|| (i_dma_pktlen[AW+BLSB-1:0] >= space_committed);

	// space_committed
	// {{{
	// Units: Bytes
	always @(posedge i_clk)
	if (i_reset || r_dma_reset || !r_validptr)
		space_committed <= 0;
	else if (r_readptr <= r_writeptr)
		// Verilator lint_off WIDTH
		space_committed <= (r_writeptr - r_readptr) << WBLSB;
	else
		space_committed <= ({ r_memsize, {(LSB){1'b0}} }
					+ r_writeptr - r_readptr) << WBLSB;
		// Verilator lint_on  WIDTH
	// }}}

	// fifo_committed
	// {{{
	always @(posedge i_clk)
	if (i_reset || (o_dma_cyc && i_dma_err) || dma_abort || r_dma_reset
			|| r_err)
		fifo_committed <= 0;
	else case({ (o_dma_stb && !i_dma_stall),
			((i_dma_ack && rd_state == S_LENGTH) || sfifo_read) })
	2'b10: fifo_committed <= fifo_committed + 1;
	2'b01: fifo_committed <= fifo_committed - 1;
	default:
		fifo_committed <= sfifo_fill + wb_outstanding;
	endcase

`ifdef	FORMAL
	always @(*)
	if (!i_reset && !r_err && !r_dma_reset)
	begin
		assert(fifo_committed == sfifo_fill + wb_outstanding);
		assert(fifo_committed >= wb_outstanding);
		assert(fifo_committed >= sfifo_fill);
	end

	always @(*)
	if (!i_reset)
		assert(fifo_committed + (o_dma_stb ? 1:0) <= (1<<LGFIFO));
`endif
	// }}}

	initial	rd_state   = S_IDLE;
	initial	o_dma_cyc  = 1'b0;
	initial	o_dma_stb  = 1'b0;
	initial	o_dma_addr = 0;
	always @(posedge i_clk)
	if (i_reset || (o_dma_cyc && i_dma_err))
	begin
		// {{{
		// On a bus error, we fail and come to a halt.  Only a user
		// can reset us.
		rd_state <= S_IDLE;
		o_dma_cyc <= 1'b0;
		o_dma_stb <= 1'b0;
		o_dma_addr <= 0;
		pkt_words  <= 0;
		// }}}
	end else if (r_dma_reset)
	begin // Like reset, save we allow ourselves to restart from r_baseaddr
		// {{{
		rd_state   <= S_IDLE;
		o_dma_cyc  <= 1'b0;
		o_dma_stb  <= 1'b0;
		o_dma_addr <= r_baseaddr;
		pkt_words  <= 0;
		// }}}
	end else if (dma_abort)
	begin // Automatically restart, from r_writeptr instead of r_readptr
		// {{{
		rd_state   <= S_IDLE;
		o_dma_cyc  <= 1'b0;
		o_dma_stb  <= 1'b0;
		o_dma_addr <= r_writeptr[AW+LSB-1:LSB];
		pkt_words  <= 0;
		// }}}
	end else if (!o_dma_stb || !i_dma_stall)
	begin
		o_dma_cyc <= (wb_outstanding
				+ (o_dma_stb ? 1:0) > (i_dma_ack ? 1:0));
		o_dma_stb <= 1'b0;
		if (o_dma_stb)
		begin
			o_dma_addr <= next_dma_addr;
			pkt_words <= pkt_words - 1;
		end

		case(rd_state)
		S_IDLE: begin
			// {{{
			o_dma_stb <= 1'b0;

			pkt_words  <= 0;

			o_dma_addr <= bus_readptr;
			if (r_validptr && r_readptr != r_writeptr
					&& sfifo_empty)
			begin
				o_dma_cyc  <= 1'b1;
				o_dma_stb  <= 1'b1;
				// o_dma_addr <= o_dma_addr;
				rd_state <= S_LENGTH;
			end end
			// }}}
		S_LENGTH: begin
			// {{{
			// o_dma_cyc <= 1'b0;
			// o_dma_stb <= 1'b0;
			if (i_dma_ack)
			begin
				rd_state <= S_PKTACTIVE;
				pkt_words  <= w_pkt_words;
				// Verilator lint_off WIDTH
				if (w_invalid_packet || w_pkt_words == 0)
				begin
					// This is either a packet length error,
					// or the last word in the set.
					//  Quietly reset.
					o_dma_addr <= bus_readptr;
					rd_state <= (w_invalid_packet) ? S_IDLE
							: S_RUNDOWN;
				end
				// Verilator lint_on  WIDTH
			end end
			// }}}
		S_PKTACTIVE: begin // Issue read requests
			// {{{
			if (pkt_words > (o_dma_stb ? 1:0))
			begin
				if (fifo_committed + 1 + (o_dma_stb ? 1:0) >= (1<<LGFIFO))
				begin
					// o_dma_cyc is controlled above
					o_dma_stb <= 0; // Issue nothing more
					rd_state <= S_PKTPAUSED;
				end else begin
					o_dma_cyc <= 1'b1;
					o_dma_stb <= 1'b1;
				end
			end else begin
				rd_state <= S_RUNDOWN;
			end end
			// }}}
		S_PKTPAUSED: begin // FIFO full or nearly so, wait for space
			// {{{
			// Verilator lint_off WIDTH
			if (fifo_committed <= (1<<LGFIFO) - BURSTSZ)
			// Verilator lint_on  WIDTH
			begin
				rd_state <= S_PKTACTIVE;
			end end
			// }}}
		S_RUNDOWN: begin
			// {{{
			o_dma_addr <= w_next_rdptr[AW+LSB-1:LSB];
			if (pkd_remaining == 0)
				rd_state <= S_IDLE;
			end
			// }}}
		default: begin // Return to idle
			// {{{
			o_dma_stb <= 1'b0;

			pkt_words <= 0;
			rd_state <= S_IDLE;
			end
			// }}}
		endcase
	end

	assign	o_dma_we = 1'b1;
	assign	o_dma_data = 0;
	assign	o_dma_sel  = -1;

	// r_readptr, next_rdptr
	// {{{
	always @(*)
	begin
		w_next_rdptr = next_rdptr;
		if (next_rdptr[AW+LSB:LSB] >= r_lastaddr)
			w_next_rdptr[AW+LSB:LSB] = next_rdptr[AW+LSB:LSB]
							- { 1'b0, r_memsize };
	end

	always @(posedge i_clk)
	if (i_reset || (o_dma_cyc && i_dma_err))
	begin
		// {{{
		// HALT, and wait for a new or updated configuration
		r_readptr  <= 0;
		next_rdptr <= 0;
		// }}}
	end else if (r_dma_reset)
	begin
		// {{{
		// A new configuration exists, start from the initial
		// baseaddr
		r_readptr  <= full_baseaddr[AW+BLSB-1:WBLSB];
		next_rdptr <= { 1'b0, full_baseaddr[AW+BLSB-1:WBLSB] };
		// }}}
	end else if (dma_abort)
	begin
		// {{{
		// A user error has occurred.  Restart from r_writeptr,
		// discarding any potential packets that may have existed in
		// memory.
		r_readptr  <= r_writeptr;
		next_rdptr <= { 1'b0, r_writeptr };
		// }}}
	end else if (rd_state == S_LENGTH && i_dma_ack)
	begin
		// We are starting a new packet.
		if (w_invalid_packet)
		begin
			// On an invalid packet length, abandon the packet
			r_readptr  <= r_writeptr;
			next_rdptr <= { 1'b0, r_writeptr };
		end else begin
			// Otherwise record where the end of the packet would be
			// We do nothing for (potential) wrap-around here.
			// (For timing reasons ... as I might imagine them.)
			next_rdptr <= r_readptr + i_dma_pktlen[AW+BLSB-1:WBLSB]
				+ ((|i_dma_pktlen[WBLSB-1:0]) ? 1:0);
		end
	end else if (rd_state == S_RUNDOWN && !o_dma_cyc)
	begin
		r_readptr <= w_next_rdptr[AW+LSB-1:0];
	end
	// }}}

	// wb_outstanding
	// {{{
	initial	wb_outstanding   = 0;
	always @(posedge i_clk)
	if (i_reset || r_dma_reset || !o_dma_cyc || i_dma_err)
	begin
		wb_outstanding   <= 0;
	end else case({ (o_dma_stb && !i_dma_stall), i_dma_ack })
	2'b10: wb_outstanding <= wb_outstanding + 1;
	2'b01: wb_outstanding <= wb_outstanding - 1;
	default: begin end
	endcase
	// }}}

	// o_int
	// {{{
	always @(posedge i_clk)
	if (i_reset || r_dma_reset)
		o_int <= 1'b0;
	else begin
		o_int <= 1'b0;
		if (r_err)
			o_int <= 1'b1;
		if (rd_state == S_IDLE && (r_readptr == r_writeptr))
			o_int <= 1'b1;
	end
	// }}}

	// Are our pointers out of order?
	// {{{
	// FAIL if: (final_size - readptr) < (write_ptr - readptr)
	//
	// That's not quite right, though, since we wrap around a base address.
	//
	// space_committed = (writeptr > readptr) ? writeptr - readptr
	//		else
	//			(lastaddr - readptr) + (writeptr - baseptr)
	//		= (writeptr-readptr + memsz)
	//
	// pkt_used = full_pktlen
	//
	// FAIL IF: pkt_used > mem_authorized
	// }}}

	// dma_abort
	// {{{
	assign	w_dma_abort = r_dma_reset || (o_dma_cyc && i_dma_err)
			|| (pkd_len > space_committed);

	always @(posedge i_clk)
	if (i_reset)
		dma_abort <= 0;
	else if (dma_abort)
		dma_abort <= (pkd_remaining > 0);
	else if (w_dma_abort)
		dma_abort <= release_packet;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Gearbox return
	// {{{

	reg	[DW-1:0]	gearbox_data, gearbox_next;
	reg	[2*DW-1:0]	next_gb_data;
	reg			gearbox_valid, gearbox_primed, gearbox_extra;
	reg	[1:0]		gearbox_last;
	reg	[$clog2(DW/PKTDW)-1:0]	gearbox_addr;

	// gearbox_valid, gearbox_primed
	// {{{
	always @(posedge i_clk)
	if (!i_reset || rd_state == S_IDLE || (o_dma_cyc && i_dma_err))
	begin
		gearbox_valid  <= 1'b0;
		gearbox_primed <= (r_readptr[$clog2(DW/PKTDW)-1:0] != 0);
	end else if (o_dma_cyc && i_dma_ack)
	begin
		gearbox_valid <= gearbox_primed;
		gearbox_primed <= 1'b1;
	end else if (gearbox_valid)
		gearbox_valid <= gearbox_last[0];
	// }}}

	// gearbox_last
	// {{{
	always @(posedge i_clk)
	if (!i_reset || rd_state == S_IDLE || (o_dma_cyc && i_dma_err))
	begin
		gearbox_last  <= 2'b0;
	end else if (o_dma_cyc && i_dma_ack)
	begin
		gearbox_last <= { !gearbox_extra, 1'b1};
		if (rd_state != S_RUNDOWN || wb_outstanding > 1)
			gearbox_last  <= 2'b00;
	end else if (gearbox_valid)
		gearbox_last <= gearbox_last << 1;
	// }}}

	always @(posedge i_clk)
	if (rd_state == S_IDLE)
		gearbox_addr <= r_readptr[$clog2(DW/PKTDW)-1:0]+1;

	always @(posedge i_clk)
	if (rd_state == S_IDLE)
		gearbox_extra <= 1'b0;
	else if (rd_state == S_LENGTH && o_dma_cyc && i_dma_ack)
		gearbox_extra <= w_pkt_extra;

	// gearbox_data, gearbox_next
	// {{{
	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		next_gb_data = { {(DW){1'b0}}, gearbox_next }
			| ({ {(DW){1'b0}}, i_dma_data } << (gearbox_addr*32));
	end else begin
		next_gb_data = { gearbox_next, {(DW){1'b0}} }
				| ({ i_dma_data,{(DW){1'b0}} }
							>> (gearbox_addr*32));
	end

	always @(posedge i_clk)
	if (!i_reset || (o_dma_cyc && i_dma_err))
	begin
		gearbox_data <= 0;
		gearbox_next <= 0;
	end else if (o_dma_cyc && i_dma_ack)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			{ gearbox_next, gearbox_data } <= next_gb_data;
		end else begin
			{ gearbox_data, gearbox_next } <= next_gb_data;
		end
	end else if (gearbox_valid && gearbox_last[0])
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			{ gearbox_next, gearbox_data } <= { {(DW){1'b0}}, gearbox_next };
		end else begin
			{ gearbox_data, gearbox_next } <= { gearbox_next, {(DW){1'b0}} };
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	sfifo_reset = i_reset || dma_abort || r_dma_reset;

	// Synchronous FIFO
	sfifo #(
		.BW(DW), .LGFLEN(LGFIFO)
	) u_pktfifo (
		// {{{
		.i_clk(i_clk), .i_reset(sfifo_reset),
		.i_wr(gearbox_valid),
			.i_data(gearbox_data),
			.o_full(sfifo_full), .o_fill(sfifo_fill),
		.i_rd(sfifo_read), .o_data( sfifo_data ),
			.o_empty(sfifo_empty)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Unpack bus words into stream words
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	sfifo_read = !sfifo_empty && !dma_abort && release_packet
			&& (!pkd_valid || (pkd_ready && pkd_load <= 1));

	// pkd_len, pkd_last
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		pkd_remaining <= 0;
		pkd_len  <= 0;
		pkd_last <= 0;
		pkd_bytes <= 0;
	end else if (!release_packet && (r_dma_reset || dma_abort
					|| rd_state == S_IDLE))
	begin
		pkd_remaining <= 0;
		pkd_len  <= 0;
		pkd_last <= 0;
		pkd_bytes <= 0;
	end else if (rd_state == S_LENGTH)
	begin
		pkd_remaining <= 0;
		pkd_len  <= 0;
		pkd_last <= 0;
		pkd_bytes <= 0;
		if (i_dma_ack && !w_invalid_packet)
		begin
			pkd_len <= i_dma_pktlen[AW+BLSB-1:0];
			pkd_remaining <= i_dma_pktlen[AW+BLSB-1:0];
		end
	end else if (pkd_valid && pkd_ready)
	begin
		pkd_last  <= (pkd_remaining <= (PKTDW/8));
		pkd_bytes <= (pkd_remaining <  (PKTDW/8))
				? pkd_remaining[$clog2(PKTDW/8)-1:0]
				: {($clog2(PKTDW/8)){1'b0}};
		if (pkd_remaining >= (PKTDW/8))
			pkd_remaining <= pkd_remaining - (PKTDW/8);
		else
			pkd_remaining <= 0;
	end
	// }}}

	// pkd_valid, pkd_load (in PKTDW-bit words)
	// {{{
	initial	pkd_valid = 0;
	initial	pkd_load  = 0;
	always @(posedge i_clk)
	begin
		if (i_reset)
		begin
			// {{{
			pkd_valid <= 0;	// == Something is in our register
			pkd_load  <= 0;	// == How many somethings in our reg
			// }}}
		end else if (!release_packet && (r_dma_reset
				|| dma_abort || rd_state == S_IDLE))
		begin
			// {{{
			pkd_valid <= 0;
			pkd_load  <= 0;
			// }}}
		end else if (sfifo_read)
		begin
			// {{{
			pkd_valid <= 1;
			pkd_load <= FULL_LOAD[$clog2(DW/PKTDW):0];
`ifdef	FORMAL
			assert(!dma_abort);
`endif
			// }}}
		end else if ((pkd_valid && pkd_ready)
				|| (dma_abort && (!pkd_valid || pkd_ready)))
		begin
			// {{{
			if (pkd_load > 0)
				pkd_load <= pkd_load - 1;
			pkd_valid <= (pkd_load > 1)||dma_abort;

			if (pkd_remaining <= (PKTDW/8))
			begin // END OF PACKET
				pkd_valid <= 0;
				pkd_load <= 0;
			end
			// }}}
		end

		pkd_load[1:0] <= 2'b00;
	end

`ifdef	FORMAL
	always @(*)
	if (!i_reset)
	begin
		assert(pkd_load <= DW/8);
		assert(pkd_load[1:0] == 2'b00);
	end

	always @(*)
	if (!i_reset && !r_dma_reset && rd_state != S_IDLE)
	begin
		assert(pkd_valid == (pkd_load > 0 && pkd_remaining > 0));
	end
`endif
	// }}}

	// pkd_wide
	// {{{
	always @(posedge i_clk)
	if (sfifo_read)
	begin
		pkd_wide <= sfifo_data;
	end else if (pkd_valid && pkd_ready)
	begin
		// {{{
		if (OPT_LITTLE_ENDIAN)
			pkd_wide <= pkd_wide >> PKTDW;
		else
			pkd_wide <= pkd_wide << PKTDW;
		// }}}
	end
	// }}}

	// pkd_data -- picked off the ending bits of pkd_wide
	// {{{
	generate if (OPT_LITTLE_ENDIAN)
	begin
		assign	pkd_data = pkd_wide[PKTDW-1:0];
	end else begin
		assign	pkd_data = pkd_wide[DW-1:DW-PKTDW];
	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Format for a final output
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Questions:
	// ----------------
	// 1. What should our output format be?
	//	Abortable AXI stream, or AXI (length + data, no last) stream?
	//
	// CHOICE: AXI (length+data, no last) stream
	//
	// 2. Can we ever abort?
	//	- What if we receive a bus error?
	//	- What if the packet buffer can't be kept full at the output?
	//	- What if the user reconfigures the port mid-transaction, and
	//		so we get an r_dma_reset?
	//
	// CHOICE: Complete the stream packet once started.  No ABORTs allowed.
	//
	// 3. How can we guarantee a full packet will always be ready?
	//	and that the network interface will never run dry?
	//	We have enough bandwidth that this shouldn't be an issue
	//	... once we get the FIFO filled and the pkd_ fsm going.
	// 	Can we wait to start transmitting the packet until either
	//	a full packet is in the FIFO and pkd_ fsm, or until the
	//	pkd_ FSM is full and the FIFO is fully charged?
	//
	// CHOICE: Wait til the FIFO has either 1) a full packet within it, or
	//	2) it's half full, before releasing VALID
	//

	initial	release_packet = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		release_packet <= 1'b0;
	else if (!release_packet)
	begin
		if (rd_state == S_RUNDOWN && !o_dma_cyc)
			release_packet <= 1'b1;
		if (pkd_valid && sfifo_fill[LGFIFO-2])
			release_packet <= 1'b1;
		if (!pkd_valid || r_dma_reset || pkd_len > space_committed)
			release_packet <= 1'b0;
	end else if (pkd_remaining == 0)
		release_packet <= 1'b0;

	assign	M_AXIN_VALID = pkd_valid && release_packet;
	assign	pkd_ready    = M_AXIN_READY && release_packet;
	assign	M_AXIN_DATA  = pkd_data;
	assign	M_AXIN_BYTES = pkd_bytes;
	assign	M_AXIN_LAST  = pkd_last;
	assign	M_AXIN_ABORT = 1'b0;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data[31:AW], i_wb_data[1:0],
			full_readptr[BLSB-1:0], sfifo_full, w_next_rdptr[AW+LSB]
			};
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
	// Local declarations
	// {{{
	localparam	FSLV_LGDEPTH = 3;
	localparam	F_LGDEPTH = LGFIFO+1;
	localparam	F_MAXPKT  = (1<<20)-5;
	localparam	F_LGMXPKT = $clog2(F_MAXPKT);

	reg	f_past_valid;
	wire	[FSLV_LGDEPTH-1:0]	fslv_nreqs, fslv_nacks,
					fslv_outstanding;
	wire	[F_LGDEPTH-1:0]		fdma_nreqs, fdma_nacks,
					fdma_outstanding;
	wire	[F_LGMXPKT-1:0]		fpkt_word;
	wire	[11:0]			fpkt_count;
	wire				M_AXIN_LAST;
	wire	[AW+BLSB-1:0]		full_memsize;

	assign	full_memsize = { r_memsize, {(BLSB){1'b0}} };

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing network properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	M_AXIN_LAST = (pkd_remaining <= 4);

	// Stream properties
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!M_AXIN_VALID);
	else if ($past(M_AXIN_VALID && !M_AXIN_READY))
	begin
		assert(M_AXIN_VALID);
		assert($stable(M_AXIN_DATA));
		assert($stable(M_AXIN_LAST));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_slave  #(
		.AW(2), .DW(32)
	) fslv (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb), .i_wb_we(i_wb_we),
			.i_wb_addr(i_wb_addr), .i_wb_data(i_wb_data),
			.i_wb_sel(i_wb_sel),
		.i_wb_ack(o_wb_ack), .i_wb_stall(o_wb_stall),
			.i_wb_idata(o_wb_data), .i_wb_err(1'b0),
		.f_nreqs(fslv_nreqs), .f_nacks(fslv_nacks),
			.f_outstanding(fslv_outstanding)
		// }}}
	);

	always @(*)
	if (i_wb_cyc)
		assert(fslv_outstanding == (o_wb_ack ? 1:0));

	fwb_master  #(
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH)
	) fdma (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(o_dma_cyc), .i_wb_stb(o_dma_stb), .i_wb_we(o_dma_we),
			.i_wb_addr(o_dma_addr), .i_wb_data(o_dma_data),
			.i_wb_sel(o_dma_sel),
		.i_wb_ack(i_dma_ack), .i_wb_stall(i_dma_stall),
			.i_wb_idata(i_dma_data), .i_wb_err(i_dma_err),
		.f_nreqs(fdma_nreqs), .f_nacks(fdma_nacks),
			.f_outstanding(fdma_outstanding)
		// }}}
	);

	always @(*)
	if (o_dma_cyc)
		assert(fdma_outstanding == wb_outstanding);

	always @(*)
	if (!o_dma_stb && fdma_outstanding == 0)
		assert(!o_dma_cyc);

	always @(*)
	if (!i_reset)
	begin
		if (r_baseaddr == 0)
			assert(r_dma_reset);
		if (r_memsize == 0)
			assert(r_dma_reset);
		// if (r_err) assert(r_dma_reset);
	end

	always @(posedge i_clk)
	if (!i_reset)
	begin
		case(rd_state)
		S_IDLE: begin
			// {{{
			if (!r_err && !r_dma_reset)
				assert(!o_dma_cyc && !release_packet);
			end
			// }}}
		S_LENGTH: begin
			// {{{
			assert(o_dma_cyc);
			assert(!release_packet);
			assert(!pkd_valid);
			assert(pkd_load == 0);
			assert(pkd_remaining  == 0);
			assert(fdma_outstanding == (o_dma_stb ? 0:1));
			assert(!dma_abort);
			end
			// }}}
		S_PKTACTIVE:	begin
			// {{{
			assert(pkt_words >= (o_dma_stb ? 1:0));	
			assert(o_dma_cyc || $changed(rd_state));
			assert(pkd_len <= space_committed || dma_abort
					|| w_dma_abort || r_dma_reset);
			if (!r_dma_reset)
				assert(full_memsize >= pkd_len);
			end
			// }}}
		S_PKTPAUSED: begin
			assert(pkt_words > (o_dma_stb ? 1:0));
			assert(pkd_len <= space_committed || dma_abort
					|| w_dma_abort || r_dma_reset);
			if (!r_dma_reset)
				assert(full_memsize >= pkd_len);
			end
		S_RUNDOWN:	begin
			assert(pkt_words == (o_dma_stb ? 1:0));
			assert(!$rose(o_dma_stb));
			// assert(o_dma_cyc || ($changed(rd_state)) || $fell(o_dma_cyc));
			assert(pkd_len <= space_committed || dma_abort
					|| w_dma_abort || r_dma_reset);
			if (!r_dma_reset)
				assert(full_memsize >= pkd_len);
			end
		default: assert(0);
		endcase
	end

	always @(posedge i_clk)
	if (!i_reset && !r_dma_reset && (o_dma_stb || !r_err))
	begin
		assert(o_dma_addr >= r_baseaddr);
		assert(o_dma_addr <  r_lastaddr);

		assert(r_readptr[AW+LSB-1:LSB]  >= r_baseaddr);
		assert(r_readptr[AW+LSB-1:LSB]  <  r_lastaddr);

		assert(w_next_rdptr[AW+LSB-1:LSB] >= r_baseaddr);
		assert(w_next_rdptr[AW+LSB-1:LSB] <  r_lastaddr);
	end

	always @(*)
		assert(r_lastaddr == r_baseaddr + r_memsize);

	always @(*)
	if (!r_dma_reset)
	begin
		assert(r_validptr == (r_writeptr[AW+LSB-1:LSB] >= r_baseaddr
				&& r_writeptr[AW+LSB-1:LSB] < r_lastaddr));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Count data from r_readptr to r_nextptr via pkd_len, pkd_remaining,
	// and pkd_words
	reg	[AW-1:0]	f_total_pkt_words;
	reg	[AW:0]		f_addr, f_lastaddr;
	reg	[AW+LSB:0]	f_lastword;
	reg	[AW+BLSB:0]	f_pkt_end;
	reg	[AW+BLSB-1:0]	f_bytes_sent;
	reg	[BLSB-1:0]	f_lastword_fraction;
	reg	[AW-1:0]	f_words_in_pipe;
	reg	[AW+BLSB-1:0]	f_bytes_in_pipe;
	reg	[AW+LSB-1:0]	f_readptr;

	always @(posedge i_clk)
	if (!i_reset && !r_dma_reset && !dma_abort && rd_state == S_IDLE)
		f_readptr <= r_readptr;

	always @(posedge i_clk)
	if (!i_reset && !r_dma_reset && !dma_abort && !r_err)
	begin
		case(rd_state)
		S_IDLE: begin
				assert(sfifo_fill == 0);
			end
		S_LENGTH:    begin
				assert(f_readptr == r_readptr);
				assert(sfifo_fill == 0);
				assert(wb_outstanding == (o_dma_stb ? 0:1));
			end
		S_PKTACTIVE: assert(f_readptr == r_readptr);
		S_PKTPAUSED: assert(f_readptr == r_readptr);
		S_RUNDOWN: begin end
		default: begin end
		endcase
	end

	always @(*)
	begin
		f_pkt_end  = pkd_len - 1
		    + { {(AW){1'b0}}, f_readptr[LSB-1:0], {(WBLSB){1'b0}} };
		f_total_pkt_words = f_pkt_end[AW+BLSB-1:BLSB] + 1;

		f_bytes_sent = pkd_len - pkd_remaining;

		// Lastword fraction is the number of extra bytes we read
		// by reading words at a time instead of bytes at a time.  As
		// a result, the last word might include more than we want.
		f_lastword_fraction = f_pkt_end[BLSB-1:0] + 1;
		if (f_lastword_fraction != 0)
			f_lastword_fraction = (DW/8) - f_lastword_fraction;

		f_words_in_pipe = pkt_words + wb_outstanding + sfifo_fill;
		// if (rd_state != S_LENGTH && rd_state != S_LENGTH)
		//	f_words_in_pipe = f_words_in_pipe + pkt_words;
		f_bytes_in_pipe = { f_words_in_pipe, {(BLSB){1'b0}} };
		if (f_words_in_pipe > 0)
			f_bytes_in_pipe = f_bytes_in_pipe - f_lastword_fraction;
	end

	always @(*)
	if (!i_reset && !r_dma_reset && !dma_abort && !r_err
			&& rd_state != S_IDLE && rd_state != S_LENGTH)
	begin
		assert(f_words_in_pipe >= pkt_words);
		assert(f_words_in_pipe >= wb_outstanding);
		assert(f_words_in_pipe >= sfifo_fill);

		assert(pkd_len >= pkd_remaining);
		if (pkd_load >= pkd_remaining)
		begin
			assert(f_words_in_pipe == 0);
		end else begin
			assert(f_bytes_in_pipe + pkd_load == pkd_remaining);
		end
	end

	// Track o_dma_addr
	always @(*)
	begin
		f_addr = f_readptr[AW+LSB-1:LSB]
				+ (f_total_pkt_words - pkt_words);
		if (rd_state == S_IDLE)
			f_addr = f_readptr[AW+LSB-1:LSB];
		else if (rd_state == S_LENGTH)
			f_addr = f_readptr[AW+LSB-1:LSB] + (o_dma_stb ? 0:1);

		if (f_addr >= r_lastaddr)
			f_addr = f_addr - r_memsize;

		f_lastword = f_readptr + pkd_len[AW+BLSB-1:WBLSB]
					+ ((|pkd_len[WBLSB-1:0]) ? 1:0);
		if (f_lastword >= { r_lastaddr, {(LSB){1'b0}} })
			f_lastword = f_lastword - { 1'b0, r_memsize, {(LSB){1'b0}} };
		f_lastaddr = f_lastword[AW+LSB-1:LSB];
	end

// END = READPTR * 4 + 0x17068000
	always @(*)
	if (!i_reset && !r_dma_reset && rd_state != S_IDLE)
	begin
		if (rd_state != S_LENGTH)
		begin
			if (next_rdptr < { r_lastaddr, {(LSB){1'b0}} })
			begin
				assert(f_lastword == next_rdptr);
			end else begin
				assert(f_lastword == next_rdptr - { 1'b0, r_memsize, {(LSB){1'b0}} });
			end
		end

		if (rd_state == S_LENGTH)
		begin
			if (o_dma_stb)
			begin
				assert(o_dma_addr == f_readptr[AW+LSB-1:LSB]);
			end else if (f_readptr[AW+LSB-1:LSB] + 1 < r_lastaddr)
			begin
				assert(o_dma_addr == f_readptr[AW+LSB-1:LSB]+1);
			end else begin
				assert(o_dma_addr == r_baseaddr);
			end
		end else if (rd_state == S_RUNDOWN)
		begin
			// assert(o_dma_addr == f_lastaddr);
		end else begin
			assert(o_dma_addr == f_addr);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Never" data checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	FNEVER
	// Given a position in a packet doesn't have a particular value in it,
	// assert that value is not returned.
	//
	// How would we do this?  We'd need to know the return address of every
	// packet
	(* anyconst *)	reg		fnvr_check;
	(* anyconst *)	reg [DW-1:0]	fnvr_data;

	always @(*)
	if (fnvr_check && o_dma_cyc && i_dma_ack)
		assume(i_dma_data != fnvr_data);

	always @(*)
	if (fnvr_check && !sfifo_empty)
		assert(sfifo_data != fnvr_data);

	always @(*)
	if (fnvr_check && !sfifo_empty)
		assert((&fifo_keep) || fifo_last);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Pick a position in a stream, and a byte at that position.  Then
	// prove that, if (fpkt_word == fc_addr), then (M_AXIN_DATA == fc_data).

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
	if (i_reset)
		cvr_packets <= 0;
	else if (M_AXIN_VALID && M_AXIN_READY && M_AXIN_LAST)
		cvr_packets <= cvr_packets + 1;

	always @(*)
	begin
		cover(cvr_packets == 1);
		cover(cvr_packets == 2);
		cover(cvr_packets == 3);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

//	always @(*)
//	begin
//		assume(r_baseaddr[19:0] == 0);
//		assume(r_memsize[19:0] == 0);
//		assume(r_writeptr[LSB-1:0] == 0);
//	end
	// }}}
`endif
// }}}
endmodule
