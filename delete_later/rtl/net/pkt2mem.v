////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pkt2mem.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Dumps incoming network packets to memory.  At this point, only
//		the CPU looks at the memory--but that should be good enough.
//
//	How to operate:
//	1. Find some memory, set the base address and memory size.  These
//		addresses need to be 32-bit aligned--even when using larger
//		bus sizes.
//
//	2. Also, set your read  pointer to the base address.  The memory pointed
//		to by this address will get filled in with the length of the
//		first packet, once such a packet arrives.
//
//	3. Either poll the read pointer address for a non-zero value, or wait
//		for an interrupt to tell you the value at the read pointer
//		address is nonzero.
//
//	4. Read the packet length from the read pointer address.
//		Process packet(length = *readptr, buf =readptr+sizeof(uint32_t),
//			wrap_base = baseaddr, wrap_len = memsize)
//
//		Beware the buffer is circular!  The packet might therefore wrap
//		around the end of your memory buffer!  You may wish to process
//		the packet in chunks:
//
//		chunk_one_size = baseaddr+ memsize - (readptr+ sizeof(uint32_t))
//		if (chunk_one_size >= *readptr)
//			no more chunks follow
//		else
//			chunk_two_size = *readptr - chunk_one_size
//			chunk_two_addr = baseaddr
//
//	5. Once you are done processing the packet, set your readptr address to
//
//		readptr += *readptr;
//		if (readptr >= baseaddr + memsize)
//			readptr -= memsize;
//
//		This is essentially a call to free(), and lets the controller
//		know it has more memory available to put packets into.
//
//	6. Next, read the new packet length from this address.
//		If it is != 0, there's another packet--process as in #4 above.
//		If it is == 0, there are no more packets.  Return to #3 above
//		  to wait for the next packet.
//
//	The network will go into an error condition should it ever receive a
//	bus error while writing to the memory range given to it.  On an error
//	condition, simply adjust the range to something valid and start over.
//
// Registers:
//	 0:	Base address
//			Will be rounded up to the nearest word.  Therefore,
//			this address must be aligned to the bus width.  (Not
//			always the neareset 32-bits.)  A base address of zero
//			will turn the packet DMA off
//	 4:	{ERR, Memory size }
//			As with the base address, this value needs to be aligned
//			to the nearest bus word--which won't always be 32-bits.
//			A size of zero will turn the packet DMA off.  A
//			Wishbone (bus) error will also turn the packet DMA off.
//			Errors may be cleared and the DMA restarted by writing
//			a new base address or size.
//	 8:	Write pointer (read only)
//			Set to zero on error or when idle.  At all other times,
//			the write pointer will be somewhere between the base
//			address and the base address plus the allocated memory
//			size.
//	12:	Read pointer (Read/write, controlled by CPU)
//			This is the CPU's half of the FIFO pointers.  It is
//			primarily used to keep the FIFO from being overrun.
//			Once the CPU finishes reading/processing a packet, it
//			should set this address to the pointer address following
//			the packet.  This way, if a new packet arrives that
//			would overwrite the memory at the read pointer's
//			address, then that packet will be dropped.
//
//			This value will be reset to the base address any time
//			the base address or memory size are updated.
//
//	All addresses must be 32b aligned.
//
// Status:	The formal proof below (was at one time) full and complete.
//		It's only fault was that it didn't track the packet word
//	through the FIFO during induction.  With a more open FIFO model, or
//	the commercial front end, this could be fixed.  This design has not
//	(yet) been tested in either hardware or simulation.
//
//	Since that time, the design has been modified to handle packet widths
//	larger than 32-bits.  No attempt has been made to redo the proof since.
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
module	pkt2mem #(
		// {{{
		parameter	DW = 512,
		parameter	AW = 31-$clog2(DW/8),// Max address width is 2GB
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter	LGFIFO = 7,
		parameter	PKTDW = 128,	// Must be PKTDW <= DW
		parameter	BURSTSZ = (1<<(LGFIFO-1)),
		parameter	LGPIPE = 7	// Allow 128 outstanding beats
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
		// Incoming packets
		// {{{
		input	wire				S_AXIN_VALID,
		output	wire				S_AXIN_READY,
		input	wire [PKTDW-1:0]		S_AXIN_DATA,
		input	wire [$clog2(PKTDW/8)-1:0]	S_AXIN_BYTES,
		input	wire				S_AXIN_LAST,
		input	wire				S_AXIN_ABORT,
		// }}}
		// Outgoing bus (master) DMA interface
		// {{{
		output	reg		o_dma_cyc,
		output	reg		o_dma_stb,
		output	wire		o_dma_we,
		output	reg [AW-1:0]	o_dma_addr,
		output	reg [DW-1:0]	o_dma_data,
		output	reg [DW/8-1:0]	o_dma_sel,
		input	wire		i_dma_stall,
		input	wire		i_dma_ack,
		input	wire [DW-1:0]	i_dma_data,
		input	wire		i_dma_err,
		// }}}
		output	reg		o_int
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[2:0]	S_CLEARPTR  = 3'b000,
				S_IDLE      = 3'b001,
				S_PKTACTIVE = 3'b010,
				S_PKTPAUSED = 3'b011,
				S_NULL      = 3'b100,	
				S_LENGTH    = 3'b101;

	localparam	BLSB = $clog2(DW/8),	// Bus LSB
			LSB = $clog2(DW/32),
			WBLSB = 2;
	localparam	[1:0]	ADR_BASEADDR = 2'b00,
				ADR_SIZE     = 2'b01,
				ADR_WRITEPTR = 2'b10,
				ADR_READPTR  = 2'b11;
	integer			ik;

	reg			r_err, r_dma_reset, r_validptr;
	reg	[AW-1:0]	r_baseaddr, r_memsize, next_dma_addr;
	reg	[AW+LSB-1:0]	r_writeptr, r_readptr, r_newstart;
	reg	[AW:0]		space_available, r_lastaddr;
	reg	[AW+LSB:0]	first_dma_addr;
	reg	[AW+LSB:0]	next_start_addr;

	reg			wfifo_write;
	reg	[3+LSB+(DW/32)+DW-1:0]	wfifo_data;

	reg			pkt_valid, pkt_abort, pkt_midpacket;
	reg	[1:0]		pkt_last;
	reg	[LSB-1:0]	pkt_start;
	reg	[LSB:0]		pkt_addr;
	reg	[(DW/32)-1:0]	pkt_keep;
	reg	[DW-1:0]	pkt_data;
	reg [(PKTDW/32)-1:0]	pkt_nxkp;
	reg	[PKTDW-1:0]	pkt_next;


	reg	[LGPIPE:0]	wb_outstanding;
	reg			wb_pipeline_full, abort_write_packet,
				mem_exhausted;
	wire			mem_full;

	reg	[2:0]		wr_state;
	// reg			mid_packet;
	wire			start_burst;

	reg	[LGFIFO:0]	fifo_pkts;
	reg	[AW+BLSB-1:0]	pkt_length;

	wire			fifo_read, fifo_valid;

	wire			fif_full, fif_empty;
	wire	[LGFIFO:0]	fif_fill;
	wire			fif_abort, fif_last;
	wire	[LSB:0]		fif_addr;
	wire	[DW-1:0]	fif_data;
	wire	[DW/32-1:0]	fif_keep;
	reg	[DW/8-1:0]	fif_sel;


	wire	[AW-1:0]		i_bus_addr;
	wire	[AW+BLSB-WBLSB-1:0]	i_word_addr;
	wire	[AW+BLSB-1:0]		full_baseaddr;
	wire	[AW+BLSB-1:0]		full_writeptr, full_readptr;
	wire	[AW+BLSB:0]		full_lastaddr;
	wire	[AW-1:0]		bus_writeptr, bus_readptr;
	reg				pre_wfifo_write;
	wire				wfifo_last, wfifo_abort;
	reg				r_wfifo_midpacket;
	wire				wfifo_midpacket;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone control handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_dma_reset, r_baseaddr, r_memsize, r_err, r_readptr
	// {{{

	assign	i_bus_addr  = i_wb_data[AW+BLSB-1:BLSB];
	assign	i_word_addr = i_wb_data[AW+BLSB-1:WBLSB];

	assign	full_baseaddr = { r_baseaddr, {(BLSB){1'b0}} };
	assign	full_lastaddr = { r_lastaddr, {(BLSB){1'b0}} };
	assign	full_writeptr = { r_writeptr, {(WBLSB){1'b0}} };
	assign	full_readptr  = { r_readptr,  {(WBLSB){1'b0}} };
	assign	bus_writeptr  = full_writeptr[AW+BLSB-1:BLSB];
	assign	bus_readptr   = full_readptr[AW+BLSB-1:BLSB];

	initial	r_dma_reset = 1;
	initial	r_baseaddr  = 0;
	initial	r_memsize   = 0;
	initial	r_lastaddr  = 0;
	initial	r_validptr  = 0;
	always @(posedge i_clk)
	begin
		// We are in reset following an error, or any time the
		// read pointer is out of bounds.
		// {{{
		r_dma_reset <= r_err || (r_baseaddr == 0)||(r_memsize == 0);
		if (r_readptr[AW+LSB-1:LSB] < r_baseaddr)
			r_dma_reset <= 1'b1;
		if ({ 1'b0,  r_readptr[AW+LSB-1:LSB] } >= r_lastaddr)
			r_dma_reset <= 1'b1;
		if (r_lastaddr >= (1<<AW))
			r_dma_reset <= 1'b1;
		// }}}

		if (r_dma_reset)
			r_readptr <= { r_baseaddr, {(LSB){1'b0}} };
		r_lastaddr <= r_baseaddr + r_memsize;
		r_validptr <= (r_readptr[AW+LSB-1:LSB] >= r_baseaddr)
				&& ({ 1'b0, r_readptr[AW+LSB-1:LSB] } < r_lastaddr );

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

				if (i_wb_sel != 0)
				begin
					r_dma_reset <= 1'b1;
					r_err <= 0;
				end end
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

				if (i_wb_sel != 0)
				begin
				r_dma_reset <= 1'b1;
				r_err <= 0;
				end end
				// }}}
			ADR_WRITEPTR: begin end // Read only register
			ADR_READPTR: begin
				// {{{
				if (i_wb_sel == 4'hf)
				begin
					r_readptr  <= i_word_addr;
					r_validptr <= (i_bus_addr >= r_baseaddr)
						&& ({ 1'b0, i_bus_addr } < r_lastaddr);
				end end
				// }}}
			endcase
		end

		if (o_dma_cyc && i_dma_err)
			r_err <= 1'b1;

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
	if (!OPT_LOWPOWER || (i_wb_stb && !i_wb_we))
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
	// Pack 32-bit-wide packets into bus words
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		pre_wfifo_write = 1'b0;
		if (pkt_valid && pkt_last != 2'b00 && !pkt_abort)
			pre_wfifo_write = 1'b1;
		if (OPT_LITTLE_ENDIAN && pkt_keep[0])
			pre_wfifo_write = 1'b1;
		if (!OPT_LITTLE_ENDIAN && pkt_keep[(DW/32)-1])
			pre_wfifo_write = 1'b1;
	end

	// pkt_midpacket
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		pkt_midpacket <= 1'b0;
	else if (S_AXIN_ABORT && (!S_AXIN_VALID || S_AXIN_READY))
		pkt_midpacket <= 1'b0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		pkt_midpacket <= !S_AXIN_LAST && !S_AXIN_ABORT;
	// }}}

	// pkt_*
	// {{{
	reg	[$clog2(PKTDW/8)-1:0]	s_words;
	reg	[PKTDW/32-1:0]		s_mask;
	reg	[DW+PKTDW-1:0]		next_data_sreg;
	reg	[(DW+PKTDW)/32-1:0]	next_keep_sreg;

	always @(*)
	begin
		s_words = S_AXIN_BYTES + 1;
		s_words = s_words >> 2;

		s_mask = ({ {(PKTDW/32-1){1'b0}}, 1'b1 } << s_words) - 1;
		if (S_AXIN_LAST)
			s_mask = {(PKTDW/32){1'b1}};
	end

	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		next_data_sreg = { {(DW){1'b0}}, pkt_next }
				| { {(DW){1'b0}}, S_AXIN_DATA }
							<< (pkt_addr*32);
		next_keep_sreg = { {(DW/32){1'b0}}, pkt_nxkp }
			| ({ {(DW/32){1'b0}}, s_mask } << pkt_addr);
	end else begin
		next_data_sreg = { pkt_next, {(DW){1'b0}} }
				| { S_AXIN_DATA, {(DW){1'b0}} }
						>> (pkt_addr*32);

		next_keep_sreg = { pkt_nxkp, {(DW/32){1'b0}} }
			| ({ s_mask, {(DW/32){1'b0}} } >> pkt_addr);
	end

	initial	pkt_valid = 0;
	initial	pkt_keep  = 0;
	initial	pkt_data  = 0;
	initial	pkt_addr  = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		pkt_valid <= 0;
		pkt_start <= 1;
		pkt_addr  <= 1;	// First data has position '1' in the word
		pkt_keep  <= 0;
		pkt_data  <= 0;
		pkt_next  <= 0;
		pkt_nxkp  <= 0;
		pkt_last  <= 2'b00;
		// }}}
	end else if (r_dma_reset || (pkt_abort && pkt_midpacket))
	begin
		// {{{
		pkt_valid <= 0;
		pkt_abort <= pkt_midpacket || (S_AXIN_VALID && S_AXIN_READY
					&& !S_AXIN_LAST && !S_AXIN_ABORT);
		pkt_addr  <= 1;
		pkt_start <= 1;

		pkt_keep  <= 0;
		pkt_data  <= 0;
		pkt_next  <= 0;
		pkt_nxkp  <= 0;
		pkt_last  <= 2'b00;
		// }}}
	end else if (S_AXIN_VALID && S_AXIN_READY)
	begin
		// {{{
		pkt_valid <= 1;
		pkt_last  <= 2'b00;

		// Clear on any new word
		// {{{
		if (pkt_last[1]
			|| (OPT_LITTLE_ENDIAN && pkt_keep[0])
			|| (!OPT_LITTLE_ENDIAN && pkt_keep[(DW/32)-1]))
		begin
			pkt_addr <= 0;
			pkt_keep <= 0;
			pkt_data <= 0;
		end
		// }}}

		pkt_addr <= pkt_addr[LSB-1:0] + 1;

		// Add to pkt_data and pkt_keep
		// {{{
		if (OPT_LITTLE_ENDIAN)
		begin
			{ pkt_next, pkt_data } <= next_data_sreg;
			{ pkt_nxkp, pkt_keep } <= next_keep_sreg;
		end else begin
			{ pkt_data, pkt_next } <= next_data_sreg;
			{ pkt_keep, pkt_nxkp } <= next_keep_sreg;
		end
		// }}}

		if (S_AXIN_ABORT)
		begin
			// {{{
			pkt_abort <= 1'b1;
			pkt_addr  <= { 1'b0, pkt_start };
			pkt_keep  <= 0;
			pkt_data  <= 0;
			pkt_last  <= 2'b10;
			// }}}
		end else if (S_AXIN_LAST)
		begin
			// {{{
			pkt_start <= pkt_addr[LSB-1:0]+2;
			pkt_addr  <= pkt_addr[LSB-1:0]+2;
			if (OPT_LITTLE_ENDIAN)
			begin
				pkt_last <= (next_keep_sreg[(PKTDW+DW)/32-1:DW/32-1] != 0) ? 2'b01 : 2'b10;
			end else begin
				pkt_last <= (next_keep_sreg[PKTDW/32-1:0] != 0) ? 2'b01 : 2'b10;
			end
			// }}}
		end
		// }}}
	end else if (pre_wfifo_write)
	begin
		// {{{
		pkt_valid <= !pkt_abort && (pkt_nxkp != 0);
		pkt_abort <= pkt_midpacket;
		pkt_last[0]<= 1'b0;
		pkt_last[1]<= pkt_last[0] && (pkt_nxkp != 0);

		if (OPT_LITTLE_ENDIAN)
		begin
			{ pkt_next, pkt_data }<= { {(DW){1'b0}},   pkt_next };
			{ pkt_nxkp, pkt_keep }<= { {(DW/32){1'b0}},pkt_nxkp };
		end else begin
			{ pkt_data, pkt_next }<= { pkt_next,{(DW   ){1'b0}} };
			{ pkt_keep, pkt_nxkp }<= { pkt_nxkp,{(DW/32){1'b0}} };
		end
		// }}}
	end
	// }}}

	// wfif_*
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		wfifo_write <= 1'b0;
	end else if (pre_wfifo_write
		|| ((pkt_abort || r_dma_reset) && wfifo_midpacket))
	begin
		wfifo_write <= 1'b1;
	end else if (!fif_full)
		wfifo_write <= 0;

	always @(posedge i_clk)
	if (pre_wfifo_write || pkt_abort || r_dma_reset)
	begin
		wfifo_data <= { (pkt_abort || r_dma_reset),pkt_last[1],pkt_addr,
							pkt_keep, pkt_data };
	end

	always @(posedge i_clk)
	if (i_reset)
		r_wfifo_midpacket <= 1'b0;
	else if (wfifo_write)
		r_wfifo_midpacket <= !wfifo_last && !wfifo_abort;

	assign	wfifo_midpacket = r_wfifo_midpacket
			|| (wfifo_write && !wfifo_last && !wfifo_abort);
	assign	wfifo_last  = wfifo_data[DW+(DW/32)+LSB+1];
	assign	wfifo_abort = wfifo_data[DW+(DW/32)+LSB+2];
	// }}}

	assign	S_AXIN_READY = !fif_full || !wfifo_write;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Push data to a (Synchronous) FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	sfifo #(
		.BW(3+LSB+(DW/32)+DW), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b0)
	) u_fifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wr(wfifo_write), .i_data(wfifo_data),
			.o_full(fif_full), .o_fill(fif_fill),
		//
		.i_rd(fifo_read),
		.o_data({ fif_abort, fif_last, fif_addr, fif_keep, fif_data }),
		.o_empty(fif_empty)
		// }}}
	);

	assign	fifo_valid = !fif_empty;
	assign	fifo_read = abort_write_packet || ((wr_state == S_PKTACTIVE)
			&& (!o_dma_stb || !i_dma_stall) && !fif_empty
			&& !wb_pipeline_full && !mem_full);

	// fif_sel, expand fif_keep by swapping every 1'b1 for a 4'hf
	// {{{
	always @(*)
	begin
		fif_sel = 0;
		for(ik=0; ik<DW/32; ik=ik+1)
		if (fif_keep[ik])
			fif_sel[ik*4 +: 4] = 4'hf;

		if (fif_empty)
			fif_sel = 0;
	end
	// }}}

	// fifo_pkts -- count the number of LASTs in the FIFO
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		fifo_pkts <= 0;
	else case({ (wfifo_write && wfifo_last), (fifo_read && fif_last) })
	2'b10:	fifo_pkts <= fifo_pkts + 1;
	2'b01:	fifo_pkts <= fifo_pkts - 1;
	default: begin end
	endcase
	// }}}
	
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Blast packets to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		next_dma_addr = o_dma_addr + 1;
		if (o_dma_addr + 1 >= r_lastaddr)
			next_dma_addr = r_baseaddr;

		first_dma_addr = { 1'b0, r_writeptr } + 1;
		if (first_dma_addr >= { r_lastaddr, {(LSB){1'b0}} })
			first_dma_addr = { 1'b0, r_baseaddr, {(LSB){1'b0}} };

		next_start_addr = 0;
		next_start_addr[AW+LSB:LSB] = r_newstart[AW+LSB-1:LSB]
					+ (fif_addr[LSB] ? 1:0);
		next_start_addr[LSB-1:0] = fif_addr[LSB-1:0];
		if (next_start_addr[AW+LSB:LSB] >= r_lastaddr)
			next_start_addr[AW+LSB:LSB] = r_lastaddr;
	end

	// Verilator lint_off WIDTH
	assign	start_burst = (fifo_valid
				&& (fifo_pkts >0 || fif_fill >= BURSTSZ)
				&& !wb_pipeline_full && !mem_full);
	// Verilator lint_on  WIDTH

	initial	wr_state   = S_IDLE;
	initial	o_dma_cyc  = 1'b0;
	initial	o_dma_stb  = 1'b0;
	initial	o_dma_addr = 0;
	initial	o_dma_data = 0;
	initial	r_writeptr = 0;
	initial	pkt_length = 0;
	always @(posedge i_clk)
	if (i_reset || (o_dma_cyc && i_dma_err))
	begin
		// {{{
		wr_state   <= S_IDLE;
		o_dma_cyc  <= 1'b0;
		o_dma_stb  <= 1'b0;
		o_dma_addr <= 0;
		o_dma_data <= 0;
		r_writeptr <= 0;
		pkt_length <= 0;
		r_newstart <= 0;
		// }}}
	end else if (r_dma_reset)
	begin // Like reset, save we allow ourselves to restart from r_baseaddr
		// {{{
		wr_state   <= S_CLEARPTR;
		o_dma_cyc  <= 1'b0;
		o_dma_stb  <= 1'b0;
		o_dma_addr <= r_baseaddr;
		r_writeptr <= { r_baseaddr, {(BLSB-WBLSB){1'b0}} };
		r_newstart <= { r_baseaddr, {(BLSB-WBLSB){1'b0}} };
		o_dma_data <= 0;
		pkt_length <= 0;
		// }}}
	end else if (abort_write_packet)
	begin
		// {{{
		wr_state   <= S_IDLE;
		o_dma_cyc  <= 1'b0;
		o_dma_stb  <= 1'b0;
		o_dma_addr <= bus_writeptr;
		o_dma_data <= 0;
		pkt_length <= 0;
		r_newstart <= r_writeptr;
		// }}}
	end else if (!o_dma_stb || !i_dma_stall)
	begin
		o_dma_cyc <= o_dma_cyc && (wb_outstanding + (o_dma_stb ? 1:0) > (i_dma_ack ? 1:0));
		o_dma_stb <= 1'b0;
		o_dma_data <= fif_data;
		o_dma_sel  <= fif_sel;

		case(wr_state)
		S_CLEARPTR: begin
			// {{{
			// Clear the write pointer at the beginning of the
			// packet to zero.  This isn't strictly necessary,
			// since the CPU can read our writeptr and know we
			// haven't gone past it, but it is a secondary
			// indication of the packet length, and should allow the
			// CPU to operate on a linked list basis without
			// reading the writeptr as often.
			wr_state   <= S_IDLE;
			o_dma_cyc  <= 1'b1;
			o_dma_stb  <= 1'b1;
			o_dma_addr <= bus_writeptr;
			o_dma_data <= 0;
			r_newstart <= r_writeptr;
			pkt_length <= 0;
			if (LSB == 0)
			begin
				o_dma_sel <= {(DW/8){1'b1}};
			end else if (OPT_LITTLE_ENDIAN)
			begin
				o_dma_sel  <= { {(DW/8-4){1'b0}}, 4'hf } << (4*r_writeptr[LSB-1:0]);
			end else begin
				o_dma_sel  <= { 4'hf, {(DW/8-4){1'b0}} } >> (4*r_writeptr[LSB-1:0]);
			end end
			// }}}
		S_IDLE: begin
			// {{{
			o_dma_stb  <= 1'b0;
			o_dma_addr <= first_dma_addr[AW+LSB-1:LSB];
			// o_dma_data <= fif_data;
			// o_dma_sel  <= fif_sel;
			r_newstart <= r_writeptr;

			pkt_length <= 4;	// Allocate room for the pointer

			if (start_burst)
			begin
				wr_state <= S_PKTACTIVE;
			end end
			// }}}
		S_PKTACTIVE: begin
			// {{{
			if (o_dma_stb)
				o_dma_addr <= next_dma_addr;
			// o_dma_data <= fif_data;
			// o_dma_sel  <= fif_sel;

			if (!fifo_read)
			begin
				o_dma_stb  <= 0;
				// o_dma_addr <= o_dma_addr;
				wr_state   <= S_PKTPAUSED;
				pkt_length <= pkt_length;
			end else begin
				o_dma_cyc <= 1'b1;
				o_dma_stb <= 1'b1;

				r_newstart <= next_start_addr[AW+LSB-1:0];
				// Verilator lint_off WIDTH
				pkt_length <= pkt_length + COUNTONES(fif_keep);
				// Verilator lint_on  WIDTH

				if (fif_last)
					wr_state <= S_NULL;
			end end
			// }}}
		S_PKTPAUSED: begin // Wait to be able to continue again
			// {{{
			o_dma_stb  <= 1'b0;
			o_dma_addr <= o_dma_addr;
			o_dma_data <= fif_data;
			o_dma_sel  <= fif_sel;

			if (start_burst)
			begin
				wr_state <= S_PKTACTIVE;
			end end
			// }}}
		S_NULL: begin // Write the NULL length byte for the next packet
			// {{{
			o_dma_data <= 0;
			if (LSB == 0)
			begin
				o_dma_sel <= {(DW/8){1'b1}};
			end else if (OPT_LITTLE_ENDIAN)
			begin
				o_dma_sel  <= { {(DW/8-4){1'b0}}, 4'hf } << (4*r_newstart[BLSB-WBLSB-1:0]);
			end else begin
				o_dma_sel  <= { 4'hf, {(DW/8-4){1'b0}} } >> (4*r_newstart[BLSB-WBLSB-1:0]);
			end

			if (!mem_full && !wb_pipeline_full)
			begin
				o_dma_cyc <= 1'b1;
				o_dma_stb <= 1'b1;
				o_dma_addr <= r_newstart[AW+LSB-1:LSB];
				wr_state <= S_LENGTH;
				{ o_dma_cyc,  o_dma_stb } <= 2'b11;
			end end
			// }}}
		S_LENGTH: begin // Go back & write the len word for this pkt
			// {{{
			if (!wb_pipeline_full)
			begin
				o_dma_cyc <= 1'b1;
				o_dma_stb <= 1'b1;
			end
			o_dma_addr <= bus_writeptr;
			o_dma_data <= {(DW/32){ {(32-AW-BLSB){1'b0}}, pkt_length}};
			if (LSB == 0)
			begin
				o_dma_sel <= {(DW/8){1'b1}};
			end else if (OPT_LITTLE_ENDIAN)
			begin
				o_dma_sel  <= { {(DW/8-4){1'b0}}, 4'hf } << (4*r_writeptr[LSB-1:0]);
			end else begin
				o_dma_sel  <= { 4'hf, {(DW/8-4){1'b0}} } >> (4*r_writeptr[LSB-1:0]);
			end

			if (!wb_pipeline_full)
			begin
				r_writeptr <= r_newstart;

				wr_state   <= S_IDLE;
				pkt_length <= 0;
			end end
			// }}}
		default: begin // Duplicate S_IDLE
			// {{{
			o_dma_stb <= 1'b0;
			o_dma_addr <= bus_writeptr;
			r_newstart <= r_writeptr;
			o_dma_data <= fif_data;

			pkt_length <= 0;
			wr_state <= S_IDLE;
			end
			// }}}
		endcase
	end

	// wb_outstanding, wb_pipeline_full
	// {{{
	localparam	WBLIMIT = (1<<LGPIPE)-2;
	initial	wb_outstanding   = 0;
	initial	wb_pipeline_full = 0;
	always @(posedge i_clk)
	if (i_reset || r_dma_reset || !o_dma_cyc || i_dma_err)
			// || (fifo_valid && fif_abort && wr_state < S_NULL))
	begin
		// {{{
		wb_outstanding   <= 0;
		wb_pipeline_full <= 0;
		// }}}
	end else case({ (o_dma_stb && !i_dma_stall), i_dma_ack })
	2'b10: begin
		wb_outstanding <= wb_outstanding + 1;
		wb_pipeline_full <= (wb_outstanding >= WBLIMIT-1);
		end
	2'b01: begin
		wb_outstanding <= wb_outstanding - 1;
		wb_pipeline_full <= (wb_outstanding > WBLIMIT);
		end
	default: begin end
	endcase
	// }}}

	assign	o_dma_we = 1'b1;

	// space_available
	// {{{
	always @(posedge i_clk)
	begin
		if (r_dma_reset || r_readptr == r_writeptr)
			space_available <= { 1'b0, r_memsize };
		else if (!r_validptr)
			space_available <= 0;
		else if (r_readptr > r_writeptr)
			// Verilator lint_off WIDTH
			space_available <= (r_readptr - r_writeptr) >> (BLSB-WBLSB);
		else
			space_available <= r_memsize
				+ ((r_readptr - r_writeptr) >> (BLSB-WBLSB));
			// Verilator lint_on  WIDTH

		mem_exhausted <= pkt_length[AW+BLSB-1:BLSB]
				+ (|pkt_length[BLSB-1:0] ? 1:0) + 2 > r_memsize;
	end
	// }}}

	assign	mem_full = pkt_length[AW+BLSB-1:BLSB] + 2 > space_available;

	// abort_write_packet
	// {{{
	always @(posedge i_clk)
	if (i_reset || r_dma_reset)
		abort_write_packet <= 0;
	else if (abort_write_packet)
	begin
		if (fifo_valid && fifo_read && (fif_last || fif_abort))
			abort_write_packet <= 0;
	end else if (mem_exhausted || (o_dma_cyc && i_dma_err))
		abort_write_packet <= 1;
	// }}}

	// o_int
	// {{{
	always @(posedge i_clk)
	if (i_reset || r_dma_reset)
		o_int <= 0;
	else
		o_int <= (r_readptr != r_writeptr) || r_err;
	// }}}

	// }}}

	function automatic [$clog2(DW/32):0] COUNTONES(input [(DW/32)-1:0] kp);
		integer	ck;
		reg	[$clog2(DW/32):0] cnt;
	begin
		cnt=0;
		for(ck=0; ck<(DW/32); ck=ck+1)
			if (kp[ck])
				cnt=cnt+1;
		COUNTONES = cnt;
	end endfunction

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_dma_data, i_wb_data,
			full_readptr[5:0], bus_readptr,
			full_baseaddr, full_writeptr, full_lastaddr };
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
`ifdef	BMC
`define	BMC_ASSERT	assert
`else
`define	BMC_ASSERT	assume
`endif
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
	begin
		assume(i_reset);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming network stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam	F_MAXPKT = (1<<20)-5;	// An arbitrary number
	localparam	F_LGMXPKT = $clog2(F_MAXPKT);

	wire	[F_LGMXPKT-1:0]	fnet_word;
	wire	[12-1:0]	fnet_packets;

	faxin_slave #(
		.DATA_WIDTH(32), .MAX_LENGTH(F_MAXPKT), .MIN_LENGTH(5)
	) fnet (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA( S_AXIN_DATA),
		.S_AXIN_LAST( S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		//
		.f_stream_word(fnet_word),
		.f_packets_rcvd(fnet_packets)
		// }}}
	);

/*
	always @(posedge i_clk)
	if (fnet_word  == 0 && !S_AXIN_ABORT)
	begin
		assert(pkt_keep == 0);
		assert(pkt_addr == 0);
	end
*/
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_LGDEPTH = LGPIPE+1;
	wire	[1:0]		fwb_nreqs,  fwb_nacks,  fwb_outstanding;
	wire	[F_LGDEPTH-1:0]	fdma_nreqs, fdma_nacks, fdma_outstanding;

	fwb_slave #(
		.DW(32), .AW(2), .F_LGDEPTH(2)
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb), .i_wb_we(i_wb_we),
			.i_wb_addr(i_wb_addr), .i_wb_data(i_wb_data),
			.i_wb_sel(i_wb_sel),
		.i_wb_stall(o_wb_stall), .i_wb_ack(o_wb_ack),
			.i_wb_data(o_wb_data), .i_wb_err(1'b0),
		//
		.f_nreqs(fwb_nreqs), .f_nacks(fwb_nacks),
			.f_outstanding(fwb_outstanding)
		// }}}
	);

	always @(*)
	if (i_wb_cyc)
		assert(fwb_outstanding == (o_wb_ack ? 1:0));


	fwb_master #(
		.DW(DW), .AW(AW), .F_LGDEPTH(F_LGDEPTH)
	) fdma (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(o_dma_cyc), .i_wb_stb(o_dma_stb), .i_wb_we(o_dma_we),
			.i_wb_addr(o_dma_addr), .i_wb_data(o_dma_data),
			.i_wb_sel(o_dma_sel),
		.i_wb_stall(i_dma_stall), .i_wb_ack(i_dma_ack),
			.i_wb_idata(i_dma_data), .i_wb_err(i_dma_err),
		//
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
	if(o_dma_cyc)
	begin
		assert(wb_pipeline_full == (wb_outstanding >= WBLIMIT));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	case(wr_state)
	S_CLEARPTR:	begin end
	S_IDLE:		begin end
	S_PKTACTIVE:	begin end
	S_PKTPAUSED:	begin end
	S_NULL:		begin end
	S_LENGTH:	begin end
	default: assert(0);
	endcase

	always @(posedge i_clk)
	if (!i_reset && !r_dma_reset)
		assert(pkt_length < (r_memsize << BLSB));

/*
	always @(posedge i_clk)
	if (!i_reset && $past(fifo_read && !fifo_empty && !i_reset))
	begin
		if ($past(o_dma_cyc && i_dma_err))
		begin
			assert(r_err);
			if ($past(!fif_abort && !fif_last))
				assert(abort_write_packet);
		end else if ($past(fif_abort || abort_write_packet || r_dma_reset))
		begin
			assert(wr_state == S_IDLE);
			assert(!o_dma_stb);
			if ($past(!fif_abort && !fif_last))
				assert(abort_write_packet);
		end else begin
			assert(o_dma_cyc);
			assert(o_dma_stb);
			assert(o_dma_data == $past(fif_data));

			if ($past(fif_last))
				assert(wr_state == S_NULL);
			else
				assert(wr_state == S_PKTACTIVE);
		end
	end
*/

	always @(*)
	if (!i_reset && !r_dma_reset && !r_err)
	begin
		assert(o_dma_addr >= r_baseaddr);
		assert({ 1'b0, o_dma_addr } < r_lastaddr);

		assert({ r_writeptr } >= { r_baseaddr, {(LSB){1'b0}} });
		assert({ 1'b0, r_writeptr } < { r_lastaddr, {(LSB){1'b0}} });
	end

	always @(*)
		assert(r_lastaddr == r_baseaddr + r_memsize);

	always @(*)
	if (!r_dma_reset)
	begin
		assert(r_validptr==((r_readptr >= { r_baseaddr, {(LSB){1'b0}} })
				&&(r_readptr < { r_lastaddr, {(LSB){1'b0}} })));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	FNVR_CHECK
	(* anyconst *)	reg			fnvr_abort, fc_check;
	(* anyconst *)	reg	[F_LGMXPKT-1:0]	fc_pktaddr;
	(* anyconst *)	reg	[8-1:0]		fc_pktdata;
	reg	[AW-1:0]			f_run_start;
	// wire	[F_LGMXPKT-1:0]	fpkt_word;
	reg	[F_LGMXPKT-1:0]	ffifo_word, fdma_word;
	reg	[AW:0]		fdma_addr;

	always @(*)
	if (fnvr_abort)
		assume(!S_AXIN_ABORT);

	// Contract assumption: assume the given address is valid
	always @(*)
	if (fc_check && fnet_word== fc_pktaddr)
		assume(!S_AXIN_VALID || S_AXIN_DATA == fc_pktdata);

	always @(*)
	if (fc_check && fnet_word < fc_pktaddr)
		assume(!S_AXIN_VALID || !S_AXIN_LAST || S_AXIN_ABORT);

	// Verify pkt_* via contract
	// {{{
	always @(*)
	if (!i_reset && fc_check
		&& fnet_word[F_LGMXPKT-1:LSB] == fc_pktaddr[F_LGMXPKT-1:LSB])
	begin
		// if (fnet_word[$clog2(DW)-1:0] == 0)
		if (fnet_word > fc_pktaddr)
		begin
			integer ik;

			for(ik=0; ik<DW/8-1; ik=ik+1)
			if(ik == fc_pktaddr[LSB-1:0])
			begin
				assert(pkt_keep[DW/8-2-ik]);
				assert(pkt_data[DW-16-(ik *8) +: 8]==fc_pktdata);
			end
		end
	end
	// }}}

	// Verify wfifo_* via contract
	// {{{
	always @(*)
	if (!i_reset && wfifo_write && fc_check
		&& fnet_word[F_LGMXPKT-1:LSB] ==fc_pktaddr[F_LGMXPKT-1:LSB] + 1)
	begin
		integer ik;

		for(ik=0; ik<DW/8-1; ik=ik+1)
		if(ik == fc_pktaddr[LSB-1:0])
		begin
			assert(wfifo_data[DW + DW/8-1-ik]);
			assert(wfifo_data[DW-8-(ik *8) +: 8]==fc_pktdata);
		end
	end
	// }}}

	// Re-ASSUME the value when reading from the FIFO
	// {{{
	// Count FIFO output words
	initial	ffifo_word = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ffifo_word <= 0;
	end else if (!fifo_empty && fifo_read)
	begin
		if (fif_last || fifo_abort)
			ffifo_word <= 0;
		else
			ffifo_word <= ffifo_word + COUNTONES(fif_keep);
	end

	always @(*)
	if (!i_reset && fc_check)
		`BMC_ASSERT(ffifo_word < F_MAXPKT);

	// Prior to FIFO last, keep must be true
	always @(*)
	if (!i_reset && fc_check && !fifo_empty && !fif_last && !fif_abort)
		`BMC_ASSERT(&fif_keep);

	// If fc_check, then we can't end prior to fc_pktaddr
	always @(*)
	if (!i_reset && !fifo_empty && fc_check
			&& ffifo_word + COUNTONES(fif_keep) < fc_pktaddr)
		`BMC_ASSERT(fif_abort || !fif_last);

	// Now verify the data on the output
	always @(*)
	if (!i_reset && !fifo_empty && fc_check && !fif_abort
			&& ffifo_word[F_LGMXPKT:LSB]==fc_pktaddr[F_LGMXPKT:LSB])
	begin
		integer ik;

		for(ik=0; ik<DW/8; ik=ik+1)
		if(ik == fc_pktaddr[LSB-1:0])
		begin
			`BMC_ASSERT(fif_keep[DW/8-1-ik]);
			`BMC_ASSERT(fifo_data[DW-8-(ik *8) +: 8]==fc_pktdata);
		end
	end

	always @(*)
	if (!i_reset)
		assert(ffifo_word[LSB-1:0] == 0);
	// }}}

	// Now, start counting output words from the DMA
	// {{{
	always @(posedge i_clk)
	if (i_reset || (o_dma_cyc && i_dma_err)|| r_dma_reset
			|| abort_write_packet
			||(fifo_valid && fif_abort && wr_state< S_NULL))
	begin
		fdma_word <= 0;
	end else if (!o_dma_stb || !i_dma_stall)
	begin
		if (wr_state == S_IDLE)
		begin
			fdma_word <= 0;
			assert(ffifo_word == 0);
			f_run_start <= r_writeptr;
		end else if (o_dma_stb)
			fdma_word <= fdma_word + (DW/8);
	end

	always @(*)
	if (!i_reset && !r_err && !r_dma_reset && !abort_write_packet)
	begin
		if (wr_state == S_IDLE || wr_state == S_NULL
				|| wr_state == S_LENGTH)
			assert(ffifo_word == 0);
	end
	// }}}

	// Verify the two counters match
	// {{{
	always @(*)
	if (!i_reset && fc_check && !r_dma_reset && !abort_write_packet
			&& wr_state != S_IDLE && wr_state < S_NULL)
	begin
		assert(ffifo_word == (o_dma_stb ? (DW/8) : 0) + fdma_word);
	end
	// }}}

	// fdma_addr -- double check o_dma_addr against the packet position
	// {{{
	always @(*)
	begin
		fdma_addr = f_run_start+(fdma_word  >> LSB) + (o_dma_stb ? 1:0);
		if (fdma_addr >= r_lastaddr)
			fdma_addr = fdma_addr - r_memsize;
	end

	always @(*)
	if (!i_reset && fc_check && wr_state != S_IDLE && wr_state < S_NULL && !r_dma_reset)
	begin
		if (o_dma_stb)
			assert(ffifo_word > 0);
		assert(o_dma_addr == fdma_addr);
		assert(f_run_start >= r_baseaddr);
		assert(f_run_start < r_lastaddr);
		assert(r_writeptr == f_run_start);
	end

	// }}}

	// Pkts mustbe less than r_memsize, or abort_write_packet must be set
	// {{{
	// It is possible that the user will adjust r_readptr along the way in
	// an inappropriate manner.  Until we assume this never happens, the
	// following won't work
	//
	// always @(*)
	// if (!i_reset && !r_err && !abort_write_packet && !r_dma_reset
	//		&& (wr_state > S_IDLE && wr_state < S_NULL))
	//	assert(fdma_word < ({ r_memsize, {(LSB){1'b0}} }));
	// }}}
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *) reg	fcvr_different;
	reg	[3:0]	cvr_packets;

	initial	cvr_packets = 0;
	always @(posedge i_clk)
	if (i_reset || abort_write_packet || r_dma_reset)
		cvr_packets <= 0;
	else if ((!o_dma_stb || !i_dma_stall) && wr_state == S_LENGTH)
		cvr_packets <= cvr_packets + 1;

	always @(posedge i_clk)
	if (fcvr_different && $past(S_AXIN_VALID && S_AXIN_READY))
		assume($changed(S_AXIN_DATA));

	always @(posedge i_clk)
	if (fcvr_different)
	begin
		cover(cvr_packets == 1);
		cover(cvr_packets == 2);
		cover(cvr_packets == 3);
		cover(cvr_packets == 4);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

/*
	always @(*)
	if (!i_reset && !fifo_empty && { fif_abort, fif_last } == 2'b00)
		assume(&fif_keep);

	always  @(*)
	if (!i_reset && !fif_empty && !fifo_abort)
	case(fif_keep)
	// 4'b0000: begin end
	4'b1000: begin end
	4'b1100: begin end
	4'b1110: begin end
	4'b1111: begin end
	default: assume(0);
	endcase
*/

	// Pkts mustbe less than r_memsize, or abort_write_packet must be set
	// {{{
	// It is possible that the user will adjust r_readptr along the way in
	// an inappropriate manner.  Until we assume this never happens, the
	// following will need to be assumed rather than asserted.  Otherwise
	// ... induction fails after the packet wraps around memory more than
	// once.
	//
//	always @(*)
//	if (!i_reset && !r_err && !abort_write_packet && !r_dma_reset
//			&& (wr_state > S_IDLE && wr_state < S_NULL))
//		assume(fdma_word < ({ r_memsize, {(LSB){1'b0}} }));
	// }}}


	// }}}
`endif
// }}}
endmodule
