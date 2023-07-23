////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ufifo.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A synchronous data FIFO, designed for supporting the Wishbone
//		UART.  Particular features include the ability to read and
//	write on the same clock, while maintaining the correct output FIFO
//	parameters.  Two versions of the FIFO exist within this file, separated
//	by the RXFIFO parameter's value.  One, where RXFIFO = 1, produces status
//	values appropriate for reading and checking a read FIFO from logic,
//	whereas the RXFIFO = 0 applies to writing to the FIFO from bus logic
//	and reading it automatically any time the transmit UART is idle.
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
// }}}
module ufifo #(
		// {{{
		parameter	BW=8,	// Byte/data width
		parameter [3:0]	LGFLEN=4,
		parameter [0:0]	RXFIFO=1'b1,
		localparam	FLEN=(1<<LGFLEN)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		input	wire		i_wr,
		input	wire [(BW-1):0]	i_data,
		output	wire		o_empty_n, // True if something is in FIFO
		input	wire		i_rd,
		output	wire [(BW-1):0]	o_data,
		output	wire	[15:0]	o_status,
		output	wire		o_err
		// }}}
	);

	// Signal declarations
	// {{{
	reg	[(BW-1):0]	fifo[0:(FLEN-1)];
	reg	[(BW-1):0]	r_data, last_write;
	reg	[(LGFLEN-1):0]	wr_addr, rd_addr, r_next;
	reg			will_overflow, will_underflow;
	reg			osrc;

	wire	[(LGFLEN-1):0]	w_waddr_plus_one, w_waddr_plus_two;
	wire			w_write, w_read;
	reg	[(LGFLEN-1):0]	r_fill;
	wire	[3:0]		lglen;
	wire			w_half_full;
	reg	[9:0]		w_fill;
	// }}}

	assign	w_write = (i_wr && (!will_overflow || i_rd));
	assign	w_read  = (i_rd && o_empty_n);

	assign	w_waddr_plus_two = wr_addr + 2;
	assign	w_waddr_plus_one = wr_addr + 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Write half
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// will_overflow
	// {{{
	initial	will_overflow = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		will_overflow <= 1'b0;
	else if (i_rd)
		will_overflow <= (will_overflow)&&(i_wr);
	else if (w_write)
		will_overflow <= (will_overflow)||(w_waddr_plus_two == rd_addr);
	else if (w_waddr_plus_one == rd_addr)
		will_overflow <= 1'b1;
	// }}}

	// wr_addr
	// {{{
	initial	wr_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		wr_addr <= { (LGFLEN){1'b0} };
	else if (w_write)
		wr_addr <= w_waddr_plus_one;
	// }}}

	// Write to the FIFO
	// {{{
	always @(posedge i_clk)
	if (w_write) // Write our new value regardless--on overflow or not
		fifo[wr_addr] <= i_data;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read half
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Notes
	// {{{
	//	Following a read, the next sample will be available on the
	//	next clock
	//	Clock	ReadCMD	ReadAddr	Output
	//	0	0	0		fifo[0]
	//	1	1	0		fifo[0]
	//	2	0	1		fifo[1]
	//	3	0	1		fifo[1]
	//	4	1	1		fifo[1]
	//	5	1	2		fifo[2]
	//	6	0	3		fifo[3]
	//	7	0	3		fifo[3]
	// }}}

	// will_underflow
	// {{{
	initial	will_underflow = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		will_underflow <= 1'b1;
	else if (i_wr)
		will_underflow <= 1'b0;
	else if (w_read)
		will_underflow <= (will_underflow)||(r_next == wr_addr);
	// }}}

	// rd_addr, r_next
	// {{{
	// Don't report FIFO underflow errors.  These'll be caught elsewhere
	// in the system, and the logic below makes it hard to reset them.
	// We'll still report FIFO overflow, however.
	//
	initial	rd_addr = 0;
	initial	r_next  = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		rd_addr <= 0;
		r_next  <= 1;
	end else if (w_read)
	begin
		rd_addr <= rd_addr + 1;
		r_next  <= rd_addr + 2;
	end
	// }}}

	// Read from the FIFO
	// {{{
	always @(posedge i_clk)
	if (w_read)
		r_data <= fifo[r_next[LGFLEN-1:0]];
	// }}}

	// last_write -- for bypassing the memory read
	// {{{
	always @(posedge i_clk)
	if (i_wr && (!o_empty_n || (w_read && r_next == wr_addr)))
		last_write <= i_data;
	// }}}

	// osrc
	// {{{
	initial	osrc = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		osrc <= 1'b0;
	else if (i_wr && (!o_empty_n || (w_read && r_next == wr_addr)))
		osrc <= 1'b1;
	else if (i_rd)
		osrc <= 1'b0;
	// }}}

	assign o_data = (osrc) ? last_write : r_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Status signals and flags
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_fill
	// {{{
	// If this is a receive FIFO, the FIFO count that matters is the number
	// of values yet to be read.  If instead this is a transmit FIFO, then
	// the FIFO count that matters is the number of empty positions that
	// can still be filled before the FIFO is full.
	//
	// Adjust for these differences here.
	generate if (RXFIFO)
	begin : RXFIFO_FILL
		// {{{
		// Calculate the number of elements in our FIFO
		//
		// Although used for receive, this is actually the more
		// generic answer--should you wish to use the FIFO in
		// another context.

		initial	r_fill = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_fill <= 0;
		else case({ w_write, w_read })
		2'b01:	r_fill <= r_fill - 1'b1;
		2'b10:	r_fill <= r_fill + 1'b1;
		default:  begin end
		endcase
		// }}}
	end else begin : TXFIFO_FILL
		// {{{
		// Calculate the number of empty elements in our FIFO
		//
		// This is the number you could send to the FIFO
		// if you wanted to.

		initial	r_fill = -1;
		always @(posedge i_clk)
		if (i_reset)
			r_fill <= -1;
		else case({ w_write, w_read })
		2'b01:	r_fill <= r_fill + 1'b1;
		2'b10:	r_fill <= r_fill - 1'b1;
		default:  begin end
		endcase
		// }}}
	end endgenerate
	// }}}

	// o_err -- Flag any overflows
	// {{{
	assign o_err = (i_wr && !w_write);
	// }}}

	// o_status
	// {{{
	assign lglen = LGFLEN;

	always @(*)
	begin
		w_fill = 0;
		w_fill[(LGFLEN-1):0] = r_fill;
	end

	assign	w_half_full = r_fill[(LGFLEN-1)];

	assign	o_status = {
		// Our status includes a 4'bit nibble telling anyone reading
		// this the size of our FIFO.  The size is then given by
		// 2^(this value).  Hence a 4'h4 in this position means that the
		// FIFO has 2^4 or 16 values within it.
		lglen,
		// The FIFO fill--for a receive FIFO the number of elements
		// left to be read, and for a transmit FIFO the number of
		// empty elements within the FIFO that can yet be filled.
		w_fill,
		// A '1' here means a half FIFO length can be read (receive
		// FIFO) or written to (not a receive FIFO).  If one, a
		// halfway interrupt can be sent indicating a half of a FIFOs
		// operationw (either transmit or receive) will be successful.
		w_half_full,
		// A '1' here means the FIFO can be read from (if it is a
		// receive FIFO), or be written to (if it isn't).  An interrupt
		// may be sourced from this bit, indicating that at least one
		// operation will be successful.
		(RXFIFO!=0)?!will_underflow:!will_overflow
	};
	// }}}

	assign	o_empty_n = !will_underflow;
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Pointer checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[LGFLEN-1:0]	f_fill;
	wire	[LGFLEN-1:0]	f_raddr_plus_one;

	always @(*)
		f_fill = wr_addr - rd_addr;

	always @(*)
		assert(will_underflow == (f_fill == 0));

	always @(*)
		assert(will_overflow  == (&f_fill));

	assign	f_raddr_plus_one = rd_addr + 1;

	always @(*)
		assert(f_raddr_plus_one  == r_next);

	always @(*)
	if (will_underflow)
	begin
		assert(!w_read);
		assert(!osrc);
	end


	always @(posedge i_clk)
	if (RXFIFO)
		assert(r_fill == f_fill);
	else
		assert(r_fill == (~f_fill));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Twin write check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	UFIFO
	// Declare two arbitrary addresses and data values
	// {{{
	(* anyconst *) reg [LGFLEN-1:0]	f_const_addr;
	(* anyconst *) reg [BW-1:0]	f_const_data, f_const_second;
	reg [LGFLEN-1:0]	f_next_addr;
	reg	[1:0]		f_state;
	reg			f_first_in_fifo, f_second_in_fifo;
	reg	[LGFLEN-1:0]	f_distance_to_first, f_distance_to_second;
	// }}}

	// Determine if those data values are at their addresses in the FIFO
	// {{{
	always @(*)
	begin
		f_next_addr = f_const_addr + 1;

		f_distance_to_first  = f_const_addr - rd_addr;
		f_distance_to_second = f_next_addr  - rd_addr;

		f_first_in_fifo  = (f_distance_to_first  < f_fill)
			&& !will_underflow
			&& (fifo[f_const_addr] == f_const_data);
		f_second_in_fifo = (f_distance_to_second < f_fill)
			&& !will_underflow
			&& (fifo[f_next_addr] == f_const_second);
	end
	// }}}

	// Generate the twin-write state machine
	// {{{
	initial	f_state = 2'b00;
	always @(posedge i_clk)
	if (i_reset)
		f_state <= 2'b00;
	else case(f_state)
	2'b00: if (w_write &&(wr_addr == f_const_addr)
			&&(i_data == f_const_data))
		f_state <= 2'b01;
	2'b01: if (w_read && (rd_addr == f_const_addr))
			f_state <= 2'b00;
		else if (w_write && (wr_addr == f_next_addr))
			f_state <= (i_data == f_const_second) ? 2'b10 : 2'b00;
	2'b10: if (w_read && (rd_addr == f_const_addr))
			f_state <= 2'b11;
	2'b11: if (w_read)
			f_state <= 2'b00;
	endcase
	// }}}

	// Check conditions against the twin write state machine
	// {{{
	always @(*)
	case(f_state)
	2'b00: begin end
	2'b01: begin
		assert(!will_underflow);
		assert(f_first_in_fifo);
		assert(!f_second_in_fifo);
		assert(wr_addr == f_next_addr);
		assert(fifo[f_const_addr] == f_const_data);
		if (rd_addr == f_const_addr)
			assert(o_data == f_const_data);
		end
	2'b10: begin
		assert(f_first_in_fifo);
		assert(f_second_in_fifo);
		end
	2'b11: begin
		assert(f_second_in_fifo);
		assert(rd_addr == f_next_addr);
		assert(o_data  == f_const_second);
		end
	endcase
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
	reg	cvr_filled;

	always @(*)
		cover(o_empty_n);

	// Can't cover the FIFO being full when the FIFO is a member of another
	// components--so we only check that we can be filled here
`ifdef	UFIFO
	always @(*)
		cover(o_err);

	initial	cvr_filled = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_filled <= 0;
	else if (&f_fill[LGFLEN-1:0])
		cvr_filled <= 1;

	always @(*)
		cover(cvr_filled && !o_empty_n);
`endif // UFIFO
	// }}}
`endif
// }}}
endmodule
