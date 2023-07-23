////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbufifo.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This was once a FIFO for a UART ... but now it works as a
//		synchronous FIFO for JTAG-wishbone conversion 36-bit codewords. 
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
module wbufifo #(
		parameter	BW=66, LGFLEN=10
	) (
		// {{{
		input	wire		i_clk, i_reset,
		input	wire		i_wr,
		input	wire [(BW-1):0]	i_data,
		input	wire		i_rd,
		output	reg [(BW-1):0]	o_data,
		output	reg		o_empty_n,
		output	wire		o_err
		// }}}
	);

	// Local declarations
	// {{{
	localparam	FLEN=(1<<LGFLEN);

	reg	[(BW-1):0]	fifo[0:(FLEN-1)];
	reg	[LGFLEN:0]	r_wrptr, r_rdptr;
	wire	[LGFLEN:0]	nxt_wrptr, nxt_rdptr;
	reg			will_overflow,will_underflow, r_empty_n;
	wire			w_write, w_read;

	assign	w_write = (i_wr && (!will_overflow || i_rd));
	assign	w_read  = (i_rd||!o_empty_n) && !will_underflow;

	assign	nxt_wrptr = r_wrptr + 1;
	assign	nxt_rdptr = r_rdptr + 1;
	// }}}

	// will_overflow
	// {{{
	initial	will_overflow = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		will_overflow <= 1'b0;
	else if (i_rd)
		will_overflow <= (will_overflow)&&(i_wr);
	else if (w_write)
		will_overflow <= (nxt_wrptr[LGFLEN-1:0] == r_rdptr[LGFLEN-1:0])
			&&(nxt_wrptr[LGFLEN] != r_rdptr[LGFLEN]);
	// else if (nxt_wrptr == r_rdptr)
	//	will_overflow <= 1'b1;
	// }}}

	// r_wrptr, write to FIFO
	// {{{
	initial	r_wrptr = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_wrptr <= 0;
	else if (w_write)
		r_wrptr <= nxt_wrptr;

	always @(posedge i_clk)
	if (w_write)
		fifo[r_wrptr[LGFLEN-1:0]] <= i_data;
	// }}}

	// Notes
	// {{{
	// Reads
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
		will_underflow <= (will_underflow) || (nxt_rdptr==r_wrptr);
	// }}}

	// r_rdptr
	// {{{
	initial	r_rdptr = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_rdptr <= 0;
	else if (w_read && r_empty_n)
		r_rdptr <= r_rdptr + 1;
	// }}}

	// o_data, and reading from the FIFO
	// {{{
	always @(posedge i_clk)
	if (w_read && r_empty_n)
		o_data<= fifo[r_rdptr[LGFLEN-1:0]];
	// }}}

	// o_err
	// {{{
	assign	o_err = ((i_wr)&&(will_overflow)&&(!i_rd))
				||(i_rd && !o_empty_n);
	// }}}

	// r_empty_n
	// {{{
	always @(*)
		r_empty_n = !will_underflow;
	// }}}

	// o_empty_n
	// {{{
	initial	o_empty_n = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_empty_n <= 1'b0;
	else if (!o_empty_n || i_rd)
		o_empty_n <= r_empty_n;
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
	reg	[LGFLEN:0]	f_fifo_fill;

	always @(*)
		assert(r_empty_n == (f_fifo_fill != 0));
	always @(*)
		assert(r_empty_n == !will_underflow);
	always @(*)
	if (f_fifo_fill > 1)
		assert(o_empty_n);
	always @(*)
		assert(will_underflow == (f_fifo_fill == 0));
	always @(*)
		f_fifo_fill = r_wrptr - r_rdptr;

	always @(*)
		assert(f_fifo_fill <= (1<<LGFLEN));

	always @(*)
		assert(will_overflow==(f_fifo_fill=={1'b1,{(LGFLEN){1'b0}} }));


	always @(*)
	if (!f_past_valid)
	begin
		assert(!r_empty_n);
		assert(!o_empty_n);
		assert(f_fifo_fill == 0);
		assert(r_wrptr == 0);
		assert(r_rdptr == 0);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Formal methods section
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	(* anyconst *) reg	[LGFLEN:0]	f_first_addr;
	reg	[BW-1:0]	f_first, f_second;
	reg	[LGFLEN:0]	f_second_addr, f_third_addr;
	reg			f_first_in_fifo, f_second_in_fifo;
	reg	[LGFLEN:0]	f_distance_to_first, f_distance_to_second;

	always @(*)
		f_second_addr = f_first_addr + 1;

	always @(*)
		f_third_addr = f_second_addr + 1;

	always @(posedge i_clk)
	if ((!i_reset)&&(w_write))
	begin
		if (r_wrptr == f_first_addr)
			f_first <= i_data;
		if (r_wrptr == f_second_addr)
			f_second <= i_data;
	end

/*
	always @(posedge i_clk)
	if (i_rd && f_first_in_fifo && (r_rdptr == f_first_addr) && !will_underflow)
		assert(o_data == f_first);

	always @(posedge i_clk)
	if (i_rd && f_second_in_fifo && (r_rdptr == f_second_addr) && !will_underflow)
		assert(o_data == f_second);
*/

	////////////////////////////////////////////////////////////////////////
	//
	// Induction properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[1:0]	f_state;

	always @(*)
	begin
		f_distance_to_first = (f_first_addr - r_rdptr);
		f_first_in_fifo = (f_distance_to_first < f_fifo_fill)
				&&(f_fifo_fill > 0);
		if (fifo[f_first_addr[LGFLEN-1:0]] != f_first)
			f_first_in_fifo = 0;

		if ((o_data == f_first)&&(r_rdptr == f_second_addr)
			&&(o_empty_n))
			f_first_in_fifo = 1;
	end

	always @(*)
	begin
		f_distance_to_second = (f_second_addr - r_rdptr);
		f_second_in_fifo = (f_distance_to_second < f_fifo_fill)
				&&(f_fifo_fill > 0);
		if (fifo[f_second_addr[LGFLEN-1:0]] != f_second)
			f_second_in_fifo = 0;

		if ((o_data == f_second)&&(r_rdptr == f_third_addr)
			&&(o_empty_n))
			f_second_in_fifo = 1;
	end

	initial	f_state = 0;
	always @(posedge i_clk)
	if (i_reset || o_err)
		f_state <= 0;
	else case(f_state)
	2'b00: begin
		if (w_write && r_wrptr == f_first_addr)
			f_state <= 1;
		end
	2'b01: begin
		if (i_rd)
			f_state <= 0;
		else if (w_write && r_wrptr == f_second_addr)
			f_state <= 2'b10;
		end
	2'b10: begin
		if (w_read && r_rdptr == f_second_addr)
			f_state <= 2'b11;
		end
	2'b11: begin
		if (i_rd)
			f_state <= 2'b00;
		end
	endcase

//	always @(*)
//	if (!o_empty_n)
//		assert(o_data == fifo[r_rdptr]);

	always @(*)
	case(f_state)
	2'b00: begin end
	2'b01: begin
		assert(f_first_in_fifo);
		if (r_rdptr == f_second_addr)
			assert(o_data == f_first && o_empty_n);
		else
			assert(r_empty_n);
		assert(fifo[f_first_addr[LGFLEN-1:0]] == f_first
			||(r_rdptr == f_second_addr));
		end
	2'b10: begin
		assert(f_first_in_fifo);
		assert(o_empty_n);
		assert(r_empty_n);
		assert((fifo[f_first_addr[LGFLEN-1:0]] == f_first)
			||(o_data == f_first));
		if (r_rdptr == f_second_addr)
			assert(o_data == f_first);

		assert(f_second_in_fifo);
		assert(fifo[f_second_addr[LGFLEN-1:0]] == f_second);
		// assert(o_data == f_first);
		end
	2'b11: begin
		assert(o_empty_n);
		assert(r_rdptr == f_third_addr);
		assert(f_second_in_fifo);
		// assert(fifo[f_second_addr[LGFLEN-1:0]] == f_second);
		assert(o_data == f_second);
		end
	endcase

	always @(posedge i_clk)
	if (f_past_valid && i_wr && will_overflow && !i_rd)
		assert(o_err);

	always @(posedge i_clk)
	if (i_rd && !o_empty_n)
		assert(o_err);

`endif
// }}}
endmodule
