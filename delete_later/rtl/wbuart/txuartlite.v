////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	txuartlite.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Transmit outputs over a single UART line.  This particular UART
//		implementation has been extremely simplified: it does not handle
//	generating break conditions, nor does it handle anything other than the
//	8N1 (8 data bits, no parity, 1 stop bit) UART sub-protocol.
//
//	To interface with this module, connect it to your system clock, and
//	pass it the byte of data you wish to transmit.  Strobe the i_wr line
//	high for one cycle, and your data will be off.  Wait until the 'o_busy'
//	line is low before strobing the i_wr line again--this implementation
//	has NO BUFFER, so strobing i_wr while the core is busy will just
//	get ignored.  The output will be placed on the o_txuart output line.
//
//	(I often set both data and strobe on the same clock, and then just leave
//	them set until the busy line is low.  Then I move on to the next piece
//	of data.)
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
module txuartlite #(
		// {{{
		// TIMING_BITS -- the number of bits required to represent
		// the number of clocks per baud.  24 should be sufficient for
		// most baud rates, but you can trim it down to save logic if
		// you would like.  TB is just an abbreviation for TIMING_BITS.
		parameter	[4:0]	TIMING_BITS = 5'd24,
		localparam		TB = TIMING_BITS,
		// CLOCKS_PER_BAUD -- the number of system clocks per baud
		// interval.
		parameter	[(TB-1):0]	CLOCKS_PER_BAUD = 8 // 24'd868
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_wr,
		input	wire	[7:0]	i_data,
		// And the UART input line itself
		output	reg		o_uart_tx,
		// A line to tell others when we are ready to accept data.  If
		// (i_wr)&&(!o_busy) is ever true, then the core has accepted
		// a byte for transmission.
		output	wire		o_busy
		// }}}
	);

	// Register/net declarations
	// {{{
	localparam [3:0]	TXUL_BIT_ZERO  = 4'h0,
			//	TXUL_BIT_ONE   = 4'h1,
			//	TXUL_BIT_TWO   = 4'h2,
			//	TXUL_BIT_THREE = 4'h3,
			//	TXUL_BIT_FOUR  = 4'h4,
			//	TXUL_BIT_FIVE  = 4'h5,
			//	TXUL_BIT_SIX   = 4'h6,
			//	TXUL_BIT_SEVEN = 4'h7,
				TXUL_STOP      = 4'h8,
				TXUL_IDLE      = 4'hf;

	reg	[(TB-1):0]	baud_counter;
	reg	[3:0]	state;
	reg	[7:0]	lcl_data;
	reg		r_busy, zero_baud_counter;
	// }}}

	// Big state machine controlling: r_busy, state
	// {{{
	//
	initial	r_busy = 1'b1;
	initial	state  = TXUL_IDLE;
	always @(posedge i_clk)
	begin
		if (!zero_baud_counter)
			// r_busy needs to be set coming into here
			r_busy <= 1'b1;
		else if (state > TXUL_STOP)	// STATE_IDLE
		begin
			state <= TXUL_IDLE;
			r_busy <= 1'b0;
			if ((i_wr)&&(!r_busy))
			begin	// Immediately start us off with a start bit
				r_busy <= 1'b1;
				state <= TXUL_BIT_ZERO;
			end
		end else begin
			// One clock tick in each of these states ...
			r_busy <= 1'b1;
			if (state <=TXUL_STOP) // start bit, 8-d bits, stop-b
				state <= state + 1'b1;
			else
				state <= TXUL_IDLE;
		end
	end
	// }}}

	// o_busy
	// {{{
	//
	// This is a wire, designed to be true is we are ever busy above.
	// originally, this was going to be true if we were ever not in the
	// idle state.  The logic has since become more complex, hence we have
	// a register dedicated to this and just copy out that registers value.
	assign	o_busy = (r_busy);
	// }}}

	// lcl_data
	// {{{
	//
	// This is our working copy of the i_data register which we use
	// when transmitting.  It is only of interest during transmit, and is
	// allowed to be whatever at any other time.  Hence, if r_busy isn't
	// true, we can always set it.  On the one clock where r_busy isn't
	// true and i_wr is, we set it and r_busy is true thereafter.
	// Then, on any zero_baud_counter (i.e. change between baud intervals)
	// we simple logically shift the register right to grab the next bit.
	initial	lcl_data = 8'hff;
	always @(posedge i_clk)
		if ((i_wr)&&(!r_busy))
			lcl_data <= i_data;
		else if (zero_baud_counter)
			lcl_data <= { 1'b1, lcl_data[7:1] };
	// }}}

	// o_uart_tx
	// {{{
	//
	// This is the final result/output desired of this core.  It's all
	// centered about o_uart_tx.  This is what finally needs to follow
	// the UART protocol.
	//
	initial	o_uart_tx = 1'b1;
	always @(posedge i_clk)
		if ((i_wr)&&(!r_busy))
			o_uart_tx <= 1'b0;	// Set the start bit on writes
		else if (zero_baud_counter)	// Set the data bit.
			o_uart_tx <= lcl_data[0];
	// }}}

	// Baud counter
	// {{{
	// All of the above logic is driven by the baud counter.  Bits must last
	// CLOCKS_PER_BAUD in length, and this baud counter is what we use to
	// make certain of that.
	//
	// The basic logic is this: at the beginning of a bit interval, start
	// the baud counter and set it to count CLOCKS_PER_BAUD.  When it gets
	// to zero, restart it.
	//
	// However, comparing a 28'bit number to zero can be rather complex--
	// especially if we wish to do anything else on that same clock.  For
	// that reason, we create "zero_baud_counter".  zero_baud_counter is
	// nothing more than a flag that is true anytime baud_counter is zero.
	// It's true when the logic (above) needs to step to the next bit.
	// Simple enough?
	//
	// I wish we could stop there, but there are some other (ugly)
	// conditions to deal with that offer exceptions to this basic logic.
	//
	// 1. When the user has commanded a BREAK across the line, we need to
	// wait several baud intervals following the break before we start
	// transmitting, to give any receiver a chance to recognize that we are
	// out of the break condition, and to know that the next bit will be
	// a stop bit.
	//
	// 2. A reset is similar to a break condition--on both we wait several
	// baud intervals before allowing a start bit.
	//
	// 3. In the idle state, we stop our counter--so that upon a request
	// to transmit when idle we can start transmitting immediately, rather
	// than waiting for the end of the next (fictitious and arbitrary) baud
	// interval.
	//
	// When (i_wr)&&(!r_busy)&&(state == TXUL_IDLE) then we're not only in
	// the idle state, but we also just accepted a command to start writing
	// the next word.  At this point, the baud counter needs to be reset
	// to the number of CLOCKS_PER_BAUD, and zero_baud_counter set to zero.
	//
	// The logic is a bit twisted here, in that it will only check for the
	// above condition when zero_baud_counter is false--so as to make
	// certain the STOP bit is complete.
	initial	zero_baud_counter = 1'b1;
	initial	baud_counter = 0;
	always @(posedge i_clk)
	begin
		zero_baud_counter <= (baud_counter == 1);
		if (state == TXUL_IDLE)
		begin
			baud_counter <= 0;
			zero_baud_counter <= 1'b1;
			if ((i_wr)&&(!r_busy))
			begin
				baud_counter <= CLOCKS_PER_BAUD - 1'b1;
				zero_baud_counter <= 1'b0;
			end
		end else if (!zero_baud_counter)
			baud_counter <= baud_counter - 1'b1;
		else if (state > TXUL_STOP)
		begin
			baud_counter <= 0;
			zero_baud_counter <= 1'b1;
		end else if (state == TXUL_STOP)
			// Need to complete this state one clock early, so
			// we can release busy one clock before the stop bit
			// is complete, so we can start on the next byte
			// exactly 10*CLOCKS_PER_BAUD clocks after we started
			// the last one
			baud_counter <= CLOCKS_PER_BAUD - 2;
		else // All other states
			baud_counter <= CLOCKS_PER_BAUD - 1'b1;
	end
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// FORMAL METHODS
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Declarations
`ifdef	TXUARTLITE
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	reg			f_past_valid, f_last_clk;
	reg	[(TB-1):0]	f_baud_count;
	reg	[9:0]		f_txbits;
	reg	[3:0]		f_bitcount;
	reg	[7:0]		f_request_tx_data;
	wire	[3:0]		subcount;

	// Setup
	// {{{
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	`ASSUME(!i_wr);
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wr))&&($past(o_busy)))
		begin
			`ASSUME(i_wr   == $past(i_wr));
			`ASSUME(i_data == $past(i_data));
		end
	// }}}

	// Check the baud counter
	// {{{
	always @(posedge i_clk)
		assert(zero_baud_counter == (baud_counter == 0));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(baud_counter != 0))&&($past(state != TXUL_IDLE)))
		assert(baud_counter == $past(baud_counter - 1'b1));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(zero_baud_counter))&&($past(state != TXUL_IDLE)))
		assert($stable(o_uart_tx));

	initial	f_baud_count = 1'b0;
	always @(posedge i_clk)
	if (zero_baud_counter)
		f_baud_count <= 0;
	else
		f_baud_count <= f_baud_count + 1'b1;

	always @(posedge i_clk)
		assert(f_baud_count < CLOCKS_PER_BAUD);

	always @(posedge i_clk)
	if (baud_counter != 0)
		assert(o_busy);
	// }}}

	// {{{
	initial	f_txbits = 0;
	always @(posedge i_clk)
	if (zero_baud_counter)
		f_txbits <= { o_uart_tx, f_txbits[9:1] };

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(zero_baud_counter))
			&&(!$past(state==TXUL_IDLE)))
		assert(state == $past(state));

	initial	f_bitcount = 0;
	always @(posedge i_clk)
	if ((!f_past_valid)||(!$past(f_past_valid)))
		f_bitcount <= 0;
	else if ((state == TXUL_IDLE)&&(zero_baud_counter))
		f_bitcount <= 0;
	else if (zero_baud_counter)
		f_bitcount <= f_bitcount + 1'b1;

	always @(posedge i_clk)
		assert(f_bitcount <= 4'ha);

	always @(*)
	if (!o_busy)
		assert(zero_baud_counter);

	always @(posedge i_clk)
	if ((i_wr)&&(!o_busy))
		f_request_tx_data <= i_data;

	assign	subcount = 10-f_bitcount;
	always @(posedge i_clk)
	if (f_bitcount > 0)
		assert(!f_txbits[subcount]);

	always @(posedge i_clk)
	if (f_bitcount == 4'ha)
	begin
		assert(f_txbits[8:1] == f_request_tx_data);
		assert( f_txbits[9]);
	end

	always @(posedge i_clk)
		assert((state <= TXUL_STOP + 1'b1)||(state == TXUL_IDLE));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(f_past_valid))&&($past(o_busy)))
		cover(!o_busy);
	// }}}

`endif	// FORMAL
`ifdef	VERIFIC_SVA
	reg	[7:0]	fsv_data;

	//
	// Grab a copy of the data any time we are sent a new byte to transmit
	// We'll use this in a moment to compare the item transmitted against
	// what is supposed to be transmitted
	//
	always @(posedge i_clk)
	if ((i_wr)&&(!o_busy))
		fsv_data <= i_data;

	//
	// One baud interval
	// {{{
	//
	// 1. The UART output is constant at DAT
	// 2. The internal state remains constant at ST
	// 3. CKS = the number of clocks per bit.
	//
	// Everything stays constant during the CKS clocks with the exception
	// of (zero_baud_counter), which is *only* raised on the last clock
	// interval
	sequence	BAUD_INTERVAL(CKS, DAT, SR, ST);
		((o_uart_tx == DAT)&&(state == ST)
			&&(lcl_data == SR)
			&&(!zero_baud_counter))[*(CKS-1)]
		##1 (o_uart_tx == DAT)&&(state == ST)
			&&(lcl_data == SR)
			&&(zero_baud_counter);
	endsequence
	// }}}

	//
	// One byte transmitted
	// {{{
	//
	// DATA = the byte that is sent
	// CKS  = the number of clocks per bit
	//
	sequence	SEND(CKS, DATA);
		BAUD_INTERVAL(CKS, 1'b0, DATA, 4'h0)
		##1 BAUD_INTERVAL(CKS, DATA[0], {{(1){1'b1}},DATA[7:1]}, 4'h1)
		##1 BAUD_INTERVAL(CKS, DATA[1], {{(2){1'b1}},DATA[7:2]}, 4'h2)
		##1 BAUD_INTERVAL(CKS, DATA[2], {{(3){1'b1}},DATA[7:3]}, 4'h3)
		##1 BAUD_INTERVAL(CKS, DATA[3], {{(4){1'b1}},DATA[7:4]}, 4'h4)
		##1 BAUD_INTERVAL(CKS, DATA[4], {{(5){1'b1}},DATA[7:5]}, 4'h5)
		##1 BAUD_INTERVAL(CKS, DATA[5], {{(6){1'b1}},DATA[7:6]}, 4'h6)
		##1 BAUD_INTERVAL(CKS, DATA[6], {{(7){1'b1}},DATA[7:7]}, 4'h7)
		##1 BAUD_INTERVAL(CKS, DATA[7], 8'hff, 4'h8)
		##1 BAUD_INTERVAL(CKS-1, 1'b1, 8'hff, 4'h9);
	endsequence
	// }}}

	//
	// Transmit one byte
	// {{{
	// Once the byte is transmitted, make certain we return to
	// idle
	//
	assert property (
		@(posedge i_clk)
		(i_wr)&&(!o_busy)
		|=> ((o_busy) throughout SEND(CLOCKS_PER_BAUD,fsv_data))
		##1 (!o_busy)&&(o_uart_tx)&&(zero_baud_counter));
	// }}}

	// {{{
	assume property (
		@(posedge i_clk)
		(i_wr)&&(o_busy) |=>
			(i_wr)&&($stable(i_data)));

	//
	// Make certain that o_busy is true any time zero_baud_counter is
	// non-zero
	//
	always @(*)
		assert((o_busy)||(zero_baud_counter) );

	// If and only if zero_baud_counter is true, baud_counter must be zero
	// Insist on that relationship here.
	always @(*)
		assert(zero_baud_counter == (baud_counter == 0));

	// To make certain baud_counter stays below CLOCKS_PER_BAUD
	always @(*)
		assert(baud_counter < CLOCKS_PER_BAUD);

	//
	// Insist that we are only ever in a valid state
	always @(*)
		assert((state <= TXUL_STOP+1'b1)||(state == TXUL_IDLE));
	// }}}

`endif // Verific SVA
// }}}
endmodule
