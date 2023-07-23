////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxuart.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Receive and decode inputs from a single UART line.
//
//
//	To interface with this module, connect it to your system clock,
//	pass it the 32 bit setup register (defined below) and the UART
//	input.  When data becomes available, the o_wr line will be asserted
//	for one clock cycle.  On parity or frame errors, the o_parity_err
//	or o_frame_err lines will be asserted.  Likewise, on a break 
//	condition, o_break will be asserted.  These lines are self clearing.
//
//	There is a synchronous reset line, logic high.
//
//	Now for the setup register.  The register is 32 bits, so that this
//	UART may be set up over a 32-bit bus.
//
//	i_setup[30]	True if we are not using hardware flow control.  This bit
//		is ignored within this module, as any receive hardware flow
//		control will need to be implemented elsewhere.
//
//	i_setup[29:28]	Indicates the number of data bits per word.  This will
//		either be 2'b00 for an 8-bit word, 2'b01 for a 7-bit word, 2'b10
//		for a six bit word, or 2'b11 for a five bit word.
//
//	i_setup[27]	Indicates whether or not to use one or two stop bits.
//		Set this to one to expect two stop bits, zero for one.
//
//	i_setup[26]	Indicates whether or not a parity bit exists.  Set this
//		to 1'b1 to include parity.
//
//	i_setup[25]	Indicates whether or not the parity bit is fixed.  Set
//		to 1'b1 to include a fixed bit of parity, 1'b0 to allow the
//		parity to be set based upon data.  (Both assume the parity
//		enable value is set.)
//
//	i_setup[24]	This bit is ignored if parity is not used.  Otherwise,
//		in the case of a fixed parity bit, this bit indicates whether
//		mark (1'b1) or space (1'b0) parity is used.  Likewise if the
//		parity is not fixed, a 1'b1 selects even parity, and 1'b0
//		selects odd.
//
//	i_setup[23:0]	Indicates the speed of the UART in terms of clocks.
//		So, for example, if you have a 200 MHz clock and wish to
//		run your UART at 9600 baud, you would take 200 MHz and divide
//		by 9600 to set this value to 24'd20834.  Likewise if you wished
//		to run this serial port at 115200 baud from a 200 MHz clock,
//		you would set the value to 24'd1736
//
//	Thus, to set the UART for the common setting of an 8-bit word, 
//	one stop bit, no parity, and 115200 baud over a 200 MHz clock, you
//	would want to set the setup value to:
//
//	32'h0006c8		// For 115,200 baud, 8 bit, no parity
//	32'h005161		// For 9600 baud, 8 bit, no parity
//	
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
// }}}
module rxuart #(
		// {{{
		// 8 data bits, no parity, (at least 1) stop bit
		parameter [30:0] INITIAL_SETUP = 31'd868,
		// States: (@ baud counter == 0)
		//	0	First bit arrives
		//	..7	Bits arrive
		//	8	Stop bit (x1)
		//	9	Stop bit (x2)
		//	c	break condition
		//	d	Waiting for the channel to go high
		//	e	Waiting for the reset to complete
		//	f	Idle state
		localparam [3:0]	RXU_BIT_ZERO    = 4'h0,
					RXU_BIT_ONE     = 4'h1,
					RXU_BIT_TWO     = 4'h2,
					RXU_BIT_THREE   =  4'h3,
					// RXU_BIT_FOUR = 4'h4, // UNUSED
					// RXU_BIT_FIVE = 4'h5, // UNUSED
					// RXU_BIT_SIX  = 4'h6, // UNUSED
					RXU_BIT_SEVEN   = 4'h7,
					RXU_PARITY      = 4'h8,
					RXU_STOP        = 4'h9,
					RXU_SECOND_STOP = 4'ha,
					// Unused 4'hb
					// Unused 4'hc
					RXU_BREAK       = 4'hd,
					RXU_RESET_IDLE  = 4'he,
					RXU_IDLE        = 4'hf
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		/* verilator lint_off UNUSED */
		input	wire	[30:0]	i_setup,
		/* verilator lint_on UNUSED */
		input	wire		i_uart_rx,
		output	reg		o_wr,
		output	reg	[7:0]	o_data,
		output	reg		o_break,
		output	reg		o_parity_err, o_frame_err,
		output	wire		o_ck_uart
		// }}}
	);

	// Signal declarations
	// {{{
	wire	[27:0]	clocks_per_baud, break_condition, half_baud;
	wire	[1:0]	data_bits;
	wire		use_parity, parity_even, dblstop, fixd_parity;
	reg	[29:0]	r_setup;
	reg	[3:0]	state;

	reg	[27:0]	baud_counter;
	reg		zero_baud_counter;
	reg		q_uart, qq_uart, ck_uart;
	reg	[27:0]	chg_counter;
	reg		line_synch;
	reg		half_baud_time;
	reg	[7:0]	data_reg;
	reg		calc_parity;
	reg		pre_wr;

	assign	clocks_per_baud = { 4'h0, r_setup[23:0] };
	// assign hw_flow_control = !r_setup[30];
	assign	data_bits   = r_setup[29:28];
	assign	dblstop     = r_setup[27];
	assign	use_parity  = r_setup[26];
	assign	fixd_parity = r_setup[25];
	assign	parity_even = r_setup[24];
	assign	break_condition = { r_setup[23:0], 4'h0 };
	assign	half_baud = { 5'h00, r_setup[23:1] }-28'h1;

	// }}}

	// ck_uart
	// {{{
	// Since this is an asynchronous receiver, we need to register our
	// input a couple of clocks over to avoid any problems with 
	// metastability.  We do that here, and then ignore all but the
	// ck_uart wire.
	initial	q_uart  = 1'b0;
	initial	qq_uart = 1'b0;
	initial	ck_uart = 1'b0;
	always @(posedge i_clk)
	begin
		q_uart <= i_uart_rx;
		qq_uart <= q_uart;
		ck_uart <= qq_uart;
	end
	// }}}

	// o_ck_uart
	// {{{
	// In case anyone else wants this clocked, stabilized value, we
	// offer it on our output.
	assign	o_ck_uart = ck_uart;
	// }}}

	// chg_counter
	// {{{
	// Keep track of the number of clocks since the last change.
	//
	// This is used to determine if we are in either a break or an idle
	// condition, as discussed further below.
	initial	chg_counter = 28'h00;
	always @(posedge i_clk)
	if (i_reset)
		chg_counter <= 28'h00;
	else if (qq_uart != ck_uart)
		chg_counter <= 28'h00;
	else if (chg_counter < break_condition)
		chg_counter <= chg_counter + 1;
	// }}}

	// o_break
	// {{{
	// Are we in a break condition?
	//
	// A break condition exists if the line is held low for longer than
	// a data word.  Hence, we keep track of when the last change occurred.
	// If it was more than break_condition clocks ago, and the current input
	// value is a 0, then we're in a break--and nothing can be read until
	// the line idles again.
	initial	o_break    = 1'b0;
	always @(posedge i_clk)
		o_break <= ((chg_counter >= break_condition)&&(~ck_uart))? 1'b1:1'b0;
	// }}}

	// line_synch
	// {{{
	// Are we between characters?
	//
	// The opposite of a break condition is where the line is held high
	// for more clocks than would be in a character.  When this happens,
	// we know we have synchronization--otherwise, we might be sampling
	// from within a data word.
	//
	// This logic is used later to hold the RXUART in a reset condition
	// until we know we are between data words.  At that point, we should
	// be able to hold on to our synchronization.
	initial	line_synch = 1'b0;
	always @(posedge i_clk)
		line_synch <= ((chg_counter >= break_condition)&&(ck_uart));
	// }}}

	// half_baud_time
	// {{{
	// Are we in the middle of a baud iterval?  Specifically, are we
	// in the middle of a start bit?  Set this to high if so.  We'll use
	// this within our state machine to transition out of the IDLE
	// state.
	initial	half_baud_time = 0;
	always @(posedge i_clk)
		half_baud_time <= (~ck_uart)&&(chg_counter >= half_baud);
	// }}}

	// r_setup
	// {{{
	// Allow our controlling processor to change our setup at any time
	// outside of receiving/processing a character.
	initial	r_setup     = INITIAL_SETUP[29:0];
	always @(posedge i_clk)
	if (state >= RXU_RESET_IDLE)
		r_setup <= i_setup[29:0];
	// }}}

	// state -- the monster state machine
	// {{{
	// Our monster state machine.  YIKES!
	//
	// Yeah, this may be more complicated than it needs to be.  The basic
	// progression is:
	//	RESET -> RESET_IDLE -> (when line is idle) -> IDLE
	//	IDLE -> bit 0 -> bit 1 -> bit_{ndatabits} -> 
	//		(optional) PARITY -> STOP -> (optional) SECOND_STOP
	//		-> IDLE
	//	ANY -> (on break) BREAK -> IDLE
	//
	// There are 16 states, although all are not used.  These are listed
	// at the top of this file.
	//
	//	Logic inputs (12):	(I've tried to minimize this number)
	//		state	(4)
	//		i_reset
	//		line_synch
	//		o_break
	//		ckuart
	//		half_baud_time
	//		zero_baud_counter
	//		use_parity
	//		dblstop
	//	Logic outputs (4):
	//		state
	//
	initial	state = RXU_RESET_IDLE;
	always @(posedge i_clk)
	if (i_reset)
		state <= RXU_RESET_IDLE;
	else if (state == RXU_RESET_IDLE)
	begin
		// {{{
		if (line_synch)
			// Goto idle state from a reset
			state <= RXU_IDLE;
		else // Otherwise, stay in this condition 'til reset
			state <= RXU_RESET_IDLE;
		// }}}
	end else if (o_break)
	begin // We are in a break condition
		state <= RXU_BREAK;
	end else if (state == RXU_BREAK)
	begin // Goto idle state following return ck_uart going high
		// {{{
		if (ck_uart)
			state <= RXU_IDLE;
		else
			state <= RXU_BREAK;
		// }}}
	end else if (state == RXU_IDLE)
	begin // Idle state, independent of baud counter
			// {{{
			if ((~ck_uart)&&(half_baud_time))
			begin
				// We are in the center of a valid start bit
				case (data_bits)
				2'b00: state <= RXU_BIT_ZERO;
				2'b01: state <= RXU_BIT_ONE;
				2'b10: state <= RXU_BIT_TWO;
				2'b11: state <= RXU_BIT_THREE;
				endcase
			end else // Otherwise, just stay here in idle
				state <= RXU_IDLE;
			// }}}
	end else if (zero_baud_counter)
	begin
		// {{{
		if (state < RXU_BIT_SEVEN)
			// Data arrives least significant bit first.
			// By the time this is clocked in, it's what
			// you'll have.
			state <= state + 1;
		else if (state == RXU_BIT_SEVEN)
			state <= (use_parity) ? RXU_PARITY:RXU_STOP;
		else if (state == RXU_PARITY)
			state <= RXU_STOP;
		else if (state == RXU_STOP)
		begin // Stop (or parity) bit(s)
			if (~ck_uart) // On frame error, wait 4 ch idle
				state <= RXU_RESET_IDLE;
			else if (dblstop)
				state <= RXU_SECOND_STOP;
			else
				state <= RXU_IDLE;
		end else // state must equal RX_SECOND_STOP
		begin
			if (~ck_uart) // On frame error, wait 4 ch idle
				state <= RXU_RESET_IDLE;
			else
				state <= RXU_IDLE;
		end
		// }}}
	end
	// }}}

	// data_reg -- Data bit capture logic.
	// {{{
	// This is drastically simplified from the state machine above, based
	// upon: 1) it doesn't matter what it is until the end of a captured
	// byte, and 2) the data register will flush itself of any invalid
	// data in all other cases.  Hence, let's keep it real simple.
	// The only trick, though, is that if we have parity, then the data
	// register needs to be held through that state without getting
	// updated.
	always @(posedge i_clk)
	if ((zero_baud_counter)&&(state != RXU_PARITY))
		data_reg <= { ck_uart, data_reg[7:1] };
	// }}}

	// calc_parity
	// {{{
	// Parity calculation logic
	//
	// As with the data capture logic, all that must be known about this
	// bit is that it is the exclusive-OR of all bits prior.  The first
	// of those will follow idle, so we set ourselves to zero on idle.
	// Then, as we walk through the states of a bit, all will adjust this
	// value up until the parity bit, where the value will be read.  Setting
	// it then or after will be irrelevant, so ... this should be good
	// and simplified.  Note--we don't need to adjust this on reset either,
	// since the reset state will lead to the idle state where we'll be
	// reset before any transmission takes place.
	always @(posedge i_clk)
	if (state == RXU_IDLE)
		calc_parity <= 0;
	else if (zero_baud_counter)
		calc_parity <= calc_parity ^ ck_uart;
	// }}}

	// o_parity_err -- Parity error logic
	// {{{
	// Set during the parity bit interval, read during the last stop bit
	// interval, cleared on BREAK, RESET_IDLE, or IDLE states.
	initial	o_parity_err = 1'b0;
	always @(posedge i_clk)
	if ((zero_baud_counter)&&(state == RXU_PARITY))
	begin
		if (fixd_parity)
			// Fixed parity bit--independent of any dat
			// value.
			o_parity_err <= (ck_uart ^ parity_even);
		else if (parity_even)
			// Parity even: The XOR of all bits including
			// the parity bit must be zero.
			o_parity_err <= (calc_parity != ck_uart);
		else
			// Parity odd: the parity bit must equal the
			// XOR of all the data bits.
			o_parity_err <= (calc_parity == ck_uart);
	end else if (state >= RXU_BREAK)
		o_parity_err <= 1'b0;
	// }}}

	// o_frame_err -- Frame error determination
	// {{{
	// For the purpose of this controller, a frame error is defined as a
	// stop bit (or second stop bit, if so enabled) not being high midway
	// through the stop baud interval.   The frame error value is
	// immediately read, so we can clear it under all other circumstances.
	// Specifically, we want it clear in RXU_BREAK, RXU_RESET_IDLE, and
	// most importantly in RXU_IDLE.
	initial	o_frame_err  = 1'b0;
	always @(posedge i_clk)
	if ((zero_baud_counter)&&((state == RXU_STOP)
					||(state == RXU_SECOND_STOP)))
		o_frame_err <= (o_frame_err)||(~ck_uart);
	else if ((zero_baud_counter)||(state >= RXU_BREAK))
		o_frame_err <= 1'b0;
	// }}}

	// pre_wr, o_data
	// {{{
	// Our data bit logic doesn't need nearly the complexity of all that
	// work above.  Indeed, we only need to know if we are at the end of
	// a stop bit, in which case we copy the data_reg into our output
	// data register, o_data.
	//
	// We would also set o_wr to be true when this is the case, but ... we
	// won't know if there is a frame error on the second stop bit for 
	// another baud interval yet.  So, instead, we set up the logic so that
	// we know on the next zero baud counter that we can write out.  That's
	// the purpose of pre_wr.
	initial	o_data = 8'h00;
	initial	pre_wr = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		pre_wr <= 1'b0;
		o_data <= 8'h00;
	end else if ((zero_baud_counter)&&(state == RXU_STOP))
	begin
		pre_wr <= 1'b1;
		case (data_bits)
		2'b00: o_data <= data_reg;
		2'b01: o_data <= { 1'b0, data_reg[7:1] };
		2'b10: o_data <= { 2'b0, data_reg[7:2] };
		2'b11: o_data <= { 3'b0, data_reg[7:3] };
		endcase
	end else if ((zero_baud_counter)||(state == RXU_IDLE))
		pre_wr <= 1'b0;
	// }}}

	// o_wr
	// {{{
	// Create an output strobe, true for one clock only, once we know
	// all we need to know.  o_data will be set on the last baud interval,
	// o_parity_err on the last parity baud interval (if it existed,
	// cleared otherwise, so ... we should be good to go here.)
	initial	o_wr   = 1'b0;
	always @(posedge i_clk)
	if ((zero_baud_counter)||(state == RXU_IDLE))
		o_wr <= (pre_wr)&&(!i_reset);
	else
		o_wr <= 1'b0;
	// }}}

	// The baud counter
	// {{{
	// This is used as a "clock divider" if you will, but the clock needs
	// to be reset before any byte can be decoded.  In all other respects,
	// we set ourselves up for clocks_per_baud counts between baud
	// intervals.
	always @(posedge i_clk)
	if (i_reset)
		baud_counter <= clocks_per_baud-28'h01;
	else if (zero_baud_counter)
		baud_counter <= clocks_per_baud-28'h01;
	else case(state)
		RXU_RESET_IDLE:baud_counter <= clocks_per_baud-28'h01;
		RXU_BREAK:	baud_counter <= clocks_per_baud-28'h01;
		RXU_IDLE:	baud_counter <= clocks_per_baud-28'h01;
		default:	baud_counter <= baud_counter-28'h01;
	endcase
	// }}}

	// zero_baud_counter
	// {{{
	// Rather than testing whether or not (baud_counter == 0) within our
	// (already too complicated) state transition tables, we use
	// zero_baud_counter to pre-charge that test on the clock
	// before--cleaning up some otherwise difficult timing dependencies.
	initial	zero_baud_counter = 1'b0;
	always @(posedge i_clk)
	if (state == RXU_IDLE)
		zero_baud_counter <= 1'b0;
	else
		zero_baud_counter <= (baud_counter == 28'h01);
	// }}}
endmodule


