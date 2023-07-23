////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	txuart.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Transmit outputs over a single UART line.
//
//	To interface with this module, connect it to your system clock,
//	pass it the 32 bit setup register (defined below) and the byte
//	of data you wish to transmit.  Strobe the i_wr line high for one
//	clock cycle, and your data will be off.  Wait until the 'o_busy'
//	line is low before strobing the i_wr line again--this implementation
//	has NO BUFFER, so strobing i_wr while the core is busy will just
//	cause your data to be lost.  The output will be placed on the o_txuart
//	output line.  If you wish to set/send a break condition, assert the
//	i_break line otherwise leave it low.
//
//	There is a synchronous reset line, logic high.
//
//	Now for the setup register.  The register is 32 bits, so that this
//	UART may be set up over a 32-bit bus.
//
//	i_setup[30]	Set this to zero to use hardware flow control, and to
//		one to ignore hardware flow control.  Only works if the hardware
//		flow control has been properly wired.
//
//		If you don't want hardware flow control, fix the i_rts bit to
//		1'b1, and let the synthesys tools optimize out the logic.
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
module txuart #(
		// {{{
		parameter	[30:0]	INITIAL_SETUP = 31'd868,
		//
		localparam 	[3:0]	TXU_BIT_ZERO  = 4'h0,
		localparam 	[3:0]	TXU_BIT_ONE   = 4'h1,
		localparam 	[3:0]	TXU_BIT_TWO   = 4'h2,
		localparam 	[3:0]	TXU_BIT_THREE = 4'h3,
		// localparam 	[3:0]	TXU_BIT_FOUR  = 4'h4,
		// localparam 	[3:0]	TXU_BIT_FIVE  = 4'h5,
		// localparam 	[3:0]	TXU_BIT_SIX   = 4'h6,
		localparam 	[3:0]	TXU_BIT_SEVEN = 4'h7,
		localparam 	[3:0]	TXU_PARITY    = 4'h8,
		localparam 	[3:0]	TXU_STOP      = 4'h9,
		localparam 	[3:0]	TXU_SECOND_STOP = 4'ha,
		//
		localparam 	[3:0]	TXU_BREAK     = 4'he,
		localparam 	[3:0]	TXU_IDLE      = 4'hf
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		input	wire	[30:0]	i_setup,
		input	wire		i_break,
		input	wire		i_wr,
		input	wire	[7:0]	i_data,
		// Hardware flow control Ready-To-Send bit.  Set this to one to
		// use the core without flow control.  (A more appropriate name
		// would be the Ready-To-Receive bit ...)
		input	wire		i_cts_n,
		// And the UART input line itself
		output	reg		o_uart_tx,
		// A line to tell others when we are ready to accept data.  If
		// (i_wr)&&(!o_busy) is ever true, then the core has accepted a
		// byte for transmission.
		output	wire		o_busy
		// }}}
	);

	// Signal declarations
	// {{{
	wire	[27:0]	clocks_per_baud, break_condition;
	wire	[1:0]	i_data_bits, data_bits;
	wire		use_parity, parity_odd, dblstop, fixd_parity,
			fixdp_value, hw_flow_control, i_parity_odd;
	reg	[30:0]	r_setup;
	assign	clocks_per_baud = { 4'h0, r_setup[23:0] };
	assign	break_condition = { r_setup[23:0], 4'h0 };
	assign	hw_flow_control = !r_setup[30];
	assign	i_data_bits     =  i_setup[29:28];
	assign	data_bits       =  r_setup[29:28];
	assign	dblstop         =  r_setup[27];
	assign	use_parity      =  r_setup[26];
	assign	fixd_parity     =  r_setup[25];
	assign	i_parity_odd    =  i_setup[24];
	assign	parity_odd      =  r_setup[24];
	assign	fixdp_value     =  r_setup[24];

	reg	[27:0]	baud_counter;
	reg	[3:0]	state;
	reg	[7:0]	lcl_data;
	reg		calc_parity, r_busy, zero_baud_counter, last_state;
	reg		q_cts_n, qq_cts_n, ck_cts;
	// }}}

	// CTS: ck_cts
	// {{{
	// First step ... handle any hardware flow control, if so enabled.
	//
	// Clock in the flow control data, two clocks to avoid metastability
	// Default to using hardware flow control (uart_setup[30]==0 to use it).
	// Set this high order bit off if you do not wish to use it.
	//
	// While we might wish to give initial values to q_rts and ck_cts,
	// 1) it's not required since the transmitter starts in a long wait
	// state, and 2) doing so will prevent the synthesizer from optimizing
	// this pin in the case it is hard set to 1'b1 external to this
	// peripheral.
	//
	// initial	q_cts_n  = 1'b1;
	// initial	qq_cts_n = 1'b1;
	// initial	ck_cts   = 1'b0;
	always	@(posedge i_clk)
		{ qq_cts_n, q_cts_n } <= { q_cts_n, i_cts_n };
	always	@(posedge i_clk)
		ck_cts <= (!qq_cts_n)||(!hw_flow_control);
	// }}}

	// r_busy, state
	// {{{
	initial	r_busy = 1'b1;
	initial	state  = TXU_IDLE;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_busy <= 1'b1;
		state <= TXU_IDLE;
	end else if (i_break)
	begin
		state <= TXU_BREAK;
		r_busy <= 1'b1;
	end else if (!zero_baud_counter)
	begin // r_busy needs to be set coming into here
		r_busy <= 1'b1;
	end else if (state == TXU_BREAK)
	begin
		state <= TXU_IDLE;
		r_busy <= !ck_cts;
	end else if (state == TXU_IDLE)	// STATE_IDLE
	begin
		if ((i_wr)&&(!r_busy))
		begin	// Immediately start us off with a start bit
			r_busy <= 1'b1;
			case(i_data_bits)
			2'b00: state <= TXU_BIT_ZERO;
			2'b01: state <= TXU_BIT_ONE;
			2'b10: state <= TXU_BIT_TWO;
			2'b11: state <= TXU_BIT_THREE;
			endcase
		end else begin // Stay in idle
			r_busy <= !ck_cts;
		end
	end else begin
		// One clock tick in each of these states ...
		// baud_counter <= clocks_per_baud - 28'h01;
		r_busy <= 1'b1;
		if (state[3] == 0) // First 8 bits
		begin
			if (state == TXU_BIT_SEVEN)
				state <= (use_parity)? TXU_PARITY:TXU_STOP;
			else
				state <= state + 1;
		end else if (state == TXU_PARITY)
		begin
			state <= TXU_STOP;
		end else if (state == TXU_STOP)
		begin // two stop bit(s)
			if (dblstop)
				state <= TXU_SECOND_STOP;
			else
				state <= TXU_IDLE;
		end else // `TXU_SECOND_STOP and default:
		begin
			state <= TXU_IDLE; // Go back to idle
			// Still r_busy, since we need to wait
			// for the baud clock to finish counting
			// out this last bit.
		end
	end 
	// }}}

	// o_busy
	// {{{
	// This is a wire, designed to be true is we are ever busy above.
	// originally, this was going to be true if we were ever not in the
	// idle state.  The logic has since become more complex, hence we have
	// a register dedicated to this and just copy out that registers value.
	assign	o_busy = (r_busy);
	// }}}

	// r_setup
	// {{{
	// Our setup register.  Accept changes between any pair of transmitted
	// words.  The register itself has many fields to it.  These are
	// broken out up top, and indicate what 1) our baud rate is, 2) our
	// number of stop bits, 3) what type of parity we are using, and 4)
	// the size of our data word.
	initial	r_setup = INITIAL_SETUP;
	always @(posedge i_clk)
	if (!o_busy)
		r_setup <= i_setup;
	// }}}

	// lcl_data
	// {{{
	// This is our working copy of the i_data register which we use
	// when transmitting.  It is only of interest during transmit, and is
	// allowed to be whatever at any other time.  Hence, if r_busy isn't
	// true, we can always set it.  On the one clock where r_busy isn't
	// true and i_wr is, we set it and r_busy is true thereafter.
	// Then, on any zero_baud_counter (i.e. change between baud intervals)
	// we simple logically shift the register right to grab the next bit.
	initial	lcl_data = 8'hff;
	always @(posedge i_clk)
	if (!r_busy)
		lcl_data <= i_data;
	else if (zero_baud_counter)
		lcl_data <= { 1'b0, lcl_data[7:1] };
	// }}}

	// o_uart_tx
	// {{{
	// This is the final result/output desired of this core.  It's all
	// centered about o_uart_tx.  This is what finally needs to follow
	// the UART protocol.
	//
	// Ok, that said, our rules are:
	//	1'b0 on any break condition
	//	1'b0 on a start bit (IDLE, write, and not busy)
	//	lcl_data[0] during any data transfer, but only at the baud
	//		change
	//	PARITY -- During the parity bit.  This depends upon whether or
	//		not the parity bit is fixed, then what it's fixed to,
	//		or changing, and hence what it's calculated value is.
	//	1'b1 at all other times (stop bits, idle, etc)

	initial	o_uart_tx = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_uart_tx <= 1'b1;
	else if ((i_break)||((i_wr)&&(!r_busy)))
		o_uart_tx <= 1'b0;
	else if (zero_baud_counter)
		casez(state)
		4'b0???:	o_uart_tx <= lcl_data[0];
		TXU_PARITY:	o_uart_tx <= calc_parity;
		default:	o_uart_tx <= 1'b1;
		endcase
	// }}}

	// calc_parity
	// {{{
	// Calculate the parity to be placed into the parity bit.  If the
	// parity is fixed, then the parity bit is given by the fixed parity
	// value (r_setup[24]).  Otherwise the parity is given by the GF2
	// sum of all the data bits (plus one for even parity).
	initial	calc_parity = 1'b0;
	always @(posedge i_clk)
	if (!o_busy)
		calc_parity <= i_setup[24];
	else if (fixd_parity)
		calc_parity <= fixdp_value;
	else if (zero_baud_counter)
	begin
		if (state[3] == 0) // First 8 bits of msg
			calc_parity <= calc_parity ^ lcl_data[0];
		else if (state == TXU_IDLE)
			calc_parity <= parity_odd;
	end else if (!r_busy)
		calc_parity <= parity_odd;
	// }}}

	// baud_counter, zero_baud_counter
	// {{{
	// All of the above logic is driven by the baud counter.  Bits must last
	// {{{
	// clocks_per_baud in length, and this baud counter is what we use to
	// make certain of that.
	//
	// The basic logic is this: at the beginning of a bit interval, start
	// the baud counter and set it to count clocks_per_baud.  When it gets
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
	// When (i_wr)&&(!r_busy)&&(state == TXU_IDLE) then we're not only in
	// the idle state, but we also just accepted a command to start writing
	// the next word.  At this point, the baud counter needs to be reset
	// to the number of clocks per baud, and zero_baud_counter set to zero.
	//
	// The logic is a bit twisted here, in that it will only check for the
	// above condition when zero_baud_counter is false--so as to make
	// certain the STOP bit is complete.
	// }}}
	initial	zero_baud_counter = 1'b0;
	initial	baud_counter = 28'h05;
	always @(posedge i_clk)
	begin
		zero_baud_counter <= (baud_counter == 28'h01);
		if ((i_reset)||(i_break))
		begin
			// Give ourselves 16 bauds before being ready
			baud_counter <= break_condition;
			zero_baud_counter <= 1'b0;
		end else if (!zero_baud_counter)
			baud_counter <= baud_counter - 28'h01;
		else if (state == TXU_BREAK)
		begin
			baud_counter <= 0;
			zero_baud_counter <= 1'b1;
		end else if (state == TXU_IDLE)
		begin
			baud_counter <= 28'h0;
			zero_baud_counter <= 1'b1;
			if ((i_wr)&&(!r_busy))
			begin
				baud_counter <= { 4'h0, i_setup[23:0]} - 28'h01;
				zero_baud_counter <= 1'b0;
			end
		end else if (last_state)
			baud_counter <= clocks_per_baud - 28'h02;
		else
			baud_counter <= clocks_per_baud - 28'h01;
	end
	// }}}

	// last_state
	// {{{
	initial	last_state = 1'b0;
	always @(posedge i_clk)
	if (dblstop)
		last_state <= (state == TXU_SECOND_STOP);
	else
		last_state <= (state == TXU_STOP);
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_parity_odd, data_bits };
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
	// Declarations
	// {{{
	reg		fsv_parity;
	reg	[30:0]	fsv_setup;
	reg	[7:0]	fsv_data;
	reg		f_past_valid;
	//
	// Our various sequence data declarations
	reg	[5:0]	f_five_seq;
	reg	[6:0]	f_six_seq;
	reg	[7:0]	f_seven_seq;
	reg	[8:0]	f_eight_seq;
	reg	[2:0]	f_stop_seq;	// parity bit, stop bit, double stop bit
	// }}}

	initial	f_past_valid = 1'b0;
	always @(posedge  i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if ((i_wr)&&(!o_busy))
		fsv_data <= i_data;

	initial	fsv_setup = INITIAL_SETUP;
	always @(posedge i_clk)
	if (!o_busy)
		fsv_setup <= i_setup;

	always @(*)
		assert(r_setup == fsv_setup);


	always @(posedge i_clk)
		assert(zero_baud_counter == (baud_counter == 0));

	always @(*)
	if (!o_busy)
		assert(zero_baud_counter);

	/*
	*
	* Will only pass if !i_break && !i_reset, otherwise the setup can
	* change in the middle of this operation
	*
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(i_break))
			&&(($past(o_busy))||($past(i_wr))))
		assert(baud_counter <= { fsv_setup[23:0], 4'h0 });
	*/

	// A single baud interval
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(zero_baud_counter))
		&&(!$past(i_reset))&&(!$past(i_break)))
	begin
		assert($stable(o_uart_tx));
		assert($stable(state));
		assert($stable(lcl_data));
		if ((state != TXU_IDLE)&&(state != TXU_BREAK))
			assert($stable(calc_parity));
		assert(baud_counter == $past(baud_counter)-1'b1);
	end


	//
	// One byte transmitted
	//
	// DATA = the byte that is sent
	// CKS  = the number of clocks per bit
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Five bit data
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_five_seq = 0;
	always @(posedge i_clk)
	if ((i_reset)||(i_break))
		f_five_seq = 0;
	else if ((state == TXU_IDLE)&&(i_wr)&&(!o_busy)
			&&(i_data_bits == 2'b11)) // five data bits
		f_five_seq <= 1;
	else if (zero_baud_counter)
		f_five_seq <= f_five_seq << 1;

	always @(*)
	if (|f_five_seq)
	begin
		assert(fsv_setup[29:28] == data_bits);
		assert(data_bits == 2'b11);
		assert(baud_counter < fsv_setup[23:0]);

		assert(1'b0 == |f_six_seq);
		assert(1'b0 == |f_seven_seq);
		assert(1'b0 == |f_eight_seq);
		assert(r_busy);
		assert(state > 4'h2);
	end

	always @(*)
	case(f_five_seq)
	6'h00: begin assert(1); end
	6'h01: begin
		assert(state == 4'h3);
		assert(o_uart_tx == 1'b0);
		assert(lcl_data[4:0] == fsv_data[4:0]);
		if (!fixd_parity)
			assert(calc_parity == parity_odd);
	end
	6'h02: begin
		assert(state == 4'h4);
		assert(o_uart_tx == fsv_data[0]);
		assert(lcl_data[3:0] == fsv_data[4:1]);
		if (!fixd_parity)
			assert(calc_parity == fsv_data[0] ^ parity_odd);
	end
	6'h04: begin
		assert(state == 4'h5);
		assert(o_uart_tx == fsv_data[1]);
		assert(lcl_data[2:0] == fsv_data[4:2]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[1:0]) ^ parity_odd);
	end
	6'h08: begin
		assert(state == 4'h6);
		assert(o_uart_tx == fsv_data[2]);
		assert(lcl_data[1:0] == fsv_data[4:3]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[2:0]) ^ parity_odd);
	end
	6'h10: begin
		assert(state == 4'h7);
		assert(o_uart_tx == fsv_data[3]);
		assert(lcl_data[0] == fsv_data[4]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[3:0]) ^ parity_odd);
	end
	6'h20: begin
		if (use_parity)
			assert(state == 4'h8);
		else
			assert(state == 4'h9);
		assert(o_uart_tx == fsv_data[4]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[4:0]) ^ parity_odd);
	end
	default: begin assert(0); end
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Six bit data
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_six_seq = 0;
	always @(posedge i_clk)
	if ((i_reset)||(i_break))
		f_six_seq = 0;
	else if ((state == TXU_IDLE)&&(i_wr)&&(!o_busy)
			&&(i_data_bits == 2'b10)) // six data bits
		f_six_seq <= 1;
	else if (zero_baud_counter)
		f_six_seq <= f_six_seq << 1;

	always @(*)
	if (|f_six_seq)
	begin
		assert(fsv_setup[29:28] == 2'b10);
		assert(fsv_setup[29:28] == data_bits);
		assert(baud_counter < fsv_setup[23:0]);

		assert(1'b0 == |f_five_seq);
		assert(1'b0 == |f_seven_seq);
		assert(1'b0 == |f_eight_seq);
		assert(r_busy);
		assert(state > 4'h1);
	end

	always @(*)
	case(f_six_seq)
	7'h00: begin assert(1); end
	7'h01: begin
		assert(state == 4'h2);
		assert(o_uart_tx == 1'b0);
		assert(lcl_data[5:0] == fsv_data[5:0]);
		if (!fixd_parity)
			assert(calc_parity == parity_odd);
	end
	7'h02: begin
		assert(state == 4'h3);
		assert(o_uart_tx == fsv_data[0]);
		assert(lcl_data[4:0] == fsv_data[5:1]);
		if (!fixd_parity)
			assert(calc_parity == fsv_data[0] ^ parity_odd);
	end
	7'h04: begin
		assert(state == 4'h4);
		assert(o_uart_tx == fsv_data[1]);
		assert(lcl_data[3:0] == fsv_data[5:2]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[1:0]) ^ parity_odd);
	end
	7'h08: begin
		assert(state == 4'h5);
		assert(o_uart_tx == fsv_data[2]);
		assert(lcl_data[2:0] == fsv_data[5:3]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[2:0]) ^ parity_odd);
	end
	7'h10: begin
		assert(state == 4'h6);
		assert(o_uart_tx == fsv_data[3]);
		assert(lcl_data[1:0] == fsv_data[5:4]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[3:0]) ^ parity_odd);
	end
	7'h20: begin
		assert(state == 4'h7);
		assert(lcl_data[0] == fsv_data[5]);
		assert(o_uart_tx == fsv_data[4]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[4:0]) ^ parity_odd));
	end
	7'h40: begin
		if (use_parity)
			assert(state == 4'h8);
		else
			assert(state == 4'h9);
		assert(o_uart_tx == fsv_data[5]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[5:0]) ^ parity_odd));
	end
	default: begin if (f_past_valid) assert(0); end
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Seven bit data
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_seven_seq = 0;
	always @(posedge i_clk)
	if ((i_reset)||(i_break))
		f_seven_seq = 0;
	else if ((state == TXU_IDLE)&&(i_wr)&&(!o_busy)
			&&(i_data_bits == 2'b01)) // seven data bits
		f_seven_seq <= 1;
	else if (zero_baud_counter)
		f_seven_seq <= f_seven_seq << 1;

	always @(*)
	if (|f_seven_seq)
	begin
		assert(fsv_setup[29:28] == 2'b01);
		assert(fsv_setup[29:28] == data_bits);
		assert(baud_counter < fsv_setup[23:0]);

		assert(1'b0 == |f_five_seq);
		assert(1'b0 == |f_six_seq);
		assert(1'b0 == |f_eight_seq);
		assert(r_busy);
		assert(state != 4'h0);
	end

	always @(*)
	case(f_seven_seq)
	8'h00: begin assert(1); end
	8'h01: begin
		assert(state == 4'h1);
		assert(o_uart_tx == 1'b0);
		assert(lcl_data[6:0] == fsv_data[6:0]);
		if (!fixd_parity)
			assert(calc_parity == parity_odd);
	end
	8'h02: begin
		assert(state == 4'h2);
		assert(o_uart_tx == fsv_data[0]);
		assert(lcl_data[5:0] == fsv_data[6:1]);
		if (!fixd_parity)
			assert(calc_parity == fsv_data[0] ^ parity_odd);
	end
	8'h04: begin
		assert(state == 4'h3);
		assert(o_uart_tx == fsv_data[1]);
		assert(lcl_data[4:0] == fsv_data[6:2]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[1:0]) ^ parity_odd);
	end
	8'h08: begin
		assert(state == 4'h4);
		assert(o_uart_tx == fsv_data[2]);
		assert(lcl_data[3:0] == fsv_data[6:3]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[2:0]) ^ parity_odd);
	end
	8'h10: begin
		assert(state == 4'h5);
		assert(o_uart_tx == fsv_data[3]);
		assert(lcl_data[2:0] == fsv_data[6:4]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[3:0]) ^ parity_odd);
	end
	8'h20: begin
		assert(state == 4'h6);
		assert(o_uart_tx == fsv_data[4]);
		assert(lcl_data[1:0] == fsv_data[6:5]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[4:0]) ^ parity_odd));
	end
	8'h40: begin
		assert(state == 4'h7);
		assert(lcl_data[0] == fsv_data[6]);
		assert(o_uart_tx == fsv_data[5]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[5:0]) ^ parity_odd));
	end
	8'h80: begin
		if (use_parity)
			assert(state == 4'h8);
		else
			assert(state == 4'h9);
		assert(o_uart_tx == fsv_data[6]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[6:0]) ^ parity_odd));
	end
	default: begin if (f_past_valid) assert(0); end
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Eight bit data
	// {{{
	////////////////////////////////////////////////////////////////////////
	initial	f_eight_seq = 0;
	always @(posedge i_clk)
	if ((i_reset)||(i_break))
		f_eight_seq = 0;
	else if ((state == TXU_IDLE)&&(i_wr)&&(!o_busy)
			&&(i_data_bits == 2'b00)) // Eight data bits
		f_eight_seq <= 1;
	else if (zero_baud_counter)
		f_eight_seq <= f_eight_seq << 1;

	always @(*)
	if (|f_eight_seq)
	begin
		assert(fsv_setup[29:28] == 2'b00);
		assert(fsv_setup[29:28] == data_bits);
		assert(baud_counter < { 6'h0, fsv_setup[23:0]});

		assert(1'b0 == |f_five_seq);
		assert(1'b0 == |f_six_seq);
		assert(1'b0 == |f_seven_seq);
		assert(r_busy);
	end

	always @(*)
	case(f_eight_seq)
	9'h000: begin assert(1); end
	9'h001: begin
		assert(state == 4'h0);
		assert(o_uart_tx == 1'b0);
		assert(lcl_data[7:0] == fsv_data[7:0]);
		if (!fixd_parity)
			assert(calc_parity == parity_odd);
	end
	9'h002: begin
		assert(state == 4'h1);
		assert(o_uart_tx == fsv_data[0]);
		assert(lcl_data[6:0] == fsv_data[7:1]);
		if (!fixd_parity)
			assert(calc_parity == fsv_data[0] ^ parity_odd);
	end
	9'h004: begin
		assert(state == 4'h2);
		assert(o_uart_tx == fsv_data[1]);
		assert(lcl_data[5:0] == fsv_data[7:2]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[1:0]) ^ parity_odd);
	end
	9'h008: begin
		assert(state == 4'h3);
		assert(o_uart_tx == fsv_data[2]);
		assert(lcl_data[4:0] == fsv_data[7:3]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[2:0]) ^ parity_odd);
	end
	9'h010: begin
		assert(state == 4'h4);
		assert(o_uart_tx == fsv_data[3]);
		assert(lcl_data[3:0] == fsv_data[7:4]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[3:0]) ^ parity_odd);
	end
	9'h020: begin
		assert(state == 4'h5);
		assert(o_uart_tx == fsv_data[4]);
		assert(lcl_data[2:0] == fsv_data[7:5]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[4:0]) ^ parity_odd);
	end
	9'h040: begin
		assert(state == 4'h6);
		assert(o_uart_tx == fsv_data[5]);
		assert(lcl_data[1:0] == fsv_data[7:6]);
		if (!fixd_parity)
			assert(calc_parity == (^fsv_data[5:0]) ^ parity_odd);
	end
	9'h080: begin
		assert(state == 4'h7);
		assert(o_uart_tx == fsv_data[6]);
		assert(lcl_data[0] == fsv_data[7]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[6:0]) ^ parity_odd));
	end
	9'h100: begin
		if (use_parity)
			assert(state == 4'h8);
		else
			assert(state == 4'h9);
		assert(o_uart_tx == fsv_data[7]);
		if (!fixd_parity)
			assert(calc_parity == ((^fsv_data[7:0]) ^ parity_odd));
	end
	default: begin if (f_past_valid) assert(0); end
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Combined properties for all of the data sequences
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	always @(posedge i_clk)
	if (((|f_five_seq[5:0]) || (|f_six_seq[6:0]) || (|f_seven_seq[7:0])
			|| (|f_eight_seq[8:0]))
		&& ($past(zero_baud_counter)))
		assert(baud_counter == { 4'h0, fsv_setup[23:0] }-1);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The stop sequence
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// This consists of any parity bit, as well as one or two stop bits
	//
	initial	f_stop_seq = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(i_break))
		f_stop_seq <= 0;
	else if (zero_baud_counter)
	begin
		f_stop_seq <= 0;
		if (f_stop_seq[0]) // Coming from a parity bit
		begin
			if (dblstop)
				f_stop_seq[1] <= 1'b1;
			else
				f_stop_seq[2] <= 1'b1;
		end

		if (f_stop_seq[1])
			f_stop_seq[2] <= 1'b1;

		if (f_eight_seq[8] | f_seven_seq[7] | f_six_seq[6]
			| f_five_seq[5])
		begin
			if (use_parity)
				f_stop_seq[0] <= 1'b1;
			else if (dblstop)
				f_stop_seq[1] <= 1'b1;
			else
				f_stop_seq[2] <= 1'b1;
		end
	end

	always @(*)
	if (|f_stop_seq)
	begin
		assert(1'b0 == |f_five_seq[4:0]);
		assert(1'b0 == |f_six_seq[5:0]);
		assert(1'b0 == |f_seven_seq[6:0]);
		assert(1'b0 == |f_eight_seq[7:0]);

		assert(r_busy);
	end

	always @(*)
	if (f_stop_seq[0])
	begin
		// 9 if dblstop and use_parity
		if (dblstop)
			assert(state == TXU_STOP);
		else
			assert(state == TXU_STOP);
		assert(use_parity);
		assert(o_uart_tx == fsv_parity);
	end
		
	always @(*)
	if (f_stop_seq[1])
	begin
		// if (!use_parity)
		assert(state == TXU_SECOND_STOP);
		assert(dblstop);
		assert(o_uart_tx);
	end

	always @(*)
	if (f_stop_seq[2])
	begin
		assert(state == 4'hf);
		assert(o_uart_tx);
		assert(baud_counter < fsv_setup[23:0]-1'b1);
	end
		

	always @(*)
	if (fsv_setup[25])
		fsv_parity <= fsv_setup[24];
	else
		case(fsv_setup[29:28])
		2'b00: fsv_parity = (^fsv_data[7:0]) ^ fsv_setup[24];
		2'b01: fsv_parity = (^fsv_data[6:0]) ^ fsv_setup[24];
		2'b10: fsv_parity = (^fsv_data[5:0]) ^ fsv_setup[24];
		2'b11: fsv_parity = (^fsv_data[4:0]) ^ fsv_setup[24];
		endcase
	// }}}
	//////////////////////////////////////////////////////////////////////
	//
	// The break sequence
	// {{{
	//////////////////////////////////////////////////////////////////////
	reg	[1:0]	f_break_seq;

	initial	f_break_seq = 2'b00;
	always @(posedge i_clk)
	if (i_reset)
		f_break_seq <= 2'b00;
	else if (i_break)
		f_break_seq <= 2'b01;
	else if (!zero_baud_counter)
		f_break_seq <= { |f_break_seq, 1'b0 };
	else
		f_break_seq <= 0;

	always @(posedge i_clk)
	if (f_break_seq[0])
		assert(baud_counter == { $past(fsv_setup[23:0]), 4'h0 });
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(f_break_seq[1]))&&(state != TXU_BREAK))
	begin
		assert(state == TXU_IDLE);
		assert(o_uart_tx == 1'b1);
	end

	always @(*)
	if (|f_break_seq)
	begin
		assert(state == TXU_BREAK);
		assert(r_busy);
		assert(o_uart_tx == 1'b0);
	end
	// }}}
	//////////////////////////////////////////////////////////////////////
	//
	// Properties for use during induction if we are made a submodule of
	// the rxuart
	// {{{
	//////////////////////////////////////////////////////////////////////
	//
	// Need enough bits for reset (24+4) plus enough bits for all of the
	// various characters, 24+4, so 24+5 is a minimum of this counter
	//
`ifndef	TXUART
	reg	[28:0]		f_counter;
	initial	f_counter = 0;
	always @(posedge i_clk)
	if (!o_busy)
		f_counter <= 1'b0;
	else
		f_counter <= f_counter + 1'b1;

	always @(*)
	if (f_five_seq[0]|f_six_seq[0]|f_seven_seq[0]|f_eight_seq[0])
		// {{{
		assert(f_counter == (fsv_setup[23:0] - baud_counter - 1));
		// }}}
	else if (f_five_seq[1]|f_six_seq[1]|f_seven_seq[1]|f_eight_seq[1])
		// {{{
		assert(f_counter == ({4'h0, fsv_setup[23:0], 1'b0} - baud_counter - 1));
		// }}}
	else if (f_five_seq[2]|f_six_seq[2]|f_seven_seq[2]|f_eight_seq[2])
		// {{{
		assert(f_counter == ({4'h0, fsv_setup[23:0], 1'b0}
				+{5'h0, fsv_setup[23:0]}
				- baud_counter - 1));
		// }}}
	else if (f_five_seq[3]|f_six_seq[3]|f_seven_seq[3]|f_eight_seq[3])
		// {{{
		assert(f_counter == ({3'h0, fsv_setup[23:0], 2'b0}
				- baud_counter - 1));
		// }}}
	else if (f_five_seq[4]|f_six_seq[4]|f_seven_seq[4]|f_eight_seq[4])
		// {{{
		assert(f_counter == ({3'h0, fsv_setup[23:0], 2'b0}
				+{5'h0, fsv_setup[23:0]}
				- baud_counter - 1));
		// }}}
	else if (f_five_seq[5]|f_six_seq[5]|f_seven_seq[5]|f_eight_seq[5])
		// {{{
		assert(f_counter == ({3'h0, fsv_setup[23:0], 2'b0}
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 1));
		// }}}
	else if (f_six_seq[6]|f_seven_seq[6]|f_eight_seq[6])
		// {{{
		assert(f_counter == ({3'h0, fsv_setup[23:0], 2'b0}
				+{5'h0, fsv_setup[23:0]}
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 1));
		// }}}
	else if (f_seven_seq[7]|f_eight_seq[7])
		// {{{
		assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}	// 8
				- baud_counter - 1));
		// }}}
	else if (f_eight_seq[8])
		// {{{
		assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}	// 9
				+{5'h0, fsv_setup[23:0]}
				- baud_counter - 1));
		// }}}
	else if (f_stop_seq[0] || (!use_parity && f_stop_seq[1]))
	begin
		// {{{
		// Parity bit, or first of two stop bits
		case(data_bits)
		2'b00: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{4'h0, fsv_setup[23:0], 1'b0} // 10
				- baud_counter - 1));
		2'b01: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]} // 9
				- baud_counter - 1));
		2'b10: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				- baud_counter - 1)); // 8
		2'b11: assert(f_counter == ({3'h0, fsv_setup[23:0], 2'b0}
				+{5'h0, fsv_setup[23:0]}	// 7
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 1));
		endcase
		// }}}
	end else if (!use_parity && !dblstop  && f_stop_seq[2])
	begin
		// {{{
		// No parity, single stop bit
		// Different from the one above, since the last counter is has
		// one fewer items within it
		case(data_bits)
		2'b00: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{4'h0, fsv_setup[23:0], 1'b0} // 10
				- baud_counter - 2));
		2'b01: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]} // 9
				- baud_counter - 2));
		2'b10: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				- baud_counter - 2)); // 8
		2'b11: assert(f_counter == ({3'h0, fsv_setup[23:0], 2'b0}
				+{5'h0, fsv_setup[23:0]}	// 7
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 2));
		endcase
		// }}}
	end else if (f_stop_seq[1])
	begin
		// {{{
		// Parity and the first of two stop bits
		assert(dblstop && use_parity);
		case(data_bits)
		2'b00: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]}	// 11
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 1));
		2'b01: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{4'h0, fsv_setup[23:0], 1'b0} // 10
				- baud_counter - 1));
		2'b10: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]}	// 9
				- baud_counter - 1));
		2'b11: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				- baud_counter - 1));		// 8
		endcase
		// }}}
	end else if ((dblstop ^ use_parity) && f_stop_seq[2])
	begin
		// {{{
		// Parity and one stop bit
		// assert(!dblstop && use_parity);
		case(data_bits)
		2'b00: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]}	// 11
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 2));
		2'b01: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{4'h0, fsv_setup[23:0], 1'b0} // 10
				- baud_counter - 2));
		2'b10: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]}	// 9
				- baud_counter - 2));
		2'b11: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				- baud_counter - 2));		// 8
		endcase
		// }}}
	end else if (f_stop_seq[2])
	begin
		// {{{
		assert(dblstop);
		assert(use_parity);
		// Parity and two stop bits
		case(data_bits)
		2'b00: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{3'h0, fsv_setup[23:0], 2'b00}	// 12
				- baud_counter - 2));
		2'b01: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]}	// 11
				+{4'h0, fsv_setup[23:0], 1'b0}
				- baud_counter - 2));
		2'b10: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{4'h0, fsv_setup[23:0], 1'b0} // 10
				- baud_counter - 2));
		2'b11: assert(f_counter == ({2'h0, fsv_setup[23:0], 3'b0}
				+{5'h0, fsv_setup[23:0]}	// 9
				- baud_counter - 2));
		endcase
		// }}}
	end
`endif
	// }}}
	//////////////////////////////////////////////////////////////////////
	//
	// Other properties, not necessarily associated with any sequences
	//
	//////////////////////////////////////////////////////////////////////
	always @(*)
		assert((state < 4'hb)||(state >= 4'he));
	//////////////////////////////////////////////////////////////////////
	//
	// Careless/limiting assumption section
	//
	//////////////////////////////////////////////////////////////////////
	always @(*)
		assume(i_setup[23:0] > 2);
	always @(*)
		assert(fsv_setup[23:0] > 2);

`endif	// FORMAL
// }}}
endmodule

