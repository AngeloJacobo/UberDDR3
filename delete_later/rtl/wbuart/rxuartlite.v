////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxuartlite.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Receive and decode inputs from a single UART line.
//
//
//	To interface with this module, connect it to your system clock,
//	and a UART input.  Set the parameter to the number of clocks per
//	baud.  When data becomes available, the o_wr line will be asserted
//	for one clock cycle.
//
//	This interface only handles 8N1 serial port communications.  It does
//	not handle the break, parity, or frame error conditions.
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
module rxuartlite #(
		// {{{
		parameter			TIMER_BITS = 10,
`ifdef	FORMAL
		parameter  [(TIMER_BITS-1):0]	CLOCKS_PER_BAUD = 16, // Necessary for formal proof
`else
		parameter  [(TIMER_BITS-1):0]	CLOCKS_PER_BAUD = 868,	// 115200 Baud at 100MHz
`endif
		localparam			TB = TIMER_BITS,
		//
		localparam [3:0]	RXUL_BIT_ZERO  = 4'h0,
		// Verilator lint_off UNUSED
		// These are used by the formal solver
		localparam [3:0]	RXUL_BIT_ONE   = 4'h1,
		localparam [3:0]	RXUL_BIT_TWO   = 4'h2,
		localparam [3:0]	RXUL_BIT_THREE = 4'h3,
		localparam [3:0]	RXUL_BIT_FOUR  = 4'h4,
		localparam [3:0]	RXUL_BIT_FIVE  = 4'h5,
		localparam [3:0]	RXUL_BIT_SIX   = 4'h6,
		localparam [3:0]	RXUL_BIT_SEVEN = 4'h7,
		// Verilator lint_on  UNUSED
		localparam [3:0]	RXUL_STOP      = 4'h8,
		localparam [3:0]	RXUL_WAIT      = 4'h9,
		localparam [3:0]	RXUL_IDLE      = 4'hf
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_uart_rx,
		output	reg		o_wr,
		output	reg	[7:0]	o_data
		// }}}
	);

	// Signal/register declarations
	// {{{
	wire	[(TB-1):0]	half_baud;
	reg	[3:0]		state;

	assign	half_baud = { 1'b0, CLOCKS_PER_BAUD[(TB-1):1] };
	reg	[(TB-1):0]	baud_counter;
	reg			zero_baud_counter;

	reg			q_uart, qq_uart, ck_uart;
	reg	[(TB-1):0]	chg_counter;
	reg			half_baud_time;
	reg	[7:0]		data_reg;
	// }}}

	// ck_uart
	// {{{
	// Since this is an asynchronous receiver, we need to register our
	// input a couple of clocks over to avoid any problems with 
	// metastability.  We do that here, and then ignore all but the
	// ck_uart wire.
	initial	q_uart  = 1'b1;
	initial	qq_uart = 1'b1;
	initial	ck_uart = 1'b1;
	always @(posedge i_clk)
		{ ck_uart, qq_uart, q_uart } <= { qq_uart, q_uart, i_uart_rx };
	// }}}

	// chg_counter
	// {{{
	// Keep track of the number of clocks since the last change.
	//
	// This is used to determine if we are in either a break or an idle
	// condition, as discussed further below.
	initial	chg_counter = {(TB){1'b1}};
	always @(posedge i_clk)
	if (qq_uart != ck_uart)
		chg_counter <= 0;
	else if (chg_counter != { (TB){1'b1} })
		chg_counter <= chg_counter + 1;
	// }}}

	// half_baud_time
	// {{{
	// Are we in the middle of a baud iterval?  Specifically, are we
	// in the middle of a start bit?  Set this to high if so.  We'll use
	// this within our state machine to transition out of the IDLE
	// state.
	initial	half_baud_time = 0;
	always @(posedge i_clk)
		half_baud_time <= (!ck_uart)&&(chg_counter >= half_baud-1'b1-1'b1);
	// }}}

	// state
	// {{{
	initial	state = RXUL_IDLE;
	always @(posedge i_clk)
	if (state == RXUL_IDLE)
	begin // Idle state, independent of baud counter
		// {{{
		// By default, just stay in the IDLE state
		state <= RXUL_IDLE;
		if ((!ck_uart)&&(half_baud_time))
			// UNLESS: We are in the center of a valid
			// start bit
			state <= RXUL_BIT_ZERO;
		// }}}
	end else if ((state >= RXUL_WAIT)&&(ck_uart))
		state <= RXUL_IDLE;
	else if (zero_baud_counter)
	begin
		// {{{
		if (state <= RXUL_STOP)
			// Data arrives least significant bit first.
			// By the time this is clocked in, it's what
			// you'll have.
			state <= state + 1;
		// }}}
	end
	// }}}

	// data_reg
	// {{{
	// Data bit capture logic.
	//
	// This is drastically simplified from the state machine above, based
	// upon: 1) it doesn't matter what it is until the end of a captured
	// byte, and 2) the data register will flush itself of any invalid
	// data in all other cases.  Hence, let's keep it real simple.
	always @(posedge i_clk)
	if ((zero_baud_counter)&&(state != RXUL_STOP))
		data_reg <= { qq_uart, data_reg[7:1] };
	// }}}

	// o_wr, o_data
	// {{{
	// Our data bit logic doesn't need nearly the complexity of all that
	// work above.  Indeed, we only need to know if we are at the end of
	// a stop bit, in which case we copy the data_reg into our output
	// data register, o_data, and tell others (for one clock) that data is
	// available.
	//
	initial	o_wr = 1'b0;
	initial	o_data = 8'h00;
	always @(posedge i_clk)
	if ((zero_baud_counter)&&(state == RXUL_STOP)&&(ck_uart))
	begin
		o_wr   <= 1'b1;
		o_data <= data_reg;
	end else
		o_wr   <= 1'b0;
	// }}}

	// baud_counter -- The baud counter
	// {{{
	// This is used as a "clock divider" if you will, but the clock needs
	// to be reset before any byte can be decoded.  In all other respects,
	// we set ourselves up for CLOCKS_PER_BAUD counts between baud
	// intervals.
	initial	baud_counter = 0;
	always @(posedge i_clk)
	if (((state==RXUL_IDLE))&&(!ck_uart)&&(half_baud_time))
		baud_counter <= CLOCKS_PER_BAUD-1'b1;
	else if (state == RXUL_WAIT)
		baud_counter <= 0;
	else if ((zero_baud_counter)&&(state < RXUL_STOP))
		baud_counter <= CLOCKS_PER_BAUD-1'b1;
	else if (!zero_baud_counter)
		baud_counter <= baud_counter-1'b1;
	// }}}

	// zero_baud_counter
	// {{{
	// Rather than testing whether or not (baud_counter == 0) within our
	// (already too complicated) state transition tables, we use
	// zero_baud_counter to pre-charge that test on the clock
	// before--cleaning up some otherwise difficult timing dependencies.
	initial	zero_baud_counter = 1'b1;
	always @(posedge i_clk)
	if ((state == RXUL_IDLE)&&(!ck_uart)&&(half_baud_time))
		zero_baud_counter <= 1'b0;
	else if (state == RXUL_WAIT)
		zero_baud_counter <= 1'b1;
	else if ((zero_baud_counter)&&(state < RXUL_STOP))
		zero_baud_counter <= 1'b0;
	else if (baud_counter == 1)
		zero_baud_counter <= 1'b1;
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
	// Declarations
	// {{{
`ifdef	FORMAL
`define	FORMAL_VERILATOR
`else
`ifdef	VERILATOR
`define	FORMAL_VERILATOR
`endif
`endif

`ifdef	FORMAL
	localparam	F_CKRES = 10;

	(* anyseq *)	wire			f_tx_start;
	(* anyconst *)	wire	[(F_CKRES-1):0]	f_tx_step;
	(* gclk *)	wire			gbl_clk;
	reg			f_tx_zclk;
	reg	[(TB-1):0]	f_tx_timer;
	wire	[7:0]		f_rx_newdata;
	reg	[TB-1:0]	f_tx_baud;
	wire			f_tx_zbaud;

	wire	[(TB-1):0]	f_max_baud_difference;
	reg	[(TB-1):0]	f_baud_difference;
	reg	[(TB+3):0]	f_tx_count, f_rx_count;
	(* anyseq *) wire	[7:0]		f_tx_data;

	wire			f_txclk;
	reg	[1:0]		f_rx_clock;
	reg	[(F_CKRES-1):0]	f_tx_clock;
	reg			f_past_valid, f_past_valid_tx;

	reg	[9:0]	f_tx_reg;
	reg		f_tx_busy;

	// }}}

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	f_rx_clock = 3'h0;
	always @(posedge gbl_clk)
		f_rx_clock <= f_rx_clock + 1'b1;

	always @(*)
		assume(i_clk == f_rx_clock[1]);


	////////////////////////////////////////////////////////////////////////
	//
	// Assume a transmitted signal
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// First, calculate the transmit clock
	localparam [(F_CKRES-1):0] F_MIDSTEP = { 2'b01, {(F_CKRES-2){1'b0}} };
	//
	// Need to allow us to slip by half a baud clock over 10 baud intervals
	//
	// (F_STEP / (2^F_CKRES)) * (CLOCKS_PER_BAUD)*10 < CLOCKS_PER_BAUD/2
	// F_STEP * 2 * 10 < 2^F_CKRES
	localparam [(F_CKRES-1):0] F_HALFSTEP= F_MIDSTEP/32;
	localparam [(F_CKRES-1):0] F_MINSTEP = F_MIDSTEP - F_HALFSTEP + 1;
	localparam [(F_CKRES-1):0] F_MAXSTEP = F_MIDSTEP + F_HALFSTEP - 1;

	initial assert(F_MINSTEP <= F_MIDSTEP);
	initial assert(F_MIDSTEP <= F_MAXSTEP);

	//	assume((f_tx_step >= F_MINSTEP)&&(f_tx_step <= F_MAXSTEP));
	//
	//
	always @(*) assume((f_tx_step == F_MINSTEP)
			||(f_tx_step == F_MIDSTEP)
			||(f_tx_step == F_MAXSTEP));

	always @(posedge gbl_clk)
		f_tx_clock <= f_tx_clock + f_tx_step;

	assign	f_txclk = f_tx_clock[F_CKRES-1];
	// 
	initial	f_past_valid_tx = 1'b0;
	always @(posedge f_txclk)
		f_past_valid_tx <= 1'b1;

	initial	assume(i_uart_rx);

	////////////////////////////////////////////////////////////////////////
	//
	// The simulated timing generator

	always @(*)
	if (f_tx_busy)
		assume(!f_tx_start);

	initial	f_tx_baud = 0;
	always @(posedge f_txclk)
	if (f_tx_zbaud && (f_tx_busy || f_tx_start))
		f_tx_baud <= CLOCKS_PER_BAUD-1;
	else if (!f_tx_zbaud)
		f_tx_baud <= f_tx_baud - 1;

	always @(*)
		assert(f_tx_baud < CLOCKS_PER_BAUD);

	always @(*)
	if (!f_tx_busy)
		assert(f_tx_baud == 0);

	assign	f_tx_zbaud = (f_tx_baud == 0);

	// But only if we aren't busy
	initial	assume(f_tx_data == 0);
	always @(posedge f_txclk)
	if ((!f_tx_zbaud)||(f_tx_busy)||(!f_tx_start))
		assume(f_tx_data == $past(f_tx_data));

	// Force the data to change on a clock only
	always @(posedge gbl_clk)
	if ((f_past_valid)&&(!$rose(f_txclk)))
		assume($stable(f_tx_data));
	else if (f_tx_busy)
		assume($stable(f_tx_data));

	//
	always @(posedge gbl_clk)
	if ((!f_past_valid)||(!$rose(f_txclk)))
	begin
		assume($stable(f_tx_start));
		assume($stable(f_tx_data));
	end

	//
	//
	//

	// Here's the transmitter itself (roughly)
	initial	f_tx_busy   = 1'b0;
	initial	f_tx_reg    = 0;
	always @(posedge f_txclk)
	if (!f_tx_zbaud)
	begin
		assert(f_tx_busy);
	end else begin
		f_tx_reg  <= { 1'b0, f_tx_reg[9:1] };
		if (f_tx_start)
			f_tx_reg <= { 1'b1, f_tx_data, 1'b0 };
	end

	// Create a busy flag that we'll use
	always @(*)
	if (!f_tx_zbaud)
		f_tx_busy <= 1'b1;
	else if (|f_tx_reg)
		f_tx_busy <= 1'b1;
	else
		f_tx_busy <= 1'b0;

	//
	// Tie the TX register to the TX data
	always @(posedge f_txclk)
	if (f_tx_reg[9])
	begin
		assert(f_tx_reg[8:0] == { f_tx_data, 1'b0 });
	end else if (f_tx_reg[8])
	begin
		assert(f_tx_reg[7:0] == f_tx_data[7:0] );
	end else if (f_tx_reg[7])
	begin
		assert(f_tx_reg[6:0] == f_tx_data[7:1] );
	end else if (f_tx_reg[6])
	begin
		assert(f_tx_reg[5:0] == f_tx_data[7:2] );
	end else if (f_tx_reg[5])
	begin
		assert(f_tx_reg[4:0] == f_tx_data[7:3] );
	end else if (f_tx_reg[4])
	begin
		assert(f_tx_reg[3:0] == f_tx_data[7:4] );
	end else if (f_tx_reg[3])
	begin
		assert(f_tx_reg[2:0] == f_tx_data[7:5] );
	end else if (f_tx_reg[2])
	begin
		assert(f_tx_reg[1:0] == f_tx_data[7:6] );
	end else if (f_tx_reg[1])
	begin
		assert(f_tx_reg[0] == f_tx_data[7]);
	end

	// Our counter since we start
	initial	f_tx_count = 0;
	always @(posedge f_txclk)
	if (!f_tx_busy)
		f_tx_count <= 0;
	else
		f_tx_count <= f_tx_count + 1'b1;

	always @(*)
	if (f_tx_reg == 10'h0)
		assume(i_uart_rx);
	else
		assume(i_uart_rx == f_tx_reg[0]);

	//
	// Make sure the absolute transmit clock timer matches our state
	//
	always @(posedge f_txclk)
	if (!f_tx_busy)
	begin
		if ((!f_past_valid_tx)||(!$past(f_tx_busy)))
			assert(f_tx_count == 0);
	end else if (f_tx_reg[9])
	begin
		assert(f_tx_count ==
				    CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[8])
	begin
		assert(f_tx_count ==
				2 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[7])
	begin
		assert(f_tx_count ==
				3 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[6])
	begin
		assert(f_tx_count ==
				4 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[5])
	begin
		assert(f_tx_count ==
				5 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[4])
	begin
		assert(f_tx_count ==
				6 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[3])
	begin
		assert(f_tx_count ==
				7 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[2])
	begin
		assert(f_tx_count ==
				8 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[1])
	begin
		assert(f_tx_count ==
				9 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else if (f_tx_reg[0])
	begin
		assert(f_tx_count ==
				10 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end else begin
		assert(f_tx_count ==
				11 * CLOCKS_PER_BAUD -1 -f_tx_baud);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Receiver
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Count RX clocks since the start of the first stop bit, measured in
	// rx clocks
	initial	f_rx_count = 0;
	always @(posedge i_clk)
	if (state == RXUL_IDLE)
		f_rx_count = (!ck_uart) ? (chg_counter+2) : 0;
	else
		f_rx_count <= f_rx_count + 1'b1;

	always @(posedge i_clk)
	case(state)
	0: assert(f_rx_count == half_baud + (CLOCKS_PER_BAUD-baud_counter));
	1: assert(f_rx_count == half_baud + 2 * CLOCKS_PER_BAUD
					- baud_counter);
	2: assert(f_rx_count == half_baud + 3 * CLOCKS_PER_BAUD
					- baud_counter);
	3: assert(f_rx_count == half_baud + 4 * CLOCKS_PER_BAUD
					- baud_counter);
	4: assert(f_rx_count == half_baud + 5 * CLOCKS_PER_BAUD
					- baud_counter);
	5: assert(f_rx_count == half_baud + 6 * CLOCKS_PER_BAUD
					- baud_counter);
	6: assert(f_rx_count == half_baud + 7 * CLOCKS_PER_BAUD
					- baud_counter);
	7: assert(f_rx_count == half_baud + 8 * CLOCKS_PER_BAUD
					- baud_counter);
	8: assert((f_rx_count == half_baud + 9 * CLOCKS_PER_BAUD
					- baud_counter)
			||(f_rx_count == half_baud + 10 * CLOCKS_PER_BAUD
					- baud_counter));
	9: begin end
	4'hf: begin end
	default:
		assert(1'b0);
	endcase

	always @(*)
		assert( ((!zero_baud_counter)
				&&(state == RXUL_IDLE)
				&&(baud_counter == 0))
			||((zero_baud_counter)&&(baud_counter == 0))
			||((!zero_baud_counter)&&(baud_counter != 0)));

	always @(posedge i_clk)
	if (!f_past_valid)
		assert((state == RXUL_IDLE)&&(baud_counter == 0)
			&&(zero_baud_counter));

	always @(*)
	begin
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'h2);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'h4);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'h5);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'h6);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'h9);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'ha);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'hb);
		assert({ ck_uart,qq_uart,q_uart,i_uart_rx } != 4'hd);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(state) >= RXUL_WAIT)&&($past(ck_uart)))
		assert(state == RXUL_IDLE);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(state) >= RXUL_WAIT)
			&&(($past(state) != RXUL_IDLE)||(state == RXUL_IDLE)))
		assert(zero_baud_counter);

	// Calculate an absolute value of the difference between the two baud
	// clocks
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(state)==RXUL_IDLE)&&(state == RXUL_IDLE))
	begin
		assert(($past(ck_uart))
			||(chg_counter <=
				{ 1'b0, CLOCKS_PER_BAUD[(TB-1):1] }));
	end

	always @(posedge f_txclk)
	if (!f_past_valid_tx)
		assert((state == RXUL_IDLE)&&(baud_counter == 0)
			&&(zero_baud_counter)&&(!f_tx_busy));

	wire	[(TB+3):0]	f_tx_count_two_clocks_ago;
	assign	f_tx_count_two_clocks_ago = f_tx_count - 2;
	always @(*)
	if (f_tx_count >= f_rx_count + 2)
		f_baud_difference = f_tx_count_two_clocks_ago - f_rx_count;
	else
		f_baud_difference = f_rx_count - f_tx_count_two_clocks_ago;

	localparam	F_SYNC_DLY = 8;

	reg	[(TB+4+F_CKRES-1):0]	f_sub_baud_difference;
	reg	[F_CKRES-1:0]	ck_tx_clock;
	reg	[((F_SYNC_DLY-1)*F_CKRES)-1:0]	q_tx_clock;
	reg	[TB+3:0]	ck_tx_count;
	reg	[(F_SYNC_DLY-1)*(TB+4)-1:0]	q_tx_count;
	initial	q_tx_count = 0;
	initial	ck_tx_count = 0;
	initial	q_tx_clock = 0;
	initial	ck_tx_clock = 0;
	always @(posedge gbl_clk)
		{ ck_tx_clock, q_tx_clock } <= { q_tx_clock, f_tx_clock };
	always @(posedge gbl_clk)
		{ ck_tx_count, q_tx_count } <= { q_tx_count, f_tx_count };


	reg	[TB+4+F_CKRES-1:0]	f_ck_tx_time, f_rx_time;
	always @(*)
		f_ck_tx_time = { ck_tx_count, !ck_tx_clock[F_CKRES-1],
						ck_tx_clock[F_CKRES-2:0] };
	always @(*)
		f_rx_time = { f_rx_count, !f_rx_clock[1], f_rx_clock[0],
						{(F_CKRES-2){1'b0}} };

	reg	[TB+4+F_CKRES-1:0]	f_signed_difference;
	always @(*)
		f_signed_difference = f_ck_tx_time - f_rx_time;

	always @(*)
	if (f_signed_difference[TB+4+F_CKRES-1])
		f_sub_baud_difference = -f_signed_difference;
	else
		f_sub_baud_difference =  f_signed_difference;

	always @(posedge gbl_clk)
	if (state == RXUL_WAIT)
		assert((!f_tx_busy)||(f_tx_reg[9:1] == 0));

	always @(posedge gbl_clk)
	if (state == RXUL_IDLE)
	begin
		assert((!f_tx_busy)||(f_tx_reg[9])||(f_tx_reg[9:1]==0));
		if (ck_uart)
			assert((f_tx_reg[9:1]==0)||(f_tx_count < (3 + CLOCKS_PER_BAUD/2)));
	end else if (state == 0)
	begin
		assert(f_sub_baud_difference
				<=  2 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 1)
	begin
		assert(f_sub_baud_difference
				<=  3 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 2)
	begin
		assert(f_sub_baud_difference
				<=  4 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 3)
	begin
		assert(f_sub_baud_difference
				<=  5 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 4)
	begin
		assert(f_sub_baud_difference
				<=  6 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 5)
	begin
		assert(f_sub_baud_difference
				<=  7 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 6)
	begin
		assert(f_sub_baud_difference
				<=  8 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 7)
	begin
		assert(f_sub_baud_difference
				<=  9 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end else if (state == 8)
	begin
		assert(f_sub_baud_difference
				<= 10 * ((CLOCKS_PER_BAUD<<F_CKRES)/20));
	end

	always @(posedge i_clk)
	if (o_wr)
		assert(o_data == $past(f_tx_data,4));

	// always @(posedge i_clk)
	// if ((zero_baud_counter)&&(state != 4'hf)&&(CLOCKS_PER_BAUD > 6))
		// assert(i_uart_rx == ck_uart);

	// Make sure the data register matches
	always @(posedge i_clk)
	case(state)
	4'h0: assert(!data_reg[7]);
	4'h1: assert((data_reg[7] == $past(f_tx_data[0]))&&(!data_reg[6]));
	4'h2: assert(data_reg[7:6] == $past(f_tx_data[1:0]));
	4'h3: assert(data_reg[7:5] == $past(f_tx_data[2:0]));
	4'h4: assert(data_reg[7:4] == $past(f_tx_data[3:0]));
	4'h5: assert(data_reg[7:3] == $past(f_tx_data[4:0]));
	4'h6: assert(data_reg[7:2] == $past(f_tx_data[5:0]));
	4'h7: assert(data_reg[7:1] == $past(f_tx_data[6:0]));
	4'h8: assert(data_reg[7:0] == $past(f_tx_data[7:0]));
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	always @(posedge i_clk)
		cover(o_wr); // Step 626, takes about 20mins

	always @(posedge i_clk)
	begin
		cover(!ck_uart);
		cover((f_past_valid)&&($rose(ck_uart)));               //  82
		cover((zero_baud_counter)&&(state == RXUL_BIT_ZERO)); // 110
		cover((zero_baud_counter)&&(state == RXUL_BIT_ONE));  // 174
		cover((zero_baud_counter)&&(state == RXUL_BIT_TWO));  // 238
		cover((zero_baud_counter)&&(state == RXUL_BIT_THREE));// 302
		cover((zero_baud_counter)&&(state == RXUL_BIT_FOUR)); // 366
		cover((zero_baud_counter)&&(state == RXUL_BIT_FIVE)); // 430
		cover((zero_baud_counter)&&(state == RXUL_BIT_SIX));  // 494
		cover((zero_baud_counter)&&(state == RXUL_BIT_SEVEN));// 558
		cover((zero_baud_counter)&&(state == RXUL_STOP));     // 622
		cover((zero_baud_counter)&&(state == RXUL_WAIT));     // 626
	end
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Properties to test via Verilator *and* formal
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
`ifdef	FORMAL_VERILATOR
	// FORMAL properties which can be tested via Verilator as well as
	// Yosys FORMAL
	always @(*)
		assert((state == 4'hf)||(state <= RXUL_WAIT));
	always @(*)
		assert(zero_baud_counter == (baud_counter == 0)? 1'b1:1'b0);
	always @(*)
		assert(baud_counter <= CLOCKS_PER_BAUD-1'b1);
	// }}}
`endif
// }}}
endmodule
