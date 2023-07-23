////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	llsdspi.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file implements the "lower-level" interface to the
//		SD-Card controller.  Specifically, it turns byte-level
//	interaction requests into SPI bit-wise interactions.  Further, it
//	handles the request and grant for the SPI wires (i.e., it requests
//	the SPI port by pulling o_cs_n low, and then waits for i_bus_grant
//	to be true before continuing.).  Finally, the speed/clock rate of the
//	communication is adjustable as a division of the current clock rate.
//
//	i_speed
//		This is the number of clocks (minus one) between SPI clock
//		transitions.  Hence a '0' (not tested, doesn't work) would
//		result in a SPI clock that alternated on every input clock
//		equivalently dividing the input clock by two, whereas a '1'
//		would divide the input clock by four.
//
//		In general, the SPI clock frequency will be given by the
//		master clock frequency divided by twice this number plus one.
//		In other words,
//
//		SPIFREQ=(i_clk FREQ) / (2*(i_speed+1))
//
//	i_stb
//		True if the master controller is requesting to send a byte.
//		This will be ignored unless o_idle is false.
//
//	i_byte
//		The byte that the master controller wishes to send across the
//		interface.
//
//	(The external SPI interface)
//
//	o_stb
//		Only true for one clock--when a byte is valid coming in from the
//		interface, this will be true for one clock (a strobe) indicating
//		that a valid byte is ready to be read.
//
//	o_byte
//		The value of the byte coming in.
//
//	o_idle
//		True if this low-level device handler is ready to accept a
//		byte from the incoming interface, false otherwise.
//
//	i_bus_grant
//		True if the SPI bus has been granted to this interface, false
//		otherwise.  This has been placed here so that the interface of
//		the XuLA2 board may be shared between SPI-Flash and the SPI
//		based SDCard.  An external arbiter will determine which of the
//		two gets to control the clock and mosi outputs given their
//		cs_n requests.  If control is not granted, i_bus_grant will
//		remain low as will the actual cs_n going out of the FPGA.
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
module	llsdspi #(
		// {{{
		parameter	SPDBITS = 7,
				// Minimum startup clocks
				STARTUP_CLOCKS = 150,
				// System clocks to wait before the startup
				// clock sequence
				POWERUP_IDLE = 1000,
		//
		// This core was originally developed for a shared SPI bus
		// implementation on a XuLA2-LX25 board--one that shared flash
		// with the SD-card.  Few cards support such an implementation
		// any more, since per protocol CS high (inactive) and clock
		// and data pins toggling could well put the SD card into it's
		// SD mode instead of SPI mode.
		parameter [0:0]	OPT_SPI_ARBITRATION = 1'b0,
		//
		//
		localparam [0:0]	CSN_ON_STARTUP = 1'b1,
		//
		// The MOSI INACTIVE VALUE *MUST* be 1'b1 to be compliant
		localparam [0:0]	MOSI_INACTIVE_VALUE = 1'b1,
		//
		// Normally, an SPI transaction shuts the clock down when
		// finished.  If OPT_CONTINUOUS_CLOCK is set, the clock will be
		// continuous.  This also means that any driving program must
		// be ready when the SDSPI is idle.
		parameter [0:0]	OPT_CONTINUOUS_CLOCK = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Parameters/setup
		input	wire	[(SPDBITS-1):0]	i_speed,
		// The incoming interface
		input	wire		i_cs,
		input	wire		i_stb,
		input	wire	[7:0]	i_byte,
		// The actual SPI interface
		output	reg		o_cs_n, o_sclk, o_mosi,
		input	wire		i_miso,
		// The outgoing interface
		output	reg		o_stb,
		output	reg	[7:0]	o_byte,
		output	reg		o_idle,
		// And whether or not we actually own the interface (yet)
		input	wire		i_bus_grant
		// }}}
	);

	// Signal / localparam declarations
	// {{{
	localparam [3:0]	LLSDSPI_IDLE    = 4'h0,
				LLSDSPI_HOTIDLE	= 4'h1,
				LLSDSPI_WAIT	= 4'h2,
				LLSDSPI_START	= 4'h3,
				LLSDSPI_END	= 4'hb;
	//
	reg			r_z_counter;
	reg	[(SPDBITS-1):0]	r_clk_counter;
	reg			r_idle;
	reg		[3:0]	r_state;
	reg		[7:0]	r_byte, r_ireg;
	wire			byte_accepted;
	reg			restart_counter;

	wire			bus_grant;
	reg	startup_hold, powerup_hold;
`ifdef	FORMAL
	reg	f_past_valid;
`endif
	// }}}

	assign	bus_grant = (OPT_SPI_ARBITRATION ? i_bus_grant : 1'b1);

	// Wait for power up
	// {{{
	generate if (POWERUP_IDLE > 0)
	begin : WAIT_FOR_POWERUP
		// {{{
		localparam	POWERUP_BITS = $clog2(POWERUP_IDLE);
		reg	[POWERUP_BITS-1:0]	powerup_counter;

		initial powerup_counter = POWERUP_IDLE[POWERUP_BITS-1:0];
		initial	powerup_hold = 1;
		always @(posedge i_clk)
		if (i_reset)
		begin
			powerup_counter <= POWERUP_IDLE;
			powerup_hold    <= 1;
		end else if (powerup_hold)
		begin
			if (|powerup_counter)
				powerup_counter <= powerup_counter - 1;
			powerup_hold <= (powerup_counter > 0);
		end

`ifdef	FORMAL
		always @(*)
		if (!f_past_valid)
			assume(powerup_counter > 2);
		always @(*)
		if (powerup_counter > 0)
			assert(powerup_hold);
`endif
		// }}}
	end else begin

		always @(*)
			powerup_hold = 0;
	end endgenerate
	// }}}

	// Send a minimum number of start up clocks after power up
	// {{{
	generate if (STARTUP_CLOCKS > 0)
	begin : WAIT_FOR_STARTUP
		// {{{
		localparam	STARTUP_BITS = $clog2(STARTUP_CLOCKS);
		reg	[STARTUP_BITS-1:0]	startup_counter;

		initial startup_counter = STARTUP_CLOCKS[STARTUP_BITS-1:0];
		initial	startup_hold = 1;
		always @(posedge i_clk)
		if (i_reset || powerup_hold)
		begin
			startup_counter <= STARTUP_CLOCKS;
			startup_hold    <= 1;
		end else if (startup_hold && r_z_counter && !o_sclk)
		begin
			if (|startup_counter)
				startup_counter <= startup_counter - 1;
			startup_hold <= (startup_counter > 0);
		end

`ifdef	FORMAL
		always @(*)
		if (!f_past_valid)
			assume(startup_counter > 1);
		always @(*)
		if (startup_counter > 0)
			assert(startup_hold);
`endif
		// }}}
	end else begin

		always @(*)
			startup_hold = 0;

	end endgenerate
	// }}}

	assign	byte_accepted = (i_stb)&&(o_idle);

`ifdef	FORMAL
	// {{{
	always @(*)
	if (powerup_hold)
		assert(startup_hold);
	// }}}
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// Clock divider and speed control
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	r_clk_counter = 0;
	initial	r_z_counter = 1'b1;

	// restart_counter
	// {{{
	always @(*)
	if (OPT_CONTINUOUS_CLOCK || powerup_hold)
		restart_counter = !powerup_hold;
	else begin
		restart_counter = 1'b0;

		if (startup_hold || !i_cs)
			restart_counter = 1'b1;
		else if (!OPT_SPI_ARBITRATION && byte_accepted)
			restart_counter = 1'b1;
		else if (OPT_SPI_ARBITRATION && r_state == LLSDSPI_IDLE)
			restart_counter = 1'b0;
		else if (OPT_SPI_ARBITRATION && r_state == LLSDSPI_WAIT
				&& !bus_grant)
			restart_counter = 1'b0;
		else if (OPT_SPI_ARBITRATION && byte_accepted)
			restart_counter = 1'b1;
		else
			restart_counter = !r_idle;
	end
	// }}}

	// r_clk_counter, r_z_counter
	// {{{
	always @(posedge i_clk)
	begin
		if (!r_z_counter)
		begin
			r_clk_counter <= (r_clk_counter - 1);
			r_z_counter <= (r_clk_counter == 1);
		end else if (restart_counter)
		begin
			r_clk_counter <= i_speed;
			r_z_counter <= (i_speed == 0);
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control o_stb, o_cs_n, and o_mosi
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_cs_n, r_state
	// {{{
	initial	o_cs_n = CSN_ON_STARTUP;
	initial	r_state = LLSDSPI_IDLE;
	always @(posedge i_clk)
	if (i_reset || (!CSN_ON_STARTUP && startup_hold))
	begin
		o_cs_n <= CSN_ON_STARTUP;
		r_state <= LLSDSPI_IDLE;
	end else if (r_z_counter)
	begin
		if (!i_cs)
		begin
			// No request for action.  If anything, a request
			// to close up/seal up the bus for the next transaction
			// Expect to lose arbitration here.
			r_state <= LLSDSPI_IDLE;
			o_cs_n <= 1'b1;
		end else if (r_state == LLSDSPI_IDLE)
		begin
			if (byte_accepted)
			begin
				o_cs_n <= 1'b0;
				if (OPT_SPI_ARBITRATION)
					// Wait for arbitration
					r_state <= LLSDSPI_WAIT;
				else
					r_state <= LLSDSPI_START + (OPT_CONTINUOUS_CLOCK ? 1:0);
			end
		end else if (r_state == LLSDSPI_WAIT)
		begin
			if (bus_grant)
				r_state <= LLSDSPI_START;
		end else if (byte_accepted)
			r_state <= LLSDSPI_START+1;
		else if (o_sclk && r_state >= LLSDSPI_START)
		begin
			r_state <= r_state + 1;
			if (r_state >= LLSDSPI_END)
				r_state <= LLSDSPI_HOTIDLE;
		end

		if (startup_hold)
			o_cs_n <= 1;
	end
	// }}}

	// r_ireg
	// {{{
	always @(posedge i_clk)
	if (r_z_counter && !o_sclk)
		r_ireg <= { r_ireg[6:0], i_miso };
	// }}}

	// o_byte
	// {{{
	always @(posedge i_clk)
	if (r_z_counter && o_sclk && r_state == LLSDSPI_END)
		o_byte <= r_ireg;
	// }}}

	// r_idle
	// {{{
	initial	r_idle  = 0;
	always @(posedge i_clk)
	if (startup_hold || i_reset)
		r_idle <= 0;
	else if (r_z_counter)
	begin
		if (byte_accepted)
			r_idle <= 1'b0;
		else if ((r_state == LLSDSPI_END)
				||(r_state == LLSDSPI_HOTIDLE))
			r_idle <= 1'b1;
		else if (r_state == LLSDSPI_IDLE)
			r_idle <= 1'b1;
		else
			r_idle <= 1'b0;
	end
	// }}}

	// o_sclk
	// {{{
	initial	o_sclk = 1;
	always @(posedge i_clk)
	if (i_reset)
		o_sclk <= 1;
	else if (r_z_counter)
	begin
		if (OPT_CONTINUOUS_CLOCK)
			o_sclk <= !o_sclk;
		else if (restart_counter
			&& (startup_hold || (i_cs && !o_cs_n) || !o_sclk))
			o_sclk <= (r_state == LLSDSPI_WAIT) || !o_sclk;
	end
	// }}}

	// r_byte, o_mosi
	// {{{
	initial	r_byte = -1;
	initial	o_mosi = MOSI_INACTIVE_VALUE;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_byte <= {(8){MOSI_INACTIVE_VALUE}};
		o_mosi <= MOSI_INACTIVE_VALUE;
	end else if (r_z_counter)
	begin
		if (byte_accepted)
		begin
			o_mosi <= MOSI_INACTIVE_VALUE;
			if (o_cs_n && !OPT_CONTINUOUS_CLOCK)
				r_byte <= i_byte[7:0];
			else begin
				r_byte <= { i_byte[6:0], MOSI_INACTIVE_VALUE };
				o_mosi <= i_byte[7];
			end
		end else if (o_sclk && (!OPT_SPI_ARBITRATION
				|| (bus_grant && r_state != LLSDSPI_WAIT)))
		begin
			r_byte <= { r_byte[6:0], MOSI_INACTIVE_VALUE };
			if (r_state >= LLSDSPI_START && r_state < LLSDSPI_END)
				o_mosi <= r_byte[7];
			else if (!i_cs)
				o_mosi <= MOSI_INACTIVE_VALUE;
		end
	end
	// }}}

	// o_stb
	// {{{
	initial	o_stb  = 1'b0;
	always @(posedge i_clk)
	if (i_reset || startup_hold || !i_cs || !r_z_counter || !o_sclk)
		o_stb <= 1'b0;
	else
		o_stb <= (r_state >= LLSDSPI_END);
	// }}}

	// o_idle
	// {{{
	always @(*)
	begin
		if (OPT_CONTINUOUS_CLOCK)
			o_idle = (r_idle)&&(r_z_counter)&&(o_sclk);
		else
			o_idle = (r_idle)&&(r_z_counter);
	end
	// }}}
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
`ifdef	LLSDSPI
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg [7:0]	fv_byte;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Clock division logic (checks)
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *) reg constant_speed;

	always @(posedge i_clk)
	if (constant_speed)
	begin
		assume($stable(i_speed));
		assert(r_clk_counter <= i_speed);
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(r_clk_counter != 0))
		assert(r_clk_counter == $past(r_clk_counter - 1));
	else if (f_past_valid)
		assert((r_clk_counter == 0)||(r_clk_counter == $past(i_speed)));

	//
	// And assumptions
	//
	always @(posedge i_clk)
	if (f_past_valid && (i_cs || !r_z_counter))
		assume($stable(i_speed));

	////////////////////////////////////////////////////////////////////////
	//
	// Interface assumptions
	//
	always @(*)
	if (i_stb)
		`ASSUME(i_cs);

	always @(posedge i_clk)
	if (f_past_valid && $past(i_stb && !o_idle))
	begin
		if ($past(i_reset || !i_cs))
			`ASSUME(!i_stb);
		// else
		//	`ASSUME(i_stb);
		if ($past(f_past_valid)&&(!$past(o_idle,2)))
			`ASSUME($stable(i_byte));
	end else if (f_past_valid && $past(i_cs && !o_idle && !i_reset))
		`ASSUME(i_cs);
		// assume(i_cs);

	always @(posedge i_clk)
	if (!f_past_valid)
		assert(o_cs_n == CSN_ON_STARTUP);
	else if ($past(bus_grant && !o_cs_n))
		`ASSUME(bus_grant);
	else if ($past(!bus_grant && o_cs_n))
		`ASSUME(!bus_grant);

	always @(*)
	if (r_state == LLSDSPI_IDLE)
		assert(!CSN_ON_STARTUP || o_cs_n);
	else
		assert(!o_cs_n);


	always @(posedge i_clk)
	if (f_past_valid && CSN_ON_STARTUP && $past(r_state == LLSDSPI_IDLE)
		&& $past(!i_reset)
		&& r_state == LLSDSPI_IDLE)
		assert(o_cs_n);

	always @(*)
	if (r_state == LLSDSPI_WAIT)
		assert(!o_cs_n && o_sclk);
	else
		assert(o_cs_n || bus_grant);

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && i_cs && !o_cs_n && !bus_grant))
		assert(!o_cs_n && o_sclk);

	always @(posedge i_clk)
	if ($past(!o_cs_n && bus_grant) && (!o_cs_n && bus_grant))
	begin
		if (!$fell(o_sclk))
			assume($stable(i_miso));

		cover($changed(i_miso));
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		`ASSUME(!i_stb);
		`ASSUME(!i_cs);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Reset checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(startup_hold);
		assert(o_cs_n == CSN_ON_STARTUP);
		assert(o_sclk);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Send byte sequences: from nothing, and from the last byte
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[17:0]	f_start_seq;
	reg	[16:0]	f_next_seq;

	always @(*)
		assert(r_z_counter == (r_clk_counter == 0));

	always @(posedge i_clk)
	if (byte_accepted)
		fv_byte <= i_byte;

	always @(posedge i_clk)
		assert(r_state <= LLSDSPI_END);

	initial	f_start_seq = 0;
	always @(posedge i_clk)
	if (i_reset || !i_cs)
		f_start_seq <= 0;
	else if (f_start_seq == 0)
	begin
		if (OPT_SPI_ARBITRATION)
		begin
			if (r_state == LLSDSPI_IDLE && byte_accepted)
			begin
			//	if (!o_cs_n && bus_grant)
			//		f_start_seq <= (f_next_seq == 0);
			//	//r_start_seq <= (!o_cs_n && bus_grant) ? 1:0;
			end else if (r_state == LLSDSPI_WAIT && r_z_counter)
				f_start_seq <= (bus_grant ? 1:0);
		end else if (byte_accepted)
		begin
			if (OPT_CONTINUOUS_CLOCK)
				f_start_seq <= (f_next_seq == 0) ? 2:0;
			else
				f_start_seq <= (f_next_seq == 0);
		end
	end else if (r_z_counter)
	begin
		f_start_seq <= f_start_seq << 1;
		if (byte_accepted)
		begin
			f_start_seq[17] <= 0;
			f_start_seq[16] <= 0;
		end else if (f_start_seq[17])
			f_start_seq[17] <= 1;
	end

	always @(*)
	if (!OPT_SPI_ARBITRATION)
		assert(r_state != LLSDSPI_WAIT);

	always @(*)
	if (r_state == LLSDSPI_WAIT)
	begin
		// assert(o_mosi == fv_byte[7]);
		assert(r_byte == fv_byte[7:0]);
		assert(o_sclk);
		assert(!o_stb);
		assert(f_start_seq == 0);
		assert(f_next_seq == 0);
		assert(!r_idle);
		assert(r_z_counter);
	end

	always @(*)
	if (|(f_start_seq & {(8){2'b01}}))
		assert(o_sclk);
	else if (|(f_start_seq & {(8){2'b10}}))
		assert(!o_sclk);

	generate if (!OPT_CONTINUOUS_CLOCK)
	begin
		always @(*)
		if (f_start_seq[17:0] == 18'h001)
			cover(r_state == LLSDSPI_START);
	end endgenerate

	always @(*)
	case(f_start_seq[17:0])
	18'h001: begin
		assert(o_sclk);
		assert(r_byte == fv_byte[7:0] );
		assert(r_state == LLSDSPI_START);
		// assert(o_mosi == fv_byte[7]);
		assert(!OPT_CONTINUOUS_CLOCK);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h002: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[6:0], {(1){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+1);
		assert(o_mosi == fv_byte[7]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h004: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[6:0], {(1){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+1);
		assert(o_mosi == fv_byte[7]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h008: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[5:0], {(2){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+2);
		assert(o_mosi == fv_byte[6]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h010: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[5:0], {(2){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+2);
		assert(o_mosi == fv_byte[6]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h020: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[4:0], {(3){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+3);
		assert(o_mosi == fv_byte[5]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h040: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[4:0], {(3){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+3);
		assert(o_mosi == fv_byte[5]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h080: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[3:0], {(4){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+4);
		assert(o_mosi == fv_byte[4]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h100: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[3:0], {(4){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+4);
		assert(o_mosi == fv_byte[4]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h00200: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[2:0], {(5){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+5);
		assert(o_mosi == fv_byte[3]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h00400: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[2:0], {(5){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+5);
		assert(o_mosi == fv_byte[3]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h00800: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[1:0], {(6){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+6);
		assert(o_mosi == fv_byte[2]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h01000: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[1:0], {(6){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+6);
		assert(o_mosi == fv_byte[2]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h02000: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[0], {(7){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+7);
		assert(o_mosi == fv_byte[1]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h04000: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[0], {(7){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+7);
		assert(o_mosi == fv_byte[1]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h08000: begin
		assert(!o_sclk);
		assert(r_byte == { {(8){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_END);
		assert(o_mosi == fv_byte[0]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h10000: begin
		assert(o_sclk);
		assert(r_byte == { {(8){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_END);
		assert(o_mosi == fv_byte[0]);
		assert(!o_cs_n);
		assert(r_idle);
		end
	18'h20000: begin
		assert(o_sclk);
		assert(r_state == LLSDSPI_HOTIDLE);
		assert(r_idle);
		end
	default: assert(f_start_seq == 0);
	endcase

	always @(*)
	if (|f_start_seq[16:1])
	begin
		assert(!o_cs_n);
		assert(bus_grant);
	end

	initial	f_next_seq = 0;
	always @(posedge i_clk)
	if (i_reset || !i_cs)
		f_next_seq <= 0;
	else if ((|f_start_seq[17:16]) && byte_accepted)
		f_next_seq <= 1;
	else if ((|f_next_seq[16:15]) && byte_accepted)
		f_next_seq <= 1;
	else if (r_z_counter)
	begin
		f_next_seq <= f_next_seq << 1;
		// if (i_stb)
		//	f_next_seq[16] <= 0;
		// else
		if (f_next_seq[16])
			f_next_seq[16] <= 1;
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && !$fell(o_sclk) && !o_cs_n)
		assert($stable(o_mosi));

	always @(*)
	if (|(f_next_seq & {(8){2'b10}}))
		assert(o_sclk);
	else if (|(f_next_seq & {(8){2'b01}}))
		assert(!o_sclk);

	always @(*)
	case(f_next_seq[16:0])
	17'h001: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[6:0], {(1){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+1);
		assert(o_mosi == fv_byte[7]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h002: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[6:0], {(1){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+1);
		assert(o_mosi == fv_byte[7]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h004: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[5:0], {(2){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+2);
		assert(o_mosi == fv_byte[6]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h008: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[5:0], {(2){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+2);
		assert(o_mosi == fv_byte[6]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h010: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[4:0], {(3){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+3);
		assert(o_mosi == fv_byte[5]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h020: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[4:0], {(3){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+3);
		assert(o_mosi == fv_byte[5]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h040: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[3:0], {(4){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+4);
		assert(o_mosi == fv_byte[4]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	18'h080: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[3:0], {(4){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+4);
		assert(o_mosi == fv_byte[4]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h100: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[2:0], {(5){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+5);
		assert(o_mosi == fv_byte[3]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h200: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[2:0], {(5){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+5);
		assert(o_mosi == fv_byte[3]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h400: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[1:0], {(6){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+6);
		assert(o_mosi == fv_byte[2]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h0800: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[1:0], {(6){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+6);
		assert(o_mosi == fv_byte[2]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h1000: begin
		assert(!o_sclk);
		assert(r_byte == { fv_byte[0], {(7){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+7);
		assert(o_mosi == fv_byte[1]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h2000: begin
		assert(o_sclk);
		assert(r_byte == { fv_byte[0], {(7){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_START+7);
		assert(o_mosi == fv_byte[1]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h4000: begin
		assert(!o_sclk);
		assert(r_byte == { {(8){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_END);
		assert(o_mosi == fv_byte[0]);
		assert(!o_cs_n);
		assert(!r_idle);
		end
	17'h8000: begin
		assert(o_sclk);
		assert(r_byte == { {(8){MOSI_INACTIVE_VALUE}} });
		assert(r_state == LLSDSPI_END);
		assert(o_mosi == fv_byte[0]);
		assert(!o_cs_n);
		assert(r_idle);
		end
	17'h10000: begin
		assert(o_sclk);
		assert(!o_cs_n);
		assert(r_state == LLSDSPI_HOTIDLE);
		assert(r_idle);
		end
	default: assert(f_next_seq == 0);
	endcase

	always @(*)
	if (f_next_seq != 0)
		assert(f_start_seq == 0);

	always @(*)
	if (r_state != LLSDSPI_IDLE)
		assert(({ 1'b0, f_next_seq } | f_start_seq)
			||(OPT_SPI_ARBITRATION && r_state == LLSDSPI_WAIT));

	always @(*)
	if ((f_start_seq==0) && (f_next_seq == 0))
		assert((r_state == LLSDSPI_IDLE)
			||(OPT_SPI_ARBITRATION && r_state == LLSDSPI_WAIT));

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $changed({ o_sclk, o_mosi }))
	begin
		if ($past(i_cs))
		begin
			assert(r_z_counter == $past(i_speed == 0));
			assert(r_clk_counter == $past(i_speed));
		end
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && !$past(r_z_counter))
	begin
		assert($stable(o_cs_n));
		assert($stable(o_sclk));
		assert($stable(o_mosi));
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Verify the receiver
	//
	(* anyseq *) reg [7:0] f_rxdata;

	always @(posedge i_clk)
	if (!$past(byte_accepted))
		assume($stable(f_rxdata));

	always @(*)
	case(f_start_seq[17:0] | { f_next_seq, 1'b0 })
	18'h001: begin
		end
	18'h002: begin
		assume(i_miso == f_rxdata[7]);
		end
	18'h004: begin
		// assume(i_miso == f_rxdata[7]);
		assert(r_ireg[0] == f_rxdata[7]);
		end
	18'h008: begin
		// assume(i_miso == f_rxdata[6]);
		assert(r_ireg[0] == f_rxdata[7]);
		end
	18'h010: begin
		assume(i_miso == f_rxdata[6]);
		assert(r_ireg[1:0] == f_rxdata[7:6]);
		end
	18'h020: begin
		assume(i_miso == f_rxdata[5]);
		assert(r_ireg[1:0] == f_rxdata[7:6]);
		end
	18'h040: begin
		assume(i_miso == f_rxdata[5]);
		assert(r_ireg[2:0] == f_rxdata[7:5]);
		end
	18'h080: begin
		assume(i_miso == f_rxdata[4]);
		assert(r_ireg[2:0] == f_rxdata[7:5]);
		end
	18'h100: begin
		assume(i_miso == f_rxdata[4]);
		assert(r_ireg[3:0] == f_rxdata[7:4]);
		end
	18'h200: begin
		assume(i_miso == f_rxdata[3]);
		assert(r_ireg[3:0] == f_rxdata[7:4]);
		end
	18'h400: begin
		assume(i_miso == f_rxdata[3]);
		assert(r_ireg[4:0] == f_rxdata[7:3]);
		end
	18'h800: begin
		assume(i_miso == f_rxdata[2]);
		assert(r_ireg[4:0] == f_rxdata[7:3]);
		end
	18'h1000: begin
		assume(i_miso == f_rxdata[2]);
		assert(r_ireg[5:0] == f_rxdata[7:2]);
		end
	18'h2000: begin
		assume(i_miso == f_rxdata[1]);
		assert(r_ireg[5:0] == f_rxdata[7:2]);
		end
	18'h4000: begin
		assume(i_miso == f_rxdata[1]);
		assert(r_ireg[6:0] == f_rxdata[7:1]);
		end
	18'h8000: begin
		assume(i_miso == f_rxdata[0]);
		assert(r_ireg[6:0] == f_rxdata[7:1]);
		end
	18'h10000: begin
		assume(i_miso == f_rxdata[0]);
		assert(r_ireg == f_rxdata);
		end
	18'h20000: begin
		assume(i_miso == f_rxdata[0]);
		assert(r_ireg == f_rxdata);
		assert(o_byte == f_rxdata);
		end
	endcase

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_stb);
	else if ($past(i_cs))
	begin
		if ($fell(f_start_seq[16]))
			assert(o_stb);
		else if ($fell(f_next_seq[15]))
			assert(o_stb);
		else
			assert(!o_stb);
	end else
		assert(!o_stb);

	always @(posedge i_clk)
	if (o_cs_n || ((f_start_seq == 0) &&(f_next_seq == 0)))
		assert(o_mosi == MOSI_INACTIVE_VALUE);

	always @(*)
	if (!f_past_valid)
	begin
		if (STARTUP_CLOCKS > 0)
			`ASSUME(startup_hold);
		assert(r_z_counter);
		assert(!r_idle);
		assert(o_cs_n == CSN_ON_STARTUP);
		assert(o_sclk);
	end

	always @(*)
	if (r_state == LLSDSPI_WAIT)
		assert(o_sclk && !o_cs_n);

	always @(*)
	if (!OPT_CONTINUOUS_CLOCK && o_cs_n && r_idle)
		assert(o_sclk);

	always @(*)
	if (startup_hold)
		assert(o_cs_n == CSN_ON_STARTUP);
	else if (!OPT_CONTINUOUS_CLOCK && o_cs_n)
		assert(o_sclk);


`ifdef	VERIFIC
	always @(*)
		assert($onehot0(f_next_seq));
	always @(*)
		assert($onehot0(f_start_seq));
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
`ifdef	LLSDSPI
	(* anyconst *) reg nonzero_speed;

	reg	[2:0]	byte_count;

	always @(posedge i_clk)
	if (i_reset || !i_cs)
		byte_count <= 0;
	else if (i_stb && !o_idle && (!(&byte_count)))
		byte_count <= byte_count + 1;

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		cover(byte_count == 2 && !o_cs_n &&  nonzero_speed);
		cover(byte_count == 2 && !o_cs_n && !nonzero_speed);

		/*
		if (nonzero_speed)
		begin
			assume(i_speed > 0);
			cover($rose(r_state == LLSDSPI_IDLE)&&($past(i_cs,2)));
			cover($past(f_next_seq[16])
					&& r_state == LLSDSPI_IDLE && (!i_cs));
			cover($past(f_next_seq[16]) && f_next_seq[0]);
		end else begin
			cover($rose(r_state == LLSDSPI_IDLE)&&($past(i_cs,2)));
			cover($past(f_next_seq[16])
					&& r_state == LLSDSPI_IDLE && (!i_cs));
			cover($past(f_next_seq[16]) && f_next_seq[0]);
		end
		*/

		cover(o_stb && o_byte == 8'haa && $changed(o_byte));
		cover(o_stb && o_byte == 8'h55 && $changed(o_byte));
	end

	generate if (OPT_CONTINUOUS_CLOCK)
	begin
		always @(*)
		begin
			cover(f_next_seq == 2);
			cover(f_start_seq[3]);
			cover(f_next_seq[15]);
			// cover(f_next_seq[16]); // Won't happen anymore
		end
	end else begin
		always @(*)
			cover(f_next_seq == 1);
	end endgenerate
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" constraining assumptions
	//
	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if ($past(i_stb && !i_reset))
			`ASSUME(i_cs);
	end

	always @(*)
	if (!CSN_ON_STARTUP && r_state == 0 && !o_cs_n)
		assume(!i_cs);

	always @(posedge i_clk)
	if (OPT_CONTINUOUS_CLOCK)
	begin
		// if ($past(i_cs && !i_stb))
		//	assume(!i_stb);
		assume(i_stb == i_cs);

		if (!o_sclk && r_state == LLSDSPI_IDLE)
			assume(!i_stb);
	end

`endif // FORMAL
// }}}
endmodule
