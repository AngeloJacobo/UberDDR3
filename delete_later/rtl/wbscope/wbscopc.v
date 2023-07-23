////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbscopc.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This scope is identical in function to the wishbone scope
//	found in wbscope, save that the output is compressed via a run-length
//	encoding scheme and that (as a result) it can only handle recording
//	31 bits at a time.  This allows the top bit to indicate the presence
//	of an 'address difference' rather than actual incoming recorded data.
//
//	Reading/decompressing the output of this scope works in this fashion:
//	Once the scope has stopped, read from the port.  Any time the high
//	order bit is set, the other 31 bits tell you how many times to repeat
//	the last value.  If the high order bit is not set, then the value
//	is a new data value.
//
//	Previous versions of the compressed scope have had some fundamental
//	flaws: 1) it was impossible to know when the trigger took place, and
//	2) if things never changed, the scope would never fill or complete
//	its capture.  These two flaws have been fixed with this release.
//
//	When dealing with a slow interface such as the PS/2 interface, or even
//	the 16x2 LCD interface, it is often true that things can change _very_
//	slowly.  They could change so slowly that the standard wishbone scope
//	doesn't work.  This scope then gives you a working scope, by sampling
//	at diverse intervals, and only capturing anything that changes within
//	those intervals.  
//
//	Indeed, I'm finding this compressed scope very valuable for evaluating
//	the timing associated with a GPS PPS and associated NMEA stream.  I
//	need to collect over a seconds worth of data, and I don't have enough
//	memory to handle one memory value per clock, yet I still want to know
//	exactly when the GPS PPS goes high, when it goes low, when I'm
//	adjusting my clock, and when the clock's PPS output goes high.  Did I
//	synchronize them well?  Oh, and when does the NMEA time string show up
//	when compared with the PPS?  All of those are valuable, but could never
//	be done if the scope wasn't compressed.
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
module wbscopc #(
		// {{{
		parameter [4:0]			LGMEM = 5'd10,
		parameter			BUSW = 32, NELM=(BUSW-1),
		parameter [0:0]			SYNCHRONOUS=1,
		parameter			HOLDOFFBITS=20,
		parameter [(HOLDOFFBITS-1):0]	DEFAULT_HOLDOFF
						= ((1<<(LGMEM-1))-4),
		parameter			STEP_BITS=BUSW-1,
		parameter [(STEP_BITS-1):0]	MAX_STEP= {(STEP_BITS){1'b1}}
		// }}}
	) (
		// {{{
		// The input signals that we wish to record
		input	wire			i_data_clk, i_ce, i_trigger,
		input	wire	[(NELM-1):0]	i_data,
		// The WISHBONE bus for reading and configuring this scope
		// {{{
		input	wire			i_wb_clk, i_wb_cyc,
						i_wb_stb, i_wb_we,
		input	wire			i_wb_addr, // One address line only
		input	wire	[(BUSW-1):0]	i_wb_data,
		input	wire	[(BUSW/8-1):0]	i_wb_sel,
		output	wire			o_wb_stall, o_wb_ack,
		output	wire	[(BUSW-1):0]	o_wb_data,
		// }}}
		// And, finally, for a final flair --- offer to interrupt the
		// CPU after our trigger has gone off.  This line is equivalent
		// to the scope  being stopped.  It is not maskable here.
		output	wire			o_interrupt
		// }}}
	);

	// Signal declarations
	// {{{
	// Pseudo bus signals
	// {{{
	wire		write_stb, read_from_data, write_to_control;
	reg	[31:0]	o_bus_data;
	wire		bus_clock;
	reg		read_address;
	wire [BUSW-1:0]	i_bus_data;
	// }}}

	reg	[(LGMEM-1):0]	raddr, waddr;
	reg	[(BUSW-1):0]	mem[0:((1<<LGMEM)-1)];

	// Our status/config register
	wire		bw_reset_request, bw_manual_trigger,
			bw_disable_trigger, bw_reset_complete;
	reg	[2:0]	br_config;
	reg	[(HOLDOFFBITS-1):0]	br_holdoff;
	(* ASYNC_REG="TRUE" *) reg	[(HOLDOFFBITS-1):0]	holdoff_counter;

	wire	dw_reset, dw_manual_trigger, dw_disable_trigger;
	reg	dr_triggered, dr_primed;
	wire	dw_trigger;
	reg		dr_stopped;
	localparam	DLYSTOP=5;
	reg	[(DLYSTOP-1):0]	dr_stop_pipe;
	wire	dw_final_stop;

	reg	[(STEP_BITS-1):0]	ck_addr;
	reg	[(NELM-1):0]		qd_data;
	reg				dr_force_write, dr_run_timeout,
					new_data;
	reg		dr_force_inhibit;
	wire	[(BUSW-2):0]	w_data;
	reg	imm_adr, lst_adr; // Is this an address (1'b1) or data value?
	reg	[(BUSW-2):0]	lst_val, // Data for the scope, delayed by one
				imm_val; // Data to write to the scope
	reg			record_ce;
	reg	[(BUSW-1):0]	r_data;
	wire	bw_stopped, bw_triggered, bw_primed;
	reg	br_wb_ack, br_pre_wb_ack;
	wire	bw_cyc_stb;
	reg	[(LGMEM-1):0]	this_addr;
	reg	[31:0]	nxt_mem;
	wire	[19:0]	full_holdoff;
	wire	[4:0]	bw_lgmem;
	reg	br_level_interrupt;
	// }}}

	assign	bus_clock = i_wb_clk;

	////////////////////////////////////////////////////////////////////////
	//
	// Decode and handle the bus signaling in a (somewhat) portable manner
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	///////////////////////////////////////////////////
	//
	//

	assign	i_bus_data = i_wb_data;
	assign	o_wb_stall = 1'b0;
	assign	read_from_data=i_wb_stb && !i_wb_we && i_wb_addr && (&i_wb_sel);
	assign	write_stb = (i_wb_stb)&&(i_wb_we);
	assign	write_to_control = write_stb && !i_wb_addr && (&i_wb_sel);

	always @(posedge bus_clock)
		read_address <= i_wb_addr;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Our status/config register
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Now that we've finished reading/writing from the
	// bus, ... or at least acknowledging reads and
	// writes from and to the bus--even if they haven't
	// happened yet, now we implement our actual scope.
	// This includes implementing the actual reads/writes
	// from/to the bus.
	//
	// From here on down, is the heart of the scope itself.
	//

	// Our status/config register
	initial	br_config = 3'b0;
	initial	br_holdoff = DEFAULT_HOLDOFF;
	always @(posedge bus_clock)
	begin
		if (write_to_control)
		begin
			br_config[1:0] <= {
				i_bus_data[27],
				i_bus_data[26] };
			if (!i_bus_data[31] && br_config[2])
				br_holdoff <= i_bus_data[(HOLDOFFBITS-1):0];
		end

		//
		// Reset logic
		if (bw_reset_complete)
			// Clear the reset request, regardless of the write
			br_config[2] <= 1'b1;
		else if (!br_config[2])
			// Reset request is already pending--don't change it
			br_config[2] <= 1'b0;
		else if (write_to_control && !i_bus_data[31])
			// Initiate a new reset request
			//   Note that we won't initiate a new reset request
			//   while one is already pending.  Once the pending
			//   one completes we'll be in the reset state anyway
			br_config[2] <= 1'b0;

		// if (i_reset)
		//	br_config[2] <= 1'b0;
	end
	assign	bw_reset_request   = (!br_config[2]);
	assign	bw_manual_trigger  = (br_config[1]);
	assign	bw_disable_trigger = (br_config[0]);

	generate if (SYNCHRONOUS > 0)
	begin : GEN_SYNCHRONOUS
		assign	dw_reset = bw_reset_request;
		assign	dw_manual_trigger = bw_manual_trigger;
		assign	dw_disable_trigger = bw_disable_trigger;
		assign	bw_reset_complete = bw_reset_request;
	end else begin : GEN_ASYNC_FLAGS
		reg		r_reset_complete;
		(* ASYNC_REG = "TRUE" *) reg	[2:0]	q_iflags;
		reg	[2:0]	r_iflags;

		// Resets are synchronous to the bus clock, not the data clock
		// so do a clock transfer here
		initial	{ q_iflags, r_iflags } = 6'h0;
		initial	r_reset_complete = 1'b0;
		always @(posedge i_data_clk)
		begin
			q_iflags <= { bw_reset_request, bw_manual_trigger, bw_disable_trigger };
			r_iflags <= q_iflags;
			r_reset_complete <= (dw_reset);
		end

		assign	dw_reset = r_iflags[2];
		assign	dw_manual_trigger = r_iflags[1];
		assign	dw_disable_trigger = r_iflags[0];

		(* ASYNC_REG = "TRUE" *) reg	q_reset_complete,
						qq_reset_complete;
		// Pass an acknowledgement back from the data clock to the bus
		// clock that the reset has been accomplished
		initial	q_reset_complete = 1'b0;
		initial	qq_reset_complete = 1'b0;
		always @(posedge bus_clock)
		begin
			q_reset_complete  <= r_reset_complete;
			qq_reset_complete <= q_reset_complete;
		end

		assign bw_reset_complete = qq_reset_complete;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Set up the trigger
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// dw_trigger -- trigger wire, defined on the data clock
	// {{{
	// Write with the i_clk, or input clock.  All outputs read with the
	// bus clock, or i_wb_clk as we've called it here.
	assign	dw_trigger = (dr_primed)&&(
				((i_trigger)&&(!dw_disable_trigger))
				||(dw_manual_trigger));
	// }}}

	// dr_triggered
	// {{{
	initial	dr_triggered = 1'b0;
	always @(posedge i_data_clk)
	if (dw_reset)
		dr_triggered <= 1'b0;
	else if ((i_ce)&&(dw_trigger))
		dr_triggered <= 1'b1;
	// }}}

	//
	// Determine when memory is full and capture is complete
	//
	// Writes take place on the data clock

	// holdoff_counter
	// {{{
	// The counter is unsigned
	initial	holdoff_counter = 0;
	always @(posedge i_data_clk)
	if (dw_reset)
		holdoff_counter <= 0;
	else if ((i_ce)&&(dr_triggered)&&(!dr_stopped))
		holdoff_counter <= holdoff_counter + 1'b1;
	// }}}

	// dr_stopped
	// {{{
	initial	dr_stopped = 1'b0;
	always @(posedge i_data_clk)
	if ((!dr_triggered)||(dw_reset))
		dr_stopped <= 1'b0;
	else if ((i_ce)&&(!dr_stopped))
	begin
		if (HOLDOFFBITS > 1) // if (i_ce)
			dr_stopped <= (holdoff_counter >= br_holdoff);
		else if (HOLDOFFBITS <= 1)
			dr_stopped <= ((i_ce)&&(dw_trigger));
	end
	// }}}

	always @(posedge i_data_clk)
	if (dw_reset)
		dr_stop_pipe <= 0;
	else if (i_ce)
		dr_stop_pipe <= { dr_stop_pipe[(DLYSTOP-2):0], dr_stopped };

	assign	dw_final_stop = dr_stop_pipe[(DLYSTOP-1)];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// A big part of this scope is the run length of any particular
	// data value.  Hence, when the address line (i.e. data[31])
	// is high on decompression, the run length field will record an
	// address difference.
	//
	// To implement this, we set our run length to zero any time the
	// data changes, but increment it on all other clocks.  Should the
	// address difference get to our maximum value, we let it saturate
	// rather than overflow.

	// dr_force_write, dr_force_inhibit
	// {{{
	//
	// The "dr_force_write" logic here is designed to make sure we write
	// at least every MAX_STEP samples, and that we stop as soon as
	// we are able.  Hence, if an interface is slow
	// and idle, we'll at least prime the scope, and even if the interface
	// doesn't have enough transitions to fill our buffer, we'll at least
	// fill the buffer with repeats.
	//
	initial	ck_addr = 0;
	initial	dr_force_write = 1'b0;
	always @(posedge i_data_clk)
	if (dw_reset)
	begin
		dr_force_write    <= 1'b1;
		dr_force_inhibit  <= 1'b0;
	end else if (i_ce)
	begin
		dr_force_inhibit <= (dr_force_write);
		if ((dr_run_timeout)&&(!dr_force_write)&&(!dr_force_inhibit))
			dr_force_write <= 1'b1;
		else if (((dw_trigger)&&(!dr_triggered))||(!dr_primed))
			dr_force_write <= 1'b1;
		else
			dr_force_write <= 1'b0;
	end
	// }}}

	// ck_addr: Keep track of how long it has been since the last write
	// {{{
	always @(posedge i_data_clk)
	if (dw_reset)
		ck_addr <= 0;
	else if (i_ce)
	begin
		if ((dr_force_write)||(new_data)||(dr_stopped))
			ck_addr <= 0;
		else
			ck_addr <= ck_addr + 1'b1;
	end
	// }}}

	// dr_run_timeout
	// {{{
	always @(posedge i_data_clk)
	if (dw_reset)
		dr_run_timeout <= 1'b1;
	else if (i_ce)
		dr_run_timeout <= (ck_addr >= MAX_STEP-1'b1);
	// }}}

	// new_data
	// {{{
	always @(posedge i_data_clk)
	if (dw_reset)
		new_data <= 1'b1;
	else if (i_ce)
		new_data <= (i_data != qd_data);
	// }}}

	// qd_data
	// {{{
	always @(posedge i_data_clk)
	if (i_ce)
		qd_data <= i_data;
	// }}}

	// w_data
	// {{{
	generate if (NELM == BUSW-1)
	begin : GEN_WDATA
		assign w_data = qd_data;
	end else begin : GEN_DATA_FILL
		assign w_data = { {(BUSW-NELM-1){1'b0}}, qd_data };
	end endgenerate
	// }}}

	// imm_val, imm_adr, lst_val, lst_adr
	// {{{
	// To do our RLE compression, we keep track of two registers: the most
	// recent data to the device (imm_ prefix) and the data from one
	// clock ago.  This allows us to suppress writes to the scope which
	// would otherwise be two address writes in a row.
	initial	lst_adr = 1'b1;
	initial	imm_adr = 1'b1;
	always @(posedge i_data_clk)
	if (dw_reset)
	begin
		imm_val <= 31'h0;
		imm_adr <= 1'b1;
		lst_val <= 31'h0;
		lst_adr <= 1'b1;
	end else if (i_ce)
	begin
		if ((new_data)||(dr_force_write)||(dr_stopped))
		begin
			imm_val <= w_data;
			imm_adr <= 1'b0; // Last thing we wrote was data
			lst_val <= imm_val;
			lst_adr <= imm_adr;
		end else begin
			imm_val <= ck_addr; // Minimum value here is '1'
			imm_adr <= 1'b1; // This (imm) is an address
			lst_val <= imm_val;
			lst_adr <= imm_adr;
		end
	end
	// }}}

	// record_ce
	// {{{
	// Here's where we suppress writing pairs of address words to the
	// scope at once.
	//
	initial			record_ce = 1'b0;
	always @(posedge i_data_clk)
		record_ce <= (i_ce)&&((!lst_adr)||(!imm_adr))&&(!dr_stop_pipe[2]);
	// }}}

	// r_data
	// {{{
	always @(posedge i_data_clk)
		r_data <= ((!lst_adr)||(!imm_adr))
			? { lst_adr, lst_val }
			: { {(32 - NELM){1'b0}}, qd_data };
	// }}}

	//
	//	Actually do our writes to memory.  Record, via 'primed' when
	//	the memory is full.
	//
	//	The 'waddr' address that we are using really crosses two clock
	//	domains.  While writing and changing, it's in the data clock
	//	domain.  Once stopped, it becomes part of the bus clock domain.
	//	The clock transfer on the stopped line handles the clock
	//	transfer for these signals.
	//

	// waddr, dr_primed
	// {{{
	initial	waddr = {(LGMEM){1'b0}};
	initial	dr_primed = 1'b0;
	always @(posedge i_data_clk)
	if (dw_reset) // For simulation purposes, supply a valid value
	begin
		waddr <= 0; // upon reset.
		dr_primed <= 1'b0;
	end else if (record_ce)
	begin
		// mem[waddr] <= i_data;
		waddr <= waddr + {{(LGMEM-1){1'b0}},1'b1};
		dr_primed <= (dr_primed)||(&waddr);
	end
	// }}}

	// mem[] <= r_data
	// {{{
	always @(posedge i_data_clk)
	if (record_ce)
		mem[waddr] <= r_data;
	// }}}


	//
	//
	//
	// Bus response
	//
	//
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Move the status signals back to the bus clock
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	generate if (SYNCHRONOUS > 0)
	begin : SYNCHRONOUS_RETURN
		assign	bw_stopped   = dw_final_stop;
		assign	bw_triggered = dr_triggered;
		assign	bw_primed    = dr_primed;
	end else begin : ASYNC_STATUS
		// {{{
		// These aren't a problem, since none of these are strobe
		// signals.  They goes from low to high, and then stays high
		// for many clocks.  Swapping is thus easy--two flip flops to
		// protect against meta-stability and we're done.
		//
		(* ASYNC_REG = "TRUE" *) reg	[2:0]	q_oflags;
		reg	[2:0]	r_oflags;
		initial	q_oflags = 3'h0;
		initial	r_oflags = 3'h0;
		always @(posedge bus_clock)
		if (bw_reset_request)
		begin
			q_oflags <= 3'h0;
			r_oflags <= 3'h0;
		end else begin
			q_oflags <= { dw_final_stop, dr_triggered, dr_primed };
			r_oflags <= q_oflags;
		end

		assign	bw_stopped   = r_oflags[2];
		assign	bw_triggered = r_oflags[1];
		assign	bw_primed    = r_oflags[0];
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read from the memory, using the bus clock.  Otherwise respond to bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Reads use the bus clock
	assign	bw_cyc_stb = (i_wb_stb);

	initial	br_pre_wb_ack = 1'b0;
	initial	br_wb_ack = 1'b0;
	always @(posedge bus_clock)
	begin
		if ((bw_reset_request)||(write_to_control))
			raddr <= 0;
		else if ((read_from_data)&&(bw_stopped))
			raddr <= raddr + 1'b1; // Data read, when stopped

		br_pre_wb_ack <= bw_cyc_stb;
		br_wb_ack <= (br_pre_wb_ack)&&(i_wb_cyc);
	end

	assign	o_wb_ack = br_wb_ack;

	always @(posedge bus_clock)
	if (read_from_data)
		this_addr <= raddr + waddr + 1'b1;
	else
		this_addr <= raddr + waddr;

	always @(posedge bus_clock)
		nxt_mem <= mem[this_addr];

	// holdoff sub-register
	// {{{
	assign full_holdoff[(HOLDOFFBITS-1):0] = br_holdoff;
	generate if (HOLDOFFBITS < 20)
	begin : GEN_FULL_HOLDOFF
		assign full_holdoff[19:(HOLDOFFBITS)] = 0;
	end endgenerate
	// }}}

	assign		bw_lgmem = LGMEM;

	// Bus read
	// {{{
	always @(posedge bus_clock)
	begin
		if (!read_address) // Control register read
			o_bus_data <= { bw_reset_request,
					bw_stopped,
					bw_triggered,
					bw_primed,
					bw_manual_trigger,
					bw_disable_trigger,
					(raddr == {(LGMEM){1'b0}}),
					bw_lgmem,
					full_holdoff  };
		else if (!bw_stopped) // read, prior to stopping
			//
			// *WARNING*: THIS READ IS NOT PROTECTED FROM
			// ASYNCHRONOUS COHERENCE ISSUES!
			//
			o_bus_data <= {1'b0, w_data };// Violates clk tfr rules
		else // if (i_wb_addr) // Read from FIFO memory
			o_bus_data <= nxt_mem; // mem[raddr+waddr];
	end
	// }}}

	assign	o_wb_data = o_bus_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Interrupt generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	br_level_interrupt = 1'b0;
	always @(posedge bus_clock)
	if ((bw_reset_complete)||(bw_reset_request))
		br_level_interrupt<= 1'b0;
	else
		br_level_interrupt<= (bw_stopped)&&(!bw_disable_trigger);

	assign	o_interrupt = (bw_stopped)&&(!bw_disable_trigger)
					&&(!br_level_interrupt);
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_bus_data[30:28], i_bus_data[25:HOLDOFFBITS],
			i_wb_sel };
	// verilator lint_on  UNUSED
	// }}}
endmodule
