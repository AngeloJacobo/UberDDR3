////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axisi2c.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is a lower level I2C driver for a master I2C byte-wise
//		interface.  It accepts commands via AXI-Stream, and reports
//	results via AXI Stream.
//
// Commands:
// {{{
//	3'h0,8'hxx	NOP
//	3'h1,8'hxx	START
//	3'h2,8'hxx	STOP	(Ignored if we are already busy)
//	3'h3,8'hdata	SEND
//	3'h4,8'hxx	RXK
//	3'h5,8'hxx	RXN
//	3'h6,8'hxx	RXLK
//	3'h7,8'hxx	RXLN
//	(4'h8)		WAIT	(for external interrupt.  Handled externally)
//	(4'h9)		HALT
//	(4'ha)		ABORT	(Return here following an unexpected NAK)
//	(4'hb)		TARGET	(Return here on any jump)
//	(4'hc)		JUMP	(Useful for repeats, handled externally)
//	(4'hd)		CHANNEL	(Sets the outgoing AXI stream channel ID)
// }}}
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
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module axisi2c #(
		parameter	OPT_WATCHDOG = 0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		//
		// Incoming instruction stream
		// {{{
		input	wire	S_AXIS_TVALID,
		output	wire	S_AXIS_TREADY,
		input	wire	[8+3-1:0]	S_AXIS_TDATA,
		// input wire			S_AXIS_TLAST, (unused)
		// }}}
		// Outgoing received data stream
		// {{{
		output	reg		M_AXIS_TVALID,
		input	wire		M_AXIS_TREADY,
		output	reg	[8-1:0]	M_AXIS_TDATA,
		output	reg		M_AXIS_TLAST,
		// }}}
		//
		input	wire	i_ckedge,
		output	wire	o_stretch,
		input	wire	i_scl, i_sda,
		output	reg	o_scl, o_sda,	// 1 = tristate, 0 = ground

		output	reg	o_abort
		// }}}
	);

	// Local declarations
	// {{{

	// Parameter, enumerations, and state declarations
	// {{{
	localparam [3:0]	IDLE_STOPPED  = 4'h0,
				START		= 4'h1,
				IDLE_ACTIVE   = 4'h2,
				STOP	= 4'h3,
				DATA	= 4'h4,
				CLOCK	= 4'h5,
				ACK	= 4'h6,
				CKACKLO	= 4'h7,
				CKACKHI	= 4'h8,
				RXNAK	= 4'h9,
				ABORT	= 4'ha,
				REPEAT_START = 4'hb,
				REPEAT_START2= 4'hc;
				// INIT  = 4'hd;	// Wait for SDA && SCL?

	localparam	D_RD = 1'b0, D_WR = 1'b1;

	localparam	[2:0]	CMD_NOOP	= 3'h0,
				CMD_START	= 3'h1,
				CMD_STOP	= 3'h2,
				CMD_SEND	= 3'h3,
				CMD_RXK		= 3'h4,
				CMD_RXN		= 3'h5,
				CMD_RXLK	= 3'h6,
				CMD_RXLN	= 3'h7;

	localparam [0:0]	OPT_ABORT_REQUEST = 1'b0;
	// }}}

	reg		last_byte, dir, will_ack; reg	[3:0]	state;
	reg	[2:0]	nbits;
	reg	[7:0]	sreg;

	reg		q_scl, q_sda, ck_scl, ck_sda, lst_scl, lst_sda;
	reg		stop_bit, channel_busy;
	wire		watchdog_timeout;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize the asynchronous inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	{ lst_scl, ck_scl, q_scl } = 3'b111;
	initial	{ lst_sda, ck_sda, q_sda } = 3'b111;

`ifndef	FORMAL
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		{ lst_scl, ck_scl, q_scl } <= 3'b111;
		{ lst_sda, ck_sda, q_sda } <= 3'b111;
	end else begin
		{ lst_scl, ck_scl, q_scl } <= { ck_scl, q_scl, i_scl };
		{ lst_sda, ck_sda, q_sda } <= { ck_sda, q_sda, i_sda };
	end
`else
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		lst_scl <= 1'b1;
		lst_sda <= 1'b1;
	end else begin
		lst_scl <= ck_scl;
		lst_sda <= ck_sda;
	end

	always @(*)
		{ ck_scl, q_scl } = {(2){i_scl}};
	always @(*)
		{ ck_sda, q_sda } = {(2){i_sda}};
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Channel busy, and watchdog
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	stop_bit  = 1'b0;
	initial	channel_busy = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		stop_bit     <= 1'b0;
		channel_busy <= 1'b0;
	end else begin
		stop_bit  <= (ck_scl)&&(lst_scl)&&( ck_sda)&&(!lst_sda);

		if (!ck_scl || !ck_sda)
			channel_busy <= 1'b1;
		else if (stop_bit)
			channel_busy <= 1'b0;
	end

	generate if (OPT_WATCHDOG > 0)
	begin : GEN_WATCHDOG
		// {{{
		reg	[OPT_WATCHDOG:0]	r_watchdog_counter;
		reg				r_watchdog_timeout;

		initial	r_watchdog_counter = 0;
		initial	r_watchdog_timeout = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			r_watchdog_counter <= 0;
			r_watchdog_timeout <= 0;
		end else begin
			if (!channel_busy)
				r_watchdog_counter <= 0;
			else if (!r_watchdog_counter[OPT_WATCHDOG])
				r_watchdog_counter <= r_watchdog_counter + 1'b1;

			r_watchdog_timeout <= r_watchdog_counter[OPT_WATCHDOG];
		end

		assign	watchdog_timeout = r_watchdog_timeout;
		// }}}
	end else begin : NO_WATCHDOG
		assign	watchdog_timeout = 1'b0;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Master state machine
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	state  = IDLE_STOPPED;
	initial	nbits  = 3'h0;
	initial	sreg   = 8'hff;
	initial	o_scl  = 1'b1;
	initial	o_sda  = 1'b1;
	always @(posedge S_AXI_ACLK)
	begin
		if (i_ckedge) case(state)
		IDLE_STOPPED: begin
			// {{{
			nbits <= 0;
			will_ack  <= 1'b1;
			last_byte <= 1'b0;

			sreg <= (OPT_LOWPOWER) ? 8'h0 : S_AXIS_TDATA[7:0];
			dir  <= D_RD;
			if (S_AXIS_TVALID && S_AXIS_TREADY)
			begin
				// NOTE: We aren't detecting collisions here.
				// Perhaps we should be, but we can't force
				// the driver to seize if something is wrong.
				// Hence, if i_ckedge is true, S_AXIS_TREADY
				// must also be true.
				case(S_AXIS_TDATA[10:8])
				CMD_NOOP:  begin end
				CMD_START: begin
					// {{{
					o_sda <= 1'b0;
					o_scl <= 1'b1;
					state <= START;
					end
					// }}}
				CMD_STOP:  begin
					// {{{
					// We are already stopped.  Therefore
					// do nothing.
					end
					// }}}
				CMD_RXK:   begin
					// {{{
					o_sda <= 1'b0;
					o_scl <= 1'b1;
					state <= START;

					nbits <= 3'h7;
					end
					// }}}
				CMD_RXN:   begin
					// {{{
					will_ack <= 1'b0;
					nbits <= 3'h7;

					o_sda <= 1'b0;
					o_scl <= 1'b1;
					state <= START;
					end
					// }}}
				CMD_RXLK:  begin
					// {{{
					o_sda <= 1'b0;
					o_scl <= 1'b1;
					state <= START;

					last_byte <= 1'b1;
					nbits <= 3'h7;
					end
					// }}}
				CMD_RXLN:  begin
					// {{{
					o_sda <= 1'b0;
					o_scl <= 1'b1;
					state <= START;

					last_byte <= 1'b1;
					will_ack <= 1'b0;
					nbits <= 3'h7;
					end
					// }}}
				CMD_SEND:  begin
					// {{{
					o_sda <= 1'b0;
					o_scl <= 1'b1;
					state <= START;

					dir   <= D_WR;
					nbits <= 3'h7;
					sreg  <= S_AXIS_TDATA[7:0];
					end
					// }}}
				endcase

				if (OPT_ABORT_REQUEST && (!ck_scl || !ck_sda || channel_busy))
				begin
					state <= ABORT;
					nbits <= 0;
					{ o_scl, o_sda } <= 2'b11;
				end
			end end
			// }}}
		START: begin
			// {{{
			if (nbits[2])
				state <= DATA;
			else
				state <= IDLE_ACTIVE;
			o_scl <= 1'b0;
			o_sda <= 1'b0;
			end
			// }}}
		IDLE_ACTIVE: begin
			// {{{
			nbits <= 0;
			will_ack  <= 1'b1;
			last_byte <= 1'b0;

			sreg <= (OPT_LOWPOWER) ? 8'h0 : S_AXIS_TDATA[7:0];
			dir  <= D_RD;
			o_sda <= 1'b0;
			o_scl <= 1'b0;
			if (S_AXIS_TVALID && S_AXIS_TREADY)
			begin
				case(S_AXIS_TDATA[10:8])
				CMD_NOOP:  begin end
				CMD_START: begin
					// {{{
					o_scl <= 1'b0;
					o_sda <= 1'b1;
					state <= REPEAT_START;
					end
					// }}}
				CMD_STOP:  begin
					// {{{
					o_scl <= 1'b1;
					o_sda <= 1'b0;
					state <= STOP;
					end
					// }}}
				CMD_RXK:   begin
					// {{{
					nbits <= 3'h7;
					o_sda <= 1'b0;
					o_scl <= 1'b0;
					state <= DATA;
					end
					// }}}
				CMD_RXN:   begin
					// {{{
					will_ack <= 1'b0;
					nbits <= 3'h7;

					o_sda <= 1'b0;
					o_scl <= 1'b0;
					state <= DATA;
					end
					// }}}
				CMD_RXLK:  begin
					// {{{
					last_byte <= 1'b1;
					nbits <= 3'h7;
					o_sda <= 1'b0;
					o_scl <= 1'b0;
					state <= DATA;
					end
					// }}}
				CMD_RXLN:  begin
					// {{{
					last_byte <= 1'b1;
					will_ack <= 1'b0;
					nbits <= 3'h7;
					o_sda <= 1'b0;
					o_scl <= 1'b0;
					state <= DATA;
					end
					// }}}
				CMD_SEND:  begin
					// {{{
					dir   <= D_WR;
					nbits <= 3'h7;
					o_sda <= 1'b0;
					o_scl <= 1'b0;
					state <= DATA;
					sreg  <= S_AXIS_TDATA[7:0];
					end
					// }}}
				endcase
			end end
			// }}}
		STOP: begin
			// {{{
			o_scl <= 1'b1;
			if (ck_scl) begin
				// o_scl == 1 on entry
				// o_sda == 0
				state <= IDLE_STOPPED;
				o_sda <= 1'b1;
			end end
			// }}}
		REPEAT_START: if (!o_stretch) begin
			// {{{
				// SDA && !SCL on entry
				o_scl <= 1'b1;
				o_sda <= 1'b1;
				state <= REPEAT_START2;

				if (o_sda != ck_sda)
				begin
					{ o_scl, o_sda } <= 2'b11;
					state <= ABORT;
				end
			end
			// }}}
		REPEAT_START2: if (!o_stretch) begin
			// {{{
				// SDA && SCL on entry
				o_scl <= 1'b1;
				o_sda <= 1'b0;
				state <= START;

				if (!ck_sda || !ck_scl)
				begin
					{ o_scl, o_sda } <= 2'b11;
					state <= ABORT;
				end
			end
			// }}}
		//
		DATA: begin
			// {{{
			o_scl <= 1'b0;
			o_sda <= sreg[7] || (dir == D_RD);
			if (o_sda == (sreg[7] || (dir == D_RD)))
				state <= CLOCK;

			if (ck_scl)
				state <= DATA;
			end
			// }}}
		CLOCK: begin
			// {{{
			if (ck_scl)
			begin
				o_scl <= 1'b0;
				sreg  <= { sreg[6:0], ck_sda };
				if (nbits > 0)
					nbits <= nbits - 1;

				if (dir == D_WR && ck_sda != sreg[7])
				begin
					state <= ABORT;
					{ o_scl, o_sda } <= 2'b11;
				end else if (nbits == 0)
					state <= ACK;
				else
					state <= DATA;
			end else
				o_scl <= 1'b1;
			end
			// }}}
		ACK: begin
			// {{{
			o_scl <= 1'b0;
			o_sda <= (dir == D_WR) || !will_ack;

			// Clock stretch
			if (!ck_scl) case(dir)
			D_RD: if (o_sda != will_ack)
				state <= CKACKLO;
			D_WR: state <= CKACKLO;
			endcase

			if (ck_scl)
				state <= ACK;
			end
			// }}}
		CKACKLO: begin
			// {{{
			// !o_scl on entry
			o_scl <= 1'b1;
			o_sda <= (dir == D_WR) || !will_ack;
			state <= CKACKHI;
			end
			// }}}
		CKACKHI: begin
			// {{{
			o_scl <= 1'b1;
			if (ck_scl) // Check for clock stretching
			begin
				o_scl <= 1'b0;
				o_sda <= 1'b0;

				if (dir == D_WR && ck_sda)
					state <= RXNAK;
				else
					state <= IDLE_ACTIVE;
			end end
			// }}}
		RXNAK: begin
			// {{{
			// We received a NAK.  Protocol failure!
			// Send a STOP bit and return to idle
			o_scl <= 1'b0;
			o_sda <= 1'b0;
			if (!ck_scl && !ck_sda)
			begin
				o_scl <= 1'b1;
				state <= STOP;
			end end
			// }}}
		ABORT: begin
			// {{{
			// COLLISION!!!
			o_scl <= 1'b1;
			o_sda <= 1'b1;
			if (!channel_busy && ck_scl && ck_sda)
				state <= IDLE_STOPPED;
			else if (watchdog_timeout)
			begin
				o_scl <= 1'b1;
				o_sda <= 1'b0;
				state <= STOP;
			end end
			// }}}
		default: begin
			// {{{
			o_scl <= 1'b1;
			o_sda <= 1'b1;
			if (!channel_busy)
				state <= IDLE_STOPPED;
			else if (watchdog_timeout)
			begin
				o_sda <= 1'b0;
				state <= STOP;
			end end
			// }}}
		endcase

		if (!S_AXI_ARESETN)
		begin
			o_scl <= 1'b1;
			o_sda <= 1'b1;
			state <= IDLE_STOPPED;
		end
	end

	assign	S_AXIS_TREADY = i_ckedge && (state == IDLE_STOPPED
				|| state == IDLE_ACTIVE);

	// o_abort
	// {{{
	initial	o_abort = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_abort <= 1'b0;
	else if (!i_ckedge || (o_stretch && !S_AXIS_TREADY))
		o_abort <= 1'b0;
	else begin
		o_abort <= 1'b0;

		// RXNAK
		if (ck_scl && dir == D_WR && state == CKACKHI && ck_sda)
			o_abort <= 1'b1;

		// COLLISION ABORT!!
		if (ck_scl && dir == D_WR && state == CLOCK && ck_sda != sreg[7])
			o_abort <= 1;

		// COLLISION ABORT ON REQUEST!!
		if (state == REPEAT_START && (o_sda != ck_sda))
			o_abort <= 1;
		if (state == REPEAT_START2 && (!ck_scl || !ck_sda))
			o_abort <= 1;

		if (OPT_ABORT_REQUEST && state == IDLE_STOPPED
			&& (!ck_scl || !ck_sda || channel_busy)&& S_AXIS_TVALID)
			o_abort <= 1;
	end
	// }}}

	// Stretch the idle clock, so we're always ready to accept once idle
	// is over.
	assign	o_stretch = (o_scl && !ck_scl)
		||(!S_AXIS_TVALID && (state == IDLE_STOPPED || state == IDLE_ACTIVE));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing AXI Stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// M_AXIS_TVALID
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TVALID <= 1'b0;
	else if (i_ckedge && !o_stretch && state == CKACKHI && dir == D_RD)
		M_AXIS_TVALID <= 1'b1;
	else if (M_AXIS_TREADY)
		M_AXIS_TVALID <= 1'b0;
	// }}}

	// M_AXIS_TDATA, M_AXIS_TLAST
	// {{{
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
	begin
		M_AXIS_TDATA <= 0;
		M_AXIS_TLAST <= 0;
	end else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		M_AXIS_TDATA <= sreg;
		M_AXIS_TLAST <= last_byte;

		if (OPT_LOWPOWER && (!i_ckedge || o_stretch
				|| state != CKACKHI || dir != D_RD || ck_sda))
		begin
			M_AXIS_TDATA <= 0;
			M_AXIS_TLAST <= 0;
		end
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
`ifdef	I2CCPU
`define	ASSUME	assert
`else
`define	ASSUME	assume
`endif
	// Local declarations
	// {{{
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		`ASSUME(!S_AXI_ARESETN);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*) if (!f_past_valid) assume({ i_scl, i_sda } == 2'b11);
	always @(*) if (!o_scl) assume(!i_scl);
	always @(*) if (!o_sda) assume(!i_sda);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && i_ckedge && o_stretch))
		`ASSUME(i_ckedge);

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !$past(S_AXI_ARESETN))
	begin
		if (S_AXI_ARESETN && !$past(S_AXI_ARESETN))
			`ASSUME(!i_ckedge);
	end else case({ lst_scl, ck_scl, q_scl, i_scl })
	4'b0000: begin end
	4'b0001: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b0011: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b0111: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b1111: begin end
	4'b1110: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b1100: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b1000: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	default: assume(0);
	endcase

	always @(posedge S_AXI_ACLK)
	case({ lst_sda, ck_sda, q_sda, i_sda })
	4'b0000: begin end
	4'b0001: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b0011: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b0111: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b1111: begin end
	4'b1110: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b1100: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	4'b1000: assume($past(i_ckedge && o_stretch) || !i_ckedge);
	default: assume(0);
	endcase

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid)
	begin
	end else if (!$past(S_AXI_ARESETN))
	begin
		`ASSUME(!S_AXIS_TVALID);

		assert(!M_AXIS_TVALID);

		if (OPT_LOWPOWER)
		begin
			assert(M_AXIS_TDATA == 0);
			assert(M_AXIS_TLAST == 0);
		end
	end else begin
		if ($past(o_abort))
			`ASSUME(!S_AXIS_TVALID);
		else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
		begin
			`ASSUME(S_AXIS_TVALID);
			`ASSUME($stable(S_AXIS_TDATA));
		end

		if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
		begin
			assert(M_AXIS_TVALID);
			assert($stable(M_AXIS_TDATA));
			assert($stable(M_AXIS_TLAST));
		end

		if (OPT_LOWPOWER && !M_AXIS_TVALID)
		begin
			assert(M_AXIS_TDATA == 0);
			assert(M_AXIS_TLAST == 0);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal consistency checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (S_AXI_ARESETN && (state != IDLE_STOPPED) && (state != IDLE_ACTIVE))
		assert(!S_AXIS_TREADY);

	always @(*)
	if (S_AXI_ARESETN) case(state)
	IDLE_STOPPED: begin
		// {{{
		assert(o_scl);
		assert(o_sda);
		end
		// }}}
	START: begin
		// {{{
		assert( o_scl);
		assert(!o_sda);
		assert(nbits == 7 || nbits == 0);
		end
		// }}}
	IDLE_ACTIVE: begin
		// {{{
		assert(!o_sda);
		assert(!o_scl);
		assert(nbits == 0);
		end
		// }}}
	STOP: begin
		// {{{
		// o_sda == 0
		// o_scl == 1 on entry
		assert( o_scl);
		assert(!o_sda);
		end
		// }}}
	REPEAT_START: begin
		// {{{
		assert(!o_scl);
		assert( o_sda);
		assert(nbits == 7 || nbits == 0);
		end
		// }}}
	REPEAT_START2: begin
		// {{{
		assert(o_sda && o_scl);
		assert(nbits == 7 || nbits == 0);
		end
		// }}}
	//
	DATA: begin
		// {{{
		assert(!o_scl);
		if (dir == D_RD)
			assert(o_sda || nbits == 7);
		end
		// }}}
	CLOCK: begin
		// {{{
		if (dir == D_RD)
			assert(o_sda);
		else
			assert(o_sda == sreg[7]);
		end
		// }}}
	ACK: begin
		// {{{
		assert(!o_scl);
		assert(nbits == 0);
		end
		// }}}
	CKACKLO: begin
		// {{{
		assert(!o_scl);
		assert(o_sda == ((dir == D_WR) || !will_ack));
		assert(nbits == 0);
		end
		// }}}
	CKACKHI: begin
		// {{{
		assert(o_scl);
		assert(o_sda == ((dir == D_WR) || !will_ack));
		assert(nbits == 0);
		end
		// }}}
	RXNAK: begin
		// {{{
		assert(!o_scl && !o_sda);
		assert(nbits == 0);
		end
		// }}}
	ABORT: begin
		// {{{
		// COLLISION!!!
		assert(o_scl);
		assert(o_sda);
		end
		// }}}
	default: begin
		// {{{
		assert(0);
		end
		// }}}
	endcase

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN) && $past(o_scl))
	begin
		if ($past(!ck_scl) && !$past(S_AXIS_TREADY)
			&& ($past(ck_sda == o_sda)))
		begin
			// HALT
			assert($stable(o_scl));
			if ($past(watchdog_timeout && state == ABORT && o_sda && i_ckedge))
			begin
				assert(state == STOP && !o_sda);
			end else begin
				assert($stable(state) || state == ABORT);
				assert($stable(o_sda));
			end
		end
	end

	always @(*)
	if (S_AXI_ARESETN && o_abort)
		assert(state == RXNAK || state == ABORT);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
	begin
		if ($rose(state == ABORT))
		begin
			assert(o_abort);	// Collision
		end else if ($rose(state == RXNAK))
		begin
			assert(o_abort);	// Failed NAK
		end else
			assert(!o_abort);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[3:0]	cvr_state, cvr_send;
	(* anyconst *)	reg nvr_abort;

	always @(*)
	if (nvr_abort)
		assume(!o_abort && state != ABORT && state != RXNAK);

	// *LONG* Cover sequence
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || state == ABORT || o_abort)
		cvr_state <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY)
	begin
		case(cvr_state)
		4'h0: cvr_state = (S_AXIS_TDATA[10:8] == CMD_START) ? 4'h1 : 0;
		4'h1: cvr_state = (S_AXIS_TDATA=={CMD_SEND, 8'h8a })? 4'h2 : 0;
		4'h2: cvr_state = (S_AXIS_TDATA=={CMD_SEND, 8'hd1 })? 4'h3 : 0;
		4'h3: cvr_state = (S_AXIS_TDATA[10:8] == CMD_START) ? 4'h4 : 0;
		4'h4: cvr_state = (S_AXIS_TDATA[10:8] == CMD_SEND)  ? 4'h5 : 0;
		4'h5: cvr_state = (S_AXIS_TDATA[10:8] == CMD_STOP)  ? 4'h6 : 0;
		endcase
	end

	always @(*)
	if (S_AXI_ARESETN && !o_abort)
	begin
		case(cvr_state)
		4'h0: begin
			cover(S_AXIS_TREADY);			// Step   1
			end
		4'h1: begin
			cover(S_AXIS_TREADY);			// Step   5
			assert(nbits == 0);
			end
		4'h2: begin
			// Measure 5-6 cycles per clock
			cover(S_AXIS_TREADY);			// Step  57
			end
		4'h3: begin
			// Measure 5-6 cycles per clock
			cover(S_AXIS_TREADY);			// Step 101
			end
		4'h4: begin
			cover(S_AXIS_TREADY && nvr_abort);	// Step 115
			end
		4'h5: cover(S_AXIS_TREADY);			// Step 161
		4'h6: cover(S_AXIS_TREADY);
		default: assert(0);
		endcase
	end
	// }}}

	// Read check
	// {{{
	always @(*)
	if (S_AXI_ARESETN && !o_abort)
	begin
		if (M_AXIS_TVALID && state == IDLE_STOPPED)
		begin
			cover( M_AXIS_TLAST && M_AXIS_TDATA == 8'h9f); // S 54
			cover(!M_AXIS_TLAST && M_AXIS_TDATA == 8'ha5); // S 54
		end
	end
	// }}}

	// cvr_send
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || o_abort || state == ABORT)
		cvr_send <= 0;
	else case(cvr_send)
	4'h0: if (S_AXIS_TVALID && S_AXIS_TREADY
					&& S_AXIS_TDATA[10:8] == CMD_SEND)
		begin
			cvr_send <= 1;
		end else if (S_AXIS_TVALID && S_AXIS_TREADY
					&& S_AXIS_TDATA[10:8] == CMD_START)
		begin
			cvr_send <= 4'h8;
		end
	4'h1: if (state == DATA)
		begin
		cvr_send <= 2;
		end
	4'h2: if (state == IDLE_ACTIVE)
		begin
		cvr_send <= 3;
		end
	4'h3: if (state == IDLE_STOPPED)
		begin
		cvr_send <= 4'h4;
		end
	4'h8: if (state == IDLE_ACTIVE)
		begin
		cvr_send <= 4'h9;
		end
	4'h9: if (state == STOP)
		begin
			cvr_send <= 4'ha;
		end else if (state == REPEAT_START)
		begin
			cvr_send <= 4'hc;
		end
	4'ha: if (state == IDLE_STOPPED)
		begin
			cvr_send <= 4'hb;
		end
	4'hc: if (state == IDLE_STOPPED)
		begin
			cvr_send <= 4'hd;
		end
	default: begin end
	endcase

	always @(*)
	if (S_AXI_ARESETN)
	begin
		cover(cvr_send == 4'h1);	// Step  3
		cover(cvr_send == 4'h2);	// Step  5
		cover(cvr_send == 4'h3);	// Step 50
		cover(cvr_send == 4'h4);	// Step 54
		//
		cover(cvr_send == 4'h8);	// Step  3
		cover(cvr_send == 4'h9);	// Step  5
		cover(cvr_send == 4'ha);	// Step  7
		cover(cvr_send == 4'hb);	// Step  9

		cover(cvr_send == 4'hc);	// Step  7
		cover(cvr_send == 4'hd);	// Step 17
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Assume no collisions
	// {{{
	always @(*)
	if ((dir == D_WR && state == CLOCK)||(dir == D_RD && state == CKACKHI))
		assume(i_sda == o_sda);
	else if (state == REPEAT_START || state == REPEAT_START2 || state == START)
		assume((i_scl == o_scl)&&(i_sda == o_sda));
	// }}}

	// No one else adjusts our clock
	// {{{
	always @(posedge S_AXI_ACLK)
	if ($past(o_scl && i_scl) && o_scl)
		assume(i_scl);
	// }}}

	// No bit adjustments mid clock cycle?  What about start & stop?
	// }}}
`endif
// }}}
endmodule
