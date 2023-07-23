////////////////////////////////////////////////////////////////////////////////
//
// Filename:	lli2cm.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is a lower level I2C driver for a master I2C byte-wise
//		interface.  This particular interface is designed to handle
//	all byte level ineraction with the actual port.  The external interface
//	to this module is something akin to wishbone, although without the
//	address register.
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
module lli2cm #(
		// {{{
		parameter	[5:0]	TICKBITS		 = 20,
		parameter	[(TICKBITS-1):0] CLOCKS_PER_TICK = 20'd1000,
		parameter	[0:0]		PROGRAMMABLE_RATE= 1'b1
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		//
		input	wire	[(TICKBITS-1):0]	i_clocks,
		//
		input	wire		i_cyc, i_stb, i_we,
		input	wire	[7:0]	i_data,
		output	reg		o_ack, o_busy, o_err,
		output	reg	[7:0]	o_data,
		input	wire		i_scl, i_sda,
		output	reg		o_scl, o_sda,
		output	wire	[31:0]	o_dbg
		// }}}
	);

	// Local declarations
	// {{{
	localparam [3:0]	I2CMIDLE	= 4'h0,
				I2CMSTART	= 4'h1,
				I2CMBIT_SET	= 4'h2,
				I2CMBIT_POSEDGE	= 4'h3,
				I2CMBIT_NEGEDGE	= 4'h4,
				I2CMBIT_CLR	= 4'h5,
				I2CMACK_SET	= 4'h6,
				I2CMACK_POSEDGE	= 4'h7,
				I2CMACK_NEGEDGE	= 4'h8,
				I2CMACK_CLR	= 4'h9,
				I2CMRESTART	= 4'ha,
				I2CMRESTART_POSEDGE= 4'hb,
				I2CMRESTART_NEGEDGE= 4'hc,
				I2CMSTOP	= 4'hd,
				I2CMSTOPPD	= 4'he,
				I2CMFINAL	= 4'hf;

	reg	[(TICKBITS-1):0]	clocks_per_tick;

	reg	[3:0]	state;
	reg	[(TICKBITS-1):0]	clock;
	reg		zclk, r_cyc, r_err, r_we;
	reg	[2:0]	nbits;
	reg	[7:0]	r_data;

	reg	q_scl, q_sda, ck_scl, ck_sda, lst_scl, lst_sda;

	reg	start_bit, stop_bit, channel_busy;
	reg		watchdog_timeout;
	reg	[27:0]	watchdog;

	always @(posedge i_clk)
		clocks_per_tick <= (PROGRAMMABLE_RATE) ? i_clocks
				: CLOCKS_PER_TICK;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize any asynchronous inputs
	// {{{
	initial	q_scl   = 1'b1;
	initial	q_sda   = 1'b1;
	initial	ck_scl  = 1'b1;
	initial	ck_sda  = 1'b1;
	initial	lst_scl = 1'b1;
	initial	lst_sda = 1'b1;
	always @(posedge i_clk)
	begin
		q_scl   <= i_scl;
		ck_scl  <= q_scl;
		lst_scl <= ck_scl;

		q_sda   <= i_sda;
		ck_sda  <= q_sda;
		lst_sda <= ck_sda;
	end
	// }}}

	// start_bit, stop_bit, channel_busy
	// {{{
	initial	start_bit = 1'b0;
	initial	stop_bit  = 1'b0;
	initial	channel_busy = 1'b0;
	always @(posedge i_clk)
	begin
		start_bit <= (ck_scl)&&(lst_scl)&&(!ck_sda)&&( lst_sda);
		stop_bit  <= (ck_scl)&&(lst_scl)&&( ck_sda)&&(!lst_sda);
		if ((!ck_scl)||(!ck_sda))
			channel_busy <= 1'b1;
		else if (stop_bit)
			channel_busy <= 1'b0;
	end
	// }}}

	// Watchdog, and watchdog_timeout
	// {{{
	always @(posedge i_clk)
	begin
		if (!channel_busy)
			watchdog <= 0;
		else if (!(&watchdog))
			watchdog <= watchdog + 1'b1;
		watchdog_timeout <= (&watchdog);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate a clock we can use
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	clock = CLOCKS_PER_TICK;
	initial	zclk  = 1'b1;
	always @(posedge i_clk)
		if (state == I2CMIDLE)
		begin
			if (watchdog_timeout)
			begin
				clock <= 0;
				zclk  <= 1'b1;
			end else if (((i_stb)&&(!o_busy))||(channel_busy))
			begin
				clock <= clocks_per_tick;
				zclk  <= 1'b0;
			end else begin
				clock <= 0;
				zclk  <= 1'b1;
			end
		end else if ((clock == 0)||((o_scl)&&(!ck_scl)))
		begin
			clock <= clocks_per_tick;
			zclk <= 1'b0;
		end else begin	
			clock <= clock - 1'b1;
			zclk <= (clock == 1);
		end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Massive state machine
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	state  = I2CMIDLE;
	initial	o_ack  = 1'b0;		
	initial	o_busy = 1'b0;
	initial	r_cyc  = 1'b1;
	initial	nbits  = 3'h0;
	initial	r_we   = 1'b0;
	initial	r_data = 8'h0;
	initial	o_scl  = 1'b1;
	initial	o_sda  = 1'b1;
	always @(posedge i_clk)
	begin
		o_ack  <= 1'b0;
		o_err  <= 1'b0;
		o_busy <= 1'b1;
		r_cyc <= (r_cyc) && (i_cyc);
		if (zclk) case(state)
			I2CMIDLE: begin
				r_err <= 1'b0;
				nbits <= 3'h0;
				r_cyc <= i_cyc;
				o_sda <= 1'b1;
				o_scl <= 1'b1;
				if ((i_stb)&&(!o_busy)) begin
					r_data <= i_data;
					r_we   <= i_we; 
					nbits  <= 0;
					state  <= I2CMSTART;
					o_sda  <= 1'b0;
				end else if (watchdog_timeout)
				begin
					o_sda <= 1'b0;
					o_scl <= 1'b0;
					state  <= I2CMSTOP;
				end else
					o_busy <= 1'b0;
			    end
			I2CMSTART: begin
				state <= I2CMBIT_SET;
				o_sda <= 1'b0;
				o_scl <= 1'b0;
			    end
			I2CMBIT_SET: begin
				o_sda <= (r_we)?r_data[7] : 1'b1;
				if (r_we)
					r_data <= { r_data[6:0], ck_sda };
				nbits <= nbits - 1'b1;
				state <= I2CMBIT_POSEDGE;
				end
			I2CMBIT_POSEDGE: begin
				if (!r_we)
					r_data <= { r_data[6:0], ck_sda };
				o_scl <= 1'b1;
				r_err <= (r_err)||((r_we)&&(o_sda != ck_sda));
				state <= I2CMBIT_NEGEDGE;
				end
			I2CMBIT_NEGEDGE: begin
				if (ck_scl)
				    begin
					o_scl <= 1'b0;
					state <= I2CMBIT_CLR;
				    end
				end
			I2CMBIT_CLR: begin
				if (nbits != 3'h0)
					state <= I2CMBIT_SET;
				else if ((!r_we)&&((!i_stb)||(!r_cyc)))
					state <= I2CMSTOP;
				else
					state <= I2CMACK_SET;
				end
			I2CMACK_SET: begin
					o_sda <= (r_we) ? 1'b1 : 1'b0;
					state <= I2CMACK_POSEDGE;
				end
			I2CMACK_POSEDGE: begin
					o_scl <= 1'b1;
					state <= I2CMACK_NEGEDGE;
				end
			I2CMACK_NEGEDGE: begin
					if (ck_scl)
					begin
						o_scl <= 1'b0;
						r_err <= (r_err)||((r_we)&&(ck_sda));
						state <= I2CMACK_CLR;
					end
				end
			I2CMACK_CLR: begin
				o_err  <= r_err;
				o_data <= r_data;
				o_ack  <= 1'b1;
				o_sda  <= 1'b0;
				o_scl  <= 1'b0;
				if (r_err)
					state <= I2CMSTOP;
				else if ((i_stb)&&(r_cyc)&&(i_cyc))
				begin
					o_busy <= 1'b0;
					r_we   <= i_we;
					r_data <= i_data;
				//	if (r_we != i_we)
				//		state <= I2CMRESTART;
				//	else
						state <= I2CMSTART;
					nbits <= 0;
				end else if ((i_cyc)&&(i_stb)&&(!r_cyc))
					state <= I2CMRESTART;
				else // if (!i_cyc)
					state <= I2CMSTOP;
				end
			I2CMRESTART: begin
				o_sda <= 1'b1;
				state <= I2CMRESTART_POSEDGE;
				end
			I2CMRESTART_POSEDGE: begin
				o_sda <= 1'b1;
				o_scl <= 1'b1;
				state <= I2CMRESTART_NEGEDGE;
				end
			I2CMRESTART_NEGEDGE: begin
				o_sda <= 1'b1;
				o_scl <= 1'b1;
				if (ck_scl)
				  begin
					state <= I2CMSTART;
					o_sda <= 1'b0;
				  end
				end
			I2CMSTOP: begin
				o_scl <= 1'b0;
				o_sda <= 1'b0;
				if ((ck_scl == 1'b0)&&(ck_sda == 1'b0))
				begin
					o_scl <= 1'b1;
					o_sda <= 1'b0; // (No change)
					state <= I2CMSTOPPD;
				end
				end
			I2CMSTOPPD: begin
				o_scl <= 1'b1;
				o_sda <= 1'b0;
				if ((ck_scl)&&(!ck_sda))
				begin
					o_sda <= 1'b1;
					state <= I2CMFINAL;
				end
				end
			default: begin
				o_scl <= 1'b1;
				o_sda <= 1'b1;
				if (!channel_busy)
					state <= I2CMIDLE;
				else if (watchdog_timeout)
					state <= I2CMSTOP;
				end
		endcase
	end
	// }}}

	assign	o_dbg = { i_cyc, i_cyc, i_stb, 13'h00,
		1'b0, watchdog_timeout, o_ack, o_busy,
		o_err, stop_bit, start_bit, channel_busy,
		state,
		ck_scl, ck_sda, o_scl, o_sda };

endmodule
