////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbuidleint.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Creates an output for the interface, inserting idle words and
//		words indicating an interrupt has taken place into the output
//	stream.  Henceforth, the output means more than just bus transaction
//	results.  It may mean there is no bus transaction result to report,
//	or that an interrupt has taken place.
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
module	wbuidleint(
		// {{{
		input	wire		i_clk, i_reset,
		// From the FIFO following the bus executor
		input	wire		i_stb,
		input	wire	[35:0]	i_codword,
		// From the rest of the board
		input	wire		i_cyc, i_busy, i_int,
		// To the next stage
		output	reg		o_stb,
		output	reg	[35:0]	o_codword,
		output	reg		o_busy,
		// Is the next stage busy?
		input	wire		i_tx_busy
		// }}}
	);

	// Local declarations
	// {{{
	localparam	CW_INTERRUPT = { 6'h4, 30'h0000 }; // interrupt codeword
	localparam	CW_BUSBUSY   = { 6'h1, 30'h0000 }; // bus busy, ow idle
	localparam	CW_IDLE      = { 6'h0, 30'h0000 }; // idle codeword
`ifdef	VERILATOR
	localparam	IDLEBITS = 22;
`else
	localparam	IDLEBITS = 31;
`endif

	reg		int_request, int_sent;
	wire		idle_expired;
	reg		idle_state;
	reg	[IDLEBITS-1:0]	idle_counter;
	// }}}

	// int_request
	// {{{
	initial	int_request = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		int_request <= 0;
	else if (i_int)
		int_request <= 1;
	else if((o_stb)&&(!i_tx_busy)&&(o_codword[35:30]==CW_INTERRUPT[35:30]))
		int_request <= 0;
	// }}}

	// idle_counter
	// {{{
	// Now, for the idle counter
	initial	idle_counter = 0;
	always @(posedge i_clk)
	if (i_reset||i_stb||o_stb||i_busy)
		idle_counter <= 0;
	else if (!idle_counter[IDLEBITS-1])
		idle_counter <= idle_counter + 1;
	// }}}

	// idle_state
	// {{{
	initial	idle_state = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		// We are now idle, and can rest
		idle_state <= 1'b1;
	else if ((o_stb)&&(!i_tx_busy)&&(o_codword[35:30]==CW_IDLE[35:30]))
		// We are now idle, and can rest
		idle_state <= 1'b1;
	else if (!idle_counter[IDLEBITS-1])
		// We became active, and can rest no longer
		idle_state <= 1'b0;
	// }}}

	assign	idle_expired = (!idle_state)&&(idle_counter[IDLEBITS-1]);

	// o_stb, o_codword
	// {{{
	initial	o_stb  = 1'b0;
	always @(posedge i_clk)
	begin
		if(!o_stb || !i_tx_busy)
		begin
			if (i_stb)
			begin
				// On a valid output, just send it out
				// We'll open this strobe, even if the
				// transmitter is busy, just 'cause we might
				// otherwise lose it
				o_stb <= 1'b1;
				o_codword <= i_codword;
			end else begin
				// Our indicators take a clock to reset, hence
				// we'll idle for one clock before sending
				// either an interrupt or an idle indicator.
				// The bus busy indicator is really only ever
				// used to let us know that something's broken.
				o_stb <= (!o_stb)&&((int_request&&!int_sent)
							|| idle_expired);
	
				if (int_request && !int_sent)
					o_codword[35:30] <= CW_INTERRUPT[35:30];
				else begin
					o_codword[35:30] <= CW_IDLE[35:30];
					if (i_cyc)
						o_codword[35:30] <= CW_BUSBUSY[35:30];
				end
			end
		end

		if (i_reset)
			o_stb <= 1'b0;
	end
	// }}}

	always @(*)
		o_busy = o_stb;

	// int_sent
	// {{{
	initial	int_sent = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		int_sent <= 1'b0;
	else if ((int_request)&&((!o_stb)&&(!o_busy)&&(!i_stb)))
		int_sent <= 1'b1;
	else if (!i_int)
		int_sent <= 1'b0;
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
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_stb);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset))
	begin
		if ($past(o_stb && i_tx_busy))
			assert(o_stb && $stable(o_codword));

		if ($past(i_stb && !o_busy))
			assert(o_stb && o_codword == $past(i_codword));
	end
`endif
// }}}
endmodule
