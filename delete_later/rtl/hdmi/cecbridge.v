////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/hdmi/crcbridge.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Connect the CEC lines together between master(driver) and slave.
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
`default_nettype none
// }}}
module	cecbridge(
		// {{{
		input	wire	i_clk,
		input	wire	i_txcec,
		output	reg	o_txcec,
		input	wire	i_rxcec,
		output	reg	o_rxcec
		// }}}
	);

	// Local declarations
	// {{{
	reg		owned;
	reg [1:0]	pipe_txcec, pipe_rxcec;
	reg		ck_txcec, ck_rxcec;
	reg	[12:0]	timer;		// Should be about 0.2ms/10
	reg		timeout;
	reg		watchdog_err;
	reg	[19:0]	watchdog_timer;	// Should be about 5ms or more
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize inputs
	// {{{
	always @(posedge i_clk)
		{ ck_txcec, pipe_txcec } <= {  pipe_txcec, i_txcec };

	always @(posedge i_clk)
		{ ck_rxcec, pipe_rxcec } <= { pipe_rxcec, i_rxcec };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// State machine: the dev that pulls the CEC line low, owns the bus
	// {{{

	initial	{ owned, o_txcec, o_rxcec } = 3'h3;
	always @(posedge i_clk)
	if (watchdog_err)
		{ owned, o_txcec, o_rxcec } <= 3'h3;
	else case({ ck_txcec, ck_rxcec })
	2'b11:begin owned <= 1'b0; o_txcec <= 1; o_rxcec <= 1; end
	2'b10: if (timeout)
		// {{{
		begin
			if (!owned)
			begin
				owned <= 1'b1;
				o_txcec <= 0; o_rxcec <= 1;
			end else if (o_rxcec)
			begin // RX OWNS, TX is Z
			end else begin // TX OWNS, RX is Z -- do nothing
				owned <= 0;
				o_txcec <= 1;
				o_rxcec <= 1;
			end
		end
		// }}}
	2'b01: if (timeout)
		// {{{
		begin
			if (!owned)
			begin
				owned <= 1'b1;
				o_txcec <= 1;
				o_rxcec <= 0;
			end else if (o_rxcec)
			begin // RX OWNS, RX is Z
				owned <= 0;
				o_txcec <= 1;
				o_rxcec <= 1;
			end else begin // TX OWNS, RX is Z -- do nothing
			end
		end
		// }}}
	2'b00: begin end
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Timeout, to prevent pulling low already pulled data
	// {{{

	// After we stop pulling something low, we need to allow time for it
	// to rise, before we decide that the value we just pulled low is
	// now pulling us low, instead of rising and not-yet risen

	initial	{ timeout, timer } = 1;
	always @(posedge i_clk)
	if (!timeout)
	begin
		{ timeout, timer } <= timer + 1;
	end else case({ ck_txcec, ck_rxcec })
	2'b11:	begin end
	2'b10:	{ timeout, timer } <= 1;
	2'b01:	{ timeout, timer } <= 1;
	2'b00:	{ timeout, timer } <= 1;
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog timeout -- in case something goes wrong, let the bus clear
	// {{{

	initial	{ watchdog_err, watchdog_timer } = 1;
	always @(posedge i_clk)
	if (ck_txcec && ck_rxcec)
		// If both CECs are set, the bus is clear, and we can restart
		// the watchdog.
		{ watchdog_err, watchdog_timer } <= 1;
	else if (!watchdog_err)
		{ watchdog_err, watchdog_timer } <= watchdog_timer + 1;
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
	always @(*)
		assert(o_rxcec || o_txcec);
	always @(*)
		assert(owned == (o_rxcec != o_txcec));
	always @(*)
		assert(timeout == (timer == 0));
`endif
// }}}
endmodule
