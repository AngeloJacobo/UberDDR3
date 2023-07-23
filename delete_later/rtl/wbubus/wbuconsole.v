////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbuconsole.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is the top level file for the entire JTAG-USB to Wishbone
//		bus conversion.  (It's also the place to start debugging, should
//	things not go as planned.)  Bytes come into this routine, bytes go out,
//	and the wishbone bus (external to this routine) is commanded in between.
//
//	You may find some strong similarities between this module and the
//	wbubus module.  They two are essentially the same, with the exception
//	that this version will also multiplex a serial port together with
//	the JTAG-USB->wishbone conversion.  Graphically:
//
//	devbus  -> TCP/IP	\			/ -> WB master
//				MUXED over USB -> UART
//	console -> TCP/IP	/			\ -> wbuconsole
//
//	Doing this, however, also entails stripping the 8th bit from the UART
//	port, so the serial port so contrived can only handle 7-bit data. 
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
module	wbuconsole #(
		// {{{
		parameter	LGWATCHDOG=19,
				LGINPUT_FIFO=6,
				LGOUTPUT_FIFO=10,
		parameter [0:0] CMD_PORT_OFF_UNTIL_ACCESSED = 1'b0,
		parameter	AW = 30
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_reset,
		// RX
		// {{{
		input	wire		i_rx_stb,
		input	wire	[7:0]	i_rx_data,
		// }}}
		// Wishbone master
		// {{{
		output	wire		o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	wire	[31:0]	o_wb_data,
		input	wire		i_wb_stall, i_wb_ack,
		input	wire	[31:0]	i_wb_data,
		input	wire		i_wb_err,
		// }}}
		input	wire		i_interrupt,
		// TX
		// {{{
		output	wire		o_tx_stb,
		output	wire	[7:0]	o_tx_data,
		input	wire		i_tx_busy,
		// }}}
		// CONSOLE
		// {{{
		input	wire		i_console_stb,
		input	wire	[6:0]	i_console_data,
		output	wire		o_console_busy,
		//
		output	reg		o_console_stb,
		output	reg	[6:0]	o_console_data,
		// }}}
		output	wire		o_dbg
		// }}}
	);

	// Local declarations
	// {{{
	wire		soft_reset;
	reg		r_wdt_reset;
	wire		cmd_port_active;

	// RX byte
	wire		rx_valid;
	wire	[7:0]	rx_data;

	// Incoming code word, once processed
	wire		in_stb, in_active;
	wire	[35:0]	in_word;

	reg		ps_full;
	reg	[7:0]	ps_data;
	wire		wbu_tx_stb;
	wire	[7:0]	wbu_tx_data;

	// Input FIFO
	wire		ififo_valid;
	wire	[35:0]	ififo_codword;

	// Code word outputs from running the bus
	wire		exec_stb;
	wire	[35:0]	exec_word;

	// Output FIFO
	wire		ofifo_rd;
	wire	[35:0]	ofifo_codword;
	wire		ofifo_err, ofifo_empty_n;

	wire				w_bus_busy, w_bus_reset;
	reg	[(LGWATCHDOG-1):0]	r_wdt_timer;
	wire				ign_input_busy;
	wire				output_busy, out_active;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Forward console inputs to the console
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	o_console_stb = 1'b0;
	always @(posedge i_clk)
		o_console_stb <= (i_rx_stb)&&(i_rx_data[7] == 1'b0);

	always @(posedge i_clk)
		o_console_data <= i_rx_data[6:0];
	// }}}

	// cmd_port_active
	// {{{
	generate if (CMD_PORT_OFF_UNTIL_ACCESSED)
	begin : GEN_DEACTIVATEPORT

		reg	r_cmd_port_active;

		initial	r_cmd_port_active = 1'b0;
		always @(posedge i_clk)
		if (i_rx_stb && i_rx_data[7])
			r_cmd_port_active <= 1'b1;

		assign	cmd_port_active = r_cmd_port_active;

	end else begin : GEN_ALWAYSON

		assign	cmd_port_active = 1'b1;

	end endgenerate
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Decode ASCII input requests into WB bus cycle requests
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	rx_valid = i_rx_stb && i_rx_data[7];
	assign	rx_data  = { 1'b0, i_rx_data[6:0] };

	wbuinput
	getinput(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(rx_valid), .o_busy(ign_input_busy),
			.i_byte(rx_data),
		.o_soft_reset(soft_reset),
		.o_stb(in_stb), .i_busy(1'b0), .o_codword(in_word),
			.o_active(in_active)
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The input FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (LGINPUT_FIFO < 2)
	begin : NO_INPUT_FIFO

		assign	ififo_valid = in_stb;
		assign	ififo_codword = in_word;
		assign	w_bus_reset = soft_reset;

	end else begin : INPUT_FIFO

		wire		ififo_empty_n, ififo_err, ififo_rd;

		assign	ififo_rd    = (!w_bus_busy)&&(ififo_empty_n);
		assign	ififo_valid = (ififo_empty_n);
		assign	w_bus_reset = r_wdt_reset;

		wbufifo	#(
			// {{{
			.BW(36),.LGFLEN(LGINPUT_FIFO)
			// }}}
		) padififo(
			// {{{
			.i_clk(i_clk), .i_reset(w_bus_reset),
			.i_wr(in_stb), .i_data(in_word),
			.i_rd(ififo_rd), .o_data(ififo_codword),
			.o_empty_n(ififo_empty_n), .o_err(ififo_err)
			// }}}
		);

		// verilator lint_off UNUSED
		wire	gen_unused;
		assign	gen_unused = &{ 1'b0, ififo_err };
		// verilator lint_on  UNUSED
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Run the bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Take requests in, Run the bus, send results out
	// This only works if no requests come in while requests
	// are pending.
	wbuexec #(
		// .LGFIFO(LGOUTPUT_FIFO)
		.AW(AW)
	) runwb(
		// {{{
		.i_clk(i_clk), .i_reset(r_wdt_reset),
		//
		.i_valid(ififo_valid), .i_codword(ififo_codword),
			.o_busy(w_bus_busy),
		//
		.o_wb_cyc(o_wb_cyc), .o_wb_stb(o_wb_stb), .o_wb_we(o_wb_we),
			.o_wb_addr(o_wb_addr), .o_wb_data(o_wb_data),
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
			.i_wb_data(i_wb_data), .i_wb_err(i_wb_err),
		//
		.o_stb(exec_stb), .o_codword(exec_word), .i_fifo_rd(ofifo_rd)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (LGOUTPUT_FIFO < 2)
	begin : NO_OUTBOUND_FIFO

		assign	ofifo_rd = exec_stb;
		assign	ofifo_codword = exec_word;
		assign	ofifo_err = 1'b0;
		assign	ofifo_empty_n = exec_stb;

	end else begin : GEN_OUTBOUND_FIFO

		assign	ofifo_rd = ofifo_empty_n && !output_busy;
		wbufifo #(
			.BW(36), .LGFLEN(LGOUTPUT_FIFO)
		) busoutfifo (
			// {{{
			.i_clk(i_clk), .i_reset(r_wdt_reset),
			.i_wr(exec_stb), .i_data(exec_word),
			.i_rd(ofifo_rd), .o_data(ofifo_codword),
				.o_empty_n(ofifo_empty_n),
				.o_err(ofifo_err)
			// }}}
		);

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Encode bus outputs into a serial data stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbuoutput
	wroutput(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_soft_reset(w_bus_reset),
		.i_stb(ofifo_rd), .i_codword(ofifo_codword),
			.o_busy(output_busy),
		//
		.i_wb_cyc(o_wb_cyc), .i_int(i_interrupt),
			.i_bus_busy(exec_stb || ofifo_empty_n),
		.o_stb(wbu_tx_stb), .o_char(wbu_tx_data), .i_tx_busy(ps_full),
			.o_active(out_active)
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate between the two outputs, console and dbg bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	ps_full = 1'b0;
	always @(posedge i_clk)
	if (!ps_full)
	begin
		if (cmd_port_active && wbu_tx_stb)
		begin
			ps_full <= 1'b1;
			ps_data <= { 1'b1, wbu_tx_data[6:0] };
		end else if (i_console_stb)
		begin
			ps_full <= 1'b1;
			ps_data <= { 1'b0, i_console_data[6:0] };
		end
	end else if (!i_tx_busy)
		ps_full <= 1'b0;

	assign	o_tx_stb = ps_full;
	assign	o_tx_data = ps_data;
	assign	o_console_busy = (wbu_tx_stb && cmd_port_active)||(ps_full);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog timer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Add in a watchdog timer to the bus
	initial	r_wdt_reset = 1'b1;
	initial	r_wdt_timer = 0;
	always @(posedge i_clk)
	if (i_reset || soft_reset)
	begin
		r_wdt_timer <= 0;
		r_wdt_reset <= 1'b1;
	end else if ((!o_wb_cyc)||(i_wb_ack))
	begin
		// We're inactive, or the bus has responded: reset the timer
		// {{{
		r_wdt_timer <= 0;
		r_wdt_reset <= 1'b0;
		// }}}
	end else if (&r_wdt_timer)
	begin	// TIMEOUT!!!
		// {{{
		r_wdt_reset <= 1'b1;
		r_wdt_timer <= 0;
		// }}}
	end else begin // Tick-tock ...
		r_wdt_timer <= r_wdt_timer+{{(LGWATCHDOG-1){1'b0}},1'b1};
		r_wdt_reset <= 1'b0;
	end
	// }}}

	assign	o_dbg = w_bus_reset;

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ofifo_err, ign_input_busy, wbu_tx_data[7],
				out_active, in_active };
	// verilator lint_on  UNUSED
	// }}}
endmodule

