////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbuart.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Unlilke wbuart-insert.v, this is a full blown wishbone core
//		with integrated FIFO support to support the UART transmitter
//	and receiver found within here.  As a result, it's usage may be
//	heavier on the bus than the insert, but it may also be more useful.
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
// `define	USE_LITE_UART
module	wbuart #(
		// {{{
		// 4MB 8N1, when using 100MHz clock
		parameter [30:0] INITIAL_SETUP = 31'd25,
		parameter [3:0]	LGFLEN = 4,
		parameter [0:0]	HARDWARE_FLOW_CONTROL_PRESENT = 1'b1,
		// Perform a simple/quick bounds check on the log FIFO length,
		// to make sure its within the bounds we can support with our
		// current interface.
		localparam [3:0]	LCLLGFLEN = (LGFLEN > 4'ha)? 4'ha
					: ((LGFLEN < 4'h2) ? 4'h2 : LGFLEN)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Wishbone inputs
		input	wire		i_wb_cyc,
		input	wire		i_wb_stb, i_wb_we,
		input	wire	[1:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		//
		input	wire		i_uart_rx,
		output	wire		o_uart_tx,
		input	wire		i_cts_n,
		output	reg		o_rts_n,
		output	wire		o_uart_rx_int, o_uart_tx_int,
					o_uart_rxfifo_int, o_uart_txfifo_int
		// }}}
	);

	localparam [1:0]	UART_SETUP = 2'b00,
				UART_FIFO  = 2'b01,
				UART_RXREG = 2'b10,
				UART_TXREG = 2'b11;

	// Register and signal declarations
	// {{{
	wire	tx_busy;
	reg	[30:0]	uart_setup;
	// Receiver
	wire		rx_stb, rx_break, rx_perr, rx_ferr, ck_uart;
	wire	[7:0]	rx_uart_data;
	reg		rx_uart_reset;
	// Receive FIFO
	wire		rx_empty_n, rx_fifo_err;
	wire	[7:0]	rxf_wb_data;
	wire	[15:0]	rxf_status;
	reg		rxf_wb_read;
	//
	wire	[(LCLLGFLEN-1):0]	check_cutoff;
	reg			r_rx_perr, r_rx_ferr;
	wire	[31:0]		wb_rx_data;
	// The transmitter
	wire		tx_empty_n, txf_err, tx_break;
	wire	[7:0]	tx_data;
	wire	[15:0]	txf_status;
	reg		txf_wb_write, tx_uart_reset;
	reg	[7:0]	txf_wb_data;
	//
	wire	[31:0]	wb_tx_data;
	wire	[31:0]	wb_fifo_data;
	reg	[1:0]	r_wb_addr;
	reg		r_wb_ack;
	// }}}

	// uart_setup
	// {{{
	// The UART setup parameters: bits per byte, stop bits, parity, and
	// baud rate are all captured within this uart_setup register.
	//
	initial	uart_setup = INITIAL_SETUP
		| ((HARDWARE_FLOW_CONTROL_PRESENT==1'b0)? 31'h40000000 : 0);
	always @(posedge i_clk)
	// Under wishbone rules, a write takes place any time i_wb_stb
	// is high.  If that's the case, and if the write was to the
	// setup address, then set us up for the new parameters.
	if ((i_wb_stb)&&(i_wb_addr == UART_SETUP)&&(i_wb_we))
	begin
		if (i_wb_sel[0])
			uart_setup[7:0] <= i_wb_data[7:0];
		if (i_wb_sel[1])
			uart_setup[15:8] <= i_wb_data[15:8];
		if (i_wb_sel[2])
			uart_setup[23:16] <= i_wb_data[23:16];
		if (i_wb_sel[3])
			uart_setup[30:24] <= { (i_wb_data[30])
					||(!HARDWARE_FLOW_CONTROL_PRESENT),
				i_wb_data[29:24] };
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The UART receiver
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The receiver itself
	// {{{
	// Here's our UART receiver.  Basically, it accepts our setup wires, 
	// the UART input, a clock, and a reset line, and produces outputs:
	// a stb (true when new data is ready), and an 8-bit data out value
	// valid when stb is high.
`ifdef	USE_LITE_UART
	// {{{
	rxuartlite	#(.CLOCKS_PER_BAUD(INITIAL_SETUP[23:0]))
		rx(i_clk, i_uart_rx, rx_stb, rx_uart_data);
	assign	rx_break = 1'b0;
	assign	rx_perr  = 1'b0;
	assign	rx_ferr  = 1'b0;
	assign	ck_uart  = 1'b0;
	// }}}
`else
	// {{{
	// The full receiver also produces a break value (true during a break
	// cond.), and parity/framing error flags--also valid when stb is true.
	rxuart	#(.INITIAL_SETUP(INITIAL_SETUP)) rx(i_clk, (i_reset)||(rx_uart_reset),
			uart_setup, i_uart_rx,
			rx_stb, rx_uart_data, rx_break,
			rx_perr, rx_ferr, ck_uart);
	// The real trick is ... now that we have this extra data, what do we do
	// with it?
	// }}}
`endif
	// }}}

	// The receive FIFO
	// {{{
	// We place new arriving data into a receiver FIFO.
	//
	// And here's the FIFO proper.
	//
	// Note that the FIFO will be cleared upon any reset: either if there's
	// a UART break condition on the line, the receiver is in reset, or an
	// external reset is issued.
	//
	// The FIFO accepts strobe and data from the receiver.
	// We issue another wire to it (rxf_wb_read), true when we wish to read
	// from the FIFO, and we get our data in rxf_wb_data.  The FIFO outputs
	// four status-type values: 1) is it non-empty, 2) is the FIFO over half
	// full, 3) a 16-bit status register, containing info regarding how full
	// the FIFO truly is, and 4) an error indicator.
	ufifo	#(
		// {{{
		.LGFLEN(LCLLGFLEN), .RXFIFO(1)
		// }}}
	) rxfifo(
		// {{{
		.i_clk(i_clk), .i_reset((i_reset)||(rx_break)||(rx_uart_reset)),
		.i_wr(rx_stb), .i_data(rx_uart_data),
		.o_empty_n(rx_empty_n),
		.i_rd(rxf_wb_read), .o_data(rxf_wb_data),
		.o_status(rxf_status), .o_err(rx_fifo_err)
		// }}}
	);
	// }}}

	assign	o_uart_rxfifo_int = rxf_status[1];

	// We produce four interrupts.  One of the receive interrupts indicates
	// whether or not the receive FIFO is non-empty.  This should wake up
	// the CPU.
	assign	o_uart_rx_int = rxf_status[0];

	// o_rts_n
	// {{{
	// The clear to send line, which may be ignored, but which we set here
	// to be true any time the FIFO has fewer than N-2 items in it.
	// Why not N-1?  Because at N-1 we are totally full, but already so full
	// that if the transmit end starts sending we won't have a location to
	// receive it.  (Transmit might've started on the next character by the
	// time we set this--thus we need to set it to one, one character before
	// necessary).
	assign	check_cutoff = -3;
	always @(posedge i_clk)
		o_rts_n <= ((HARDWARE_FLOW_CONTROL_PRESENT)
			&&(!uart_setup[30])
			&&(rxf_status[(LCLLGFLEN+1):2] > check_cutoff));
	// }}}

	// rxf_wb_read
	// {{{
	// If the bus requests that we read from the receive FIFO, we need to
	// tell this to the receive FIFO.  Note that because we are using a 
	// clock here, the output from the receive FIFO will necessarily be
	// delayed by an extra clock.
	initial	rxf_wb_read = 1'b0;
	always @(posedge i_clk)
		rxf_wb_read <= (i_wb_stb)&&(i_wb_addr[1:0]== UART_RXREG)
				&&(!i_wb_we);
	// }}}

	// r_rx_perr, r_rx_ferr -- parity and framing errors
	// {{{
	// Now, let's deal with those RX UART errors: both the parity and frame
	// errors.  As you may recall, these are valid only when rx_stb is
	// valid, so we need to hold on to them until the user reads them via
	// a UART read request..
	initial	r_rx_perr = 1'b0;
	initial	r_rx_ferr = 1'b0;
	always @(posedge i_clk)
	if ((rx_uart_reset)||(rx_break))
	begin
		// Clear the error
		r_rx_perr <= 1'b0;
		r_rx_ferr <= 1'b0;
	end else if ((i_wb_stb)
			&&(i_wb_addr[1:0]== UART_RXREG)&&(i_wb_we))
	begin
		// Reset the error lines if a '1' is ever written to
		// them, otherwise leave them alone.
		//
		if (i_wb_sel[1])
		begin
			r_rx_perr <= (r_rx_perr)&&(~i_wb_data[9]);
			r_rx_ferr <= (r_rx_ferr)&&(~i_wb_data[10]);
		end
	end else if (rx_stb)
	begin
		// On an rx_stb, capture any parity or framing error
		// indications.  These aren't kept with the data rcvd,
		// but rather kept external to the FIFO.  As a result,
		// if you get a parity or framing error, you will never
		// know which data byte it was associated with.
		// For now ... that'll work.
		r_rx_perr <= (r_rx_perr)||(rx_perr);
		r_rx_ferr <= (r_rx_ferr)||(rx_ferr);
	end
	// }}}

	// rx_uart_reset
	// {{{
	initial	rx_uart_reset = 1'b1;
	always @(posedge i_clk)
	if ((i_reset)||((i_wb_stb)&&(i_wb_addr[1:0]== UART_SETUP)&&(i_wb_we)))
		// The receiver reset, always set on a master reset
		// request.
		rx_uart_reset <= 1'b1;
	else if ((i_wb_stb)&&(i_wb_addr[1:0]== UART_RXREG)&&(i_wb_we)&&i_wb_sel[1])
		// Writes to the receive register will command a receive
		// reset anytime bit[12] is set.
		rx_uart_reset <= i_wb_data[12];
	else
		rx_uart_reset <= 1'b0;
	// }}}

	// wb_rx_data
	// {{{
	// Finally, we'll construct a 32-bit value from these various wires,
	// to be returned over the bus on any read.  These include the data
	// that would be read from the FIFO, an error indicator set upon
	// reading from an empty FIFO, a break indicator, and the frame and
	// parity error signals.
	assign	wb_rx_data = { 16'h00,
				3'h0, rx_fifo_err,
				rx_break, rx_ferr, r_rx_perr, !rx_empty_n,
				rxf_wb_data};
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The UART transmitter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// txf_wb_write, txf_wb_data
	// {{{
	// Unlike the receiver which goes from RXUART -> UFIFO -> WB, the
	// transmitter basically goes WB -> UFIFO -> TXUART.  Hence, to build
	// support for the transmitter, we start with the command to write data
	// into the FIFO.  In this case, we use the act of writing to the 
	// UART_TXREG address as our indication that we wish to write to the 
	// FIFO.  Here, we create a write command line, and latch the data for
	// the extra clock that it'll take so that the command and data can be
	// both true on the same clock.
	initial	txf_wb_write = 1'b0;
	always @(posedge i_clk)
	begin
		txf_wb_write <= (i_wb_stb)&&(i_wb_addr == UART_TXREG)
					&&(i_wb_we)&&(i_wb_sel[0]);
		txf_wb_data  <= i_wb_data[7:0];
	end
	// }}}

	// Transmit FIFO
	// {{{
	// Most of this is just wire management.  The TX FIFO is identical in
	// implementation to the RX FIFO (theyre both UFIFOs), but the TX
	// FIFO is fed from the WB and read by the transmitter.  Some key
	// differences to note: we reset the transmitter on any request for a
	// break.  We read from the FIFO any time the UART transmitter is idle.
	// and ... we just set the values (above) for controlling writing into
	// this.
	ufifo	#(
		// {{{
		.LGFLEN(LGFLEN), .RXFIFO(0)
		// }}}
	) txfifo(
		// {{{
		.i_clk(i_clk), .i_reset((tx_break)||(tx_uart_reset)),
		.i_wr(txf_wb_write), .i_data(txf_wb_data),
			.o_empty_n(tx_empty_n),
		.i_rd((!tx_busy)&&(tx_empty_n)), .o_data(tx_data),
			.o_status(txf_status), .o_err(txf_err)
		// }}}
	);
	// }}}

	// Transmit interrupts
	// {{{
	// Let's create two transmit based interrupts from the FIFO for the CPU.
	//	The first will be true any time the FIFO has at least one open
	//	position within it.
	assign	o_uart_tx_int = txf_status[0];
	//	The second will be true any time the FIFO is less than half
	//	full, allowing us a change to always keep it (near) fully 
	//	charged.
	assign	o_uart_txfifo_int = txf_status[1];
	// }}}

	// Break logic
`ifndef	USE_LITE_UART
	// {{{
	// A break in a UART controller is any time the UART holds the line
	// low for an extended period of time.  Here, we capture the wb_data[9]
	// wire, on writes, as an indication we wish to break.  As long as you
	// write unsigned characters to the interface, this will never be true
	// unless you wish it to be true.  Be aware, though, writing a valid
	// value to the interface will bring it out of the break condition.
	reg	r_tx_break;
	initial	r_tx_break = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_tx_break <= 1'b0;
	else if ((i_wb_stb)&&(i_wb_addr[1:0]== UART_TXREG)&&(i_wb_we)
		&&(i_wb_sel[1]))
		r_tx_break <= i_wb_data[9];

	assign	tx_break = r_tx_break;
	// }}}
`else
	// {{{
	assign	tx_break = 1'b0;
	// }}}
`endif

	// TX-Reset logic
	// {{{
	// This is nearly identical to the RX reset logic above.  Basically,
	// any time someone writes to bit [12] the transmitter will go through
	// a reset cycle.  Keep bit [12] low, and everything will proceed as
	// normal.
	initial	tx_uart_reset = 1'b1;
	always @(posedge i_clk)
	if((i_reset)||((i_wb_stb)&&(i_wb_addr ==  UART_SETUP)&&(i_wb_we)))
		tx_uart_reset <= 1'b1;
	else if ((i_wb_stb)&&(i_wb_addr[1:0]== UART_TXREG)&&(i_wb_we) && i_wb_sel[1])
		tx_uart_reset <= i_wb_data[12];
	else
		tx_uart_reset <= 1'b0;
	// }}}

	// The actuall transmitter itself
`ifdef	USE_LITE_UART
	// {{{
	txuartlite #(.CLOCKS_PER_BAUD(INITIAL_SETUP[23:0])) tx(i_clk, (tx_empty_n), tx_data,
			o_uart_tx, tx_busy);
	// }}}
`else
	// cts_n
	// {{{
	wire	cts_n;
	assign	cts_n = (HARDWARE_FLOW_CONTROL_PRESENT)&&(i_cts_n);
	// }}}

	// The *full* transmitter impleemntation
	// {{{
	// Finally, the UART transmitter module itself.  Note that we haven't
	// connected the reset wire.  Transmitting is as simple as setting
	// the stb value (here set to tx_empty_n) and the data.  When these
	// are both set on the same clock that tx_busy is low, the transmitter
	// will move on to the next data byte.  Really, the only thing magical
	// here is that tx_empty_n wire--thus, if there's anything in the FIFO,
	// we read it here.  (You might notice above, we register a read any
	// time (tx_empty_n) and (!tx_busy) are both true---the condition for
	// starting to transmit a new byte.)
	txuart	#(.INITIAL_SETUP(INITIAL_SETUP)) tx(i_clk, 1'b0, uart_setup,
			r_tx_break, (tx_empty_n), tx_data,
			cts_n, o_uart_tx, tx_busy);
	// }}}
`endif

	// wb_tx_data
	// {{{
	// Now that we are done with the chain, pick some wires for the user
	// to read on any read of the transmit port.
	//
	// This port is different from reading from the receive port, since
	// there are no side effects.  (Reading from the receive port advances
	// the receive FIFO, here only writing to the transmit port advances the
	// transmit FIFO--hence the read values are free for ... whatever.)
	// We choose here to provide information about the transmit FIFO
	// (txf_err, txf_half_full, txf_full_n), information about the current
	// voltage on the line (o_uart_tx)--and even the voltage on the receive
	// line (ck_uart), as well as our current setting of the break and
	// whether or not we are actively transmitting.
	assign	wb_tx_data = { 16'h00, 
			i_cts_n, txf_status[1:0], txf_err,
			ck_uart, o_uart_tx, tx_break, (tx_busy|txf_status[0]),
			(tx_busy|txf_status[0])?txf_wb_data:8'b00};
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus / register handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// wb_fifo_data
	// {{{
	// Each of the FIFO's returns a 16 bit status value.  This value tells
	// us both how big the FIFO is, as well as how much of the FIFO is in
	// use.  Let's merge those two status words together into a word we
	// can use when reading about the FIFO.
	assign	wb_fifo_data = { txf_status, rxf_status };
	// }}}

	// r_wb_addr
	// {{{
	// You may recall from above that reads take two clocks.  Hence, we
	// need to delay the address decoding for a clock until the data is
	// ready.  We do that here.
	always @(posedge i_clk)
		r_wb_addr <= i_wb_addr;
	// }}}

	// r_wb_ack
	// {{{
	initial	r_wb_ack = 1'b0;
	always @(posedge i_clk) // We'll ACK in two clocks
		r_wb_ack <= (!i_reset)&&(i_wb_stb);
	// }}}

	// o_wb_ack
	// {{{
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk) // Okay, time to set the ACK
		o_wb_ack <= (!i_reset)&&(r_wb_ack)&&(i_wb_cyc);
	// }}}

	// o_wb_data
	// {{{
	// Finally, set the return data.  This data must be valid on the same
	// clock o_wb_ack is high.  On all other clocks, it is irrelelant--since
	// no one cares, no one is reading it, it gets lost in the mux in the
	// interconnect, etc.  For this reason, we can just simplify our logic.
	always @(posedge i_clk)
	casez(r_wb_addr)
	UART_SETUP: o_wb_data <= { 1'b0, uart_setup };
	UART_FIFO:  o_wb_data <= wb_fifo_data;
	UART_RXREG: o_wb_data <= wb_rx_data;
	UART_TXREG: o_wb_data <= wb_tx_data;
	endcase
	// }}}

	// o_wb_stall
	// {{{
	// This device never stalls.  Sure, it takes two clocks, but they are
	// pipelined, and nothing stalls that pipeline.  (Creates FIFO errors,
	// perhaps, but doesn't stall the pipeline.)  Hence, we can just
	// set this value to zero.
	assign	o_wb_stall = 1'b0;
	// }}}
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_data[31] };
	// verilator lint_on UNUSED
	// }}}
endmodule
