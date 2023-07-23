////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbconsole.v
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
module	wbconsole #(
		parameter [3:0]	LGFLEN = 4
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Wishbone inputs
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[1:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		// }}}
		// TX
		// {{{
		output	wire		o_uart_stb,
		output	wire	[6:0]	o_uart_data,
		input	wire		i_uart_busy,
		// }}}
		// RX
		// {{{
		input	wire		i_uart_stb,
		input	wire	[6:0]	i_uart_data,
		// }}}
		// Interrupts
		output	wire		o_uart_rx_int, o_uart_tx_int,
					o_uart_rxfifo_int, o_uart_txfifo_int,
		//
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	// parameter [0:0]	HARDWARE_FLOW_CONTROL_PRESENT = 1'b1;
	// Perform a simple/quick bounds check on the log FIFO length, to make
	// sure its within the bounds we can support with our current
	// interface.
	localparam [3:0]	LCLLGFLEN = (LGFLEN > 4'ha)? 4'ha
					: ((LGFLEN < 4'h2) ? 4'h2 : LGFLEN);
	//
	//
	localparam	[1:0]	UART_SETUP = 2'b00,
				UART_FIFO  = 2'b01,
				UART_RXREG = 2'b10,
				UART_TXREG = 2'b11;

	reg		rx_uart_reset;
	wire		rx_empty_n, rx_fifo_err;
	wire	[6:0]	rxf_wb_data;
	wire	[15:0]	rxf_status;
	reg		rxf_wb_read;

	wire	[31:0]	wb_rx_data;

	wire		tx_empty_n, txf_err;
	wire	[15:0]	txf_status;
	reg		txf_wb_write, tx_uart_reset;
	reg	[6:0]	txf_wb_data;

	wire	[31:0]	wb_tx_data;
	wire	[31:0]	wb_fifo_data;
	reg	[1:0]	r_wb_addr;
	reg		r_wb_ack;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// First, the receiver
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We place it into a receiver FIFO.

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
		.LGFLEN(LCLLGFLEN), .BW(7), .RXFIFO(1)
	) rxfifo(
		// {{{
		i_clk, (i_reset)||(rx_uart_reset),
			i_uart_stb, i_uart_data,
			rx_empty_n,
			rxf_wb_read, rxf_wb_data,
			rxf_status, rx_fifo_err
		// }}}
	);

	assign	o_uart_rxfifo_int = rxf_status[1];

	// We produce four interrupts.  One of the receive interrupts indicates
	// whether or not the receive FIFO is non-empty.  This should wake up
	// the CPU.
	assign	o_uart_rx_int = rxf_status[0];

	// If the bus requests that we read from the receive FIFO, we need to
	// tell this to the receive FIFO.  Note that because we are using a
	// clock here, the output from the receive FIFO will necessarily be
	// delayed by an extra clock.
	initial	rxf_wb_read = 1'b0;
	always @(posedge i_clk)
		rxf_wb_read <= (i_wb_stb)&&(i_wb_addr[1:0]==UART_RXREG)
				&& !i_wb_we && i_wb_sel[0];

	initial	rx_uart_reset = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		rx_uart_reset <= 1'b1;
	else begin
		rx_uart_reset <= 1'b0;

		if (i_wb_stb && i_wb_we)
		begin
			if (i_wb_addr[1:0]==UART_SETUP && i_wb_sel[0])
				// The receiver reset, always set on a master
				// reset request.
				rx_uart_reset <= 1'b1;

			if (i_wb_addr[1:0]==UART_RXREG && i_wb_sel[1]
					&& i_wb_data[12])
				// Writes to the receive register will command
				// a receive reset anytime bit[12] is set.
				rx_uart_reset <= 1'b1;
		end
	end

	// Finally, we'll construct a 32-bit value from these various wires,
	// to be returned over the bus on any read.  These include the data
	// that would be read from the FIFO, an error indicator set upon
	// reading from an empty FIFO, a break indicator, and the frame and
	// parity error signals.
	assign	wb_rx_data = { 16'h00,
				3'h0, rx_fifo_err,
				1'b0, 1'b0, 1'b0, !rx_empty_n,
				1'b0, rxf_wb_data};
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Then the UART transmitter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
					&& i_wb_we && i_wb_sel[0];
		txf_wb_data  <= i_wb_data[6:0];
	end

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
		.LGFLEN(LGFLEN), .BW(7), .RXFIFO(0)
	) txfifo(
		// {{{
		i_clk, (tx_uart_reset),
			txf_wb_write, txf_wb_data,
			tx_empty_n,
			(!i_uart_busy)&&(tx_empty_n), o_uart_data,
			txf_status, txf_err
		// }}}
	);
	// }}}

	assign	o_uart_stb = tx_empty_n;

	// Let's create two transmit based interrupts from the FIFO for the CPU.
	//	The first will be true any time the FIFO has at least one open
	//	position within it.
	assign	o_uart_tx_int = txf_status[0];
	//	The second will be true any time the FIFO is less than half
	//	full, allowing us a change to always keep it (near) fully
	//	charged.
	assign	o_uart_txfifo_int = txf_status[1];

	// TX-Reset logic
	// {{{
	// This is nearly identical to the RX reset logic above.  Basically,
	// any time someone writes to bit [12] the transmitter will go through
	// a reset cycle.  Keep bit [12] low, and everything will proceed as
	// normal.
	initial	tx_uart_reset = 1'b1;
	always @(posedge i_clk)
	if((i_reset)||((i_wb_stb)&&(i_wb_addr == UART_SETUP && i_wb_sel[0])&&(i_wb_we)))
		tx_uart_reset <= 1'b1;
	else if ((i_wb_stb)&&(i_wb_addr[1:0]==UART_TXREG)&&(i_wb_we))
		tx_uart_reset <= i_wb_data[12] && i_wb_sel[1];
	else
		tx_uart_reset <= 1'b0;
	// }}}

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
				1'b0, txf_status[1:0], txf_err,
				1'b0, o_uart_stb, 1'b0,
				(i_uart_busy|tx_empty_n),
				1'b0,(i_uart_busy|tx_empty_n)?txf_wb_data:7'h0};
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus return handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Each of the FIFO's returns a 16 bit status value.  This value tells
	// us both how big the FIFO is, as well as how much of the FIFO is in
	// use.  Let's merge those two status words together into a word we
	// can use when reading about the FIFO.
	assign	wb_fifo_data = { txf_status, rxf_status };

	// You may recall from above that reads take two clocks.  Hence, we
	// need to delay the address decoding for a clock until the data is
	// ready.  We do that here.
	always @(posedge i_clk)
		r_wb_addr <= i_wb_addr;

	// o_wb_ack
	// {{{
	// Likewise, the acknowledgement is delayed by one clock.
	always @(posedge i_clk) // We'll ACK in two clocks
	if (i_reset || !i_wb_cyc)
		r_wb_ack <= 1'b0;
	else
		r_wb_ack <= i_wb_stb;

	always @(posedge i_clk) // Okay, time to set the ACK
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= r_wb_ack;
	// }}}

	// o_wb_data
	// {{{
	// Finally, set the return data.  This data must be valid on the same
	// clock o_wb_ack is high.  On all other clocks, it is irrelelant--since
	// no one cares, no one is reading it, it gets lost in the mux in the
	// interconnect, etc.  For this reason, we can just simplify our logic.
	always @(posedge i_clk)
	casez(r_wb_addr)
	UART_SETUP: o_wb_data <= 32'h0;
	UART_FIFO:  o_wb_data <= wb_fifo_data;
	UART_RXREG: o_wb_data <= wb_rx_data;
	UART_TXREG: o_wb_data <= wb_tx_data;
	endcase
	// }}}

	// This device never stalls.  Sure, it takes two clocks, but they are
	// pipelined, and nothing stalls that pipeline.  (Creates FIFO errors,
	// perhaps, but doesn't stall the pipeline.)  Hence, we can just
	// set this value to zero.
	assign	o_wb_stall = 1'b0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// A debug return
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	begin
		o_debug[31:16] <= { txf_status[11:0], rxf_status[3:0] };

		//
		// Transmit byte
		o_debug[15] <= tx_empty_n;
		if ((i_wb_stb)&&(i_wb_addr[1:0]==UART_TXREG)&&(i_wb_we && i_wb_sel[0]))
			o_debug[14:8] <= i_wb_data[6:0];
		else if (o_uart_stb)
			o_debug[14:8] <= o_uart_data;
		else
			o_debug[14:8] <= 0;
		//
		// Received
		o_debug[7] <= i_uart_stb;
		if (i_uart_stb)
			o_debug[6:0] <= i_uart_data;
		else
			o_debug[6:0] <= rxf_wb_data;
	end
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data[31:13], i_wb_data[11:7],
			i_wb_sel };
	// verilator lint_on  UNUSED
	// }}}
endmodule
