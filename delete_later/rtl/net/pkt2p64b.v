////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/pkt2p64b.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Converts from our AXI network protocol to the 64bit payload
//		required by the PCS layer in the IEEE standard, while bypassing
//	the XGMII layer in the process.
//
//	Why bypass the 32-bit XGMII?  1) Because the Xilinx PHY operates at
//	64-bits at a time, not 32.  2) Because the 64b/66b encoder requires
//	64 bits at a time.  Other projects still call this an XGMII interface.
//	This interface is close, though not quite there, since the IEEE
//	requires XSGMII to be 32-bits per cycle.
//
//	By convention, ethernet sends the two sync bits first, followed by
//	bit 0 of byte 0 first.  This IP, therefore, assumes a little endian
//	byte order, with S_DATA[7:0] being the *first* byte in any packet.
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
// }}}
module	pkt2p64b (
		// {{{
		input	wire		TX_CLK, S_ARESETN,
		//
		input	wire		i_remote_fault, i_local_fault,
		//
		input	wire		S_VALID,
		output	wire		S_READY,
		input	wire	[63:0]	S_DATA,
		input	wire	[2:0]	S_BYTES,
		input	wire		S_LAST,
		input	wire		S_ABORT,
		//
		// output wire		TXVALID=1 is assumed
		// Ideally, we wouldn't need TXREADY, *but* the FPGA operates
		// at a faster clock rate (at one clock per 64 outputs, not
		// 1 clock per 66 inputs), so we need it here.
		input	wire		TXREADY,
		output	reg	[65:0]	TXDATA
		// }}}
	);

	// Local declarations
	// {{{
	localparam [1:0]	TX_IDLE     = 2'h0,
				TX_DATA     = 2'h1,
				TX_LAST     = 2'h2,
				TX_PAUSE    = 2'h3;
	localparam [1:0]	SYNC_CONTROL = 2'b10,
				SYNC_DATA    = 2'b01;

	// FIXME!  "The 10GBASE-R PCS encodes the start and terminate control
	// characters implicitly by the block type field. ... The 10GBASE-R PCS
	// encodes each of the other control characters into a 7-bit C code.
	//
	localparam	[65:0]	P_IDLE  = { {(8){7'h07}}, 8'h1e, SYNC_CONTROL },
			// Indicate a remote fault
			P_FAULT = { 24'h02, 8'h0, 24'h02, 8'h55, SYNC_CONTROL },
			// Start a packet--always on a 64b boundary
			P_START = { 8'hab, {(6){8'haa}}, 8'h78, SYNC_CONTROL },
			P_LAST  = { {(8){7'h07}}, 8'h87, SYNC_CONTROL };
	// "They [idles] shall not be added while data is being received.  When
	// deleting /I/s, the first four characters after a /T/ shall not be
	// deleted.

	reg		r_ready, flushing;
	reg	[1:0]	state;
	// }}}

	initial	r_ready = 1'b0;
	initial	TXDATA  = P_IDLE;
	always @(posedge TX_CLK)
	if (!S_ARESETN)
	begin
		// {{{
		r_ready <= 1'b0;
		state   <= TX_IDLE;
		TXDATA  <= P_IDLE;
		flushing <= 1'b0;
		// }}}
	end else if (i_remote_fault || i_local_fault || flushing)
	begin
		// {{{
		if (TXREADY)
		begin
			if (i_remote_fault || !i_local_fault)
				TXDATA <= P_IDLE;
			else // if !i_remote_fault && i_local_fault
				TXDATA <= P_FAULT;
		end

		if (state == TX_DATA)
			flushing <= 1'b1;

		state  <= TX_PAUSE;

		if (S_VALID && S_READY && S_LAST)
		begin
			r_ready <= 1'b0;
			state   <= TX_PAUSE;
			flushing<= 1'b0;
		end else // Flush any ongoing packet
			r_ready <= flushing || (state == TX_DATA);
		// }}}
	end else case(state)
	TX_IDLE: begin
		// {{{
		r_ready <= 1'b0;
		TXDATA <= P_IDLE;
		if (S_VALID)
		begin
			if (!S_ABORT && TXREADY)
			begin
				state  <= TX_DATA;
				TXDATA <= P_START;
				r_ready <= 1'b1;
			end else begin
				// Accept the ABORT flag and continue
				r_ready <= 1'b1;
			end
		end end
		// }}}
	TX_DATA: begin
		// {{{
		r_ready <= 1'b1;
		if (TXREADY)
		begin
			TXDATA  <= { S_DATA, SYNC_DATA };
			if (S_ABORT || !S_VALID)
			begin
				// ERROR!!  Send error code, then terminate
				state   <= TX_PAUSE;
				TXDATA  <= P_FAULT;
				r_ready <= 1'b0;
			end else if (S_LAST)
			begin
				r_ready <= 1'b0;
				state <= TX_PAUSE;
				case(S_BYTES)
				3'h0: state <= TX_LAST;
				3'h1: TXDATA <= { 48'h0000_0000_0000,
					S_DATA[7:0], 8'h99, SYNC_CONTROL };
				3'h2: TXDATA <= { 40'h0000_0000_00,
					S_DATA[15:0], 8'haa, SYNC_CONTROL };
				3'h3: TXDATA <= { 32'h0000_0000, S_DATA[23:0],
							8'hb4, SYNC_CONTROL };
				3'h4: TXDATA <= { 24'h0000_00,
					S_DATA[31:0], 8'hcc, SYNC_CONTROL };
				3'h5: TXDATA <= { 16'h0000,
					S_DATA[39:0], 8'hd2, SYNC_CONTROL };
				3'h6: TXDATA <= { 8'h00,
					S_DATA[47:0], 8'he1, SYNC_CONTROL };
				3'h7: TXDATA <= {
					S_DATA[55:0], 8'hff, SYNC_CONTROL};
				// No default needed
				endcase
			end
		end end
		// }}}
	TX_LAST: begin
		// {{{
		r_ready <= 1'b0;
		if (TXREADY)
		begin
			TXDATA  <= P_LAST;
			state   <= TX_PAUSE;
		end end
		// }}}
	TX_PAUSE: begin // Ensure interframe gaps
		// {{{
		r_ready <= 1'b0;
		if (TXREADY)
		begin
			TXDATA <= P_IDLE;
			state <= TX_IDLE;
		end end
		// }}}
	// default: begin end
	endcase

	assign	S_READY = r_ready && (TXREADY || flushing);
endmodule
