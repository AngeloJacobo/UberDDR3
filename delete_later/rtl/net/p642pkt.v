////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/net/p642pkt.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Convert from the format at the output of the PHY (66 bits
//		per clock) to an outgoing AXI network packet protocol.
//
//	Note that because Xilinx GTX will be generating 66-bits at a time,
//	we're skipping the 32-bit XGMII interface and going directly from a
//	66-bit interface to a 64-bit AXI network interface.
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
module	p642pkt (
		// {{{
		input	wire		RX_CLK, S_ARESETN,
		//
		input	wire		i_phy_fault,
		output	reg		o_remote_fault,
		output	wire		o_local_fault,
		output	wire		o_link_up,
		//
		input	wire		RX_VALID,
		input	wire	[65:0]	RX_DATA,
		//
		output	reg		M_VALID,
		input	wire		M_READY,
		output	reg	[63:0]	M_DATA,
		output	reg	[2:0]	M_BYTES,
		output	reg		M_ABORT,
		output	reg		M_LAST
		// }}}
	);

	// Local declarations
	// {{{
	localparam 	[1:0]	SYNC_CONTROL = 2'b10,
				SYNC_DATA = 2'b01;
	localparam		PRE_IDLE = 1'b0,
				PRE_DATA = 1'b1;

	localparam	[65:0]	R_PREAMBLE = { 32'habaa_aaaa, 32'haaaa_aa1e,
							SYNC_CONTROL },
			R_HALF_PREAMBLE = { 24'haaaa_aa,4'h0,28'h0000_00, 8'h33,
							SYNC_CONTROL },
			R_HALF_MASK = { 24'hff_ffff, 4'h0, 28'h000_0000, 8'hff,
							SYNC_CONTROL };
			// R_IDLE = { 32'h00000000, 32'h0000001e,
			//				SYNC_CONTROL },
			// R_LPIDLE = { 32'h06060606, 32'h0606061e,
			//				SYNC_CONTROL };
	localparam	[23:0]	REMOTE_FAULT = 24'h02;
	localparam		LNKMSB = 26;

	reg		pstate, phalf, poffset;

	reg		dly_valid, dly_last;
	reg	[63:0]	dly_data;
	reg	[31:0]	dly_half;
	reg	[3:0]	dly_bytes;

	// Fault detection registers
	reg		r_local_fault;
	reg	[6:0]	watchdog_counter;
	reg		watchdog_timeout;
	reg	[LNKMSB:0]	link_up_counter;

	reg			max_packet_fault;
	reg	[18:0]		max_packet_counter;

	reg			powering_up;
	// }}}

	// Processing steps:
	// (0) Unscramble the payload
	// 1. Unpack control and data characters
	// 2. Check control characters for validity
	// 3. Classify packets
	// 4. Generate START/STOP characters
	// 5. Pack data words
	// 6. Generate LAST and flush the packing circuit

	// pstate
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN || i_phy_fault)
		pstate <= PRE_IDLE;
	else if (RX_VALID)
	case(pstate)
	PRE_IDLE: begin
		// {{{
		pstate <= PRE_IDLE;
		if (RX_DATA == R_PREAMBLE
				|| ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE))
			pstate <= PRE_DATA;
		if (M_VALID && !M_READY)
			// Output is still hung with the previous packet.
			// Drop this one and wait for the next preamble.
			pstate <= PRE_IDLE;
		end
		// }}}
	PRE_DATA: begin
		if (RX_DATA[1:0] == SYNC_DATA)
			pstate <= PRE_DATA;
		// else if (RX_DATA == R_IDLE)
		//	pstate <= PRE_DATA;
		else
			pstate <= PRE_IDLE;
		end
	endcase
	// }}}

	// phalf, poffset
	// {{{
	// phalf   == discard the first half of the next word.
	// poffset == we are off-set from true.  Each new data word will bring
	//	four bytes to output, and four bytes to reserve for the next
	//	cycle.
	always @(posedge RX_CLK)
	if (!S_ARESETN || i_phy_fault)
		{ phalf, poffset } <= 2'b00;
	else if (RX_VALID)
	case(pstate)
	PRE_IDLE: begin
		// {{{
		if (RX_DATA == R_PREAMBLE)
			{ phalf, poffset } <= 2'b00;
		else if ((RX_DATA & R_HALF_MASK) == R_HALF_PREAMBLE)
			{ phalf, poffset } <= 2'b11;
		end
		// }}}
	PRE_DATA: phalf <= 1'b0;
	endcase
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// dly_*: The delay stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We need this stage because XGMII sends an "end-of-packet" indicator
	// one byte after the last character, whereas our AXI-network protocol
	// is supposed to guarantee M_LAST on the last beat of the packet.
	// Hence, if the "end-of-packet" character shows up on byte-0, then
	// we'd set M_LAST one beat too late if we didn't have this delay stage.

	// One problem: there's no guarantee of receiving 8-bytes per clock.
	// The following assuming we either have 8-bytes per clock or its the
	// last beat in the packet.  The protocol doesn't require this.  Rather,
	// the protocol only requires 4-bytes per beat, allowing for the other
	// 4-bytes to be stuff bytes (i.e. idles, either low-power or otherwise)
	// in order to deal with clock mismatch issues.

	// Not quite.  It's illegal to send IDLEs during a packet.  If the
	// transmitted can't keep up with the packet, the packet will be
	// ABORTed.  (Otherwise, we might be confuse an all IDLE control stream
	// with a response to an remote_fault packet.)

	// During an packet, we should be able to expect code words:
	// ALL DATA
	// 8'h87
	// 8'h99
	// 8'haa
	// 8'hb4
	// 8'hcc
	// 8'hd2
	// 8'he1
	// 8'hff
	// All but the all-data control word indicate the end of the packet.
	// Any other control words will need to result in an aborted packet

	// dly_valid
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		dly_valid <= 0;
	else if (RX_VALID)
	begin
		if (RX_DATA[1:0] == SYNC_DATA)
			dly_valid <= 1'b1;
		else if (RX_DATA[1:0] != SYNC_CONTROL)
			dly_valid <= 1'b0;
		else if (RX_DATA[9:2] == 8'h87)
			// Unless this is a completely control frame, we're
			// valid
			dly_valid <= 1'b1;
		else
			dly_valid <= poffset;

		if (pstate != PRE_DATA || phalf)
			dly_valid <= 1'b0;
	end else
		dly_valid <= 1'b0;
	// }}}

	// dly_half
	// {{{
	// Since it's posible for a packet to start on a half-64-bit boundary,
	// we need a bit of a gearbox to realign the packet back onto a 64bit
	// boundary.  dly_half is where we stuff that extra data.
	always @(posedge RX_CLK)
	if (!S_ARESETN || !poffset)
		dly_half <= 0;
	else if (RX_VALID)
	begin
		dly_half <= RX_DATA[65:34];	// D4, D5, D6, D7

		// If the word is a control word, then we're offset, based upon
		// the 8'bits necessary to specify the type of control word.
		// That puts our first bit at (2+32+8 = 42), not 34.  So, let's
		// adjust that here.
		if (RX_DATA[1:0] == SYNC_CONTROL)
		case(RX_DATA[9:2])
		// 8'h99:
		// 8'haa:
		// 8'hb4:
		// 8'hcc:
		8'hd2: dly_half <= { 24'h0, RX_DATA[49:42] };
		8'he1: dly_half <= { 16'h0, RX_DATA[57:42] };
		8'hff: dly_half <= {  8'h0, RX_DATA[65:42] };
		default: dly_half <= 32'h0;
		endcase
	end
	// }}}

	// dly_data
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		dly_data <= 0;
	else if (RX_VALID)
	begin
		if (poffset)
		begin // Gearbox.  Use 32-bits from before, and up to 32-bits
			// {{{
			// from the current word
			dly_data <= { RX_DATA[33:2], dly_half };
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			8'h99: dly_data[63:32] <= { 24'h0, RX_DATA[17:10] };
			8'haa: dly_data[63:32] <= { 16'h0, RX_DATA[25:10] };
			8'hb4: dly_data[63:32] <= {  8'h0, RX_DATA[33:10] };
			8'hcc: dly_data[63:32] <= {        RX_DATA[41:10] };
			// The rest of these have more than 32bits defined,
			// but we only need 32 of the incoming bits.  The other
			// 32bits will be in dly_half for the next clock cycle.
			8'hd2: dly_data[63:32] <= {        RX_DATA[41:10] };
			8'he1: dly_data[63:32] <= {        RX_DATA[41:10] };
			8'hff: dly_data[63:32] <= {        RX_DATA[41:10] };
			default: dly_data[63:32] <= 32'h0;
			endcase
			// }}}
		end else begin // No gearbox, direct map 64bits to output
			// {{{
			dly_data <= RX_DATA[65:2];
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			8'h99: dly_data <= { 56'h0, RX_DATA[17:10] };
			8'haa: dly_data <= { 48'h0, RX_DATA[25:10] };
			8'hb4: dly_data <= { 40'h0, RX_DATA[33:10] };
			8'hcc: dly_data <= { 32'h0, RX_DATA[41:10] };
			8'hd2: dly_data <= { 24'h0, RX_DATA[49:10] };
			8'he1: dly_data <= { 16'h0, RX_DATA[57:10] };
			8'hff: dly_data <= {  8'h0, RX_DATA[65:10] };
			default: begin end
			endcase

			if (pstate != PRE_DATA)
				dly_data <= 0;
			// }}}
		end
	end
	// }}}

	// dly_bytes
	// {{{
	// Number of valid bytes in the delay cell.
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		dly_bytes <= 0;
	else if (RX_VALID)
	begin
		if (phalf)
			dly_bytes <= 4;	// These bytes are in dly_half
		else if (poffset)
		begin
			// {{{
			dly_bytes <= 12;	// dly_half + dly_data
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			8'h99: dly_bytes <= 4'd4 + 4'd1;
			8'haa: dly_bytes <= 4'd4 + 4'd2;
			8'hb4: dly_bytes <= 4'd4 + 4'd3;
			8'hcc: dly_bytes <= 4'd4 + 4'd4;
			8'hd2: dly_bytes <= 4'd4 + 4'd5;
			8'he1: dly_bytes <= 4'd4 + 4'd6;
			8'hff: dly_bytes <= 4'd4 + 4'd7;
			default: begin end
			endcase

			if (pstate != PRE_DATA)
				dly_bytes<=(dly_bytes <= 8) ? 0 : (dly_bytes-8);
			// }}}
		end else begin
			dly_bytes <= 4'd8;	// 64 incoming bits => 8bytes
			if (RX_DATA[1:0] == SYNC_CONTROL)
			case(RX_DATA[9:2])
			8'h99: dly_bytes <= 4'd1;
			8'haa: dly_bytes <= 4'd2;
			8'hb4: dly_bytes <= 4'd3;
			8'hcc: dly_bytes <= 4'd4;
			8'hd2: dly_bytes <= 4'd5;
			8'he1: dly_bytes <= 4'd6;
			8'hff: dly_bytes <= 4'd7;
			default: begin end
			endcase
		end
	end else if (dly_valid && dly_last)
		dly_bytes <= 0;
	// }}}

	// dly_last
	// {{{
	always @(posedge RX_CLK)
	if (!S_ARESETN)
		dly_last <= 0;
	else if (RX_VALID)
	begin
		dly_last <= 1'b0;
		if (pstate != PRE_DATA)
			dly_last <= poffset;
		else if (RX_DATA[1:0] == SYNC_CONTROL && !poffset)
			dly_last <= 1'b1;
	end else
		dly_last <= 1'b0;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Fault detection
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// Local & Remote fault detection
	// {{{
	// These faults are all determined by the data sent.  If no data
	// gets sent, or if we never lock (and hence RX_VALID stays low),
	// then we'll never know a fault
	initial	o_remote_fault = 1'b0;
	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		o_remote_fault <= 1'b0;
		r_local_fault  <= 1'b0;
	end else if (RX_VALID)
	begin
		case(RX_DATA[9:2])
		8'h2d: o_remote_fault <= (RX_DATA[65:42] == REMOTE_FAULT);
		// 8'h66: // The fault must've been cleared by data start,
		//   or data wouldn't be starting
		8'h55: o_remote_fault <= (RX_DATA[65:42] == REMOTE_FAULT);
		8'h4b: o_remote_fault <= (RX_DATA[33:10] == REMOTE_FAULT);
		default: o_remote_fault <= 1'b0;
		endcase

		if (RX_DATA[1:0] != SYNC_CONTROL)
			o_remote_fault <= 1'b0;

		case(RX_DATA[9:2])
		8'h1e: r_local_fault <= 1'b0;
		8'h2d: r_local_fault <= (RX_DATA[65:42] != REMOTE_FAULT);
		8'h33: r_local_fault <= 1'b0;
		8'h66: r_local_fault <= (RX_DATA[33:10] != REMOTE_FAULT);
		8'h55: r_local_fault <= (RX_DATA[65:42] != REMOTE_FAULT);
		8'h78: r_local_fault <= 1'b0;
		8'h4b: r_local_fault <= (RX_DATA[33:10] != REMOTE_FAULT);
		8'h87: r_local_fault <= 1'b0;
		8'h99: r_local_fault <= 1'b0;
		8'haa: r_local_fault <= 1'b0;
		8'hb4: r_local_fault <= 1'b0;
		8'hcc: r_local_fault <= 1'b0;
		8'hd2: r_local_fault <= 1'b0;
		8'he1: r_local_fault <= 1'b0;
		8'hff: r_local_fault <= 1'b0;
		default: r_local_fault <= 1'b1;
		endcase

		if (RX_DATA[1:0] != SYNC_CONTROL)
			r_local_fault <= 1'b0;
	end
	// }}}

	// watchdog_timeout
	// {{{
	// If the PHY never produces any data for us, then we have a watchdog
	// error condition.
	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		watchdog_counter <= -1;
		watchdog_timeout <=  0;
	end else if (RX_VALID)
	begin
		watchdog_counter <= -1;
		watchdog_timeout <=  0;
	end else begin
		if (watchdog_counter > 0)
			watchdog_counter <= watchdog_counter - 1;
		watchdog_timeout <= (watchdog_counter <= 1);
	end
	// }}}

	// max_packet_fault
	// {{{
	// It is a fault to have a continuous packet with no control characters.
	// In this case, our maximum packet length is still excessively large,
	// set (above) at 2^19 words, or 2^22 (4MB) bytes.
	always @(posedge RX_CLK)
	if (!S_ARESETN)
	begin
		max_packet_counter <= 0;
		max_packet_fault <=  0;
	end else if (RX_VALID)
	begin
		if (RX_DATA[1:0] == SYNC_CONTROL)
		begin
			max_packet_counter <= -1;
			max_packet_fault <=  0;
		end else if (max_packet_counter != 0)
		begin
			max_packet_counter <= max_packet_counter - 1;
			max_packet_fault <= (max_packet_counter <= 1);
		end
	end
	// }}}

	// link_up_counter--used to stretch faults and errors so the eye can
	// see them
	// {{{
	always @(posedge RX_CLK or negedge S_ARESETN)
	if (!S_ARESETN)
		link_up_counter <= 0;
	else if (watchdog_timeout || o_remote_fault || o_local_fault
			|| max_packet_fault || powering_up)
		link_up_counter <= 0;
	else if (!link_up_counter[LNKMSB])
		link_up_counter <= link_up_counter+1;
	// else
	//	link is solidly good
	// }}}

	always @(posedge RX_CLK or negedge S_ARESETN)
	if (!S_ARESETN)
		powering_up <= 1'b1;
	else if (RX_VALID)
		powering_up <= 1'b0;

	assign	o_link_up = link_up_counter[LNKMSB];

	assign o_local_fault = (powering_up || r_local_fault
						|| watchdog_timeout);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// M_*: The final output
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge RX_CLK)
	if (!S_ARESETN)
		M_VALID <= 0;
	else if (!M_VALID || M_READY)
		M_VALID <= dly_valid && (RX_VALID || dly_last);

	always @(posedge RX_CLK)
	if (!M_VALID || M_READY)
	begin
		M_DATA <= dly_data;
		M_BYTES<= dly_bytes[2:0];
		M_LAST <= dly_last || (RX_DATA[9:0] == { 8'h87, SYNC_CONTROL });
	end

	always @(posedge RX_CLK)
	if (!S_ARESETN)
		M_ABORT <= 1'b0;
	else if (RX_VALID && dly_valid && M_VALID && !M_READY)
		M_ABORT <= 1'b1;
	else if (i_phy_fault && ((dly_valid && !dly_last)
					|| (M_VALID && !M_READY && !M_LAST)))
		M_ABORT <= 1'b1;
	else if (dly_valid && !M_ABORT)
	begin
		if (dly_last)
			M_ABORT <= 1'b0;
		else if (RX_DATA[1:0] == SYNC_CONTROL)
		begin
			case(RX_DATA[9:2])
			8'h87: begin end
			8'h99: begin end
			8'haa: begin end
			8'hb4: begin end
			8'hcc: begin end
			8'hd2: begin end
			8'he1: begin end
			8'hff: begin end
			default: M_ABORT <= 1'b1;
			endcase
		end
	end else if (!M_VALID || M_READY)
		M_ABORT <= 1'b0;
	// }}}
endmodule
