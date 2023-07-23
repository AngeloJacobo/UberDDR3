////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axincdc.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Move packets across clock domains.  Both interfaces need to
//		be at less than 100% utilization to be successful.  This will
//	often require expanding the packet from X bits / clock to
//	2X bits / clock or more prior to entering (or after leaving) this
//	module.
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
module axincdc #(
		// {{{
		parameter	DW=32,		// Bits per beat
		parameter	LGFIFO = 4	// Async FIFO size (log_2)
		// }}}
	) (
		// {{{
		// Incoming packet data from one interface
		// {{{
		input	wire				S_CLK, S_ARESETN,
		//
		input	wire				S_VALID,
		output	wire				S_READY,
		input	wire	[DW-1:0]		S_DATA,
		input	wire	[$clog2(DW/8)-1:0]	S_BYTES,
		input	wire				S_ABORT,
		input	wire				S_LAST,
		// }}}
		// Outgoing packet data
		// {{{
		input	wire				M_CLK, M_ARESETN,
		//
		output	wire				M_VALID,
		input	wire				M_READY,
		output	wire	[DW-1:0]		M_DATA,
		output	wire	[$clog2(DW/8)-1:0]	M_BYTES,
		output	wire				M_ABORT,
		output	wire				M_LAST
		// }}}
		// }}}
	);

	wire	w_full, w_empty, w_abort;
	reg	s_midpkt, s_abort;

	// s_midpkt
	// {{{
	always @(posedge S_CLK)
	if (!S_ARESETN)
		s_midpkt <= 1'b0;
	else if (S_ABORT && (!S_VALID || S_READY))
		s_midpkt <= 1'b0;
	else if (S_VALID && S_READY)
		s_midpkt <= !S_LAST;
	// }}}

	// s_abort
	// {{{
	always @(posedge S_CLK)
	if (S_ARESETN)
		s_abort <= 1'b0;
	else if (!w_full)
		s_abort <= 1'b0;
	else if (s_midpkt && S_ABORT && (!S_VALID || S_READY))
		s_abort <= 1'b1;
	// }}}

	afifo #(
		.LGFIFO(LGFIFO),
		.WIDTH(1+1+$clog2(DW/8)+DW)
	) u_afifo (
		// {{{
		.i_wclk(S_CLK),		.i_wr_reset_n(S_ARESETN),
		.i_wr(s_abort || (S_VALID && !S_ABORT) || (S_ABORT&& s_midpkt)),
		.i_wr_data({ s_abort || (S_ABORT && s_midpkt),
						S_LAST, S_BYTES, S_DATA }),
		.o_wr_full(w_full),
		//
		.i_rclk(M_CLK),		.i_rd_reset_n(M_ARESETN),
		.i_rd(M_READY),
		.o_rd_data({ w_abort, M_LAST, M_BYTES, M_DATA }),
		.o_rd_empty(w_empty)
		// }}}
	);

	assign	M_VALID = !w_empty;
	assign	S_READY = S_ABORT || (!w_full && !s_abort);
	assign  M_ABORT = w_abort && M_VALID;
endmodule
