////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	smi.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generates a sort of serial port out of the SMI interface, for
//		interfacing with the CM4.
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
module smi #(
		parameter [0:0]	OPT_ASYNC = 1'b0,
		parameter	LGFIFO = 8
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_reset,
		// (Asynchronous) SMI interface
		// {{{
		input	wire		i_smi_oen, i_smi_wen,
		input	wire	[5:0]	i_smi_sa,
		input	wire	[17:0]	i_smi_data,
		output	wire	[17:0]	o_smi_data,
		output	wire		o_smi_oen,
		// }}}
		// AXI stream interfaces to/from FPGA
		// {{{
		input	wire		S_TX_VALID,
		output	wire		S_TX_READY,
		input	wire	[7:0]	S_TX_DATA,
		//
		output	wire		M_RX_VALID,
		input	wire		M_RX_READY,
		output	wire	[7:0]	M_RX_DATA,

		output	wire	[31:0]	o_debug
		// }}}
		// }}}
	);

	generate if (OPT_ASYNC)
	begin : GEN_ASYNC
		// {{{
		// This should work nicely for writing to the FPGA.  It will
		// fail on reading, however, since transitions will take place
		// as soon as the positive edge of OEN takes place, whereas the
		// protocol requires it hold a bit longer.
		//

		// Local declarations
		// {{{
		wire		ifif_full, ifif_empty, ofif_full, ofif_empty;
		wire	[7:0]	ofif_data;
		reg		rerr, werr;
		wire		ifif_err;
		// }}}

		afifo #(
			.LGFIFO(LGFIFO), .WIDTH(8), .WRITE_ON_POSEDGE(1'b1),
			.OPT_REGISTER_READS(1'b0)
		) u_from_pi (
			// {{{
			.i_wclk(i_smi_wen), .i_wr_reset_n(!i_reset),
			.i_wr(i_smi_sa == 6'h0), .i_wr_data(i_smi_data[7:0]),
				.o_wr_full(ifif_full),
			.i_rclk(i_clk), .i_rd_reset_n(!i_reset),
				.i_rd(M_RX_VALID && M_RX_READY),
				.o_rd_data(M_RX_DATA),
				.o_rd_empty(ifif_empty)
			// }}}
		);

		assign	M_RX_VALID = !ifif_empty;

		afifo #(
			.LGFIFO(LGFIFO), .WIDTH(8), .WRITE_ON_POSEDGE(1'b1),
			.OPT_REGISTER_READS(1'b0)
		) u_to_pi (
			// {{{
			.i_wclk(i_clk), .i_wr_reset_n(!i_reset),
				.i_wr(S_TX_VALID && S_TX_READY),
				.i_wr_data(S_TX_DATA),
				.o_wr_full(ofif_full),
			.i_rclk(i_smi_oen), .i_rd_reset_n(!i_reset),
				.i_rd(i_smi_sa == 6'h0),
				.o_rd_data(ofif_data),
				.o_rd_empty(ofif_empty)
			// }}}
		);

		// FIFO overflow error -- cleared on any read
		// {{{
		always @(posedge i_smi_wen or posedge i_reset)
		if (i_reset)
			werr <= 1'b0;
		else if (ifif_full)
			werr <= !rerr;
	
		always @(posedge i_smi_oen or posedge i_reset)
		if (i_reset)
			rerr <= 1'b0;
		else
			rerr <= werr;

		assign	ifif_err = werr ^ rerr;
		// }}}
	
		assign	S_TX_READY = !ofif_full;
		assign	o_smi_data = { {(18-11){1'b0}}, ifif_err,
				ifif_full, ofif_empty,
				((ofif_empty) ? 8'hff : ofif_data) };
		assign	o_smi_oen = i_smi_oen;
		// }}}
	end else begin : GEN_SYNCHRONOUS
		// {{{
		// Local declarations
		// {{{
		reg		last_oen, last_wen, r_active;
		reg		ck_oen, ck_wen;
		reg	[1:0]	pipe_oen, pipe_wen;

		reg	[11:0]	pipe_addr;
		reg	[5:0]	r_smi_sa;

		reg	[15:0]	pipe_data;
		reg	[7:0]	r_smi_data, r_data;

		wire		ifif_empty, ifif_full, ofif_empty, ofif_full;
		wire	[7:0]	ofif_data;

		wire	[LGFIFO:0]	ign_ifif_fill, ign_ofif_fill;
		reg		fif_err;
		// }}}

		// Clock domain transfer(s)
		// {{{
		always @(posedge i_clk)
		if (i_reset)
		begin
			{ last_oen, ck_oen, pipe_oen } <= -1;
			{ last_wen, ck_wen, pipe_wen } <= -1;
		end else begin
			{ last_oen, ck_oen, pipe_oen }
					<= { ck_oen, pipe_oen, i_smi_oen };
			{ last_wen, ck_wen, pipe_wen }
					<= { ck_wen, pipe_wen, i_smi_wen };
		end

		always @(posedge i_clk)
			{ r_smi_sa, pipe_addr } <= { pipe_addr, i_smi_sa };

		always @(posedge i_clk)
			{ r_smi_data, pipe_data } <= { pipe_data, i_smi_data[7:0] };
		// }}}

		// r_active: Latch the address when it's not changing
		// {{{
		always @(posedge i_clk)
		if ((!ck_oen && !last_oen)||(!ck_wen && !last_wen))
			r_active <= (r_smi_sa == 6'h0);
		// }}}

		// r_data: Latch the data when it's not changing
		// {{{
		always @(posedge i_clk)
		if (!ck_wen && !last_wen)
			r_data   <=  r_smi_data;
		// }}}

		sfifo #(
			.BW(8), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b1)
		) u_from_pi (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_wr(ck_wen && !last_wen && r_active),
				.i_data(r_data),
				.o_full(ifif_full), .o_fill(ign_ifif_fill),
			.i_rd(M_RX_VALID && M_RX_READY),
				.o_data(M_RX_DATA),
				.o_empty(ifif_empty)
			// }}}
		);

		assign	M_RX_VALID = !ifif_empty;

		//
		sfifo #(
			.BW(8), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b1)
		) u_to_pi (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_wr(S_TX_VALID && S_TX_READY),
				.i_data(S_TX_DATA),
				.o_full(ofif_full), .o_fill(ign_ofif_fill),
			.i_rd(ck_oen && !last_oen && r_active),
				.o_data(ofif_data), .o_empty(ofif_empty)
			// }}}
		);

		assign	S_TX_READY = !ofif_full;

		always @(posedge i_clk)
		if (i_reset)
			fif_err <= 1'b0;
		else if (ck_wen && !last_wen && r_active && ifif_full)
			fif_err <= 1'b1;
		else if (ck_oen && !last_oen && r_active)
			fif_err <= 1'b0;
		
		assign	o_smi_data = { {(18-11){1'b0}},
				fif_err, ifif_full, ofif_empty, ofif_data };

		assign	o_smi_oen = &{ last_oen, ck_oen, pipe_oen, i_smi_oen };

		assign	o_debug = {
				((last_oen && !ck_oen)||(last_wen && !ck_wen)),
				o_smi_oen, last_wen && last_oen, ck_oen, ck_wen,
				fif_err, ifif_full, ofif_empty, i_smi_sa,
				(o_smi_oen) ? i_smi_data : o_smi_data
			};


		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_ifif_fill, ign_ofif_fill };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end endgenerate

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_smi_data[17:8] };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
