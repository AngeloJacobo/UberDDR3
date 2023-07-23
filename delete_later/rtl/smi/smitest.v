////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	smitest.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	
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
`default_nettype	none
// }}}
module	smitest (
		input	wire		i_clk_200mhz_p, i_clk_200mhz_n,
		input	wire		i_wbu_uart_rx,
		output	wire		o_wbu_uart_tx,
		output	wire		o_wbu_uart_cts_n,
		input	wire		i_smi_wen, i_smi_oen,
		input	wire	[5:0]	i_smi_sa,
		inout	wire	[17:0]	io_smi_sd
	);

	localparam	real	CLOCK_FREQUENCY_MHZ = 200.0,
				BAUD_RATE_KHZ = 19.200;
	localparam	CLOCKS_PER_BAUD = $rtoi(CLOCK_FREQUENCY_MHZ * 1000.0
					/ BAUD_RATE_KHZ),
			TIMING_BITS = $clog2(CLOCKS_PER_BAUD+1);

	wire		ck_prebuf, s_clk;
	wire		rx_valid, rx_ready, tx_valid, tx_ready, tx_busy;
	wire	[7:0]	rx_data, tx_data;
	wire	[17:0]	o_smi_data;
	wire		o_smi_oen;
	reg		s_reset;
	reg	[1:0]	reset_pipe;

	IBUFDS
	clk_ibuf (
		.I(i_clk_200mhz_p), .IB(i_clk_200mhz_n),
		.O(ck_prebuf)
	);

	BUFG clk_bfg ( .I(ck_prebuf), .O(s_clk) );

	initial	{ s_reset, reset_pipe } = -1;
	always @(posedge s_clk)
		{ s_reset, reset_pipe } <= { reset_pipe, 1'b0 };

	txuartlite #(
		.TIMING_BITS(TIMING_BITS[4:0]),
		.CLOCKS_PER_BAUD(CLOCKS_PER_BAUD[TIMING_BITS-1:0])
	) u_txuart (
		.i_clk(s_clk), .i_wr(tx_valid && !tx_busy),
			.i_data(tx_data),
		.o_uart_tx(o_wbu_uart_tx), .o_busy(tx_busy)
	);

	assign	tx_ready = !tx_busy;

	rxuartlite #(
		.TIMER_BITS(TIMING_BITS[4:0]),
		.CLOCKS_PER_BAUD(CLOCKS_PER_BAUD[TIMING_BITS-1:0])
	) u_rxuart (
		.i_clk(s_clk), .i_uart_rx(i_wbu_uart_rx),
		.o_wr(rx_valid), .o_data(rx_data)
	);

	assign	o_wbu_uart_cts_n = o_smi_data[8];

	smi #(
		.OPT_ASYNC(1'b0)
	) u_smi (
		.i_clk(s_clk), .i_reset(s_reset),
		.i_smi_oen(i_smi_oen), .i_smi_wen(i_smi_wen),
		.i_smi_sa(i_smi_sa),
		.i_smi_data(io_smi_sd), .o_smi_data(o_smi_data),
		.o_smi_oen(o_smi_oen),
		.S_TX_VALID(rx_valid), .S_TX_READY(rx_ready),
			.S_TX_DATA(rx_data),
		.M_RX_VALID(tx_valid), .M_RX_READY(tx_ready),
			.M_RX_DATA(tx_data)
	);

	assign	io_smi_sd = (o_smi_oen) ? 18'hz : o_smi_data;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, rx_ready };
	// Verilator lint_on  UNUSED
endmodule

`ifdef	VERILATOR
// {{{
// Verilator lint_off DECLFILENAME
module IBUFDS ( input wire I, input wire IB, output wire O );
	assign	O = I;
	// Verilator lint_off UNUSED
	wire	unused = IB;
	// Verilator lint_on  UNUSED
endmodule

module BUFG ( input wire I, output wire O );
	assign	O = I;
endmodule
// Verilator lint_on  DECLFILENAME
// }}}
`endif	// VERILATOR
