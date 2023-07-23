////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdio_top.v
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
//
`default_nettype none
// }}}
module sdio_top #(
		// {{{
		parameter	LGFIFO = 12, NUMIO=4, MW=32,
		parameter [0:0]	OPT_SERDES=0,
		parameter [0:0]	OPT_DDR=1,
		parameter [0:0]	OPT_CARD_DETECT=1,
		parameter	LGTIMEOUT = 23
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset, i_hsclk,
		// Control (Wishbone) interface
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[2:0]	i_wb_addr,
		input	wire [MW-1:0]	i_wb_data,
		input	wire [MW/8-1:0]	i_wb_sel,
		//
		output	wire		o_wb_stall, o_wb_ack,
		output	wire [MW-1:0]	o_wb_data,
		// }}}
		// IO interface
		// {{{
		output	wire			o_ck,
		input	wire			i_ds,
`ifdef	VERILATOR
		output	wire			io_cmd_tristate,
		output	wire			o_cmd,
		input	wire			i_cmd,
		//
		output	wire	[NUMIO-1:0]	io_dat_tristate,
		output	wire	[NUMIO-1:0]	o_dat,
		input	wire	[NUMIO-1:0]	i_dat,
`else
		inout	wire			io_cmd,
		inout	wire	[NUMIO-1:0]	io_dat,
`endif
		// }}}
		input	wire		i_card_detect,
		output	wire		o_1p8v,
		output	wire		o_int,
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	wire		cfg_ddr;
	wire	[4:0]	cfg_sample_shift;
	wire	[7:0]	sdclk;
		//
	wire		cmd_en, pp_cmd;
	wire	[1:0]	cmd_data;
		//
	wire		data_en, pp_data, rx_en;
	wire	[31:0]	tx_data;
	wire		afifo_reset_n;
		//
	wire	[1:0]	rply_strb, rply_data;
	wire		card_busy;
	wire	[1:0]	rx_strb;
	wire	[15:0]	rx_data;
		//
	wire		AC_VALID;
	wire	[1:0]	AC_DATA;
	wire		AD_VALID;
	wire	[31:0]	AD_DATA;
	// }}}

	sdio #(
		// {{{
		.LGFIFO(LGFIFO), .NUMIO(NUMIO), .MW(MW),
		.OPT_DDR(OPT_DDR), .OPT_SERDES(OPT_SERDES),
		.OPT_CARD_DETECT(OPT_CARD_DETECT),
		.LGTIMEOUT(LGTIMEOUT)
		// }}}
	) u_sdio (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// Control (Wishbone) interface
		// {{{
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb), .i_wb_we(i_wb_we),
		.i_wb_addr(i_wb_addr),.i_wb_data(i_wb_data),.i_wb_sel(i_wb_sel),
		//
		.o_wb_stall(o_wb_stall), .o_wb_ack(o_wb_ack),
		.o_wb_data(o_wb_data),
		// }}}
		.i_card_detect(i_card_detect),
		.o_1p8v(o_1p8v),
		.o_int(o_int),
		// Interface to PHY
		// {{{
		.o_cfg_ddr(cfg_ddr),
		.o_cfg_sample_shift(cfg_sample_shift),
		.o_sdclk(sdclk),
		//
		.o_cmd_en(cmd_en), .o_pp_cmd(pp_cmd),
		.o_cmd_data(cmd_data),
		//
		.o_data_en(data_en), .o_rx_en(rx_en), .o_pp_data(pp_data),
		.o_tx_data(tx_data),
		.o_afifo_reset_n(afifo_reset_n),
		//
		.i_cmd_strb(rply_strb), .i_cmd_data(rply_data),
		.i_card_busy(card_busy),
		.i_rx_strb(rx_strb),
		.i_rx_data(rx_data),
		//
		.S_AC_VALID(AC_VALID), .S_AC_DATA(AC_DATA),
		.S_AD_VALID(AD_VALID), .S_AD_DATA(AD_DATA)
		// }}}
		// }}}
	);

	sdfrontend #(
		.OPT_SERDES(OPT_SERDES), .OPT_DDR(OPT_DDR), .NUMIO(NUMIO)
	) u_sdfrontend (
		// {{{
		.i_clk(i_clk), .i_hsclk(i_hsclk), .i_reset(i_reset),
		.i_cfg_ddr(cfg_ddr), .i_sample_shift(cfg_sample_shift),
		// Tx path
		// {{{
		// MSB "first" incoming data.
		.i_sdclk(sdclk),
		//
		.i_cmd_en(cmd_en), .i_pp_cmd(pp_cmd), .i_cmd_data(cmd_data),				.o_data_busy(card_busy),
		//
		.i_data_en(data_en), .i_pp_data(pp_data), .i_tx_data(tx_data),
			.i_afifo_reset_n(afifo_reset_n),
		// }}}
		// Synchronous Rx path
		// {{{
		.i_rx_en(rx_en),
		.o_cmd_strb(rply_strb),
		.o_cmd_data(rply_data),
		//
		.o_rx_strb(rx_strb),
		.o_rx_data(rx_data),
		// }}}
		// Async Rx path
		// {{{
		.MAC_VALID(AC_VALID), .MAC_DATA(AC_DATA),
		.MAD_VALID(AD_VALID), .MAD_DATA(AD_DATA),
		// }}}
		// I/O ports
		// {{{
		.o_ck(o_ck), .i_ds(i_ds),
`ifdef	VERILATOR
		.io_cmd_tristate(io_cmd_tristate),
		.o_cmd(o_cmd), .i_cmd(i_cmd),
		//
		.io_dat_tristate(io_dat_tristate),
		.o_dat(o_dat), .i_dat(i_dat),
`else
		.io_cmd(io_cmd),
		.io_dat(io_dat),
`endif
		// }}}
		.o_debug(o_debug)
		// }}}
	);

endmodule
