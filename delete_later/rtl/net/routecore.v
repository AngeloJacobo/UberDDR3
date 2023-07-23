////////////////////////////////////////////////////////////////////////////////
//
// Filename:	routecore.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is intended to be the core of the network router: the
//		routing table.  When a packet is received, from any interface,
//	it is registered in this table together with the interface it comes
//	from.  Then, when we later want to transmit a packet, the table can be
//	queried for which port the given MAC address was last seen on.
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
module routecore #(
		// {{{
		parameter [0:0]	OPT_SKIDBUFFER   = 1'b0,
		parameter [0:0]	OPT_LOWPOWER     = 1'b1,
		parameter [0:0]	OPT_LITTLE_ENDIAN= 1'b0,
		// parameter [0:0]	OPT_DEFBROADCAST = 1'b0
		// parameter [0:0]	OPT_ONE_TO_MANY  = 1'b0
		parameter	NETH = 4,	// Number of incoming eth ports
		// PKTDW is the # of bits per clock cycle or beat of both the
		// {{{
		// incoming and outgoing packet data.  In order to properly
		// cross clock domains, PKTDW must be greater than the
		// original source & sink.  So if the Ethernet interface will
		// generate (roughly) 32'bits per clock, PKTDW must be at least
		// 64-bits per clock.
		parameter	PKTDW = 128,
		// }}}
		localparam	PKTBYW = $clog2(PKTDW/8),
		// BUSDW is the bits per clock cycle or beat of the WB memory
		// {{{
		// bus.  A width conversion may need to take place within the
		// PKTVFIFO to adjust from PKTDW to BUSDW and back again.
		parameter	BUSDW = 512,	// Bits per clock cycle
		// }}}
		// parameter 	BROADCAST_PORT = NETH,
		// parameter 	DEFAULT_PORT = BROADCAST_PORT,
		// parameter	LGTBL = 6,	// Log_2(NTBL entries)
		// localparam	NTBL = (1<<LGTBL), // Number of table entries
		// parameter	LGTIMEOUT = 64-MACW-1,
		parameter	MACW = 48,	// Bits in a MAC address
		parameter	LGROUTETBL = 5,
		parameter	LGROUTE_TIMEOUT = 24,
		parameter	AW = 30-$clog2(BUSDW/8),
		parameter [0:0]	OPT_VFIFO = 1,
		parameter [0:0]	OPT_CPUNET = 0,
		// We need a VFIFO to be successful.
		parameter [AW-1:0]	DEF_BASEADDR = 0,
		parameter [AW-1:0]	DEF_MEMSIZE  = 0
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		// We have only one clock--the bus clock.  All CDCs take
		// place on the way in and on the way out to allow us to
		// work in this one clock domain
		// input	wire	[NETH-1:0]		ETH_CLK,
		//
		// It is possible that we might turn off various interfaces.
		// When an interface is off, that bit in ETH_RESET will be one.
		input	wire	[NETH-1:0]		ETH_RESET,
		// Incoming packets from all interfaces
		// {{{
		input	wire	[NETH-1:0]		RX_VALID,
		output	wire	[NETH-1:0]		RX_READY,
		input	wire	[NETH*PKTDW-1:0]		RX_DATA,
		input	wire	[NETH*PKTBYW-1:0]	RX_BYTES,
		input	wire	[NETH-1:0]		RX_LAST,
		input	wire	[NETH-1:0]		RX_ABORT,
		// }}}
		// VFIFO control interface
		// {{{
		input	wire		i_ctrl_cyc, i_ctrl_stb, i_ctrl_we,
		input	wire	[$clog2(NETH-(OPT_CPUNET ? 1:0))+2-1:0]
					i_ctrl_addr,
		input	wire	[31:0]			i_ctrl_data,
		input	wire	[3:0]			i_ctrl_sel,
		output	wire				o_ctrl_stall,
		output	reg				o_ctrl_ack,
		output	reg	[31:0]			o_ctrl_data,
		// }}}
		// VFIFO memory interface
		// {{{
		output	wire		o_vfifo_cyc, o_vfifo_stb, o_vfifo_we,
		output	wire	[AW-1:0]		o_vfifo_addr,
		output	wire	[BUSDW-1:0]		o_vfifo_data,
		output	wire	[BUSDW/8-1:0]		o_vfifo_sel,
		input	wire				i_vfifo_stall,
		input	wire				i_vfifo_ack,
		input	wire	[BUSDW-1:0]		i_vfifo_data,
		input	wire				i_vfifo_err,
		// }}}
		// Outgoing packets
		// {{{
		output	wire	[NETH-1:0]		TX_VALID,
		input	wire	[NETH-1:0]		TX_READY,
		output	wire	[NETH*PKTDW-1:0]	TX_DATA,
		output	wire	[NETH*PKTBYW-1:0]	TX_BYTES,
		output	wire	[NETH-1:0]		TX_LAST,
		output	wire	[NETH-1:0]		TX_ABORT
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	// parameter [AW-1:0]	DEF_BASEADDR = 0,
	parameter		NMEM = NETH-(OPT_CPUNET ? 1:0);
	// Verilator lint_off WIDTH
	parameter [AW-1:0]	DEF_SUBSIZE  = DEF_MEMSIZE / NMEM;
	// Verilator lint_on  WIDTH
	genvar				geth;

	wire	[NMEM-1:0]		tomem_valid, tomem_ready;
	wire	[NMEM*PKTDW-1:0]	tomem_data;
	wire	[NMEM*PKTBYW-1:0]	tomem_bytes;
	wire	[NMEM-1:0]		tomem_abort;
	wire	[NMEM-1:0]		tomem_last;

	wire	[NETH*NETH-1:0]		rxtbl_valid;
	reg	[NETH*NETH-1:0]		rxtbl_ready;
	wire	[NETH*NETH*MACW-1:0]	rxtbl_data;

	wire	[NETH*NETH-1:0]		txx_valid;
	reg	[NETH*NETH-1:0]		txx_ready;
	wire	[NETH*NETH*PKTDW-1:0]	txx_data;
	wire [NETH*NETH*PKTBYW-1:0]	txx_bytes;
	wire	[NETH*NETH-1:0]		txx_last, txx_abort;

	wire	[NMEM-1:0]		vfifo_cyc, vfifo_stb, vfifo_we,
					vfifo_stall, vfifo_ack, vfifo_err;
	wire	[NMEM*AW-1:0]		vfifo_addr;
	wire	[NMEM*BUSDW-1:0]		vfifo_data, vfifo_idata;
	wire	[NMEM*BUSDW/8-1:0]	vfifo_sel;

	wire	[NMEM-1:0]		ctrl_stb, ctrl_ack, ctrl_stall;
	wire	[NMEM*32-1:0]		ctrl_data;

	integer		wbport;
	reg		pre_ctrl_ack;
	reg	[31:0]	pre_ctrl_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Per-port processing
	// {{{
	generate for (geth=0; geth < NETH-(OPT_CPUNET ? 1:0); geth = geth+1)
	begin : GEN_INTERFACES
		// Per-port declarations
		// {{{
		localparam [NETH-1:0]	THIS_PORT = (1<<geth);
		localparam [NETH-1:0]	EVERYONE_ELSE = ~THIS_PORT;

		wire			smac_valid, smac_ready;
		wire	[MACW-1:0]	smac_data;

		wire			mmout_valid, mmout_ready,
					mmout_abort, mmout_last;
		wire	[PKTDW-1:0]	mmout_data;
		wire [PKTBYW-1:0]	mmout_bytes;

		integer			iport;
		reg	[NETH-1:0]	remap_valid;
		wire	[NETH-1:0]	remap_ready;
		reg	[NETH*MACW-1:0]	remap_data;

		wire			lkup_request, lkup_valid;
		wire	[MACW-1:0]	lkup_dstmac;
		wire	[NETH-1:0]	lkup_port;

		wire			rtd_valid, rtd_ready,
					rtd_last, rtd_abort;
		wire	[PKTDW-1:0]	rtd_data;
		wire	[PKTBYW-1:0]	rtd_bytes;
		wire	[NETH-1:0]	rtd_port;

		reg	[NETH-1:0]		prearb_valid;
		wire	[NETH-1:0]		prearb_ready;
		reg	[NETH*PKTDW-1:0]	prearb_data;
		reg	[NETH*PKTBYW-1:0]	prearb_bytes;
		reg	[NETH-1:0]		prearb_last, prearb_abort;
		// }}}

		// Grab packet MACs for the router
		// {{{
		rxgetsrcmac #(
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(PKTDW), .MACW(MACW)
		) u_rxgetsrcmac (
			// {{{
			.i_clk(i_clk),
			.i_reset(i_reset || ETH_RESET[geth]),
			//
			.S_VALID(RX_VALID[geth]),
			.S_READY(RX_READY[geth]),
			.S_DATA( RX_DATA[geth * PKTDW +: PKTDW]),
			.S_BYTES(RX_BYTES[geth * PKTBYW +: PKTBYW]),
			.S_LAST( RX_LAST[geth]),
			.S_ABORT(RX_ABORT[geth]),
			//
			.M_VALID(tomem_valid[geth]),
			.M_READY(tomem_ready[geth]),
			.M_DATA( tomem_data[geth * PKTDW +: PKTDW]),
			.M_BYTES(tomem_bytes[geth * PKTBYW +: PKTBYW]),
			.M_LAST( tomem_last[geth]),
			.M_ABORT(tomem_abort[geth]),
			//
			.TBL_VALID(smac_valid),
			.TBL_READY(smac_ready),
			.TBL_SRCMAC(smac_data)
			// }}}
		);
		// }}}

		// smac->rxtbl: Broadcast Rx MACs to each channel's router
		// {{{
		axisbroadcast #(
			.C_AXIS_DATA_WIDTH(MACW), .NM(NETH)
		) u_rxtbl_broadcast (
			// {{{
			.S_AXI_ACLK(i_clk),
			.S_AXI_ARESETN(i_reset || ETH_RESET[geth]),
			//
			.S_AXIS_TVALID(smac_valid),
			.S_AXIS_TREADY(smac_ready),
			.S_AXIS_TDATA(smac_data),
			//
			.M_AXIS_TVALID(rxtbl_valid[geth * NETH +: NETH]),
			.M_AXIS_TREADY(rxtbl_ready[geth * NETH +: NETH] | ETH_RESET),
			.M_AXIS_TDATA(rxtbl_data[geth * MACW * NETH +: MACW * NETH])
			// }}}
		);
		// }}}

		// All packets go to memory: tomem -> (dma_wb) -> mmout
		// {{{
		assign	ctrl_stb[geth] = i_ctrl_stb
				&& i_ctrl_addr[2 +: $clog2(NMEM)] == geth;

		if (OPT_VFIFO)
		begin : GEN_VFIFO

			pktvfifo #(
				// {{{
				.AW(AW),		// Bus address width
				.PKTDW(PKTDW),		// Packet data width
				.BUSDW(BUSDW),		// Bus width
				// DEF_BASEADDR: The VFIFO default base
				// address -- set this and the default memory
				// size to nonzero in order to cause the VFIFO
				// to start automaticallt w/o CPU intervention.
				// Both addresses are *WORD* addresses, so need
				// to be shifted by $clog2(BUSDW/8) to get
				// their proper bus address location.
				.DEF_BASEADDR(DEF_BASEADDR + geth*DEF_SUBSIZE),
				.DEF_MEMSIZE(DEF_SUBSIZE),
				.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
				.OPT_LOWPOWER(OPT_LOWPOWER)
				// }}}
			) u_pktvfifo (
				// {{{
				.i_clk(i_clk),
				.i_reset(i_reset || ETH_RESET[geth]),
				// Bus control port
				// {{{
				.i_ctrl_cyc(i_ctrl_cyc), .i_ctrl_stb(i_ctrl_stb
					&& i_ctrl_addr[2 +: $clog2(NMEM)] == geth),
				.i_ctrl_we(i_ctrl_we), .i_ctrl_addr(i_ctrl_addr[1:0]),
				.i_ctrl_data(i_ctrl_data), .i_ctrl_sel(i_ctrl_sel),
				.o_ctrl_stall(ctrl_stall[geth]),
				.o_ctrl_ack(  ctrl_ack[  geth]),
				.o_ctrl_data( ctrl_data[ geth * 32 +: 32]),
				// }}}
				// Incoming packet
				// {{{
				.S_VALID(tomem_valid[geth]),
				.S_READY(tomem_ready[geth]),
				.S_DATA( tomem_data[ geth * PKTDW +: PKTDW]),
				.S_BYTES(tomem_bytes[geth * PKTBYW +: PKTBYW]),
				.S_LAST( tomem_last[geth]),
				.S_ABORT(tomem_abort[geth]),
				// }}}
				// DMA bus interface
				// {{{
				.o_wb_cyc(vfifo_cyc[    geth]),
				.o_wb_stb(vfifo_stb[    geth]),
				.o_wb_we(vfifo_we[      geth]),
				.o_wb_addr(vfifo_addr[  geth * AW +: AW]),
				.o_wb_data(vfifo_data[  geth * BUSDW   +: BUSDW  ]),
				.o_wb_sel(vfifo_sel[    geth * BUSDW/8 +: BUSDW/8]),
				.i_wb_stall(vfifo_stall[geth]),
				.i_wb_ack(vfifo_ack[    geth]),
				.i_wb_data(vfifo_idata[ geth * BUSDW +: BUSDW]),
				.i_wb_err(vfifo_err[    geth]),
				// This needs to go to a crossbar next ...
				// }}}
				// Outgoing packet
				// {{{
				.M_VALID(mmout_valid),
				.M_READY(mmout_ready),
				.M_DATA( mmout_data),
				.M_BYTES(mmout_bytes),
				.M_LAST( mmout_last),
				.M_ABORT(mmout_abort)
				// }}}
				// }}}
			);

		end else begin : NO_VFIFO
			reg	r_ctrl_ack;

			netfifo #(
				// {{{
				.BW(PKTDW + $clog2(PKTDW/8)),
				.LGFLEN(10)
				// }}}
			) u_netfifo (
				// {{{
				.S_AXI_ACLK(i_clk),
				.S_AXI_ARESETN(!i_reset && !ETH_RESET[geth]),
				// Incoming packet
				// {{{
				.S_AXIN_VALID(tomem_valid[geth]),
				.S_AXIN_READY(tomem_ready[geth]),
				.S_AXIN_DATA({ tomem_bytes[geth * PKTBYW +: PKTBYW],
					tomem_data[ geth * PKTDW +: PKTDW] }),
				.S_AXIN_LAST( tomem_last[geth]),
				.S_AXIN_ABORT(tomem_abort[geth]),
				// }}}
				// (No) DMA bus interface
				// Outgoing packet
				// {{{
				.M_AXIN_VALID(mmout_valid),
				.M_AXIN_READY(mmout_ready),
				.M_AXIN_DATA({ mmout_bytes, mmout_data }),
				.M_AXIN_LAST( mmout_last),
				.M_AXIN_ABORT(mmout_abort)
				// }}}
				// }}}
			);

			assign	vfifo_cyc[geth] = 1'b0;
			assign	vfifo_stb[geth] = 1'b0;
			assign	vfifo_we[geth]  = 1'b0;
			assign	vfifo_addr[geth * AW +: AW]= {(AW){1'b0}};
			assign	vfifo_data[geth * BUSDW +: BUSDW]= {(BUSDW){1'b0}};
			assign	vfifo_sel[geth * BUSDW/8 +: BUSDW/8] = {(BUSDW/8){1'b0}};

			initial	r_ctrl_ack = 1'b0;
			always @(posedge i_clk)
			if (i_reset || !i_ctrl_cyc)
				r_ctrl_ack <= 1'b0;
			else
				r_ctrl_ack <= i_ctrl_stb
					&& i_ctrl_addr[2 +: $clog2(NMEM)]==geth;

			assign	ctrl_stall[geth] = 1'b0;
			assign	ctrl_ack[geth]   = r_ctrl_ack;
			assign	ctrl_data[ geth * 32 +: 32] = 32'h0;
		end
		// }}}

		// mmout->rtd, On return from memory, lookup the destinations
		// {{{
		txgetports #(
			// {{{
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.NETH(NETH), .DW(PKTDW), .MACW(MACW)
			// }}}
		) u_txgetports (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.S_VALID(mmout_valid), .S_READY(mmout_ready),
			.S_DATA(mmout_data), .S_BYTES(mmout_bytes),
			.S_LAST(mmout_last), .S_ABORT(mmout_abort),
			//
			//
			.TBL_REQUEST(lkup_request), .TBL_VALID(lkup_valid),
			.TBL_MAC(lkup_dstmac),.TBL_PORT(lkup_port & ~THIS_PORT),
			//
			.M_VALID(rtd_valid), .M_READY(rtd_ready),
			.M_DATA(rtd_data), .M_BYTES(rtd_bytes),
			.M_LAST(rtd_last), .M_ABORT(rtd_abort),
			.M_PORT(rtd_port)
			//
			// }}}
		);
		// }}}

		// rtd->txx Broadcast our packet to all interested ports
		// {{{
		axinbroadcast #(
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.NOUT(NETH), .DW(PKTDW)
		) u_rtdbroadcast (
			// {{{
			.i_clk(i_clk),
			.i_reset(i_reset),
			//
			.i_cfg_active(~ETH_RESET),
			// rtd_*, packet with routing
			// {{{
			.S_VALID(rtd_valid),
			.S_READY(rtd_ready),
			.S_DATA(rtd_data),
			.S_PORT(rtd_port),
			.S_BYTES(rtd_bytes),
			.S_LAST(rtd_last),
			.S_ABORT(rtd_abort),
			// }}}
			// txx_*
			// {{{
			.M_VALID(txx_valid[geth * NETH +: NETH]),
			.M_READY(txx_ready[geth * NETH +: NETH] | ETH_RESET),
			.M_DATA(txx_data[geth * PKTDW * NETH +: PKTDW * NETH]),
			.M_BYTES(txx_bytes[geth * PKTBYW * NETH
						+: PKTBYW * NETH]),
			.M_LAST(txx_last[geth * NETH +: NETH]),
			.M_ABORT(txx_abort[geth * NETH +: NETH])
			// }}}
			// }}}
		);
		// }}}

		// Arbitrate from among packets from other ports
		// {{{
		always @(*)
		for(iport=0; iport<NETH; iport=iport+1)
		begin
			prearb_valid[iport] = txx_valid[geth * NETH+iport];
			txx_ready[geth*NETH+iport] = prearb_ready[iport];
			prearb_data[iport * PKTDW +: PKTDW]
				 = txx_data[(geth*NETH+iport)*PKTDW +: PKTDW];
			prearb_bytes[iport * PKTBYW +: PKTBYW]
				 = txx_bytes[(geth*NETH+iport)*PKTBYW +: PKTBYW];
			prearb_last[iport]  = txx_last[geth*NETH+iport];
			prearb_abort[iport] = txx_abort[geth*NETH+iport];
		end

		axinarbiter #(
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(PKTDW),
			.NIN(NETH)
		) u_txarbiter (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.S_VALID(prearb_valid),
			.S_READY(prearb_ready),
			.S_DATA( prearb_data),
			.S_BYTES(prearb_bytes),
			.S_LAST( prearb_last),
			.S_ABORT(prearb_abort),
			//
			.M_VALID(TX_VALID[geth]),
			.M_READY(TX_READY[geth]),
			.M_DATA( TX_DATA[ geth*PKTDW +: PKTDW]),
			.M_BYTES(TX_BYTES[geth*PKTBYW +: PKTBYW]),
			.M_LAST( TX_LAST[ geth]),
			.M_ABORT(TX_ABORT[geth])
			// }}}
		);
		// }}}

		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		// The router table itself
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////

		always @(*)
		for(iport=0; iport<NETH; iport=iport+1)
		begin
			remap_valid[iport] = rxtbl_valid[geth * NETH+iport];
			rxtbl_ready[geth*NETH+iport] = remap_ready[iport];
			remap_data[iport * MACW +: MACW]
				 = rxtbl_data[(geth*NETH+iport)*MACW +: MACW];
		end

		routetbl #(
			// {{{
			.NETH(NETH),
			.BROADCAST_PORT(EVERYONE_ELSE),
			// .DEFAULT_PORT(NETH),
			.LGTBL(LGROUTETBL),
			.LGTIMEOUT(LGROUTE_TIMEOUT),
			.MACW(MACW),
			.OPT_LOWPOWER(OPT_LOWPOWER)
			// }}}
		) u_routetbl (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.RX_VALID(remap_valid),
			.RX_READY(remap_ready),
			.RX_SRCMAC(remap_data),

			.TX_VALID( lkup_request),
			.TX_ACK(   lkup_valid),
			.TX_DSTMAC(lkup_dstmac),
			.TX_PORT(  lkup_port)
			// }}}
		);

		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Special port: the CPUNET
	// {{{

	generate if (OPT_CPUNET)
	begin : GEN_CPUNET
		// Per-port declarations
		// {{{
		localparam [NETH-1:0]	THIS_PORT = (1<<(NETH-1));
		localparam [NETH-1:0]	EVERYONE_ELSE = ~THIS_PORT;

		wire			smac_valid, smac_ready;
		wire	[MACW-1:0]	smac_data;

		wire			mmout_valid, mmout_ready,
					mmout_abort, mmout_last;
		wire	[PKTDW-1:0]	mmout_data;
		wire [PKTBYW-1:0]	mmout_bytes;

		integer			iport;
		reg	[NETH-1:0]	remap_valid;
		wire	[NETH-1:0]	remap_ready;
		reg	[NETH*MACW-1:0]	remap_data;

		wire			lkup_request, lkup_valid;
		wire	[MACW-1:0]	lkup_dstmac;
		wire	[NETH-1:0]	lkup_port;

		wire			rtd_valid, rtd_ready,
					rtd_last, rtd_abort;
		wire	[PKTDW-1:0]	rtd_data;
		wire	[PKTBYW-1:0]	rtd_bytes;
		wire	[NETH-1:0]	rtd_port;

		reg	[NETH-1:0]		prearb_valid;
		wire	[NETH-1:0]		prearb_ready;
		reg	[NETH*PKTDW-1:0]	prearb_data;
		reg	[NETH*PKTBYW-1:0]	prearb_bytes;
		reg	[NETH-1:0]		prearb_last, prearb_abort;
		// }}}

		// Grab packet MACs for the router
		// {{{
		rxgetsrcmac #(
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(PKTDW), .MACW(MACW)
		) u_rxgetsrcmac (
			// {{{
			.i_clk(i_clk),
			.i_reset(i_reset || ETH_RESET[NETH-1]),
			//
			.S_VALID(RX_VALID[NETH-1]),
			.S_READY(RX_READY[NETH-1]),
			.S_DATA( RX_DATA[(NETH-1) * PKTDW +: PKTDW]),
			.S_BYTES(RX_BYTES[(NETH-1) * PKTBYW +: PKTBYW]),
			.S_LAST( RX_LAST[NETH-1]),
			.S_ABORT(RX_ABORT[NETH-1]),
			//
			.M_VALID(mmout_valid),
			.M_READY(mmout_ready),
			.M_DATA( mmout_data),
			.M_BYTES(mmout_bytes),
			.M_LAST( mmout_last),
			.M_ABORT(mmout_abort),
			//
			.TBL_VALID(smac_valid),
			.TBL_READY(smac_ready),
			.TBL_SRCMAC(smac_data)
			// }}}
		);
		// }}}

		// smac->rxtbl: Broadcast Rx MACs to each channel's router
		// {{{
		axisbroadcast #(
			.C_AXIS_DATA_WIDTH(MACW), .NM(NETH)
		) u_rxtbl_broadcast (
			// {{{
			.S_AXI_ACLK(i_clk),
			.S_AXI_ARESETN(i_reset || ETH_RESET[NETH-1]),
			//
			.S_AXIS_TVALID(smac_valid),
			.S_AXIS_TREADY(smac_ready),
			.S_AXIS_TDATA(smac_data),
			//
			.M_AXIS_TVALID(rxtbl_valid[(NETH-1) * NETH +: NETH]),
			.M_AXIS_TREADY(rxtbl_ready[(NETH-1) * NETH +: NETH] | ETH_RESET),
			.M_AXIS_TDATA(rxtbl_data[(NETH-1) * MACW * NETH +: MACW * NETH])
			// }}}
		);
		// }}}

		// The big difference--incoming CPU pkts do *not* go to memory

		// mmout->rtd, On return from memory, lookup the destinations
		// {{{
		txgetports #(
			// {{{
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.NETH(NETH), .DW(PKTDW), .MACW(MACW)
			// }}}
		) u_txgetports (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.S_VALID(mmout_valid), .S_READY(mmout_ready),
			.S_DATA(mmout_data), .S_BYTES(mmout_bytes),
			.S_LAST(mmout_last), .S_ABORT(mmout_abort),
			//
			//
			.TBL_REQUEST(lkup_request), .TBL_VALID(lkup_valid),
			.TBL_MAC(lkup_dstmac),.TBL_PORT(lkup_port & ~THIS_PORT),
			//
			.M_VALID(rtd_valid), .M_READY(rtd_ready),
			.M_DATA(rtd_data), .M_BYTES(rtd_bytes),
			.M_LAST(rtd_last), .M_ABORT(rtd_abort),
			.M_PORT(rtd_port)
			//
			// }}}
		);
		// }}}

		// rtd->txx Broadcast our packet to all interested ports
		// {{{
		axinbroadcast #(
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.NOUT(NETH), .DW(PKTDW)
		) u_rtdbroadcast (
			// {{{
			.i_clk(i_clk),
			.i_reset(i_reset),
			//
			.i_cfg_active(~ETH_RESET),
			// rtd_*, packet with routing
			// {{{
			.S_VALID(rtd_valid),
			.S_READY(rtd_ready),
			.S_DATA(rtd_data),
			.S_PORT(rtd_port),
			.S_BYTES(rtd_bytes),
			.S_LAST(rtd_last),
			.S_ABORT(rtd_abort),
			// }}}
			// txx_*
			// {{{
			.M_VALID(txx_valid[(NETH-1) * NETH +: NETH]),
			.M_READY(txx_ready[(NETH-1) * NETH +: NETH] | ETH_RESET),
			.M_DATA(txx_data[(NETH-1) * PKTDW * NETH +: PKTDW * NETH]),
			.M_BYTES(txx_bytes[(NETH-1) * PKTBYW * NETH
						+: PKTBYW * NETH]),
			.M_LAST(txx_last[(NETH-1) * NETH +: NETH]),
			.M_ABORT(txx_abort[(NETH-1) * NETH +: NETH])
			// }}}
			// }}}
		);
		// }}}

		// Arbitrate from among packets from other ports
		// {{{
		always @(*)
		for(iport=0; iport<NETH; iport=iport+1)
		begin
			prearb_valid[iport] = txx_valid[(NETH-1) * NETH+iport];
			txx_ready[(NETH-1)*NETH+iport] = prearb_ready[iport];
			prearb_data[iport * PKTDW +: PKTDW]
				 = txx_data[((NETH-1)*NETH+iport)*PKTDW +: PKTDW];
			prearb_bytes[iport * PKTBYW +: PKTBYW]
				 = txx_bytes[((NETH-1)*NETH+iport)*PKTBYW +: PKTBYW];
			prearb_last[iport]  = txx_last[(NETH-1)*NETH+iport];
			prearb_abort[iport] = txx_abort[(NETH-1)*NETH+iport];
		end

		axinarbiter #(
			.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(PKTDW),
			.NIN(NETH)
		) u_txarbiter (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.S_VALID(prearb_valid),
			.S_READY(prearb_ready),
			.S_DATA( prearb_data),
			.S_BYTES(prearb_bytes),
			.S_LAST( prearb_last),
			.S_ABORT(prearb_abort),
			//
			.M_VALID(TX_VALID[(NETH-1)]),
			.M_READY(TX_READY[(NETH-1)]),
			.M_DATA( TX_DATA[ (NETH-1)*PKTDW +: PKTDW]),
			.M_BYTES(TX_BYTES[(NETH-1)*PKTBYW +: PKTBYW]),
			.M_LAST( TX_LAST[ (NETH-1)]),
			.M_ABORT(TX_ABORT[(NETH-1)])
			// }}}
		);
		// }}}

		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		// The router table itself
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////

		always @(*)
		for(iport=0; iport<NETH; iport=iport+1)
		begin
			remap_valid[iport] = rxtbl_valid[(NETH-1) * NETH+iport];
			rxtbl_ready[(NETH-1)*NETH+iport] = remap_ready[iport];
			remap_data[iport * MACW +: MACW]
				 = rxtbl_data[((NETH-1)*NETH+iport)*MACW +: MACW];
		end

		routetbl #(
			// {{{
			.NETH(NETH),
			.BROADCAST_PORT(EVERYONE_ELSE),
			// .DEFAULT_PORT(NETH),
			.LGTBL(LGROUTETBL),
			.LGTIMEOUT(LGROUTE_TIMEOUT),
			.MACW(MACW),
			.OPT_LOWPOWER(OPT_LOWPOWER)
			// }}}
		) u_routetbl (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.RX_VALID(remap_valid),
			.RX_READY(remap_ready),
			.RX_SRCMAC(remap_data),

			.TX_VALID( lkup_request),
			.TX_ACK(   lkup_valid),
			.TX_DSTMAC(lkup_dstmac),
			.TX_PORT(  lkup_port)
			// }}}
		);

		// }}}
	end endgenerate
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone slave return processing
	// {{{

	assign	o_ctrl_stall = |(ctrl_stb & ctrl_stall);

	always @(posedge i_clk)
	if (i_reset || !i_ctrl_cyc)
		pre_ctrl_ack <= 0;
	else
		pre_ctrl_ack <= i_ctrl_stb && !o_ctrl_stall;

	always @(posedge i_clk)
	if (i_reset || !i_ctrl_cyc)
		o_ctrl_ack <= 0;
	else
		o_ctrl_ack <= pre_ctrl_ack;

	always @(*)
	begin
		pre_ctrl_data = 0;
		for(wbport=0; wbport < NETH; wbport = wbport+1)
		if (ctrl_ack[wbport])
			pre_ctrl_data = pre_ctrl_data | ctrl_data[wbport*32 +: 32];
	end

	always @(posedge i_clk)
	if (OPT_VFIFO)
		o_ctrl_data <= pre_ctrl_data;
	else
		o_ctrl_data <= 0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone master arbiter, for the VFIFO interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wbmarbiter #(
		.DW(BUSDW), .AW(AW), .NIN(NMEM)
	) u_wbmarbiter (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.s_cyc(  vfifo_cyc),   .s_stb( vfifo_stb),  .s_we( vfifo_we),
		.s_addr( vfifo_addr),  .s_data(vfifo_data), .s_sel(vfifo_sel),
		.s_stall(vfifo_stall), .s_ack( vfifo_ack),.s_idata(vfifo_idata),
			.s_err(vfifo_err),
		//
		.m_cyc(o_vfifo_cyc),  .m_stb(o_vfifo_stb),  .m_we(o_vfifo_we),
		.m_addr(o_vfifo_addr),.m_data(o_vfifo_data),.m_sel(o_vfifo_sel),
		.m_stall(i_vfifo_stall),.m_ack(i_vfifo_ack),.m_idata(i_vfifo_data),
			.m_err(i_vfifo_err)
		// }}}
	);

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };

	generate if (!OPT_VFIFO)
	begin : GEN_UNUSED_VFIFO
		wire	unused_vfifo_wb;
		assign	unused_vfifo_wb = &{ 1'b0, vfifo_stall, vfifo_ack,
				vfifo_idata, vfifo_err, i_ctrl_addr,
				i_ctrl_we, i_ctrl_sel, i_ctrl_data };
	end endgenerate
	// Verilator lint_on  UNUSED
	// }}}
endmodule
