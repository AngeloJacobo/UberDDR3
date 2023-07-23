////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xgtxphy.v
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
module	xgtxphy #(
		parameter	NDEV=1
	) (
		input	wire			i_wb_clk,
		//
		output	wire	[NDEV-1:0]	o_phy_fault,
		// p64b: Internal connections
		// {{{
		// TX path, from IP to PHY
		output	wire	[NDEV-1:0]	S_CLK,
		// input wire			S_VALID,	// Assumed == 1
		output	wire	[NDEV-1:0]	S_READY,
		input	wire	[66*NDEV-1:0]	S_DATA,
		// RX path, from PHY to IP
		output	wire	[NDEV-1:0]	M_CLK,
		output	wire	[NDEV-1:0]	M_VALID,
		// input wire	[NDEV-1:0]	M_READY,	// Assumed == 1
		output	wire	[66*NDEV-1:0]	M_DATA,
		// }}}
		// Pad connections from PHY
		// {{{
		input	wire			i_refck_p, i_refck_n,
		input	wire	[NDEV-1:0]	i_rx_p, i_rx_n,
		output	wire	[NDEV-1:0]	o_tx_p, o_tx_n
		// }}}
	);

	// Local declarations
	// {{{
	genvar		gk;
	wire		pll_lock, qpll_clk, gtx_refck;
	reg		pll_reset, pll_reset_pipe;
	reg		gtx_reset;
	reg	[1:0]	gtx_reset_pipe;
	wire [NDEV-1:0]	unbuf_rx_clk, unbuf_tx_clk;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// GTX PLL / clock control
	// {{{
	initial { pll_reset, pll_reset_pipe } = -1;
	always @(posedge i_wb_clk)
		{ pll_reset, pll_reset_pipe } <= { pll_reset_pipe, 1'b0 };

	// fPllClkIn = 156.25
	// fPLLClkOut = fPllClkIn * (N / 2 / M)
	//		N == 66
	//		M == 1
	//		D == 1
	// fLineRate = fPllClkOut * 2 / D
	//	fLineRate = (fPllClkIn) * (66 / (2M) * 2 / D)
	//	(iff M == D)
	//	fLineRate = (fPllClkIn) * 66
	//		= 10312.5 MHz
	GTXE2_COMMON #(
		// {{{
		// .BIAS_CFG(),		// 63:0
		// .COMMON_CFG(),		// 32:0
		// .IS_DRPCLK_INVERTED(),
		// .IS_GTGREFCLK_INVERTED(),
		// .IS_QPLLLOCKDETCLK_INVERTED(),
		// .QPLL_CFG(),			// 26:0
		// .QPLL_CLKOUT_CFG(),		// 3:0
		// .QPLL_COARSE_FREQ_OVRD(),	// 5:0
		.QPLL_COARSE_FREQ_OVRD_EN(1'b0),
		// .QPLL_CP(),			// 9:0
		.QPLL_CP_MONITOR_EN(1'b0),
		// .QPLL_DMONITOR_SEL(),
		.QPLL_FBDIV(10'h140),			// 9:0
		.QPLL_FBDIV_MONITOR_EN(1'b0),
		.QPLL_FBDIV_RATIO(1),
		// .QPLL_INIT_CFG(),		// 23:0
		// .QPLL_LOCK_CFG(),		// 15:0
		// .QPLL_LPF(),			//  4:0
		.QPLL_REFCLK_DIV(1)		// integer
		// SIM_QPLLREFCLK_SEL(),	//  2:0
		// SIM_RESET_SPEEDUP = "TRUE";
		// SIM_VERSION = "4.0";
		// }}}
	) u_gtxck (
		// {{{
		// QPLL	Ports
		// {{{
		.QPLLDMONITOR(),		//  7:0 -- IGNORED
		// .QPLLFBCLKLOST(),
		.QPLLLOCK(pll_lock),
		.QPLLLOCKDETCLK(i_wb_clk),
		.QPLLLOCKEN(1'b1),
		.QPLLOUTCLK(qpll_clk),
		// .QPLLREFCLKLOST(),

		// .QPLLOUTREFCLK(),
		// .QPLLOUTRESET(),
		.QPLLPD(1'b0),
		.QPLLREFCLKSEL(3'b001),		//  2:0

		.QPLLRESET(pll_reset),

		.GTREFCLK0(gtx_refck),
		// .GTREFCLK1(),
		.BGBYPASSB(1'b1),
		.BGMONITORENB(1'b1),
		.BGPDB(1'b1),
		.BGRCALOVRD(5'b11111),			//  4:0
		.RCALENB(1'b1),
		.PMARSVD(8'h0),			//  7:0
		// }}}
		.REFCLKOUTMONITOR(),
		.GTGREFCLK(),
		.GTNORTHREFCLK0(),
		.GTNORTHREFCLK1(),
		.GTSOUTHREFCLK0(),
		.GTSOUTHREFCLK1(),
		.QPLLRSVD1(),			// 15:0
		.QPLLRSVD2(),			//  4:0
		// DRP
		// {{{
		.DRPCLK(i_wb_clk),
		.DRPEN(),
		.DRPWE(),
		.DRPADDR(),			//  7:0
		.DRPDI(),			// 15:0
		.DRPDO(),			// 15:0
		.DRPRDY()
		// }}}
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset handling
	// {{{

	always @(posedge i_wb_clk or negedge pll_reset)
	if (!pll_reset)
		{ gtx_reset, gtx_reset_pipe } <= -1;
	else
		{ gtx_reset, gtx_reset_pipe } <= { gtx_reset_pipe, !pll_lock };

	// gtx_tx_reset
	// {{{
	reg	[6:0]	tx_reset_counter;
	reg		gtx_tx_reset, tx_pcs_reset, tx_pma_reset;
	wire		tx_mmcm_locked;

	assign	tx_mmcm_locked = 1'b1;

	initial	tx_reset_counter <= -1;
	always @(posedge i_wb_clk)
	if (gtx_reset || !tx_pcs_reset)
		tx_reset_counter <= -1;
	else
		tx_reset_counter <= tx_reset_counter - 1;

	initial	{ gtx_tx_reset, tx_pma_reset, tx_pcs_reset } <= -1;
	always @(posedge i_wb_clk)
	if (gtx_reset)
		{ gtx_tx_reset, tx_pma_reset, tx_pcs_reset } <= -1;
	else if (tx_reset_counter == 0)
	begin
		if (gtx_tx_reset)
			{ tx_pcs_reset, tx_pma_reset, gtx_tx_reset } <= 3'b110;
		else if (tx_pma_reset)
			{ tx_pcs_reset, tx_pma_reset, gtx_tx_reset } <= 3'b100;
		else if (tx_pcs_reset)
			tx_pcs_reset <= !tx_mmcm_locked;
	end
	// }}}

	// }}}

	generate for(gk=0; gk<NDEV; gk=gk+1)
	begin : GEN_GTX
		// Per port declarations
		// {{{
		wire		gtx_rx_fault;
		reg	[1:0]	rx_fault_pipe;
		reg		r_phy_fault; 
		wire		rx_invalid_alignment_fsm,
				tx_reset_done,
				tx_gearbox_ready,
				ign_txphaligndone,
				ign_txphinitdone,
				ign_qspisenn,
				ign_qspisenp,
				tx_mmcm_locked,	// CONNECT ME!
				ign_comfinish,
				rx_cdr_lock,
				rx_buf_status;
		wire	[1:0]	ign_txbufstatus;
		wire		rxbuf_reset,
				rx_mmcm_locked,
				rx_user_clk_d2, rx_user_clk;
		wire	[7:0]	ign_monitor;
		// }}}

		GTXE2_CHANNEL #(
			// {{{
			.TXGEARBOX_EN("TRUE"),
			.GEARBOX_MODE(3'b011),	// 66/64B gearbox, Internal sequence ctr
			//
			.TX_DATA_WIDTH(64),
			.TX_INT_DATAWIDTH(1),	// Must be 32-bits
			// TX buffer
			.TXBUF_EN("TRUE"),
			.TX_XCLK_SEL("TXOUT"),
			.TXBUF_RESET_ON_RATE_CHANGE("TRUE"),
			// TX Configurable driver control
			// {{{
			.TX_DEEMPH0(5'b00000),
			.TX_DEEMPH1(5'b00000),
			.TX_MAINCURSOR_SEL(1'b0),
			.TX_DRIVE_MODE("DIRECT"),
			.TX_MARGIN_FULL_0(7'b100_1110),
			.TX_MARGIN_FULL_1(7'b100_1001),
			.TX_MARGIN_FULL_2(7'b100_0101),
			.TX_MARGIN_FULL_3(7'b100_0010),
			.TX_MARGIN_FULL_4(7'b100_0000),
			.TX_MARGIN_LOW_0(7'b100_0110),
			.TX_MARGIN_LOW_1(7'b100_0100),
			.TX_MARGIN_LOW_2(7'b100_0010),
			.TX_MARGIN_LOW_3(7'b100_0000),
			.TX_MARGIN_LOW_4(7'b100_0000),
			.TX_PREDRIVER_MODE(1'b0),
			.TX_QPI_STATUS_EN(1'b0),
			.TX_EIDLE_ASSERT_DELAY(3'b110),
			.TX_EIDLE_DEASSERT_DELAY(3'b100),
			.TX_LOOPBACK_DRIVE_HIZ("FALSE"),
			// }}}
			// RX termination control
			// {{{
			// RX termination voltage selection
			//	2'b00 selects AVTT
			//	2'b01 selects GND
			//	2'b10 selects floating
			//	2'b11 selects programmable ... 800mV recommended
			.RX_CM_SEL(2'b11),
			.RX_CM_TRIM(3'b010),
			// }}}
			// RX OOB (unused)
			// {{{
			.RXOOB_CFG(7'b000_0110),
			.SATA_BURST_SEQ_LEN(4'b0101),
			.SATA_BURST_VAL(3'b100),
			.SATA_CPLL_CFG("VCO_3000MHZ"),
			.SATA_EIDLE_VAL(3'b100),
			.SAS_MIN_COM(36),
			.SAS_MAX_COM(64),
			.SATA_MIN_INIT(12),
			.SATA_MAX_INIT(21),
			.SATA_MIN_BURST(4),
			.SATA_MAX_BURST(4),
			.SATA_MIN_WAKE(4),
			.SATA_MAX_WAKE(7),
			// }}}
			// RX Equalizer
			// {{{
			.RX_OS_CFG(13'h0080),
			.RXLPM_LF_CFG(14'h00f0),
			.RXLPM_HF_CFG(14'h00f0),
			.RX_DFE_LPM_CFG(16'h0954),
			.RX_DFE_GAIN_CFG(23'h20fea),
			.RX_DFE_H2_CFG(12'h000),
			.RX_DFE_H3_CFG(12'h040),
			.RX_DFE_H4_CFG(11'h0f0),
			.RX_DFE_H5_CFG(11'h0e0),
			.PMA_RSV(32'h01e_7080),
			.RX_DFE_LPM_HOLD_DURING_EIDLE(1'b0),
			.RX_DFE_XYD_CFG(13'h00),
			.RX_BIAS_CFG(12'h04),
			.RX_DEBUG_CFG(12'h0),
			.RX_DFE_KL_CFG(13'hfe),
			.RX_DFE_KL_CFG2(32'h301148ac),
			.RX_DFE_UT_CFG(17'h11e00),
			.RX_DFE_VP_CFG(17'h03f03),
			//
			.PMA_RSV2(16'h2050),
			.PMA_RSV3(2'b00),
			.PMA_RSV4(32'h0000_0000),
			.RXDFELPMRESET_TIME(7'b000_1111),
			// }}}
			// RX CDR (Clock/data recovery)
			// {{{
			.RXCDR_CFG(72'h0b_0000_23ff_1040_0020),
			.RXCDR_LOCK_CFG(6'b010101),
			.RXCDR_HOLD_DURING_EIDLE(1'b0),
			.RXCDR_FR_RESET_ON_EIDLE(1'b0),
			.RXCDR_PH_RESET_ON_EIDLE(1'b0),
			.RXCDRFREQRESET_TIME(5'h1),
			.RXCDRPHRESET_TIME(5'h1),
			// }}}
			// RX fabric clock output control
			// {{{
			.RXOUT_DIV(1),
			// }}}
			// RX Byte alignment
			// {{{
			.ALIGN_COMMA_DOUBLE("FALSE"),
			.ALIGN_COMMA_ENABLE(10'b11_1111_1111),
			.ALIGN_COMMA_WORD(1),
			.ALIGN_MCOMMA_DET("FALSE"),
			.ALIGN_MCOMMA_VALUE(10'b10_1000_0011),
			.ALIGN_PCOMMA_DET("FALSE"),
			.ALIGN_PCOMMA_VALUE(10'b01_0111_1100),
			.RXSLIDE_AUTO_WAIT(7),
			.RXSLIDE_MODE("OFF"),
			.SHOW_REALIGN_COMMA("FALSE"),
			// }}}
			// RX 8B10B decoder
			// {{{
			.RX_DISPERR_SEQ_MATCH("FALSE"),
			.DEC_MCOMMA_DETECT("FALSE"),
			.DEC_PCOMMA_DETECT("FALSE"),
			.DEC_VALID_COMMA_ONLY("FALSE"),
			.UCODEER_CLR(1'b0),		// Reserved
			// }}}
			// RX Buffer Bypass
			// {{{
			.RXBUF_EN("TRUE"),
			.RX_XCLK_SEL("RXREC"),
			.RX_DEFER_RESET_BUF_EN("FALSE"),
			.RX_BUFFER_CFG(6'h00),
			.RXPH_CFG(24'h0000),
			.RXPH_MONITOR_SEL(5'h00),
			.RXDLY_CFG(16'h001f),
			.RXDLY_LCFG(9'h030),
			.RXDLY_TAP_CFG(16'h000),
			.RX_DDI_SEL(6'h00),
			.RXBUF_ADDR_MODE("FAST"),
			.RXBUF_EIDLE_HI_CNT(4'b1000),
			.RXBUF_EIDLE_LO_CNT(4'b0000),
			.RXBUF_RESET_ON_CB_CHANGE("TRUE"),
			.RXBUF_RESET_ON_COMMAALIGN("FALSE"),
			.RXBUF_RESET_ON_EIDLE("FALSE"),
			.RXBUF_RESET_ON_RATE_CHANGE("TRUE"),
			.RXBUF_THRESH_OVFLW(61),	// Reserved
			.RXBUF_THRESH_OVRD("FALSE"),
			.RXBUF_THRESH_UNDFLW(4),	// Reserved
			.RXBUFRESET_TIME(5'b00001),	// Reserved
			// }}}
			// RX Clock correction
			// {{{
			.CBCC_DATA_SOURCE_SEL("ENCODED"),
			.CLK_CORRECT_USE("FALSE"),
			.CLK_COR_MAX_LAT(19),
			.CLK_COR_MIN_LAT(15),
			.CLK_COR_PRECEDENCE("TRUE"),
			.CLK_COR_REPEAT_WAIT(0),
			.CLK_COR_SEQ_1_1(10'b01_0000_0000),
			.CLK_COR_SEQ_1_2(10'b00_0000_0000),
			.CLK_COR_SEQ_1_3(10'b00_0000_0000),
			.CLK_COR_SEQ_1_4(10'b00_0000_0000),
			.CLK_COR_SEQ_1_ENABLE(4'b1111),
			.CLK_COR_SEQ_2_1(10'b01_0000_0000),
			.CLK_COR_SEQ_2_2(10'b00_0000_0000),
			.CLK_COR_SEQ_2_3(10'b00_0000_0000),
			.CLK_COR_SEQ_2_4(10'b00_0000_0000),
			.CLK_COR_SEQ_2_ENABLE(4'b1111),
			.CLK_COR_SEQ_2_USE("FALSE"),
			.CLK_COR_SEQ_LEN(1),
			.CLK_COR_KEEP_IDLE("FALSE"),
			// }}}
			// RX Channel bonding
			// {{{
			.CHAN_BOND_MAX_SKEW(1),
			.CHAN_BOND_KEEP_ALIGN("FALSE"),
			//
			.CHAN_BOND_SEQ_1_ENABLE(4'b1111),
			.CHAN_BOND_SEQ_1_1(10'b00_0000_0000),
			.CHAN_BOND_SEQ_1_2(10'b00_0000_0000),
			.CHAN_BOND_SEQ_1_3(10'b00_0000_0000),
			.CHAN_BOND_SEQ_1_4(10'b00_0000_0000),
			//
			.CHAN_BOND_SEQ_2_ENABLE(4'b1111),
			.CHAN_BOND_SEQ_2_1(10'b00_0000_0000),
			.CHAN_BOND_SEQ_2_2(10'b00_0000_0000),
			.CHAN_BOND_SEQ_2_3(10'b00_0000_0000),
			.CHAN_BOND_SEQ_2_4(10'b00_0000_0000),
			.CHAN_BOND_SEQ_2_USE("FALSE"),
			.CHAN_BOND_SEQ_LEN(1),
			//
			.FTS_DESKEW_SEQ_ENABLE(4'b1111),
			.FTS_LANE_DESKEW_CFG(4'b1111),
			.FTS_LANE_DESKEW_EN("FALSE"),
			.PCS_PCIE_EN("FALSE"),
			// }}}
			// RX Gearbox
			// {{{
			.RXGEARBOX_EN("TRUE"),
			// }}}
			.CPLL_CFG(24'hbc07dc),
			.CPLL_FBDIV(4),
			.CPLL_FBDIV_45(5),
			.CPLL_INIT_CFG(24'h001e),
			.CPLL_LOCK_CFG(16'h01e8),
			.CPLL_REFCLK_DIV(1),
			.DMONITOR_CFG(24'h00a00),
			.ES_CONTROL(6'b00_0000),
			.ES_ERRDET_EN("FALSE"),
			.ES_EYE_SCAN_EN("TRUE"),
			.ES_HORZ_OFFSET(12'h00),
			.ES_PMA_CFG(10'b00_0000_0000),
			.ES_PRESCALE(5'b00000),
			.ES_QUALIFIER(80'h00000000000000000000),
			.ES_QUAL_MASK(80'h00000000000000000000),
			.ES_SDATA_MASK(80'h00000000000000000000),
			.ES_VERT_OFFSET(9'h000),
			.IS_CPLLLOCKDETCLK_INVERTED(),
			.IS_DRPCLK_INVERTED(),
			.IS_GTGREFCLK_INVERTED(),
			.IS_RXUSRCLK2_INVERTED(),
			.IS_RXUSRCLK_INVERTED(),
			.IS_TXPHDLYTSTCLK_INVERTED(),
			.IS_TXUSRCLK2_INVERTED(),
			.IS_TXUSRCLK_INVERTED(),
			.OUTREFCLK_SEL_INV(2'b11),
			.PCS_RSVD_ATTR(48'h0),
			.PD_TRANS_TIME_FROM_P2(12'h03c),
			.PD_TRANS_TIME_NONE_P2(8'h19),
			.PD_TRANS_TIME_TO_P2(8'h64),
			.RXISCANRESET_TIME(),
			.RXPCSRESET_TIME(),
			.RXPHDLY_CFG(24'h084020),
			.RXPMARESET_TIME(),
			.RX_CLK25_DIV(7),
			.RX_CLKMUX_PD(1'b1),
			.RX_DATA_WIDTH(64),
			.RX_INT_DATAWIDTH(1),	// Must be 32-bits
			.RX_SIG_VALID_DLY(10),
			.SIM_CPLLREFCLK_SEL(3'b001),
			.SIM_RECEIVER_DETECT_PASS("TRUE"),
			.SIM_RESET_SPEEDUP("FALSE"),
			.SIM_TX_EIDLE_DRIVE_LEVEL("X"),
			.SIM_VERSION("4.0"),
			.TRANS_TIME_RATE(8'h0e),
			.TST_RSV(32'h0),
			.TXOUT_DIV(1),
			.TXPCSRESET_TIME(5'b00001),
			.TXPMARESET_TIME(5'b00001),
			.TX_CLK25_DIV(7),
			.TX_CLKMUX_PD(1'b1),
			// Unused configuration parameters
			// {{{
			.TXPHDLY_CFG(24'h084020),
			.TXPH_CFG(16'h0780),
			.TXPH_MONITOR_SEL(5'b00),
			.TXDLY_CFG(16'h001f),
			.TXDLY_LCFG(9'h030),
			.TXDLY_TAP_CFG(16'h00),
			.RXPRBS_ERR_LOOPBACK(1'b0),
			.TX_RXDETECT_CFG(14'h1832),
			.TX_RXDETECT_REF(3'b100),
			//
			.TERM_RCAL_CFG(5'h10),	// Should be set to Transceiver Wiz val
			.TERM_RCAL_OVRD(1'b0)
			// }}}
			// }}}
		) u_xgtx (
			// {{{
			.CPLLFBCLKLOST(),
			.CPLLLOCK(),
			.CPLLREFCLKLOST(),
			.GTREFCLKMONITOR(),
			.PHYSTATUS(),
			.RXPHALIGNDONE(),
			.RXSTARTOFSEQ(),
			.RXVALID(),	// Ignore (bc we are using the gearbox)
			.RXSTATUS(),
			.TSTOUT(),
			.CFGRESET(),
			.CPLLLOCKDETCLK(1'b0),
			.CPLLLOCKEN(1'b1),
			.CPLLPD(1'b1),
			.CPLLRESET(1'b0),
			.GTGREFCLK(1'b0),
			.GTNORTHREFCLK0(1'b0),
			.GTNORTHREFCLK1(1'b0),
			.GTREFCLK0(1'b0),
			.GTREFCLK1(1'b0),
			.GTRESETSEL(1'b0),	// Sequential reset mode
			.GTSOUTHREFCLK0(1'b0),
			.GTSOUTHREFCLK1(1'b0),
			.QPLLCLK(qpll_clk),
			.QPLLREFCLK(gtx_refck),
			.RESETOVRD(),
			.TSTIN(20'hf_ffff),
			.CPLLREFCLKSEL(),
			// IO Pads/Pins
			// {{{
			.GTTXRESET(gtx_tx_reset),
			.GTXTXP(o_tx_p[gk]),
			.GTXTXN(o_tx_n[gk]),
			//
			.GTRXRESET(gtx_reset),
			.GTXRXP(i_rx_p[gk]),
			.GTXRXN(i_rx_n[gk]),
			.RXQPIEN(1'b0),		// Disable sense outputs
			// .RXQPISENN(),	// Sense output on pads (unused here)
			// .RXQPISENP(),
			// }}}
			// TX Control
			// {{{
			.TXPMARESET(tx_pma_reset),	// Input
			.TXPCSRESET(tx_pcs_reset),	// Input
			.TXPHDLYRESET(),
			.TXDLYSRESET(),
			.TXRESETDONE(tx_reset_done),
			//
			.TXOUTCLK(),		// Clock to fabric
			.TXUSRCLK2(unbuf_tx_clk[gk]),	// Returned clocks w/ data clocks
			.TXUSRCLK(),
			.TXHEADER({ 1'b0, S_DATA[1:0] }),
			.TXDATA(S_DATA[65:2]),
			.TXGEARBOXREADY(tx_gearbox_ready),
			//
			.TXSEQUENCE(),		// LOOK ME UP!
			.TXSTARTSEQ(1'b1),	// First valid byte of first sequence
			//

			.TXRATEDONE(),

			// TX Buffer Bypass / Phase alignment circuit control
			// {{{
			.TXDLYBYPASS(1'b1),
			.TXPHALIGNDONE(ign_txphaligndone),
			.TXPHINITDONE(ign_txphinitdone),
			.TXPHDLYTSTCLK(),
			.TXPHALIGN(1'b0),
			.TXPHALIGNEN(1'b0),
			.TXPHDLYPD(1'b1),
			.TXPHINIT(1'b0),
			.TXPHOVRDEN(1'b0),
			.TXDLYEN(1'b0),
			.TXDLYHOLD(1'b0),
			.TXDLYOVRDEN(1'b0),
			.TXDLYUPDOWN(1'b0),
			.TXDLYSRESETDONE(),
			// }}}
			// TX Configurable driver
			// {{{
			.TXBUFDIFFCTRL(3'b100),		//
			// .TXDEEMPH(),			// ???
			// .TXDIFFCTRL(),			// ???
			.TXELECIDLE(1'b0),
			.TXINHIBIT(1'b0),
			.TXMAINCURSOR(7'h0),		// Unused (I hope)
			// .TXMARGIN(),			// ???
			.TXQPIBIASEN(1'b0),
			.TXQPISTRONGPDOWN(1'b0),
			.TXQPIWEAKPUP(1'b0),
			.TXQPISENN(ign_qspisenn),
			.TXQPISENP(ign_qspisenp),
			// .TXPOSTCURSOR(),		// ???
			.TXPOSTCURSORINV(1'b0),
			// .TXPRECURSOR(),
			// .TXPRECURSORINV(),
			.TXSWING(1'b1),			// Full swing
			.TXDIFFPD(1'b0),		// Reserved
			.TXPISOPD(1'b0),		// Reserved
			// }}}
			.TXUSERRDY(tx_mmcm_locked),
			.TXSYSCLKSEL(2'b11),
			.TXOUTCLKSEL(),
			.TXRATE(),
			.TX8B10BBYPASS(),
			// Constants
			// {{{
			.TX8B10BEN(1'b0),		// Disable the 8B10B encoder
			.TXCHARDISPMODE(8'h0),
			.TXCHARDISPVAL(8'h0),
			.TXCHARISK(8'h0),
			//
			.TXPOLARITY(1'b0),	// Normal polarity
			// PRBS
			// {{{
			.TXPRBSSEL(3'b0),	// Standard operation
			.TXPRBSFORCEERR(1'b0),
			// }}}
			.TXDETECTRX(1'b0),	// Normal operation
			.TXPDELECIDLEMODE(1'b1),
			.TXPD(2'b00),		// Normal operation
			// }}}
			// Unused
			// {{{
			.TXCOMFINISH(ign_comfinish),
			.TXCOMINIT(1'b0),
			.TXCOMSAS(1'b0),
			.TXCOMWAKE(1'b0),
			.TXBUFSTATUS(ign_txbufstatus[1:0]),
			.TXOUTCLKFABRIC(),	// Redundant.  Don't use in new designs
			.TXOUTCLKPCS(),		// Redundant.  Don't use in new designs
			// }}}
			// }}}
			// RX Control
			// {{{
			.RXPCSRESET(),
			.RXBUFRESET(rxbuf_reset),		// TODO
			.RXUSERRDY(rx_mmcm_locked),
			.RXRESETDONE(),
			.RXPMARESET(),
			.RXPD(2'b00),		// Normal operation
			.RXUSRCLK2(rx_user_clk_d2),
			.RXUSRCLK(rx_user_clk),
			.RXSYSCLKSEL(2'b11),		// FIXME / checkme
			// .RXPMARESETDONE(),
			// RX Margin analysis
			// {{{
			.EYESCANTRIGGER(1'b0),
			.EYESCANDATAERROR(),
			.EYESCANMODE(1'b0),
			// }}}
			// Equalizer/DFE config
			// {{{
			.RXLPMEN(1'b0),
			.RXDFELPMRESET(gtx_reset),
			.RXOSHOLD(2'b00),
			.RXOSOVRDEN(2'b00),
			//
			.RXLPMLFHOLD(2'b00),
			.RXLPMLFKLOVRDEN(2'b00),
			//
			.RXLPMHFHOLD(2'b00),
			.RXLPMHFOVRDEN(2'b00),
			.RXDFELFHOLD(2'b00),
			.RXDFELFOVRDEN(2'b00),
			.RXDFEAGCHOLD(2'b0),
			.RXDFEAGCOVRDEN(2'b0),
			.RXDFEUTHOLD(2'b00),
			.RXDFEUTOVRDEN(2'b00),
			.RXDFEVPHOLD(2'b00),
			.RXDFEVPOVRDEN(2'b00),
			.RXDFETAP2HOLD(2'b00),
			.RXDFETAP2OVRDEN(2'b00),
			.RXDFETAP3HOLD(2'b00),
			.RXDFETAP3OVRDEN(2'b00),
			.RXDFETAP4HOLD(2'b00),
			.RXDFETAP4OVRDEN(2'b00),
			.RXDFETAP5HOLD(2'b00),
			.RXDFETAP5OVRDEN(2'b00),
			//
			.RXDFECM1EN(),
			.RXDFEVSEN(),
			.RXDFEXYDEN(1'b1),
			.RXDFEXYDHOLD(1'b0),		// Reserved
			.RXDFEXYDOVRDEN(1'b0),		// Reserved
			// .RXMONITORSEL(),
			// .RXMONITOROUT(),		// Ignore/reserved
			// }}}
			// RX Clock data recovery (CDR)
			// {{{
			.RXCDRFREQRESET(1'b0),
			.RXCDRHOLD(1'b0),
			.RXCDROVRDEN(1'b1),		// Tie to ground??
			.RXCDRRESET(1'b0),
			.RXCDRRESETRSV(1'b0),
			.RXRATE(2'b00),			// ???	FIXME
			.RXCDRLOCK(rx_cdr_lock),
			// }}}
			// RX fabric clock output control
			// {{{
			.RXOUTCLKSEL(3'b011),		// FIXME!!
			.RXOUTCLKFABRIC(),	// Redundant output -- ignore this
			.RXOUTCLK(unbuf_rx_clk[gk]),	// RX clock to fabric
			// .RXOUTCLKPCS(),	// Redundant output -- ignore this
			// .RXRATEDONE(ign_rx_rate_done),
			.RXDLYBYPASS(1'b1),		// Set to 1 when buffer is used
			// }}}
			// RX Polarity control
			// {{{
			.RXPOLARITY(1'b0),
			// }}}
			// RX Pattern checker
			// {{{
			.RXPRBSCNTRESET(1'b0),
			.RXPRBSSEL(3'b000),		// Turns PRBS off
			.RXPRBSERR(),		// (out) PRBS errors have occurred (ign)
			// }}}
			// RX Byte and word alignment
			// {{{
			.RXCOMMADETEN(1'b0),	// Enable comma detection ?
			.RXMCOMMAALIGNEN(1'b0),
			.RXPCOMMAALIGNEN(1'b0),
			.RXSLIDE(1'b0),
			// outputs ...
			.RXBYTEISALIGNED(),	// True (out) if comma aligned
			.RXBYTEREALIGN(),	// (out) Byte alignment has changed
			.RXCOMMADET(),
			// }}}
			// RX 8B10B decoder
			// {{{
			.RX8B10BEN(1'b0),
			.SETERRSTATUS(1'b0),
			// outputs
			.RXNOTINTABLE(),
			.RXCHARISCOMMA(),
			.RXCHARISK(),
			.RXDISPERR(),
			// }}}
			// RX Buffer Bypass
			// {{{
			.RXDLYEN(),
			.RXDLYOVRDEN(),
			.RXDLYSRESET(),
			.RXPHOVRDEN(1'b0),
			.RXPHALIGN(),
			.RXPHALIGNEN(),
			.RXPHDLYPD(),
			.RXPHMONITOR(),
			.RXPHSLIPMONITOR(),
			.RXDLYSRESETDONE(),
			.RXDDIEN(),
			.RXPHDLYRESET(),
			// Outputs
			.RXBUFSTATUS(rx_buf_status),
			// }}}
			// RX Clock correction
			// {{{
			.RXCLKCORCNT(),
			// }}}
			// RX Channel bonding
			// {{{
			.RXCHBONDEN(1'b0),
			.RXCHBONDMASTER(1'b1),
			.RXCHBONDSLAVE(1'b0),
			.RXCHBONDLEVEL(0),
			.RXCHBONDI(),
			// Outputs
			.RXCHBONDO(),
			.RXCHANBONDSEQ(),
			.RXCHANISALIGNED(),
			.RXCHANREALIGN(),
			// }}}
			// RX Gearbox
			// {{{
			.RXDATAVALID(M_VALID[gk]),
			.RXGEARBOXSLIP(rx_invalid_alignment_fsm),
			.RXHEADER(M_DATA[gk*66 +: 2]),
			.RXDATA(M_DATA[gk*66 + 2 +: 64]),
			.RXHEADERVALID(),	// Is this the same as M_VALID ???
			// }}}
			// Constants
			// {{{
			.RXELECIDLEMODE(2'b11),	// Not using RXELECIDLE
			// }}}
			// Unused
			// {{{
			// OOB
			.RXOOBRESET(1'b0),
			// .RXELECIDLE(),
			// .RXCOMSASDET(),
			// .RXCOMWAKEDET(),
			// .RXCOMINITDET(),
			// }}}
			// }}}
			// DRP -- FIXME
			// {{{
			.DRPCLK(i_wb_clk),	// = wb_clk
			.DRPEN(1'b0),	// Strobe signal, = wb_stb && !wb_stall
			.DRPWE(),	// Write enable = wb_stb && !wb_stall && wb_we
			.DRPADDR(8'h0),
			.DRPDI(15'h0),	// Input data, valid when wb_stb && !wb_we
			.DRPDO(),	// Output data, valid when DRPRDY
			.DRPRDY(),	// wb_ack: Dat vld for read ops, wr complete o/w
			// }}}
			// Other unused
			// {{{
			.LOOPBACK(3'b000),	// Normal operation
			.DMONITOROUT(ign_monitor),	// 8b ignore
			.PCSRSVDOUT(),
			.GTRSVD(16'h0),
			.PCSRSVDIN(16'b0),
			.CLKRSVD(4'b0),
			.PCSRSVDIN2(5'h0),
			.PMARSVDIN(5'h0),
			.PMARSVDIN2(5'h0),
			.EYESCANRESET()
			// }}}
			// }}}
		);

		// MMCM
		// {{{
		//	TXOUTCLK -> BUFG -> MMCM -> TXUSRCLK2		-> BUFG
		//					TXUSRCLK	-> BUFG
		//	TXUSRCLK2 = TXUSRCLK / 2
		//		Since TX_INT_DATA_WIDTH=1, required for high speed
		//		or other 8-byte modes
		// }}}

		assign	S_READY[gk] = tx_reset_done && tx_gearbox_ready;

		assign	gtx_rx_fault = gtx_reset || !rx_cdr_lock;

		always @(posedge M_CLK[gk] or posedge gtx_rx_fault)
		if (gtx_rx_fault)
			{ r_phy_fault, rx_fault_pipe } <= -1;
		else
			{ r_phy_fault, rx_fault_pipe } <= { rx_fault_pipe, 1'b0 };

		assign	o_phy_fault[gk] = r_phy_fault;

		BUFG rxbuf(.I(unbuf_rx_clk[gk]), .O(M_CLK[gk]));
		BUFG txbuf(.I(unbuf_tx_clk[gk]), .O(S_CLK[gk]));
	end endgenerate
endmodule
