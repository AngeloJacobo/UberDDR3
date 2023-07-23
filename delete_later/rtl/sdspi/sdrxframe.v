////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdrxframe.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Process incoming data from the front end.  Data will come in
//		on (potentially) every edge of DS.  We need to turn it here
//	into one data stream for each IO pin, check the CRC on each data
//	stream, and then compose the results into (up to) 32-bits per clock
//	cycle to be written to the SRAM on an outgoing stream.
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
module	sdrxframe #(
		// {{{
		parameter	LGLEN = 15, NUMIO=4,
		parameter	MW = 32,
		localparam	LGLENW = LGLEN-$clog2(MW/8),
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_DS = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter	LGTIMEOUT = 23	// 8 of slowest clock cycle
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_cfg_ds, i_cfg_ddr,
		input	wire	[1:0]		i_cfg_width,
		//
		input	wire			i_rx_en,
		input	wire			i_crc_en,
		input	wire	[LGLEN:0]	i_length,	// In bytes
		//
		input	wire	[1:0]		i_rx_strb,
		input	wire	[15:0]		i_rx_data,

		input	wire			S_ASYNC_VALID,
		input	wire	[31:0]		S_ASYNC_DATA,

		output	wire			o_mem_valid,
		output	wire	[MW/8-1:0]	o_mem_strb,
		output	wire	[LGLENW-1:0]	o_mem_addr,	// Word address
		output	wire	[MW-1:0]	o_mem_data,	// Outgoing data

		output	reg			o_done,
		output	reg			o_err
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[1:0]	WIDTH_1W = 2'b00,
				WIDTH_4W = 2'b01,
				// Verilator lint_off UNUSED
				WIDTH_8W = 2'b10;
				// Verilator lint_on  UNUSED

	localparam	NCRC = 16;
	localparam	[NCRC-1:0]	CRC_POLYNOMIAL = 16'h1021;
	genvar	gk;

	reg	[4:0]	sync_fill;
	reg	[19:0]	sync_sreg;

	reg		s2_valid;
	reg	[1:0]	s2_fill;
	reg	[15:0]	s2_data;

	reg				mem_valid, mem_full, rnxt_strb;
	reg	[MW/8-1:0]		mem_strb;
	reg	[MW-1:0]		mem_data;
	reg	[LGLENW-1:0]		mem_addr;
	reg	[$clog2(MW/8)-1:0]	subaddr, next_subaddr;
	reg	[7:0]			rnxt_data;

	reg			busy, data_phase, load_crc, pending_crc;
	reg	[LGLEN+4-1:0]	rail_count;

	wire	[NUMIO*2-1:0]	err;

	reg	[LGTIMEOUT-1:0]	r_timeout;
	reg			r_watchdog;

	reg	last_strb;
	reg	w_done;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Notes:
	// {{{
	// Two channels of processing:
	//	 Sync processing: (No data strobe)
	//	0. The PHY will sample data a fixed distance from each clk edge
	//		That means it will always be sampling, whether or not
	//		we're expecting something.
	//	1. Wait for the enable
	//	2. Wait for the start bit: (S_VALID && S_DATA != 8'hff)
	//	3. Capture every S_VALID, and realign incoming bits
	//	4. Move to stage #2
	//
	//	Async processing: (w/ data strobe)
	//	0. The PHY will detect DS edges for us, and provide data
	//		VALID, (READY *MUST* be true), DATA, STRB
	//	1. Pack data into M_VALID, 32bits of M_DATA, M_LAST
	//	2. Move to stage #2
	//
	// Stage #2
	//	1. Calculate CRC on each of the 8 channels
	//	2. Generate error on failed CRC, failed start, or failed stop
	//	3. Drop unused data paths
	//
	// Potential errors:
	//	Start bits not aligned
	//	Stop bits not aligned, or not at the right place
	//	Failed CRC on a data bit we are using
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronous (no DS) data path
	// {{{

	// Step #1: Bit sync
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (i_cfg_ds && OPT_DS) || !data_phase)
		sync_fill <= 0;
	else if (i_rx_strb == 0)
	begin
		sync_fill[4:3] <= 2'b0;
	// Verilator lint_off WIDTH
	end else case(i_cfg_width)
	WIDTH_1W: sync_fill <= sync_fill[2:0] + (i_rx_strb[1] ? 1:0)
						+ (i_rx_strb[0] ? 1:0);
	WIDTH_4W: sync_fill <= sync_fill[2:0] + (i_rx_strb[1] ? 4:0)
						+ (i_rx_strb[0] ? 4:0);
	default:  sync_fill <= sync_fill[2:0] + (i_rx_strb[1] ? 8:0)
						+ (i_rx_strb[0] ? 8:0);
	endcase
	// Verilator lint_on  WIDTH

	always @(posedge i_clk)
	if (!i_rx_en)
		sync_sreg <= 0;
	else if (i_rx_strb != 0)
	begin
		case(i_cfg_width)
		WIDTH_1W: if (i_rx_strb == 2'b11)
			sync_sreg <= { sync_sreg[17:0], i_rx_data[8], i_rx_data[0] };
			else if (i_rx_strb[1])
				sync_sreg <= { sync_sreg[18:0], i_rx_data[8] };
			else
				sync_sreg <= { sync_sreg[18:0], i_rx_data[0] };
		WIDTH_4W: if (i_rx_strb == 2'b11)
			sync_sreg <= { sync_sreg[11:0], i_rx_data[11:8], i_rx_data[3:0] };
			else if (i_rx_strb[1])
				sync_sreg <= { sync_sreg[15:0], i_rx_data[11:8] };
			else
				sync_sreg <= { sync_sreg[15:0], i_rx_data[3:0] };
		default: if (i_rx_strb == 2'b11)
			sync_sreg <= { sync_sreg[3:0], i_rx_data[15:8], i_rx_data[7:0] };
			else if (i_rx_strb[1])
				sync_sreg <= { sync_sreg[11:0], i_rx_data[15:8] };
			else
				sync_sreg <= { sync_sreg[11:0], i_rx_data[7:0] };
		endcase
	end
	// }}}

	// Step #2: Byte sync: s2_valid, s2_fill (byte count), and s2_data
	// {{{
	// We assume this register gets fully and completely emptied on every
	// cycle, so we only have to capture what spills out from the sync_*
	// registers.
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (i_cfg_ds && OPT_DS))
		// If RX is not enabled, or
		//   or we haven't seen the sync bit(s)
		//   or we are using the async path,
		// Then keep s2 disabled
		s2_valid <= 0;
	else
		s2_valid <= (sync_fill >= 8);

	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (i_cfg_ds && OPT_DS))
		s2_fill <= 0;
	else
		s2_fill <= sync_fill[4:3];

	// Verilator lint_off WIDTH
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (!i_rx_en || (i_cfg_ds && OPT_DS)))
		s2_data <= 0;
	else if (sync_fill[4])
		s2_data <= sync_sreg >> sync_fill[2:0];
	else if (sync_fill[3])
		s2_data <= {sync_sreg, 8'h0} >> sync_fill[2:0];
	// Verilator lint_on  WIDTH
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Asynchronous (w/ DS) data path
	// {{{

	// Nothing really more needs to be done.  The async path comes in at
	// 4bytes at a times, all four valid (presently), and needs to be
	// synchronized to a 4-byte stream w/ all four valid.  Of course, this
	// will only work as long as the DS strobe signals only ever arrive
	// in pairs of pulses.

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Align, and write to (external) memory
	// {{{
	// (Memory is just external to this module, not necessarily to the chip)
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_mem_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || mem_full || r_watchdog
			|| (mem_valid && (&mem_addr) && mem_strb[0]))
		mem_valid <= 0;
	else if (!i_cfg_ds || !OPT_DS)
	begin
		mem_valid <= s2_valid || rnxt_strb;
	end else begin
		mem_valid <= S_ASYNC_VALID && data_phase;
	end

	always @(posedge i_clk)
	if (i_reset || !i_rx_en)
		mem_full <= 0;
	else if (mem_valid && (&mem_addr) && mem_strb[0])
		mem_full <= 1;

	assign	o_mem_valid = mem_valid;
	// }}}

	// o_mem_addr
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || mem_full
			|| (mem_valid && (&mem_addr) && mem_strb[0]))
		next_subaddr <= 0;
	else if (!i_cfg_ds || !OPT_DS)
		next_subaddr <= next_subaddr + s2_fill;
	// else if (S_ASYNC_VALID)
	//	next_subaddr <= next_subaddr + 4;
	else
		next_subaddr <= subaddr;

	always @(posedge i_clk)
	if (i_reset || !i_rx_en)
		{ mem_addr, subaddr } <= 0;
	else if (o_mem_valid)
	begin
		// Verilator lint_off WIDTH
		{ mem_addr, subaddr } <= { mem_addr, subaddr } + COUNTONES(o_mem_strb);
		// Verilator lint_on  WIDTH
	end

	assign	o_mem_addr  = mem_addr;
	// }}}

	// o_mem_data, o_mem_strb
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || mem_full)
	begin
		mem_data <= 0;
		mem_strb <= 0;
		rnxt_data <= 0;
		rnxt_strb <= 0;
	end else if (!i_cfg_ds || !OPT_DS)
	begin

		if (s2_fill[1])
		begin
			{ mem_data, rnxt_data } <= { rnxt_data, {(MW){1'b0}} }
				|({ s2_data[15:0], {(MW-8){1'b0}} } >> (next_subaddr*8));
			{ mem_strb, rnxt_strb } <= { rnxt_strb, {(MW/8){1'b0}} }
				|({ 2'b11, {(MW/8-1){1'b0}} } >> (next_subaddr));
		end else if (s2_fill[0])
		begin
			{ mem_data, rnxt_data } <= {rnxt_data, {(MW){1'b0}} }
				|({ s2_data[15:8], {(MW){1'b0}} } >> (next_subaddr*8));
			{ mem_strb, rnxt_strb } <= { rnxt_strb, {(MW/8){1'b0}} }
				|({ s2_fill[0],{(MW/8){1'b0}} }>> next_subaddr);
		end else begin
			{ mem_data, rnxt_data } <= {rnxt_data,{(MW  ){1'b0}} };
			{ mem_strb, rnxt_strb } <= {rnxt_strb,{(MW/8){1'b0}} };
		end
	end else begin
		rnxt_data <= 0;
		rnxt_strb <= 0;
		mem_strb <= 0;

		if (S_ASYNC_VALID)
		begin
			mem_data <= { S_ASYNC_DATA, {(MW-32){1'b0}} } >> (next_subaddr*8);
			mem_strb <= { 4'hf, {(MW/8-4){1'b0}} } >> (next_subaddr);
		end
	end

	generate if (OPT_LITTLE_ENDIAN)
	begin : GEN_LIL_ENDIAN_SWAP
		reg	[MW/8-1:0]	swap_strb;
		reg	[MW-1:0]	swap_data;
		integer			ik;

		always @(*)
		for(ik=0; ik<MW/8; ik=ik+1)
		begin
			swap_strb[ik] = mem_strb[MW/8-1-ik];
			swap_data[ik*8 +: 8] = mem_strb[MW-ik*8 +: 8];
		end

		assign	o_mem_strb  = swap_strb;
		assign	o_mem_data  = swap_data;
	end else begin : NO_ENDIAN_SWAP
		assign	o_mem_strb  = mem_strb;
		assign	o_mem_data  = mem_data;
	end endgenerate
`ifdef	FORMAL
	always @(posedge i_clk)
	if (!i_reset && i_rx_en)
	begin
		if (i_cfg_ds && OPT_DS)
		begin
			assert(rnxt_strb == 0);
			assert(rnxt_data == 0);
		end else if (rnxt_strb)
		begin
			assert(next_subaddr == 1);
		end else
			assert(rnxt_data == 0);
	end
`endif
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Are we done?  Have we received a full packet?
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (i_reset || o_done || !i_rx_en)
	begin
		rail_count <= 0;
		load_crc   <= 0;
		data_phase <= 0;
		last_strb  <= 0;
	end else if (!busy && i_rx_en)
	begin
		// {{{
		// Verilator lint_off WIDTH
		last_strb  <= (!i_crc_en && i_cfg_width == WIDTH_8W && i_length == 1);
		if (i_cfg_ds)
			rail_count <= i_length + (i_crc_en ? (16 + (i_cfg_ddr ? 16 : 0)) : 0);
		else case(i_cfg_width)
		WIDTH_1W: rail_count <= (i_length << 3) + (i_crc_en ? (16 + (i_cfg_ddr ? 16:0)):0);
		WIDTH_4W: rail_count <= (i_length << 1) + (i_crc_en ? (16 + (i_cfg_ddr ? 16:0)):0);
		default:  rail_count <= i_length + (i_crc_en ? (16 + (i_cfg_ddr ? 16:0)):0);
		endcase
		// Verilator lint_on  WIDTH

		data_phase <= 1;
		load_crc   <= 0;
		// }}}
	end else if (!i_cfg_ds || !OPT_DS)
	begin
		if (i_rx_strb == 2'b11)
		begin
			// {{{
			rail_count <= rail_count - 2;
			last_strb  <= (rail_count == 3);
			if (!i_crc_en)
			begin
				data_phase <= (rail_count > 2);
				load_crc   <= 1'b0;
			end else if (i_cfg_ddr)
			begin
				data_phase <= (rail_count > 16*2+2);
				load_crc   <= (rail_count <= 16*2+2)&&(rail_count > 2) && i_crc_en;
			end else begin
				data_phase <= (rail_count > 18);
				load_crc   <= (rail_count <= 18)&&(rail_count > 2) && i_crc_en;
			end

			if (rail_count < 2)
				rail_count <= 0;
			// }}}
		end else if (i_rx_strb[1])
		begin
			// {{{
			rail_count <= rail_count - 1;
			last_strb  <= (rail_count == 2);

			if (!i_crc_en)
			begin
				data_phase <= (rail_count > 1);
				load_crc   <= 1'b0;
			end else if (i_cfg_ddr)
			begin
				data_phase <= (rail_count >  16*2+1);
				load_crc   <= (rail_count <= 16*2+1)&&(rail_count > 1);
			end else begin
				data_phase <= (rail_count >  17);
				load_crc   <= (rail_count <= 17)&&(rail_count > 1);
			end

			if (rail_count < 1)
				rail_count <= 0;
			// }}}
		end
	end else if (S_ASYNC_VALID)
	begin
		// {{{
		rail_count <= rail_count - 4;
		last_strb  <= 0;

		if (!i_crc_en)
		begin
			data_phase <= (rail_count > 4);
			load_crc   <= 1'b0;
		end else if (i_cfg_ddr)
		begin
			data_phase <= (rail_count >  32+4);
			load_crc   <= (rail_count <= 32+4)&&(rail_count > 4);
		end else begin
			data_phase <= (rail_count >  16+4);
			load_crc   <= (rail_count <= 16+4)&&(rail_count > 4);
		end

		if ((rail_count < 4)||(i_cfg_ddr && rail_count < 8))
			rail_count <= 0;
		// }}}
	end

	always @(posedge i_clk)
	if (i_reset || o_done || !i_rx_en || !i_crc_en)
	begin
		pending_crc <= 1'b0;
	end else if ((i_rx_en && !busy) || load_crc || data_phase)
		pending_crc <= 1'b1;
	else if (!load_crc)
		pending_crc <= 1'b0;

	always @(*)
	begin
		w_done = !(data_phase || pending_crc || s2_valid
				|| sync_fill[4:3] != 2'b00 || mem_valid);
		if (r_watchdog)
			w_done = 1'b1;
		if (!busy)
			w_done = 1'b0;
	end

	always @(posedge i_clk)
	if (i_reset)
		busy <= 0;
	else if (!busy)
		busy <= i_rx_en && i_length > 0 && !o_done;
	else if (w_done)
		busy <= 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CRC checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate for(gk=0; gk<NUMIO; gk=gk+1)
	begin : GEN_RAIL_CRC
		reg	[15:0]		pedge_crc,
					nedge_crc;
		reg	[1:0]		lcl_err;

		// pedge_crc: POSEDGE Calculate the CRC for each rail
		// {{{
		initial	pedge_crc = 0;
		always @(posedge i_clk)
		if (i_reset || !i_rx_en || !i_crc_en ||(!data_phase&&!load_crc))
			pedge_crc <= 0;
		else if ((gk >= 1 && i_cfg_width == WIDTH_1W)
				|| (gk >= 4 && i_cfg_width == WIDTH_4W))
			pedge_crc <= 0;
		else if (!i_cfg_ds || !OPT_DS)
		begin // CRC based upon synchronous inputs
			// {{{
			if (i_rx_strb == 2'b11 && !i_cfg_ddr && !last_strb)
				pedge_crc <= STEPCRC(STEPCRC(pedge_crc,
					i_rx_data[8+gk]),
					i_rx_data[  gk]);
			else if (i_rx_strb[1] && (!i_cfg_ddr || !rail_count[0]))
				pedge_crc <= STEPCRC(pedge_crc,i_rx_data[8+gk]);
			else if (i_rx_strb[0] &&  rail_count[0] && i_cfg_ddr)
				pedge_crc <= STEPCRC(pedge_crc,i_rx_data[0+gk]);
			// }}}
		end else if (S_ASYNC_VALID)
		begin // Asynchronous CRC generation
			// {{{
			// Note that in ASYNC mode, all rails are used
			if (i_cfg_ddr)
			begin
				pedge_crc <= STEPCRC( STEPCRC(pedge_crc,
					S_ASYNC_DATA[gk+24]),
					S_ASYNC_DATA[gk+ 8]);
			end else begin
				pedge_crc <= STEPCRC( STEPCRC(
					STEPCRC( STEPCRC(pedge_crc,
						S_ASYNC_DATA[gk+24]),
						S_ASYNC_DATA[gk+16]),
						S_ASYNC_DATA[gk+ 8]),
						S_ASYNC_DATA[gk   ]);
			end
			// }}}
		end
		// }}}

		// nedge_crc: NEGEDGE Calculate the CRC for each rail
		// {{{
		initial	nedge_crc = 0;
		always @(posedge i_clk)
		if (i_reset || !i_rx_en || !i_crc_en || (!data_phase&&!load_crc)
								|| !i_cfg_ddr)
			nedge_crc <= 0;
		else if ((gk >= 1 && i_cfg_width == WIDTH_1W)
				|| (gk >= 4 && i_cfg_width == WIDTH_4W))
			// Zero out any unused rails
			nedge_crc <= 0;
		else if (!i_cfg_ds || !OPT_DS)
		begin // CRC based upon synchronous inputs
			// {{{
			if (i_rx_strb[1] && rail_count[0])
				nedge_crc <= STEPCRC(nedge_crc, i_rx_data[8+gk]);
			else if (i_rx_strb[0] && !rail_count[0])
				nedge_crc <= STEPCRC(nedge_crc, i_rx_data[0+gk]);
			// }}}
		end else if (S_ASYNC_VALID)
		begin // Asynchronous CRC generation
			// {{{
			// Note that in ASYNC mode, all rails are used (IIRC)
			nedge_crc <= STEPCRC( STEPCRC(nedge_crc,
						S_ASYNC_DATA[gk+16]),
						S_ASYNC_DATA[gk   ]);
			// }}}
		end
		// }}}

		always @(posedge i_clk)
		if (i_reset || !i_rx_en || !i_crc_en || data_phase || load_crc)
		begin
			lcl_err <= 2'b00;
		end else begin
			lcl_err[0] <= (pedge_crc != 0);

			lcl_err[1] <= (nedge_crc != 0) && i_cfg_ddr;
		end

		assign	err[gk] = lcl_err[0];
		assign	err[gk+NUMIO] = lcl_err[1];
	end endgenerate

	initial	o_done = 0;
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || o_done || !busy)
		{ o_done, o_err } <= 0;
	else if (w_done)
	begin
		o_done <= 1'b1;
		o_err  <= |err;
	end

	function automatic [NCRC-1:0]	STEPCRC(reg[NCRC-1:0] prior,
						input i_crc_data);
	begin
		if (prior[NCRC-1] ^ i_crc_data)
			STEPCRC = { prior[NCRC-2:0], 1'b0 } ^ CRC_POLYNOMIAL;
		else
			STEPCRC = { prior[NCRC-2:0], 1'b0 };
	end endfunction

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog timeout
	// {{{

	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (!r_watchdog &&
			(((!OPT_DS || !i_cfg_ds) && i_rx_strb != 0)
			|| (OPT_DS && i_cfg_ds && S_ASYNC_VALID))))
	begin
		r_watchdog <= 0;
		r_timeout  <= -1;
	end else if (r_timeout != 0)
	begin
		r_watchdog <= (r_timeout <= 1);
		r_timeout  <= r_timeout - 1;
	end
	// }}}

	function automatic [$clog2(MW/8):0] COUNTONES(input [MW/8-1:0] set);
		integer ik;
	begin
		COUNTONES=0;
		for(ik=0; ik<MW/8; ik=ik+1)
		if (set[ik])
			COUNTONES=COUNTONES+1;
	end endfunction

	//
	// Make verilator happy
	// verilator lint_off UNUSED
	// wire	unused;
	// assign	unused = i_wb_cyc;
	// verilator lint_on  UNUSED
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	[LGLEN+3:0]		f_count;
	reg				f_past_valid, f_state;
	reg	[LGLEN:0]		fmem_count, f_recount;
	(* anyconst *)	reg	[LGLEN:0]	fc_posn;
	(* anyconst *)	reg	[7:0]		fc_data;
	reg	[MW-1:0]		fmem_data;
	reg	[MW/8-1:0]		fmem_strb;
	reg	[$clog2(MW/8)-1:0]	f_next_subaddr;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Configuration validation
	// {{{

	always @(*)
	if (!OPT_DS)
		assume(!i_cfg_ds);

	always @(posedge i_clk)
	if (!i_reset && $past(i_reset))
		assume(!i_rx_en);
	else if ($past(i_rx_en && o_done))
		assume(!i_rx_en);
	else if ($past(i_rx_en))
		assume(i_rx_en);

	always @(posedge i_clk)
	if (i_rx_en)
	begin
		assume($stable(i_crc_en));
		assume($stable(i_length));
		assume($stable(i_cfg_ds));
		assume($stable(i_cfg_ddr));
		assume($stable(i_cfg_width));

		assume(i_length > 0);
		if (i_cfg_ds)
		begin
			assume(i_length[1:0] == 2'b00);
		end else if (i_cfg_ddr && i_cfg_width >= WIDTH_8W)
			assume(i_length[0] == 1'b0);
	end

	always @(*)
	if (i_cfg_ds) assume(i_cfg_width == WIDTH_8W && i_cfg_ddr);

	always @(*)
	if (!i_reset)
	begin
		assume(i_cfg_width != 2'b11);
		assume(i_length <= 16'h8000);
	end

	always @(posedge i_clk)
	if (i_reset)
		f_state <= 1'b0;
	else if (o_done)
		f_state <= 1'b0;
	else if (i_rx_en)
		f_state <= 1'b1;

	always @(posedge i_clk)
	if (!i_reset && !r_watchdog)
	begin
		if (busy || data_phase || load_crc || o_done
				|| s2_valid || o_mem_valid)
		begin
			assert(f_state);
		end else begin
			assert(!f_state || $past(o_mem_valid));
		end

		if (load_crc || data_phase)
			assert(busy || r_watchdog);
	end

	always @(posedge i_clk)
	if (!i_reset && o_err)
		assert(i_crc_en && o_done);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PHY assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!i_reset && $past(!i_rx_en))
	begin
		assume(i_rx_strb == 0);
		assume(S_ASYNC_VALID == 0);
	end

	always @(*)
	if (!i_rx_strb[1])
		assume(!i_rx_strb[0]);

	always @(*)
	if (!OPT_DS)
		assume(!S_ASYNC_VALID);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// f_count: count received bits
	// {{{
	initial	f_count = 0;
	always @(posedge i_clk)
	if (i_reset || !i_rx_en)
		f_count <= 0;
	else if (data_phase || load_crc)
	begin
		if (i_cfg_ds)
		begin
			if (S_ASYNC_VALID)
				f_count <= f_count + 32;
		end else case(i_cfg_width)
		WIDTH_1W: f_count <= f_count + (i_rx_strb[1] ? 1:0)
							+ (i_rx_strb[0] ? 1:0);
		WIDTH_4W: f_count <= f_count + (i_rx_strb[1] ? 4:0)
							+ (i_rx_strb[0] ? 4:0);
		default:  f_count <= f_count + (i_rx_strb[1] ? 8:0)
							+ (i_rx_strb[0] ? 8:0);
		endcase
	end

	always @(posedge i_clk)
	if (!i_reset && i_rx_en)
	begin
		if (i_cfg_ds)
		begin
			assert(f_count[4:0] == 0);
		end else case(i_cfg_width)
		WIDTH_1W: begin end
		WIDTH_4W: assert(f_count[1:0] == 2'b0);
		WIDTH_8W: assert(f_count[2:0] == 3'b0);
		endcase

		if (!i_cfg_ds && data_phase)
			assert(f_count[2:0] == sync_fill[2:0]);
	end
	// }}}

	// fmem_count
	// {{{
	always @(posedge i_clk)
	if (!i_rx_en)
		fmem_count <= 0;
	else if (o_mem_valid)
		fmem_count <= fmem_count + $countones(o_mem_strb);
	// }}}

	always @(posedge i_clk)
	if (!i_reset)
		assert(s2_valid == (s2_fill != 0));

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && (i_cfg_ds && OPT_DS))
		assert(!s2_valid);

	always @(posedge i_clk)
	if (i_reset || !i_rx_en)
	begin end
	else if (!$past(i_rx_en))
		assert(sync_fill == 0);
	else case(i_cfg_width)
	WIDTH_1W: assert(sync_fill <= 5'd9);
	WIDTH_4W: assert(sync_fill[1:0] == 2'b00 && sync_fill <= 5'd12);
	WIDTH_8W: assert(sync_fill[2:0] == 3'b00 && sync_fill <= 5'd16);
	default: assert(0);
	endcase

	always @(*)
	begin
		// Relate the two counts together
		// fmem_count
		//	+ (o_mem_valid ? $countones(o_mem_strb)
		//	+ (s2_valid ? s2_fill
		//	+ sync_fill[4:3]
		//	======================
		//	f_count

		f_recount = fmem_count;
		if (o_mem_valid)
			f_recount = f_recount + $countones(o_mem_strb);
		if (rnxt_strb)
			f_recount = f_recount + 1;
		if (!i_cfg_ds || !OPT_DS)
		begin
			if (s2_valid)
				f_recount = f_recount + s2_fill;
			f_recount = f_recount + sync_fill[4:3];
		end
	end

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && data_phase && !r_watchdog)
	begin
		// reg	[LGLEN:0]	fmem_count, f_recount;
		assert(f_count[LGLEN+3:3] == f_recount);
	end

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && o_mem_valid)
	begin
		if (i_cfg_ds)
		begin
			assert($countones(o_mem_strb) == 4);
		end else case(i_cfg_width)
		WIDTH_1W: assert($countones(o_mem_strb) == 1);
		WIDTH_4W: assert($countones(o_mem_strb) == 1);
		WIDTH_8W: begin end // assert($countones(o_mem_strb) <= 2 + ($past(rnxt_strb) ? 1:0));
		default: assert(0);
		endcase
	end

	// Relate the rail_count to f_count
	// {{{
	always @(posedge i_clk)
	if (!i_reset && i_rx_en)
	begin
		case(i_cfg_width)
		WIDTH_1W: if (!i_crc_en)
			begin
				assert(rail_count <= (i_length*8));
			end else if (i_cfg_ddr)
			begin
				assert(rail_count <= (i_length*8) + 32);
			end else
				assert(rail_count <= (i_length*8) + 16);
		WIDTH_4W: if (!i_crc_en)
			begin
				assert(rail_count <= (i_length*2));
			end else if (i_cfg_ddr)
			begin
				assert(rail_count <= (i_length*2 + 32));
			end else
				assert(rail_count <= (i_length*2 + 16));
		WIDTH_8W: if (!i_crc_en)
			begin
				assert(rail_count <= i_length);
			end else if (i_cfg_ddr)
			begin
				assert(rail_count <= (i_length + 32));
			end else
				assert(rail_count <= (i_length + 16));
		default: assert(0);
		endcase

		if (!i_crc_en)
		begin
			assert(!load_crc);
			assert(!pending_crc);
			assert(data_phase == (rail_count > 0));
		end  else if (i_cfg_ddr)
		begin
			assert(data_phase == (rail_count > 32));
			assert(load_crc   == (rail_count <= 32 && rail_count>0));
		end else begin
			assert(data_phase == (rail_count > 16));
			assert(load_crc   == (rail_count <= 16 && rail_count>0));
		end

		if (i_crc_en && (load_crc || data_phase))
			assert(pending_crc);
		assert(last_strb == (rail_count == 1));
	end

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && busy && (data_phase || load_crc))
	begin
		casez({ i_crc_en, i_cfg_ddr, i_cfg_width })
		{ 1'b0, 1'b?, WIDTH_1W }: begin
				assert(rail_count + f_count == i_length*8);
				assert(f_count <= i_length*8);
				assert(rail_count <= i_length*8);
				end
		{ 2'b10, WIDTH_1W }: begin
				assert(rail_count + f_count == i_length*8+16);
				assert(f_count <= i_length*8+16);
				assert(rail_count <= i_length*8+16);
				end
		{ 2'b11, WIDTH_1W }: begin
				assert(rail_count + f_count == i_length*8+32);
				assert(f_count <= i_length*8+32);
				assert(rail_count <= i_length*8+32);
				end
		{ 1'b0, 1'b?, WIDTH_4W }: begin
				assert(rail_count + (f_count>>2) == i_length*2);
				assert((f_count>>2) <= i_length*2);
				assert(rail_count <= i_length*2);
				end
		{ 2'b10, WIDTH_4W }: begin
				assert(rail_count + (f_count>>2) == i_length*2+16);
				assert((f_count>>2) <= i_length*2+16);
				assert(rail_count <= i_length*2+16);
				end
		{ 2'b11, WIDTH_4W }: begin
				assert(rail_count + (f_count>>2) == i_length*2+32);
				assert((f_count>>2) <= i_length*2+32);
				assert(rail_count <= i_length*2+32);
				end
		{ 1'b0, 1'b?, WIDTH_8W }: begin
				assert(rail_count + (f_count>>3) == i_length);
				assert((f_count>>3) <= i_length);
				assert(rail_count <= i_length);
				end
		{ 2'b10, WIDTH_8W }: begin
				assert(rail_count + (f_count>>3) == i_length+16);
				assert((f_count>>3) <= i_length+16);
				assert(rail_count <= i_length+16);
				end
		{ 2'b11, WIDTH_8W }: begin
				assert(rail_count+(f_count>>3) == i_length+32);
				assert((f_count>>3) <= i_length+32);
				assert(rail_count <= i_length+32);
				end
		default: assert(0);
		endcase
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory interface
	// {{{

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && fmem_count == 0)
		assert(!mem_full);

	always @(*)
	if (o_mem_valid)
		f_next_subaddr = subaddr + $countones(o_mem_strb)
					+ (rnxt_strb ? 1:0);
	else
		f_next_subaddr = subaddr;

	always @(posedge i_clk)
	if (i_reset)
	begin end else
		assert(f_next_subaddr == next_subaddr);

	always @(posedge i_clk)
	if (!i_reset && rnxt_strb)
		assert(o_mem_valid);

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && mem_full)
		assert({ mem_addr, subaddr } == 0);

	always @(*)
	if (!i_reset && i_rx_en)
		assert({ mem_full, o_mem_addr, subaddr } == fmem_count);

	always @(posedge i_clk)
	if (!i_reset && !i_rx_en)
		assert(!o_mem_valid);
	else if (!i_reset && o_mem_valid)
		assert(o_mem_strb != 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{

	// Assume the known receive value
	// {{{
	always @(posedge i_clk)
	if (i_rx_en && f_count[LGLEN+3:5] == fc_posn[LGLEN:2]
			&& i_cfg_ds && S_ASYNC_VALID)
	begin
		case(fc_posn[1:0])
		2'b00: assume(S_ASYNC_DATA[31:24] == fc_data);
		2'b01: assume(S_ASYNC_DATA[23:16] == fc_data);
		2'b10: assume(S_ASYNC_DATA[15: 8] == fc_data);
		2'b11: assume(S_ASYNC_DATA[ 7: 0] == fc_data);
		endcase
	end

	always @(posedge i_clk)
	if (i_rx_en && !i_cfg_ds && i_cfg_width == WIDTH_1W)
	begin
		// {{{
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd0 })
			assume(i_rx_data[8] == fc_data[7]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd1 })
			assume(i_rx_data[8] == fc_data[6]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd2 })
			assume(i_rx_data[8] == fc_data[5]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd3 })
			assume(i_rx_data[8] == fc_data[4]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd4 })
			assume(i_rx_data[8] == fc_data[3]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd5 })
			assume(i_rx_data[8] == fc_data[2]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd6 })
			assume(i_rx_data[8] == fc_data[1]);
		if (i_rx_strb[1] && f_count == { fc_posn, 3'd7 })
			assume(i_rx_data[8] == fc_data[0]);

		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd0 })
			assume(i_rx_data[0] == fc_data[7]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd1 })
			assume(i_rx_data[0] == fc_data[6]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd2 })
			assume(i_rx_data[0] == fc_data[5]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd3 })
			assume(i_rx_data[0] == fc_data[4]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd4 })
			assume(i_rx_data[0] == fc_data[3]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd5 })
			assume(i_rx_data[0] == fc_data[2]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd6 })
			assume(i_rx_data[0] == fc_data[1]);
		if (i_rx_strb[0] && f_count + 1 == { fc_posn, 3'd7 })
			assume(i_rx_data[0] == fc_data[0]);
		// }}}
	end

	always @(posedge i_clk)
	if (i_rx_en && !i_cfg_ds && i_cfg_width == WIDTH_4W)
	begin
		// {{{
		if (f_count == { fc_posn, 3'd0 } && i_rx_strb[1])
			assume(i_rx_data[11:8] == fc_data[7:4]);
		if (f_count == { fc_posn, 3'd4 } && i_rx_strb[1])
			assume(i_rx_data[11:8] == fc_data[3:0]);

		if (f_count +4 == { fc_posn, 3'd0 } && i_rx_strb[0])
			assume(i_rx_data[ 3: 0] == fc_data[7:4]);
		if (f_count +4 == { fc_posn, 3'd4 } && i_rx_strb[0])
			assume(i_rx_data[ 3: 0] == fc_data[3:0]);
		// }}}
	end

	always @(posedge i_clk)
	if (i_rx_en && !i_cfg_ds && i_cfg_width == WIDTH_8W)
	begin
		if (f_count == { fc_posn, 3'b0 } && i_rx_strb[1])
			assume(i_rx_data[15:8] == fc_data);
		if (f_count + 8 == { fc_posn, 3'b0 } && i_rx_strb[0])
			assume(i_rx_data[ 7:0] == fc_data);
	end
	// }}}

	// Assert the value if it's in our pipeline, perhaps stalled somewhere
	// {{{
	always @(*)
	if (!i_reset && i_rx_en && !i_cfg_ds && sync_fill != 0
		&& i_cfg_width == WIDTH_1W && f_count[LGLEN+3:3] == fc_posn)
	begin
		case(sync_fill[2:0])
		3'd0: begin end // Nothing loaded, nothing to assert
		3'd1: assert(sync_sreg[0:0] == fc_data[7:7]);
		3'd2: assert(sync_sreg[1:0] == fc_data[7:6]);
		3'd3: assert(sync_sreg[2:0] == fc_data[7:5]);
		3'd4: assert(sync_sreg[3:0] == fc_data[7:4]);
		3'd5: assert(sync_sreg[4:0] == fc_data[7:3]);
		3'd6: assert(sync_sreg[5:0] == fc_data[7:2]);
		3'd7: assert(sync_sreg[6:0] == fc_data[7:1]);
		endcase
	end

	always @(*)
	if (!i_reset && i_rx_en && !i_cfg_ds && sync_fill != 0
		&& i_cfg_width == WIDTH_4W && f_count == { fc_posn, 3'd4 })
	begin
		assert(sync_sreg[3:0] == fc_data[7:4]);
	end
	// }}}

	// Assert the known value out
	// {{{
	always @(*)
	begin
		fmem_data = mem_data << (8*fc_posn[$clog2(MW/8)-1:0]);
		fmem_strb = mem_strb << (fc_posn[$clog2(MW/8)-1:0]);
	end

	always @(posedge i_clk)
	if (!i_reset && i_rx_en && o_mem_valid)
	begin
		if ((o_mem_addr == fc_posn[LGLEN:$clog2(MW/8)])
				&& mem_strb[(MW/8-1)-fc_posn[$clog2(MW/8)-1:0]])
		begin
			// Assume big-endian ordering
			assert(fmem_data[MW-1:MW-8] == fc_data);
			assert(fmem_strb);
		end
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	always @(posedge i_clk)
	if (!i_reset && i_rx_en && o_done)
	begin
		case({ i_cfg_ds, i_cfg_ddr, i_cfg_width })
		4'b0000: begin
				cover(!i_crc_en);
				cover(o_err);		// !!!
				cover(i_crc_en && !o_err);
				end
		4'b0001: begin
				cover(!i_crc_en);
cover(fc_posn == 0 && fc_data == 8'hff);
cover(fc_posn == 0 && fc_data == 8'ha5);
cover(fc_posn == 0 && fc_data == 8'h5a);
cover(fc_posn == 0 && fc_data == 8'h7e);
				cover(o_err);		// !!!
				cover(i_crc_en && !o_err);
				end
		4'b0010: begin
				cover(!i_crc_en);
				cover(o_err);		// !!!
				cover(i_crc_en && !o_err);
				end
		4'b0100: begin
				cover(!i_crc_en);
				cover(o_err);		// !!!
				cover(i_crc_en && !o_err);
				end
		4'b0101: begin
				cover(!i_crc_en);
				cover(o_err);		// !!!
				cover(i_crc_en && !o_err);
				end
		4'b0110: begin
				cover(!i_crc_en);
				cover(o_err);		// !!!
				cover(i_crc_en && !o_err);
				end
		// 4'b1110: cover(1);
		default: begin end
		endcase
	end

	generate if (OPT_DS)
	begin : CVR_DATA_STROBE
		always @(posedge i_clk)
		if (!i_reset && i_rx_en && o_done)
		begin
			case({ i_cfg_ds, i_cfg_ddr, i_cfg_width })
			// 4'b0000: cover(1);
			// 4'b0001: cover(1);
			// 4'b0010: cover(1);
			// 4'b0100: cover(1);
			// 4'b0101: cover(1);
			// 4'b0110: cover(1);
			4'b1110: begin
				cover(!i_crc_en);
				cover(o_err);
				cover(i_crc_en && !o_err);
				end
			default: begin end
			endcase
		end

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{

	// always @(*) assume(!r_watchdog);
	// }}}
`endif	// FORMAL
// }}}
endmodule
