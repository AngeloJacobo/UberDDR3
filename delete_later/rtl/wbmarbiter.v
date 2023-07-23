////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbmarbiter.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A *HIGH* speed N:1 WB arbiter.  This works like an N:1 AXI
//		arbiter: Wishbone requests are potentially interleaved between
//	multiple (incoming) slave connections.  Hence, an outgoing connection
//	might include requests from slave 1, 2, 4, 3, etc, and the arbiter
//	will be responsible for returning ACKs in the order they were received:
//	1, 2, 4, 3, etc.  There are some unfortunate consequences to this,
//	however, that break some key features of Wishbone.
//
//	1. If two slaves have outstanding requests and a bus error is returned,
//		the bus error will be returned to *both* slaves, not just one,
//		*EVEN IF* only one slave created an illegal access.
//	2. Read-Modify-Write accesses are now broken, because there is no longer
//		any guarantee, when using this arbiter, that no other bus master
//		(incoming slave) will not have modified a given address.
//	3. The property that bus requests will only ever be a string of reads,
//		or a string of writes, is also broken.
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
module wbmarbiter #(
		// {{{
		parameter	DW = 64,
		parameter	AW = 31-$clog2(DW/8),
		parameter	NIN = 4,
		parameter	LGFIFO = 5,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire	[NIN-1:0]	s_cyc, s_stb, s_we,
		input	wire	[NIN*AW-1:0]	s_addr,
		input	wire	[NIN*DW-1:0]	s_data,
		input	wire	[NIN*DW/8-1:0]	s_sel,
		output	wire	[NIN-1:0]	s_stall, s_ack,
		output	wire	[NIN*DW-1:0]	s_idata,
		output	wire	[NIN-1:0]	s_err,
		//
		output	reg			m_cyc, m_stb, m_we,
		output	reg	[AW-1:0]	m_addr,
		output	reg	[DW-1:0]	m_data,
		output	reg	[DW/8-1:0]	m_sel,
		input	wire			m_stall, m_ack,
		input	wire	[DW-1:0]	m_idata,
		input	wire			m_err
		// }}}
	);

	// Register/net declarations
	// {{{
	genvar			gk;
	integer			ik;

	wire			arb_stall;
	wire	[NIN-1:0]	grant;
	reg	[NIN-1:0]	ack, err;
	reg	[DW-1:0]	data;

	wire			fifo_reset;
	wire			ack_wr, ack_rd;
	reg	[LGFIFO:0]	fif_wraddr, fif_rdaddr;
	wire	[LGFIFO:0]	ack_fill;
	wire			ack_empty, ack_full;
	wire	[NIN-1:0]	ack_fifo_data;

	reg	[NIN-1:0]	flushing;

	reg			nxt_stb, nxt_we;
	reg	[AW-1:0]	nxt_addr;
	reg	[DW-1:0]	nxt_data;
	reg	[DW/8-1:0]	nxt_sel;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate among sources
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	pktarbiter #(
		.W(NIN)
	) u_arb (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.i_req(s_stb & ~flushing), .i_stall(arb_stall),
		.o_grant(grant)
	);

	assign	arb_stall = m_stb && m_stall;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Log STBs, to know where to deliver ACKs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	fifo_reset = i_reset || (m_cyc && m_err);
	assign	ack_wr =|(s_stb & ~s_stall);
	assign	ack_rd = m_ack;

`ifdef	FORMAL
	// {{{
	wire	[LGFIFO:0]	f_first_addr, f_second_addr,
				f_distance_to_first, f_distance_to_second;
	wire			f_first_in_fifo, f_second_in_fifo;
	wire	[NIN-1:0]	f_first_data, f_second_data;
	wire	[LGFIFO:0]	f_wraddr, f_rdaddr;
	wire [NIN-1:0]		f_ch_empty;
	wire [NIN*(LGFIFO+1)-1:0] f_ch_last_addr;
	// }}}
`endif

	sfifo #(
		.BW(NIN),
		.LGFLEN(LGFIFO)
	) u_ack_fifo (
		// {{{
		.i_clk(i_clk), .i_reset(fifo_reset),
		.i_wr(ack_wr), .i_data(grant),
		.o_full(ack_full), .o_fill(ack_fill),
		.i_rd(ack_rd), .o_data(ack_fifo_data),
		.o_empty(ack_empty)
`ifdef	FORMAL
		// {{{
		, .f_first_addr(f_first_addr),
		.f_second_addr(f_second_addr),
		.f_first_data(f_first_data),
		.f_second_data(f_second_data),
		.f_first_in_fifo(f_first_in_fifo),
		.f_second_in_fifo(f_second_in_fifo),
		.f_distance_to_first(f_distance_to_first),
		.f_distance_to_second(f_distance_to_second),
		.f_wraddr(f_wraddr), .f_rdaddr(f_rdaddr)
		// }}}
`endif
		// }}}
	);

	always @(posedge i_clk)
	if (fifo_reset)
		fif_wraddr <= 0;
	else if (ack_wr && !ack_full)
		fif_wraddr <= fif_wraddr + 1;

	always @(posedge i_clk)
	if (fifo_reset)
		fif_rdaddr <= 0;
	else if (ack_rd && !ack_empty)
		fif_rdaddr <= fif_rdaddr + 1;

`ifdef	FORMAL
	always @(*)
	if (!fifo_reset)
		assert(fif_wraddr == f_wraddr);

	always @(*)
	if (!fifo_reset)
		assert(fif_rdaddr == f_rdaddr);
`endif

	// Need to do some extra work, just to deal with potential bus errors
	// and dropped CYC lines
	initial	ack = 0;
	initial	err = 0;
	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : FLUSH_ACKS
		// At issue is the fact that, if the slave drops CYC, we need
		// to abort any ongoing transactions.  Likewise, if the master
		// returns a bus error--we'll also need to abort any ongoing
		// transactions.  In both of those cases we need to make sure
		// nothing in the FIFO is returned to this slave as an ACK from
		// any outstanding transactions.
		reg			empty;
		reg	[LGFIFO:0]	last_addr;

		// last_addr
		// {{{
		// last_addr == fif_rdaddr if we are empty, or if we have only
		//   one address in the FIFO
		always @(posedge i_clk)
		if (fifo_reset)
			last_addr <= 0;
		else if (ack_empty || s_stb[gk] && !s_stall[gk])
			last_addr <= fif_wraddr;
		else if (ack_rd && last_addr == fif_rdaddr)
			last_addr <= fif_rdaddr + 1;
		// }}}

		// empty
		// {{{
		initial	empty = 1;
		always @(posedge i_clk)
		if (fifo_reset || !s_cyc[gk])
			empty <= 1;
		else if (s_stb[gk] && !s_stall[gk])
			empty <= 1'b0;
		else if (ack_empty)
			empty <= 1;
		else if (ack_rd && last_addr == fif_rdaddr)
			empty <= 1;
		// }}}

		// flushing[gk]
		// {{{
		always @(posedge i_clk)
		if (fifo_reset)
			flushing[gk] <= 0;
		else if (ack_empty || (m_ack && last_addr == fif_rdaddr))
			flushing[gk] <= 0;
		else if (!s_cyc[gk])
			flushing[gk] <= 1;
		// }}}

		assign	s_stall[gk] = flushing[gk] || (grant != (1<<gk))
				|| ack_full || (m_stb && m_stall)
				|| (m_cyc && m_err);

		// initial	ack[gk] = 0;
		// ack[gk]
		// {{{
		always @(posedge i_clk)
		if (i_reset || !m_cyc || !s_cyc[gk] || empty)
			ack[gk] <= 0;
		else
			ack[gk] <= m_ack && ack_fifo_data[gk];
		// }}}

		// err[gk]
		// {{{
		always @(posedge i_clk)
		if (i_reset || !m_cyc || !s_cyc[gk])
			err[gk] <= 0;
		else if (empty && (!s_stb[gk] || s_stall[gk]))
			err[gk] <= 0;
		else if (m_err && !ack_empty)
			err[gk] <= 1'b1;
		// }}}

`ifdef	FORMAL
		// {{{
		always @(*)
		if (ack_empty)
			assert(empty);

		reg	[LGFIFO:0]	f_dist_to_last;
		always @(*)
			f_dist_to_last = last_addr - f_rdaddr;

		always @(*)
		if (!fifo_reset)
			assert(f_dist_to_last <= ack_fill);

		always @(*)
		if (!fifo_reset && f_dist_to_last == ack_fill)
			assert(empty);

		/*
		if (!fifo_reset)
			assert(empty == ((f_dist_to_last == ack_fill)
					&& (ack_empty || !ack_fifo_data[gk])));
		*/

		always @(*)
		if (!fifo_reset && last_addr != fif_rdaddr
					&& f_first_addr == last_addr)
			assert(f_first_in_fifo && f_first_data & (1<<gk));

		always @(*)
		if (!fifo_reset && last_addr != fif_rdaddr
					&& f_second_addr == last_addr)
			assert(f_second_in_fifo && f_second_data & (1<<gk));

		assign	f_ch_empty[gk] = empty;
		assign	f_ch_last_addr[gk*(LGFIFO+1) +: (LGFIFO+1)] = last_addr;
		// }}}
`endif
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// m_*: Generate downstram outputs
	// {{{

	initial	m_cyc = 1'b0;
	always @(posedge i_clk)
	if (fifo_reset)
		m_cyc <= 1'b0;
	else if (ack_wr)
		m_cyc <= 1'b1;
	else if (m_cyc && m_ack && ack_fill == 1)
		m_cyc <= 1'b0;

	always @(*)
	begin
		nxt_stb  = |(s_stb & ~s_stall & ~s_err);
		nxt_we   = 0;
		nxt_addr = 0;
		nxt_data = 0;
		nxt_sel  = 0;
		for(ik=0; ik<NIN; ik=ik+1)
		if (grant[ik])
		begin
			nxt_we   = nxt_we   | s_we[ik];
			nxt_addr = nxt_addr | s_addr[ik * AW   +: AW  ];
			nxt_data = nxt_data | s_data[ik * DW   +: DW  ];
			nxt_sel  = nxt_sel  | s_sel[ ik * DW/8 +: DW/8];
		end
	end

	initial	m_stb = 1'b0;
	always @(posedge i_clk)
	if (fifo_reset)
		m_stb <= 1'b0;
	else if (!m_stb || !m_stall)
		m_stb <= nxt_stb;

	always @(posedge i_clk)
	if (OPT_LOWPOWER && fifo_reset)
	begin
		m_addr <= 0;
		m_data <= 0;
		m_sel  <= 0;
	end else if (!m_stb || !m_stall)
	begin
		m_we   <= nxt_we;
		m_addr <= nxt_addr;
		m_data <= nxt_data;
		m_sel  <= nxt_sel;

		if (OPT_LOWPOWER && !nxt_stb)
		begin
			m_we   <= 1'b0;
			m_addr <= {(AW  ){1'b0}};
			m_data <= {(DW  ){1'b0}};
			m_sel  <= {(DW/8){1'b0}};
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// s_*: Generate return data
	// {{{
	assign	s_ack = ack;
	assign	s_err = err;

	always @(posedge i_clk)
		data <= m_idata;

	assign	s_idata = {(NIN){data}};
	// }}}

	// Keep Verilator happy
	// {{{
	// }}}
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
	localparam	F_LGDEPTH = LGFIFO+1;
	reg			f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwbm_nreqs, fwbm_nacks, fwbm_outstanding;
	wire	[F_LGDEPTH-1:0]	fwbs_nreqs, fwbs_nacks, fwbs_outstanding;
	(* anyconst *) reg	[$clog2(NIN)-1:0]	fc_checkid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Bus checks
	// {{{
	fwb_slave #(
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH)
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(s_cyc[fc_checkid]), .i_wb_stb(s_stb[fc_checkid]),
				.i_wb_we(s_we[fc_checkid]),
		.i_wb_addr(s_addr[fc_checkid*AW +: AW]),
			.i_wb_data(s_data[fc_checkid*DW +: DW]),
			.i_wb_sel(s_sel[fc_checkid*DW/8 +: DW/8]),
		.i_wb_ack(s_ack[fc_checkid]), .i_wb_stall(s_stall[fc_checkid]),
		.i_wb_idata(s_idata[fc_checkid*DW +: DW]),
		.i_wb_err(s_err[fc_checkid]),
		.f_nreqs(fwbs_nreqs),
		.f_nacks(fwbs_nacks),
		.f_outstanding(fwbs_outstanding)
		// }}}
	);

	fwb_master #(
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH)
	) fwb_m (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(m_cyc), .i_wb_stb(m_stb), .i_wb_we(1'b0 && m_we),
		.i_wb_addr(m_addr), .i_wb_data(m_data), .i_wb_sel(m_sel),
		.i_wb_ack(m_ack), .i_wb_stall(m_stall), .i_wb_idata(m_idata),
		.i_wb_err(m_err),
		.f_nreqs(fwbm_nreqs),
		.f_nacks(fwbm_nacks),
		.f_outstanding(fwbm_outstanding)
		// }}}
	);


	wire			f_known_data, fc_ack;
	wire	[LGFIFO:0]	f_known_checkid, fc_last_addr, fc_last_distance,
				f_known_noncheckid;
	wire			fc_empty;

	assign	fc_empty = f_ch_empty[fc_checkid];
	assign	fc_last_addr = f_ch_last_addr >> (fc_checkid * (LGFIFO+1));
	assign	fc_last_distance = fc_last_addr - f_rdaddr;

	assign	f_known_data = (f_first_in_fifo && f_distance_to_first == 0)
			|| (f_second_in_fifo && f_distance_to_second == 0);

	assign	f_known_checkid =
		((f_first_in_fifo && (f_first_data & (1<<fc_checkid))) ? 1:0)
		+((f_second_in_fifo && (f_second_data & (1<<fc_checkid)))? 1:0);

	assign	f_known_noncheckid =
		((f_first_in_fifo&&(0==(f_first_data & (1<<fc_checkid))))? 1:0)
		+((f_second_in_fifo&&(0==(f_second_data&(1<<fc_checkid))))?1:0);

	assign	fc_ack = (s_ack & (1<<fc_checkid)) ? 1:0;

	always @(*)
	if (!i_reset)
		assume((s_cyc & s_stb) == s_stb);

	generate for(gk=0; gk<NIN; gk=gk+1)
	begin
		always @(*)
		if (!i_reset && s_stb[gk])
			assume(s_cyc[gk]);

		always @(posedge i_clk)
		if (!f_past_valid || $past(i_reset))
			assume(!s_cyc[gk] && !s_stb[gk]);
		else if ($past(s_stb[gk] && s_stall[gk]))
		begin
			assume(s_cyc[gk]);
			assume(s_stb[gk]);
			assume($stable(s_we[gk]));
			assume($stable(s_addr[gk * AW +: AW]));
			assume($stable(s_data[gk * DW +: DW]));
			assume($stable(s_sel[ gk * (DW/8) +: (DW/8)]));
		end

	end endgenerate

	always @(*)
	if (!i_reset)
	begin
		// assert(empty == ((f_dist_to_last == ack_fill)
		//			&& (ack_empty || !ack_fifo_data[gk])));
		if (f_first_in_fifo)
		begin
			assert($onehot(f_first_data));
			if (fc_last_addr == f_first_addr && f_first_addr != f_rdaddr)
				assert(f_first_data & (1<<fc_checkid));
			if (f_first_data & (1<<fc_checkid))
			begin
				assert(f_distance_to_first <= fc_last_distance);
			end else begin
				assert(fc_last_distance == 0
					|| fc_last_distance != f_distance_to_first);
				assert(f_distance_to_first < ack_fill);
			end
		end

		if (f_second_in_fifo)
		begin
			assert($onehot(f_second_data));
			if (fc_last_addr == f_second_addr && f_second_addr != f_rdaddr)
				assert(f_second_data & (1<<fc_checkid));
			if (f_second_data & (1<<fc_checkid))
			begin
				assert(f_distance_to_second <= fc_last_distance);
			end else begin
				assert(fc_last_distance == 0
					|| fc_last_distance != f_distance_to_second);
				assert(f_distance_to_second < ack_fill);
			end

			if (fc_last_distance >= f_distance_to_second) // ***
				assert(fwbs_outstanding <= fc_last_distance+1
						- f_known_noncheckid + fc_ack);
		end

		if (fc_last_addr == f_wraddr)
			assert(ack_empty);

		// f_known_checkid+fc_ack<= fwbs_outstanding <= ack_fill+fc_ack
		assert(fwbs_outstanding >= f_known_checkid + fc_ack);
		assert(fwbs_outstanding <= ack_fill+fc_ack-f_known_noncheckid);
		assert(fc_last_distance <= ack_fill);
		assert(fwbs_outstanding <= fc_last_distance
						+ fc_ack + (ack_empty ? 0 :1));
		assert(fwbm_outstanding + (m_stb ? 1:0) + (fc_ack ? 1:0)
			>= fwbs_outstanding);				// ***
		assert(ack_fill == fwbm_outstanding + (m_stb ? 1:0));
		if (fc_empty)
		begin
			assert(fwbs_outstanding == (fc_ack ? 1:0));
			assert(fc_last_distance == 0);
			assert(ack_empty
				|| ((ack_fifo_data & (1<<fc_checkid))==0));
		end else begin
			assert(!ack_empty);
			assert(fc_last_distance != 0
				|| (ack_fifo_data & (1<<fc_checkid)));
		end

		assume((flushing & (1<<fc_checkid))==0);
		if (ack_empty)
		begin
		end else if (!f_known_data)
		begin
			assume($onehot(ack_fifo_data));

			if(fc_empty)
			begin
				assume((ack_fifo_data & (1<<fc_checkid))==0);
			end else if (fc_last_distance == 0)
			begin
				assume(ack_fifo_data & (1<<fc_checkid));
			end

			if (fwbs_outstanding == f_known_checkid + fc_ack)
			begin
				assume((ack_fifo_data & (1<<fc_checkid))==0);
			end

			if (fwbs_outstanding == ack_fill - f_known_noncheckid + fc_ack)
			begin
				assume(ack_fifo_data & (1<<fc_checkid));
			end

			if (fwbs_outstanding == fc_last_distance + fc_ack + 1)
			begin
				assume(ack_fifo_data & (1<<fc_checkid));
			end

			if (fwbs_outstanding == fc_last_distance
						+ fc_ack + (ack_empty ? 0 :1))
				assume(ack_fifo_data & (1<<fc_checkid));
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// OPT_LOWPOWER
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_LOWPOWER)
	begin
		always @(*)
		if (!i_reset && !m_stb)
		begin
			assert(m_we   == 1'b0);
			assert(m_addr == {(AW){1'b0}});
			assert(m_data == {(DW){1'b0}});
			assert(m_sel  == {(DW/8){1'b0}});
		end

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!i_reset && fwbm_nreqs != fwbm_nacks)
		assume(m_cyc);

	always @(*)
	if (!i_reset && fwbs_nreqs != fwbs_nacks)
		assume(s_cyc[fc_checkid]);

	always @(*)
	if (!i_reset && m_cyc)
		assume(!m_err);

	always @(*)
	if (!i_reset)
		assert(err == 0);

	always @(*)
	if (!i_reset)
		assume(fc_checkid == 0);

`endif
// }}}
endmodule
