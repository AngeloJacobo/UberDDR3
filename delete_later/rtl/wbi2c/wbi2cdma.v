////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbi2cdma.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This is a basic stream to memory DMA.  It's designed to work
//		with the I2C controller, where memory accesses are on a byte by
//	byte basis and rare.  Therefore there's no buffering, and stream data
//	is immediately written to memory as soon as its received.  Similarly,
//	since this is designed to write bytes, all bytes will be aligned by
//	nature.  If the stream width is increased beyond 8bits (a non-I2C
//	application), the address will need to remain aligned.
//
//	The design is activated as soon as a non-zero length is allotted to it.
//
//	On receiving a stream LAST, the current address will return to the
//	base address.
//
//	Registers:
//	0:	Control/Status
//		1:	Active.  Data has been received without receiving a
//			last.
//		0:	(Bus) Error.  The design is deactivated on an error.
//			Write a new base address or length to clear this bit.
//	1:	(Current address)
//		Almost.  The actual current address will return to the base
//		address once a LAST is received.  This address will increment
//		up to and including the LAST item.  Hence, if nothing has been
//		received, this will reflect the base address.  If LAST has been
//		received, then the difference between this and the base address
//		will be the length of data received.
//	2:	Base address (No alignment required)
//	3:	Allocated length (Byte alignment)
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
module	wbi2cdma #(
		// {{{
		parameter	AW = 28,
		parameter	DW = 32,
		parameter	SW = 8,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Control port
		// {{{
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[1:0]		i_wb_addr,
		input	wire	[31:0]		i_wb_data,
		input	wire	[3:0]		i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[31:0]		o_wb_data,
		// }}}
		// Stream port
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[SW-1:0]	S_DATA,
		input	wire			S_LAST,
		// }}}
		// DMA master port
		// {{{
		output	reg		o_dma_cyc, o_dma_stb,
		output	wire		o_dma_we,
		output	reg [AW-1:0]	o_dma_addr,
		output	reg [DW-1:0]	o_dma_data,
		output	reg [DW/8-1:0]	o_dma_sel,
		input	wire		i_dma_stall,
		input	wire		i_dma_ack,
		input	wire [DW-1:0]	i_dma_data,
		input	wire		i_dma_err
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	SUBLSB = $clog2(SW/8);
	localparam	WBLSB  = $clog2(DW/SW);
	localparam	ADDRESS_WIDTH = AW + WBLSB;

	reg	[ADDRESS_WIDTH-1:0]	r_baseaddr, r_memlen;
	reg	[WBLSB-1:0]		subaddr;
	reg	[ADDRESS_WIDTH-1:0]	current_addr;
	reg	[31:0]	next_baseaddr, next_memlen;
	reg			wb_last, bus_err, r_reset, r_overflow;

	wire			skd_valid, skd_ready, skd_last;
	wire	[SW-1:0]	skd_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Control
	// {{{
	////////////////////////////////////////////////////////////////////////

	always @(posedge i_clk)
	if (i_reset)
		bus_err <= 1'b0;
	else if (o_dma_cyc && i_dma_err)
		bus_err <= 1'b1;
	else if (i_wb_stb && !o_wb_stall && i_wb_we)
	case(i_wb_addr)
	2'b00: begin end // Control
	2'b01: begin end // Current address
	2'b10: bus_err <= bus_err && (i_wb_sel == 0);
	2'b11: bus_err <= bus_err && (i_wb_sel == 0);
	endcase

	always @(*)
	begin
		next_baseaddr = 0;
		next_baseaddr[ADDRESS_WIDTH-1:0] = r_baseaddr;
		next_baseaddr = next_baseaddr << SUBLSB;
		next_baseaddr = apply_strb(next_baseaddr, i_wb_sel, i_wb_data);
		next_baseaddr = next_baseaddr >> SUBLSB;

		next_memlen = 0;
		next_memlen[ADDRESS_WIDTH-1:0] = r_memlen;
		next_memlen = next_memlen << SUBLSB;
		next_memlen = apply_strb(next_memlen, i_wb_sel, i_wb_data);
		next_memlen = next_memlen >> SUBLSB;
	end

	initial	r_baseaddr = 0;
	initial	r_memlen   = 0;
	initial	r_reset    = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_baseaddr <= 0;
		r_memlen   <= 0;
		r_reset    <= 1;
	end else if (i_wb_stb && !o_wb_stall && i_wb_we)
	case(i_wb_addr)
	2'b00: begin end // Control
	2'b01: begin end // Current address
	2'b10: begin
		r_baseaddr <= next_baseaddr[ADDRESS_WIDTH-1:0];
		r_reset <= 1;
		end
	2'b11: begin
		r_memlen <= next_memlen[ADDRESS_WIDTH-1:0];
		r_reset <= 1;
		end
	endcase else if (!i_wb_cyc)
	begin
		r_reset <= (r_memlen == 0) || bus_err
			|| (r_baseaddr + r_memlen >= (1<<(AW+WBLSB)));
	end

	assign	o_wb_stall = 1'b0;

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb && !o_wb_stall;

	initial	o_wb_data = 0;
	always @(posedge i_clk)
	begin
		o_wb_data <= 32'h0;

		case(i_wb_addr)
		2'b00: begin
			o_wb_data[1] <= !wb_last
					&& (current_addr != r_baseaddr);
			o_wb_data[0] <= bus_err;
			end
		2'b01: o_wb_data[ADDRESS_WIDTH-1:0] <= current_addr;
		2'b10: o_wb_data[ADDRESS_WIDTH-1:0] <= r_baseaddr;
		2'b11: o_wb_data[ADDRESS_WIDTH-1:0] <= r_memlen;
		endcase

		if (OPT_LOWPOWER && (i_reset || !i_wb_stb
						|| !i_wb_we || i_wb_sel == 0))
			o_wb_data <= 0;
	end


	function automatic [31:0] apply_strb(input [31:0] old,
			input [ 3:0] strb,
			input [31:0] nxt);
	begin
		apply_strb[31:24] = (strb[3]) ? nxt[31:24] : old[31:24];
		apply_strb[23:16] = (strb[2]) ? nxt[23:16] : old[23:16];
		apply_strb[15: 8] = (strb[1]) ? nxt[15: 8] : old[15: 8];
		apply_strb[ 7: 0] = (strb[0]) ? nxt[ 7: 0] : old[ 7: 0];
	end endfunction

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stream processing
	// {{{
	////////////////////////////////////////////////////////////////////////

	skidbuffer #(
		.DW(1+SW), .OPT_LOWPOWER(OPT_LOWPOWER)
	) sskd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_valid(S_VALID), .o_ready(S_READY),
			.i_data({ S_LAST, S_DATA }),
		//
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data({ skd_last, skd_data })
		// }}}
	);

	assign	skd_ready = r_reset || bus_err || !o_dma_cyc;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// DMA
	// {{{
	////////////////////////////////////////////////////////////////////////

	assign	o_dma_we = 1'b1;

	initial	{ o_dma_cyc, o_dma_stb } = 2'b00;
	always @(posedge i_clk)
	if (i_reset || r_reset || bus_err || (o_dma_cyc && i_dma_err))
		{ o_dma_cyc, o_dma_stb } <= 2'b00;
	else if (o_dma_cyc)
	begin
		if (!i_dma_stall)
			o_dma_stb <= 1'b0;
		if (i_dma_ack)
			o_dma_cyc <= 1'b0;
	end else if (skd_valid)
	begin
		if (r_overflow && !wb_last)
			{ o_dma_cyc, o_dma_stb } <= 2'b00;
		else
			{ o_dma_cyc, o_dma_stb } <= 2'b11;
	end


	always @(posedge i_clk)
	if (r_reset)
		wb_last <= 1'b1;
	else if (skd_valid && skd_ready)
		wb_last <= skd_last;

	// o_dma_addr, subaddr
	// {{{
	always @(posedge i_clk)
	if (r_reset || bus_err)
		{ o_dma_addr, subaddr } <= r_baseaddr;
	else if ((!o_dma_stb || !i_dma_stall) && (wb_last || r_overflow))
		{ o_dma_addr, subaddr } <= r_baseaddr;
	else if (skd_valid && skd_ready && !r_overflow)
		{ o_dma_addr, subaddr } <= { o_dma_addr, subaddr } + 1;
	// }}}

	// r_overflow
	// {{{
	always @(posedge i_clk)
	if (r_reset)
		r_overflow <= 0;
	else if ((!o_dma_stb || !i_dma_stall) && wb_last)
		r_overflow <= 0;
	else if (skd_valid && skd_ready && skd_last)
		r_overflow <= 1'b0;
	else if (!r_overflow)
		r_overflow <= ({ o_dma_addr, subaddr } + 1 - r_baseaddr
					>= r_memlen);
	// }}}

	// o_dma_sel
	// {{{
	generate if (OPT_LITTLE_ENDIAN)
	begin : GEN_LILSEL
		always @(posedge i_clk)
		if (r_reset || bus_err)
			o_dma_sel <= { {(DW/8-1){1'b0}},1'b1 } << r_baseaddr[WBLSB-1:0];
		else if ((!o_dma_stb || !i_dma_stall) &&(wb_last || r_overflow))
			o_dma_sel <= { {(DW/8-1){1'b0}},1'b1 } << r_baseaddr[WBLSB-1:0];
		else if (skd_valid && skd_ready)
			o_dma_sel <= { o_dma_sel[(DW-SW)/8-1:0], o_dma_sel[DW/8-1: (DW-SW)/8] };
	end else begin : GEN_BIGSEL
		always @(posedge i_clk)
		if (r_reset || bus_err)
			o_dma_sel <= { 1'b1, {(DW/8-1){1'b0}} } >> r_baseaddr[WBLSB-1:0];
		else if ((!o_dma_stb || !i_dma_stall) && (wb_last || r_overflow))
			o_dma_sel <= { 1'b1, {(DW/8-1){1'b0}} } >> r_baseaddr[WBLSB-1:0];
		else if (skd_valid && skd_ready)
			o_dma_sel <= { o_dma_sel[SW/8-1:0], o_dma_sel[DW/8-1:SW/8] };
	end endgenerate
	// }}}

	// o_dma_data
	// {{{
	generate if (!OPT_LOWPOWER)
	begin : GEN_DATABLAST
		always @(posedge i_clk)
		if (skd_ready)
			o_dma_data <= {(DW/SW){skd_data }};

	end else if (OPT_LITTLE_ENDIAN)
	begin : GEN_LILDATA
		// {{{
		always @(posedge i_clk)
		if (r_reset || bus_err)
			o_dma_data <= 0;
		else if (skd_valid && skd_ready)
		begin
			if (wb_last)
				o_dma_data <= { {(DW-1){1'b0}},skd_data } << r_baseaddr[WBLSB-1:0]*SW;
			else
				o_dma_data <= { {(DW-1){1'b0}},skd_data } << subaddr*SW;
		end
		// }}}
	end else begin : GEN_BIGDATA
		always @(posedge i_clk)
		if (r_reset || bus_err)
			o_dma_data <= 0;
		else if (skd_valid && skd_ready)
		begin
			if (wb_last)
				o_dma_data <= { skd_data, {(DW-1){1'b0}} } >> r_baseaddr[WBLSB-1:0];
			else
				o_dma_data <= { skd_data, {(DW-1){1'b0}} } >> subaddr;
		end
	end endgenerate
	// }}}

	always @(posedge i_clk)
	if (r_reset)
		current_addr <= r_baseaddr;
	else if (o_dma_stb && !i_dma_stall)
		current_addr <= { o_dma_addr, subaddr } + 1;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_dma_data };
	// Verilator lint_on  UNUSED
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
	localparam	F_LGDEPTH=4, F_LGCOUNT=12;
	reg	f_past_valid;
	wire	[AW+WBLSB-1:0]	fdma_addr;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	assign	fdma_addr = { o_dma_addr, subaddr };

	////////////////////////////////////////////////////////////////////////
	//
	// Control port (WB slave) properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire	[1:0]	fwb_nreqs, fwb_nacks, fwb_noutstanding;

	fwb_slave #(
		.AW(2), .DW(32), .F_MAX_STALL(1), .F_MAX_ACK_DELAY(2),
		.F_LGDEPTH(2)
	) fslv (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb), .i_wb_we(i_wb_we),
			.i_wb_addr(i_wb_addr),
			.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
		.i_wb_stall(o_wb_stall),
		.i_wb_idata(o_wb_data),
		.i_wb_ack(o_wb_ack),
		.i_wb_err(1'b0),
		.f_nreqs(fwb_nreqs),
		.f_nacks(fwb_nacks),
		.f_outstanding(fwb_noutstanding)
		// }}}
	);

	always @(*)
	if (!i_reset && i_wb_cyc)
	begin
		assert(fwb_noutstanding == (o_wb_ack ? 1:0));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming stream assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[F_LGCOUNT-1:0]	s_count;

	always @(posedge i_clk)
	if (!f_past_valid)
		assume(!S_VALID);
	else if ($past(i_reset))
		assume(!S_VALID);
	else if ($past(S_VALID && !S_READY))
	begin
		assume(S_VALID);
		assume($stable(S_DATA));
		assume($stable(S_LAST));
	end

	always @(posedge i_clk)
	if (i_reset || r_reset)
		s_count <= 0;
	else if (skd_valid && skd_ready)
		s_count <= (skd_last) ? 0 : (s_count + 1);

	always @(*)
		assume(!(&s_count));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// DMA (WB master) properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire	[F_LGDEPTH-1:0]	fdma_nreqs, fdma_nacks, fdma_noutstanding;

	fwb_master #(
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH)
	) fdma (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(o_dma_cyc), .i_wb_stb(o_dma_stb), .i_wb_we(o_dma_we),
			.i_wb_addr(o_dma_addr),
			.i_wb_data(o_dma_data), .i_wb_sel(o_dma_sel),
		.i_wb_stall(i_dma_stall),
		.i_wb_idata(i_dma_data),
		.i_wb_ack(i_dma_ack),
		.i_wb_err(1'b0),
		.f_nreqs(fdma_nreqs),
		.f_nacks(fdma_nacks),
		.f_outstanding(fdma_noutstanding)
		// }}}
	);

	always @(posedge i_clk)
	if (o_dma_cyc)
	begin
		assert(fdma_nreqs == (o_dma_stb ? 0 : 1));
		assert(fdma_nacks == 0);
	end

	always @(posedge i_clk)
	if (!i_reset && !r_reset)
	begin
		assert($countones(o_dma_sel)==1);

		assert(wb_last == (s_count == 0));
		if (!bus_err && s_count != 0 && !r_overflow)
			assert(fdma_addr ==r_baseaddr + s_count-1);

		if (!r_overflow)
		begin
			assert(fdma_addr  >= r_baseaddr);
			assert(fdma_addr  < r_baseaddr + r_memlen);
		end
	end

	generate if (OPT_LITTLE_ENDIAN)
	begin : GEN_LITTLE_ENDIAN_SELCHECK
		always @(posedge i_clk)
		if (!i_reset && !r_reset && !bus_err)
			assert(o_dma_sel == ({{((DW-SW)/8){1'b0}},
				{(SW/8){1'b1}} } >> subaddr));
	end else begin : GEN_BIG_ENDIAN_SELCHECK
		always @(posedge i_clk)
		if (!i_reset && !r_reset && !bus_err)
			assert(o_dma_sel == ({{(SW/8){1'b1}},
					{((DW-SW)/8){1'b0}} } >> subaddr));
	end endgenerate

	always @(*)
	if (!i_reset && !r_reset)
	begin
		assert(r_memlen != 0);
		assert(r_memlen + r_baseaddr < (1<<(AW+WBLSB)));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg	[F_LGCOUNT-1:0]	fc_count;
	(* anyconst *)	reg	[SW-1:0]	fc_data;
	reg	[DW-1:0]	f_shifted;

	always @(*)
	if (s_count == fc_count)
		assume(skd_data == fc_data);

	generate if (OPT_LITTLE_ENDIAN)
	begin : GEN_LITTLE_ENDIAN_CONTRACT
		always @(*)
			f_shifted = o_dma_data >> subaddr * SW;

		always @(posedge i_clk)
		if (o_dma_stb && s_count == fc_count+1)
			assert(f_shifted[SW-1:0] == fc_data);
	end else begin : GEN_BIG_ENDIAN_CONTRACT
		always @(*)
			f_shifted = o_dma_data << subaddr*SW; 

		always @(posedge i_clk)
		if (o_dma_stb && s_count == fc_count+1)
			assert(f_shifted[DW-1:DW-SW] == fc_data);
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *) reg fcvr;
	always @(*)
	if (fcvr)
		assume(skd_last == (s_count == 7));

	always @(*)
		cover(o_dma_stb && wb_last && fcvr);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{

	// always @(*) assume(i_reset || r_reset || !r_overflow);
	// }}}
`endif	// FORMAL
// }}}
endmodule
