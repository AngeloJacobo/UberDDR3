////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/rtl/memdev.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file is really simple: it creates an on-chip memory,
//		accessible via the wishbone bus, that can be used in this
//	project.  The memory has single cycle pipeline access, although the
//	memory pipeline here still costs a cycle and there may be other cycles
//	lost between the ZipCPU (or whatever is the master of the bus) and this,
//	thus costing more cycles in access.  Either way, operations can be
//	pipelined for single cycle access on subsequent transactions.
//
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
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	memdev #(
		// {{{
		parameter	LGMEMSZ=15, DW=32, EXTRACLOCK= 1,
		parameter	HEXFILE="",
		parameter [0:0]	OPT_ROM = 1'b0,
		localparam	AW = LGMEMSZ - $clog2(DW/8)
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(AW-1):0]	i_wb_addr,
		input	wire	[(DW-1):0]	i_wb_data,
		input	wire	[(DW/8-1):0]	i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[(DW-1):0]	o_wb_data
		// }}}
	);

	// Local declarations
	// {{{
	wire			w_wstb, w_stb;
	wire	[(DW-1):0]	w_data;
	wire	[(AW-1):0]	w_addr;
	wire	[(DW/8-1):0]	w_sel;

	reg	[(DW-1):0]	mem	[0:((1<<AW)-1)];
	// }}}

	// Pre-load the memory
	// {{{
	generate if (HEXFILE != 0)
	begin : PRELOAD_MEMORY

		initial $readmemh(HEXFILE, mem);

	end endgenerate
	// }}}

	// Delay request if necessary
	// {{{
	generate if (EXTRACLOCK == 0)
	begin : NO_EXTRA_CLOCK
		// {{{
		assign	w_wstb = (i_wb_stb)&&(i_wb_we);
		assign	w_stb  = i_wb_stb;
		assign	w_addr = i_wb_addr;
		assign	w_data = i_wb_data;
		assign	w_sel  = i_wb_sel;
		// }}}
	end else begin : EXTRA_MEM_CLOCK_CYCLE
		// {{{
		reg			last_wstb, last_stb;
		reg	[(AW-1):0]	last_addr;
		reg	[(DW-1):0]	last_data;
		reg	[(DW/8-1):0]	last_sel;

		initial	last_wstb = 0;
		always @(posedge i_clk)
		if (i_reset)
			last_wstb <= 0;
		else
			last_wstb <= (i_wb_stb)&&(i_wb_we);

		initial	last_stb = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			last_stb <= 1'b0;
		else
			last_stb <= (i_wb_stb);

		always @(posedge i_clk)
			last_data <= i_wb_data;
		always @(posedge i_clk)
			last_addr <= i_wb_addr;
		always @(posedge i_clk)
			last_sel <= i_wb_sel;

		assign	w_wstb = last_wstb;
		assign	w_stb  = last_stb;
		assign	w_addr = last_addr;
		assign	w_data = last_data;
		assign	w_sel  = last_sel;
		// }}}
	end endgenerate
	// }}}

	// Read from memory
	// {{{
	always @(posedge i_clk)
		o_wb_data <= mem[w_addr];
	// }}}

	// Write to memory (if not a ROM)
	// {{{
	generate if (!OPT_ROM)
	begin : WRITE_TO_MEMORY
		// {{{
		integer	ik;

		always @(posedge i_clk)
		if (w_wstb)
		begin
			for(ik=0; ik<DW/8; ik=ik+1)
			if (w_sel[ik])
				mem[w_addr][ik*8 +: 8] <= w_data[ik*8 +: 8];
		end
`ifdef	VERILATOR
	end else begin : VERILATOR_ROM

		// Make Verilator happy
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	rom_unused;
		assign	rom_unused = &{ 1'b0, w_wstb, w_data, w_sel };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
`endif
		// }}}
	end endgenerate
	// }}}

	// o_wb_ack
	// {{{
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= (w_stb)&&(i_wb_cyc);
	// }}}

	assign	o_wb_stall = 1'b0;

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = { 1'b0 };
	// verilator lint_on UNUSED
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
	localparam	F_LGDEPTH = 2;
	reg			f_past_valid;
	wire	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;

	wire	[(AW-1):0]	f_addr;
	reg	[31:0]		f_data;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	fwb_slave #(
		.AW(AW), .DW(DW), .F_MAX_STALL(1), .F_MAX_ACK_DELAY(2),
		.F_OPT_DISCONTINUOUS(1), .F_LGDEPTH(F_LGDEPTH)
	) fwb(i_clk, i_reset, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr,
		i_wb_data, i_wb_sel, o_wb_ack, o_wb_stall, o_wb_data,
		1'b0, f_nreqs, f_nacks, f_outstanding);

	generate if (EXTRACLOCK)
	begin

		always @(posedge i_clk)
		if ((f_past_valid)&&(!i_reset)&&(i_wb_cyc)&&($past(i_wb_cyc)))
			assert((f_outstanding == 0)
				== ((!$past(w_stb))&&(!$past(i_wb_stb))));

		always @(posedge i_clk)
		if ((f_past_valid)&&(!i_reset)&&(i_wb_cyc))
			assert((f_outstanding == 1)
				== ( (($past(w_stb))&&($past(i_wb_cyc)))
					^($past(i_wb_stb))));

		always @(posedge i_clk)
		if ((f_past_valid)&&(!i_reset)&&(i_wb_cyc))
			assert((f_outstanding == 2'h2)
				== (($past(w_stb))&&($past(i_wb_cyc))
					&&($past(i_wb_stb))));

		always @(posedge i_clk)
			assert(f_outstanding <= 2);

	end else begin

		always @(posedge i_clk)
		if (f_outstanding > 0)
			assert(o_wb_ack);

		always @(posedge i_clk)
			assert(f_outstanding <= 1);
		always @(posedge i_clk)
		if ((f_past_valid)&&(!i_reset)&&(i_wb_cyc)&&($past(i_wb_stb)))
			assert(f_outstanding == 1);

	end endgenerate

	always @(*)
		assert(!o_wb_stall);

	assign	f_addr = $anyconst;
	initial	assume(mem[f_addr] == f_data);

	generate if (!OPT_ROM)
	begin : F_MATCH_WRITES
		integer	ik;

		always @(posedge i_clk)
		if (w_wstb && f_addr == w_addr)
		for(ik=0; ik < DW/8; ik=ik+1)
		if (w_sel[ik])
			f_data[ik * 8 +: 8] <= w_data[ik*8 +: 8];

	end endgenerate

	always @(*)
		assert(mem[f_addr] == f_data);

	always @(posedge i_clk)
	if ((f_past_valid)&&(OPT_ROM))
		assert($stable(f_data));

`endif
// }}}
endmodule
