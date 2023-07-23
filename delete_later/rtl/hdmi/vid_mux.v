////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vid_mux.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To select from among many potential video sources, and to do
//		so without ever losing video sync.  Hence, the source selection
//	must take place between frames, and remain AXI stream compliant.
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
module	vid_mux #(
		// {{{
		parameter	NIN = 5,
		parameter	LGDIM = 11,
		parameter	PW = 24,
		parameter	DEF_SELECT = 0,
		parameter [0:0]	OPT_TUSER_IS_SOF = 0
		// }}}
	) (
		// {{{
		input	wire			S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire	[NIN-1:0]	S_VID_VALID,
		output	reg	[NIN-1:0]	S_VID_READY,
		input	wire	[NIN*PW-1:0]	S_VID_DATA,
		input	wire	[NIN-1:0]	S_VID_LAST,	// HLAST
		input	wire	[NIN-1:0]	S_VID_USER,	// SOF
		//
		output	reg			M_VID_VALID,
		input	wire			M_VID_READY,
		output	reg	[PW-1:0]	M_VID_DATA,
		output	reg			M_VID_LAST,	// HLAST
		output	reg			M_VID_USER,	// SOF
		//
		input	wire	[$clog2(NIN)-1:0]	i_select
		// }}}
	);

	// local declarations
	// {{{
	localparam	LGNIN = $clog2(NIN);
	reg	[LGNIN-1:0]	r_framesel;
	reg				adjust_select;
	reg				M_VID_HLAST, M_VID_VLAST;
	wire	[NIN-1:0]		S_VID_HLAST, S_VID_VLAST, S_VID_SOF;
	wire	[NIN-1:0]		eof;
	reg	[NIN-1:0]		new_frame;
	genvar				gk;
	integer				ik;
	// }}}

	// r_framesel
	// {{{
	initial	r_framesel = ({ 1'b0, DEF_SELECT[LGNIN-1:0] } < NIN[LGNIN:0]) ? DEF_SELECT : 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_framesel <= ({ 1'b0, DEF_SELECT[LGNIN-1:0] } < NIN[LGNIN:0]) ? DEF_SELECT : 0;
	else if (adjust_select && { 1'b0, i_select } < NIN[LGNIN:0])
		r_framesel <= i_select;
	// }}}

	// M_VID_VALID
	// {{{
	always @(posedge  S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_VID_VALID <= 0;
	else if (!M_VID_VALID || M_VID_READY)
		M_VID_VALID <= S_VID_VALID[r_framesel]&&S_VID_READY[r_framesel];
	// }}}

	// M_VID_DATA
	// {{{
	always @(posedge  S_AXI_ACLK)
	if (!M_VID_VALID || M_VID_READY)
	begin
		for(ik=0; ik < NIN; ik=ik+1)
		if (r_framesel == ik[$clog2(NIN)-1:0])
			M_VID_DATA <= S_VID_DATA[ik * PW +: PW];
	end
	// }}}

	// M_VID_LAST, M_VID_USER, M_VID_HLAST, M_VID_VLAST
	// {{{
	always @(posedge  S_AXI_ACLK)
	if (!M_VID_VALID || M_VID_READY)
	begin
		M_VID_LAST  <= S_VID_LAST[r_framesel];
		M_VID_USER  <= S_VID_USER[r_framesel];
		M_VID_HLAST <= S_VID_HLAST[r_framesel];
		M_VID_VLAST <= S_VID_VLAST[r_framesel];
	end
	// }}}

	// adjust_select
	// {{{
	assign	eof = S_VID_VALID & S_VID_READY & S_VID_HLAST & S_VID_VLAST;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		adjust_select <= 1;
	else if (adjust_select)
	begin
		if ({ 1'b0, i_select } < NIN[LGNIN:0])
			adjust_select <= !new_frame[i_select];
	end else if (|(eof & (1<<r_framesel)))
	begin
		adjust_select <= (i_select != r_framesel)
				&& ({ 1'b0, i_select } < NIN[LGNIN:0]);
	end
	// }}}

	// S_VID_HLAST, S_VID_SOF, S_VID_READY
	// {{{
	generate for(gk=0; gk<NIN; gk=gk+1)
	begin
		if (OPT_TUSER_IS_SOF)
		begin
			// {{{
			reg	[LGDIM-1:0]	height, vpos;
			reg			vlast;

			assign	S_VID_HLAST[gk] = S_VID_LAST[gk];
			assign	S_VID_SOF[gk]   = S_VID_USER[gk];

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				vpos <= 0;
			else if (S_VID_VALID[gk] && S_VID_READY[gk])
			begin
				if (S_VID_SOF[gk])
				begin
					height <= vpos;
					vpos <= 0;
				end else if (S_VID_HLAST[gk])
					vpos <= vpos + 1;
			end

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				vlast <= 0;
			else if  (S_VID_VALID[gk] && S_VID_READY[gk])
				vlast <= S_VID_HLAST[gk]&& (height == vpos + 1);
			assign	S_VID_VLAST[gk] = vlast;
			// }}}
		end else begin
			// {{{
			reg	sof;

			assign	S_VID_HLAST[gk] = S_VID_USER[gk];
			assign	S_VID_VLAST[gk] = S_VID_LAST[gk];

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				sof <= 1'b1;
			else if (S_VID_VALID[gk] && S_VID_READY[gk])
				sof <= S_VID_HLAST[gk] && S_VID_VLAST[gk];

			assign	S_VID_SOF[gk] = sof;
			// }}}
		end

		initial	new_frame[gk] = 1'b1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			new_frame[gk] <= 1'b1;
		else if (S_VID_VALID[gk] && S_VID_READY[gk])
			new_frame[gk] <= S_VID_HLAST[gk] && S_VID_VLAST[gk];
		else if (S_VID_VALID[gk] && OPT_TUSER_IS_SOF)
			new_frame[gk] <= S_VID_SOF[gk];

		always @(*)
		if (adjust_select)
			S_VID_READY[gk] = 1'b0;
		else if (r_framesel == gk)
			S_VID_READY[gk] = !M_VID_VALID || M_VID_READY;
		else
			S_VID_READY[gk] = !new_frame[gk];

	end endgenerate
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;;
	assign	unused = &{ 1'b0, M_VID_HLAST, M_VID_VLAST };
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
	reg	f_past_valid;
	(* anyconst *)	wire	[LGDIM-1:0]	fm_width, fm_height;
	wire	[LGDIM-1:0]	fm_xpos, fm_ypos;
	wire			fm_known, fm_hlast, fm_vlast, fm_sof;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	////////////////////////////////////////////////////////////////////////
	//
	// Input stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate for(gk=0; gk<NIN; gk=gk+1)
	begin : FGEN_INPUTS;
		//parameter	LGDIM = 11,
		(* anyconst *)	reg	[LGDIM-1:0]	f_width, f_height;
		wire	[LGDIM-1:0]	f_xpos, f_ypos;
		wire			f_known, f_hlast, f_vlast, f_sof;

		always @(*)	assume(f_width  == fm_width);
		always @(*)	assume(f_height == fm_height);

		faxivideo #(
			// {{{
			.PW(PW), .LGDIM(LGDIM), .OPT_SOURCE(1'b0),
			.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
			// }}}
		) f_slv (
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
			//
			.S_VID_TVALID(S_VID_VALID[gk]),
				.S_VID_TREADY(S_VID_READY[gk]),
			.S_VID_TDATA(S_VID_DATA[gk*PW +: PW]),
			.S_VID_TLAST(S_VID_LAST[gk]),
			.S_VID_TUSER(S_VID_USER[gk]),
			.i_width(f_width), .i_height(f_height),
			.o_xpos(f_xpos), .o_ypos(f_ypos),
			.f_known_height(f_known),
			.o_hlast(f_hlast), .o_vlast(f_vlast), .o_sof(f_sof)
			// }}}
		);

		// Stream assumptions
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!f_past_valid || $past(!S_AXI_ARESETN))
		begin
			assume(!S_VID_VALID[gk]);
		end else if ($past(S_VID_VALID[gk] && !S_VID_READY[gk]))
		begin
			assume(S_VID_VALID[gk]);
			assume($stable(S_VID_DATA[gk*PW +: PW]));
			assume($stable(S_VID_LAST[gk]));
			assume($stable(S_VID_USER[gk]));
		end
		// }}}

		// Sync descriptors
		// {{{
		if (OPT_TUSER_IS_SOF)
		begin
			always @(*)
			if (S_VID_VALID[gk])
			begin
				assume(f_hlast == S_VID_LAST[gk]);
				assume(f_sof   == S_VID_USER[gk]);
			end
		end else begin
			always @(*)
			if (S_VID_VALID[gk])
			begin
				assume(f_hlast == S_VID_USER[gk]);
				assume((f_vlast && f_hlast) == S_VID_LAST[gk]);
			end
		end
		// }}}

		always @(*)
			assert(new_frame[gk]==((f_xpos == 0) && (f_ypos == 0)));

		always @(*)
		if (S_AXI_ARESETN && (r_framesel != gk || adjust_select))
			assert(new_frame[gk]);

		always @(*)
		if (S_AXI_ARESETN && r_framesel == gk)
		begin
			if (f_xpos == 0)
			begin
				if (M_VID_VALID)
				begin
					assert(fm_hlast);
				end else begin
					assert(fm_xpos == 0);
				end

				if (f_ypos == 0)
				begin
					assert((M_VID_VALID && fm_hlast && fm_vlast)
						||(fm_xpos == 0 && fm_ypos==0));
				end else if (M_VID_VALID)
				begin
					assert(f_ypos == fm_ypos + 1);
				end else begin
					assert(fm_ypos == f_ypos);
				end
			end else begin
				assert(f_xpos == fm_xpos + (M_VID_VALID ? 1:0));
				assert(f_ypos == fm_ypos);
				assert(!M_VID_VALID || !fm_hlast);
				assert(!M_VID_VALID || !fm_vlast || !fm_hlast);
			end

		end

		always @(*)
			assume(f_width >= 3 && f_height >= 1);
	end endgenerate
	//  }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output stream assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGDIM), .OPT_SOURCE(1'b0),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) f_master (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
		//
		.S_VID_TVALID(M_VID_VALID),
			.S_VID_TREADY(M_VID_READY),
		.S_VID_TDATA(M_VID_DATA),
		.S_VID_TLAST(M_VID_LAST),
		.S_VID_TUSER(M_VID_USER),
		.i_width(fm_width), .i_height(fm_height),
		.o_xpos(fm_xpos), .o_ypos(fm_ypos),
		.f_known_height(fm_known),
		.o_hlast(fm_hlast), .o_vlast(fm_vlast), .o_sof(fm_sof)
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN && M_VID_VALID)
	begin
		assert(M_VID_LAST == (fm_hlast && fm_vlast));
		assert(M_VID_USER == fm_hlast);
	end

	always @(*)
	if (S_AXI_ARESETN && adjust_select)
	begin
		if (M_VID_VALID)
		begin
			assert(M_VID_HLAST);
			if (!OPT_TUSER_IS_SOF)
				assert(M_VID_VLAST);
		end else begin
			assert(fm_xpos == 0);
			assert(fm_ypos == 0);
		end
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(r_framesel < NIN);

	// }}}
`endif
// }}}
endmodule
