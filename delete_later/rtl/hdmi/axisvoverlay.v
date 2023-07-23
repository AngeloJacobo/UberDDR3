////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisvoverlay.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Overlay a second video stream on top of a first one, producing
//		an outgoing video stream.
//
// Inputs:
//	Primary video:
//		Can be from a camera or a memory/frame buffer driving a display.
//		The assumption is made that the speed can be controlled by
//		the downstream/output video port.  (i.e., hold READY high if
//		this is coming from a camera, or toggle it if/when the outgoing
//		display is/isn't ready.)
//	Secondary (overlay) video
//		May or may not be present.  Must be able to handle stalls, so
//		must be driven from memory.  The primary video and associated
//		output interface drives drive the speed of the interface.
//		The design will report an error if the secondary video ever
//		gets out of sync.
//
// Outputs:
//	Outgoing AXI Stream video stream
//		To be produced at all costs.
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
module	axisvoverlay #(
		// {{{
		// LGFRAME: Control the number of bits required in the two
		// {{{
		// position counters.  If there will never be more than 2047
		// horizontal positions, then this number never need be more
		// than 11.
		parameter	LGFRAME = 11,
		// }}}
		// ALPHA_BITS: Number of alpha bits in the overlay channel
		// {{{
		// If zero, the overlay will always replace the primary when
		// present.  If one, then the overlay will only replace the
		// primary when the alpha bit is 1.  If greater than 1, then
		// the alpha bits are used to scale both primary, by 1-alpha,
		// and overlay, by alpha, before summing the two together.
		// This allows the generation of a gradient effect if desired.
		parameter	ALPHA_BITS = 1,
		// }}}
		// COLORS: Number of color components to apply alpha mixing to
		// {{{
		// While you might think of this as nominally 3, REG+GRN+BLU,
		// it could be set to 6 (RGB, RGB), or even 9 (RGB, RGB, RGB),
		// if you want to share alpha across multiple pixels.
		parameter	COLORS = 3,
		// }}}
		// BITS_PER_PIXEL: Bits per color component
		// {{{
		parameter	BITS_PER_PIXEL = 8,
		localparam	BPP = BITS_PER_PIXEL,
		parameter	DATA_WIDTH = COLORS * BITS_PER_PIXEL,
		localparam	DW = DATA_WIDTH,
		// }}}
		// OPT_TUSER_IS_SOF: This is the normal video mode, as defined
		// {{{
		// by Xilinx's documentation.  TUSER = the start of frame
		// signal.  This makes TUSER true for the one pixel when
		// X = Y == 0.  TLAST is then used to reference the last item
		// in a line.  Set this to 1 for best compatibility with other
		// video cores for this reason.  Unfortunately, this makes
		// our processing below more challenging.  Therefore, I offer
		// another option: TLAST == the last pixel in the frame, when
		// X == WIDTH -1 && Y == HEIGHT-1.  This is easier to work with
		// internally, and requires less logic.  Both are tested.
		parameter [0:0]	OPT_TUSER_IS_SOF = 1'b1,
		// }}}
		// OPT_LINE_BREAK: If set, then we force READY to be low for
		// {{{
		// one clock cycle following every line break (HLAST).  This
		// allows our pointers to recover and the in_overlay flag to
		// be calculated with seven fewer logic operations on the
		// critical path between clock ticks.  This should help the
		// design pass timing in a high speed environment.
		parameter [0:0]	OPT_LINE_BREAK = 1'b0
		// }}}
		// }}}
	) (
		// {{{
		input	wire	ACLK, ARESETN,
		// Config inputs
		// {{{
		// i_enable: if true, apply the overlay to the primary channel
		// {{{
		input	wire		i_enable,
		// }}}
		// i_hpos, i_vpos: Describe the location of the top-left corner
		// {{{
		// of the overlay.  This will allow the overlay position to be
		// adjusted as necessary.  The design (currently) does not
		// allow the overlay to be positioned partially off screen to
		// either top or left, although running off screen to right or
		// bottom should be okay as long as there's enough bandwidth
		// to allow it.
		input	wire	[LGFRAME-1:0]	i_hpos, i_vpos,
		// }}}
		output	wire		o_err,
		// }}}
		// Primary video input
		// {{{
		input	wire			S_PRI_TVALID,
		output	wire			S_PRI_TREADY,
		input	wire	[DW-1:0]	S_PRI_TDATA,
		input	wire			S_PRI_TLAST,	// HLAST
		input	wire			S_PRI_TUSER,	// SOF
		// }}}
		// Secondary (overlap) video input
		// {{{
		input	wire			S_OVW_TVALID,
		output	wire			S_OVW_TREADY,
		input wire [DW+ALPHA_BITS-1:0]	S_OVW_TDATA,
		input	wire			S_OVW_TLAST,	// HLAST
		input	wire			S_OVW_TUSER,	// SOF
		// }}}
		// Video output
		// {{{
		output	reg			M_VID_TVALID,
		input	wire			M_VID_TREADY,
		output	reg	[DW-1:0]	M_VID_TDATA,
		output	reg			M_VID_TLAST,	// HLAST
		output	reg			M_VID_TUSER	// SOF
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam [ALPHA_BITS:0]	// OPAQUE = (1<<ALPHA_BITS),
					TRANSPARENT = 0;

	wire			pskd_tuser, pskd_tlast, pskd_ready, pskd_valid,
				pskd_vlast, pskd_hlast, pskd_sof;
	wire	[DW-1:0]	pskd_data;

	wire			ovskd_tuser, ovskd_tlast, ovskd_ready,
				ovskd_vlast, ovskd_hlast, ovskd_sof,
				ovskd_valid;
	wire [ALPHA_BITS+DW-1:0]	ovskd_data;
	reg			pix_line_pause, ov_line_pause;

	reg	[LGFRAME-1:0]	prhpos, prvpos;
	reg	[LGFRAME-1:0]	ovhpos, ovvpos;
	wire	[LGFRAME-1:0]	lines_per_frame;

	reg	in_overlay, in_frame, frame_err, ovw_eof, ovw_eol;

	wire	pix_loaded;
	wire	pix_ready;

	wire	mpy_loaded, mpy_ready;
	wire	mix_valid, mix_ready, mix_hlast, mix_vlast, mix_sof;

	wire	[DW-1:0]	mix_pixel;
`ifdef	FORMAL
	(* anyconst *)	reg	[LGFRAME-1:0]	f_vid_width, f_vid_height;
	(* anyconst *)	reg	[LGFRAME-1:0]	f_ovw_width, f_ovw_height;
	reg	[LGFRAME-1:0]	f_pri_hpos, f_pri_vpos;
	reg	[LGFRAME-1:0]	f_ovw_hpos, f_ovw_vpos;
	reg	[LGFRAME-1:0]	f_vid_hpos, f_vid_vpos;
	reg	[LGFRAME-1:0]	f_pskd_hpos, f_pskd_vpos;
	reg	[LGFRAME-1:0]	f_mix_hpos, f_mix_vpos;
	wire			f_pri_known, f_ovw_known;
	wire	[LGFRAME-1:0]	f_ovw_lines_per_frame;
	wire			f_mix_err;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pixel skid buffers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		.DW(DW+2), .OPT_OUTREG(0)
`ifdef	FORMAL
		, .OPT_PASSTHROUGH(1)
`endif
	) primary_skid (
		// {{{
		.i_clk(ACLK), .i_reset(!ARESETN),
		.i_valid(S_PRI_TVALID), .o_ready(S_PRI_TREADY),
			.i_data({ S_PRI_TDATA, S_PRI_TLAST, S_PRI_TUSER }),
		.o_valid(pskd_valid), .i_ready(pskd_ready),
			.o_data({ pskd_data, pskd_tlast, pskd_tuser })
		// }}}
	);

	skidbuffer #(
		.DW(DW+ALPHA_BITS+2), .OPT_OUTREG(0)
`ifdef	FORMAL
		, .OPT_PASSTHROUGH(1)
`endif
	) overlay_skid (
		// {{{
		.i_clk(ACLK), .i_reset(!ARESETN),
		.i_valid(S_OVW_TVALID), .o_ready(S_OVW_TREADY),
			.i_data({ S_OVW_TDATA, S_OVW_TLAST, S_OVW_TUSER }),
		.o_valid(ovskd_valid), .i_ready(ovskd_ready),
			.o_data({ ovskd_data, ovskd_tlast, ovskd_tuser })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming frame counters, VLAST/SOF insertion
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// VLAST, HLAST, SOF
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : GEN_VLAST
		// {{{
		reg			p_vlast, ov_vlast;
		reg	[LGFRAME-1:0]	ovw_lines, vcount, ovcount, r_lines;

		assign	pskd_sof   = pskd_tuser;
		assign	pskd_hlast = pskd_tlast;
		assign	pskd_vlast = p_vlast && pskd_hlast;
		assign	lines_per_frame = r_lines;

		// vcount, lines_per_frame, p_vlast
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			p_vlast <= 0;
			vcount  <= 0;
			r_lines <= 0;
		end else if (pskd_valid && pskd_ready)
		begin
			if (pskd_sof)
			begin
				r_lines <= vcount;
				vcount <= 0;
			end

			if (pskd_hlast)
			begin
				vcount <= vcount + 1;
				p_vlast <= (vcount == lines_per_frame - 2);
				if (lines_per_frame == 0)
					p_vlast <= 0;
			end
		end
		// }}}

		assign	ovskd_sof   = ovskd_tuser;
		assign	ovskd_hlast = ovskd_tlast;
		assign	ovskd_vlast = ov_vlast && ovskd_hlast;

		// ovcount, ovw_lines, ovskd_vlast
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			ov_vlast <= 0;
			ovcount     <= 0;
			ovw_lines   <= 0;
		end else if (ovskd_valid && ovskd_ready)
		begin
			if (ovskd_sof)
			begin
				ovw_lines <= ovcount;
				ovcount <= 0;
			end

			if (ovskd_hlast)
			begin
				ovcount  <=  ovcount + 1;
				ov_vlast <= (ovcount + 2 == ovw_lines);
			end
		end
		// }}}
`ifdef	FORMAL
		// {{{
		assign	f_ovw_lines_per_frame = ovw_lines;
		always @(*)
		if (ARESETN)
		begin
			assert((r_lines == 0) || (r_lines == f_vid_height));

			if (f_pri_sof && (vcount != 0 || r_lines != 0))
			begin
				assert(vcount == f_vid_height);
			end

			// Primary tracking
			if (r_lines == 0)
			begin
				assert(!p_vlast);
				assert(!f_pri_known
					|| (f_pri_sof && (vcount == f_vid_height)));
			end else begin
				assert(f_pri_known);
				assert(r_lines == f_vid_height);
				assert(p_vlast == (f_pri_vpos == f_vid_height-1));
			end

			if (vcount < f_vid_height)
			begin
				assert(f_pri_vpos == vcount);
				assert(prvpos == f_pri_vpos
					|| (f_pri_sof && prvpos == f_vid_height));
			end else begin
				assert(vcount == f_vid_height);
				assert(!p_vlast);
				assert(f_pri_sof);
				assert(f_pri_known);
			end
		end

		always @(*)
		if (ARESETN)
		begin
			if (ovw_lines != 0)
				assert(ovw_lines == f_ovw_height);
			assert((ovw_lines == 0) || (ovw_lines == f_ovw_height));
			if (f_ovw_known)
			begin
				assert(ov_vlast == (f_ovw_vpos == f_ovw_height-1));
				if (!f_ovw_sof)
					assert(ovw_lines== f_ovw_height);
				else begin
					assert(ovcount == f_ovw_height);
					assert(ovw_lines == 0
						|| ovw_lines == f_ovw_height);
				end
			end else
				assert(!ov_vlast);

			if (f_ovw_known && f_ovw_sof)
				assert(ovcount == f_ovw_height);
			if (f_ovw_vpos != ovcount)
				assert(ovcount == f_ovw_height && f_ovw_sof
						&& f_ovw_known);

			if (ovw_lines == 0)
			begin
				assert(!f_ovw_known
					||(f_ovw_sof && ovcount == f_ovw_height));
				assert(!ov_vlast);
			end else begin
				assert(f_ovw_known);
				assert(ovw_lines == f_ovw_height);
				assert(ov_vlast == (f_ovw_vpos == f_ovw_height-1));
			end

			if (f_ovw_known && ovw_lines == f_ovw_height)
			begin
				assert(ovvpos  == f_ovw_vpos);
				assert(ovw_eof == f_ovw_sof);
			end else
				assert(ovw_lines == 0);
		end
		// }}}
`endif
		// }}}
	end else begin : GEN_SOF
		// {{{
		reg			p_sof, ov_sof;

		assign	pskd_vlast = pskd_tlast && pskd_tuser;
		assign	pskd_hlast = pskd_tuser;
		assign	pskd_sof   = p_sof;
		assign	lines_per_frame = 0;	// A dummy value

		// p_sof
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
			p_sof <= 1;
		else if (pskd_valid && pskd_ready)
			p_sof <= pskd_tlast && pskd_tuser;
		// }}}

		assign	ovskd_vlast = ovskd_tlast && ovskd_tuser;
		assign	ovskd_hlast = ovskd_tuser;
		assign	ovskd_sof   = ov_sof;

		// ov_sof
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
			ov_sof <= 1;
		else if (ovskd_valid && ovskd_ready)
			ov_sof <= ovskd_tlast && ovskd_tuser;
		// }}}
`ifdef	FORMAL
		assign	f_ovw_lines_per_frame = f_ovw_height;
		always @(*)
		if (ARESETN)
		begin
			assert(pskd_sof == ((f_pri_hpos == 0) && (f_pri_vpos  == 0)));
			assert(ovskd_sof == ((f_ovw_hpos == 0) && (f_ovw_vpos  == 0)));
			assert(prvpos  == f_pskd_vpos);
			assert(ovw_eof == f_ovw_sof);
			assert(ovvpos  == f_ovw_vpos);
		end
`endif
		// }}}
	end endgenerate
	// }}}

	// prhpos, prvpos
	//  {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		prhpos <= 0;
		prvpos <= 0;
	end else if (pskd_valid && pskd_ready)
	begin
		if (pskd_hlast)
		begin
			prhpos <= 0;
			prvpos <= prvpos + 1;
			if (pskd_vlast)
				prvpos <= 0;
		end else
			prhpos <= prhpos + 1;

		if (pskd_vlast || pskd_sof)
			prvpos <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (ARESETN)
	begin
		assert(prhpos == f_pskd_hpos);
		if (!f_pskd_sof)
			assert(f_pskd_vpos == prvpos);
		else if (f_pskd_known)
		begin
			if (lines_per_frame == 0)
			begin
				assert(!OPT_TUSER_IS_SOF
					|| prvpos == f_vid_height);
			end else
				assert(prvpos == 0);
		end

		if (prvpos < f_vid_height)
		begin
			assert(prvpos == f_pskd_vpos);
		end else if (prvpos != f_pskd_vpos)
		begin
			assert(!f_pri_known
				|| (f_pri_sof && prvpos == f_vid_height));
			assert(prvpos == f_vid_height);
			assert(f_pskd_vpos == 0);
			assert(prhpos == 0);
		end
	end
`endif
	// }}}

	// ovhpos, ovvpos
	//  {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		ovhpos <= 0;
		ovvpos <= 0;
	end else if (ovskd_valid && ovskd_ready)
	begin
		if (ovskd_sof)
			ovvpos <= 0;
		if (ovskd_hlast)
		begin
			ovhpos <= 0;
			ovvpos <= ovvpos + 1;
			if (ovskd_vlast)
				ovvpos <= 0;
		end else
			ovhpos <= ovhpos + 1;
	end
`ifdef	FORMAL
	// {{{
	always @(*)
	if (ARESETN)
	begin
		assert(ovhpos == f_ovw_hpos);
		assert(ovvpos == f_ovw_vpos
			|| (ovvpos == f_ovw_height && f_ovw_sof && f_ovw_known));
		if (ovskd_valid)
			assert(ovskd_hlast == (f_ovw_hpos == f_ovw_width-1));
	end
	// }}}
`endif
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) line breaks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge ACLK)
	if (!ARESETN || !OPT_LINE_BREAK)
		pix_line_pause <= 1'b0;
	else
		pix_line_pause <= pskd_valid && pskd_ready && pskd_hlast;

	always @(posedge ACLK)
	if (!ARESETN || !OPT_LINE_BREAK)
		ov_line_pause <= 1'b0;
	else
		ov_line_pause <= ovskd_valid && ovskd_ready && ovskd_hlast;

`ifdef	FORMAL
	always @(*)
	if (ARESETN)
	begin
		if (!OPT_LINE_BREAK || f_pskd_hpos != 0)
			assert(!pix_line_pause);
		if (!OPT_LINE_BREAK || f_ovw_hpos != 0)
			assert(!ov_line_pause);
	end
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Overlay flags: in_overlay, o_err, frame_err, ovw_eof, ovw_eol
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// ovw_eof, ovw_eol
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		ovw_eof    <= !OPT_TUSER_IS_SOF;
		ovw_eol    <= 1;
	end else if (ovskd_valid && ovskd_ready)
	begin
		ovw_eol <= ovskd_hlast;
		ovw_eof <= ovskd_hlast && ovskd_vlast;
	end
`ifdef	FORMAL
	always @(*)
	if (ARESETN)
	begin
		assert(ovw_eol == (f_ovw_hpos == 0));
		if (ovw_eof)
			assert(ovw_eol);
		//
		// ovw_eof is checked in the big generate block above
		// if (f_ovw_known)
		//	assert(ovw_eof == f_ovw_sof);
	end
`endif
	// }}}

	// in_frame -- y-handling
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
		in_frame <= 0;
	else begin
		if (in_frame && ovskd_valid && ovskd_ready && ovskd_vlast
			&& ((prvpos > i_vpos)
				||(prvpos == i_vpos && prhpos > i_hpos)))
			in_frame <= 0;

		if (pskd_valid && pskd_ready)
		begin
			if (pskd_vlast)
				in_frame <= (i_vpos == 0);
			else if (pskd_hlast && !in_frame)
				in_frame <= (i_vpos == prvpos + 1);
		end
	end
`ifdef	FORMAL
	// {{{
	always @(posedge ACLK)
	if (ARESETN && !frame_err)
	begin
		if (ovw_eof && f_pri_vpos != i_vpos)
			assert(!in_frame || (i_hpos >= f_vid_width));
	end

	always @(posedge ACLK)
	if (ARESETN && !frame_err // && !w_frame_err
		&& (f_pri_known && $past(f_pri_known))
		&& (f_ovw_known && $past(f_ovw_known)
				&& !f_ovw_sof && !$past(f_ovw_sof)
				&& (lines_per_frame != 0)
				&& $stable(lines_per_frame))
			)
	begin
		if (in_overlay)
			assert(in_frame);

		if (f_pri_vpos < i_vpos)
		begin
			assert(!in_frame);
		end else if (f_pri_vpos
				>= { 1'b0, i_vpos } + { 1'b0, f_ovw_height })
		begin
			// Was ... if (f_sum_ypos != prvpos)
			assert(!in_frame
				// It is possible that we passed the end of the
				// primary line, but not (yet) the end of the
				// overlay line.  In this case, we'd be on the
				// last overline of the overlay frame, and we
				// wouldn't have come across the EOL yet.
				|| ((f_pri_vpos == { 1'b0, i_vpos }
						+ { 1'b0, f_ovw_height })
					&& !ovw_eol));
		end else if ({ 1'b0, f_pri_vpos } + 1
				== { 1'b0, i_vpos }+{ 1'b0, f_ovw_height })
		begin
			assert(in_frame != ovw_eof);
		end else begin
			assert(in_frame);
		end
	end
	// }}}
`endif
	// }}}

	// in_overlay
	// {{{
	always @(posedge ACLK)
	if (!ARESETN)
		in_overlay <= 0;
	else if (pskd_valid && pskd_ready)
	begin
		if (pskd_vlast)
			in_overlay <= (i_hpos == 0) && (i_vpos == 0);
		else if (pskd_hlast)
		begin
			in_overlay <= 0;
			if (in_frame && !ovw_eof)
				in_overlay <= !ovskd_vlast;
			if (i_vpos == prvpos + 1)
				in_overlay <= 1'b1;

			if (i_hpos != 0)
				in_overlay <= 0;
		end else if (ovskd_hlast && in_overlay)
			in_overlay <= 0;
		else if (prhpos + 1 == i_hpos)
			in_overlay <= in_frame;
	end

`ifdef	FORMAL
	// {{{
	(* keep *) reg	[LGFRAME:0]	f_sum_xpos, f_sum_ypos;
	always @(*)
	begin
		f_sum_xpos = { 1'b0, i_hpos } + { 1'b0, f_ovw_hpos };
		f_sum_ypos = { 1'b0, i_vpos } + { 1'b0, f_ovw_vpos };
	end

	always @(posedge ACLK)
	if (ARESETN && !frame_err)
	begin
		if (f_pri_hpos != i_hpos && ovw_eol)
			assert(!in_overlay);

		if (in_overlay && (f_pri_hpos != i_hpos || !w_frame_err))
			assert(f_pri_hpos == f_sum_xpos);

		if ((f_pri_hpos < i_hpos)
				|| f_pri_hpos >= { 1'b0, i_hpos }
						+ { 1'b0, f_ovw_width })
		begin
			assert(!in_overlay);
		end else if (!in_frame && f_pri_vpos > i_vpos)
		begin
			assert(!in_overlay);
		end else if (f_pri_vpos < i_vpos)
		begin
			assert(!in_overlay);
		end

		if (ovw_eof && (f_pri_vpos == i_vpos)
				&& (f_pri_hpos > { 1'b0, i_hpos }))
			assert(!in_frame);
	end

	always @(posedge ACLK)
	if (ARESETN && !frame_err && !w_frame_err)
	begin
		if (f_pri_hpos != i_hpos && ovw_eol)
			assert(!in_overlay);

		if ((f_pri_hpos < i_hpos)
				|| f_pri_hpos >= { 1'b0, i_hpos }
						+ { 1'b0, f_ovw_width })
		begin
			// Was ... if (f_sum_xpos != { 1'b0, f_pri_hpos })
			assert(!in_overlay);
		end else if (!in_frame && f_pri_vpos > i_vpos)
		begin
			assert(!in_overlay);
		end else if (f_pri_vpos < i_vpos)
		begin
			assert(!in_overlay);
		end else if (in_frame)
		begin
			assert(in_overlay);
		end
	end
	// }}}
`endif
	// }}}

	// o_err, frame_err
	// {{{
	reg	w_frame_err;

	always @(*)
	begin
		w_frame_err = 1'b0;
		if (in_overlay)
			w_frame_err = (!ovskd_valid || !ovskd_ready);
		else begin
			// if (prhpos >= i_hpos && !ovw_eol)
			//	w_frame_err = 1;
			// if (prvpos >= i_vpos && !ovw_eof)
			//	w_frame_err = 1;
		end

		if (prhpos == i_hpos)
		begin
			if (!ovw_eol)
				w_frame_err = 1;
			if (prvpos == i_vpos && !ovw_eof)
				w_frame_err = 1;
		end
	end

	initial	frame_err = OPT_TUSER_IS_SOF;
	always @(posedge ACLK)
	if (!ARESETN)
	begin
		frame_err <= OPT_TUSER_IS_SOF;
	end else if (!frame_err && pskd_valid && pskd_ready)
	begin
		frame_err <= w_frame_err;
	end else if ((ovw_eof || ovskd_valid && ovskd_ready && ovskd_vlast)
			&& ((pskd_valid && pskd_ready && pskd_vlast)
				|| (prvpos < i_vpos)))
	begin
		frame_err <= 0;
	end

	assign	o_err = frame_err && i_enable;
`ifdef	FORMAL
			reg		f_ovw_recovering,
					f_ovw_final_line,
					f_offscreen;
	(* keep *)	reg	[3:0]	f_region;

	always @(*)
	begin
		f_ovw_final_line = 0;
		if (((f_sum_ypos + 1 == f_vid_height)
					|| (f_ovw_vpos + 1 == f_ovw_height))
				&& (f_sum_xpos >= f_vid_width))
			f_ovw_final_line = 1;

		f_ovw_recovering = f_ovw_final_line;
		if (f_ovw_vpos + i_vpos >= f_vid_height)
			f_ovw_recovering = 1;

		f_offscreen = (i_hpos >= f_vid_width);
	end

	always @(posedge ACLK)
	if (ARESETN && $past(ARESETN))
	begin
		if (f_pri_hpos < i_hpos)
		begin
			// Left column
			// {{{
			assert(!in_overlay);

			if (f_pri_vpos < i_vpos)
			begin // #0: Top left corner
				// {{{
				f_region <= 0;
				assert(!in_frame);
				assert(frame_err|| ovw_eof || f_ovw_recovering);
				// }}}
			end else if (f_pri_vpos < { 1'b0, i_vpos } + {1'b0, f_ovw_height})
			begin // #4: Left of overlay area
				// {{{
				f_region <= 4;
				if (f_pri_vpos == i_vpos)
					assert(frame_err || in_frame);

				if (in_frame && !frame_err)
				begin
					if (f_pri_vpos == i_vpos)
					begin
						assert(ovw_eof	// !!!
							|| f_ovw_recovering);
					end else if (ovw_eol)
					begin
						assert(f_pri_vpos== f_sum_ypos
							|| f_offscreen);
					end else if (ovw_eof)
					begin
						assert(f_pri_vpos == i_vpos);
					end else if (f_pri_vpos == i_vpos)
					begin
						assert(f_ovw_recovering);
					end else if (f_pri_vpos > i_vpos)
					begin
						assert(f_sum_ypos + 1
								== f_pri_vpos);
					end
				end
				// }}}
			end else begin // #8: Below the overlay area
				// {{{
				f_region <= 8;
				assert(frame_err || !in_frame
					|| i_hpos >= f_vid_width
					|| f_ovw_final_line);	// !!!
				if (!frame_err)
				begin
					assert(ovw_eof || f_offscreen
						|| (!ovw_eol && f_ovw_final_line));
				end
				// }}}
			end
			// }}}
		end else if (f_pri_hpos < { 1'b0, i_hpos }+{ 1'b0, f_ovw_width})
		begin
			// Center column
			// {{{
			if (f_pri_vpos < i_vpos)
			begin
				assert(!in_frame);

				// #1: Top middle section
				f_region <= 1;
				assert(frame_err|| ovw_eof || f_ovw_recovering);
			end else if (f_pri_vpos < { 1'b0, i_vpos } + {1'b0, f_ovw_height})
			begin // #5: Valid middle section
				// {{{
				f_region <= 5;
				if (!frame_err)
				begin
					assert(in_frame);
					assert(in_overlay);
					if (ovw_eof)
					begin
						assert(f_pri_vpos == i_vpos
							&&f_pri_hpos == i_hpos);
					end

					if (ovw_eol)
					begin
						assert(f_pri_hpos == i_hpos);
					end

					if (f_sum_xpos != f_pri_hpos)
					begin
						assert(w_frame_err);
						assert(f_pri_hpos == i_hpos
							&& !ovw_eol);
					end

					if (f_sum_ypos != f_pri_vpos)
					begin
						assert(w_frame_err);
						assert(!ovw_eol
							|| (f_pri_vpos == i_vpos
								&& f_ovw_recovering));
					end
				end
				// }}}
			end else begin
				// #9: Bottom center section
				f_region <= 9;
				assert(frame_err || !in_frame
					|| (!ovw_eol && f_ovw_final_line));
				assert(frame_err || ovw_eof || f_offscreen
					|| (!ovw_eol && f_ovw_final_line));
			end
			// }}}
		end else begin
			// Right column
			// {{{
			assert(frame_err || !in_overlay);

			if (f_pri_vpos < i_vpos)
			begin // #2: Top right corner
				// {{{
				f_region <= 2;
				assert(frame_err|| ovw_eof || f_ovw_recovering);
				// }}}
			end else if (f_pri_vpos < { 1'b0, i_vpos } + {1'b0, f_ovw_height})
			begin // #6: Right of overlay area
				// {{{
				f_region <= 6;
				assert(frame_err || ovw_eol);
				assert(frame_err || in_frame
					|| (f_pri_vpos + 1 == { 1'b0, i_vpos } + { 1'b0, f_ovw_height }));
				// }}}
			end else begin // #10: Bottom right corner
				// {{{
				f_region <= 10;
				assert(frame_err || ovw_eof || f_offscreen
					|| (!ovw_eol && f_ovw_vpos + 1 == f_ovw_height
						&& f_ovw_hpos + i_hpos >= f_vid_width));
				assert(frame_err || !in_frame);
				// }}}
			end
			// }}}
		end
	end else
		f_region <= 12;

	always @(posedge ACLK)
	if (ARESETN && $past(ARESETN) && !ovw_eof)
	begin
		if (f_pri_vpos >= i_vpos
				&& f_pri_vpos != f_sum_ypos)
		begin
			if (f_pri_hpos >= i_hpos
				&& f_pri_hpos != f_sum_xpos)
			begin
				assert(ovw_eol || frame_err || w_frame_err);
			end
		end

		/*
		if (f_pri_vpos > i_vpos // && !ovw_eof
			&& ((ovw_eol && f_pri_hpos <= i_hpos
					&& f_pri_vpos != f_sum_ypos)
				|| (!ovw_eol && f_pri_hpos <= i_hpos
					&& f_pri_vpos != f_sum_ypos + 1)
				|| (!ovw_eol && f_pri_hpos > i_hpos
					&& f_pri_vpos != f_sum_ypos)
				))
			assert(frame_err || w_frame_err);
		*/
	end

	always @(posedge ACLK)
	if (ARESETN && OPT_TUSER_IS_SOF)
	begin
		if (!f_pri_known || lines_per_frame == 0)
			assert(frame_err);
		if (!f_ovw_known || f_ovw_lines_per_frame == 0)
			assert(frame_err);
		if (ovw_eof)
			assert(f_ovw_lines_per_frame != 0);
	end
`endif
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Mix the two channels together
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// mix_pixel
	// {{{
	generate if (ALPHA_BITS == 0)
	begin : NO_ALPHA
		// {{{
		reg	[DW-1:0]	r_mix_pixel;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			r_mix_pixel <= pskd_data;
			if (in_overlay && ovskd_valid && !frame_err
					&& i_enable)
				r_mix_pixel <= ovskd_data;
		end

		assign	mix_pixel = r_mix_pixel;
		// }}}
	end else if (ALPHA_BITS == 1)
	begin: ALPHA_MASK
		// {{{
		reg	[DW-1:0]	r_mix_pixel;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			r_mix_pixel <= pskd_data;
			if (in_overlay && ovskd_valid && i_enable
					&& !frame_err && ovskd_data[DW])
				r_mix_pixel <= ovskd_data[DW-1:0];
		end

		assign	mix_pixel = r_mix_pixel;
		// }}}
	end else begin : ALPHA_MIXING
		// {{{
		genvar	clr;
		reg	[ALPHA_BITS:0]	alpha, negalpha;
		reg	[DW-1:0]	pri_pixel, ovw_pixel;

		// pri_pixel, ovw_pixel
		// {{{
		always @(posedge ACLK)
		if (!ARESETN)
		begin
			pri_pixel <= 0;
			ovw_pixel <= 0;
			alpha     <= TRANSPARENT;
		end else if (pskd_valid && pskd_ready)
		begin
			pri_pixel <= pskd_data;
			ovw_pixel <= ovskd_data[DW-1:0];
			// Verilator lint_off WIDTH
			alpha     <= ovskd_data[ALPHA_BITS + DW-1 : DW]
					+ ovskd_data[ALPHA_BITS + DW-1];
			negalpha  <= (1<<ALPHA_BITS)
					- ovskd_data[ALPHA_BITS + DW-1 : DW]
					- ovskd_data[ALPHA_BITS + DW-1];
			// Verilator lint_on  WIDTH
			if (!ovskd_valid || frame_err || !in_overlay
							|| !i_enable)
			begin
				ovw_pixel <= 0;
				alpha     <= TRANSPARENT;
			end
		end
		// }}}

		// mix_pixel
		// {{{
		for(clr=0; clr<COLORS; clr=clr+1)
		begin : MIXCLR
			// Verilator lint_off UNUSED
			reg	[BPP + ALPHA_BITS:0] pclr, oclr, sclr;
			wire	[BPP-1:0] pri_clr, ovw_clr;

			assign	pri_clr = pri_pixel[clr * BPP +: BPP];
			assign	ovw_clr = ovw_pixel[clr * BPP +: BPP];
			// Verilator lint_on  UNUSED

			always @(posedge ACLK)
			if (pix_loaded && pix_ready)
				pclr <= pri_clr * alpha;

			always @(posedge ACLK)
			if (pix_loaded && pix_ready)
				oclr <= ovw_clr * negalpha;

			always @(posedge ACLK)
			if (mpy_loaded && mpy_ready)
				sclr <= pclr + oclr;

			assign	mix_pixel[clr * BPP +: BPP] = sclr[ALPHA_BITS +: BPP];
		end
		// }}}
		// }}}
	end endgenerate
	// }}}

	// mix_valid, mix_hlast, mix_vlast, mix_sof
	// {{{
	generate if (ALPHA_BITS <= 1)
	begin : NO_ALPHA_PIPELINE
		assign	pskd_ready = !pix_line_pause
				&&(!mix_valid || mix_ready);
		// {{{
		reg	r_mix_sof, r_mix_valid, r_mix_hlast, r_mix_vlast;

		// r_mix_valid
		// {{{
		initial	r_mix_valid = 0;
		always @(posedge ACLK)
		if (!ARESETN)
			r_mix_valid <= 1'b0;
		else if (pskd_valid && pskd_ready)
			r_mix_valid <= 1'b1;
		else if (mix_ready)
			r_mix_valid <= 1'b0;
		// }}}

		// r_mix_[vh]last, r_mix_sof
		// {{{
		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			r_mix_hlast <= pskd_hlast;
			r_mix_vlast <= pskd_vlast;
			r_mix_sof   <= pskd_sof;
		end
		// }}}

		// mix_*
		// {{{
		assign	mix_valid = r_mix_valid;
		assign	mix_hlast = r_mix_hlast;
		assign	mix_vlast = r_mix_vlast;
		assign	mix_sof   = r_mix_sof;
		// }}}

		// Keep Verilator happy
		// {{{
		wire	unused_no_alpha;
		assign	pix_ready = 1'b0;
		assign	{ pix_loaded, mpy_loaded, mpy_ready } = 0;
		assign	unused_no_alpha = &{ 1'b0, pix_loaded, mpy_loaded,
				pix_ready, mix_valid, mpy_ready };
		// }}}
`ifdef	FORMAL
		// {{{
		reg	r_mix_err;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
			r_mix_err <= frame_err;

		assign	f_mix_err = r_mix_err;

		always @(*)
		if (ARESETN)
		begin
			if (!mix_valid)
			begin
				assert(f_pskd_hpos == f_mix_hpos);
				assert(f_pskd_vpos == f_mix_vpos);
			end else if (f_mix_hpos < f_vid_width-1)
			begin
				assert(f_pskd_hpos == f_mix_hpos + 1);
				assert(f_pskd_vpos == f_mix_vpos);
			end else if (f_mix_vpos < f_vid_height-1)
			begin
				assert(f_pskd_hpos == 0);
				assert(f_pskd_vpos == f_mix_vpos + 1);
			end else // if (f_mix_vpos == f_mix_height-1)
			begin
				assert(f_pskd_hpos == 0);
				assert(f_pskd_vpos == 0);
			end
		end
		// }}}
`endif
		// }}}
	end else begin : MATCH_ALPHA_PIPELINE
		assign	pskd_ready = !pix_line_pause
					&& (!pix_loaded || pix_ready);
		// {{{
		reg	pix_hlast, pix_vlast, pix_sof, r_pix_loaded;
		reg	r_mpy_loaded, mpy_hlast, mpy_vlast, mpy_sof;
		reg	mix_loaded, r_mix_hlast, r_mix_vlast, r_mix_sof;

		assign	pix_ready = !mpy_loaded || mpy_ready;
		assign	mpy_ready = !mix_valid || mix_ready;

		always @(posedge ACLK)
		if (!ARESETN)
			r_pix_loaded <= 0;
		else if (pskd_valid && pskd_ready)
			r_pix_loaded <= 1;
		else if (pix_ready)
			r_pix_loaded <= 0;

		always @(posedge ACLK)
		if (pskd_valid && pskd_ready)
		begin
			pix_hlast <= pskd_hlast;
			pix_vlast <= pskd_vlast;
			pix_sof   <= pskd_sof;
		end

		always @(posedge ACLK)
		if (!ARESETN)
			r_mpy_loaded <= 0;
		else if (pix_loaded && pix_ready)
			r_mpy_loaded<= 1;
		else if (mpy_ready)
			r_mpy_loaded <= 0;

		assign	mpy_loaded = r_mpy_loaded;

		always @(posedge ACLK)
		if (pix_loaded && pix_ready)
		begin
			mpy_hlast <= pix_hlast;
			mpy_vlast <= pix_vlast;
			mpy_sof   <= pix_sof;
		end

		always @(posedge ACLK)
		if (!ARESETN)
			mix_loaded <= 0;
		else if (mpy_loaded && mpy_ready)
			mix_loaded <= 1;
		else if (mix_ready)
			mix_loaded <= 0;

		always @(posedge ACLK)
		if (mpy_loaded && mpy_ready)
		begin
			r_mix_hlast <= mpy_hlast;
			r_mix_vlast <= mpy_vlast;
			r_mix_sof   <= mpy_sof;
		end


		assign	pix_loaded= r_pix_loaded;
		assign	mix_hlast = r_mix_hlast;
		assign	mix_vlast = r_mix_vlast;
		assign	mix_sof   = r_mix_sof;

		assign	mix_valid = mix_loaded;
		// }}}
	end endgenerate
	// }}}
	// }}}

	assign	ovskd_ready = (frame_err && !ovw_eof)
		|| !ov_line_pause && ((!in_overlay && !ovw_eol)
				|| (in_overlay && pskd_valid && pskd_ready));

	// M_VID_TVALID
	// {{{
	assign	mix_ready = !M_VID_TVALID || M_VID_TREADY;

	initial	M_VID_TVALID = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		M_VID_TVALID <= 0;
	else if (!M_VID_TVALID || M_VID_TREADY)
		M_VID_TVALID <= mix_valid;
	// }}}

	// M_VID_TDATA, M_VID_TLAST, M_VID_TUSER
	// {{{
	always @(posedge ACLK)
	if (!M_VID_TVALID || M_VID_TREADY)
	begin
		M_VID_TDATA <= mix_pixel;
		if (OPT_TUSER_IS_SOF)
		begin
			M_VID_TLAST <= mix_hlast;
			M_VID_TUSER <= mix_sof;
		end else begin
			M_VID_TLAST <= mix_vlast;
			M_VID_TUSER <= mix_hlast;
		end
	end
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, lines_per_frame };
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
	// Declarations
	// {{{
	wire	f_pri_hlast,  f_pri_vlast,  f_pri_sof;
	wire	f_ovw_hlast,  f_ovw_vlast,  f_ovw_sof;
	wire	f_pskd_hlast, f_pskd_vlast, f_pskd_sof, f_pskd_known;
	wire	f_mix_hlast,  f_mix_vlast,  f_mix_sof, f_mix_known;
	wire	f_vid_hlast,  f_vid_vlast,  f_vid_sof, f_vid_known;
	(* keep *) reg	f_past_valid, f_mix_frame_valid, f_ovw_frame_valid,
			f_m_frame_valid;

	initial	f_past_valid = 0;
	always @(posedge ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!ARESETN);

	always @(posedge ACLK)
	if (!ARESETN)
		f_ovw_frame_valid <= 0;
	else if (f_ovw_lines_per_frame == f_ovw_height)
		f_ovw_frame_valid <= 1;

	always @(posedge ACLK)
	if (!ARESETN)
		f_mix_frame_valid <= 0;
	else if (pskd_valid && pskd_ready && lines_per_frame == f_vid_height)
		f_mix_frame_valid <= 1;

	always @(posedge ACLK)
	if (!ARESETN)
		f_m_frame_valid <= 0;
	else if ((!M_VID_TVALID || M_VID_TREADY) && f_mix_frame_valid)
		f_m_frame_valid <= 1;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge ACLK)
	begin
		assume($stable(i_enable));
		assume($stable(i_hpos));
		assume($stable(i_vpos));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Priority video slave input
	// {{{
	always @(posedge ACLK)
	if (!f_past_valid || $past(!ARESETN))
		assume(!S_PRI_TVALID);
	else if ($past(S_PRI_TVALID && !S_PRI_TREADY))
	begin
		assume(S_PRI_TVALID);
		assume($stable(S_PRI_TDATA));
		assume($stable(S_PRI_TLAST));
		assume($stable(S_PRI_TUSER));
	end
	// }}}

	// Overlay slave input
	// {{{
	always @(posedge ACLK)
	if (!f_past_valid || $past(!ARESETN))
		assume(!S_OVW_TVALID);
	else if ($past(S_OVW_TVALID && !S_OVW_TREADY))
	begin
		assume(S_OVW_TVALID);
		assume($stable(S_OVW_TDATA));
		assume($stable(S_OVW_TLAST));
		assume($stable(S_OVW_TUSER));
	end
	// }}}

	// Video output (master)
	// {{{
	always @(posedge ACLK)
	if (!f_past_valid || $past(!ARESETN))
		assert(!M_VID_TVALID);
	else if ($past(M_VID_TVALID && !M_VID_TREADY))
	begin
		assert(M_VID_TVALID);
		assert($stable(M_VID_TDATA));
		assert($stable(M_VID_TLAST));
		assert($stable(M_VID_TUSER));
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		assume(f_vid_width >= 4);
		assume(f_vid_height>= 4);

		assume(f_ovw_width >= 2);
		assume(f_ovw_height>= 2);
	end

	// f_pri_?pos
	// {{{
	faxivideo #(
		// {{{
		.PW(DW), .LGDIM(LGFRAME),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fpri (
		// {{{
		.i_clk(ACLK), .i_reset_n(ARESETN),
		.S_VID_TVALID(S_PRI_TVALID),
		.S_VID_TREADY(S_PRI_TREADY),
		.S_VID_TDATA( S_PRI_TDATA),
		.S_VID_TLAST( S_PRI_TLAST),
		.S_VID_TUSER( S_PRI_TUSER),
		//
		.i_width(f_vid_width), .i_height(f_vid_height),
		.o_xpos(f_pri_hpos), .o_ypos(f_pri_vpos),
			.f_known_height(f_pri_known),
		.o_hlast(f_pri_hlast), .o_vlast(f_pri_vlast),
			.o_sof(f_pri_sof),
		// }}}
	);

	always @(*)
	if (ARESETN && S_PRI_TVALID)
	begin
		if (OPT_TUSER_IS_SOF)
		begin
			assume(S_PRI_TLAST == f_pri_hlast);
			assume(S_PRI_TUSER == f_pri_sof);
		end else begin
			assume(S_PRI_TLAST == (f_pri_vlast && f_pri_hlast));
			assume(S_PRI_TUSER == f_pri_hlast);
		end
	end
	// }}}

	// f_ovw_?pos
	// {{{
	faxivideo #(
		// {{{
		.PW(DW), .LGDIM(LGFRAME),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fovw (
		// {{{
		.i_clk(ACLK), .i_reset_n(ARESETN),
		.S_VID_TVALID(S_OVW_TVALID),
		.S_VID_TREADY(S_OVW_TREADY),
		.S_VID_TDATA( S_OVW_TDATA),
		.S_VID_TLAST( S_OVW_TLAST),
		.S_VID_TUSER( S_OVW_TUSER),
		//
		.i_width(f_ovw_width), .i_height(f_ovw_height),
		.o_xpos(f_ovw_hpos), .o_ypos(f_ovw_vpos),
			.f_known_height(f_ovw_known),
		.o_hlast(f_ovw_hlast), .o_vlast(f_ovw_vlast),
			.o_sof(f_ovw_sof),
		// }}}
	);

	always @(*)
	if (ARESETN && S_OVW_TVALID)
	begin
		if (OPT_TUSER_IS_SOF)
		begin
			assume(S_OVW_TLAST == f_ovw_hlast);
			assume(S_OVW_TUSER == f_ovw_sof);
		end else begin
			assume(S_OVW_TLAST == (f_ovw_vlast && f_ovw_hlast));
			assume(S_OVW_TUSER == f_ovw_hlast);
		end
	end
	// }}}

	// S_PRI_TLAST, S_PRI_TUSER
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : ASSUME_SOF
		always @(*)
		if (S_PRI_TVALID)
		begin
			assume(S_PRI_TLAST == (f_pri_hpos == f_vid_width-1));
			assume(S_PRI_TUSER == (f_pri_hpos == 0 && f_pri_vpos == 0));
		end
	end else begin : ASSUME_VLAST
		always @(*)
		if (S_PRI_TVALID)
		begin
			assume(S_PRI_TUSER == (f_pri_hpos == f_vid_width-1));
			if (f_pri_vpos < f_vid_height-1)
				assume(!S_PRI_TLAST);
			else if (S_PRI_TUSER)
				assume(S_PRI_TLAST == (f_pri_vpos == f_vid_height-1));
		end
	end endgenerate
	// }}}

	// S_OVW_TLAST, S_OVW_TUSER
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(*)
		if (S_OVW_TVALID)
		begin
			assume(S_OVW_TLAST == (f_ovw_hpos == f_ovw_width-1));
			assume(S_OVW_TUSER == (f_ovw_hpos == 0 && f_ovw_vpos == 0));
		end
	end else begin
		always @(*)
		if (S_OVW_TVALID)
		begin
			assume(S_OVW_TUSER == (f_ovw_hpos == f_ovw_width-1));
			if (f_ovw_vpos < f_ovw_height-1)
				assume(!S_OVW_TLAST);
			else if (S_OVW_TUSER)
				assume(S_OVW_TLAST == (f_ovw_vpos == f_ovw_height-1));
		end
	end endgenerate
	// }}}

	// f_vid_?pos
	// {{{
	faxivideo #(
		// {{{
		.PW(DW), .LGDIM(LGFRAME),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fvid (
		// {{{
		.i_clk(ACLK), .i_reset_n(ARESETN),
		.S_VID_TVALID(M_VID_TVALID),
		.S_VID_TREADY(M_VID_TREADY),
		.S_VID_TDATA( M_VID_TDATA),
		.S_VID_TLAST( M_VID_TLAST),
		.S_VID_TUSER( M_VID_TUSER),
		//
		.i_width(f_vid_width), .i_height(f_vid_height),
		.o_xpos(f_vid_hpos), .o_ypos(f_vid_vpos),
			.f_known_height(f_vid_known),
		.o_hlast(f_vid_hlast), .o_vlast(f_vid_vlast),
			.o_sof(f_vid_sof),
		// }}}
	);
	// }}}

	// f_mix_?pos
	// {{{
	faxivideo #(
		// {{{
		.PW(DW), .LGDIM(LGFRAME),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fmix (
		// {{{
		.i_clk(ACLK), .i_reset_n(ARESETN),
		.S_VID_TVALID(mix_valid),
		.S_VID_TREADY(mix_ready),
		.S_VID_TDATA( mix_pixel),
		.S_VID_TLAST( (OPT_TUSER_IS_SOF) ? mix_hlast : mix_vlast),
		.S_VID_TUSER( (OPT_TUSER_IS_SOF) ? mix_sof   : mix_hlast),
		//
		.i_width(f_vid_width), .i_height(f_vid_height),
		.o_xpos(f_mix_hpos), .o_ypos(f_mix_vpos),
			.f_known_height(f_mix_known),
		.o_hlast(f_mix_hlast), .o_vlast(f_mix_vlast),
			.o_sof(f_mix_sof),
		// }}}
	);
	// }}}

	// f_mix_hlast, f_mix_sof, f_mix_vlast
	// {{{
	always @(*)
	if (ARESETN && mix_valid)
	begin
		assert(mix_hlast == (f_mix_hpos == f_vid_width-1));
		assert(mix_sof   == (f_mix_vpos == 0 && f_mix_hpos == 0));
		if (mix_vlast || f_mix_known || f_pri_known)
			assert(f_pri_sof || (mix_vlast == (mix_hlast && f_mix_vpos == f_vid_height-1)));
	end
	// }}}

	always @(*)
	if (ARESETN)
	begin
		if (!M_VID_TVALID)
		begin
			assert(f_mix_hpos == f_vid_hpos);
			assert(f_mix_vpos == f_vid_vpos);
		end else if (f_vid_hpos < f_vid_width-1)
		begin
			assert(f_mix_hpos == f_vid_hpos + 1);
			assert(f_mix_vpos == f_vid_vpos);
		end else // if (f_vid_hpos == f_vid_width-1)
		begin
			assert(f_mix_hpos == 0);
			if (f_vid_vpos == f_vid_height-1)
				assert(f_mix_vpos == 0);
			else
				assert(f_mix_vpos == f_vid_vpos + 1);
		end
	end

	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_VLAST

		always @(*)
		if (ARESETN && lines_per_frame > 0)
		begin
			assert(lines_per_frame == f_vid_height);
			if (pskd_valid)
				assert(pskd_vlast == (pskd_hlast && f_pskd_vpos == f_vid_height-1));
		end else if (ARESETN)
		begin
			if (pskd_valid)
				assert(!pskd_vlast);
			if (mix_valid)
				assert(!mix_vlast);
		end

	end endgenerate

	// f_pskd_?pos
	// {{{
	faxivideo #(
		// {{{
		.PW(DW), .LGDIM(LGFRAME),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fpskd (
		// {{{
		.i_clk(ACLK), .i_reset_n(ARESETN),
		.S_VID_TVALID(pskd_valid),
		.S_VID_TREADY(pskd_ready),
		.S_VID_TDATA( pskd_data),
		.S_VID_TLAST( (OPT_TUSER_IS_SOF) ? pskd_hlast : pskd_vlast),
		.S_VID_TUSER( (OPT_TUSER_IS_SOF) ? pskd_sof   : pskd_hlast),
		//
		.i_width(f_vid_width), .i_height(f_vid_height),
		.o_xpos(f_pskd_hpos), .o_ypos(f_pskd_vpos),
			.f_known_height(f_pskd_known),
		.o_hlast(f_pskd_hlast), .o_vlast(f_pskd_vlast),
			.o_sof(f_pskd_sof),
		// }}}
	);

	always @(*)
	begin
		assert(f_pskd_sof   == f_pri_sof);
		assert(f_pskd_hpos  == f_pri_hpos);
		assert(f_pskd_vpos  == f_pri_vpos);
		assert(f_pskd_known == f_pri_known);
	end
	// }}}

	// Relate f_pskd to f_pri (they are the same)
	// {{{
	always @(*)
	if (ARESETN)
	begin
		if (1 || S_PRI_TREADY)
		begin
			assert(f_pskd_hpos == f_pri_hpos);
			assert(f_pskd_vpos == f_pri_vpos);
		end else if (f_vid_hpos > 0)
		begin
			assert(f_pskd_hpos + 1 == f_pri_hpos);
			assert(f_pskd_vpos <= f_pri_vpos);
		end else if (f_vid_vpos > 0)
		begin
			assert(f_pskd_hpos == f_vid_width -1);
			assert(f_pskd_vpos + 1 == f_pri_vpos);
		end else begin
			assert(f_pskd_hpos == f_vid_width -1);
			assert(f_pskd_vpos == f_vid_height - 1);
		end
	end
	// }}}

	// pskd_hlast, pskd_sof
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : CHECK_LINES_PER_FRAME
		always @(posedge ACLK)
		if (f_past_valid && $past(ARESETN))
		begin
			if ($past(lines_per_frame == f_vid_height))
				assert(lines_per_frame == f_vid_height);
			if (lines_per_frame != 0)
				assert(f_pri_known);
		end
	end endgenerate

	always @(*)
	if (ARESETN)
	begin
		if (!f_pri_known)
		begin
			assert(lines_per_frame == 0);
		end else begin
			assert(lines_per_frame == f_vid_height
				|| lines_per_frame == 0);
		end
	end

	always @(*)
	if (pskd_valid)
	begin
		assert(pskd_hlast == f_pskd_hlast);
		assert(pskd_sof   == f_pskd_sof);
		if (lines_per_frame == f_vid_height)
		begin
			assert(f_pskd_known);
			assert(pskd_vlast == (pskd_hlast && f_pskd_vlast));
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	fc_check;
	(* anyconst *)	reg	[LGFRAME-1:0]	fc_pri_hpos, fc_pri_vpos;
	(* anyconst *)	reg	[LGFRAME-1:0]	fc_ovw_hpos, fc_ovw_vpos;
	(* anyconst *)	reg	[LGFRAME-1:0]	fc_off_hpos, fc_off_vpos;
	(* anyconst *)	reg	[DW-1:0]	fc_pri_pixel;
	(* anyconst *)	reg	[DW+ALPHA_BITS-1:0]	fc_ovw_pixel;
	reg	f_vid_err;

	always @(*)
	begin
		assume(fc_pri_hpos < f_vid_width);
		assume(fc_pri_vpos < f_vid_height);

		assume(fc_off_hpos < f_vid_width);
		assume(fc_off_vpos < f_vid_height);

		assume(fc_ovw_hpos < f_ovw_width);
		assume(fc_ovw_vpos < f_ovw_height);

	end

	always @(posedge ACLK)
	if (!ARESETN)
		f_vid_err <= 0;
	else if (!M_VID_TVALID || M_VID_TREADY)
		f_vid_err <= f_mix_err;

	always @(*)
	if (fc_check && ARESETN)
	begin
		if (S_PRI_TVALID && f_pri_hpos == fc_pri_hpos
				&&  f_pri_vpos == fc_pri_vpos)
			assume(S_PRI_TDATA == fc_pri_pixel);
		if (S_OVW_TVALID && f_ovw_hpos == fc_ovw_hpos
				&&  f_ovw_vpos == fc_ovw_vpos)
			assume(S_OVW_TDATA == fc_ovw_pixel);

		assume(fc_off_hpos == i_hpos);
		assume(fc_off_vpos == i_vpos);

		assume({ 1'b0, fc_pri_hpos } == { 1'b0, i_hpos } + { 1'b0, fc_ovw_hpos });
		assume({ 1'b0, fc_pri_vpos } == { 1'b0, i_vpos } + { 1'b0, fc_ovw_vpos });
	end

	always @(posedge ACLK)
	if (ARESETN && fc_check)
		assume(!$rose(frame_err));

	always @(posedge ACLK)
	if (ARESETN && fc_check && !frame_err)
	begin
		if (f_pri_known && $stable(f_pri_known)
			&& f_ovw_known && $stable(f_ovw_known)
				&& f_ovw_lines_per_frame == f_ovw_height
			&& (lines_per_frame > 0)
			&& $stable(lines_per_frame))
		begin
			if (f_pri_hpos >= i_hpos && f_pri_vpos >= i_vpos
				&& f_pri_hpos < { 1'b0, i_hpos } + { 1'b0, f_ovw_width }
				&& f_pri_vpos < { 1'b0, i_vpos } + { 1'b0, f_ovw_height })
			begin
				assert(in_overlay);
				// {{{
				// assert({ 1'b0, f_pri_hpos } == { 1'b0, f_ovw_hpos } + { 1'b0, i_hpos });
				// assert({ 1'b0, f_pri_vpos } == { 1'b0, f_ovw_vpos } + { 1'b0, i_vpos });
				// }}}
			end else begin
				assert(!in_overlay);
				// {{{
				if (ovw_eof)
				begin
					// {{{
					assert(
						// Before/waiting 4 the frame
						(f_pri_vpos < i_vpos
							|| (f_pri_vpos == i_vpos && f_pri_hpos < i_hpos))
						// or afterwards on the same line
						||(f_pri_hpos >= { 1'b0, i_hpos } + { 1'b0, f_ovw_width }
							&& { 1'b0, f_pri_vpos } == { 1'b0, i_vpos } + { 1'b0, f_ovw_height } - 1)
						// or on following lines
						||({ 1'b0, f_pri_vpos } >= { 1'b0, i_vpos } + { 1'b0, f_ovw_height }));
					// }}}
				end else if (ovw_eol
					&& f_pri_vpos >= i_vpos
					&& f_pri_vpos < { 1'b0, i_vpos } + { 1'b0, f_ovw_height })
				begin
					if (f_pri_hpos < i_hpos)
					begin
						assert({ 1'b0, f_pri_vpos } == { 1'b0, f_ovw_vpos } + { 1'b0, i_vpos });
					end else 
						assert({ 1'b0, f_pri_vpos } == { 1'b0, f_ovw_vpos } + { 1'b0, i_vpos } - 1);
				end else if (f_pri_vpos >= i_vpos
					&& f_pri_vpos < { 1'b0, i_vpos } + { 1'b0, f_ovw_height })
				begin
					if (f_pri_hpos <= i_hpos)
					begin
						assert({ 1'b0, f_pri_vpos }
							== { 1'b0, f_ovw_vpos }
						 	+ { 1'b0, i_vpos } + 1);
					end else
						assert({ 1'b0, f_pri_vpos }
							== { 1'b0, f_ovw_vpos }
						 	+ { 1'b0, i_vpos });
				end // else assert(ovw_eof);
				// }}}
			end
		end
	end

	generate if (ALPHA_BITS == 0)
	begin : GEN_CONTRACT_A0
		// {{{
		always @(posedge ACLK)
		if (ARESETN && fc_check && mix_valid
			&& (f_mix_hpos == fc_pri_hpos
				&& f_mix_vpos == fc_pri_vpos))
		begin
			if (i_enable && !f_mix_err)
			begin
				assert(mix_pixel == fc_ovw_pixel);
			end else begin
				assert(mix_pixel == fc_pri_pixel);
			end
		end

		always @(posedge ACLK)
		if (ARESETN && fc_check && M_VID_TVALID)
		begin
			if (f_vid_hpos == fc_pri_hpos
					&& f_vid_vpos == fc_pri_vpos)
			begin
				if (i_enable && !f_vid_err)
				begin
					assert(M_VID_TDATA == fc_ovw_pixel);
				end else begin
					assert(M_VID_TDATA == fc_pri_pixel);
				end
			end
		end
		// }}}
	end else if (ALPHA_BITS == 1)
	begin : GEN_CONTRACT_A1
		// {{{
		always @(posedge ACLK)
		if (ARESETN && fc_check && mix_valid
			&& (f_mix_hpos == fc_pri_hpos
				&& f_mix_vpos == fc_pri_vpos))
		begin
			if (fc_ovw_pixel[DW] && i_enable && !f_mix_err)
			begin
				assert(mix_pixel == fc_ovw_pixel[DW-1:0]);
			end else begin
				assert(mix_pixel == fc_pri_pixel[DW-1:0]);
			end
		end

		always @(posedge ACLK)
		if (ARESETN && fc_check && M_VID_TVALID)
		begin
			if (f_vid_hpos == fc_pri_hpos
				&& f_vid_vpos == fc_pri_vpos)
			begin
				if (fc_ovw_pixel[DW] && i_enable && !f_vid_err)
				begin
					assert(M_VID_TDATA == fc_ovw_pixel[DW-1:0]);
				end else begin
					assert(M_VID_TDATA == fc_pri_pixel[DW-1:0]);
				end
			end
		end
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Overlay tracking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge ACLK)
	if (ARESETN && (!OPT_LINE_BREAK || !pix_line_pause))
	begin
		if (f_pskd_hpos < i_hpos)
		begin
			assert(!in_overlay);
		end else if (f_pskd_vpos < i_vpos
				&& f_pskd_vpos == prvpos
				&& f_ovw_vpos == ovvpos
				&& f_pskd_hpos != 1)
			assert(!in_overlay);

		if (!frame_err && !ovw_eof && in_frame && lines_per_frame > 0)
		begin
			if (ovw_eol && f_pri_hpos > i_hpos)
			begin
				assert(f_sum_ypos == f_pskd_vpos + 1);
			/*
			end else if (ovw_eol && f_pri_hpos <= i_hpos)
			begin
				assert(f_sum_ypos == f_pskd_vpos
					|| (f_ovw_vpos == 0
						&& f_ovw_hpos == 0
						&& f_ovw_lines_per_frame == 0
						&& (f_sum_ypos == { 1'b0, i_vpos } + { 1'b0, f_ovw_height })
						&& OPT_TUSER_IS_SOF));
			end
			else if (f_pri_hpos <= i_hpos)
			begin
				assert(f_sum_ypos + 1 == f_pskd_vpos);
			end else begin // if (!ovw_eol && f_pri_hpos > i_hpos)
				assert(f_sum_ypos == f_pskd_vpos
					|| f_sum_ypos >= f_vid_height);
			*/
			end
		end

		if (!frame_err && !ovw_eof && in_overlay
			&& lines_per_frame > 0)
		begin
			assert(w_frame_err || (i_hpos + f_ovw_hpos == f_pskd_hpos));
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[2:0]	cvr_pframes, cvr_oframes;

	initial	cvr_pframes = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		cvr_pframes <= 0;
	else if (pskd_valid && pskd_ready && pskd_vlast && !cvr_pframes[2])
		cvr_pframes <= cvr_pframes + 1;

	initial	cvr_oframes = 0;
	always @(posedge ACLK)
	if (!ARESETN)
		cvr_oframes <= 0;
	else if (ovskd_valid && ovskd_ready && ovskd_vlast && !cvr_oframes[2])
		cvr_oframes <= cvr_oframes + 1;

	always @(posedge ACLK)
	if (ARESETN)
	begin
		cover(cvr_pframes == 1);
		cover(cvr_oframes == 1);

		cover(cvr_pframes == 2);
		cover(cvr_oframes == 2);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge ACLK)
	if ((1||fc_check) && ARESETN && $past(ARESETN && !S_PRI_TVALID)
			&& $past(ARESETN && !S_PRI_TVALID, 2)
			&& $past(ARESETN && !S_PRI_TVALID, 3))
	begin
		assume(S_PRI_TVALID);
	end

	always @(*)
	if (fc_check)
		assume(M_VID_TREADY);

	always @(posedge ACLK)
	if ((1||fc_check) && ARESETN && $past(ARESETN && !M_VID_TREADY)
			&& $past(ARESETN && !M_VID_TREADY, 2)
			&& $past(ARESETN && !M_VID_TREADY, 3))
	begin
		assume(M_VID_TREADY);
	end


	always @(*)
		assume(i_vpos == 0);

	always @(*)
	if (!S_PRI_TVALID)
	begin
		assume(!S_PRI_TUSER);
		assume(!S_PRI_TLAST);
	end

	always @(*)
	if (!S_OVW_TVALID)
	begin
		assume(!S_OVW_TUSER);
		assume(!S_OVW_TLAST);
	end

	// }}}
`endif
// }}}
endmodule
