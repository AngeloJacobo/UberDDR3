////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axishdmi
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generates the timing signals (not the clock) for an outgoing
//		video signal, and then encodes the incoming pixels into
//	an HDMI data stream.
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
module	axishdmi #(
		// {{{
		parameter	HW=12,
				VW=12,
		parameter [0:0]	OPT_RESYNC_ON_VLAST = 1'b0,
		// HDMI *only* works with 24-bit color, using 8-bits per color
		localparam	BITS_PER_COLOR = 8,
		localparam	BPC = BITS_PER_COLOR,
				BITS_PER_PIXEL = 3 * BPC,
				BPP = BITS_PER_PIXEL
		// }}}
	) (
		// {{{
		input	wire	i_pixclk,
		// Verilator lint_off SYNCASYNCNET
		input	wire			i_reset,
		// Verilator lint_on SYNCASYNCNET
		//
		// AXI Stream interface
		// {{{
		input	wire		i_valid,
		output	reg		o_ready,
		input	wire		i_hlast,
		input	wire		i_vlast,
		input	wire [BPP-1:0]	i_rgb_pix,
		// }}}
		//
		// Video mode information
		// {{{
		input	wire [HW-1:0]	i_hm_width,
		input	wire [HW-1:0]	i_hm_porch,
		input	wire [HW-1:0]	i_hm_synch,
		input	wire [HW-1:0]	i_hm_raw,
		//
		input	wire [VW-1:0]	i_vm_height,
		input	wire [VW-1:0]	i_vm_porch,
		input	wire [VW-1:0]	i_vm_synch,
		input	wire [VW-1:0]	i_vm_raw,
		// }}}
		//
		// HDMI outputs
		// {{{
		output	wire	[9:0]	o_red,
		output	wire	[9:0]	o_grn,
		output	wire	[9:0]	o_blu
		// }}}
		// }}}
	);

	// Register declarations
	// {{{
	reg		r_newline, r_newframe, lost_sync;
	reg		vsync, hsync;
	reg	[1:0]	hdmi_type;
	wire	[3:0]	hdmi_ctl;
	reg	[11:0]	hdmi_data;
	reg	[7:0]	red_pixel, grn_pixel, blu_pixel;
	reg		pre_line;
	reg		first_frame;

	wire			w_rd;
	wire	[BPC-1:0]	i_red, i_grn, i_blu;
	assign	i_red = i_rgb_pix[3*BPC-1:2*BPC];
	assign	i_grn = i_rgb_pix[2*BPC-1:  BPC];
	assign	i_blu = i_rgb_pix[  BPC-1:0];

	reg	[HW-1:0]	hpos;
	reg	[VW-1:0]	vpos;
	reg			hrd, vrd;
	reg		pix_reset;
	reg	[1:0]	pix_reset_pipe;
	wire		w_external_sync;
`ifdef	FORMAL
	wire	[47:0]		f_vmode, f_hmode;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize the reset release
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	{ pix_reset, pix_reset_pipe } = -1;
	always @(posedge i_pixclk, posedge i_reset)
	if (i_reset)
		{ pix_reset, pix_reset_pipe } <= -1;
	else
		{ pix_reset, pix_reset_pipe } <= { pix_reset_pipe, 1'b0 };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Horizontal line counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// hpos, r_newline, hsync, hrd
	// {{{
	initial	hpos       = 0;
	initial	r_newline  = 0;
	initial	hsync = 0;
	initial	hrd = 1;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		// {{{
		hpos <= 0;
		r_newline <= 1'b0;
		hsync <= 1'b0;
		hrd <= 1;
		// }}}
	end else if (w_external_sync)
	begin
		hpos      <= i_hm_width-1;
		r_newline <= 0;
		hrd       <= 0;
		hsync <= 1'b0;
	end else begin
		// {{{
		hrd <= (hpos < i_hm_width-2)
				||(hpos >= i_hm_raw-2);
		if (hpos < i_hm_raw-1'b1)
			hpos <= hpos + 1'b1;
		else
			hpos <= 0;
		r_newline <= (hpos == i_hm_width-3);
		hsync <= (hpos >= i_hm_porch-1'b1)&&(hpos<i_hm_synch-1'b1);
		// }}}
	end
	// }}}

	// lost_sync detection
	// {{{
	assign	w_external_sync = (OPT_RESYNC_ON_VLAST && i_valid && o_ready
			&& i_vlast && i_hlast);

	initial	lost_sync = 1;
	always @(posedge i_pixclk)
	if (pix_reset)
		lost_sync <= 1;
	else if (w_external_sync)
		lost_sync <= 0;
	else if (w_rd)
	begin
		if (r_newframe && i_hlast && i_vlast && i_valid)
			lost_sync <= 0;
		else begin
			if (!i_valid)
				lost_sync <= 1;
			if (i_hlast != r_newline)
				lost_sync <= 1;
			if ((i_vlast && i_hlast) != r_newframe)
				lost_sync <= 1;
		end
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Vertical / frame based timing and synchronization
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_newframe
	// {{{
	initial	r_newframe = 0;
	always @(posedge i_pixclk)
	if (pix_reset)
		r_newframe <= 1'b0;
	else if (w_external_sync)
		r_newframe <= 1'b0;
	else if ((hpos == i_hm_width - 3)&&(vpos == i_vm_height-1))
		r_newframe <= 1'b1;
	else
		r_newframe <= 1'b0;
	// }}}

	// vpos, vsync
	// {{{
	initial	vpos = 0;
	initial	vsync = 1'b0;
	always @(posedge i_pixclk)
	if (pix_reset)
	begin
		vpos <= 0;
		vsync <= 1'b0;
	end else if (w_external_sync)
	begin
		vpos  <= i_vm_height -1;
		vsync <= 0;
	end else if (hpos == i_hm_porch-1'b1)
	begin
		if (vpos < i_vm_raw-1'b1)
			vpos <= vpos + 1'b1;
		else
			vpos <= 0;
		// Realistically, the new frame begins at the top
		// of the next frame.  Here, we define it as the end
		// last valid row.  That gives any software depending
		// upon this the entire time of the front and back
		// porches, together with the synch pulse width time,
		// to prepare to actually draw on this new frame before
		// the first pixel clock is valid.
		vsync <= (vpos >= i_vm_porch-1'b1)&&(vpos<i_vm_synch-1'b1);
	end
	// }}}

	// vrd
	// {{{
	initial	vrd = 1'b1;
	always @(posedge i_pixclk)
		vrd <= (vpos < i_vm_height)&&(!pix_reset);
	// }}}

	// first_frame
	// {{{
	initial	first_frame = 1'b1;
	always @(posedge i_pixclk)
	if (pix_reset)
		first_frame <= 1'b1;
	else if (OPT_RESYNC_ON_VLAST && w_external_sync)
		first_frame <= 1'b0;
	else if (!OPT_RESYNC_ON_VLAST && r_newframe)
		first_frame <= 1'b0;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-stream Ready generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// w_rd
	// {{{
	assign	w_rd = (hrd)&&(vrd)&&(!first_frame);
	// }}}

	// o_ready
	// {{{
	// If we've lost sync, flush the incoming frame and then force the
	// input to wait until the first of the frame.
	always @(*)
	if (lost_sync)
	begin
		if (OPT_RESYNC_ON_VLAST)
			o_ready = 1'b1;
		else if (!i_vlast || !i_hlast)
			// Skip to the end of the incoming frame before
			// trying again
			o_ready = 1'b1;
		else if (!r_newframe)
			o_ready = 1'b0;
		else
			// First pixel of a new frame--sync to it
			o_ready = 1'b1;
	end else
		o_ready = w_rd;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// HDMI encoding
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// Set *_pixel values
	// {{{
	always @(posedge i_pixclk)
	if (w_rd)
	begin
		if (lost_sync)
		begin
			red_pixel <= 0;
			grn_pixel <= 0;
			blu_pixel <= 0;
		end else begin
			red_pixel <= i_red;
			grn_pixel <= i_grn;
			blu_pixel <= i_blu;
		end
	end else begin
		red_pixel <= 0;
		grn_pixel <= 0;
		blu_pixel <= 0;
	end
	// }}}

	// hdmi_type
	// {{{
	localparam	[1:0]	GUARD = 2'b00;
	localparam	[1:0]	CTL_PERIOD  = 2'b01;
	localparam	[1:0]	VIDEO_DATA  = 2'b11;
	localparam		GUARD_PIXELS= 2;

	initial	pre_line = 1'b1;
	always @(posedge i_pixclk)
	if (pix_reset)
		pre_line <= 1'b1;
	else
		pre_line <= (vpos < i_vm_height);

	initial	hdmi_type = GUARD;
	always @(posedge i_pixclk)
	if (pix_reset)
		hdmi_type <= GUARD;
	else if (pre_line)
	begin
		if (hpos >= i_hm_raw - 1)
			hdmi_type <= VIDEO_DATA;
		else if (hpos < i_hm_width - 1)
			hdmi_type <= VIDEO_DATA;
		else if (hpos >= i_hm_raw - 1-GUARD_PIXELS)
			hdmi_type <= GUARD;
		else
			hdmi_type <= CTL_PERIOD;
	end else
		hdmi_type <= CTL_PERIOD;

	assign	hdmi_ctl = 4'h1;
	// }}}

	// hdmi_data
	// {{{
	always @(*)
	begin
		hdmi_data[1:0]	= { vsync, hsync };
		hdmi_data[11:2] = 0;
	end
	// }}}

	// TMDS encoding
	// {{{
`ifdef	FORMAL
	(* anyseq *) reg [9:0]	w_blu, w_grn, w_red;
	//
	// Verific complains of logic loops within tmdsencode.  Since the TMDS
	// encoder isn't really a part of our formal proof, we can cut it out
	// here and replace it's results with ... whatever we want ... just to
	// get the proof to pass.
	//

	assign	o_red = w_red;
	assign	o_grn = w_grn;
	assign	o_blu = w_blu;
`else
	// Channel 0 = blue
	tmdsencode #(.CHANNEL(2'b00)) hdmi_encoder_ch0(i_pixclk,
			hdmi_type, { vsync, hsync },
			hdmi_data[3:0], blu_pixel, o_blu);

	// Channel 1 = green
	tmdsencode #(.CHANNEL(2'b01)) hdmi_encoder_ch1(i_pixclk,
			hdmi_type, hdmi_ctl[1:0],
			hdmi_data[7:4], grn_pixel, o_grn);

	// Channel 2 = red
	tmdsencode #(.CHANNEL(2'b10)) hdmi_encoder_ch2(i_pixclk,
			hdmi_type, hdmi_ctl[3:2],
			hdmi_data[11:8], red_pixel, o_red);
`endif
	// }}}

	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties for verification purposes
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	[1:0]	DATA_ISLAND = 2'b10;
	localparam		PREGUARD_CONTROL = 6;
	reg	f_past_valid;
	reg	[47:0]	f_last_vmode, f_last_hmode;
	reg	f_stable_mode;
	reg	[3:0]	f_ctrl_length;
	reg	[1:0]	f_video_start, f_packet_start;

	////////////////////////////////////////////////////////////////////////
	//
	// Reset assumptions
	//
	initial	f_past_valid = 1'b0;
	always @(posedge i_pixclk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// AXI Stream assumptions
	//
	always @(posedge i_pixclk)
	if (f_past_valid && !$past(pix_reset))
	begin
		if ($past(i_valid && !o_ready))
		begin
			assume(i_valid);
			assume($stable(i_hlast));
			assume($stable(i_vlast));
			assume($stable(i_rgb_pix));
		end
	end

	generate if (OPT_RESYNC_ON_VLAST)
	begin : GEN_VIDCHECK
		// {{{
		localparam LGFRAME = (HW > VW) ? HW : VW;
		wire			f_vlast, f_hlast, f_sof, f_known_height;
		wire	[LGFRAME-1:0]	f_xpos, f_ypos;
		reg	[LGFRAME-1:0]	f_width, f_height;

		always @(posedge i_pixclk)
		if (!pix_reset && $past(pix_reset))
			assume(!i_valid);

		always @(*)
		begin
			f_width = 0; f_height = 0;
			f_width[HW-1:0]  = i_hm_width;
			f_height[VW-1:0] = i_vm_height;
		end

		faxivideo #(
			// {{{
			.LGDIM(LGFRAME), .PW(BPP), .OPT_TUSER_IS_SOF(1'b0),
			.OPT_SOURCE(1'b0)
			// }}}
		) fvid (
			// {{{
			.i_clk(i_pixclk), .i_reset_n(!pix_reset),
			//
			.S_VID_TVALID(i_valid && !lost_sync), .S_VID_TREADY(o_ready),
			.S_VID_TDATA(i_rgb_pix),.S_VID_TLAST(i_hlast&& i_vlast),
			.S_VID_TUSER(i_hlast),
			.i_width(f_width), .i_height(f_height),
			.o_xpos(f_xpos), .o_ypos(f_ypos),
				.f_known_height(f_known_height),
			.o_hlast(f_hlast), .o_vlast(f_vlast), .o_sof(f_sof)
			// }}}
		);

		always @(posedge i_pixclk)
		if (!i_reset && !lost_sync)
		begin
			if (w_rd)
				assume(i_valid);

			if (f_xpos != 0)
			begin
				assert(hpos == f_xpos - 1);
				assert(vpos == f_ypos);
			end else begin
				assert(hpos <= 1 || hpos >= f_width-1
					|| vpos >= i_vm_height);
				if (hpos < i_hm_width)
				begin
					assert(hpos == i_hm_width-1
						|| vpos == f_ypos
						|| (f_ypos == 0 && vpos >= f_height));	
				end else if (hpos < i_hm_porch)
				begin
					if (vpos < f_height-1)
					begin
						assert(vpos + 1== f_ypos);	
					end else begin
						assert(f_ypos == 0);
					end
				end else begin
					if (vpos <= f_height-1)
					begin
						assert(vpos == f_ypos);
					end else begin
						assert(f_ypos == 0);
					end
				end
			end

			if (f_ypos != 0)
			begin
			end else
				assert(vpos == 0 || vpos >= f_height -1);
		end else if (!i_reset)
		begin
			assert(f_xpos == 0);
			assert(f_ypos == 0);
		end

		always @(posedge i_pixclk)
		if (!i_reset && first_frame)
		begin
			assert(lost_sync);
			assert(!f_known_height);
			assert(f_xpos == 0);
			assert(f_ypos == 0);
		end

		always @(*)
			assume(i_hlast == f_hlast);

		always @(*)
		if (!f_vlast)
			assume(!i_vlast);
		else if (f_hlast)
			assume(i_vlast == f_hlast);
		// }}}
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Mode-line assumptions
	//
	always @(*)
	begin
		assume(12'h10 < i_hm_width);
		assume(i_hm_width < i_hm_porch);
		assume(i_hm_porch < i_hm_synch);
		assume(i_hm_synch < i_hm_raw);
		assume(i_hm_porch+14 < i_hm_raw);

		assume(12'h10 < i_vm_height);
		assume(i_vm_height < i_vm_porch);
		assume(i_vm_porch  < i_vm_synch);
		assume(i_vm_synch  < i_vm_raw);
	end

	assign	f_hmode = { i_hm_width,  i_hm_porch, i_hm_synch, i_hm_raw };
	assign	f_vmode = { i_vm_height, i_vm_porch, i_vm_synch, i_vm_raw };

	always @(posedge i_pixclk)
		f_last_vmode <= f_vmode;
	always @(posedge i_pixclk)
		f_last_hmode <= f_hmode;

	always @(*)
		f_stable_mode = (f_last_vmode == f_vmode)&&(f_last_hmode == f_hmode);

	always @(*)
	if (!pix_reset)
		assume(f_stable_mode);

	////////////////////////////////////////////////////////////////////////
	//
	// Pixel counting
	//

	always @(posedge i_pixclk)
	if ((!f_past_valid)||($past(pix_reset)))
	begin
		assert(hpos == 0);
		assert(vpos == 0);
		assert(first_frame);
	end

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(pix_reset))&&(!pix_reset)
			&&(f_stable_mode)&&($past(f_stable_mode)))
	begin
		if ($past(w_external_sync))
		begin
			assert(hpos == i_hm_width);
		end else if ($past(hpos >= i_hm_raw-1'b1))
		begin
			assert(hpos == 0);
		end else
			// The horizontal position counter should increment
			assert(hpos == $past(hpos)+1'b1);

		// The vertical position counter should increment
		if ($past(w_external_sync))
		begin
		end else if (hpos == i_hm_porch)
		begin
			if ($past(vpos >= i_vm_raw-1'b1))
			begin
				assert(vpos == 0);
			end else
				assert(vpos == $past(vpos)+1'b1);
		end else
			assert(vpos == $past(vpos));

		// For induction purposes, we need to insist that both
		// horizontal and vertical counters stay within their
		// required ranges
		assert(hpos < i_hm_raw);
		assert(vpos < i_vm_raw);

		// If we are less than the data width for both horizontal
		// and vertical, then we should be asserting we are in a
		// valid data cycle
		// if ((hpos < i_hm_width)&&(vpos < i_vm_height)
		//		&&(!first_frame))
		//	assert(w_rd);
		// else
		//	assert(!w_rd);

		//
		// The horizontal sync should only be valid between positions
		// i_hm_porch <= hpos < i_hm_sync, invalid at all other times
		//
		if (hpos < i_hm_porch)
		begin
			assert(!hsync);
		end else if (hpos < i_hm_synch)
		begin
			assert(hsync);
		end else
			assert(!hsync);

		// Same thing for vertical
		if (vpos < i_vm_porch)
		begin
			assert(!vsync);
		end else if (vpos < i_vm_synch)
		begin
			assert(vsync);
		end else
			assert(!vsync);

		// At the end of every horizontal line cycle, we assert
		// a new line
		if (hpos == i_hm_width-2)
		begin
			assert(r_newline);
		end else
			assert(!r_newline);

		// At the end of every vertical frame cycle, we assert
		// a new frame, but only on the newline measure
		if ((vpos == i_vm_height-1'b1)&&(r_newline))
		begin
			assert(r_newframe);
		end else
			assert(!r_newframe);
	end

	//////////////////////////////
	//
	// HDMI Specific properties
	//
	//////////////////////////////

	always @(posedge i_pixclk)
	if (pix_reset)
		f_ctrl_length <= 4'hf;
	else if (hdmi_type != CTL_PERIOD)
		f_ctrl_length <= 0;
	else if (f_ctrl_length < 4'hf)
		f_ctrl_length <= f_ctrl_length + 1'b1;

	initial	f_video_start = 2'b01;
	always @(posedge i_pixclk)
	if (pix_reset)
		f_video_start = 2'b01;
	else if ((f_video_start == 2'b00)
			&&(f_ctrl_length >= 4'hc)&&(hdmi_type == GUARD)
			&&(hdmi_ctl == 4'h1))
		f_video_start <= 2'b1;
	else if ((f_video_start == 2'b01)&&(hdmi_type == GUARD)
			&&(hdmi_ctl == 4'h1))
		f_video_start <= 2'b10;
	else
		f_video_start <= 2'b00;

	always @(posedge i_pixclk)
	if ((f_ctrl_length >= 4'hc)&&(hdmi_type == GUARD))
		f_packet_start <= 2'b1;
	else if ((f_packet_start == 2'b1)&&(hdmi_type == GUARD))
		f_packet_start <= 2'b10;
	else
		f_packet_start <= 2'b00;

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(pix_reset)))
	begin
		if (($past(hdmi_type != VIDEO_DATA))
				&&(f_video_start != 2'b10))
			assert(hdmi_type != VIDEO_DATA);
	end

	always @(posedge i_pixclk)
	if ((f_past_valid)&&(!$past(pix_reset))&&(!pix_reset))
	begin
		if ($past(w_external_sync))
		begin
		end else if ((hpos < i_hm_width)&&(vpos < i_vm_height))
		begin
			assert(hdmi_type == VIDEO_DATA);
		end else
			assert(hdmi_type != VIDEO_DATA);
		if (!$past(first_frame))
			assert($past(w_rd) == (hdmi_type == VIDEO_DATA));

		if (vpos < i_vm_height)
		begin
			if (hpos < i_hm_width)
				assert(hdmi_type == VIDEO_DATA);
			if (hpos >= (i_hm_raw-GUARD_PIXELS))
			begin
				assert(hdmi_type == GUARD);
			end else if (hpos >= (i_hm_raw-GUARD_PIXELS-PREGUARD_CONTROL))
				assert((hdmi_type == CTL_PERIOD)
					&&(hdmi_ctl == 4'h1));
		end
	end

	// always @(posedge i_pixclk)
	// if ((f_past_valid)&&(!$past(i_reset)))
		// assert(o_rd == (hdmi_type == VIDEO_DATA));

`ifdef	VERIFIC
	// {{{
	sequence	VIDEO_PREAMBLE;
		(hdmi_type == CTL_PERIOD) [*2]
		##1 ((hdmi_type == CTL_PERIOD)&&(hdmi_ctl == 4'h1)) [*10]
		##1 (hdmi_type == GUARD) [*2];
	endsequence

	assume property (@(posedge i_pixclk)
		VIDEO_PREAMBLE
		|=> (hdmi_type == VIDEO_DATA)&&(hpos == 0)&&(vpos == 0));

	// assert property (@(posedge i_pixclk)
	//	disable iff (pix_reset)
	//	((hdmi_type != VIDEO_DATA) throughout (not VIDEO_PREAMBLE)));

	//
	// Data Islands
	//
	sequence	DATA_PREAMBLE;
		(hdmi_type == CTL_PERIOD) [*2]
		##1 ((hdmi_type == CTL_PERIOD)&&(hdmi_ctl == 4'h5)) [*10]
		##1 (hdmi_type == GUARD) [*2];
	endsequence

	assert property (@(posedge i_pixclk)
		disable iff (pix_reset)
		(DATA_PREAMBLE)
		|=> 0 && (hdmi_type == DATA_ISLAND)[*64]
		##1 0 && (hdmi_type == GUARD) [*2]);

	// assert property (@(posedge i_pixclk)
	//	disable iff (pix_reset)
	//	((hdmi_type != DATA_ISLAND) throughout (not DATA_PREAMBLE))
	//	|=> (hdmi_type != DATA_ISLAND));

	// }}}
`endif
`endif
// }}}
endmodule
