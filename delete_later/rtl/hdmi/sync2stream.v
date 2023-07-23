////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sync2stream.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Given a VGA input, synchronize to it, count its size, and then
//		generate an AXI video stream output to encapsulate the stream.
//
//	NOTE: There's no FIFO here.  The outgoing video stream therefore
//	cannot handle *ANY* backpressure.
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
//
`default_nettype	none
// }}}
module	sync2stream #(
		// {{{
		parameter [0:0]	OPT_INVERT_HSYNC = 0,
		parameter [0:0]	OPT_INVERT_VSYNC = 0,
		parameter [0:0]	OPT_TUSER_IS_SOF = 0,
		parameter	LGDIM = 16
		// }}}
	) (
		// {{{
		input	wire				i_clk,
		input	wire				i_reset,
		//
		input	wire				i_pix_valid,
		input	wire				i_hsync,
		input	wire				i_vsync,
		input	wire	[24-1:0]		i_pixel,
		//
		output	reg				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	reg	[24-1:0]		M_AXIS_TDATA,	// Color
		output	wire				M_AXIS_TLAST,	// Vsync
		output	wire				M_AXIS_TUSER,	// Hsync
		//
		output	reg	[LGDIM-1:0]		o_width,
		output	reg	[LGDIM-1:0]		o_hfront,
		output	reg	[LGDIM-1:0]		o_hsync,
		output	reg	[LGDIM-1:0]		o_raw_width,
		//
		output	reg	[LGDIM-1:0]		o_height,
		output	reg	[LGDIM-1:0]		o_vfront,
		output	reg	[LGDIM-1:0]		o_vsync,
		output	reg	[LGDIM-1:0]		o_raw_height,
		//
		output	wire				o_locked
		// }}}
	);

	// Register/wire declarations
	// {{{
	wire		new_data_row, hsync, vsync;
	reg	[LGDIM:0]	hcount_pix, hcount_shelf, hcount_sync, hcount_tot;
	reg		hin_shelf, last_pv, hlocked;

	reg	linestart, has_pixels, has_vsync, newframe, last_hs,
		this_line_had_vsync, this_line_had_pixels, last_line_had_pixels;

	reg	[LGDIM:0]	vcount_lines, vcount_shelf, vcount_sync, vcount_tot;
	reg		vin_shelf, vlost_lock, vlocked;
	reg		empty_row;

	reg		M_AXIS_HLAST, M_AXIS_VLAST;
	// }}}

	// Adjust for sync inversion (if necessary)
	// {{{
	assign	hsync = OPT_INVERT_HSYNC ^ i_hsync;
	assign	vsync = OPT_INVERT_VSYNC ^ i_vsync;
	// }}}

	initial	last_pv = 0;
	always @(posedge i_clk)
		last_pv <= i_pix_valid;

	assign	new_data_row = (!last_pv)&&(i_pix_valid);

	////////////////////////////////////////////////////////////////////////
	//
	// Horizontal mode line
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// hcount* _pix, _shelf, _sync, _tot
	// {{{
	initial	hcount_pix   = 0;
	initial	hcount_shelf = 0;
	initial	hcount_sync  = 0;
	initial	hcount_tot   = 0;
	initial	hin_shelf    = 1'b1;
	initial	empty_row    = 1;
	always @(posedge i_clk)
	if (new_data_row)
	begin
		hcount_pix   <= 1;
		hcount_shelf <= 0;
		hcount_sync  <= 0;
		hcount_tot   <= 1;
		hin_shelf    <= 0;
		empty_row    <= 0;
	end else begin
		if (!hcount_tot[LGDIM])
			hcount_tot <= hcount_tot + 1'b1;
		if ((!hcount_pix[LGDIM])&&(i_pix_valid))
			hcount_pix <= hcount_pix + 1'b1;
		if ((!hcount_sync[LGDIM])&&(hsync))
			hcount_sync <= hcount_sync + 1'b1;
		if ((!hcount_sync[LGDIM])&&(hsync && !last_hs) && hcount_sync != 0)
			empty_row <= 1;
		if ((!hcount_shelf[LGDIM])&&(!i_pix_valid)
				&&(!hsync)&&(hin_shelf))
			hcount_shelf <= hcount_shelf + 1'b1;
		if (hsync)
			hin_shelf <= 1'b0;
	end
	// }}}

	// o_width, o_raw_width, o_hfront, o_hsync
	// {{{
	initial	o_width     = 0;
	initial	o_raw_width = 0;
	initial	o_hfront    = 0;
	initial	o_hsync     = 0;
	always @(posedge i_clk)
	if (new_data_row && !empty_row)
	begin
		o_width     <= hcount_pix[LGDIM-1:0]; // -16'd10;
		o_raw_width <= hcount_tot[LGDIM-1:0]; // +16'd1;
		o_hfront    <= hcount_pix[LGDIM-1:0] + hcount_shelf[LGDIM-1:0]; // + 16'd11;
		o_hsync     <= hcount_pix[LGDIM-1:0] + hcount_shelf[LGDIM-1:0] + hcount_sync[LGDIM-1:0];
	end
	// }}}

	// hlocked
	// {{{
	always @(posedge i_clk)
	begin
		if (new_data_row && !empty_row)
		begin
			hlocked <= 1;
			if ({ 1'b0, o_width } != hcount_pix)
				hlocked <= 0;
			if ({ 1'b0, o_raw_width } != hcount_tot)
				hlocked <= 0;
		end

		if (i_reset)
			hlocked <= 0;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Vertical mode line
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// last_hs
	// {{{
	initial	last_hs = 1'b0;
	always @(posedge i_clk)
		last_hs <= hsync;
	// }}}

	// linestart, has_pixels, has_vsync, newframe
	// {{{
	initial	linestart  = 1'b0;
	initial	has_pixels = 1'b0;
	initial	has_vsync  = 1'b0;
	initial	newframe   = 1'b0;
	always @(posedge i_clk)
	if ((!last_hs)&&(hsync))
	begin
		linestart  <= 1'b1;
		has_pixels <= 1'b0;
		has_vsync  <= 1'b0;
		this_line_had_vsync  <= has_vsync;
		this_line_had_pixels <= has_pixels;
		last_line_had_pixels <= last_line_had_pixels;
		newframe <= (has_pixels)&&(!this_line_had_pixels);
	end else begin
		linestart  <= 1'b0;
		newframe   <= 1'b0;
		if (i_pix_valid)
			has_pixels <= 1'b1;
		if (vsync)
			has_vsync  <= 1'b1;
	end
	// }}}

	// vcount* _lines, _shelf, _sync, _tot, _lock
	// {{{
	initial	vcount_lines = 1;
	initial	vcount_shelf = 0;
	initial	vcount_sync  = 0;
	initial	vcount_tot   = 1;
	initial	vlost_lock   = 1;
	always @(posedge i_clk)
	if (linestart)
	begin
		if (newframe)
		begin
			// We'll get here *after* the first line of a new frame
			// {{{
			vcount_lines <= 1;
			vcount_shelf <= 0;
			vcount_sync  <= 0;
			vcount_tot   <= 1;
			vin_shelf    <= 1'b1;
			vlost_lock   <= !hlocked;
			// }}}
		end else begin
			// Count up
			// {{{
			if (!vcount_tot[LGDIM])
				vcount_tot <= vcount_tot + 1'b1;
			if ((!vcount_lines[LGDIM])&&(this_line_had_pixels))
				vcount_lines <= vcount_lines + 1'b1;
			if ((!vcount_sync[LGDIM])&&(this_line_had_vsync))
				vcount_sync <= vcount_sync + 1'b1;
			if ((!vcount_shelf[LGDIM])&&(!this_line_had_pixels)
					&&(!this_line_had_vsync)&&(vin_shelf))
				vcount_shelf <= vcount_shelf + 1'b1;
			if (this_line_had_vsync)
				vin_shelf <= 1'b0;
			if (!hlocked)
				vlost_lock <= 1;
			// }}}
		end
	end
	// }}}

	// o_height, o_raw_height, o_vfront, o_vsync
	// {{{
	initial	o_height    = 0;
	initial	o_raw_height= 0;
	initial	o_vfront    = 0;
	initial	o_vsync     = 0;
	always @(posedge i_clk)
	if (newframe)
	begin
		o_height     <= vcount_lines[LGDIM-1:0];
		o_raw_height <= vcount_tot[LGDIM-1:0];
		o_vfront     <= vcount_shelf[LGDIM-1:0] + vcount_lines[LGDIM-1:0];
		o_vsync      <= vcount_sync[LGDIM-1:0] + vcount_shelf[LGDIM-1:0]
					+ vcount_lines[LGDIM-1:0] - 1;
	end
	// }}}

	// vlocked, o_locked
	// {{{
	initial	vlocked = 0;
	always @(posedge i_clk)
	begin
		if (newframe)
		begin
			vlocked <= !vlost_lock && !vcount_tot[LGDIM];
			if ({ 1'b0, o_height } != vcount_lines)
				vlocked <= 0;
			if ({ 1'b0, o_raw_height } != vcount_tot)
				vlocked <= 0;
		end

		if (!hlocked)
			vlocked <= 0;
		if (i_reset)
			vlocked <= 0;
	end

	assign	o_locked = vlocked;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pixel stream outputs
	// {{{

	// M_AXIS_TVALID
	// {{{
	always @(posedge i_clk)
		M_AXIS_TVALID <= i_pix_valid;
	// }}}

	// M_AXIS_TDATA
	// {{{
	always @(posedge i_clk)
		M_AXIS_TDATA <= i_pixel;
	// }}}

	// M_AXIS_HLAST -- last data in line signal
	// {{{
	always @(posedge i_clk)
		M_AXIS_HLAST <= !i_reset && i_pix_valid && (hcount_pix == o_width-1);
	// }}}

	// M_AXIS_VLAST -- last data in frame signal
	// {{{
	always @(posedge i_clk)
		M_AXIS_VLAST <= !i_reset && i_pix_valid
			&& (hcount_pix == o_width-1)
			&& (vcount_lines == o_height-1);
	// }}}

	// Adjust between VLAST == TLAST and TUSER == start of frame encodings
	// (I've chosen the former, Xilinx chose the latter)
	generate if (OPT_TUSER_IS_SOF)
	begin : XILINXS_ENCODING
		reg	sof;

		assign	M_AXIS_TLAST = M_AXIS_HLAST;

		always @(posedge i_clk)
		if (M_AXIS_TVALID)
			sof <= M_AXIS_VLAST;

		assign	M_AXIS_TUSER = sof;

	end else begin : VLAST_IS_TLAST

		assign	M_AXIS_TLAST = M_AXIS_VLAST;

		assign	M_AXIS_TUSER = M_AXIS_HLAST;

	end endgenerate
	// }}}

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXIS_TREADY };
	// Verilator lint_on  UNUSED
endmodule
