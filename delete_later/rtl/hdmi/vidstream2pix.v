////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vidstream2pix.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Converts an AXI-Stream of video data, packed into bus/memory
//		words, into a second AXI-stream of 24-bit pixels only.
//
//	Several color encodings are available:
//	3'b000:	Black and white.
//	3'b001: 2-bit gray scale
//	3'b010: 4-bit gray scale
//	3'b011: 4-bit colormap, using the first 16-entries of the color mapping
//			table
//	3'b100: 8-bit colormap
//	3'b101: 8-bit color, no color map, encoded as 3-bits of red, 3-bits of
//			green, and 2-bits of blue
//	3'b110: 16-bit color, encoded as 5-bits red, 6-bits green and 5-bits blu
//	3'b111: 24-bit color.  The upper 8-bits of every 32-bits are ignored
//			in this encoding.  (They are packed in other encodings)
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
module	vidstream2pix #(
		// {{{
		parameter	HMODE_WIDTH = 12,
		parameter [0:0]	OPT_MSB_FIRST = 1'b0,
		parameter 	BUS_DATA_WIDTH = 32,
		parameter [0:0]	OPT_TUSER_IS_SOF = 1'b0
		// }}}
	) (
		// {{{
		input	wire	i_clk,
		input	wire	i_reset,
		// Incoming video data from the memory bus
		// {{{
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire [BUS_DATA_WIDTH-1:0]	S_AXIS_TDATA,
		input	wire 				S_AXIS_TLAST,
		input	wire 				S_AXIS_TUSER,
		// }}}
		// Outgoing video pixel data
		// {{{
		output	wire				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	wire	[23:0]			M_AXIS_TDATA,	// Color
		output	reg				M_AXIS_TLAST,
		output	reg				M_AXIS_TUSER,
		// }}}
		// Control information
		// {{{
		input	wire	[2:0]			i_mode,
		input	wire [HMODE_WIDTH-1:0]		i_pixels_per_line,
		// }}}
		// Colormap control
		// {{{
		input	wire				i_cmap_clk,
		input	wire				i_cmap_rd,
		input	wire	[7:0]			i_cmap_raddr,
		output	reg	[23:0]			o_cmap_rdata,
		input	wire				i_cmap_we,
		input	wire	[7:0]			i_cmap_waddr,
		input	wire	[23:0]			i_cmap_wdata,
		input	wire	[2:0]			i_cmap_wstrb
		// }}}
		// }}}
	);

	// Register/net/localparam declarations
	// {{{
	localparam	[2:0]		MODE_BW		= 3'b000,
					MODE_GRAY2	= 3'b001,
					MODE_GRAY4	= 3'b010,
					MODE_CMAP4	= 3'b011,
					MODE_CMAP8	= 3'b100,
					MODE_CLR8	= 3'b101,
					MODE_CLR16	= 3'b110,
					MODE_DIRECT	= 3'b111;
	// Steps:
	//	t_	incoming data
	//	s_	Shift register
	//	c_	Colors
	//	m_	Outgoing data
	localparam	BASE_1 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 1) : 0;
	localparam	BASE_2 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 2) : 0;
	localparam	BASE_4 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 4) : 0;
	localparam	BASE_8 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH- 8) : 0;
	localparam	BASE16 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH-16) : 0;
	localparam	BASE32 = (OPT_MSB_FIRST) ? (BUS_DATA_WIDTH-32) : 0;

	reg	[23:0]	cmap	[0:255];

	reg				S_AXIS_HLAST, S_AXIS_FRAME;

	wire				skd_valid, skd_hlast, skd_frame;
	wire	[BUS_DATA_WIDTH-1:0]	skd_data;
	reg	[HMODE_WIDTH-1:0]	s_remaining;

	reg				s_valid, skd_ready, s_frame, s_hlast,
					s_last_in_word, s_last_word_in_packet;
	reg [$clog2(BUS_DATA_WIDTH)-1:0] scount;
	reg	[BUS_DATA_WIDTH-1:0]	sreg;
	wire				s_step;

	reg		c_hlast, c_valid, c_frame;
	reg	[23:0]	bw_pix, gray_2, gray_4, cmap_4, cmap_8, clr_8, clr_16,
			direct_clr;
	wire		c_step;

	reg	[23:0]			pix_data;
	reg	[HMODE_WIDTH-1:0]	pix_count;
	reg				pix_frame, pix_hlast, pix_valid;

	// integer			k;

	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(*)
			S_AXIS_HLAST = S_AXIS_TLAST;
		always @(*)
			S_AXIS_FRAME = S_AXIS_TUSER;
	end else begin
		always @(*)
			S_AXIS_HLAST = S_AXIS_TUSER;
		always @(*)
			S_AXIS_FRAME = S_AXIS_TLAST;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Colormap memory access (control interface)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_cmap_rdata, reading from the colormap
	// {{{
	always @(posedge i_cmap_clk)
	if (i_cmap_rd)
		o_cmap_rdata <= cmap[i_cmap_raddr];
	// }}}

	// Writes to the color map
	// {{{
	always @(posedge i_cmap_clk)
	if (i_cmap_we)
	begin
		if (i_cmap_wstrb[0])
			cmap[i_cmap_waddr][ 7: 0] <= i_cmap_wdata[ 7: 0];
		if (i_cmap_wstrb[1])
			cmap[i_cmap_waddr][15: 8] <= i_cmap_wdata[15: 8];
		if (i_cmap_wstrb[2])
			cmap[i_cmap_waddr][23:16] <= i_cmap_wdata[23:16];
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming skid buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		// {{{
		.OPT_OUTREG(1),
		.DW(BUS_DATA_WIDTH+2)
`ifdef	FORMAL
		, .OPT_PASSTHROUGH(1'b1)
`endif
		// }}}
	) tskd (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data({ S_AXIS_TDATA, S_AXIS_FRAME, S_AXIS_HLAST }),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data({ skd_data, skd_frame, skd_hlast })
		// }}}
	);

	always @(*)
		skd_ready = !s_valid || (s_step && s_last_in_word);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Shift register stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// sreg, s_valid, s_frame, scount, s_hlast, s_last_in_word,
	// s_last_word_in_packet
	// {{{
	initial	s_valid = 0;
	initial	scount  = 0;
	initial	s_hlast = 0;
	always @(posedge i_clk)
	begin
		if (skd_ready)
		begin
			// Accept a new bus word to be processed
			// {{{
			sreg    <= skd_data;
			s_valid <= skd_valid;
			s_frame <= skd_frame && skd_valid;

			if (!skd_hlast) case(i_mode)
			// Verilator lint_off WIDTH
			MODE_BW:	scount <= BUS_DATA_WIDTH - 1'b1;
			MODE_GRAY2:	scount <= BUS_DATA_WIDTH/2 - 1'b1;
			MODE_GRAY4:	scount <= BUS_DATA_WIDTH/4 - 1'b1;
			MODE_CMAP4:	scount <= BUS_DATA_WIDTH/4 - 1'b1;
			MODE_CMAP8:	scount <= BUS_DATA_WIDTH/8 - 1'b1;
			MODE_CLR8:	scount <= BUS_DATA_WIDTH/8 - 1'b1;
			MODE_CLR16:	scount <= BUS_DATA_WIDTH/16 - 1'b1;
			MODE_DIRECT:	scount <= BUS_DATA_WIDTH/32 - 1'b1;
			endcase else
				scount <= s_remaining - 1'b1;
			// Verilator lint_on  WIDTH
			if (!skd_valid)
				scount <= 0;

			s_last_word_in_packet <= (skd_valid) ? skd_hlast : 0;
			if (!skd_valid)
			begin
				s_last_in_word <= 0;
				s_hlast <= 0;
			end else if (i_mode == MODE_DIRECT && BUS_DATA_WIDTH == 32)
			begin
				s_last_in_word <= 1;
				s_hlast <= skd_hlast;
			end else if (!skd_hlast)
			begin
				s_last_in_word <= 1'b0;
				s_hlast <= 1'b0;
			end else begin // if valid && read && hlast && ...
				s_last_in_word <= (s_remaining == 1);
				s_hlast <= (s_remaining == 1);
			end
			// }}}
		end else if (s_valid && s_step)
		begin
			// Process the next pixel of the bus word
			// {{{

			// sreg
			// {{{
			if (OPT_MSB_FIRST)
			case(i_mode)
			MODE_BW:	sreg <= sreg << 1;
			MODE_GRAY2:	sreg <= sreg << 2;
			MODE_GRAY4:	sreg <= sreg << 4;
			MODE_CMAP4:	sreg <= sreg << 4;
			MODE_CMAP8:	sreg <= sreg << 8;
			MODE_CLR8:	sreg <= sreg << 8;
			MODE_CLR16:	sreg <= sreg << 16;
			MODE_DIRECT:	begin end
			endcase else case(i_mode)
			MODE_BW:	sreg <= sreg >> 1;
			MODE_GRAY2:	sreg <= sreg >> 2;
			MODE_GRAY4:	sreg <= sreg >> 4;
			MODE_CMAP4:	sreg <= sreg >> 4;
			MODE_CMAP8:	sreg <= sreg >> 8;
			MODE_CLR8:	sreg <= sreg >> 8;
			MODE_CLR16:	sreg <= sreg >> 16;
			MODE_DIRECT:	sreg <= sreg >> 32;
			endcase
			// }}}

			if (scount == 0)
				s_valid <= 0;
			if (scount <= 1)
				s_last_in_word <= 1;
			if (scount <= 1)
				s_hlast <= s_last_word_in_packet;
			if (scount > 0)
				scount <= scount - 1;

			if (OPT_TUSER_IS_SOF)
				s_frame <= 0;
			// }}}
		end

		// Reset any values on i_reset
		// {{{
		if (i_reset)
		begin
			s_valid  <= 0;
			s_last_in_word <= 1;
			s_last_word_in_packet <= 0;
			s_hlast  <= 0;
			scount   <= 0;
		end
		// }}}
	end
	// }}}

	// s_remaining
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		s_remaining <= i_pixels_per_line;
	else if (skd_valid && skd_ready)
	begin
		if (skd_hlast)
			s_remaining <= i_pixels_per_line;
		else case(i_mode)
		// Verilator lint_off WIDTH
		MODE_BW:	s_remaining <= s_remaining - BUS_DATA_WIDTH;
		MODE_GRAY2:	s_remaining <= s_remaining - BUS_DATA_WIDTH/2;
		MODE_GRAY4:	s_remaining <= s_remaining - BUS_DATA_WIDTH/4;
		MODE_CMAP4:	s_remaining <= s_remaining - BUS_DATA_WIDTH/4;
		MODE_CMAP8:	s_remaining <= s_remaining - BUS_DATA_WIDTH/8;
		MODE_CLR8:	s_remaining <= s_remaining - BUS_DATA_WIDTH/8;
		MODE_CLR16:	s_remaining <= s_remaining - BUS_DATA_WIDTH/16;
		MODE_DIRECT:	s_remaining <= s_remaining - BUS_DATA_WIDTH/32;
		// Verilator lint_on  WIDTH
		endcase
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The color stage selects from among the various color mappings
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// c_hlast, c_valid, c_frame
	// {{{
	initial	c_hlast = 1;
	initial	c_frame = (OPT_TUSER_IS_SOF);
	initial	c_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		c_hlast <= 1;
		c_valid <= 0;
		c_frame <= (OPT_TUSER_IS_SOF);
	end else if (s_step)
	begin
		c_hlast <= s_hlast;
		c_valid <= s_valid;
		if (OPT_TUSER_IS_SOF)
			c_frame <= s_frame;
		else
			c_frame <= s_frame && s_hlast;
	end
	// }}}

	// bw_pix, gray_2
	// {{{
	always @(posedge i_clk)
	if (s_step)
		bw_pix <= sreg[BASE_1] ? 24'hFFFFFF : 24'h000000;
	// }}}

	// gray_2
	// {{{
	always @(posedge i_clk)
	if (s_step)
	case(sreg[BASE_2 +: 2])
	2'b00: gray_2 <= 24'h000000;
	2'b01: gray_2 <= 24'h555555;
	2'b10: gray_2 <= 24'haaaaaa;
	2'b11: gray_2 <= 24'hFFFFFF;
	endcase
	// }}}

	// gray_4
	// {{{
	always @(posedge i_clk)
	if (s_step)
		gray_4 <= {(6){sreg[BASE_4 +: 4]}};
	// }}}

	// cmap_4
	// {{{
	always @(posedge i_clk)
	if (s_step)
		cmap_4 <= cmap[{ 4'h0, sreg[BASE_4 +: 4] }];
	// }}}

	// cmap_8
	// {{{
	always @(posedge i_clk)
	if (s_step)
		cmap_8 <= cmap[sreg[BASE_8 +: 8]];
	// }}}

	// clr_8
	// {{{
	always @(posedge i_clk)
	if (s_step)
	begin	// RRR.GGG.BB, 3R, 3G, 2B
		clr_8[23:16] <= {{(2){ sreg[BASE_8+5 +:3]}},sreg[BASE_8+6 +:2]};
		clr_8[15: 8] <= {{(2){ sreg[BASE_8+2 +:3]}},sreg[BASE_8+3 +:2]};
		clr_8[ 7: 0] <= {(4){sreg[BASE_8    +: 2]} };
	end
	// }}}

	// clr_16
	// {{{
	always @(posedge i_clk)
	if (s_step)
	begin	// RRRRR.GGGGGG.BBBBB, 5R, 6G, 5B
		clr_16[23:16] <= { sreg[BASE16+11 +: 5], sreg[BASE16+13 +: 3] };
		clr_16[15: 8] <= { sreg[BASE16+ 5 +: 6], sreg[BASE16+ 9 +: 2] };
		clr_16[ 7: 0] <= { sreg[BASE16    +: 5], sreg[BASE16+ 2 +: 3] };
	end
	// }}}

	// direct_clr
	// {{{
	always @(posedge i_clk)
	if (s_step)
		direct_clr <= sreg[BASE32 +: 24];
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Selection from among the various color maps
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// pix_data
	// {{{
	always @(posedge i_clk)
	if (c_step)
	case(i_mode)
	MODE_BW:	pix_data <= bw_pix;
	MODE_GRAY2:	pix_data <= gray_2;
	MODE_GRAY4:	pix_data <= gray_4;
	MODE_CMAP4:	pix_data <= cmap_4;
	MODE_CMAP8:	pix_data <= cmap_8;
	MODE_CLR8:	pix_data <= clr_8;
	MODE_CLR16:	pix_data <= clr_16;
	MODE_DIRECT:	pix_data <= direct_clr;
	endcase
	// }}}

	// pix_valid, pix_frame
	// {{{
	initial	pix_valid = 1'b0;
	initial	pix_frame = OPT_TUSER_IS_SOF;
	always @(posedge i_clk)
	if (i_reset)
		{ pix_valid, pix_frame } <= { 1'b0, OPT_TUSER_IS_SOF };
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		pix_valid <= c_valid;
		pix_frame <= c_frame;
	end
	// }}}

	// pix_hlast, pix_count
	// {{{
	initial	pix_hlast = 1;
	initial	pix_count = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		pix_hlast <= 1;
		pix_count <= 0;
	end else if ((!M_AXIS_TVALID || M_AXIS_TREADY) && c_valid)
	begin
		if (!c_hlast)
		begin
			pix_hlast  <= 0;
			pix_count <= pix_count - 1;
		end else // if (!M_AXIS_TLAST)
		begin
			pix_hlast <= 1;
			pix_count <= i_pixels_per_line - 1;
		end
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pipeline control, and final output settings
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	s_step = !c_valid || c_step;
	assign	c_step = (!M_AXIS_TVALID || M_AXIS_TREADY);
	assign	M_AXIS_TVALID = pix_valid;
	assign	M_AXIS_TDATA  = pix_data;

	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(*)
		begin
			M_AXIS_TLAST  = pix_hlast;	// HLAST
			M_AXIS_TUSER  = pix_frame;	// SOF
		end
	end else begin
		always @(*)
		begin
			M_AXIS_TLAST  = pix_frame;	// VLAST
			M_AXIS_TUSER  = pix_hlast;	// HLAST
		end
	end endgenerate
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
	// Register/net declarations necessary for formal
	// {{{
	(* anyconst *)	reg	[15:0]	f_lines_per_frame;
	reg	[HMODE_WIDTH-1:0]	f_pixel_x, f_bus_x, f_s_x, f_c_x,
					f_bus_words_per_line;
	reg	[15:0]			f_bus_y, f_s_y, f_c_y;
	reg	[15:0]			f_pixel_y;
	reg				f_past_valid;
	reg				M_AXIS_FRAME, M_AXIS_HLAST;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
		M_AXIS_HLAST = pix_hlast;

	always @(*)
	if (OPT_TUSER_IS_SOF)
		M_AXIS_FRAME = M_AXIS_TUSER;
	else
		M_AXIS_FRAME = M_AXIS_TLAST;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus (input) framing assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	case(i_mode)
	MODE_BW:     f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH-1)) /  BUS_DATA_WIDTH;
	MODE_GRAY2:  f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/2-1)) / (BUS_DATA_WIDTH/2);
	MODE_GRAY4:  f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/4-1)) / (BUS_DATA_WIDTH/4);
	MODE_CMAP4:  f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/4-1)) / (BUS_DATA_WIDTH/4);
	MODE_CMAP8:  f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/8-1)) / (BUS_DATA_WIDTH/8);
	MODE_CLR8:   f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/8-1)) / (BUS_DATA_WIDTH/8);
	MODE_CLR16:  f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/16-1)) / (BUS_DATA_WIDTH/16);
	MODE_DIRECT: f_bus_words_per_line = (i_pixels_per_line + (BUS_DATA_WIDTH/32-1)) /(BUS_DATA_WIDTH/32);
	endcase

	initial	f_bus_x = 0;
	initial	f_bus_y = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		f_bus_x <= 0;
		f_bus_y <= 0;
	end else if (S_AXIS_TVALID && S_AXIS_TREADY)
	begin
		f_bus_x <= f_bus_x + 1;
		if (S_AXIS_HLAST)
		begin
			f_bus_x <= 0;
			f_bus_y <= f_bus_y + 1;
			if (f_bus_y + 1 == f_lines_per_frame)
				f_bus_y <= 0;
		end
	end

	always @(*)
	if (!i_reset && S_AXIS_TVALID)
	begin
		assume(S_AXIS_HLAST ==(f_bus_x == (f_bus_words_per_line - 1)));
		if (OPT_TUSER_IS_SOF)
		begin
			assume(S_AXIS_FRAME == ((f_bus_x== 0)&&(f_bus_y == 0)));
		end else
			assume(S_AXIS_FRAME == (S_AXIS_HLAST
					&& (f_bus_y == f_lines_per_frame-1)));
	end
	// }}}

	always @(posedge i_clk)
	if (!i_reset)
		assert(f_bus_x < f_bus_words_per_line);

	always @(posedge i_clk)
	if (!i_reset)
		assert(f_bus_y < f_lines_per_frame);

	always @(*)
	if (!f_past_valid)
		assume(!S_AXIS_TVALID);

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
		assume($stable(S_AXIS_TUSER));
		assume($stable(S_AXIS_TLAST));
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Pixel (output) framing assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// Make sure N pixels per line turns into ... N pixels per line
	// SOF is the first pixel of any group

	// Count pixels, f_pixel_*
	// {{{
	initial	f_pixel_x = 0;
	initial	f_pixel_y = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		f_pixel_x <= 0;
		f_pixel_y <= 0;
	end else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		f_pixel_x <= f_pixel_x + 1;
		if (M_AXIS_HLAST)
		begin
			f_pixel_x <= 0;
			f_pixel_y <= f_pixel_y + 1;
			if (f_pixel_y + 1 >= f_lines_per_frame)
				f_pixel_y <= 0;
		end
	end
	// }}}

	always @(posedge i_clk)
	if (!i_reset)
		assert(f_pixel_x < i_pixels_per_line);

	always @(posedge i_clk)
	if (!i_reset && M_AXIS_TVALID)
	begin
		assert(M_AXIS_HLAST == (f_pixel_x+1 == i_pixels_per_line));
		if (!OPT_TUSER_IS_SOF)
		begin
			if (!M_AXIS_HLAST)
			begin
				assert(!M_AXIS_FRAME);
			end
			assert(f_pixel_y < f_lines_per_frame);
			if (M_AXIS_FRAME)
			begin
				assert(f_pixel_y + 1 == f_lines_per_frame);
			end else
				assert(f_pixel_y <= f_lines_per_frame - 1);
		end else begin
			assert(f_pixel_y <= f_lines_per_frame);
			assert(M_AXIS_FRAME == ((f_pixel_y == 0)&&(f_pixel_x == 0)));
		end

		assert(M_AXIS_HLAST == (f_pixel_x+1 == i_pixels_per_line));
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TUSER));
		assert($stable(M_AXIS_TLAST));
	end

	// always @(posedge i_clk)
	// if (!i_reset && M_AXIS_TVALID &&)
		// assert(f_pixel_x == i_pixels_per_line);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// s_*
	// {{{

	// s_remaining -- tied to f_bus_x and i_pixels_per_line
	// {{{
	always @(posedge i_clk)
	if (!i_reset) case(i_mode)
	MODE_BW:     assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH) == i_pixels_per_line);
	MODE_GRAY2:  assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/2) == i_pixels_per_line);
	MODE_GRAY4:  assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/4) == i_pixels_per_line);
	MODE_CMAP4:  assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/4) == i_pixels_per_line);
	MODE_CMAP8:  assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/8) == i_pixels_per_line);
	MODE_CLR8:   assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/8) == i_pixels_per_line);
	MODE_CLR16:  assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/16) == i_pixels_per_line);
	MODE_DIRECT: assert(s_remaining + (f_bus_x * BUS_DATA_WIDTH/32) == i_pixels_per_line);
	endcase
	// }}}

	// f_s_*
	// {{{
	initial	f_s_x = 0;
	initial	f_s_y = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		f_s_x <= 0;
		f_s_y <= 0;
	end else if (s_valid && s_step)
	begin
		f_s_x <= f_s_x + 1;
		if (s_hlast)
		begin
			f_s_x <= 0;
			f_s_y <= f_s_y + 1;
			if (f_s_y + 1 >= f_lines_per_frame)
				f_s_y <= 0;
		end
	end
	// }}}

	// s_hlast
	// {{{
	always @(posedge i_clk)
	if (!i_reset && s_valid)
		assert(s_hlast == (f_s_x + 1 == i_pixels_per_line));
	// }}}

	// scount
	// {{{
	always @(*)
	if (scount > 0)
		assert(s_valid);

	always @(posedge i_clk)
	if (!i_reset) case(i_mode)
	MODE_BW:	assert(scount < BUS_DATA_WIDTH);
	MODE_GRAY2:	assert(scount < BUS_DATA_WIDTH/2);
	MODE_GRAY4:	assert(scount < BUS_DATA_WIDTH/4);
	MODE_CMAP4:	assert(scount < BUS_DATA_WIDTH/4);
	MODE_CMAP8:	assert(scount < BUS_DATA_WIDTH/8);
	MODE_CLR8:	assert(scount < BUS_DATA_WIDTH/8);
	MODE_CLR16:	assert(scount < BUS_DATA_WIDTH/16);
	MODE_DIRECT:	assert(scount < BUS_DATA_WIDTH/32);
	endcase
	// }}}

	// s_last_in_word
	// {{{
	always @(posedge i_clk)
	if (!i_reset && s_valid)
		assert(s_last_in_word == (scount == 0));
	// }}}

	// s_last_word_in_packet
	// {{{
	always @(posedge i_clk)
	if (!i_reset && s_valid)
		assert(s_last_word_in_packet == (f_bus_x == 0));
	// }}}

	// assert(f_s_x ==
	// {{{
	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (c_valid && !c_hlast)
		begin
			assert(f_s_x == f_c_x + 1);
		end else if (c_valid && c_hlast)
		begin
			assert(f_s_x == 0);
		end else
			assert(f_s_x == f_c_x);
	end

	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (f_bus_x != 0 || !s_valid)
		begin
			assert(f_s_y == f_bus_y);
		end else if (f_bus_y == 0)
		begin
			assert(f_s_x == 0 || f_s_x + scount == i_pixels_per_line-1);
			assert(f_s_y == 0 || f_s_y == f_lines_per_frame-1);
			if (f_s_x > 0)
				assert(f_s_y != 0);
		end else begin
			assert(f_s_x + scount + (s_valid ? 1:0) == i_pixels_per_line);
			assert(f_s_y == f_bus_y-(s_valid ? 1:0));
		end

		// Relate f_s_x, scount, s_valid, and f_bus_x
		// {{{
		if (f_bus_x != 0)
		case(i_mode)
		MODE_BW:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH));
		MODE_GRAY2:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/2));
		MODE_GRAY4:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/4));
		MODE_CMAP4:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/4));
		MODE_CMAP8:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/8));
		MODE_CLR8:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/8));
		MODE_CLR16:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/16));
		MODE_DIRECT:	assert(f_s_x + scount + (s_valid ? 1:0) == (f_bus_x * BUS_DATA_WIDTH/32));
		endcase
		// }}}
		else if (f_s_x != 0)
		begin
			assert(f_s_x + scount + (s_valid ? 1:0) == i_pixels_per_line);
		end else
			assert(!s_valid);
	end
	// }}}

	// assert(f_s_y ==
	// {{{
	always @(*)
		assert(f_s_y < f_lines_per_frame);

	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (c_valid && c_hlast)
		begin
			if (f_c_y >= f_lines_per_frame - 1)
			begin
				assert(f_s_y == 0);
			end else
				assert(f_s_y == f_c_y + 1);
		end else
			assert(f_s_y == f_c_y);
	end

	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (!s_valid)
		begin
			assert(f_s_y == f_bus_y);
		end else if (!s_last_word_in_packet)
		begin
			assert(f_s_y == f_bus_y);
		end else if (f_bus_y > 0)
		begin
			assert(f_s_y == f_bus_y - 1);
		end else
			assert(f_s_y == 0 || f_s_y == f_lines_per_frame-1);
	end
	// }}}

	// assert(s_frame
	// {{{
	always @(posedge i_clk)
	if (!i_reset && s_valid)
	begin
		if (OPT_TUSER_IS_SOF)
		begin
			assert(s_frame == (f_s_y == 0 && f_s_x == 0));
		end else
			assert(s_frame == (f_s_y == f_lines_per_frame - 1
					&& f_s_x + (scount+(s_valid ? 1:0))
							>= i_pixels_per_line));
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// c_* stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_c_x = 0;
	initial	f_c_y = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		f_c_x <= 0;
		f_c_y <= 0;
	end else if (c_valid && c_step)
	begin
		f_c_x <= f_c_x + 1;
		if (c_hlast)
		begin
			f_c_x <= 0;
			f_c_y <= f_c_y + 1;
			if (f_c_y + 1 >= f_lines_per_frame)
				f_c_y <= 0;
		end
	end


	// assert(f_c_x ==
	// {{{
	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (M_AXIS_TVALID && !M_AXIS_HLAST)
		begin
			assert(f_c_x == f_pixel_x + 1);
		end else if (M_AXIS_TVALID && M_AXIS_HLAST)
		begin
			assert(f_c_x == 0);
		end else
			assert(f_c_x == f_pixel_x);

		assert(f_c_x < i_pixels_per_line);
	end
	// }}}

	// assert(f_c_y ==
	// {{{
	always @(posedge i_clk)
	if (!i_reset)
		assert(f_c_y < f_lines_per_frame);

	always @(posedge i_clk)
	if (!i_reset)
	begin
		if (pix_valid && pix_hlast)
		begin
			if (f_pixel_y >= f_lines_per_frame - 1)
			begin
				assert(f_c_y == 0);
			end else
				assert(f_c_y == f_pixel_y + 1);
		end else
			assert(f_c_y == f_pixel_y);
	end
	// }}}

	// c_hlast && c_frame
	// {{{
	always @(posedge i_clk)
	if (!i_reset && c_valid)
	begin
		assert(c_hlast == (f_c_x + 1 == i_pixels_per_line));
		if (OPT_TUSER_IS_SOF)
		begin
			assert(c_frame == ((f_c_x == 0)&&(f_c_y == 0)));
		end else
			assert(c_frame == (c_hlast && (f_c_y + 1 == f_lines_per_frame)));
		/*
		if (OPT_TUSER_IS_SOF)
		begin
			assert(c_frame == ((f_c_x == 0)&&(f_c_y == 0)));
		end else begin
			if (!c_hlast)
				assert(!c_frame);
			else if (f_c_y != f_lines_per_frame - 1)
				assert(!c_frame);
			else
				assert(c_frame);
		end
		*/
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Cover checking
	// {{{

	reg	[3:0]	cvr_frames;

	initial	cvr_frames = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_frames = 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
		cvr_frames <= cvr_frames + M_AXIS_FRAME;

	always @(*)
	if (!i_reset)
		cover(cvr_frames > 2);

	always @(posedge i_clk)
	if (!i_reset && cvr_frames > 2)
	begin
		// cover(i_mode == 3'b000);	// These take too long
		// cover(i_mode == 3'b001);	// These take too long
		cover(i_mode == 3'b010);	// step 59, 13:38
		cover(i_mode == 3'b011);	// step 59, 12:14
		cover(i_mode == 3'b100);	// step 35
		cover(i_mode == 3'b101);	// step 35
		cover(i_mode == 3'b110);	// step 23
		cover(i_mode == 3'b111);	// step 17
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		assume(f_bus_words_per_line > 1);

	always @(*)
		assume(f_lines_per_frame > 1);

	always @(posedge i_clk)
	if (!i_reset)
		assume($stable(i_mode));

	always @(posedge i_clk)
	if (!i_reset)
		assume($stable(i_pixels_per_line));
	// }}}
`endif
// }}}
endmodule
