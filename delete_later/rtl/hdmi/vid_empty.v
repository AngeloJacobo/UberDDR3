////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	vid_empty.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Generates an outgoing video stream, having all the proper
//		video stream signals, but with a constant pixel value.
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
module	vid_empty #(
		// {{{
		parameter		PW = 24,
		parameter		LGFRAME = 12,
		parameter [PW-1:0]	PIXEL = 0,
		parameter [0:0]		OPT_TUSER_IS_SOF = 1
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		//
		input	wire	[LGFRAME-1:0]	i_width, i_height,
		//
		output	reg			M_VID_VALID,
		input	wire			M_VID_READY,
		output	wire	[PW-1:0]	M_VID_DATA,
		output	wire			M_VID_LAST,
		output	wire			M_VID_USER
		// }}}
	);

	// Local declarations
	// {{{
	reg			hlast, vlast;
	reg	[LGFRAME-1:0]	xpos, ypos;
	// }}}

	// M_VID_VALID
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		M_VID_VALID <= 0;
	else
		M_VID_VALID <= 1;
	// }}}

	assign	M_VID_DATA = PIXEL;

	// xpos, ypos, hlast, vlast
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		xpos  <= 0;
		ypos  <= 0;
		hlast <= 0;
		vlast <= 0;
	end else if (M_VID_VALID && M_VID_READY)
	begin
		xpos <= xpos + 1;
		hlast <= (xpos >= i_width-2);

		if (hlast)
		begin
			hlast <= 0;
			xpos  <= 0;
			vlast <= (ypos >= i_height-2);
			ypos  <= ypos + 1;

			if (vlast)
			begin
				vlast <= 0;
				ypos  <= 0;
			end
		end
	end
	// }}}

	generate if (OPT_TUSER_IS_SOF)
	begin
		reg	sof;

		always @(posedge i_clk)
		if (i_reset)
			sof <= 1;
		else if (M_VID_VALID && M_VID_READY)
			sof <= hlast && vlast;

		assign	M_VID_LAST = hlast;
		assign	M_VID_USER = sof;
`ifdef	FORMAL
		always @(*)
		if (!i_reset)
			assert(sof == (xpos == 0 && ypos == 0));
`endif
	end else begin
		assign	M_VID_LAST = vlast & hlast;
		assign	M_VID_USER = hlast;
	end endgenerate
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
	wire	[LGFRAME-1:0]	f_xpos, f_ypos;
	wire			f_hlast, f_vlast, f_sof, f_known_height;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!i_reset)
	begin
		assume($stable(i_width));
		assume($stable(i_height));

		assume(i_width  > 2);
		assume(i_height > 2);
	end

	faxivideo #(
		// {{{
		.PW(PW), .LGDIM(LGFRAME), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
		// }}}
	) fvid (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.S_VID_TVALID(M_VID_VALID),
		.S_VID_TREADY(M_VID_READY),
		.S_VID_TDATA(M_VID_DATA),
		.S_VID_TLAST(M_VID_LAST),
		.S_VID_TUSER(M_VID_USER),
		//
		.i_width(i_width), .i_height(i_height),
		.o_xpos(f_xpos), .o_ypos(f_ypos),
		.f_known_height(f_known_height),
		.o_hlast(f_hlast), .o_vlast(f_vlast), .o_sof(f_sof)
		// }}}
	);

	always @(*)
	if (!i_reset)
	begin
		assert(xpos == f_xpos);
		assert(ypos == f_ypos);
		assert(hlast == f_hlast);
		assert(vlast == f_vlast);
	end

	always @(*)
		cover(!i_reset && M_VID_VALID && hlast && vlast);

	generate if (OPT_TUSER_IS_SOF)
	begin
		always @(posedge i_clk)
			cover(!i_reset && M_VID_VALID && $rose(M_VID_USER));
	end endgenerate
`endif
// }}}
endmodule
