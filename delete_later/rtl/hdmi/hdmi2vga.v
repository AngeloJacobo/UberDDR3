////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmi2vga.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Convert an HDMI input stream into an outgoing VGA stream,
//		for further processing as a (nearly video format independent)
//	stream.
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
module	hdmi2vga // #()	// No parameters (yet)
	(
		// {{{
		input	wire	i_clk,	i_reset,
		input	wire	[9:0]	i_hdmi_blu,
		input	wire	[9:0]	i_hdmi_grn,
		input	wire	[9:0]	i_hdmi_red,
		//
		output	reg		o_pix_valid,
		output	reg		o_vsync,
		output	reg		o_hsync,
		output	reg	[7:0]	o_vga_red, o_vga_green, o_vga_blue
		// }}}
	);

	// Register/wire definitions
	// {{{
	wire	[9:0]	blu_word, grn_word, red_word;
	// Decoded data, not yet word synchronized
	wire	[1:0]	ublu_ctl, ugrn_ctl, ured_ctl;
	wire	[6:0]	ublu_aux, ugrn_aux, ured_aux;
	wire	[7:0]	ublu_pix, ugrn_pix, ured_pix;
	// now synchronized word dsata
	reg	[1:0]	sblu_ctl, sgrn_ctl, sred_ctl;
	reg	[6:0]	sblu_aux, sgrn_aux, sred_aux;
	reg	[7:0]	sblu_pix, sgrn_pix, sred_pix;

	reg	[9:0]	video_control_blu, video_control_grn, video_control_red;
	reg	[1:0]	video_guard_blu, video_guard_grn, video_guard_red;
	reg	[2:0]	video_start_blu, video_start_grn, video_start_red;
	reg		video_start, video_period;

	reg	[9:0]	data_control_blu, data_control_grn, data_control_red;
	reg	[1:0]	data_guard_blu, data_guard_grn, data_guard_red;
	reg	[2:0]	data_start_blu, data_start_grn, data_start_red;
	reg		data_start, data_guard; // data_period;

	reg		lag_blu, lag_red, lag_grn;
	reg	[16:0]	lag_data_blu, lag_data_red, lag_data_grn;

	reg		non_video_data, control_sync;
	reg	[11:0]	control_sync_sreg;

	wire	[31:0]	sync_word;

	reg	[7:0]	blu_pixel, grn_pixel, red_pixel;

	reg		r_pix_valid;
	reg	[7:0]	r_vga_red, r_vga_green, r_vga_blue;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Bit synchronization: [clr]_word and sync_word generation
	// {{{
	hdmibitsync
	bitsync(i_clk, i_reset, i_hdmi_blu, i_hdmi_grn, i_hdmi_red,
			blu_word, grn_word, red_word, sync_word);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// TMDS decoding
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	tmdsdecode
	decblu(i_clk, blu_word, ublu_ctl, ublu_aux, ublu_pix);

	tmdsdecode
	decgrn(i_clk, grn_word, ugrn_ctl, ugrn_aux, ugrn_pix);

	tmdsdecode
	decred(i_clk, red_word, ured_ctl, ured_aux, ured_pix);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video data start detection, and channel sync
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// video_control_blu, video_guard_blu => video_start_blu
	// {{{
	initial	video_control_blu = 0;
	always @(posedge i_clk)
		video_control_blu <= {video_control_blu[8:0], ublu_aux[4] };

	initial	video_guard_blu = 0;
	always @(posedge i_clk)
		video_guard_blu <= {video_guard_blu[0],
				ublu_aux[6] && !ublu_aux[0] };

	initial	video_start_blu = 0;
	always @(posedge i_clk)
		video_start_blu <= { video_start_blu[1:0],
			(&video_control_blu[9:2])&&(&video_guard_blu) };
	// }}}

	// video_control_grn, video_guard_grn => video_start_grn
	// {{{
	initial	video_control_grn = 0;
	always @(posedge i_clk)
		video_control_grn <= {video_control_grn[8:0],
				ugrn_aux[4] && ugrn_ctl == 2'b10 };

	initial	video_guard_grn = 0;
	always @(posedge i_clk)
		video_guard_grn <= {video_guard_grn[0],
				ugrn_aux[6] && ugrn_aux[0] };

	initial	video_start_grn = 0;
	always @(posedge i_clk)
		video_start_grn <= { video_start_grn[1:0],
			(&video_control_grn[9:2])&&(&video_guard_grn) };
	// }}}

	// video_control_red, video_guard_red => video_start_red
	// {{{
	initial	video_control_red = 0;
	always @(posedge i_clk)
		video_control_red <= {video_control_red[8:0],
				ured_aux[4] && ured_ctl == 2'b00 };

	initial	video_guard_red = 0;
	always @(posedge i_clk)
		video_guard_red <= {video_guard_red[0],
				ured_aux[6] && !ured_aux[0] };

	initial	video_start_red = 0;
	always @(posedge i_clk)
		video_start_red <= { video_start_red[1:0],
			(&video_control_red[9:2])&&(&video_guard_red) };
	// }}}

	// video_start, lag_[clr]
	// {{{
	initial	video_start = 1'b0;
	always @(posedge i_clk)
		video_start <= (|video_start_red) && (|video_start_grn)
				&&(|video_start_blu)
			&&(|{ video_start_red[0], video_start_grn[0],
				video_start_blu[0] });

	always @(posedge i_clk)
	if (video_start)
	begin
		lag_blu <= video_start_blu[1];
		lag_grn <= video_start_grn[1];
		lag_red <= video_start_red[1];
	end
	// }}}

	// lag_data_[clr], s[clr]_[ctl,aux,pix]: Frame sync
	// {{{
	// bit sync achieved above, now we align our various color channels
	always @(posedge i_clk)
	begin
		lag_data_blu <= { ublu_ctl, ublu_aux, ublu_pix };
		lag_data_grn <= { ugrn_ctl, ugrn_aux, ugrn_pix };
		lag_data_red <= { ured_ctl, ured_aux, ured_pix };

		if (lag_blu)
			{ sblu_ctl, sblu_aux, sblu_pix }
					<= { ublu_ctl, ublu_aux, ublu_pix };
		else
			{ sblu_ctl, sblu_aux, sblu_pix } <= lag_data_blu;

		if (lag_grn)
			{ sgrn_ctl, sgrn_aux, sgrn_pix }
					<= { ugrn_ctl, ugrn_aux, ugrn_pix };
		else
			{ sgrn_ctl, sgrn_aux, sgrn_pix } <= lag_data_grn;

		if (lag_red)
			{ sred_ctl, sred_aux, sred_pix }
					<= { ured_ctl, ured_aux, ured_pix };
		else
			{ sred_ctl, sred_aux, sred_pix } <= lag_data_red;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Data island start detection, post channel sync
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// data_control_blu, data_guard_blu => data_start_blu
	// {{{
	always @(*)
		data_control_blu = video_control_blu;

	// The blue (channel 0) data island guard bands is just a control
	// word (not guard, not video, not data, etc)
	initial	data_guard_blu = 0;
	always @(*)
		data_guard_blu = data_control_blu[1:0];

	initial	data_start_blu = 0;
	always @(posedge i_clk)
		data_start_blu <= { data_start_blu[1:0],
			(&data_control_blu[9:2])&&(&data_guard_blu) };
	// }}}

	// data_control_grn, data_guard_grn => data_start_grn
	// {{{
	always @(*)
		data_control_grn = video_control_grn;

	initial	data_guard_grn = 0;
	always @(posedge i_clk)
		data_guard_grn <= {data_guard_grn[0],
				ugrn_aux[6] && ugrn_aux[0] };

	initial	data_start_grn = 0;
	always @(posedge i_clk)
		data_start_grn <= { data_start_grn[1:0],
			(&data_control_grn[9:2])&&(&data_guard_grn) };
	// }}}

	// data_control_red, data_guard_red => data_start_red
	// {{{
	initial	data_control_red = 0;
	always @(posedge i_clk)
		data_control_red <= {data_control_red[8:0],
				ured_aux[4] && ured_ctl == 2'b10 };

	initial	data_guard_red = 0;
	always @(posedge i_clk)
		data_guard_red <= {data_guard_red[0],
				ured_aux[6] && !ured_aux[0] };

	initial	data_start_red = 0;
	always @(posedge i_clk)
		data_start_red <= { data_start_red[1:0],
			(&data_control_red[9:2])&&(&data_guard_red) };
	// }}}

	// data_start, data_guard, lag_[clr]
	// {{{
	initial	data_start = 1'b0;
	always @(posedge i_clk)
		data_start <=
			((lag_blu) ? data_guard_blu[1] : data_guard_blu[0]) &&
			((lag_grn) ? data_guard_grn[1] : data_guard_grn[0]) &&
			((lag_red) ? data_guard_red[1] : data_guard_red[0]);

	always @(*)
		data_guard = data_start;
	// }}}

	// }}}

	// non_video_data
	// {{{
	always @(posedge i_clk)
		non_video_data <= (sblu_aux[4])&&(sgrn_aux[4]) &&(sred_aux[4]);
	// }}}
	// control_sync_sreg
	// {{{
	always @(posedge i_clk)
	begin
		control_sync_sreg[10:1] <=  control_sync_sreg[ 9:0];
		control_sync_sreg[11]   <= (&control_sync_sreg[10:0]);
		control_sync_sreg[0]    <= sblu_aux[4] && sgrn_aux[4]
							&& sred_aux[4];
	end
	// }}}
	// control_sync
	// {{{
	always @(*)
		control_sync = control_sync_sreg[11] && control_sync_sreg[0];
	// }}}

	always @(posedge i_clk)
	begin
		blu_pixel <= sblu_pix;
		grn_pixel <= sgrn_pix;
		red_pixel <= sred_pix;
	end

	always @(posedge i_clk)
	begin
		// data_end <= data_period && data_guard;
		if (control_sync)
		begin
			// data_period <= 0;
			video_period <= 0;
		end else begin
			if (video_start)
				video_period <= 1;
			else if (non_video_data)
				video_period <= 0;
			/*
			if (data_start)
				data_period <= 1;
			else if (data_end)
				data_period <= 0;
			*/
		end

		// Outgoing pixels
		// {{{
		r_pix_valid <= (video_start)||(video_period && !non_video_data);

		r_vga_red   <= red_pixel;
		r_vga_green <= grn_pixel;
		r_vga_blue  <= blu_pixel;
		// }}}

		// Outgoing sync
		// {{{
		if (sblu_aux[5:4] == 2'b01)
		begin
			o_vsync <= sblu_ctl[1];
			o_hsync <= sblu_ctl[0];
		end
		// }}}
	end

	always @(*)
	begin
		o_pix_valid = r_pix_valid;

		o_vga_red   = r_vga_red;
		o_vga_green = r_vga_green;
		o_vga_blue  = r_vga_blue;
	end

	// Make verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, sblu_aux[3:0], sgrn_aux[3:0], sred_aux[3:0],
			sgrn_ctl, sred_ctl, sync_word, control_sync,
			non_video_data,
			data_start_red[2], data_start_grn[2], data_start_blu[2],
			data_control_red[1:0], data_control_grn[1:0], data_control_blu[1:0],
			sred_aux[6:5], sgrn_aux[6:5], sblu_aux[6:5],
			data_guard
			};
	// Verilator lint_on  UNUSED
	// }}}
endmodule
