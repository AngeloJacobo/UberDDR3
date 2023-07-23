////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbgpio.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This extremely simple GPIO controller, although minimally
//		featured, is designed to control up to sixteen general purpose
//	input and sixteen general purpose output lines of a module from a
//	single address on a 32-bit wishbone bus.
//
//	Input GPIO values are contained in the top 16-bits.  Any change in
//	input values will generate an interrupt.
//
//	Output GPIO values are contained in the bottom 16-bits.  To change an
//	output GPIO value, writes to this port must also set a bit in the
//	upper sixteen bits.  Hence, to set GPIO output zero, one would write
//	a 0x010001 to the port, whereas a 0x010000 would clear the bit.  This
//	interface makes it possible to change only the bit of interest, without
//	needing to capture and maintain the prior bit values--something that
//	might be difficult from a interrupt context within a CPU.
//
//	Unlike other controllers, this controller offers no capability to
//	change input/output direction, or to implement pull-up or pull-down
//	resistors.  It simply changes and adjusts the values going out the
//	output pins, while allowing a user to read the values on the input
//	pins.
//
//	Any change of an input pin value will result in the generation of an
//	interrupt signal.
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
module wbgpio #(
		// {{{
		parameter		NIN=16, NOUT=16,
		parameter [(NOUT-1):0]	DEFAULT=0
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		//
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[31:0]		i_wb_data,
		input	wire	[32/8-1:0]	i_wb_sel,
		//
		output	wire		o_wb_stall,
		output	wire		o_wb_ack,
		output	wire	[31:0]	o_wb_data,
		//
		input	wire	[(NIN-1):0]	i_gpio,
		output	reg	[(NOUT-1):0]	o_gpio,
		//
		output	reg		o_int
		// }}}
	);

	// Local declarations
	// {{{
	reg	[(NIN-1):0]	r_gpio;
	(* ASYNC_REG *)	reg	[(NIN-1):0]	x_gpio, q_gpio;
	wire	[15:0]	hi_bits, low_bits;
	// }}}

	assign	o_wb_ack   = i_wb_stb;
	assign	o_wb_stall = 1'b0;

	// o_gpio
	// {{{
	// 9LUT's, 16 FF's
	initial	o_gpio = DEFAULT;
	always @(posedge i_clk)
	if (i_wb_stb && i_wb_we && (&i_wb_sel))
		o_gpio <= ((o_gpio)&(~i_wb_data[(NOUT+16-1):16]))
			|((i_wb_data[(NOUT-1):0])&(i_wb_data[(NOUT+16-1):16]));
	// }}}

	// 3 LUTs, 33 FF's
	// {{{
	always @(posedge i_clk)
	begin
		{ r_gpio, q_gpio, x_gpio } <= { q_gpio, x_gpio, i_gpio };
		o_int  <= (q_gpio != r_gpio);
	end
	// }}}

	// o_wb_data
	// {{{
	assign	hi_bits[ (NIN -1):0] = r_gpio;
	assign	low_bits[(NOUT-1):0] = o_gpio;

	generate
	if (NIN < 16)
	begin : GEN_HIBITS
		assign hi_bits[ 15: NIN] = 0;
	end
	if (NOUT < 16)
	begin : GEN_LOBITS
		assign low_bits[15:NOUT] = 0;
	end endgenerate

	assign	o_wb_data = { hi_bits, low_bits };
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data[31:0], i_wb_sel };
	// verilator lint_on  UNUSED
	// }}}
endmodule
