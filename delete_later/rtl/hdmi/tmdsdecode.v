////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tmdsdecode.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Convert incoming TMDS data into usable pixel and packet data.
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
module	tmdsdecode(
		// {{{
		input	wire		i_clk,
		input	wire	[9:0]	i_word,
		output	wire	[1:0]	o_ctl,
		output	wire	[6:0]	o_aux,
		output	wire	[7:0]	o_pix
		// }}}
	);

	// Local declarations
	// {{{
	reg	[1:0]	r_ctl;
	reg	[6:0]	r_aux;
	reg	[7:0]	r_pix;
	wire	[9:0]	first_midp;
	wire	[9:0]	brev_word;
	// }}}

	// r_pix generation
	// {{{
	assign	first_midp = {
			((i_word[0]) ? (~i_word[9:2]) : (i_word[9:2])),
			i_word[1:0] };

	always @(posedge i_clk)
	if (first_midp[1])
	begin
		r_pix[0] <= (first_midp[9]);
		r_pix[1] <= (first_midp[8] ^ first_midp[9]);
		r_pix[2] <= (first_midp[7] ^ first_midp[8]);
		r_pix[3] <= (first_midp[6] ^ first_midp[7]);
		r_pix[4] <= (first_midp[5] ^ first_midp[6]);
		r_pix[5] <= (first_midp[4] ^ first_midp[5]);
		r_pix[6] <= (first_midp[3] ^ first_midp[4]);
		r_pix[7] <= (first_midp[2] ^ first_midp[3]);
	end else begin
		r_pix[0] <=  first_midp[9];
		r_pix[1] <= !(first_midp[8] ^ first_midp[9]);
		r_pix[2] <= !(first_midp[7] ^ first_midp[8]);
		r_pix[3] <= !(first_midp[6] ^ first_midp[7]);
		r_pix[4] <= !(first_midp[5] ^ first_midp[6]);
		r_pix[5] <= !(first_midp[4] ^ first_midp[5]);
		r_pix[6] <= !(first_midp[3] ^ first_midp[4]);
		r_pix[7] <= !(first_midp[2] ^ first_midp[3]);
	end
	// }}}

	// Bit-reverse i_word
	// {{{
	genvar	k;
	generate for(k=0; k<10; k=k+1)
		assign brev_word[k] = i_word[9-k];
	endgenerate
	// }}}

	// AUX and control channel decoding
	// {{{
	always @(posedge i_clk)
	begin
		r_aux <= 7'h0;
		r_ctl <= 2'b00;
		//
		case(brev_word)
		// 2-bit control period coding
		10'h354: begin r_aux <= 7'h10; r_ctl <= 2'h0; end
		10'h0ab: begin r_aux <= 7'h11; r_ctl <= 2'h1; end
		10'h154: begin r_aux <= 7'h12; r_ctl <= 2'h2; end
		10'h2ab: begin r_aux <= 7'h13; r_ctl <= 2'h3; end
		// TERC4 coding
		10'h29c: begin r_aux <= 7'h20; r_ctl <= 2'h0; end
		10'h263: begin r_aux <= 7'h21; r_ctl <= 2'h1; end
		10'h2e4: begin r_aux <= 7'h22; r_ctl <= 2'h2; end
		10'h2e2: begin r_aux <= 7'h23; r_ctl <= 2'h3; end
		10'h171: begin r_aux <= 7'h24; r_ctl <= 2'h0; end
		10'h11e: begin r_aux <= 7'h25; r_ctl <= 2'h1; end
		10'h18e: begin r_aux <= 7'h26; r_ctl <= 2'h2; end
		10'h13c: begin r_aux <= 7'h27; r_ctl <= 2'h3; end
		// This next pixel is also a guard pixel
		10'h2cc: begin r_aux <= 7'h68; r_ctl <= 2'h0; end
		//
		10'h139: begin r_aux <= 7'h29; r_ctl <= 2'h1; end
		10'h19c: begin r_aux <= 7'h2a; r_ctl <= 2'h2; end
		10'h2c6: begin r_aux <= 7'h2b; r_ctl <= 2'h3; end
		10'h28e: begin r_aux <= 7'h2c; r_ctl <= 2'h0; end
		10'h271: begin r_aux <= 7'h2d; r_ctl <= 2'h1; end
		10'h163: begin r_aux <= 7'h2e; r_ctl <= 2'h2; end
		10'h2c3: begin r_aux <= 7'h2f; r_ctl <= 2'h3; end
		// Guard band characters
		//10'h2cc:r_aux<= 8'h38; // done above
		10'h133: begin r_aux <= 7'h41; r_ctl <= 2'h0; end
		default: begin end
		endcase
	end
	// }}}

	assign	o_ctl  = r_ctl;
	assign	o_aux  = r_aux;
	assign	o_pix  = r_pix;

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = first_midp[0];
	// verilator lint_on  UNUSED
	// }}}
endmodule
