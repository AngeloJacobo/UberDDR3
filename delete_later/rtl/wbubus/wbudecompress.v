////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbudecompress.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Compression via this interface is simply a lookup table.
//		When writing, if requested, rather than writing a new 36-bit
//	word, we may be asked to repeat a word that's been written recently.
//	That's the goal of this routine: if given a word's (relative) address
//	in the write stream, we use that address, else we expect a full 32-bit
//	word to come in to be written.
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
module	wbudecompress (
		// {{{
		input	wire		i_clk, i_reset, i_stb,
		output	wire		o_busy,
		input	wire	[35:0]	i_word,
		output	reg		o_stb,
		input	wire		i_busy,
		output	reg	[35:0]	o_word,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	reg	[7:0]	wr_addr;
	reg	[31:0]	compression_tbl	[0:255];
	reg	[35:0]	r_word;
	reg	[7:0]	cmd_addr;
	reg	[24:0]	r_addr;
	wire	[31:0]	w_addr;
	reg	[9:0]	rd_len;
	reg	[31:0]	cword;
	reg	[2:0]	r_stb;
	wire		cmd_write_not_compressed;

	assign	o_busy = (o_stb && i_busy) || (|r_stb);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock zero
	//	{ o_stb, r_stb } = 0
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	cmd_write_not_compressed = (i_word[35:33] == 3'h3);


	// Clock one: { o_stb, r_stb } = 4'h1 when done

	// wr_addr
	// {{{
	initial	wr_addr = 8'h0;
	always @(posedge i_clk)
	if (i_reset)
		wr_addr <= 8'h0;
	else if ((i_stb && !o_busy)&&(cmd_write_not_compressed))
		wr_addr <= wr_addr + 8'h1;
	// }}}

	// Write to compression_tbl
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
		compression_tbl[wr_addr] <= { i_word[32:31], i_word[29:0] };
	// }}}

	// r_word
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
		r_word <= i_word;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock two, calculate the table address ... 1 is the smallest address
	//	{ o_stb, r_stb } = 4'h2 when done
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// cmd_addr
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
		cmd_addr <= wr_addr - { i_word[32:31], i_word[29:24] };
	// }}}

	// r_addr
	// {{{
	// Let's also calculate the address, in case this is a compressed
	// address word
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	case(i_word[32:30])
	3'b000: r_addr <= { 19'h0, i_word[29:24] };
	3'b010: r_addr <= { 13'h0, i_word[29:18] };
	3'b100: r_addr <= {  7'h0, i_word[29:12] };
	3'b110: r_addr <= {  1'h0, i_word[29: 6] };
	3'b001: r_addr <= { {(19){ i_word[29]}}, i_word[29:24] };
	3'b011: r_addr <= { {(13){ i_word[29]}}, i_word[29:18] };
	3'b101: r_addr <= { {( 7){ i_word[29]}}, i_word[29:12] };
	3'b111: r_addr <= { {( 1){ i_word[29]}}, i_word[29: 6] };
	endcase

	assign	w_addr = { {(7){r_addr[24]}}, r_addr };
	// }}}

	// rd_len
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	begin
		if (!i_word[34])
			rd_len <= 10'h01 + { 6'h00, i_word[33:31] };
		else
			rd_len <= 10'h09 + { 1'b0,i_word[33:31],i_word[29:24] };
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock three, read the table value
	//	{ o_stb, r_stb } = 4'h4 when done
	// Maintaining ...
	//	r_word (clock 1)
	//	r_addr, rd_len (clock 2)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
		cword <= compression_tbl[cmd_addr];

	// r_stb
	// {{{
	// Pipeline the strobe signal to create an output strobe, 3 clocks later
	initial	r_stb = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_stb <= 0;
	else
		r_stb <= { r_stb[1:0], i_stb && !o_busy };
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock four, now that the table value is valid, let's set our output
	// word.
	//	{ o_stb, r_stb } = 4'h8 when done
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_stb
	// {{{
	initial	o_stb = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 0;
	else if (!o_stb || !i_busy)
		o_stb <= r_stb[2];
	// }}}

	// o_word
	// {{{
	// Maintaining ...
	//	r_word		(clock 1)
	//	r_addr, rd_len	(clock 2)
	//	cword		(clock 3)
	//		Any/all of these can be pipelined for faster operation
	// However, speed is really limited by the speed of the I/O port.  At
	// it's fastest, it's 1 bit per clock, 48 clocks per codeword therefore,
	// thus ... things will hold still for much longer than just 5 clocks.
	always @(posedge i_clk)
	if (!o_stb || !i_busy)
	begin
		if (r_word[35:30] == 6'b101110)
			o_word <= r_word;
		else casez(r_word[35:30])
		// Set address from something compressed ... unsigned
		6'b001??0: o_word <= { 4'h0, w_addr[31:0] };
		// Set a new address as a signed offset from the last (set) one
		//	(The last address is kept further down the chain,
		//	we just mark here that the address is to be set
		//	relative to it, and by how much.)
		6'b001??1: o_word <= { 3'h1, w_addr[31:30], 1'b1, w_addr[29:0]};
		// Write a value to the bus, with the value given from our
		// codeword table
		6'b010???: o_word <=
			{ 3'h3, cword[31:30], r_word[30], cword[29:0] };
		// Read, highly compressed length (1 word)
		6'b1?????: o_word <= { 5'b11000, r_word[30], 20'h00, rd_len };
		// Read, two word (3+9 bits) length ... same encoding
		// 6'b1?????: o_word <= { 5'b11000, r_word[30], 20'h00, rd_len };
		default: o_word <= r_word;
		endcase
	end
	// }}}

	assign	o_active = o_stb || (|r_stb);
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

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	// always @(*)
	// if (!f_past_valid)
	//	assume(i_reset);

	always @(*)
	if (|r_stb)
		assert(!o_stb);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_stb);
	else if ($past(i_stb && o_busy))
	begin
		assume(i_stb);
		assume($stable(i_word));
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_stb);
	else if ($past(o_stb && i_busy))
	begin
		assert(o_stb);
		assert($stable(o_word));
	end

`ifdef	VERIFIC
	assert property	(@(posedge i_clk)
		disable iff (i_reset)
		i_stb && !o_busy |=> r_stb[0] ##1 r_stb[1] ##1 r_stb[2] ##1 o_stb);

	//
	// Without changing things, I would note that any time o_stb is valid,
	// the codeword has been known for a full clock.  Hence, we could
	// trim a clock off of the whole calculation.
	assert property	(@(posedge i_clk)
		disable iff (i_reset)
		o_stb |-> $stable(o_word));

	// Uncompressed
	assert property	(@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b101110)
		|=> (!o_stb) [*3]
		##1 (o_stb) && $stable(o_word) && o_word == $past(i_word, 4));

	// Address (compressed)
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001000)
		|=> ##3 (o_stb)&&(o_word == { 4'h0, 26'h0, $past(i_word[29:24], 4)}));

	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001010)
		|=> ##3 (o_stb)&&(o_word == { 4'h0, 20'h0, $past(i_word[29:18], 4)}));

	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001100)
		|=> ##3 (o_stb)&&(o_word == { 4'h0, 12'h0, $past(i_word[29:12], 4)}));

	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001110)
		|=> ##3 (o_stb)&&(o_word == { 4'h0, 6'h0, $past(i_word[29:6], 4)}));

	// Address (compressed, offset)
	// initial $warn("Addresses not checked\n")
	// 6'b001??1: o_word <= { 3'h1, w_addr[31:30], 1'b1, w_addr[29:0]};
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001001)
		|=> ##3 (o_stb)&&(o_word == { 3'h1,
			$past({
				{(2){i_word[29]}}, 1'b1,
				{(24){i_word[29]}}, i_word[29:24]}, 4)}));

	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001011)
		|=> ##3 (o_stb)&&(o_word == { 3'h1,
			$past({
				{(2){i_word[29]}}, 1'b1,
				{(18){i_word[29]}}, i_word[29:18]}, 4)}));

	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001101)
		|=> ##3 (o_stb)&&(o_word == { 3'h1,
			$past({
				{(2){i_word[29]}}, 1'b1,
				{(12){i_word[29]}}, i_word[29:12]}, 4)}));

	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:30] == 6'b001111)
		|=> ##3 (o_stb)&&(o_word == { 3'h1,
			$past({
				{(2){i_word[29]}}, 1'b1,
				{(6){i_word[29]}}, i_word[29:6]}, 4)}));


	// Write from codeword table
	assert property	(@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:33] == 3'b010)
		|=> ##3
		(cword == compression_tbl[cmd_addr])
		&& (o_word == { 3'h3, cword[31:30], r_word[30], cword[29:0] }));

	assert property	(@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:33] == 3'b010)
		|=> !o_stb
		##1 !o_stb && (cmd_addr == (wr_addr - $past({i_word[32:31], i_word[29:24]},2)))
		##1 (!o_stb) && (cmd_addr == (wr_addr - $past({i_word[32:31], i_word[29:24]}, 3)))
			&& $stable(wr_addr));

	//
	// 1-word compressed reads
	//
	// Read, highly compressed length (1 word)
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && (i_word[35:34] == 2'b10) && (i_word[35:30] != 6'h2e))
		|=> ##3 (o_word[35:31] == 5'b11000)
			&&(o_word[30] == $past(i_word[30],4))
			&&(o_word[29:0] == $past(i_word[33:31],4)+1));

	//
	// 2-word compressed reads
	//
	// Read, highly compressed length (1 word)
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_stb && !o_busy && i_word[35:34] == 2'b11)
		|=> ##3 (o_word[35:31] == 5'b11000)
			&&(o_word[30] == $past(i_word[30],4))
			&&(o_word[29:0] == $past({i_word[33:31], i_word[29:24]},4)+9));
`else
	initial begin
		// This design *requires* verific to verify
		$stop();
	end

`endif
`endif
// }}}
endmodule

