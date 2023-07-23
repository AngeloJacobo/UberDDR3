////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdtxframe.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Given a frame of data from memory, formats it for sending to
//		the front end.
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
module	sdtxframe #(
		parameter		NCRC = 16,
		parameter [0:0]		OPT_SERDES = 1'b1,
		parameter [NCRC-1:0]	CRC_POLYNOMIAL  = 16'h1021
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire	[7:0]		i_cfg_spd,
		input	wire	[1:0]		i_cfg_width,
		input	wire			i_cfg_ddr,
		//
		input	wire			i_en, i_ckstb, i_hlfck,
		//
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[31:0]		S_DATA,
		input	wire			S_LAST,
		//
		output	wire			tx_valid,
		// input wire			tx_ready,
		output	wire	[31:0]		tx_data
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[1:0]	P_IDLE = 2'b00,
				P_DATA = 2'b01,
				P_CRC  = 2'b10,
				P_LAST = 2'b11;

	localparam [1:0]	WIDTH_1W = 2'b00,
				WIDTH_4W = 2'b01,
				WIDTH_8W = 2'b10;

	localparam [1:0]	P_1D = 2'b00,
				P_2D = 2'b01,
				P_4D = 2'b10;

	reg		cfg_ddr;
	reg	[1:0]	cfg_width, cfg_period;


	wire		start_packet;
	reg		pre_valid;
	reg	[1:0]	pstate;
	wire		pre_ready;
	reg	[31:0]	pre_data;
	reg	[3:0]	pre_count;


	integer		ik, jk;
	reg	[NCRC- 1:0]	crc_1w_reg;
	reg	[NCRC* 2-1:0]	di_crc_2w, nxt_crc_2w, new_crc_2w, crc_2w_reg;
	reg	[NCRC* 4-1:0]	di_crc_4w, nxt_crc_4w, new_crc_4w, crc_4w_reg;
	reg	[NCRC* 8-1:0]	di_crc_8w, nxt_crc_8w, new_crc_8w, crc_8w_reg;
	reg	[NCRC*16-1:0]	di_crc_8d, nxt_crc_8d, new_crc_8d, crc_8d_reg;

	reg		ck_valid;
	reg	[4:0]	ck_counts;
	reg	[31:0]	ck_data, ck_sreg;
	// }}}
	// Steps: #1, Packetizer: breaks incoming signal into wires
	// 	#2, add CRC
	//	#3, split across clocks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Configuration
	// {{{
	initial	cfg_period = 2'b00;
	always @(posedge i_clk)
	if (i_reset || !OPT_SERDES)
		cfg_period <= P_1D;
	else if (pstate == P_IDLE)
	begin
		if (i_cfg_ddr && i_cfg_spd == 0)
			cfg_period <= P_4D;	// Four data periods / clk
		else if ((i_cfg_ddr && i_cfg_spd == 1)
			||(!i_cfg_ddr && i_cfg_spd == 0))
			cfg_period <= P_2D;	// Two data periods / clk
		else
			cfg_period <= P_1D;	// One data period / clk
	end

	always @(posedge i_clk)
	if (i_reset)
		cfg_width <= WIDTH_1W;
	else if (pstate == P_IDLE)
		cfg_width <= i_cfg_width;

	always @(posedge i_clk)
	if (i_reset)
		cfg_ddr <= 1'b0;
	else if (pstate == P_IDLE)
		cfg_ddr <= i_cfg_ddr;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packetizer: Add CRC(s) to the packet
	// {{{

	assign	start_packet = i_en && S_VALID && i_ckstb && !tx_valid && !ck_valid;
	initial	pstate    = P_IDLE;
	initial	pre_valid = 1'b0;
	initial	pre_data  = {(32){1'b1}};
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		pstate    <= P_IDLE;
		pre_valid <= 1'b0;
		pre_data  <= {(32){1'b1}};
		// }}}
	end else case(pstate)
	P_IDLE: begin
		// {{{
		pstate <= P_IDLE;
		pre_valid <= 0;
		pre_data <= (S_VALID) ? S_DATA : {(32){1'b1}};
		if (start_packet)
		begin
			pstate    <= (S_LAST) ? P_CRC : P_DATA;
			pre_valid <= 1;
		end end
		// }}}
	P_DATA: if (S_VALID && S_READY)
		// {{{
		begin
			pstate <= P_DATA;
			pre_valid <= 1;
			pre_data <= S_DATA;

			if (S_LAST)
				pstate <= P_CRC;
		end
		// }}}
	P_CRC: if (pre_ready)
		// {{{
		begin
			pre_valid <= 1'b1;
			if (pre_count == 0)
				pstate <= P_LAST;

			case(cfg_width)
			WIDTH_1W: if (cfg_ddr)
					pre_data <= crc_2w_reg[NCRC*2-1:0];
				else
				pre_data <= { crc_1w_reg[NCRC-1:0], 16'hffff };
			WIDTH_4W: if (cfg_ddr)
				pre_data <= crc_8w_reg[8*NCRC-1:8*NCRC-32];
				else
				pre_data <= crc_4w_reg[4*NCRC-1:4*NCRC-32];
			WIDTH_8W: if (cfg_ddr)
				pre_data <= crc_8d_reg[16*NCRC-1:16*NCRC-32];
				else
				pre_data <= crc_8w_reg[8*NCRC-1:8*NCRC-32];
			default: pre_data  <= crc_8w_reg[8*NCRC-1:8*NCRC-32];
			endcase
		end
		// }}}
	P_LAST: begin
		if (pre_ready)
		begin
			pre_valid <= 0;
			pre_data <= {(32){1'b1}};
		end

		if (!tx_valid)
			pstate <= P_IDLE;
		end
	endcase

	initial	pre_count = 0;
	always @(posedge i_clk)
	if (i_reset)
		pre_count <= 0;
	else if (pstate == P_DATA || pstate == P_IDLE)
	begin
		// pre_count = 
		//	(SDR)	16bits / wire / 32
		//	(DDR)	32bits / wire / 32
		case(cfg_width)
		WIDTH_1W: pre_count <= 0;
		WIDTH_4W: pre_count <= (cfg_ddr) ? 3 : 1;
		default: // WIDTH_8W
			pre_count <= (cfg_ddr) ? 7:3;
		endcase
	end else if (pre_ready && pre_count != 0)
		pre_count <= pre_count - 1;

	assign	S_READY = pre_ready && (pstate == P_DATA || pstate == P_IDLE);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CRC calculation
	// {{{

	// di_crc*, new_crc*, next_crc*: Advance CRC calculations combinatorialy
	// {{{
	always @(*)
	begin
		// Notes:
		// {{{
		// Why the following monstrosity?  So we can read data out
		// directly into the shift register(s).  However, the shift
		// register(s) are not sorted by rail, hence all the work
		// below to first sort them by rail, adjust the CRC, then
		// sort them back, etc.
		//
		// The good news is that, inspite of all the tortured pain
		// below, it's primarily just wire assignments and
		// rearrangements.  The logic itself is either a shift, or
		// (for 1-4 bits per CRC per step), a XOR reduction of up
		// to 20 incoming bits.
		// }}}

		// Pre-load the CRC fills
		// {{{
		for(ik=0; ik<NCRC; ik=ik+1)
		begin
			for(jk=0; jk<2; jk=jk+1)
				di_crc_2w[jk*NCRC+ik] = crc_2w_reg[ik*2+jk];

			for(jk=0; jk<4; jk=jk+1)
				di_crc_4w[jk*NCRC+ik] = crc_4w_reg[ik*4+jk];

			for(jk=0; jk<8; jk=jk+1)
				di_crc_8w[jk*NCRC+ik] = crc_8w_reg[ik*8+jk];

			for(jk=0; jk<16; jk=jk+1)
				di_crc_8d[jk*NCRC+ik] = crc_8d_reg[ik*16+jk];
		end
		// }}}

		// Advance the CRCs based on S_DATA
		// {{{
		for(ik=0; ik<2; ik=ik+1)
		begin
			new_crc_2w[ik*NCRC +: NCRC] = 
				APPLYCRC16(di_crc_2w[ik*NCRC +: NCRC],
			  		{ S_DATA[30+ik],S_DATA[28+ik],
						S_DATA[26+ik],S_DATA[24+ik],
						S_DATA[22+ik],S_DATA[20+ik],
						S_DATA[18+ik],S_DATA[16+ik],
						S_DATA[14+ik],S_DATA[12+ik],
						S_DATA[10+ik],S_DATA[ 8+ik],
						S_DATA[ 6+ik],S_DATA[ 4+ik],
						S_DATA[ 2+ik],S_DATA[   ik] });
		end

		for(ik=0; ik<4; ik=ik+1)
		begin
			new_crc_4w[ik*NCRC +: NCRC] = 
				APPLYCRC8(di_crc_4w[ik*NCRC +: NCRC],
			  		{ S_DATA[28+ik],S_DATA[24+ik],
						S_DATA[20+ik],S_DATA[16+ik],
						S_DATA[12+ik],S_DATA[ 8+ik],
						S_DATA[ 4+ik],S_DATA[   ik] });
		end

		for(ik=0; ik<8; ik=ik+1)
		begin
			new_crc_8w[ik*NCRC +: NCRC] = 
				APPLYCRC4(di_crc_8w[ik*NCRC +: NCRC],
			  		{ S_DATA[24+ik], S_DATA[16+ik],
						S_DATA[8+ik], S_DATA[ik] });
		end

		for(ik=0; ik<16; ik=ik+1)
		begin
			new_crc_8d[ik*NCRC +: NCRC] = 
				APPLYCRC2(di_crc_8d[ik*NCRC +: NCRC],
			  		{ S_DATA[16+ik], S_DATA[ik] });
		end
		// }}}

		// Order the bits to place the results back in line
		// {{{
		for(ik=0; ik<NCRC; ik=ik+1)
		begin
			for(jk=0; jk<2; jk=jk+1)
				nxt_crc_2w[ik*2+jk] = new_crc_2w[jk*NCRC+ik];
			for(jk=0; jk<4; jk=jk+1)
				nxt_crc_4w[ik*4+jk] = new_crc_4w[jk*NCRC+ik];
			for(jk=0; jk<8; jk=jk+1)
				nxt_crc_8w[ik*8+jk] = new_crc_8w[jk*NCRC+ik];
			for(jk=0; jk<16; jk=jk+1)
				nxt_crc_8d[ik*16+jk] = new_crc_8d[jk*NCRC+ik];
		end
		// }}}
	end
	// }}}

	// crc_*_reg: Advance CRC calculations sequentially w/ new data
	// {{{
	always @(posedge i_clk)
	if (i_reset || (!i_en && !tx_valid))
	begin
		crc_1w_reg <= 0;
		crc_2w_reg <= 0;
		crc_4w_reg <= 0;
		crc_8w_reg <= 0;
		crc_8d_reg <= 0;
	end else if (S_VALID && S_READY)
	begin
		crc_1w_reg <= {(NCRC   ){1'b1}};
		crc_2w_reg <= {(NCRC* 2){1'b1}};
		crc_4w_reg <= {(NCRC* 4){1'b1}};
		crc_8w_reg <= {(NCRC* 8){1'b1}};
		crc_8d_reg <= {(NCRC*16){1'b1}};

		case(cfg_width)
		WIDTH_1W: if (cfg_ddr)
				crc_2w_reg <= nxt_crc_2w;
			else
				crc_1w_reg <= APPLYCRC32(crc_1w_reg, S_DATA);
		WIDTH_4W: if (cfg_ddr)
				crc_8w_reg <= nxt_crc_8w;
			else
				crc_4w_reg <= nxt_crc_4w;
		WIDTH_8W: if (cfg_ddr)
				crc_8d_reg <= nxt_crc_8d;
			else
				crc_8w_reg <= nxt_crc_8w;
		default: begin end
		endcase
	end else if (i_ckstb && pstate != P_IDLE && pstate != P_DATA && ck_counts == 0)
	begin
		crc_1w_reg <= {(NCRC){1'b1}};
		crc_2w_reg <= {(2*NCRC){1'b1}};
		crc_4w_reg <= { crc_4w_reg[ 4*NCRC-32-1:0], 32'hffff_ffff };
		crc_8w_reg <= { crc_8w_reg[ 8*NCRC-32-1:0], 32'hffff_ffff };
		crc_8d_reg <= { crc_8d_reg[16*NCRC-32-1:0], 32'hffff_ffff };
	end
	// }}}

	function automatic [NCRC-1:0] STEPCRC(reg [NCRC-1:0] prior,
		// {{{
				input i_bit);
	begin
		if (prior[NCRC-1] ^ i_bit)
			STEPCRC = { prior[NCRC-2:0], 1'b0 } ^ CRC_POLYNOMIAL;
		else
			STEPCRC = { prior[NCRC-2:0], 1'b0 };
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC32(reg [NCRC-1:0] prior,
		// {{{
			input [31:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<32; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[31-ck]);

		APPLYCRC32 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC16(input [NCRC-1:0] prior,
		// {{{
			input [15:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<16; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[15-ck]);
		APPLYCRC16 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC8(reg [NCRC-1:0] prior,
		// {{{
			input [7:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<8; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[7-ck]);
		APPLYCRC8 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC4(reg [NCRC-1:0] prior,
		// {{{
			input [3:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<4; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[3-ck]);
		APPLYCRC4 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC2(reg [NCRC-1:0] prior,
		// {{{
			input [1:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<2; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[1-ck]);
		APPLYCRC2 = fill;
	end endfunction
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock divider, data shift register
	// {{{

	reg	ck_stop_bit;

	// ck_valid
	// {{{
	initial	ck_valid = 0;
	initial	ck_stop_bit = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ck_valid <= 0;
		ck_stop_bit <= 1'b0;
	end else if (start_packet)
	begin
		// Start us one clock cycle early with a single start bit
		ck_valid <= 1;
		ck_stop_bit <= 1'b1;	// Need a stop bit
	end else if (i_ckstb && ck_counts == 0)
	begin
		ck_valid    <= pre_valid || ck_stop_bit;
		ck_stop_bit <= pre_valid;
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset && (ck_stop_bit || pre_valid))
		assert(ck_valid);
`endif
	// }}}

	initial	ck_counts = 0;
	initial	ck_sreg = -1;
	initial	ck_data = -1;
	always @(posedge i_clk)
	if (i_reset) // pstate == P_IDLE)
	begin
		// {{{
		ck_sreg  <= {(32){1'b1}};
		ck_data  <= {(32){1'b1}};
		ck_counts<= 0;
		// }}}
	end else if (i_ckstb && pre_valid && ck_counts == 0) // && tx_ready
	begin // Load the shift registers
		case(cfg_period)
		P_1D: begin // One clock period of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { pre_data[30: 0], 1'b1 };
				ck_data <= { (4){7'h7f, pre_data[31] } };
				// In the case of the 1b CRC, we only need
				// 16 clock cycles, not 32.
				ck_counts <= (!cfg_ddr && pstate == P_LAST) ? 15: 31;
				end
			WIDTH_4W: begin
				ck_sreg <= { pre_data[27: 0], 4'hf };
				ck_data <= { (4){ 4'hf, pre_data[31:28] } };
				ck_counts <= 7;
				end
			default: begin // WIDTH_8W
				ck_sreg <= { pre_data[23: 0], 8'hff };
				ck_data <= { (4){pre_data[31:24] } };
				ck_counts <= 3;
				end
			endcase end
			// }}}
		P_2D: begin // Two clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { pre_data[29: 0], 2'b11 };
				ck_data <= { {(2){7'h7f, pre_data[31] }},
						{(2){7'h7f, pre_data[30] }} };
				ck_counts <= 15;
				end
			WIDTH_4W: begin
				ck_sreg <= { pre_data[23: 0], 8'hff };
				ck_data <= { {(2){4'hf, pre_data[31:28] }},
						{(2){4'hf, pre_data[27:24] }} };
				ck_counts <= 3;
				end
			default: begin // WIDTH_8W
				ck_sreg <= { pre_data[15: 0], 16'hffff };
				ck_data <= { {(2){pre_data[31:24] }},
						{(2){pre_data[23:16]}} };
				ck_counts <= 1;
				end
			endcase end
			// }}}
		default: begin // Four clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { pre_data[27: 0], 4'hf };
				ck_data <= { 7'h7f, pre_data[31],
						7'h7f, pre_data[30],
						7'h7f, pre_data[29],
						7'h7f, pre_data[28] };
				ck_counts <= 7;
				end
			WIDTH_4W: begin
				ck_sreg <= { pre_data[15: 0], 16'hffff };
				ck_data <= { 4'hf, pre_data[31:28],
					4'hf, pre_data[27:24],
					4'hf, pre_data[23:20],
					4'hf, pre_data[19:16] };
				ck_counts <= 1;
				end
			default: begin // WIDTH_8W
				ck_sreg <= {(32){1'b1}};
				ck_data <= pre_data;
				ck_counts <= 0;
				end
			endcase end
			// }}}
		endcase
	end else if ((i_ckstb || (i_hlfck && cfg_ddr)) && ck_counts > 0)
	begin // Drain the shift registers
		ck_counts <= ck_counts - 1;
		case(cfg_period)
		P_1D: begin // One clock period of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { ck_sreg[30: 0], 1'b1 };
				ck_data <= { (4){7'h7f, ck_sreg[31] }};
				end
			WIDTH_4W: begin
				ck_sreg <= { ck_sreg[27: 0], 4'hf };
				ck_data <= { (4){4'hf, ck_sreg[31:28] } };
				end
			default: begin // WIDTH_8W
				ck_sreg <= { ck_sreg[23: 0], 8'hff };
				ck_data <= { (4){ck_sreg[31:24] } };
				end
			endcase end
			// }}}
		P_2D: begin // Two clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { ck_sreg[29: 0], 2'b11 };
				ck_data <= { {(2){7'h7f, ck_sreg[31] }},
						{(2){7'h7f, ck_sreg[30] }} };
				end
			WIDTH_4W: begin
				ck_sreg <= { ck_sreg[23: 0], 8'hff };
				ck_data <= { {(2){4'hf, ck_sreg[31:28] }},
						{(2){4'hf, ck_sreg[27:24] }} };
				end
			default: begin // WIDTH_8W
				ck_sreg <= { ck_sreg[15: 0], 16'hffff };
				ck_data <= { {(2){ck_sreg[31:24] }},
						{(2){ck_sreg[23:16]}} };
				end
			endcase end
			// }}}
		default: begin // Four clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { ck_sreg[27: 0], 4'hf };
				ck_data <= { 7'h7f, ck_sreg[31],
						7'h7f, ck_sreg[30],
						7'h7f, ck_sreg[29],
						7'h7f, ck_sreg[28] };
				end
			WIDTH_4W: begin
				ck_sreg <= { ck_sreg[15: 0], 16'hffff };
				ck_data <= { 4'hf, ck_sreg[31:28],
					4'hf, ck_sreg[27:24],
					4'hf, ck_sreg[23:20],
					4'hf, ck_sreg[19:16] };
				end
			default: begin // WIDTH_8W
				ck_sreg <= {(32){1'b1}};
				ck_data <= ck_sreg;
				end
			endcase end
			// }}}
		endcase
	end else if (i_ckstb && ck_counts == 0)
	begin
		// Fully idle
		ck_data  <= -1;
		ck_sreg  <= -1;

		ck_counts <= (start_packet && i_cfg_ddr && !i_hlfck) ? 1:0;

		if (start_packet)	// Implies i_ckstb
		case(cfg_period)
		2'b00: begin // One data period / clock
			case(cfg_width)
			WIDTH_1W: ck_data  <= {(4){ 8'hfe }};
			WIDTH_4W: ck_data  <= {(4){ 8'hf0 }};
			default:  ck_data  <= {(4){ 8'h00 }};
			endcase end
		2'b01: begin // Two data periods / clock
			// {{{
			if (cfg_ddr)
			begin
				// One pedge, one negedge
				case(cfg_width)
				WIDTH_1W: ck_data  <= {(4){ 8'hfe }};
				WIDTH_4W: ck_data  <= {(4){ 8'hf0 }};
				default:  ck_data  <= {(4){ 8'h00 }};
				endcase
			end else begin
				// Two posedges, so only the second gets the
				// start bits
				case(cfg_width)
				WIDTH_1W: ck_data  <= { {(2){8'hff}}, {(2){8'hfe}} };
				WIDTH_4W: ck_data  <= { {(2){8'hff}}, {(2){8'hf0}} };
				default:  ck_data  <= { {(2){8'hff}}, {(2){8'h00}} };
				endcase
			end end
			// }}}
		default: begin // 4 data periods / clock, DDR
			// pedge, nedge, pedge, nedge, so the last two
			// get the start bit
			case(cfg_width)
			WIDTH_1W: ck_data  <= { {(2){8'hff}}, {(2){8'hfe}} };
			WIDTH_4W: ck_data  <= { {(2){8'hff}}, {(2){8'hf0}} };
			default:  ck_data  <= { {(2){8'hff}}, {(2){8'h00}} };
			endcase end
		endcase
	end

	assign	pre_ready = (ck_counts == 0) && i_ckstb; // && tx_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Final outputs
	// {{{
	assign	tx_valid = ck_valid;
	// assign ck_ready = (i_ckstb || (i_hlfck && cfg_ddr)); // && tx_ready;
	assign	tx_data  = ck_data;
	// }}}

	//
	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	// wire	unused;
	// assign	unused = i_wb_cyc;
	// verilator lint_on  UNUSED
	// verilator coverage_on
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
	reg	f_ckstb, f_hlfck;
	(* keep *)	reg	[9+5:0]	fb_count, fd_offset, fd_count,
					f_loaded_count;
	(* keep *)	reg	[9:0]	fs_count;
			reg	[10:0]	fcrc_count;
	(* keep *)	reg		fs_last;
	wire		f_step, fload_xtra;

	assign	f_step = f_ckstb || (cfg_ddr && f_hlfck);
	assign	fload_xtra = tx_valid && f_step; // || fb_count == fd_offset);

	always @(*)
	begin
		if (fb_count < fd_offset)
			f_loaded_count = 0;
		else if (!tx_valid)
			f_loaded_count = fb_count - fd_offset;
		else case(cfg_period)
		P_1D: case(cfg_width)
			// {{{
			WIDTH_1W: f_loaded_count = fd_count + ck_counts + (fload_xtra ? 1:0);
			WIDTH_4W: f_loaded_count = fd_count + (ck_counts*4) + (fload_xtra ? 4:0);
			WIDTH_8W: f_loaded_count = fd_count + (ck_counts*8) + (fload_xtra ? 8:0);
			endcase
			// }}}
		P_2D: case(cfg_width)
			// {{{
			WIDTH_1W: f_loaded_count = fd_count + ck_counts*2 + (fload_xtra ? 2:0);
			WIDTH_4W: f_loaded_count = fd_count + ck_counts*8 + (fload_xtra ? 8:0);
			WIDTH_8W: f_loaded_count = fd_count + ck_counts*16 + (fload_xtra ? 16:0);
			endcase
			// }}}
		P_4D: case(cfg_width)
			// {{{
			WIDTH_1W: f_loaded_count = fd_count + ck_counts*4 + (fload_xtra ? 4:0);
			WIDTH_4W: f_loaded_count = fd_count + ck_counts*16 + (fload_xtra ? 16:0);
			WIDTH_8W: f_loaded_count = fd_count + ck_counts*32 + (fload_xtra ? 32:0);
			endcase
			// }}}
		endcase
	end

	always @(posedge i_clk)
	if (i_reset)
		{ f_ckstb, f_hlfck } <= 2'b00;
	else
		{ f_ckstb, f_hlfck } <= { i_ckstb, i_hlfck };

	// fb_count -- count bits sent, including starting word
	// {{{
	always @(posedge i_clk)
	if (i_reset || !tx_valid)
		fb_count <= 0;
	else if (f_ckstb || (cfg_ddr && f_hlfck)) case(cfg_width)
	WIDTH_1W: begin
		case(cfg_period)
		P_1D: fb_count <= fb_count + 1;
		P_2D: fb_count <= fb_count + 2;
		default: fb_count <= fb_count + 4;
		endcase end
	WIDTH_4W: begin
		case(cfg_period)
		P_1D: fb_count <= fb_count + 4;
		P_2D: fb_count <= fb_count + 8;
		default: fb_count <= fb_count + 16;
		endcase end
	default: begin
		case(cfg_period)
		P_1D: fb_count <= fb_count + 8;
		P_2D: fb_count <= fb_count + 16;
		default: fb_count <= fb_count + 32;
		endcase end
	endcase
	// }}}

	initial	fs_last = 0;
	always @(posedge i_clk)
	if (i_reset || !i_en || (pstate == P_LAST && !tx_valid))
	begin
		fs_count <= 0;
		fs_last  <= 0;
		fcrc_count <= 0;
	end else if (S_VALID && S_READY)
	begin
		fs_count <= fs_count + 1;
		fcrc_count <= fs_count + 1;
		fs_last  <= S_LAST;
	end else if (pre_valid && pre_ready)
		fcrc_count <= fcrc_count + 1;

	// fd_offset, fd_count: bit count, not including the starting word
	// {{{
	always @(*)
	begin
		fd_offset = 1;
		case(cfg_width)
		WIDTH_1W: begin
			case(cfg_period)
			P_1D: fd_offset = (cfg_ddr ? 2:1);
			P_2D: fd_offset = 2;
			default: fd_offset = 4;
			endcase end
		WIDTH_4W: begin
			case(cfg_period)
			P_1D: fd_offset = (cfg_ddr ?  8: 4);
			P_2D: fd_offset = 8;
			default: fd_offset = 16;
			endcase end
		default: begin
			case(cfg_period)
			P_1D: fd_offset = (cfg_ddr ? 16: 8);
			P_2D: fd_offset = 16;
			default: fd_offset= 32;
			endcase end
		endcase
	end

	always @(*)
	if (fb_count > fd_offset)
		fd_count = fb_count - fd_offset;
	else
		fd_count = 0;
	// }}}

	reg	f_past_valid, f_pending_half;
	(* anyconst *)	reg	[9:0]	fc_posn;
	(* anyconst *)	reg	[31:0]	fc_data;
	wire	[9:0]	fp_count;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Configuraion interface
	// {{{

	always @(*)
	if (!OPT_SERDES)
	begin
		assume(!i_cfg_ddr || i_cfg_spd > 1);
		assume(i_cfg_spd > 0);
	end

	always @(*)
	if (!i_reset)
		assume(i_cfg_width != 2'b11);

	////////

	always @(*)
	if (!i_reset)
		assert(cfg_period <= P_4D);

	always @(posedge i_clk)
	if (!i_reset && $past(tx_valid))
		assume(i_en);

	always @(posedge i_clk)
	if (!i_reset && (i_en || $past(i_en)))
	begin
		assume($stable(i_cfg_ddr));
		assume($stable(i_cfg_spd));
		assume($stable(i_cfg_width));
	end

	always @(posedge i_clk)
	if (!i_reset && i_en)
	begin
		assert(i_cfg_ddr   == cfg_ddr);
		assert(i_cfg_width == cfg_width);
	end

	always @(*)
	if (!i_reset)
		assert(cfg_width != 2'b11);


	always @(*)
	if (!i_reset && pstate != P_IDLE)
	begin
		if (cfg_period == P_4D)
			assert(cfg_ddr);
	end

	always @(posedge i_clk)
	if (!i_reset && i_en)
	begin
		if (i_cfg_ddr && i_cfg_spd == 0)
		begin
			assert(cfg_period == 2'b10);
		end else if ((i_cfg_ddr && i_cfg_spd == 1)
			||(!i_cfg_ddr && i_cfg_spd == 0))
		begin
			assert(cfg_period == 2'b01);
		end else begin
			assert(cfg_period == 2'b00);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock interface
	// {{{

	always @(*)
	if (!OPT_SERDES)
		assume(!i_ckstb || !i_hlfck);

	initial	f_pending_half = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		f_pending_half <= 1'b0;
	else if (i_ckstb)
		f_pending_half <= !i_hlfck;
	else if (i_hlfck)
		f_pending_half <= 1'b0;

	always @(*)
	if (i_en) case(i_cfg_spd)
	0: assume(i_ckstb && i_hlfck);
	1: assume(i_ckstb && i_hlfck);
	2: assume(i_ckstb ^ i_hlfck);
	default: assume(!i_ckstb || !i_hlfck);
	endcase

	always @(*)
	if (i_en && i_cfg_spd == 2)
		assume({ i_ckstb, i_hlfck } == (f_pending_half ? 2'b01:2'b10));

	always @(*)
	if (f_pending_half)
		assume(!i_ckstb);
	else if (i_hlfck)
		assume(i_ckstb);

	always @(*)
	if (!i_reset)
	begin
		if (cfg_period == P_1D)
		begin
			assume(!i_ckstb || (!cfg_ddr || !i_hlfck));
		end else
			assume(i_ckstb && i_hlfck);	// On every clock period
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// IO properties
	// {{{

	// Only change on a clock
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!tx_valid);
	else if (!$past(i_ckstb) && !$past(i_hlfck && cfg_ddr))
	begin
		assert($stable(tx_valid));
		assert($stable(tx_data));
	end
	// }}}

	// Unused bits to be set to 1'b1
	// {{{
	always @(*)
	if (!i_reset)
	begin
		if (!tx_valid)
			assert(&tx_data);
		else case(cfg_width)
		WIDTH_1W: begin
			assert(tx_data[31:25] == 7'h7f);
			assert(tx_data[23:17] == 7'h7f);
			assert(tx_data[15: 9] == 7'h7f);
			assert(tx_data[ 7: 1] == 7'h7f);
			end
		WIDTH_4W: begin
			assert(tx_data[31:28] == 4'hf);
			assert(tx_data[23:20] == 4'hf);
			assert(tx_data[15:12] == 4'hf);
			assert(tx_data[ 7: 4] == 4'hf);
			end
		default: begin end
		endcase
	end
	// }}}

	// CFG_PERIOD requires repeated bits
	// {{{
	always @(*)
	if (!i_reset && tx_valid)
	case(cfg_period)
	P_1D: begin
		assert(tx_data[31:24] == tx_data[ 7: 0]);
		assert(tx_data[23:16] == tx_data[ 7: 0]);
		assert(tx_data[15: 8] == tx_data[ 7: 0]);
		end
	P_2D: begin
		assert(tx_data[31:24] == tx_data[23:16]);
		assert(tx_data[15: 8] == tx_data[ 7: 0]);
		end
	default: begin end
	endcase
	// }}}

	always @(posedge i_clk)
	if (!i_reset && pstate == P_CRC || pstate == P_DATA)
		assert(tx_valid && pre_valid);

	always @(posedge i_clk)
	if (!i_reset && pstate == P_IDLE)
		assert(!tx_valid);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI Stream inputs
	// {{{

	// Enable
	// {{{
	always @(posedge i_clk)
	if (!i_reset && (S_VALID || tx_valid))// || pstate != P_IDLE))
		assume(i_en);

	always @(*)
	if (!i_en)
		assume(!S_VALID);

	// always @(posedge i_clk)
	// if (fs_last)
	//	assume(!i_en);

	always @(posedge i_clk)
	if (!i_reset && pstate == P_IDLE)
		assert(fs_count == 0);

	always @(*)
	if (!i_reset)
	begin
		if (!fs_last)
		begin
			assert(fcrc_count == fs_count);
		end else
			assert(fcrc_count >= fs_count);
	end
	// }}}

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!S_VALID);
		assume(!i_en);
	end else if ($past(S_VALID && !S_READY))
	begin
		assume(S_VALID);
		assume($stable(S_DATA));
		assume($stable(S_LAST));
	end else if ($past(S_VALID && !S_LAST))
		assume(S_VALID);

	always @(*)
	if (fs_last)
		assume(!S_VALID);

	always @(*)
	if (fs_count == 10'h3df)
		assume(!S_VALID || S_LAST);

	always @(*)
	if (!i_reset && fs_count >= 10'h3e0)
		assert(fs_last);

	always @(*)
	if (!i_reset && fs_count==0)
		assert(!fs_last);

	always @(posedge i_clk)
	if (!i_reset && (pstate == P_CRC || pstate == P_LAST))
		assert(fs_last);

	always @(posedge i_clk)
	if (!i_reset && pstate == P_DATA)
		assert(!fs_last && S_VALID && fs_count > 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking
	// {{{

	always @(*)
	if (S_VALID && fs_count == fc_posn)
		assume(fc_data == S_DATA);

	// Start bit checking
	// {{{
	always @(*)
	if (!i_reset && tx_valid && fb_count < fd_offset)
	begin
		if (!f_step)
		begin
			case({(cfg_ddr && !f_pending_half), cfg_width})
			{1'b0,WIDTH_1W}: assert(fb_count==1);
			{1'b1,WIDTH_1W}: assert(fb_count==2);
			{1'b0,WIDTH_4W}: assert(fb_count==4);
			{1'b1,WIDTH_1W}: assert(fb_count==8);
			{1'b0,WIDTH_8W}: assert(fb_count==8);
			{1'b1,WIDTH_8W}: assert(fb_count==16);
			default: assert(0);
			endcase
		end
		assert(ck_counts == ((cfg_ddr && f_pending_half) ? 1:0));
		assert(fs_count <= 1);
		assert(fd_count == 0);
		assert(pstate == P_DATA || (pstate == P_CRC && fs_count == 1));
		case(cfg_period)
		P_1D: case(cfg_width)
			WIDTH_1W: assert((cfg_ddr && !f_pending_half)
				|| ({ tx_data[24], tx_data[16], tx_data[8], tx_data[0] } == 4'b0));
			WIDTH_4W: assert((cfg_ddr && !f_pending_half)
				|| ({ tx_data[27:24], tx_data[19:16],
					tx_data[11:8], tx_data[3:0] } == 16'b0));
			WIDTH_8W: assert((cfg_ddr && !f_pending_half)
				|| tx_data == 32'h0);
			default: begin end
			endcase
		P_2D: case(cfg_width)
			WIDTH_1W: assert({ tx_data[24], tx_data[16], tx_data[8], tx_data[0] }
					== (cfg_ddr) ? 4'b0000 : 4'b1100);
			WIDTH_4W:	assert({ tx_data[27:24], tx_data[19:16],
					tx_data[11:8], tx_data[3:0] }
					== (cfg_ddr) ? 16'h00 : 16'hff00);
			WIDTH_8W:	assert(tx_data == (cfg_ddr) ? 32'h00 : 32'hffff_0000);
			default: begin end
			endcase
		P_4D: case(cfg_width)
			WIDTH_1W: assert({ tx_data[24], tx_data[16], tx_data[8], tx_data[0] } == 4'b1100);
			WIDTH_4W: assert({ tx_data[27:24], tx_data[19:16],
					tx_data[11:8], tx_data[3:0] } == 16'hff00);
			WIDTH_8W: assert(tx_data == 32'hffff_0000);
			default: begin end
			endcase
		endcase
	end
	// }}}

	assign	fp_count=((pstate == P_DATA && pre_valid) || (pstate == P_CRC))
			? fs_count-1 : fs_count;

	always @(*)
	if (pre_valid)
	begin
		assert(pstate != P_IDLE);
		if (fp_count == fc_posn && pstate == P_DATA)
			assert(pre_data == fc_data);
	end else begin
		assert(pstate == P_IDLE || pstate == P_LAST);
	end

	// Verify pre_count
	// {{{
	always @(*)
	if (!i_reset)
		assert(pre_count <= 7);

	always @(*)
	if (!i_reset && pstate == P_DATA)
		assert(pre_valid);

	always @(*)
	if (!i_reset && pstate == P_DATA)
	begin
		case(cfg_width)
		WIDTH_1W: assert(pre_count == 0);
		WIDTH_4W: assert(pre_count == (cfg_ddr) ? 3 : 1);
		default: // WIDTH_8W
			assert(pre_count == (cfg_ddr) ? 7 : 3);
		endcase
	end else if (!i_reset && pstate == P_CRC)
	begin
		assert(pre_valid);
		case(cfg_width)
		WIDTH_1W: assert(pre_count == 0);
		WIDTH_4W: assert(pre_count <= (cfg_ddr) ? 3 : 1);
		default: // WIDTH_8W
			assert(pre_count <= (cfg_ddr) ? 7 : 3);
		endcase
	end else if (!i_reset && pstate == P_LAST)
	begin
		assert(pre_count == 0);
	end
	// }}}

	always @(*)
	if (!i_reset && pstate == P_DATA)
	begin
		if (fs_count < 2)
		begin
			assert(fd_count == 0);
		end else begin
			assert(fs_count == (pre_valid ? 1:0) + f_loaded_count[14:5]);
		end
	end

	always @(*)
	if (!i_reset && pstate == P_CRC)
	begin
		assert(pre_valid);
		assert(fcrc_count == 1 + f_loaded_count[14:5]);

		case(cfg_width)
		WIDTH_1W: assert(fcrc_count == fs_count);
		WIDTH_4W: assert(fcrc_count == fs_count + (((cfg_ddr) ? 3 : 1)-pre_count));
		WIDTH_8W: assert(fcrc_count == fs_count + (((cfg_ddr) ? 7 : 3)-pre_count));
		endcase
	end

	always @(*)
	if (!i_reset && pstate == P_LAST)
	begin
		case(cfg_width)
		WIDTH_1W: assert(fcrc_count == fs_count + 1 + (pre_valid ? 0:1));
		WIDTH_4W: assert(fcrc_count == fs_count + 1 + (pre_valid ? 0:1)
				+ (((cfg_ddr) ? 3 : 1)-pre_count));
		WIDTH_8W: assert(fcrc_count == fs_count + 1 + (pre_valid ? 0:1)
				+ (((cfg_ddr) ? 7 : 3)-pre_count));
		endcase
	end

	always @(*)
	if (!i_reset && (pstate == P_IDLE || !tx_valid))
		assert(ck_counts == 0);

	always @(*)
	if (!i_reset && fb_count >= fd_offset)
	case(cfg_period)
	P_1D: case(cfg_width)
		// {{{
		WIDTH_1W: begin end
		WIDTH_4W: begin
				assert(ck_counts <= 7);
			end
		WIDTH_8W: begin
				assert(ck_counts <= 3);
			end
		endcase
		// }}}
	P_2D: case(cfg_width)
		// {{{
		WIDTH_1W: begin
				assert(ck_counts <= 15);
			end
		WIDTH_4W: begin
				assert(ck_counts <= 3);
			end
		WIDTH_8W: begin
				assert(ck_counts <= 1);
			end
		endcase
		// }}}
	P_4D: case(cfg_width)
		// {{{
		WIDTH_1W: begin
				assert(ck_counts <= 7);
			end
		WIDTH_4W: begin
				assert(ck_counts <= 1);
			end
		WIDTH_8W: begin
			assert(ck_counts == 0);
			if (pstate == P_DATA) begin
				assert(fd_count + 32 == { fp_count, 5'h0 });
				if (fd_count == { fc_posn, 5'h0 })
					assert(ck_data == fc_data);
			end end
		endcase
		// }}}
	endcase

	// Verify fb_count modulo step is always zero
	// {{{
	always @(*)
	if (!i_reset)
	begin
		case(cfg_period)
		P_1D: case(cfg_width)
			// {{{
			WIDTH_1W: begin end
			WIDTH_4W: assert(fb_count[1:0] == 2'b0);
			WIDTH_8W: assert(fb_count[2:0] == 3'b0);
			endcase
			// }}}
		P_2D: case(cfg_width)
			// {{{
			WIDTH_1W: assert(fb_count[0] == 1'b0);
			WIDTH_4W: assert(fb_count[2:0] == 3'b0);
			WIDTH_8W: assert(fb_count[3:0] == 4'b0);
			endcase
			// }}}
		P_4D: case(cfg_width)
			// {{{
			WIDTH_1W: assert(fb_count[1:0] == 2'h0);
			WIDTH_4W: assert(fb_count[3:0] == 4'h0);
			WIDTH_8W: assert(fb_count[4:0] == 5'h0);
			endcase
			// }}}
		endcase
	end
	// }}}

	// Verify f_loaded_count[4:0]
	// {{{
	always @(*)
	if (!i_reset)
	begin
		// assert(f_loaded_count[4:0] == 0);
		if (pstate == P_DATA || pstate == P_CRC) case(cfg_period)
		P_1D: case(cfg_width)
			WIDTH_1W: assert(f_loaded_count[4:0] == 5'h00);
			WIDTH_4W: assert(f_loaded_count[4:0] == 5'h00);
			WIDTH_8W: assert(f_loaded_count[4:0] == 5'h00);
			default: begin end
			endcase
		P_2D: case(cfg_width)
			WIDTH_1W: assert(f_loaded_count[4:0] == (f_step ? 5'h00 : 5'h04));
			WIDTH_4W: assert(f_loaded_count[4:0] == (f_step ? 5'h00 : 5'h08));
			WIDTH_8W: assert(f_loaded_count[4:0] == 5'h0);
			default: begin end
			endcase
		P_4D: case(cfg_width)
			WIDTH_1W: assert(f_loaded_count[4:0] == (f_step ? 5'h00 : 5'h08));
			WIDTH_4W: assert(f_loaded_count[4:0] == (f_step ? 5'h00 : 5'h10));
			WIDTH_8W: assert(f_loaded_count[4:0] == 5'h0);
			default: begin end
			endcase
		default: begin end
		endcase
	end
	// }}}

	// Verify ck_count[LSB] for DDR
	// {{{
	always @(*)
	if (!i_reset && tx_valid && cfg_ddr && cfg_period == P_1D)
	begin
		assert(ck_counts[0] == f_pending_half
			|| (!pre_valid && pstate == P_LAST && ck_counts==0));
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{

	// Pre-contract cover check: Can we start a packet in each mode?
	// {{{
	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && tx_valid)
	begin
		case(cfg_period)
		P_1D: case(cfg_width)
			// {{{
			WIDTH_1W: cover(1);
			WIDTH_4W: cover(1);
			WIDTH_8W: cover(1);
			default: begin end
			endcase
			// }}}
		P_2D: if(cfg_ddr)
			// {{{
			begin
				case(cfg_width)
				WIDTH_1W: cover(1);
				WIDTH_4W: cover(1);
				WIDTH_8W: cover(1);
				default: begin end
				endcase
			end else begin
				case(cfg_width)
				WIDTH_1W: cover(1);
				WIDTH_4W: cover(1);
				WIDTH_8W: cover(1);
				default: begin end
				endcase
			end
			// }}}
		P_4D: case(cfg_width)
			// {{{
			WIDTH_1W: cover(1);
			WIDTH_4W: begin
				cover(1);
				cover(fs_count == 1);
				cover(fs_count == 2);
				cover(fs_count == 3);		// !!!
				cover(fs_count == 4);		// !!!
				cover(S_VALID && S_LAST);
				cover(!S_VALID);
				cover($fell(pre_valid));
				cover(pstate == P_CRC);
				cover(pstate == P_LAST);	// !!!
				cover(!pre_valid);		// !!!
				end
			WIDTH_8W: cover(1);
			default: begin end
			endcase
			// }}}
		endcase
	end
	// }}}

	// Contract covers: can we complete a packet in the first place?
	// {{{
	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && $fell(tx_valid))
	begin
		case(cfg_period)
		P_1D: case(cfg_width)
			// {{{
			WIDTH_1W: cover(1);		// !!!
			WIDTH_4W: cover(1);		// !!!
			WIDTH_8W: cover(1);		// !!!
			default: begin end
			endcase
			// }}}
		P_2D: if(cfg_ddr)
			// {{{
			begin
				case(cfg_width)
				WIDTH_1W: cover(1);		// !!!
				WIDTH_4W: cover(1);
				WIDTH_8W: cover(1);
				default: begin end
				endcase
			end else begin
				case(cfg_width)
				WIDTH_1W: cover(1);		// !!!
				WIDTH_4W: cover(1);
				WIDTH_8W: cover(1);
				default: begin end
				endcase
			end
			// }}}
		P_4D: case(cfg_width)
			// {{{
			WIDTH_1W: cover(1);		// !!!
			WIDTH_4W: cover(1);		// !!!
			WIDTH_8W: cover(1);
			default: begin end
			endcase
			// }}}
		endcase
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{

	// }}}
`endif	// FORMAL
// }}}
endmodule

