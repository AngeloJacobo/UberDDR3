////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbicapetwo.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This routine maps the configuration registers of a 7-series
//		Xilinx part onto register addresses on a wishbone bus interface
//		via the ICAPE2 access port to those parts.  The big thing this
//		captures is the timing and handshaking required to read and
//		write registers from the configuration interface.
//
//		As an example of what can be done, writing a 32'h00f to
//		local address 5'h4 sends the IPROG command to the FPGA, causing
//		it to immediately reconfigure itself.
//
//		As another example, the warm boot start address is located
//		in register 5'h10.  Writing to this address, followed by
//		issuing the IPROG command just mentioned will cause the
//		FPGA to configure from that warm boot start address.
// 
//		For more details on the configuration interface, the registers
//		in question, their meanings and what they do, please see
//		User's Guide 470, the "7 Series FPGAs Configuration" User
//		Guide.
//
// Notes:	This module supports both reads and writes from the ICAPE2
//		interface.  These follow the following pattern.
//
//	For writes:
//		(Idle)	0xffffffff	(Dummy)
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0xaa995566	SYNC WORD
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	...		Write command
//		(CS/W)	...		Write value, from Wishbone bus
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x30008001	Write to CMD register (address 4)
//		(CS/W)	0x0000000d	DESYNC command
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(Idle)
//
//	and for reads:
//		(Idle)	0xffffffff	(Dummy)
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0xaa995566	SYNC WORD
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	...		Read command
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(Idle)	0x20000000	(Idle the interface again, so we can rd)
//		(CS/R)	0x20000000	(Wait)
//		(CS/R)	0x20000000	(Wait)
//		(CS/R)	0x20000000	(Wait)
//		(CS/R)	0x20000000	(Wait)
//		(Idle)	0x20000000	(Idle the interface before writing)
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x30008001	Write to CMD register (address 4)
//		(CS/W)	0x0000000d	DESYNC command
//		(CS/W)	0x20000000	NOOP
//		(CS/W)	0x20000000	NOOP
//		(Idle)
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
`default_nettype none
// }}}
module	wbicapetwo #(
		parameter	LGDIV = 3	/// Log of the clock divide
	) (
		// {{{
		input	wire		i_clk,
		// Wishbone inputs
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[4:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		// Wishbone outputs
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		//
		output	wire	[31:0]	o_dbg
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Local declarations
	// {{{
	localparam [4:0]	MBOOT_IDLE	= 5'h00,
				MBOOT_START	= 5'h01,
				MBOOT_END_OF_SYNC  = 5'h05,
				MBOOT_READ	= 5'h06,
				MBOOT_END_OF_READ  = 5'h0e,
				MBOOT_WRITE	= 5'h0f,
				MBOOT_END_OF_WRITE = 5'h10,
				MBOOT_DESYNC	= 5'h11,
				MBOOT_END	   = 5'h17;
		localparam [31:0]	NOOP = 32'h2000_0000;

	// ICAPE2 interface signals
	//	These are kept internal to this block ...

	genvar	k;
	reg		wb_req, r_we, pre_stall;
	reg	[31:0]	r_data;
	reg	[4:0]	r_addr;

	reg	[31:0]	cfg_in;
	reg		cfg_cs_n, cfg_rdwrn;
	wire	[31:0]	cfg_out;
	reg	[4:0]	state;

	wire	[31:0]	bit_swapped_cfg_in;
	wire	[31:0]	bit_swapped_cfg_out;

	reg		clk_stb;
	wire		slow_clk;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal "Clock" generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate
	if (LGDIV <= 1)
	begin : DDRCK
		// {{{
		reg		r_slow_clk;
		always @(posedge i_clk)
		begin
			r_slow_clk  <= (slow_clk + 1'b1);
			// We'll move on the positive edge of the clock,
			// so therefore clk_stb must be true one clock before
			// that, so we test for it one clock before that.
			clk_stb   <= (slow_clk == 1'b1);
		end

		assign	slow_clk = r_slow_clk;
		// }}}
	end else begin : CLOCKGEN
		// {{{
		reg	[(LGDIV-1):0]	slow_clk_counter;
		localparam [LGDIV-1:0]	MINUS_TWO = -2;

		initial	slow_clk_counter = 0;
		always @(posedge i_clk)
		begin
			slow_clk_counter  <= slow_clk_counter + 1'b1;
			// We'll move on the negative edge of the clock, so
			// therefore clk_stb must be true one clock before
			// that, so we test for it one clock before that.
			clk_stb <= (slow_clk_counter==MINUS_TWO);
		end

		assign	slow_clk = slow_clk_counter[(LGDIV-1)];
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Giant state machine
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	state = MBOOT_IDLE;
	initial	cfg_cs_n  = 1'b1;
	initial	cfg_rdwrn = 1'b1;
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	begin
		// In general, o_wb_ack is always zero.  The exceptions to this
		// will be handled individually below.
		o_wb_ack <= 1'b0;
		// We can simplify our logic a touch by always setting
		// o_wb_data.  It will only be examined if o_wb_ack
		// is also true, so this is okay.
		o_wb_data <= cfg_out;

		// Turn any request "off", so that it will not be ack'd, if
		// the wb_cyc line is ever lowered.
		wb_req <= wb_req && i_wb_cyc;

		pre_stall <= (state != MBOOT_IDLE);
		if (clk_stb)
		begin
			state <= state + 5'h01;
			case(state)
			MBOOT_IDLE: begin
				// {{{
				cfg_cs_n <= 1'b1;
				cfg_rdwrn <= 1'b1;
				cfg_in <= 32'hffffffff;	// Dummy word

				state <= MBOOT_IDLE;
				pre_stall <= 1'b0;

				o_wb_ack <= 1'b0;

				r_addr <= i_wb_addr;
				r_data <= i_wb_data;
				r_we   <= i_wb_we;
				if(i_wb_stb) // &&(!o_wb_stall)
				begin
					if (&i_wb_sel)
					begin
						state <= MBOOT_START;
						wb_req <= 1'b1;
						pre_stall <= 1'b1;
					end else
						o_wb_ack <= 1'b1;
				end end
				// }}}
			MBOOT_START: begin
				// {{{
				cfg_in <= 32'hffffffff; // NOOP
				cfg_cs_n <= 1'b1;
				end
				// }}}
			5'h02: begin
				// {{{
				cfg_cs_n <= 1'b0; // Activate interface
				cfg_rdwrn <= 1'b0;
				cfg_in <= 32'h20000000;	// NOOP
				end
				// }}}
			5'h03: begin // Sync word
				// {{{
				cfg_in <= 32'haa995566;	// Sync word
				cfg_cs_n <= 1'b0;
				end
				// }}}
			5'h04: begin // NOOP
				// {{{
				cfg_in <= 32'h20000000; // NOOP
				cfg_cs_n <= 1'b0;
				end
				// }}}
			5'h05: begin // NOOP
				// {{{
				// Opening/sync sequence is complete.  Continue
				// now with either the read or write sequence
				cfg_in <= 32'h20000000;	// NOOP
				state <= (r_we) ? MBOOT_WRITE : MBOOT_READ;
				cfg_cs_n <= 1'b0;
				end
				// }}}
			MBOOT_READ: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= { 8'h28, 6'h0, r_addr, 13'h001 };
				end
				// }}}
			5'h07: begin	// (Read, NOOP)
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h20000000; // NOOP
				end
				// }}}
			5'h08: begin	// (Read, NOOP)
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h20000000; // NOOP
				end
				// }}}
			5'h09: begin // Idle the interface before the read cycle
				// {{{
				cfg_cs_n <= 1'b1;
				cfg_rdwrn <= 1'b1;
				cfg_in <= 32'h20000000; // NOOP
				end
				// }}}
			5'h0a: begin // Re-activate the interface, wait 3 cycles
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_rdwrn <= 1'b1;
				cfg_in <= 32'h20000000; // NOOP
				end
				// }}}
			5'h0b: begin // NOOP ... still waiting, cycle two
				// {{{
				cfg_in <= 32'h20000000; // NOOP
				cfg_cs_n <= 1'b0;
				end
				// }}}
			5'h0c: begin // NOOP ... still waiting, cycle three
				// {{{
				cfg_in <= 32'h20000000; // NOOP
				cfg_cs_n <= 1'b0;
				end
				// }}}
			5'h0d: begin // NOOP ... still waiting, cycle four
				// {{{
				cfg_in <= 32'h20000000; // NOOP
				cfg_cs_n <= 1'b0;
				end
				// }}}
			MBOOT_END_OF_READ: begin // and now our answer is there
				// {{{
				cfg_cs_n <= 1'b1;
				cfg_rdwrn <= 1'b1;
				cfg_in <= 32'h20000000; // NOOP
				//
				// Wishbone return
				o_wb_ack <= i_wb_cyc && wb_req;
				// o_wb_data <= cfg_out; // Independent of state
				wb_req <= 1'b0;
				//
				state <= MBOOT_DESYNC;
				end
				// }}}
			MBOOT_WRITE: begin // Issue write cmd to the given addr
				// {{{
				cfg_in <= { 8'h30, 6'h0, r_addr, 13'h001 };
				cfg_cs_n <= 1'b0;
				end
				// }}}
			MBOOT_END_OF_WRITE: begin
				// {{{
				cfg_in <= r_data;	// Write the value
				cfg_cs_n <= 1'b0;
				end
				// }}}
			MBOOT_DESYNC: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_rdwrn <= 1'b0;
				cfg_in <= 32'h20000000;	// 1st NOOP
				end
				// }}}
			5'h12: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h20000000;	// 2nd NOOP
				end
				// }}}
			5'h13: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h30008001;	// Write to CMD register
				end
				// }}}
			5'h14: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h0000000d;	// DESYNC command
				end
				// }}}
			5'h15: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h20000000;	// NOOP
				end
				// }}}
			5'h16: begin
				// {{{
				cfg_cs_n <= 1'b0;
				cfg_in <= 32'h20000000;	// NOOP
				end
				// }}}
			MBOOT_END: begin // Acknowledge the bus transaction,
				// {{{
				// it is now complete
				o_wb_ack <= i_wb_cyc && wb_req;
				wb_req <= 1'b0;
				//
				cfg_cs_n <= 1'b1;
				cfg_rdwrn <= 1'b0;
				cfg_in <= 32'hffffffff;	// DUMMY
				//
				state <= MBOOT_IDLE;
				pre_stall <= 1'b0;
				end
				// }}}
			default: begin
				// {{{
				wb_req <= 1'b0;
				cfg_cs_n <= 1'b1;
				cfg_rdwrn <= 1'b0;
				state <= MBOOT_IDLE;
				pre_stall <= 1'b0;
				cfg_in <= 32'hffffffff;	// DUMMY WORD
				end
				// }}}
			endcase
		end
	end

	assign	o_wb_stall = pre_stall || !clk_stb;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bit-swap in and out registers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	// The data registers to the ICAPE2 interface are bit swapped within
	// each byte.  Thus, in order to read from or write to the interface,
	// we need to bit swap the bits in each byte.  These next lines
	// accomplish that for both the input and output ports.
	//
	generate for(k=0; k<8; k=k+1)
	begin : GEN_BITSWAP
		assign bit_swapped_cfg_in[   k] = cfg_in[   7-k];
		assign bit_swapped_cfg_in[ 8+k] = cfg_in[ 8+7-k];
		assign bit_swapped_cfg_in[16+k] = cfg_in[16+7-k];
		assign bit_swapped_cfg_in[24+k] = cfg_in[24+7-k];
	end endgenerate

	generate for(k=0; k<8; k=k+1)
	begin : GEN_CFGOUT
		assign cfg_out[   k] = bit_swapped_cfg_out[   7-k];
		assign cfg_out[ 8+k] = bit_swapped_cfg_out[ 8+7-k];
		assign cfg_out[16+k] = bit_swapped_cfg_out[16+7-k];
		assign cfg_out[24+k] = bit_swapped_cfg_out[24+7-k];
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Instantiate ICAPE2
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	VERILATOR
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, slow_clk, cfg_cs_n, cfg_rdwrn };
	assign	bit_swapped_cfg_out = bit_swapped_cfg_in;
	// Verilator lint_on  UNUSED
`else
`ifndef	FORMAL
	ICAPE2 #(
		.ICAP_WIDTH("X32")
	) reconfig(
		.CLK(slow_clk), .CSIB(cfg_cs_n), .RDWRB(cfg_rdwrn),
		.I(bit_swapped_cfg_in), .O(bit_swapped_cfg_out)
	);
`else
	(* anyseq *)	wire	[31:0]	f_icape_return;

	assign	bit_swapped_cfg_out = f_icape_return;
`endif
`endif
	// }}}

	assign o_dbg = { (i_wb_stb && !o_wb_stall),		// TRIGGER
		clk_stb, slow_clk, 1'b0,			// 3b
		i_wb_stb, o_wb_ack, cfg_cs_n, cfg_rdwrn,	// 4b
		o_wb_stall, 2'h0, state,			// 8b
		   (cfg_rdwrn) ?
			(clk_stb ? cfg_out[15:0]:cfg_out[31:16])
			: (clk_stb ? cfg_in[15:0] : cfg_in[31:16]) };	// 16b
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
	// This is only a partial formal proof
	localparam	F_LGDEPTH = 4;
	reg			f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwb_nreqs, fwb_nacks, fwb_outstanding;
	reg			fwb_we;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	fwb_slave #(
		// {{{
		.AW(5), .F_MAX_STALL(0), .F_MAX_ACK_DELAY(0),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(!f_past_valid),
		//
		// Wishbone inputs
		.i_wb_cyc(i_wb_cyc),
		.i_wb_stb(i_wb_stb),
		.i_wb_we(i_wb_we),
		.i_wb_addr(i_wb_addr),
		.i_wb_data(i_wb_data),
		.i_wb_sel(i_wb_sel),
		.i_wb_ack(o_wb_ack),
		.i_wb_err(1'b0),
		.i_wb_stall(o_wb_stall),
		.f_nreqs(fwb_nreqs),
		.f_nacks(fwb_nacks),
		.f_outstanding(fwb_outstanding)
		// }}}
	);

	always @(*)
		assert(fwb_outstanding <= 1);

	always @(*)
	if (i_wb_cyc)
		assert(fwb_outstanding == ((o_wb_ack || wb_req) ? 1:0));

	always @(*)
	if (!clk_stb || state != MBOOT_IDLE)
		assert(o_wb_stall);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	always @(posedge i_clk)
	if (i_wb_stb && !o_wb_stall)
		fwb_we <= i_wb_we;

	always @(*)
	if (state >= MBOOT_WRITE && state < MBOOT_DESYNC)
		assert(fwb_we);

	always @(*)
	if (state < MBOOT_WRITE && state >= MBOOT_READ)
		assert(!fwb_we);

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if (state == MBOOT_IDLE)
			assert(!wb_req);

		case(state)
		MBOOT_IDLE: assert($stable(state) || $past(state) == MBOOT_END);
		MBOOT_READ: assert($stable(state)
				|| $past(state) == MBOOT_END_OF_SYNC);
		MBOOT_WRITE:assert($stable(state)
				|| $past(state) == MBOOT_END_OF_SYNC);
		MBOOT_DESYNC:assert($stable(state)
				|| $past(state) == MBOOT_END_OF_WRITE
				|| $past(state) == MBOOT_END_OF_READ);
		default:
			assert($stable(state) || state == $past(state)+1);
		endcase
	end

	always @(*)
		assert(state <= 5'h17);

	always @(*)
	case(state)
	MBOOT_IDLE: begin
		// {{{
		if (f_past_valid)
		begin
			assert(cfg_cs_n);
			// assert(cfg_rdwrn);
		// cfg_cs_n <= 1'b1;
		// cfg_rdwrn <= 1'b1;
		// cfg_in <= 32'hffffffff;	// Dummy word
		end end
		// }}}
	MBOOT_START: begin
		// {{{
		// cfg_in <= 32'hffffffff; // NOOP
		// cfg_cs_n <= 1'b1;
		assert(cfg_cs_n);
		assert(cfg_rdwrn);
		end
		// }}}
	5'h02: begin
		// {{{
		assert(cfg_cs_n);
		assert(cfg_rdwrn);
		assert(&cfg_in);
		end
		// }}}
	5'h03: begin
		// {{{
		assert(!cfg_cs_n); // Activate interface
		assert(!cfg_rdwrn);
		assert(cfg_in == 32'h20000000);	// NOOP
		end
		// }}}
	5'h04: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == 32'haa995566);	// NOOP
		end
		// }}}
	5'h05: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == 32'h2000_0000);	// NOOP
		end
		// }}}
	MBOOT_READ: begin
		// {{{
		assert(!cfg_cs_n); // Activate interface
		assert(!cfg_rdwrn);
		assert(cfg_in == 32'h2000_0000);	// NOOP
		end
		// }}}
	5'h07: begin
		// {{{
		assert(!cfg_cs_n);
		// cfg_in <= { 8'h28, 6'h0, r_addr, 13'h001 };
		end
		// }}}
	5'h08: begin
		// {{{
		assert(!cfg_cs_n); // Activate interface
		assert(!cfg_rdwrn);
		assert(cfg_in == NOOP);	// NOOP
		end
		// }}}
	5'h09: begin // Idle the interface before the read cycle
		// {{{
		// cfg_cs_n <= 1'b1;
		// cfg_rdwrn <= 1'b1;
		// cfg_in <= 32'h20000000; // NOOP
		end
		// }}}
	5'h0a: begin // Re-activate the interface and wait 3 cycles
		// {{{
		assert(cfg_cs_n);
		assert(cfg_rdwrn);
		assert(cfg_in == NOOP);	// NOOP
		end
		// }}}
	5'h0b: begin // ... still waiting, cycle two
		// {{{
		assert(!cfg_cs_n);
		assert(cfg_rdwrn);
		assert(cfg_in == NOOP);	// NOOP
		end
		// }}}
	5'h0c: begin // ... still waiting, cycle three
		// {{{
		assert(!cfg_cs_n);
		assert(cfg_rdwrn);
		assert(cfg_in == NOOP);	// NOOP
		end
		// }}}
	5'h0d: begin // ... still waiting, cycle four
		// {{{
		assert(!cfg_cs_n);
		assert(cfg_rdwrn);
		assert(cfg_in == NOOP);	// NOOP
		end
		// }}}
	MBOOT_END_OF_READ: begin // and now our answer is there
		// {{{
		// cfg_in <= 32'h20000000; // NOOP
		// cfg_cs_n <= 1'b0;
		// cfg_cs_n <= 1'b1;
		end
		// }}}
	MBOOT_WRITE: begin
		// {{{
		// Issue a write command to the given address
		// cfg_in <= { 8'h30, 6'h0, r_addr, 13'h001 };
		// cfg_cs_n <= 1'b0;
		end
		// }}}
	MBOOT_END_OF_WRITE: begin
		// {{{
		// cfg_in <= r_data;	// Write the value
		// cfg_cs_n <= 1'b0;
		end
		// }}}
	MBOOT_DESYNC: begin
		// {{{
		// cfg_cs_n <= 1'b0;
		// cfg_rdwrn <= 1'b0;
		// cfg_in <= 32'h20000000;	// 1st NOOP
		end
		// }}}
	5'h12: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == NOOP);
		end
		// }}}
	5'h13: begin
		// {{{
		// cfg_cs_n <= 1'b0;
		// cfg_in <= 32'h30008001;	// Write to CMD register
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == NOOP);
		end
		// }}}
	5'h14: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == 32'h30008001);
		// cfg_in <= 32'h0000000d;	// DESYNC command
		end
		// }}}
	5'h15: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == 32'h0d);
		// cfg_in <= 32'h0000000d;	// DESYNC command
		end
		// }}}
	5'h16: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == NOOP);
		end
		// }}}
	MBOOT_END: begin
		// {{{
		assert(!cfg_cs_n);
		assert(!cfg_rdwrn);
		assert(cfg_in == NOOP);
		end
		// }}}
	default: assert(0);
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	cvr_write, cvr_read;

	always @(*)
	if (f_past_valid)
		cover(o_wb_ack);

	initial	cvr_write = 1'b0;
	always @(posedge i_clk)
	if (i_wb_cyc && o_wb_ack && fwb_we)
		cvr_write <= 1'b1;

	initial	cvr_read = 1'b0;
	always @(posedge i_clk)
	if (i_wb_cyc && o_wb_ack && !fwb_we)
		cvr_read <= 1'b1;

	always @(*)
	if (!o_wb_stall && cvr_write && !i_wb_cyc)
		cover(cvr_write);

	always @(*)
	if (!o_wb_stall && cvr_write && !i_wb_cyc)
		cover(cvr_read);
	// }}}
`endif
// }}}
endmodule
