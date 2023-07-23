////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	spirxdata.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	To handle all of the processing associated with receiving data
//		from an SD card via the lower-level SPI processor, and then
//	issuing write commands to our internal memory store (external to this
//	module).
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
module spirxdata #(
		// {{{
		parameter	DW = 32, AW = 8,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		localparam	CRC_POLYNOMIAL = 16'h1021
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		i_start,
		input	wire	[3:0]	i_lgblksz,
		input	wire		i_fifo,
		output	reg		o_busy,
		//
		input	wire		i_ll_stb,
		input	wire [7:0]	i_ll_byte,
		//
		output	reg 		o_write,
		output	reg [AW-1:0]	o_addr,
		output	reg [DW-1:0]	o_data,
		//
		output	reg 		o_rxvalid,
		output	reg [7:0]	o_response
		// }}}
	);

	// Signal declarations
	// {{{
	reg		error_token, start_token, token, received_token, done,
			lastaddr;
	reg		all_mem_written, lastdata;

	reg	[1:0]	crc_byte;
	reg	[2:0]	r_lgblksz_m3;
	reg	new_data_byte;
	reg	[3:0]	crc_fill;
	reg	[7:0]	crc_gearbox;
	reg	[15:0]	next_crc_data;
	reg	[15:0]	crc_data;
	reg		crc_err, crc_active;
	reg	[2:0]	fill;
	reg	[23:0]	gearbox;
	reg	[15:0]	first_crc_data;
	// }}}

	// error_token
	// {{{
	always @(*)
	begin
		error_token = 0;

		if (i_ll_byte[7:4] == 0)
			error_token = 1;
		if (!i_ll_stb || received_token)
			error_token = 0;
	end
	// }}}

	// start_token
	// {{{
	always @(*)
	begin
		start_token = 0;

		if (!i_ll_byte[0])
			start_token = 1;
		if (!i_ll_stb || received_token)
			start_token = 0;
	end
	// }}}

	// token
	// {{{
	always @(*)
		token = (start_token || error_token);
	// }}}

	// done
	// {{{
	always @(*)
		done = (i_ll_stb && (crc_byte>1));
	// }}}

	// received_token
	// {{{
	initial	received_token = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		received_token <= 0;
	else if (token)
		received_token <= 1;
	// }}}

	// o_busy
	// {{{
	initial	o_busy = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_busy <= 0;
	else if (!o_busy)
		o_busy <= i_start;
	else if (error_token || done)
		o_busy <= 0;
	// }}}

	// o_rxvalid
	// {{{
	initial	o_rxvalid = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		o_rxvalid <= 0;
	else if (error_token || done)
		o_rxvalid <= 1;
	// }}}

	// o_response
	// {{{
	initial	o_response = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		o_response <= 0;
	else if (error_token)
		o_response <= i_ll_byte;
	else if (done)
		o_response <= (crc_err || (crc_data[7:0] != i_ll_byte)) ? 8'h10 : 0;
	// }}}

	// o_write
	// {{{
	initial	o_write = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		o_write <= 0;
	else if (received_token && !all_mem_written)
		o_write <= (&fill) && i_ll_stb;
	else
		o_write <= 0;
	// }}}

	// o_data
	// {{{
	initial	o_data = 0;
	always @(posedge i_clk)
	if (received_token && !all_mem_written)
	begin
		if (OPT_LITTLE_ENDIAN)
			o_data <= { i_ll_byte, gearbox };
		else
			o_data <= { gearbox, i_ll_byte };
	end
	// }}}

	// o_addr
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
		o_addr <= { i_fifo, {(AW-1){1'b0}} };
	else if (o_write && !lastaddr)
		o_addr <= o_addr + 1;
	// }}}

	// fill
	// {{{
	initial	fill = 0;
	always @(posedge i_clk)
	begin
		if (i_ll_stb)
		begin
			if (OPT_LITTLE_ENDIAN)
				gearbox <= { i_ll_byte, gearbox[23:8] };
			else
				gearbox <= { gearbox[15:0], i_ll_byte };
		end

		if (!o_busy || !received_token)
			fill <= 0;
		else if ((&fill) && i_ll_stb)
			fill <= 0;
		else if (i_ll_stb)
			fill <= { fill[1:0], 1'b1 };
	end
	// }}}

	// lastdata
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
		lastdata <= 0;
	else if (!lastdata)
		lastdata <= (lastaddr && (&fill));
	// }}}

	// all_mem_written
	// {{{
	initial	all_mem_written = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		all_mem_written <= 0;
	else if (o_write && lastaddr)
		all_mem_written <= 1;
	// }}}

	// crc_byte
	// {{{
	initial	crc_byte = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		crc_byte <= 0;
	else if (i_ll_stb && lastaddr && lastdata)
		crc_byte <= crc_byte + 1;
	// }}}

	// lastaddr, r_lgblksz_m3
	// {{{
	initial	r_lgblksz_m3 = 0;
	initial	lastaddr = 0;
	always @(posedge i_clk)
	if (!o_busy)
	begin
		lastaddr <= (i_lgblksz < 4);
		// Verilator lint_off WIDTH
		r_lgblksz_m3 <= i_lgblksz-3;
		// Verilator lint_on WIDTH
	end else if (o_write && !lastaddr)
	begin
		case(r_lgblksz_m3)
		0: lastaddr <= 1;		//   8 bytes
		1: lastaddr <= (&o_addr[1:1]);	//  16 bytes
		2: lastaddr <= (&o_addr[2:1]);	//  32 bytes
		3: lastaddr <= (&o_addr[3:1]);	//  64 bytes
		4: lastaddr <= (&o_addr[4:1]);	// 128 bytes
		5: lastaddr <= (&o_addr[5:1]);	// 256 bytes
		default: lastaddr <= (&o_addr[6:1]);	// 512 bytes
		endcase
	end
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// CRC calculation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// new_data_byte
	// {{{
	always @(*)
		new_data_byte = (i_ll_stb && !all_mem_written);
	// }}}

	// crc_fill, crc_active
	// {{{
	initial	crc_fill   = 0;
	initial	crc_active = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy || !received_token)
	begin
		crc_fill <= 0;
		crc_active <= 0;
	end else if (crc_active || new_data_byte)
	begin
		// Verilator lint_off WIDTH
		crc_fill <= crc_fill - (crc_active ? 1:0)
					+ (new_data_byte ? 4:0);
		// Verilator lint_on WIDTH
		if (new_data_byte)
			crc_active <= 1;
		else
			crc_active <= (crc_fill > 1);
	end
	// }}}

	// crc_gearbox
	// {{{
	always @(posedge i_clk)
	if (!crc_active)
		crc_gearbox <= i_ll_byte;
	else
		crc_gearbox <= { crc_gearbox[8-3:0], 2'b00 };
	// }}}


	// first_crc_data, next_crc_data
	// {{{
	always @(*)
	begin
		first_crc_data = crc_data << 1;;

		if (crc_data[15] ^ crc_gearbox[7])
			first_crc_data = first_crc_data ^ CRC_POLYNOMIAL;

		if (first_crc_data[15] ^ crc_gearbox[6])
			next_crc_data = (first_crc_data << 1) ^ CRC_POLYNOMIAL;
		else
			next_crc_data = (first_crc_data << 1);
	end
	// }}}

	// crc_data
	// {{{
	initial	crc_data = 0;
	always @(posedge i_clk)
	if (!o_busy)
		crc_data <= 0;
	else if (crc_active)
		crc_data <= next_crc_data;
	// }}}

	// crc_err
	// {{{
	initial	crc_err = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		crc_err <= 0;
	else if (i_ll_stb && (crc_byte == 1))
		crc_err <= (crc_data[15:8] != i_ll_byte);
	// else if (i_ll_stb && (crc_byte == 2)
	//	crc_err <= (crc_data[7:0] != i_ll_byte);
	// }}}
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
`ifdef	SPIRXDATA
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg		f_past_valid;
	reg	[3:0]	f_lgblksz;
	wire	[3:0]	f_lgblksz_m3;
	reg		f_fifo;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	// Reset check(s)
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(!o_busy);
		assert(o_write  == 0);
	end

	always @(posedge i_clk)
	if (!f_past_valid || !$past(o_busy))
	begin
		assert(!o_rxvalid);
		assert(crc_fill == 0);
	end

	always @(*)
	if (!o_busy)
		assert(!o_write);

	////////////////////////////////////////////////////////////////////////
	//
	// Data assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[6:0]	f_last_read;

	initial	f_last_read = 0;
	always @(posedge i_clk)
	begin
		f_last_read <= f_last_read << 1;
		if (i_ll_stb)
			f_last_read[0] <= 1;
	end

`ifdef	VERIFIC
	always @(*)
		`ASSUME($onehot0({f_last_read, i_ll_stb}));
`else
	always @(*)
	case({f_last_read, i_ll_stb})
	8'h00: begin end
	8'h01: begin end
	8'h02: begin end
	8'h04: begin end
	8'h08: begin end
	8'h10: begin end
	8'h20: begin end
	8'h40: begin end
	8'h80: begin end
	default: `ASSUME(0);
	endcase
`endif

	always @(*)
	if (!o_busy && i_start)
	begin
		`ASSUME(i_lgblksz <= 9);
		`ASSUME(i_lgblksz >= 3);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (o_busy)
		assert(crc_active == (crc_fill > 0));

	always @(*)
	if (o_write)
		assert(fill == 0);

	always @(*)
	if (o_busy && crc_byte > 0)
	begin
		assert(lastaddr);
		assert(all_mem_written || o_write);
		assert(lastdata);
	end

	always @(*)
	if (o_busy && all_mem_written)
	begin
		assert(lastaddr);
		assert(lastdata);
	end

	always @(*)
	if (o_busy && lastdata)
	begin
		assert(lastaddr);
		assert((&fill) || o_write || all_mem_written);
	end

	always @(posedge i_clk)
	if (!o_busy)
	begin
		f_lgblksz <= i_lgblksz;
		f_fifo <= i_fifo;
	end

	assign	f_lgblksz_m3 = f_lgblksz - 3;

	always @(*)
	if (o_busy)
	begin
		assert(f_lgblksz >= 3);
		assert(f_lgblksz <= 9);

		assert(o_addr[AW-1] == f_fifo);

		if (!received_token)
		begin
			assert((f_lgblksz == 3) || !lastaddr);
			assert(o_addr[AW-2:0] == 0);
			assert(fill == 0);
		end
	end

	always @(*)
	if (o_busy)
		assert(f_lgblksz_m3[2:0] == r_lgblksz_m3);

	always @(*)
	if (o_busy)
	case(r_lgblksz_m3)
	3'h0: assert(lastaddr);			//   8 bytes
	3'h1: assert(lastaddr == (&o_addr[1:0]));	//  16 bytes
	3'h2: assert(lastaddr == (&o_addr[2:0]));	//  32 bytes
	3'h3: assert(lastaddr == (&o_addr[3:0]));	//  64 bytes
	3'h4: assert(lastaddr == (&o_addr[4:0]));	// 128 bytes
	3'h5: assert(lastaddr == (&o_addr[5:0]));	// 256 bytes
	default: assert(lastaddr == (&o_addr[AW-2:0]));
	endcase

	always @(*)
	if (o_busy)
	case(r_lgblksz_m3)
	3'h0: assert(o_addr[AW-2:1] == 0);	//   8 bytes
	3'h1: assert(o_addr[AW-2:2] == 0);	//  16 bytes
	3'h2: assert(o_addr[AW-2:3] == 0);	//  32 bytes
	3'h3: assert(o_addr[AW-2:4] == 0);	//  64 bytes
	3'h4: assert(o_addr[AW-2:5] == 0);	// 128 bytes
	3'h5: assert(o_addr[AW-2:6] == 0);	// 256 bytes
	default: begin end // assert(lastaddr == (&o_addr[AW-2:0]));
	endcase

	always @(*)
	if (fill != 0)
	begin
		assert(fill[0]);
		if (!fill[1])
			assert(fill[2] == 0);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CRC checks and properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		assert(crc_fill <= 4);

	always @(*)
	if (o_busy && !received_token)
	begin
		assert(!crc_active);
		assert(crc_fill == 0);
		assert(crc_data == 0);
	end

	always @(*)
	if (crc_active)
	begin
		if (crc_data == 0 && crc_gearbox[7:6] == 0)
			assert(next_crc_data == 0);

		if ((crc_data[15] ^ crc_gearbox[7])
			&&((crc_data[14] ^ crc_gearbox[6])==0))
			assert(next_crc_data == ({ crc_data[13:0], 2'b00 } ^ { CRC_POLYNOMIAL[14:0], 1'b0 }));

		if (((crc_data[15] ^ crc_gearbox[7])==0)
			&&(crc_data[14] ^ crc_gearbox[6]))
			assert(next_crc_data == ({ crc_data[13:0], 2'b00 } ^ CRC_POLYNOMIAL[14:0]));
	end


/*
	reg	[5:0]		f_read_seq;
	(* anyseq *) reg	f_read_check;
	reg	[DW-1:0]	f_read_data;

	always @(posedge i_clk)
	if (rdvalid[RDDELAY-1])
		f_read_data <= i_data;

	always @(*)
	if (f_read_seq != 0)
		assume(!f_read_check);

	initial	f_read_seq = 0;
	always @(posedge i_clk)
	if (!o_busy)
		f_read_seq <= 0;
	else if (f_read_check && o_read)
		f_read_seq <= 1;
	else if (rdvalid != 0)
	begin
		if (rdvalid[RDDELAY-1])
			f_read_seq <= 2;
	end else if (!i_ll_busy)
		f_read_seq <= (f_read_seq << 1);

	always @(*)
	if (i_reset || !o_busy || (f_read_seq == 0))
	begin end
	else case(f_read_seq)
	6'h01: begin
		assert(rdvalid != 0);
		assert(fill == 5'h10);
		end
	6'h02: begin
		assert(rdvalid == 0);
		assert(fill == 5'h1f);
		assert(gearbox[DW-1:0] == f_read_data);
		end
	6'h04: begin
		assert(rdvalid == 0);
		assert(fill == 5'h1e);
		assert(gearbox[8+DW-1:8] == f_read_data);
		end
	6'h08: begin
		assert(rdvalid == 0);
		assert(fill == 5'h1c);
		assert(gearbox[8+DW-1:16] == f_read_data[23:0]);
		end
	6'h10: begin
		assert(rdvalid == 0);
		assert(fill == 5'h18);
		assert(gearbox[8+DW-1:24] == f_read_data[15:0]);
		end
	6'h20: begin
		assert(fill[4]);
		assert(gearbox[8+DW-1:DW] == f_read_data[7:0]);
		end
	default: assert($onehot0(f_read_seq));
	endcase
*/
	// }}}
`ifdef	SPIRXDATA
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	reg	cvr_packet_received;

	always @(*)
	if (!received_token)
	begin
		cover(error_token);
		cover(start_token);
	end

	initial	cvr_packet_received = 0;
	always @(posedge i_clk)
	if (i_reset || error_token)
		cvr_packet_received <= 0;
	else if (o_rxvalid)
		cvr_packet_received <= 1;

	always @(posedge i_clk)
	begin
		cover(o_rxvalid);
		cover(o_rxvalid && all_mem_written);
		cover(o_rxvalid && f_lgblksz == 4 && all_mem_written);
		cover(o_rxvalid && f_lgblksz == 4 && o_response == 0);
		cover(o_rxvalid && f_lgblksz == 4 && o_response == 0 && all_mem_written);

		cover(o_busy && f_lgblksz == 4 && o_addr == 8'h01);
		cover(o_busy && f_lgblksz == 4 && o_addr == 8'h02);
		cover(o_busy && f_lgblksz == 4 && o_addr == 8'h03);
		cover(o_busy && crc_byte == 0);
		cover(o_busy && crc_byte == 1);
		cover(o_busy && crc_byte == 2);
		cover(o_busy && crc_byte == 1 && i_ll_stb);
		cover(o_busy && crc_byte == 2 && i_ll_stb);

		cover(cvr_packet_received && !o_busy);
	end
	// }}}
`endif	// SPIRXDATA
`endif	// FORMAL
// }}}
endmodule
