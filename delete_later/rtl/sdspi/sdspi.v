////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sdspi.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	SD Card controller, using SPI interface with the card and
//		WB interface with the rest of the system.  This is the top
//	level of the SPI based controller.
//
//	See the specification for more information.
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
// License:	GPL, v3, as defined and found on www.gnu.org,
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
module	sdspi #(
		// {{{
		parameter [0:0]	OPT_CARD_DETECT = 1'b1,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		//
		// LGFIFOLN
		// {{{
		// LGFIFOLN defines the size of the internal memory in words.
		// An LGFIFOLN of 7 is appropriate for a 2^(7+2)=512 byte FIFO
		parameter			LGFIFOLN = 7,
		// }}}
		parameter			POWERUP_IDLE = 1000,
		// STARTUP_CLOCKS
		// {{{
		// Many SD-Cards require a minimum number of SPI clocks to get
		// them started.  STARTUP_CLOCKS defines this number.  Set this
		// to zero if you don't want to use this initialization
		// sequence.
		parameter			STARTUP_CLOCKS = 75,
		// }}}
		// CKDIV_BITS
		// {{{
		// For my first design, using an 80MHz clock, 7 bits to the
		// clock divider was plenty.  Now that I'm starting to use
		// faster and faster designs, it becomes important to
		// parameterize the number of bits in the clock divider.  More
		// than 8, however, and the interface will need to change.
		parameter			CKDIV_BITS = 8,
		// }}}
		// INITIAL_CLKDIV
		// {{{
		// The SPI frequency is given by the system clock frequency
		// divided by a (clock_divider + 1).  INITIAL_CLKDIV provides
		// an initial value for this clock divider.
		parameter [CKDIV_BITS-1:0]	INITIAL_CLKDIV = 8'h7c,
		// }}}
		// OPT_SPI_ARBITRATION
		// {{{
		// When I originally built this SDSPI controller, it was for an
		// environment where the SPI was shared.  Doing this requires
		// feedback from an arbiter, to know when one SPI device has
		// the bus or not.  This feedback is provided in i_bus_grant.
		// If you don't have an arbiter, just set i_bus_grant to the
		// constant 1'b1 and set OPT_SPI_ARBITRATION to 1'b0 to remove
		// this extra logic.
		parameter [0:0]			OPT_SPI_ARBITRATION = 1'b0,
		// }}}
		//
		//
		parameter [0:0]		OPT_EXTRA_WB_CLOCK = 1'b0,
		//
		//
		//
		localparam	AW = 2, DW = 32
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_sd_reset,
		// Wishbone interface
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire [AW-1:0]	i_wb_addr,
		input	wire [DW-1:0]	i_wb_data,
		input	wire [DW/8-1:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg [DW-1:0]	o_wb_data,
		// }}}
		// SDCard interface
		// {{{
		output	wire		o_cs_n, o_sck, o_mosi,
		input	wire		i_miso, i_card_detect,
		// }}}
		// Our interrupt
		output	reg		o_int,
		// .. and whether or not we can use the SPI port
		input	wire		i_bus_grant,
		// And some wires for debugging it all
		//
		output	reg [DW-1:0]	o_debug
		// }}}
	);

	// Signal / parameter declarations
	// {{{
	localparam [1:0]	SDSPI_CMD_ADDRESS = 2'b00,
				SDSPI_DAT_ADDRESS = 2'b01,
				SDSPI_FIFO_A_ADDR = 2'b10,
				SDSPI_FIFO_B_ADDR = 2'b11;

	localparam	BLKBASE = 16;

	//
	// Command register bit definitions
	//
	localparam	CARD_REMOVED_BIT= 18,
			// CRCERR_BIT	= 16,
			ERR_BIT		= 15,
			FIFO_ID_BIT	= 12,
			USE_FIFO_BIT	= 11,
			FIFO_WRITE_BIT	= 10;
	//
	// Some WB simplifications:
	//
	reg		r_cmd_busy;

	reg			dbg_trigger;

	wire		wb_stb, write_stb, wb_cmd_stb, new_data;
	wire	[AW-1:0]	wb_addr;
	wire	[DW-1:0]	wb_data;
	wire	[3:0]		wb_sel;
	reg	[1:0]	pipe_addr;
	reg		dly_stb;

	reg	[31:0]	fifo_a	[0:((1<<LGFIFOLN)-1)];
	reg	[31:0]	fifo_b	[0:((1<<LGFIFOLN)-1)];
	reg	[(LGFIFOLN-1):0]	fifo_wb_addr;
	reg	[(LGFIFOLN-1):0]	write_fifo_a_addr, write_fifo_b_addr,
					read_fifo_a_addr, read_fifo_b_addr;
	wire	[LGFIFOLN:0]	spi_read_addr, spi_write_addr;
	// reg	[3:0]		write_fifo_a_mask, write_fifo_b_mask;
	reg	[31:0]		write_fifo_a_data, write_fifo_b_data,
				fifo_a_word, fifo_b_word, spi_read_data;
	wire	[31:0]		spi_write_data;
	reg			write_fifo_a, write_fifo_b;
	reg	[31:0]		r_data_reg;
	reg			r_cmd_err;
	reg	[7:0]		r_last_r_one;

	//
	//
	wire		card_removed, card_present;
	//
	reg	[3:0]	r_lgblklen;
	wire	[3:0]	max_lgblklen;
	reg	[25:0]	r_watchdog;
	reg		r_watchdog_err;

	reg	[DW-1:0]	card_status;
	wire		ll_advance;

	reg	[CKDIV_BITS-1:0]	r_sdspi_clk;
	reg		ll_cmd_stb;
	reg	[7:0]	ll_cmd_dat;
	wire		ll_out_stb, ll_idle;
	wire	[7:0]	ll_out_dat;

	reg		r_fifo_id, r_use_fifo, write_to_card;

	wire	w_reset;

	wire		cmd_out_stb;
	wire	[7:0]	cmd_out_byte;
	wire		cmd_sent, cmd_valid, cmd_busy;
	wire	[39:0]	cmd_response;

	reg		rx_start;
	wire		spi_write_to_fifo;
	wire		rx_valid, rx_busy;
	wire	[7:0]	rx_response;

	reg		tx_start;
	wire		spi_read_from_fifo;
	wire		tx_stb;
	wire	[7:0]	tx_byte;
	wire		tx_valid, tx_busy;
	wire	[7:0]	tx_response;

	reg	last_busy;


	// }}}

	// Take an extra wishbone clock?
	// {{{
	generate if (!OPT_EXTRA_WB_CLOCK)
	begin : EXTRA_WB_PASSTHROUGH
		// {{{
		assign	wb_stb    = ((i_wb_stb)&&(!o_wb_stall));
		assign	write_stb = ((wb_stb)&&( i_wb_we) && i_wb_sel != 0);
		// assign	read_stb  = ((wb_stb)&&(!i_wb_we));
		assign	wb_sel = i_wb_sel;
		assign	wb_cmd_stb  = (!r_cmd_busy)&& write_stb && (&i_wb_sel)
				&&(i_wb_addr==SDSPI_CMD_ADDRESS);
		assign	wb_addr = i_wb_addr;
		assign	wb_data = i_wb_data;
		assign	new_data = (i_wb_stb)&&(!o_wb_stall)
				&&(i_wb_we && i_wb_sel != 0)
				&&(i_wb_addr == SDSPI_DAT_ADDRESS);
		// }}}
	end else begin : GEN_EXTRA_WB_CLOCK
		// {{{
		reg		r_wb_stb, r_write_stb, r_wb_cmd_stb, r_new_data;
		reg	[AW-1:0]	r_wb_addr;
		reg	[DW-1:0]	r_wb_data;
		reg	[DW/8-1:0]	r_wb_sel;

		initial	r_wb_stb = 1'b0;
		always @(posedge i_clk)
			r_wb_stb <= ((i_wb_stb)&&(!o_wb_stall));

		initial	r_write_stb = 1'b0;
		always @(posedge i_clk)
			r_write_stb <= ((i_wb_stb)&&(!o_wb_stall)&&(i_wb_we && i_wb_sel != 0));

		initial	r_wb_sel = 1'b0;
		always @(posedge i_clk)
			r_wb_sel <= i_wb_sel;

		initial	r_wb_cmd_stb = 1'b0;
		always @(posedge i_clk)
			r_wb_cmd_stb <= (!r_cmd_busy)&&(i_wb_stb)&&(!o_wb_stall)&&(i_wb_we && i_wb_sel != 0)
					&&(i_wb_addr == SDSPI_CMD_ADDRESS);

		always @(posedge i_clk)
			r_new_data <= (i_wb_stb)&&(!o_wb_stall)
					&&(i_wb_we && i_wb_sel != 0)
					&&(i_wb_addr == SDSPI_DAT_ADDRESS);

		always @(posedge i_clk)
			r_wb_addr <= i_wb_addr;

		always @(posedge i_clk)
			r_wb_data <= i_wb_data;

		assign	wb_stb   = r_wb_stb;
		assign	write_stb= r_write_stb;
		assign	wb_cmd_stb  = r_wb_cmd_stb;
		assign	new_data = r_new_data;
		assign	wb_addr  = r_wb_addr;
		assign	wb_data  = r_wb_data;
		assign	wb_sel   = r_wb_sel;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Lower-level SDSPI driver
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Access to our lower-level SDSPI driver, the one that actually
	// uses/sets the SPI ports
	//

	llsdspi #(
		// {{{
		.SPDBITS(CKDIV_BITS),
		.STARTUP_CLOCKS(STARTUP_CLOCKS),
		.POWERUP_IDLE(POWERUP_IDLE),
		.OPT_SPI_ARBITRATION(OPT_SPI_ARBITRATION)
		// }}}
	) lowlevel(
		// {{{
		i_clk, i_sd_reset, r_sdspi_clk, r_cmd_busy, ll_cmd_stb,
		ll_cmd_dat, o_cs_n, o_sck, o_mosi, i_miso,
		ll_out_stb, ll_out_dat, ll_idle,
		i_bus_grant
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Command controller
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	w_reset = i_sd_reset || r_watchdog_err;

	spicmd
	spicmdi(
		// {{{
		i_clk, w_reset, (wb_cmd_stb && wb_data[7:6] == 2'b01),
			wb_data[9:8], wb_data[5:0], r_data_reg, cmd_busy,
		cmd_out_stb, cmd_out_byte, !ll_advance,
		ll_out_stb, ll_out_dat,
		cmd_sent,
		cmd_valid, cmd_response
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Receive data (not commands)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	spirxdata #(
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN)
	) spirxdatai(
		// {{{
		i_clk, w_reset | r_cmd_err, rx_start,
			r_lgblklen, r_fifo_id, rx_busy,
		ll_out_stb && !cmd_busy, ll_out_dat,
		spi_write_to_fifo, spi_write_addr, spi_write_data,
		rx_valid, rx_response
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Transmit/send data (not commands) to the SD card
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	spitxdata #(
		.RDDELAY(2),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN)
	) spitxdatai(
		// {{{
		i_clk, w_reset | r_cmd_err, tx_start,
			r_lgblklen, r_fifo_id, tx_busy,
		spi_read_from_fifo, spi_read_addr, spi_read_data,
		!ll_advance || cmd_busy, tx_stb, tx_byte,
		ll_out_stb && !cmd_busy, ll_out_dat,
		tx_valid, tx_response
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal FIFO memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Let's work with our FIFO memory here ...
	//
	always @(posedge i_clk)
	begin
		if ((write_stb)&&(wb_addr == SDSPI_CMD_ADDRESS))
		begin // Command write
			// Clear the read/write address
			fifo_wb_addr <= {(LGFIFOLN){1'b0}};
		end else if ((wb_stb)&&(wb_addr[1] && wb_sel != 0))
		begin // On read or write, of either FIFO,
			// we increase our pointer
			// if (wb_sel[0])
				fifo_wb_addr <= fifo_wb_addr + 1;
			// And let ourselves know we need to update ourselves
			// on the next clock
		end
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Writes to the FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	write_fifo_a = 0;
	always @(posedge i_clk)
	if (r_use_fifo && rx_busy && !spi_write_addr[LGFIFOLN])
	begin
		write_fifo_a      <= spi_write_to_fifo;
		write_fifo_a_data <= spi_write_data;
		write_fifo_a_addr <= spi_write_addr[LGFIFOLN-1:0];
		// write_fifo_a_mask <= 4'hf;
	end else begin
		write_fifo_a      <= write_stb &&(wb_addr == SDSPI_FIFO_A_ADDR) &&(&wb_sel);
		write_fifo_a_data <= wb_data;
		write_fifo_a_addr <= fifo_wb_addr;
		// write_fifo_a_mask <= 4'hf;
	end

	initial	write_fifo_b = 0;
	always @(posedge i_clk)
	if (r_use_fifo && rx_busy && spi_write_addr[LGFIFOLN])
	begin
		write_fifo_b      <= spi_write_to_fifo;
		write_fifo_b_data <= spi_write_data;
		write_fifo_b_addr <= spi_write_addr[LGFIFOLN-1:0];
		// write_fifo_b_mask <= 4'hf;
	end else begin
		write_fifo_b      <= write_stb &&(wb_addr == SDSPI_FIFO_B_ADDR) && (&wb_sel);
		write_fifo_b_data <= wb_data;
		write_fifo_b_addr <= fifo_wb_addr;
		// write_fifo_b_mask <= 4'hf;
	end

	always @(posedge i_clk)
	if (write_fifo_a)
		fifo_a[write_fifo_a_addr] <= write_fifo_a_data;

	always @(posedge i_clk)
	if (write_fifo_b)
		fifo_b[write_fifo_b_addr] <= write_fifo_b_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reads from the FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (r_use_fifo && tx_busy && !spi_read_addr[LGFIFOLN])
		read_fifo_a_addr = spi_read_addr[LGFIFOLN-1:0];
	else
		read_fifo_a_addr = fifo_wb_addr;

	always @(*)
	if (r_use_fifo && tx_busy && spi_read_addr[LGFIFOLN])
		read_fifo_b_addr = spi_read_addr[LGFIFOLN-1:0];
	else
		read_fifo_b_addr = fifo_wb_addr;

	always @(posedge i_clk)
		fifo_a_word <= fifo_a[read_fifo_a_addr];

	always @(posedge i_clk)
		fifo_b_word <= fifo_b[read_fifo_b_addr];

	always @(posedge i_clk)
	if (!spi_read_addr[LGFIFOLN])
		spi_read_data <= fifo_a_word;
	else
		spi_read_data <= fifo_b_word;

	initial	r_fifo_id = 0;
	always @(posedge i_clk)
	if (!r_cmd_busy && wb_cmd_stb)
		r_fifo_id  <= wb_data[FIFO_ID_BIT];
	// }}}
	// }}}
	// r_cmd_busy, tx_start, rx_start, r_use_fifo, write_to_card
	// {{{
	initial	r_cmd_busy = 0;
	initial	tx_start = 0;
	initial	rx_start = 0;
	always @(posedge i_clk)
	if (i_sd_reset)
	begin
		// {{{
		r_cmd_busy <= 0;
		r_use_fifo <= 0;
		tx_start <= 0;
		rx_start <= 0;
		// }}}
	end else if (!r_cmd_busy)
	begin
		// {{{
		r_cmd_busy <= wb_cmd_stb && (wb_data[7:6] == 2'b01);
		tx_start <= 0;
		rx_start <= 0;
		if (wb_cmd_stb && wb_data[7:6] == 2'b01)
		begin
			write_to_card <= wb_data[FIFO_WRITE_BIT];
			r_use_fifo <= wb_data[USE_FIFO_BIT];
			if (wb_data[USE_FIFO_BIT])
			begin
				tx_start   <= (wb_data[FIFO_WRITE_BIT]);
				rx_start   <= (!wb_data[FIFO_WRITE_BIT]);
			end
		end
		if (r_watchdog_err)
		begin
			r_use_fifo <= 0;
			tx_start <= 0;
			rx_start <= 0;
		end
		// }}}
	end else begin
		// {{{
		if (ll_idle && !ll_cmd_stb && !cmd_busy && !rx_busy && !tx_busy)
		begin
			r_cmd_busy <= 0;
			r_use_fifo <= 0;
		end

		if (r_cmd_err || tx_busy || rx_busy)
		begin
			tx_start <= 0;
			rx_start <= 0;
		end

		if (r_watchdog_err)
		begin
			r_use_fifo <= 0;
			tx_start <= 0;
			rx_start <= 0;
		end
		// }}}
	end
	// }}}

	// r_cmd_err
	// {{{
	initial	r_cmd_err = 0;
	always @(posedge i_clk)
	if (r_watchdog_err)
		r_cmd_err <= 1;
	else if (r_cmd_busy)
	begin
		//
		// A command error is a watchdog error, so nothing needed here
		//
		// if (cmd_valid) r_cmd_err <= |cmd_response[38:33];
		//
		// A transmit error can be discovered as a response to a
		// command
		//
		// if (tx_valid)  r_cmd_err <= 0;
		//
		// However, we can check read response tokens for errors
		if (cmd_valid)
			r_cmd_err <= r_cmd_err || (cmd_response[38:33] != 0);
		if (rx_valid)
			r_cmd_err <= r_cmd_err || rx_response[3];
	end else if (wb_cmd_stb)
		r_cmd_err <= (r_cmd_err)&&(!wb_data[ERR_BIT]);
	// }}}

	// r_data_reg
	// {{{
	always @(posedge i_clk)
	if (!r_cmd_busy)
	begin
		if (new_data)
			r_data_reg <= wb_data;
		else if (wb_cmd_stb && wb_data[7])
			r_data_reg <= {
				4'h0, max_lgblklen,
				1'b0, // Rsrved for: Read data from CMD wire
				3'h0, r_lgblklen,
				{(16-CKDIV_BITS){1'b0}},
				r_sdspi_clk };
	end else begin
		if (cmd_valid)
		begin
			r_data_reg   <= cmd_response[31:0];
			r_last_r_one <= cmd_response[39:32];
		end else if (tx_valid)
			r_data_reg   <= { 24'h0, tx_response[7:0] };
		else if (rx_valid)
			r_data_reg   <= { 24'h0, rx_response[7:0] };
	end
	// }}}

	assign	ll_advance = (!ll_cmd_stb || ll_idle);

	// ll_cmd_stb, ll_cmd_dat
	// {{{
	initial	ll_cmd_stb = 0;
	always @(posedge i_clk)
	begin
		if (ll_advance)
		begin
			if (cmd_busy)
			begin
				ll_cmd_stb <= (ll_cmd_stb || cmd_out_stb);
				ll_cmd_dat <= cmd_out_stb ? cmd_out_byte :8'hff;
			end else begin
				ll_cmd_stb <= (ll_cmd_stb || tx_stb);
				ll_cmd_dat <= tx_stb ? tx_byte : 8'hff;
			end
		end

		if (ll_idle && !cmd_busy && !rx_busy && !tx_busy)
			ll_cmd_stb <= 1'b0;

		if (!r_cmd_busy || i_sd_reset)
			ll_cmd_stb <= 1'b0;
	end
	// }}}

	assign	max_lgblklen = LGFIFOLN+2;

	// r_sdspi_clk, r_lgblklen
	// {{{
	initial	r_sdspi_clk = INITIAL_CLKDIV;
	initial	r_lgblklen = 9;
	always @(posedge i_clk)
	begin
		// Update our internal configuration parameters, unconnected
		// with the card.  These include the speed of the interface,
		// and the size of the block length to expect as part of a FIFO
		// command.
		if ((wb_cmd_stb)&&(wb_data[7:6]==2'b11))
			// &&(!r_data_reg[7])
			// &&(r_data_reg[15:12]==4'h00))
		begin
			if (r_data_reg[CKDIV_BITS-1:0] != 0)
				r_sdspi_clk <= r_data_reg[CKDIV_BITS-1:0];
			if ((r_data_reg[BLKBASE +: 4] >= 3)
				&&(r_data_reg[BLKBASE +: 4] <= max_lgblklen))
				r_lgblklen <= r_data_reg[BLKBASE +: 4];
		end
		// if (r_lgblklen > max_lgblklen)
		//	r_lgblklen <= max_lgblklen;

		if (!card_present)
			r_sdspi_clk <= INITIAL_CLKDIV;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone return logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
		pipe_addr <= wb_addr;

	always @(*)
		card_status = { 8'h00,		// 8b
			2'b0, r_watchdog_err, i_sd_reset,	// 4b
			!card_present, card_removed, 1'b0, 1'b0,
			r_cmd_err, r_cmd_busy, 1'b0, r_fifo_id,	// 4b
			r_use_fifo, write_to_card, 2'b00,	// 4b
			r_last_r_one };	// 8b

	always @(posedge i_clk)
	case(pipe_addr)
	SDSPI_CMD_ADDRESS:
		o_wb_data <= card_status;
	SDSPI_DAT_ADDRESS:
		o_wb_data <= r_data_reg;
	SDSPI_FIFO_A_ADDR:
		o_wb_data <= fifo_a_word;
	SDSPI_FIFO_B_ADDR:
		o_wb_data <= fifo_b_word;
	endcase

	initial	dly_stb = 0;
	always @(posedge i_clk)
	if (!i_wb_cyc)
		dly_stb <= 0;
	else
		dly_stb <= wb_stb;

	initial	o_wb_ack = 0;
	always @(posedge i_clk)
	if (!i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= dly_stb;

	assign	o_wb_stall = 1'b0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Interrupt generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	initial	last_busy = 0;
	always @(posedge i_clk)
		last_busy <= r_cmd_busy;

	initial	o_int = 0;
	always @(posedge i_clk)
		o_int <= (!r_cmd_busy)&&(last_busy)
			||(!card_removed && !card_present);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Card detection logic --- is the card even present?
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Depends upon the i_card_detect signal.  Set this signal to 1'b1 if
	// you your device doesn't have it.
	//
	//
	generate if (OPT_CARD_DETECT)
	begin : GEN_CARD_DETECT
		reg	[2:0]	raw_card_present;
		reg	[9:0]	card_detect_counter;
		reg		r_card_removed, r_card_present;

		initial	r_card_removed = 1'b1;
		always @(posedge i_clk)
		if (i_sd_reset)
			r_card_removed <= 1'b1;
		else if (!card_present)
			r_card_removed <= 1'b1;
		else if (wb_cmd_stb && wb_data[CARD_REMOVED_BIT])
			r_card_removed <= 1'b0;

		initial	raw_card_present = 0;
		always @(posedge i_clk)
			raw_card_present <= { raw_card_present[1:0], i_card_detect };

		initial	card_detect_counter = 0;
		always @(posedge i_clk)
		if (i_sd_reset || !raw_card_present[2])
			card_detect_counter <= 0;
		else if (!(&card_detect_counter))
			card_detect_counter <= card_detect_counter + 1;

		initial r_card_present = 1'b0;
		always @(posedge i_clk)
		if (i_sd_reset || !raw_card_present[2])
			r_card_present <= 1'b0;
		else if (&card_detect_counter)
			r_card_present <= 1'b1;

		assign	card_present = r_card_present;
		assign	card_removed = r_card_removed;

	end else begin : NO_CARD_DETECT_SIGNAL

		assign	card_present = 1'b1;
		assign	card_removed = 1'b0;

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog protection logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Some watchdog logic for us.  This way, if we are waiting for the
	// card to respond, and something goes wrong, we can timeout the
	// transaction and ... figure out what to do about it later.  At least
	// we'll have an error indication.
	//
	initial	r_watchdog_err = 1'b0;
	always @(posedge i_clk)
	if (!r_cmd_busy)
		r_watchdog_err <= 1'b0;
	else if (r_watchdog == 0)
		r_watchdog_err <= 1'b1;

	initial	r_watchdog = 26'h3ffffff;
	always @(posedge i_clk)
	if (!r_cmd_busy)
		r_watchdog <= 26'h3fffff;
	else if (|r_watchdog)
		r_watchdog <= r_watchdog - 26'h1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug signals
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	dbg_trigger = 0;
	always @(posedge i_clk)
		dbg_trigger <= (cmd_valid)&&(cmd_response[38:33] != 0);

	always @(posedge i_clk)
		o_debug <= { dbg_trigger, ll_cmd_stb,
				(ll_cmd_stb & ll_idle), ll_out_stb, // 4'h
			o_cs_n, o_sck, o_mosi, i_miso, 	// 4'h
			3'b000, i_sd_reset,	// 4'h
			3'b000, r_cmd_busy,	// 4'h
			ll_cmd_dat,		// 8'b
			ll_out_dat };		// 8'b
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_sel, cmd_sent,
			spi_read_from_fifo };
	// verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal verification properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = 3;
	wire	[F_LGDEPTH-1:0]	f_nacks, f_nreqs, f_outstanding;
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone Bus properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	fwb_slave #(
		.AW(2), .DW(32),
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_STALL(1),
		.F_MAX_ACK_DELAY(2),
		.F_OPT_DISCONTINUOUS(1),
		.F_OPT_MINCLOCK_DELAY(1)
	) fwb(
		.i_clk(i_clk), .i_reset(!f_past_valid),
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb), .i_wb_we(i_wb_we),
		.i_wb_addr(i_wb_addr),.i_wb_data(i_wb_data),.i_wb_sel(i_wb_sel),
			.i_wb_stall(o_wb_stall), .i_wb_ack(o_wb_ack),
			.i_wb_idata(o_wb_data), .i_wb_err(1'b0),
		.f_nreqs(f_nreqs), .f_nacks(f_nacks),
		.f_outstanding(f_outstanding)
	);

	always @(*)
	if (i_wb_cyc)
		assert(f_outstanding == (o_wb_ack ? 1:0) + (dly_stb ? 1:0)
			+ (OPT_EXTRA_WB_CLOCK ? wb_stb : 0));

	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		assert(!tx_busy || !rx_busy);

	always @(*)
		assert(!tx_start || !rx_start);

	always @(*)
	if (!r_use_fifo)
	begin
		assert(!tx_start && !rx_start);
		assert(!tx_busy && !rx_busy);
		if(!write_to_card)
			assert(!rx_start && !rx_busy);
		else
			assert(!tx_start && !tx_busy);
	end

	always @(*)
	if (tx_busy || rx_busy || cmd_busy)
		assert(r_cmd_busy);

	always @(*)
	begin
		assert(r_lgblklen >= 3);
		assert(r_lgblklen <= 9);
	end

	always @(*)
	if (cmd_busy)
	begin
		assert(spi_read_addr[LGFIFOLN-1:0] <= 1);
		assert(spi_write_addr[LGFIFOLN-1:0] <= 1);
	end

	//
	// Command sequence check
	(* anyseq *)	reg	f_cmd_check_value;
	reg	[1:0]	f_cmd_seq;
	reg	[7:0]	f_cmd_byte;
`ifdef	VERIFIC
	always @(posedge i_clk)
	if (f_cmd_check_value && f_cmd_seq == 0 && cmd_out_stb && !spicmdi.i_ll_busy)
		f_cmd_byte <= cmd_out_byte;

	initial	f_cmd_seq = 0;
	always @(posedge i_clk)
	if (i_sd_reset || r_watchdog_err)
		f_cmd_seq <= 0;
	else if (f_cmd_check_value && f_cmd_seq == 0 && cmd_out_stb && !spicmdi.i_ll_busy)
		f_cmd_seq <= 1;
	else if (!ll_cmd_stb || ll_idle)
		f_cmd_seq <= f_cmd_seq << 1;

	always @(*)
	if (!i_sd_reset && !r_watchdog_err) case(f_cmd_seq)
	0: begin end
	1: begin
		assert(ll_cmd_stb);
		assert(ll_cmd_dat == f_cmd_byte);
		end
	2: begin
		end
	endcase
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// Abstract LLSDSPI properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
//`ifdef	ABSTRACT_LLSDSPI
//`define	LLSDSPI_ASSERT	assume
//`else
//`define	LLSDSPI_ASSERT	assert
//`endif
//	reg	f_first_byte_accepted;
//
//	always @(posedge i_clk)
//	if (!f_past_valid)
//		`LLSDSPI_ASSERT(!ll_out_stb);
//	else if (!$past(r_cmd_busy))
//		`LLSDSPI_ASSERT(!ll_out_stb);
//	else if ($past(ll_out_stb))
//		`LLSDSPI_ASSERT(!ll_out_stb);
//
//	always @(posedge i_clk)
//	if (!r_cmd_busy)
//		f_first_byte_accepted <= 1'b0;
//	else if (ll_cmd_stb && ll_idle)
//		f_first_byte_accepted <= 1'b1;
//
//	always @(posedge i_clk)
//	if (f_past_valid && $past(f_past_valid))
//	begin
//		if ($rose(r_cmd_busy))
//		begin
//			assert($rose(ll_cmd_stb));
//			`LLSDSPI_ASSERT(!ll_out_stb);
//		end else if (r_cmd_busy && f_first_byte_accepted && $past(f_first_byte_accepted))
//			`LLSDSPI_ASSERT(ll_out_stb == $past(ll_idle));
//	end
//
//	always @(posedge i_clk)
//	if (f_past_valid)
//	begin
//		if ($past(i_sd_reset || r_watchdog_err))
//			assert(!r_cmd_busy);
//		else if ($past(r_cmd_busy && ll_out_stb && !ll_idle))
//		begin
//			assert(ll_out_stb);
//			assert($stable(ll_out_dat));
//		end
//	end

	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (f_past_valid && $past(r_watchdog_err))
		assert(!cmd_busy && !tx_busy && !rx_busy);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	begin
		cover(cmd_sent && !r_cmd_busy);
		cover(tx_busy  && tx_start);
		cover(rx_busy  && rx_start);
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_sd_reset) && !$past(r_watchdog_err))
	begin
		cover($fell(cmd_busy));
		cover($fell(tx_busy));
		cover($fell(rx_busy));
		cover($fell(r_cmd_busy));
	end

	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// always @(*)
	//	assume(!r_watchdog_err);
`endif
// }}}
endmodule
