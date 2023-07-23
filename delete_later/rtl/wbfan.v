////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbfan
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	Controls the FPGA and case fan speeds.
//
// Registers:
//	0:	Current FPGA fan PWM
//	1:	Current System fan PWM
//	2:	Measured FAN speed
//	3:	Measured temperature, twos-complement, in quarter degrees
//			centigrade.  Multiply by 36/5 and add 128 to get
//			Fahrenheit.
//	4:	Temperature I2C control, bypass to temp I2CCPU
//	5:	Temperature I2C Override
//	6:	Temperature I2C address	-- only points to local (fixed) mem
//	7:	Temperature I2C ckcount
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
module	wbfan (
		// {{{
		input	wire	i_clk, i_reset,
		//
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[2:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		//
		input	wire		i_temp_sda, i_temp_scl,
		output	wire		o_temp_sda, o_temp_scl,
		//
		output	reg		o_fpga_pwm,
		output	reg		o_sys_pwm,
		input	wire		i_fan_tach,
		//
		output	wire	[31:0]	temp_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	CK_PER_SECOND = 100_000_000,
			CK_PER_MS = (CK_PER_SECOND / 1000),
			PWM_HZ = 20_000;
	localparam	MAX_PWM = (CK_PER_SECOND / PWM_HZ)-1;
	localparam	LGPWM = $clog2(MAX_PWM+1);
	reg	[LGPWM-1:0]	pwm_counter;
	reg [LGPWM-1:0]	ctl_fpga, ctl_sys;

	reg		ck_tach, last_tach;
	reg	[1:0]	pipe_tach;
	reg		tach_reset;
	reg	[$clog2(CK_PER_SECOND)-1:0]	tach_count, tach_counter,
			tach_timer;

	wire		i2c_wb_stall, i2c_wb_ack;
	wire	[31:0]	i2c_wb_data;

	wire		ign_mem_cyc, mem_stb, ign_mem_we, ign_mem_sel;
	wire	[4:0]	mem_addr;
	wire	[7:0]	ign_mem_data;
	reg	[7:0]	mem_data;
	reg		mem_ack;

	wire		i2cd_valid, i2cd_last, ign_i2cd_id;
	wire	[7:0]	i2cd_data;

	reg		pp_ms;
	reg	[$clog2(CK_PER_MS)-1:0]	trigger_counter;

	reg	[23:0]	temp_tmp;
	reg	[31:0]	temp_data;

	reg		pre_ack;
	reg	[31:0]	pre_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Fan control itself
	// {{{

	// ctl_fpga, ctl_sys
	// {{{
	initial	ctl_fpga = MAX_PWM[LGPWM-1:0];
	initial	ctl_sys  = MAX_PWM[LGPWM-1:0];
	always @(posedge i_clk)
	if (i_reset)
	begin
		ctl_fpga <= MAX_PWM[LGPWM-1:0];
		ctl_sys  <= MAX_PWM[LGPWM-1:0];
	end else if (i_wb_stb && i_wb_we && i_wb_addr[2] == 1'b0)
	begin
		case(i_wb_addr[1:0])
		2'b00: begin
			if (i_wb_sel[0]) ctl_fpga[ 7: 0] <= i_wb_data[ 7: 0];
			if (i_wb_sel[1]) ctl_fpga[LGPWM-1: 8] <= i_wb_data[LGPWM-1: 8];
			// if (i_wb_sel[2]) ctl_fpga[23:16] <= i_wb_data[23:16];
			// if (i_wb_sel[3]) ctl_fpga[31:24] <= i_wb_data[31:24];
			end
		2'b01: begin
			if (i_wb_sel[0]) ctl_sys[ 7: 0] <= i_wb_data[ 7: 0];
			if (i_wb_sel[1]) ctl_sys[LGPWM-1: 8] <= i_wb_data[LGPWM-1: 8];
			// if (i_wb_sel[2]) ctl_sys[23:16] <= i_wb_data[23:16];
			// if (i_wb_sel[3]) ctl_sys[31:24] <= i_wb_data[31:24];
			end
		default: begin end
		endcase
	end else begin
		if (ctl_fpga >= MAX_PWM[LGPWM-1:0])
			ctl_fpga <= MAX_PWM[LGPWM-1:0];
		if (ctl_sys >= MAX_PWM[LGPWM-1:0])
			ctl_sys <= MAX_PWM[LGPWM-1:0];
	end
	// }}}

	// pwm_counter
	// {{{
	always @(posedge i_clk)
	if (pwm_counter >= MAX_PWM[LGPWM-1:0])
		pwm_counter <= 0;
	else
		pwm_counter <= pwm_counter + 1;

	// }}}

	// o_*_pwm
	// {{{
	// Need a 20kHz proper PWM signal, with an adjustable duty cycle
	always @(posedge i_clk)
		o_fpga_pwm <=(ctl_fpga >= pwm_counter)||(ctl_fpga >= MAX_PWM[LGPWM-1:0]);
	always @(posedge i_clk)
		o_sys_pwm  <= (ctl_sys >= pwm_counter)|| (ctl_sys >= MAX_PWM[LGPWM-1:0]);
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Tachometer counter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//


	always @(posedge i_clk)
		{ last_tach, ck_tach, pipe_tach }
			<= { ck_tach, pipe_tach, i_fan_tach };

	always @(posedge i_clk)
	if (i_reset)
	begin
		tach_reset   <= 1;
		tach_counter <= 0;
		tach_count   <= 0;
		tach_timer   <= 0;
	end else if (tach_reset)
	begin
		tach_reset <= 1'b0;
		tach_timer <= CK_PER_SECOND[$clog2(CK_PER_SECOND)-1:0]-1;
		tach_count <= tach_counter;
		tach_counter <= (ck_tach && !last_tach) ? 1 : 0;
	end else begin
		tach_counter <= tach_counter + ((ck_tach && !last_tach) ? 1:0);

		tach_timer <= tach_timer - 1;
		tach_reset <= (tach_timer <= 1);
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// I2C Temperature reader: Address 7'b1001_000 and/or 7'b1001_001
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	always @(posedge i_clk)
	if (i_reset)
	begin
		pp_ms <= 1'b0;
		trigger_counter <= CK_PER_MS[$clog2(CK_PER_MS)-1:0]-1;
	end else if (trigger_counter == 0)
	begin
		pp_ms <= 1'b0;
		trigger_counter <= CK_PER_MS[$clog2(CK_PER_MS)-1:0]-1;
	end else begin
		pp_ms <= (trigger_counter <= 1);
		trigger_counter <= trigger_counter - 1;
	end

	// Our script
	// {{{
	// TARGET:
	//	CHANNEL	0
	//	ABORT
	//	WAIT
	//	START			// @ 4.1
	//	SEND	0x48,WR
	//	SEND	0x00		// Temperature address
	//	START
	//	SEND	0x48,RD
	//	RXK			// Read two bytes of temperature
	//	RXN
	//	STOP			// @B.1
	//	START			// @C.0
	//	SEND	0x49,WR
	//	SEND	0x00		// Temperature address
	//	START
	//	SEND	0x49,RD
	//	RXK			// Read two bytes of temperature
	//	RXLN
	//	STOP
	//	JUMP
	// Second start, if only TEMP1 is available
	// TARGET:
	//	ABORT
	//	WAIT
	//	START			// @C.0
	//	SEND	0x49,WR
	//	SEND	0x00		// Temperature address
	//	START
	//	SEND	0x49,RD
	//	RXK			// Read two bytes of temperature
	//	RXLN
	//	STOP
	//	JUMP
	//	HALT
	// }}}

	wbi2ccpu #(
		// {{{
		.ADDRESS_WIDTH(5),
		.DATA_WIDTH(8),
		.AXIS_ID_WIDTH(0),
		.OPT_START_HALTED(1'b0),
		.DEF_CKCOUNT(200)
		// }}}
	) u_i2ccpu (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb && i_wb_addr[2]),
		.i_wb_we(i_wb_we), .i_wb_addr(i_wb_addr[1:0]),
			.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
		.o_wb_stall(i2c_wb_stall), .o_wb_ack(i2c_wb_ack),
			.o_wb_data(i2c_wb_data),
		//
		.o_pf_cyc(ign_mem_cyc), .o_pf_stb(mem_stb),
			.o_pf_we(ign_mem_we), .o_pf_addr(mem_addr),
			.o_pf_data(ign_mem_data), .o_pf_sel(ign_mem_sel),
		.i_pf_stall(1'b0), .i_pf_ack(mem_ack), .i_pf_err(1'b0),
		.i_pf_data(mem_data),
		//
		.i_i2c_sda(i_temp_sda), .i_i2c_scl(i_temp_scl),
		.o_i2c_sda(o_temp_sda), .o_i2c_scl(o_temp_scl),
		//
		.M_AXIS_TVALID(i2cd_valid),
		.M_AXIS_TREADY(1'b1),
		.M_AXIS_TDATA(i2cd_data),
		.M_AXIS_TID(ign_i2cd_id),
		.M_AXIS_TLAST(i2cd_last),
		//
		.i_sync_signal(pp_ms),
		.o_debug(temp_debug)
		// }}}
	);

	always @(posedge i_clk)
		mem_ack <= !i_reset && mem_stb;

	// mem_addr
	// {{{
	always @(posedge i_clk)
	if (mem_stb)
	case(mem_addr)
	5'h00:	mem_data <= 8'hb0;	// TARGET
	5'h01:	mem_data <= 8'hd0;	// CHANNEL
	5'h02:	mem_data <= 8'h00;	//	#0
	5'h03:	mem_data <= 8'ha0;	// ABORT
	5'h04:	mem_data <= 8'h81;	// WAIT | START
	5'h05:	mem_data <= 8'h30;	// SEND
	5'h06:	mem_data <= 8'h90;	//	#90
	5'h07:	mem_data <= 8'h30;	// SEND
	5'd08:	mem_data <= 8'h00;	//	#00
	5'h09:	mem_data <= 8'h13;	// START | SEND
	5'h0a:	mem_data <= 8'h91;	//	#91
	5'h0b:	mem_data <= 8'h45;	// RXK | RXN
	5'h0c:	mem_data <= 8'h21;	// STOP | START
	5'h0d:	mem_data <= 8'h30;	// SEND
	5'h0e:	mem_data <= 8'h92;	//	#92
	5'h0f:	mem_data <= 8'h30;	// SEND
	5'h10:	mem_data <= 8'h00;	//	#00
	5'h11:	mem_data <= 8'h13;	// START | SEND
	5'h12:	mem_data <= 8'h93;	//	#93
	5'h13:	mem_data <= 8'h47;	// RXK  | RXLN
	5'h14:	mem_data <= 8'h2c;	// STOP | JUMP
	// Sensor #1 only (skip sensor #0)
	5'h15:	mem_data <= 8'hb0;	// TARGET
	5'h16:	mem_data <= 8'ha0;	// ABORT
	5'h17:	mem_data <= 8'h81;	// WAIT | START
	5'h18:	mem_data <= 8'h30;	// SEND 0x49,WR
	5'h19:	mem_data <= 8'h92;	//	#92
	5'h1a:	mem_data <= 8'h30;	// SEND 0x00
	5'h1b:	mem_data <= 8'h00;	//
	5'h1c:	mem_data <= 8'h13;	// START | SEND 0x49,RD
	5'h1d:	mem_data <= 8'h93;	//	#93
	5'h1e:	mem_data <= 8'h47;	// RXK  | RXLN
	5'h1f:	mem_data <= 8'h2c;	// STOP | JUMP
	// default: mem_data <= 8'h99;
	endcase
	// }}}

	always @(posedge i_clk)
	if (i2cd_valid)
		temp_tmp <= { temp_tmp[15:0], i2cd_data };

	always @(posedge i_clk)
	if (i2cd_valid && i2cd_last)
		temp_data <= { temp_tmp, i2cd_data };

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// WB returns
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	pre_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		pre_ack <= 1'b0;
	else
		pre_ack <= i_wb_stb && !o_wb_stall;

	always @(posedge i_clk)
	if (i_reset || !i_wb_stb || i_wb_addr[2])
		pre_data <= 0;
	else begin
		pre_data <= 0;
		case(i_wb_addr[1:0])
		2'b00: pre_data[LGPWM-1:0] <= ctl_fpga;
		2'b01: pre_data[LGPWM-1:0] <= ctl_sys;
		2'b10: pre_data[$clog2(CK_PER_SECOND)-1:0] <= tach_count;
		2'b11: pre_data <= temp_data;
		default: pre_data <= 32'h0;
		endcase
	end

	assign	o_wb_stall = i2c_wb_stall;

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= pre_ack;

	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_data <= 0;
	else if (i2c_wb_ack)
		o_wb_data <= i2c_wb_data;
	else
		o_wb_data <= pre_data;
	// }}}

	// Keep Verilator happy
	// {{{
	wire	unused;
	assign	unused = &{ 1'b0, ign_mem_cyc, ign_mem_we, ign_mem_data,
			ign_mem_sel, ign_i2cd_id };
	// }}}
endmodule
