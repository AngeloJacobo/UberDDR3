////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_test_top.v
// Project: Top level module instantiating the ddr3 test and UberDDR3.
//
// Engineer: Angelo C. Jacobo
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2023-2025  Angelo Jacobo
// 
//     This program is free software: you can redistribute it and/or modify
//     it under the terms of the GNU General Public License as published by
//     the Free Software Foundation, either version 3 of the License, or
//     (at your option) any later version.
// 
//     This program is distributed in the hope that it will be useful,
//     but WITHOUT ANY WARRANTY; without even the implied warranty of
//     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//     GNU General Public License for more details.
// 
//     You should have received a copy of the GNU General Public License
//     along with this program.  If not, see <https://www.gnu.org/licenses/>.
//
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps

   module enclustra_ddr3_test
	(
	input wire i_clk200_p, i_clk200_n, 
	input wire i_rst_n,
	// DDR3 I/O Interface
    output wire ddr3_clk_p, ddr3_clk_n,
    output wire ddr3_reset_n,
    output wire ddr3_cke, 
    output wire ddr3_cs_n, 
    output wire ddr3_ras_n, 
    output wire ddr3_cas_n, 
    output wire ddr3_we_n,
    output wire[15-1:0] ddr3_addr,
    output wire[3-1:0] ddr3_ba,
    inout wire[64-1:0] ddr3_dq,
    inout wire[8-1:0] ddr3_dqs_p, ddr3_dqs_n,
    output wire[8-1:0] ddr3_dm,
    output wire ddr3_odt, 
    // UART line
	input wire rx,
	output wire tx,
	//Debug LEDs
	output wire[3:0] led,
    // Button for fault injection
    input wire btn
    );
    

    localparam CONTROLLER_CLK_PERIOD = 5_000, // ps, clock period of the controller interface
            DDR3_CLK_PERIOD = 1_250, // ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD)
            ROW_BITS = 15, // Width of row address
            COL_BITS = 10, // Width of column address
            BA_BITS = 3, // Width of bank address
            BYTE_LANES = 8, // Number of DDR3 modules to be controlled
            AUX_WIDTH = 16, // Width of aux line (must be >= 4)
            BIST_MODE = 0; // Don't perform BIST, go straight to external DDR3 test

    parameter MICRON_SIM = 0, // Enable faster simulation for Micron DDR3 model
            ODELAY_SUPPORTED = 1, // Set to 1 when ODELAYE2 is supported
            DATA_MASK = 1; // enable test on datamask


    localparam WB_ADDR_BITS = ROW_BITS + COL_BITS + BA_BITS - 3,
                   WB_DATA_BITS = 8*BYTE_LANES*8,
                   WB_SEL_BITS = WB_DATA_BITS / 8;

    wire sys_clk_200MHz;
    wire i_controller_clk, i_ddr3_clk, i_ref_clk,i_clk100;
    wire clk_locked;
    wire timer_pulse, wrong_data_counter_non_zero;

    // Wishbone output signals
    wire o_wb_cyc;  // Bus cycle active (1 = normal operation, 0 = cancel all ongoing transactions)
    wire o_wb_stb;  // Request a transfer
    wire o_wb_we;   // Write-enable (1 = write, 0 = read)
    wire [WB_ADDR_BITS - 1:0] o_wb_addr;  // Burst-addressable {row, bank, col}
    wire [WB_DATA_BITS - 1:0] o_wb_data;  // Write data (depends on controller width)
    wire [WB_SEL_BITS - 1:0] o_wb_sel;    // Byte strobe for write (1 = write the byte)
    wire [AUX_WIDTH - 1:0] o_aux;  // AXI-interface compatibility (given upon strobe)

    // Wishbone input signals
    wire i_wb_stall;  // 1 = Busy, cannot accept requests
    wire i_wb_ack;    // 1 = Read/write request completed
    wire [WB_DATA_BITS - 1:0] i_wb_data;  // Read data
    wire [AUX_WIDTH - 1:0] i_aux;  // AXI-interface compatibility (given upon strobe)
    (* mark_debug = "true" *) wire calib_complete;

    assign led[0] = !calib_complete; //light up if at DONE_CALIBRATE
    assign led[1] = !wrong_data_counter_non_zero; //light up if at there is wrong data
    assign led[2] = !timer_pulse; //light up at timer pulse
    assign led[3] = !timer_pulse; //light up at timer pulse

    IBUFDS sys_clk_ibufgds
    (
        .O(sys_clk_200MHz),
        .I(i_clk200_p),
        .IB(i_clk200_n)
    );

    clk_wiz_0 clk_wiz_inst
    (
        // Clock out ports
        .controller_clk(i_controller_clk),
        .ddr3_clk(i_ddr3_clk),
        .ref200_clk(i_ref_clk),
        .clk100(i_clk100),
        // Status and control signals
        .reset(!i_rst_n),
        .locked(clk_locked),
        // Clock in ports
        .clk_in1(sys_clk_200MHz)
    );

    // DDR3 Controller 
    ddr3_top #(
        .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ps, clock period of the controller interface
        .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
        .ROW_BITS(ROW_BITS), //width of row address
        .COL_BITS(COL_BITS), //width of column address
        .BA_BITS(BA_BITS), //width of bank address
        .BYTE_LANES(BYTE_LANES), //number of DDR3 modules to be controlled
        .AUX_WIDTH(AUX_WIDTH), //width of aux line (must be >= 4) 
        .MICRON_SIM(MICRON_SIM), //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
        .ODELAY_SUPPORTED(ODELAY_SUPPORTED), //set to 1 when ODELAYE2 is supported
        .BIST_MODE(BIST_MODE)
    ) ddr3_top_inst
        (
            //clock and reset
            .i_controller_clk(i_controller_clk),
            .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
            .i_ref_clk(i_ref_clk),
            .i_ddr3_clk_90(),
            .i_rst_n(i_rst_n && clk_locked), 
            // Wishbone inputs
            .i_wb_cyc(o_wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb_stb(o_wb_stb), //request a transfer
            .i_wb_we(o_wb_we), //write-enable (1 = write, 0 = read)
            .i_wb_addr(o_wb_addr), //burst-addressable {row,bank,col} 
            .i_wb_data(o_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_wb_sel(o_wb_sel), //byte strobe for write (1 = write the byte)
            .i_aux(o_aux), //for AXI-interface compatibility (given upon strobe)
            // Wishbone outputs
            .o_wb_stall(i_wb_stall), //1 = busy, cannot accept requests
            .o_wb_ack(i_wb_ack), //1 = read/write request has completed
            .o_wb_data(i_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
            .o_aux(i_aux),
            // PHY Interface (to be added later)
            // DDR3 I/O Interface
            .o_ddr3_clk_p(ddr3_clk_p),
            .o_ddr3_clk_n(ddr3_clk_n),
            .o_ddr3_reset_n(ddr3_reset_n),
            .o_ddr3_cke(ddr3_cke), // CKE
            .o_ddr3_cs_n(ddr3_cs_n), // chip select signal (controls rank 1 only)
            .o_ddr3_ras_n(ddr3_ras_n), // RAS#
            .o_ddr3_cas_n(ddr3_cas_n), // CAS#
            .o_ddr3_we_n(ddr3_we_n), // WE#
            .o_ddr3_addr(ddr3_addr),
            .o_ddr3_ba_addr(ddr3_ba),
            .io_ddr3_dq(ddr3_dq),
            .io_ddr3_dqs(ddr3_dqs_p),
            .io_ddr3_dqs_n(ddr3_dqs_n),
            .o_ddr3_dm(ddr3_dm),
            .o_ddr3_odt(ddr3_odt), // on-die termination
            // debug
            .o_calib_complete(calib_complete)
        );
        
        ddr3_test #(
            .WB_ADDR_BITS(WB_ADDR_BITS),
            .WB_DATA_BITS(WB_DATA_BITS),
            .WB_SEL_BITS(WB_SEL_BITS),
            .AUX_WIDTH(AUX_WIDTH),
            .DATA_MASK(DATA_MASK),
            .MICRON_SIM(MICRON_SIM)
        ) ddr3_test_inst
        (
            .i_clk(i_controller_clk),
            .i_clk100(i_clk100),
            .i_rst_n(i_rst_n),
            //
            // Wishbone inputs
            .o_wb_cyc(o_wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .o_wb_stb(o_wb_stb), //request a transfer
            .o_wb_we(o_wb_we), //write-enable (1 = write, 0 = read)
            .o_wb_addr(o_wb_addr), //burst-addressable {row,bank,col} 
            .o_wb_data(o_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .o_wb_sel(o_wb_sel), //byte strobe for write (1 = write the byte)
            .o_aux(o_aux), //for AXI-interface compatibility (given upon strobe)
            //
            // Wishbone outputs
            .i_wb_stall(i_wb_stall), //1 = busy, cannot accept requests
            .i_wb_ack(i_wb_ack), //1 = read/write request has completed
            .i_wb_err(0), //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
            .i_wb_data(i_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_aux(i_aux), //for AXI-interface compatibility (given upon strobe)
            //
            // Done Calibration pin
            .i_calib_complete(calib_complete),
            // 
            // UART line
            .rx(rx),
            .tx(tx),
            // Button for fault injection
            .btn(!btn),
            // Debug
            .timer_pulse(timer_pulse),
            .wrong_data_counter_non_zero(wrong_data_counter_non_zero)
        );


endmodule

