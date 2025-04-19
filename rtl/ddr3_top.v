////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_top.v
// Project: UberDDR3 - An Open Source DDR3 Controller
//
// Purpose: Top module which instantiates the ddr3_controller and ddr3_phy modules
// Use this as top module for instantiating UberDDR3 with Wishbone Interface.
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

`default_nettype none
`timescale 1ps / 1ps

module ddr3_top #(
    parameter      CONTROLLER_CLK_PERIOD = 12_000, //ps, clock period of the controller interface
                   DDR3_CLK_PERIOD = 3_000, //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
                   ROW_BITS = 14,   //width of row address
                   COL_BITS = 10, //width of column address
                   BA_BITS = 3, //width of bank address
                   BYTE_LANES = 2, //number of byte lanes of DDR3 RAM
                   AUX_WIDTH = 4, //width of aux line (must be >= 4) 
                   WB2_ADDR_BITS = 7, //width of 2nd wishbone address bus 
                   WB2_DATA_BITS = 32, //width of 2nd wishbone data bus 
                   DUAL_RANK_DIMM = 0, // enable dual rank DIMM (1 =  enable, 0 = disable)
    // DDR3 timing parameter values
    parameter      SPEED_BIN = 3, // 0 = Use top-level parameters , 1 = DDR3-1066 (7-7-7) , 2 = DR3-1333 (9-9-9) , 3 = DDR3-1600 (11-11-11)
                   SDRAM_CAPACITY = 5, // 0 = 256Mb, 1 = 512Mb, 2 = 1Gb, 3 = 2Gb, 4 = 4Gb, 5 = 8Gb, 6 = 16Gb
                   TRCD = 13_750, // ps Active to Read/Write command time (only used if SPEED_BIN = 0)
                   TRP = 13_750, // ps Precharge command period (only used if SPEED_BIN = 0)
                   TRAS = 35_000, // ps ACT to PRE command period (only used if SPEED_BIN = 0)
    parameter[0:0] MICRON_SIM = 0, //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
                   ODELAY_SUPPORTED = 0, //set to 1 when ODELAYE2 is supported
                   SECOND_WISHBONE = 0, //set to 1 if 2nd wishbone for debugging is needed 
                   DLL_OFF = 0, // 1 = DLL off for low frequency ddr3 clock (< 125MHz)
                   WB_ERROR = 0, // set to 1 to support Wishbone error (asserts at ECC double bit error)
    parameter[1:0] BIST_MODE = 1, // 0 = No BIST, 1 = run through all address space ONCE , 2 = run through all address space for every test (burst w/r, random w/r, alternating r/w)
    parameter[1:0] ECC_ENABLE = 0, // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC ) 
    parameter[1:0] DIC = 2'b00, //Output Driver Impedance Control (2'b00 = RZQ/6, 2'b01 = RZQ/7, RZQ = 240ohms) (only change when you know what you are doing)
    parameter[2:0] RTT_NOM = 3'b011, //RTT Nominal (3'b000 = disabled, 3'b001 = RZQ/4, 3'b010 = RZQ/2 , 3'b011 = RZQ/6, RZQ = 240ohms)  (only change when you know what you are doing)
    parameter[1:0] SELF_REFRESH = 2'b00, // 0 = use i_user_self_refresh input, 1 = Self-refresh mode is enabled after 64 controller clock cycles of no requests, 2 = 128 cycles, 3 = 256 cycles
    parameter // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
                DQ_BITS = 8,  //device width (fixed to 8, if DDR3 is x16 then BYTE_LANES will be 2 while )
                serdes_ratio = 4, // this controller is fixed as a 4:1 memory controller (CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD = 4)
                wb_addr_bits = ROW_BITS + COL_BITS + BA_BITS - $clog2(serdes_ratio*2) + DUAL_RANK_DIMM,
                wb_data_bits = DQ_BITS*BYTE_LANES*serdes_ratio*2,
                wb_sel_bits = wb_data_bits / 8,
                wb2_sel_bits = WB2_DATA_BITS / 8,
                //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
                cmd_len = 4 + 3 + BA_BITS + ROW_BITS + 2*DUAL_RANK_DIMM
    ) 
    (
        input wire i_controller_clk, i_ddr3_clk, i_ref_clk, //i_controller_clk = CONTROLLER_CLK_PERIOD, i_ddr3_clk = DDR3_CLK_PERIOD, i_ref_clk = 200MHz
        input wire i_ddr3_clk_90, //required only when ODELAY_SUPPORTED is zero
        input wire i_rst_n,
        //
        // Wishbone inputs
        input wire i_wb_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb_stb, //request a transfer
        input wire i_wb_we, //write-enable (1 = write, 0 = read)
        input wire[wb_addr_bits - 1:0] i_wb_addr, //burst-addressable {row,bank,col} 
        input wire[wb_data_bits - 1:0] i_wb_data, //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        input wire[wb_sel_bits - 1:0] i_wb_sel, //byte strobe for write (1 = write the byte)
        input wire[AUX_WIDTH - 1:0]  i_aux, //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        output wire o_wb_stall, //1 = busy, cannot accept requests
        output wire o_wb_ack, //1 = read/write request has completed
        output wire o_wb_err, //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
        output wire[wb_data_bits - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output wire[AUX_WIDTH - 1:0]  o_aux, //for AXI-interface compatibility (given upon strobe)
        //
        // Wishbone 2 (PHY) inputs
        input wire i_wb2_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb2_stb, //request a transfer
        input wire i_wb2_we, //write-enable (1 = write, 0 = read)
        input wire[WB2_ADDR_BITS - 1:0] i_wb2_addr, // memory-mapped register to be accessed
        input wire[WB2_DATA_BITS - 1:0] i_wb2_data, //write data
        input wire[wb2_sel_bits - 1:0] i_wb2_sel, //byte strobe for write (1 = write the byte)
        // Wishbone 2 (Controller) outputs
        output wire o_wb2_stall, //1 = busy, cannot accept requests
        output wire o_wb2_ack, //1 = read/write request has completed
        output wire[WB2_DATA_BITS - 1:0] o_wb2_data, //read data
        //
        // DDR3 I/O Interface
        output wire[DUAL_RANK_DIMM:0] o_ddr3_clk_p, o_ddr3_clk_n,
        output wire o_ddr3_reset_n,
        output wire[DUAL_RANK_DIMM:0] o_ddr3_cke, // CKE
        output wire[DUAL_RANK_DIMM:0] o_ddr3_cs_n, // chip select signal
        output wire o_ddr3_ras_n, // RAS#
        output wire o_ddr3_cas_n, // CAS#
        output wire o_ddr3_we_n, // WE#
        output wire[ROW_BITS-1:0] o_ddr3_addr,
        output wire[BA_BITS-1:0] o_ddr3_ba_addr,
        inout wire[(DQ_BITS*BYTE_LANES)-1:0] io_ddr3_dq,
        inout wire[BYTE_LANES-1:0] io_ddr3_dqs, io_ddr3_dqs_n,
        output wire[BYTE_LANES-1:0] o_ddr3_dm,
        output wire[DUAL_RANK_DIMM:0] o_ddr3_odt, // on-die termination
        //
        // Done Calibration pin
        output wire o_calib_complete,
        // Debug outputs
        output wire[31:0] o_debug1,
//        output wire[31:0] o_debug2,
//        output wire[31:0] o_debug3,
//        output wire[(DQ_BITS*BYTE_LANES)/8-1:0] o_ddr3_debug_read_dqs_p,
//        output wire[(DQ_BITS*BYTE_LANES)/8-1:0] o_ddr3_debug_read_dqs_n
        // 
        // User enabled self-refresh
        input wire i_user_self_refresh,
        output wire uart_tx
    );
    
// Instantiation Template (DEFAULT VALUE IS FOR ARTY S7)
/*
// DDR3 Controller 
ddr3_top #(
    .CONTROLLER_CLK_PERIOD(12_000), //ps, clock period of the controller interface
    .DDR3_CLK_PERIOD(3_000), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
    .ROW_BITS(14), //width of row address
    .COL_BITS(10), //width of column address
    .BA_BITS(3), //width of bank address
    .BYTE_LANES(2), //number of byte lanes of DDR3 RAM
    .AUX_WIDTH(4), //width of aux line (must be >= 4) 
    .MICRON_SIM(0), //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
    .ODELAY_SUPPORTED(0), //set to 1 if ODELAYE2 is supported
    .SECOND_WISHBONE(0), //set to 1 if 2nd wishbone for debugging is needed 
    .ECC_ENABLE(0), // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC ) 
    .WB_ERROR(0), // set to 1 to support Wishbone error (asserts at ECC double bit error)
    ) ddr3_top
    (
        //clock and reset
        .i_controller_clk(i_controller_clk),
        .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
        .i_ref_clk(i_ref_clk), // usually set to 200 MHz 
        .i_ddr3_clk_90(i_ddr3_clk_90), //90 degree phase shifted version i_ddr3_clk (required only when ODELAY_SUPPORTED is zero)
        .i_rst_n(!i_rst && clk_locked), 
        //
        // Wishbone inputs
        .i_wb_cyc(1), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb_stb(i_wb_stb), //request a transfer
        .i_wb_we(i_wb_we), //write-enable (1 = write, 0 = read)
        .i_wb_addr(i_wb_addr), //burst-addressable {row,bank,col} 
        .i_wb_data(i_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb_sel(16'hffff), //byte strobe for write (1 = write the byte)
        .i_aux(i_wb_we), //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
        .o_wb_ack(o_wb_ack), //1 = read/write request has completed
        .o_wb_err(o_wb_err), //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
        .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        .o_aux(o_aux),
        //
        // Wishbone 2 (PHY) inputs
        .i_wb2_cyc(0), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb2_stb(0), //request a transfer
        .i_wb2_we(0), //write-enable (1 = write, 0 = read)
        .i_wb2_addr(0), //burst-addressable {row,bank,col} 
        .i_wb2_data(0), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb2_sel(0), //byte strobe for write (1 = write the byte)
        // Wishbone 2 (Controller) outputs
        .o_wb2_stall(), //1 = busy, cannot accept requests
        .o_wb2_ack(), //1 = read/write request has completed
        .o_wb2_data(), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        //
        // DDR3 I/O Interface
        .o_ddr3_clk_p(ddr3_clk_p), 
        .o_ddr3_clk_n(ddr3_clk_n),
        .o_ddr3_reset_n(ddr3_reset_n),
        .o_ddr3_cke(ddr3_cke), 
        .o_ddr3_cs_n(ddr3_cs_n), // width = number of DDR3 ranks
        .o_ddr3_ras_n(ddr3_ras_n), 
        .o_ddr3_cas_n(ddr3_cas_n), 
        .o_ddr3_we_n(ddr3_we_n), 
        .o_ddr3_addr(ddr3_addr), // width = ROW_BITS
        .o_ddr3_ba_addr(ddr3_ba), // width = BA_BITS
        .io_ddr3_dq(ddr3_dq), // width = BYTE_LANES*8
        .io_ddr3_dqs(ddr3_dqs_p), // width = BYTE_LANES
        .io_ddr3_dqs_n(ddr3_dqs_n), // width = BYTE_LANES
        .o_ddr3_dm(ddr3_dm), // width = BYTE_LANES
        .o_ddr3_odt(ddr3_odt),
        // Debug outputs
        .o_debug1(),
        ////////////////////////////////////
    );
*/
    
    // Wire connections between controller and phy
    wire[cmd_len*serdes_ratio-1:0] cmd;
    wire dqs_tri_control, dq_tri_control;
    wire toggle_dqs;
    wire[wb_data_bits-1:0] data;
    wire[wb_sel_bits-1:0] dm;
    wire[BYTE_LANES-1:0] bitslip;
    wire[DQ_BITS*BYTE_LANES*8-1:0] iserdes_data;
    wire[BYTE_LANES*8-1:0] iserdes_dqs;
    wire[BYTE_LANES*8-1:0] iserdes_bitslip_reference;
    wire idelayctrl_rdy;
    wire[4:0] odelay_data_cntvaluein, odelay_dqs_cntvaluein;
    wire[4:0] idelay_data_cntvaluein, idelay_dqs_cntvaluein;
    wire[BYTE_LANES-1:0] odelay_data_ld, odelay_dqs_ld;
    wire[BYTE_LANES-1:0] idelay_data_ld, idelay_dqs_ld;
    wire write_leveling_calib;
    wire reset;
    
    // logic for self-refresh
    reg[8:0] refresh_counter = 0;
    reg user_self_refresh;
    // refresh counter 
    always @(posedge i_controller_clk) begin
        if(i_wb_stb && i_wb_cyc) begin // if there is Wishbone request, then reset counter
            refresh_counter <= 0;
        end
        else if(!o_wb_stall || user_self_refresh) begin // if no request (but not stalled) OR already on self-refresh, then increment counter
            refresh_counter <= refresh_counter + 1;
        end
    end
    // choose self-refresh options
    always @* begin
        case(SELF_REFRESH) 
            2'b00: user_self_refresh = i_user_self_refresh; // use input i_user_self_refresh (high = enter self-refresh, low = exit self-refresh)
            2'b01: user_self_refresh = refresh_counter[6];  // Self-refresh mode is enabled after 64 controller clock cycles of no requests, then exit Self-refresh after another 64 controller clk cycles
            2'b10: user_self_refresh = refresh_counter[7];  // Self-refresh mode is enabled after 128 controller clock cycles of no requests, then exit Self-refresh after another 128 controller clk cycles
            2'b11: user_self_refresh = refresh_counter[8];  // Self-refresh mode is enabled after 256 controller clock cycles of no requests, then exit Self-refresh after another 256 controller clk cycles
        endcase
    end
    

    
    //module instantiations
    ddr3_controller #(
            .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ps, clock period of the controller interface
            .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
            .ROW_BITS(ROW_BITS), //width of row address
            .COL_BITS(COL_BITS), //width of column address
            .BA_BITS(BA_BITS), //width of bank address
            .DQ_BITS(DQ_BITS),  //width of DQ
            .LANES(BYTE_LANES), // byte lanes
            .AUX_WIDTH(AUX_WIDTH), //width of aux line (must be >= 4) 
            .WB2_ADDR_BITS(WB2_ADDR_BITS), //width of 2nd wishbone address bus 
            .WB2_DATA_BITS(WB2_DATA_BITS),  //width of 2nd wishbone data bus
            .MICRON_SIM(MICRON_SIM), //simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
            .ODELAY_SUPPORTED(ODELAY_SUPPORTED),  //set to 1 when ODELAYE2 is supported
            .SECOND_WISHBONE(SECOND_WISHBONE), //set to 1 if 2nd wishbone is needed 
            .ECC_ENABLE(ECC_ENABLE), // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC ) 
            .DLL_OFF(DLL_OFF), // 1 = DLL off for low frequency ddr3 clock (< 125MHz)
            .WB_ERROR(WB_ERROR), // set to 1 to support Wishbone error (asserts at ECC double bit error)
            .BIST_MODE(BIST_MODE), // 0 = No BIST, 1 = run through all address space ONCE , 2 = run through all address space for every test (burst w/r, random w/r, alternating r/w)
            .DIC(DIC), //Output Driver Impedance Control (2'b00 = RZQ/6, 2'b01 = RZQ/7, RZQ = 240ohms)
            .RTT_NOM(RTT_NOM), //RTT Nominal (3'b000 = disabled, 3'b001 = RZQ/4, 3'b010 = RZQ/2 , 3'b011 = RZQ/6, RZQ = 240ohms)
            .DUAL_RANK_DIMM(DUAL_RANK_DIMM), // enable dual rank DIMM (1 =  enable, 0 = disable)
            .SPEED_BIN(SPEED_BIN), // 0 = Use top-level parameters , 1 = DDR3-1066 (7-7-7) , 2 = DR3-1333 (9-9-9) , 3 = DDR3-1600 (11-11-11)
            .SDRAM_CAPACITY(SDRAM_CAPACITY), // 0 = 256Mb, 1 = 512Mb, 2 = 1Gb, 3 = 2Gb, 4 = 4Gb, 5 = 8Gb, 6 = 16Gb
            .TRCD(TRCD), // ps Active to Read/Write command time (only used if SPEED_BIN = 0)
            .TRP(TRP), // ps Precharge command period (only used if SPEED_BIN = 0)
            .TRAS(TRAS) // ps ACT to PRE command period (only used if SPEED_BIN = 0)
        ) ddr3_controller_inst (
            .i_controller_clk(i_controller_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD 
            .i_rst_n(i_rst_n), //200MHz input clock
            // Wishbone inputs
            .i_wb_cyc(i_wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb_stb(i_wb_stb), //request a transfer
            .i_wb_we(i_wb_we), //write-enable (1 = write, 0 = read)
            .i_wb_addr(i_wb_addr), //burst-addressable {row,bank,col} 
            .i_wb_data(i_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_wb_sel(i_wb_sel), //byte strobe for write (1 = write the byte)
            .i_aux(i_aux), //for AXI-interface compatibility (given upon strobe)
            // Wishbone outputs
            .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
            .o_wb_ack(o_wb_ack), //1 = read/write request has completed
            .o_wb_err(o_wb_err), //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
            .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
            .o_aux(o_aux), //for AXI-interface compatibility (returned upon ack)
            // Wishbone 2 (PHY) inputs
            .i_wb2_cyc(i_wb2_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb2_stb(i_wb2_stb), //request a transfer
            .i_wb2_we(i_wb2_we), //write-enable (1 = write, 0 = read)
            .i_wb2_addr(i_wb2_addr), // memory-mapped register to be accessed 
            .i_wb2_data(i_wb2_data), //write data
            .i_wb2_sel(i_wb2_sel), //byte strobe for write (1 = write the byte)
            // Wishbone 2 (Controller) outputs
            .o_wb2_stall(o_wb2_stall), //1 = busy, cannot accept requests
            .o_wb2_ack(o_wb2_ack), //1 = read/write request has completed
            .o_wb2_data(o_wb2_data), //read data
            //
            // PHY interface
            .i_phy_iserdes_data(iserdes_data),
            .i_phy_iserdes_dqs(iserdes_dqs),
            .i_phy_iserdes_bitslip_reference(iserdes_bitslip_reference),
            .i_phy_idelayctrl_rdy(idelayctrl_rdy),
            .o_phy_cmd(cmd),
            .o_phy_dqs_tri_control(dqs_tri_control), 
            .o_phy_dq_tri_control(dq_tri_control),
            .o_phy_toggle_dqs(toggle_dqs),
            .o_phy_data(data),
            .o_phy_dm(dm),
            .o_phy_odelay_data_cntvaluein(odelay_data_cntvaluein),
            .o_phy_odelay_dqs_cntvaluein(odelay_dqs_cntvaluein),
            .o_phy_idelay_data_cntvaluein(idelay_data_cntvaluein), 
            .o_phy_idelay_dqs_cntvaluein(idelay_dqs_cntvaluein),
            .o_phy_odelay_data_ld(odelay_data_ld),
            .o_phy_odelay_dqs_ld(odelay_dqs_ld),
            .o_phy_idelay_data_ld(idelay_data_ld), 
            .o_phy_idelay_dqs_ld(idelay_dqs_ld),
            .o_phy_bitslip(bitslip),
            .o_phy_write_leveling_calib(write_leveling_calib),
            .o_phy_reset(reset),
            // Done Calibration pin
            .o_calib_complete(o_calib_complete),
            // Debug outputs
            .o_debug1(o_debug1),
//            .o_debug2(o_debug2),
//            .o_debug3(o_debug3)
            // User enabled self-refresh
            .i_user_self_refresh(user_self_refresh),
            .uart_tx(uart_tx)
        );
    `ifndef LATTICE_ECP5_PHY // XILINX PHY
        ddr3_phy #(
                .ROW_BITS(ROW_BITS), //width of row address
                .BA_BITS(BA_BITS), //width of bank address
                .DQ_BITS(DQ_BITS),  //width of DQ
                .LANES(BYTE_LANES), //8 lanes of DQ
                .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ps, period of clock input to this DDR3 controller module
                .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ps, period of clock input to DDR3 RAM device 
                .ODELAY_SUPPORTED(ODELAY_SUPPORTED), //set to 1 when ODELAYE2 is supported
                .DUAL_RANK_DIMM(DUAL_RANK_DIMM) // enable dual rank DIMM (1 =  enable, 0 = disable)
            ) ddr3_phy_inst (
                .i_controller_clk(i_controller_clk), 
                .i_ddr3_clk(i_ddr3_clk),
                .i_ref_clk(i_ref_clk),
                .i_ddr3_clk_90(i_ddr3_clk_90), 
                .i_rst_n(i_rst_n),
                // Controller Interface
                .i_controller_reset(reset),
                .i_controller_cmd(cmd),
                .i_controller_dqs_tri_control(dqs_tri_control), 
                .i_controller_dq_tri_control(dq_tri_control),
                .i_controller_toggle_dqs(toggle_dqs),
                .i_controller_data(data),
                .i_controller_dm(dm),
                .i_controller_odelay_data_cntvaluein(odelay_data_cntvaluein),
                .i_controller_odelay_dqs_cntvaluein(odelay_dqs_cntvaluein),
                .i_controller_idelay_data_cntvaluein(idelay_data_cntvaluein),
                .i_controller_idelay_dqs_cntvaluein(idelay_dqs_cntvaluein),
                .i_controller_odelay_data_ld(odelay_data_ld), 
                .i_controller_odelay_dqs_ld(odelay_dqs_ld),
                .i_controller_idelay_data_ld(idelay_data_ld), 
                .i_controller_idelay_dqs_ld(idelay_dqs_ld),
                .i_controller_bitslip(bitslip),
                .i_controller_write_leveling_calib(write_leveling_calib),
                .o_controller_iserdes_data(iserdes_data),
                .o_controller_iserdes_dqs(iserdes_dqs),
                .o_controller_iserdes_bitslip_reference(iserdes_bitslip_reference),
                .o_controller_idelayctrl_rdy(idelayctrl_rdy),
                // DDR3 I/O Interface
                .o_ddr3_clk_p(o_ddr3_clk_p),
                .o_ddr3_clk_n(o_ddr3_clk_n),
                .o_ddr3_reset_n(o_ddr3_reset_n),
                .o_ddr3_cke(o_ddr3_cke), // CKE
                .o_ddr3_cs_n(o_ddr3_cs_n), // chip select signal
                .o_ddr3_ras_n(o_ddr3_ras_n), // RAS#
                .o_ddr3_cas_n(o_ddr3_cas_n), // CAS#
                .o_ddr3_we_n(o_ddr3_we_n), // WE#
                .o_ddr3_addr(o_ddr3_addr),
                .o_ddr3_ba_addr(o_ddr3_ba_addr),
                .io_ddr3_dq(io_ddr3_dq),
                .io_ddr3_dqs(io_ddr3_dqs),
                .io_ddr3_dqs_n(io_ddr3_dqs_n),
                .o_ddr3_dm(o_ddr3_dm),
                .o_ddr3_odt(o_ddr3_odt), // on-die termination
                .o_ddr3_debug_read_dqs_p(/*o_ddr3_debug_read_dqs_p*/),
                .o_ddr3_debug_read_dqs_n(/*o_ddr3_debug_read_dqs_n*/)
            );
    `else // LATTICE ECP5 PHY
        ddr3_phy_ecp5 #(
                .ROW_BITS(ROW_BITS), //width of row address
                .BA_BITS(BA_BITS), //width of bank address
                .DQ_BITS(DQ_BITS),  //width of DQ
                .LANES(BYTE_LANES), //8 lanes of DQ
                .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD) //ps, period of clock input to this DDR3 controller module
            ) ddr3_phy_inst (
                .i_controller_clk(i_controller_clk), 
                .i_ddr3_clk(i_ddr3_clk),
                .i_ref_clk(i_ref_clk),
                .i_ddr3_clk_90(i_ddr3_clk_90), 
                .i_rst_n(i_rst_n),
                // Controller Interface
                .i_controller_reset(reset),
                .i_controller_cmd(cmd),
                .i_controller_dqs_tri_control(dqs_tri_control), 
                .i_controller_dq_tri_control(dq_tri_control),
                .i_controller_toggle_dqs(toggle_dqs),
                .i_controller_data(data),
                .i_controller_dm(dm),
                .i_controller_odelay_data_cntvaluein(odelay_data_cntvaluein),
                .i_controller_odelay_dqs_cntvaluein(odelay_dqs_cntvaluein),
                .i_controller_idelay_data_cntvaluein(idelay_data_cntvaluein),
                .i_controller_idelay_dqs_cntvaluein(idelay_dqs_cntvaluein),
                .i_controller_odelay_data_ld(odelay_data_ld), 
                .i_controller_odelay_dqs_ld(odelay_dqs_ld),
                .i_controller_idelay_data_ld(idelay_data_ld), 
                .i_controller_idelay_dqs_ld(idelay_dqs_ld),
                .i_controller_bitslip(bitslip),
                .i_controller_write_leveling_calib(write_leveling_calib),
                .o_controller_iserdes_data(iserdes_data),
                .o_controller_iserdes_dqs(iserdes_dqs),
                .o_controller_iserdes_bitslip_reference(iserdes_bitslip_reference),
                .o_controller_idelayctrl_rdy(idelayctrl_rdy),
                // DDR3 I/O Interface
                .o_ddr3_clk_p(o_ddr3_clk_p),
                .o_ddr3_clk_n(o_ddr3_clk_n),
                .o_ddr3_reset_n(o_ddr3_reset_n),
                .o_ddr3_cke(o_ddr3_cke), // CKE
                .o_ddr3_cs_n(o_ddr3_cs_n), // chip select signal
                .o_ddr3_ras_n(o_ddr3_ras_n), // RAS#
                .o_ddr3_cas_n(o_ddr3_cas_n), // CAS#
                .o_ddr3_we_n(o_ddr3_we_n), // WE#
                .o_ddr3_addr(o_ddr3_addr),
                .o_ddr3_ba_addr(o_ddr3_ba_addr),
                .io_ddr3_dq(io_ddr3_dq),
                .io_ddr3_dqs(io_ddr3_dqs),
                .io_ddr3_dqs_n(io_ddr3_dqs_n),
                .o_ddr3_dm(o_ddr3_dm),
                .o_ddr3_odt(o_ddr3_odt), // on-die termination
                .o_ddr3_debug_read_dqs_p(/*o_ddr3_debug_read_dqs_p*/),
                .o_ddr3_debug_read_dqs_n(/*o_ddr3_debug_read_dqs_n*/)
            );
    `endif 

        // // display value of parameters for easy debugging
        // initial begin
        //     $display("\nDDR3 TOP PARAMETERS:\n-----------------------------");
        //     $display("CONTROLLER_CLK_PERIOD = %0d", CONTROLLER_CLK_PERIOD);
        //     $display("DDR3_CLK_PERIOD = %0d", DDR3_CLK_PERIOD);
        //     $display("ROW_BITS = %0d", ROW_BITS);
        //     $display("COL_BITS = %0d", COL_BITS);
        //     $display("BA_BITS = %0d", BA_BITS);
        //     $display("BYTE_LANES = %0d", BYTE_LANES);
        //     $display("AUX_WIDTH = %0d", AUX_WIDTH);
        //     $display("WB2_ADDR_BITS = %0d", WB2_ADDR_BITS);
        //     $display("WB2_DATA_BITS = %0d", WB2_DATA_BITS);
        //     $display("MICRON_SIM = %0d", MICRON_SIM);
        //     $display("ODELAY_SUPPORTED = %0d", ODELAY_SUPPORTED);
        //     $display("SECOND_WISHBONE = %0d", SECOND_WISHBONE);
        //     $display("WB_ERROR = %0d", WB_ERROR);
        //     $display("BIST_MODE = %0d", BIST_MODE);
        //     $display("ECC_ENABLE = %0d", ECC_ENABLE);
        //     $display("DIC = %0d", DIC);
        //     $display("RTT_NOM = %0d", RTT_NOM);
        //     $display("SELF_REFRESH = %0d", SELF_REFRESH);
        //     $display("DUAL_RANK_DIMM = %0d", DUAL_RANK_DIMM);
        //     $display("End of DDR3 TOP PARAMETERS\n-----------------------------");
        // end

endmodule
