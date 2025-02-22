////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_top_axi.v
// Project: UberDDR3 - An Open Source DDR3 Controller
//
// Purpose: Top module which instantiates the ddr3_top and AXI to Wishbone bridge.
// Use this as top module for instantiating UberDDR3 with AXI4 interface.
//
// Engineer: Angelo C. Jacobo
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2023-2024  Angelo Jacobo
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

module ddr3_top_axi #(
    parameter      CONTROLLER_CLK_PERIOD = 12_000, //ps, clock period of the controller interface
                   DDR3_CLK_PERIOD = 3_000, //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
                   ROW_BITS = 14,   //width of row address
                   COL_BITS = 10, //width of column address
                   BA_BITS = 3, //width of bank address
                   BYTE_LANES = 2, //number of byte lanes of DDR3 RAM
                   AXI_ID_WIDTH = 4, // The AXI id width used for R&W, an int between 1-16
                   WB2_ADDR_BITS = 7, //width of 2nd wishbone address bus 
                   WB2_DATA_BITS = 32, //width of 2nd wishbone data bus 
    /* verilator lint_off UNUSEDPARAM */ 
    parameter[0:0] MICRON_SIM = 0, //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
                   ODELAY_SUPPORTED = 0, //set to 1 when ODELAYE2 is supported
                   SECOND_WISHBONE = 0, //set to 1 if 2nd wishbone for debugging is needed 
                   WB_ERROR = 0, // set to 1 to support Wishbone error (asserts at ECC double bit error)
    parameter[1:0] BIST_MODE = 2, // 0 = No BIST, 1 = run through all address space ONCE , 2 = run through all address space for every test (burst w/r, random w/r, alternating r/w)
    parameter[1:0] ECC_ENABLE = 0, // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC ) 
    parameter[1:0] DIC = 2'b00, //Output Driver Impedance Control (2'b00 = RZQ/6, 2'b01 = RZQ/7, RZQ = 240ohms) (only change when you know what you are doing)
    parameter[2:0] RTT_NOM = 3'b011, //RTT Nominal (3'b000 = disabled, 3'b001 = RZQ/4, 3'b010 = RZQ/2 , 3'b011 = RZQ/6, RZQ = 240ohms)  (only change when you know what you are doing)
    parameter[1:0] SELF_REFRESH = 2'b00, // 0 = use i_user_self_refresh input, 1 = Self-refresh mode is enabled after 64 controller clock cycles of no requests, 2 = 128 cycles, 3 = 256 cycles
    parameter // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
                DQ_BITS = 8,  //device width (fixed to 8, if DDR3 is x16 then BYTE_LANES will be 2 while )
                serdes_ratio = 4, // this controller is fixed as a 4:1 memory controller (CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD = 4)
                wb_addr_bits = ROW_BITS + COL_BITS + BA_BITS - $clog2(serdes_ratio*2),
                wb_data_bits = DQ_BITS*BYTE_LANES*serdes_ratio*2,
                wb_sel_bits = wb_data_bits / 8,
                wb2_sel_bits = WB2_DATA_BITS / 8,
                //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
                cmd_len = 4 + 3 + BA_BITS + ROW_BITS,
                AXI_LSBS = $clog2(wb_data_bits)-3,
                AXI_ADDR_WIDTH = wb_addr_bits + AXI_LSBS,
                AXI_DATA_WIDTH = wb_data_bits
    ) 
    (
        input wire i_controller_clk, i_ddr3_clk, i_ref_clk, //i_controller_clk = CONTROLLER_CLK_PERIOD, i_ddr3_clk = DDR3_CLK_PERIOD, i_ref_clk = 200MHz
        input wire i_ddr3_clk_90, //required only when ODELAY_SUPPORTED is zero
        input wire i_rst_n,
        //
        // AXI Interface
        // AXI write address channel signals
        input wire s_axi_awvalid,
        output wire s_axi_awready,
        input wire [AXI_ID_WIDTH-1:0] s_axi_awid,
        input wire [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
        input wire [7:0] s_axi_awlen,
        input wire [2:0] s_axi_awsize,
        input wire [1:0] s_axi_awburst,
        input wire [0:0] s_axi_awlock,
        input wire [3:0] s_axi_awcache,
        input wire [2:0] s_axi_awprot,
        input wire [3:0] s_axi_awqos,
        // AXI write data channel signals
        input wire s_axi_wvalid,
        output wire s_axi_wready, 
        input wire [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
        input wire [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
        input wire s_axi_wlast,
        // AXI write response channel signals
        output wire s_axi_bvalid, 
        input wire s_axi_bready,
        output wire [AXI_ID_WIDTH-1:0] s_axi_bid,
        output wire [1:0] s_axi_bresp,
        // AXI read address channel signals
        input wire s_axi_arvalid,
        output wire s_axi_arready,
        input wire [AXI_ID_WIDTH-1:0]   s_axi_arid,
        input wire [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
        input wire [7:0] s_axi_arlen,
        input wire [2:0] s_axi_arsize,
        input wire [1:0] s_axi_arburst,
        input wire [0:0] s_axi_arlock,
        input wire [3:0] s_axi_arcache,
        input wire [2:0] s_axi_arprot,
        input wire [3:0] s_axi_arqos,
        // AXI read data channel signals
        output wire s_axi_rvalid,  // rd rslt valid
        input wire s_axi_rready,  // rd rslt ready
        output wire [AXI_ID_WIDTH-1:0]   s_axi_rid, // response id
        output wire [AXI_DATA_WIDTH-1:0] s_axi_rdata,// read data
        output wire s_axi_rlast,   // read last
        output wire [1:0] s_axi_rresp,   // read response
        //
        // DDR3 I/O Interface
        output wire o_ddr3_clk_p, o_ddr3_clk_n,
        output wire o_ddr3_reset_n,
        output wire o_ddr3_cke, 
        output wire o_ddr3_cs_n, 
        output wire o_ddr3_ras_n, 
        output wire o_ddr3_cas_n,
        output wire o_ddr3_we_n,
        output wire[ROW_BITS-1:0] o_ddr3_addr,
        output wire[BA_BITS-1:0] o_ddr3_ba_addr,
        inout wire[(DQ_BITS*BYTE_LANES)-1:0] io_ddr3_dq,
        inout wire[BYTE_LANES-1:0] io_ddr3_dqs, io_ddr3_dqs_n,
        output wire[BYTE_LANES-1:0] o_ddr3_dm,
        output wire o_ddr3_odt,
        //
        // Done Calibration pin
        output wire o_calib_complete,
        //
        // Debug outputs
        output wire[31:0] o_debug1,
//        output wire[31:0] o_debug2,
//        output wire[31:0] o_debug3,
//        output wire[(DQ_BITS*BYTE_LANES)/8-1:0] o_ddr3_debug_read_dqs_p,
//        output wire[(DQ_BITS*BYTE_LANES)/8-1:0] o_ddr3_debug_read_dqs_n
        //
        // User enabled self-refresh
        input wire i_user_self_refresh
    );

wire wb_cyc;
wire wb_stb;
wire wb_we;
wire[wb_addr_bits-1:0] wb_addr;
wire[wb_data_bits-1:0] o_wb_data;
wire[wb_sel_bits-1:0] wb_sel;
wire wb_stall;
wire wb_ack;
wire[wb_data_bits-1:0] i_wb_data;

// DDR3 Controller 
ddr3_top #(
    .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ps, clock period of the controller interface
    .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
    .ROW_BITS(ROW_BITS), //width of row address
    .COL_BITS(COL_BITS), //width of column address
    .BA_BITS(BA_BITS), //width of bank address
    .BYTE_LANES(BYTE_LANES), //number of byte lanes of DDR3 RAM
    .AUX_WIDTH(AXI_ID_WIDTH), //width of aux line (must be >= 4) 
    .MICRON_SIM(MICRON_SIM), //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
    .ODELAY_SUPPORTED(ODELAY_SUPPORTED), //set to 1 if ODELAYE2 is supported
    .SECOND_WISHBONE(SECOND_WISHBONE), //set to 1 if 2nd wishbone for debugging is needed 
    .WB2_ADDR_BITS(WB2_ADDR_BITS), //width of 2nd wishbone address bus 
    .WB2_DATA_BITS(WB2_DATA_BITS), //width of 2nd wishbone data bus
    .WB_ERROR(WB_ERROR), // set to 1 to support Wishbone error (asserts at ECC double bit error)
    .BIST_MODE(BIST_MODE), // 0 = No BIST, 1 = run through all address space ONCE , 2 = run through all address space for every test (burst w/r, random w/r, alternating r/w)
    .ECC_ENABLE(ECC_ENABLE), // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC ) 
    .DIC(DIC), // Output Driver Impedance Control (2'b00 = RZQ/6, 2'b01 = RZQ/7, RZQ = 240ohms) (only change when you know what you are doing)
    .RTT_NOM(RTT_NOM), //RTT Nominal (3'b000 = disabled, 3'b001 = RZQ/4, 3'b010 = RZQ/2 , 3'b011 = RZQ/6, RZQ = 240ohms)  (only change when you know what you are doing)
    .SELF_REFRESH(SELF_REFRESH) // Self-refresh options (0 = use i_user_self_refresh input, 1 = Self-refresh mode is enabled after 64 controller clock cycles of no requests, 2 = 128 cycles, 3 = 256 cycles)
    ) ddr3_top_inst
    (
        //clock and reset
        .i_controller_clk(i_controller_clk),
        .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
        .i_ref_clk(i_ref_clk), // usually set to 200 MHz 
        .i_ddr3_clk_90(i_ddr3_clk_90), //90 degree phase shifted version i_ddr3_clk (required only when ODELAY_SUPPORTED is zero)
        .i_rst_n(i_rst_n), 
        //
        // Wishbone inputs
        .i_wb_cyc(wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb_stb(wb_stb), //request a transfer
        .i_wb_we(wb_we), //write-enable (1 = write, 0 = read)
        .i_wb_addr(wb_addr), //burst-addressable {row,bank,col} 
        .i_wb_data(o_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb_sel(wb_sel), //byte strobe for write (1 = write the byte)
        .i_aux(0), //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        .o_wb_stall(wb_stall), //1 = busy, cannot accept requests
        .o_wb_ack(wb_ack), //1 = read/write request has completed
        .o_wb_data(i_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        .o_aux(),
        //
        // Wishbone 2 (PHY) inputs (WISHBONE 2 UNCONNECTED IN AXI MODE)
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
        .o_ddr3_clk_p(o_ddr3_clk_p), 
        .o_ddr3_clk_n(o_ddr3_clk_n),
        .o_ddr3_reset_n(o_ddr3_reset_n),
        .o_ddr3_cke(o_ddr3_cke), 
        .o_ddr3_cs_n(o_ddr3_cs_n), // width = number of DDR3 ranks
        .o_ddr3_ras_n(o_ddr3_ras_n), 
        .o_ddr3_cas_n(o_ddr3_cas_n), 
        .o_ddr3_we_n(o_ddr3_we_n), 
        .o_ddr3_addr(o_ddr3_addr), // width = ROW_BITS
        .o_ddr3_ba_addr(o_ddr3_ba_addr), // width = BA_BITS
        .io_ddr3_dq(io_ddr3_dq), // width = BYTE_LANES*8
        .io_ddr3_dqs(io_ddr3_dqs), // width = BYTE_LANES
        .io_ddr3_dqs_n(io_ddr3_dqs_n), // width = BYTE_LANES
        .o_ddr3_dm(o_ddr3_dm), // width = BYTE_LANES
        .o_ddr3_odt(o_ddr3_odt),
        //
        // Done Calibration pin
        .o_calib_complete(o_calib_complete),
        //
        // Debug outputs
        .o_debug1(o_debug1),
        // .o_debug2(o_debug2),
        // .o_debug3(o_debug3),
        // .o_ddr3_debug_read_dqs_p(o_ddr3_debug_read_dqs_p),
        // .o_ddr3_debug_read_dqs_n(o_ddr3_debug_read_dqs_n)
        //
        .i_user_self_refresh(i_user_self_refresh)
        ////////////////////////////////////
    );

axim2wbsp #(
        .C_AXI_ID_WIDTH(AXI_ID_WIDTH), // The AXI id width used for R&W, an int between 1-16
        .C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),// Width of the AXI R&W data
        .C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),	// AXI Address width
        .LGFIFO(5),
        .OPT_SWAP_ENDIANNESS(0),
        .OPT_READONLY(0),
        .OPT_WRITEONLY(0)
    ) axim2wbsp_inst (
            .S_AXI_ACLK(i_controller_clk),	// System clock
            .S_AXI_ARESETN(i_rst_n),
            // AXI write address channel signals
            .S_AXI_AWVALID(s_axi_awvalid),
            .S_AXI_AWREADY(s_axi_awready),
            .S_AXI_AWID(s_axi_awid),
            .S_AXI_AWADDR(s_axi_awaddr),
            .S_AXI_AWLEN(s_axi_awlen),
            .S_AXI_AWSIZE(s_axi_awsize),
            .S_AXI_AWBURST(s_axi_awburst),
            .S_AXI_AWLOCK(s_axi_awlock),
            .S_AXI_AWCACHE(s_axi_awcache),
            .S_AXI_AWPROT(s_axi_awprot),
            .S_AXI_AWQOS(s_axi_awqos),
            // AXI write data channel signals
            .S_AXI_WVALID(s_axi_wvalid),
            .S_AXI_WREADY(s_axi_wready), 
            .S_AXI_WDATA(s_axi_wdata),
            .S_AXI_WSTRB(s_axi_wstrb),
            .S_AXI_WLAST(s_axi_wlast),
            // AXI write response channel signals
            .S_AXI_BVALID(s_axi_bvalid), 
            .S_AXI_BREADY(s_axi_bready),
            .S_AXI_BID(s_axi_bid),
            .S_AXI_BRESP(s_axi_bresp),
            // AXI read address channel signals
            .S_AXI_ARVALID(s_axi_arvalid),
            .S_AXI_ARREADY(s_axi_arready),
            .S_AXI_ARID(s_axi_arid),
            .S_AXI_ARADDR(s_axi_araddr),
            .S_AXI_ARLEN(s_axi_arlen),
            .S_AXI_ARSIZE(s_axi_arsize),
            .S_AXI_ARBURST(s_axi_arburst),
            .S_AXI_ARLOCK(s_axi_arlock),
            .S_AXI_ARCACHE(s_axi_arcache),
            .S_AXI_ARPROT(s_axi_arprot),
            .S_AXI_ARQOS(s_axi_arqos),
            // AXI read data channel signals
            .S_AXI_RVALID(s_axi_rvalid),  // Rd rslt valid
            .S_AXI_RREADY(s_axi_rready),  // Rd rslt ready
            .S_AXI_RID(s_axi_rid), // Response ID
            .S_AXI_RDATA(s_axi_rdata),// Read data
            .S_AXI_RLAST(s_axi_rlast),   // Read last
            .S_AXI_RRESP(s_axi_rresp),   // Read response
            // We'll share the clock and the reset
            .o_reset(),
            .o_wb_cyc(wb_cyc),
            .o_wb_stb(wb_stb),
            .o_wb_we(wb_we),
            .o_wb_addr(wb_addr),
            .o_wb_data(o_wb_data),
            .o_wb_sel(wb_sel),
            .i_wb_stall(wb_stall),
            .i_wb_ack(wb_ack),
            .i_wb_data(i_wb_data),
            .i_wb_err(0)
        );



endmodule
    
