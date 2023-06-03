
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/13/2023 07:48:19 AM
// Design Name: 
// Module Name: ddr3_micron_sim
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ps / 1ps
`define den8192Mb
`define sg125
`define x8

module ddr3_micron_sim;
`ifdef den1024Mb
    `include "1024Mb_ddr3_parameters.vh"
`elsif den2048Mb
    `include "2048Mb_ddr3_parameters.vh"
`elsif den4096Mb
    `include "4096Mb_ddr3_parameters.vh"
`elsif den8192Mb
    `include "8192Mb_ddr3_parameters.vh"
`else
    // NOTE: Intentionally cause a compile fail here to force the users
    //       to select the correct component density before continuing
    ERROR: You must specify component density with +define+den____Mb.
`endif


 reg i_controller_clk, i_ddr3_clk;
 reg i_rst_n;
 // Wishbone Interface
 reg i_wb_cyc; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
 reg i_wb_stb; //request a transfer
 reg i_wb_we; //write-enable (1 = write, 0 = read)
 reg[$bits(ddr3_controller.i_wb_addr)-1:0] i_wb_addr; //burst-addressable {row,bank,col} 
 reg[$bits(ddr3_controller.i_wb_data)-1:0] i_wb_data; //write data, for a 4:1 controller data width is 8 times the number of pins on the device
 wire o_wb_stall; //1 = busy, cannot accept requests
 wire o_wb_ack; //1 = read/write request has completed
 wire[$bits(ddr3_controller.o_wb_data)-1:0] o_wb_data; //read data, for a 4:1 controller data width is 8 times the number of pins on the device
 // PHY Interface to DDR3 Device
  wire ck_en; // CKE
  wire cs_n; // chip select signal
  wire odt; // on-die termination
  wire ras_n; // RAS#
  wire cas_n; // CAS#
  wire we_n; // WE#
  wire reset_n;
  wire[$bits(ddr3_top.o_ddr3_addr)-1:0] addr;
  wire[$bits(ddr3_top.o_ddr3_ba_addr)-1:0] ba_addr;
  wire[$bits(ddr3_top.io_ddr3_dq)-1:0] dq;
  wire[$bits(ddr3_top.io_ddr3_dqs)-1:0] dqs;
  wire[$bits(ddr3_top.io_ddr3_dqs_n)-1:0] dqs_n;
  wire o_ddr3_clk_p, o_ddr3_clk_n;
 
 
// DDR3 Controller 
ddr3_top #(
    .ROW_BITS(14),   //width of row address
    .COL_BITS(10), //width of column address
    .BA_BITS(3), //width of bank address
    .DQ_BITS(8),  //width of DQ
    .CONTROLLER_CLK_PERIOD(5), //ns, period of clock input to this DDR3 controller module
    .DDR3_CLK_PERIOD(1.25), //ns, period of clock input to DDR3 RAM device 
    .LANES(1), //8 lanes of DQ
    .OPT_LOWPOWER(1), //1 = low power, 0 = low logic
    .OPT_BUS_ABORT(1)  //1 = can abort bus, 0 = no absort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
    ) ddr3_top
    (
        .i_controller_clk(i_controller_clk),
        .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
        .i_ref_clk(i_controller_clk),
        .i_rst_n(i_rst_n), //200MHz input clock
        // Wishbone inputs
        .i_wb_cyc(i_wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb_stb(i_wb_stb), //request a transfer
        .i_wb_we(i_wb_we), //write-enable (1 = write, 0 = read)
        .i_wb_addr(i_wb_addr), //burst-addressable {row,bank,col} 
        .i_wb_data(i_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb_sel(), //byte strobe for write (1 = write the byte)
        .i_aux(), //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
        .o_wb_ack(o_wb_ack), //1 = read/write request has completed
        .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        // PHY Interface (to be added later)
        .o_ddr3_clk_p(o_ddr3_clk_p),
        .o_ddr3_clk_n(o_ddr3_clk_n),
        .o_ddr3_cke(ck_en), // CKE
        .o_ddr3_cs_n(cs_n), // chip select signal
        .o_ddr3_odt(odt), // on-die termination
        .o_ddr3_ras_n(ras_n), // RAS#
        .o_ddr3_cas_n(cas_n), // CAS#
        .o_ddr3_we_n(we_n), // WE#
        .o_ddr3_reset_n(reset_n),
        .o_ddr3_addr(addr),
        .o_ddr3_ba_addr(ba_addr),
        .io_ddr3_dq(dq),
        .io_ddr3_dqs(dqs),
        .io_ddr3_dqs_n(dqs_n)
        ////////////////////////////////////
    );
    
    always #2500 i_controller_clk = !i_controller_clk;
    always #625 i_ddr3_clk = !i_ddr3_clk;
    initial begin
        i_controller_clk = 1;
        i_ddr3_clk = 1;
    end
    integer stored_time = 0;
    always begin
        if($rtoi($time/1000) != $rtoi(stored_time/1000)) begin
            $write("%t ", $time);
            stored_time = $time;
        end
        #10;
    end
    // DDR3 Device 
    ddr3 ddr3_0(
        .rst_n(reset_n),
        .ck(o_ddr3_clk_p),
        .ck_n(o_ddr3_clk_n),
        .cke(ck_en),
        .cs_n(cs_n),
        .ras_n(ras_n),
        .cas_n(cas_n),
        .we_n(we_n),
        .dm_tdqs(),
        .ba(ba_addr),
        .addr(addr),
        .dq(dq),
        .dqs(dqs),
        .dqs_n(dqs_n),
        .tdqs_n(),
        .odt(odt)
    );
    initial begin
        @(negedge i_controller_clk)
        i_rst_n = 0;
        i_wb_cyc = 0;
        i_wb_stb = 0;
        i_wb_we = 0;
        i_wb_addr = 0;
        i_wb_data = 0;
        @(negedge i_controller_clk)
        i_rst_n = 1;
        
        wait(ddr3_controller.state_calibrate == ddr3_controller.DONE_CALIBRATE);
        // burst read 1
        wait(!o_wb_stall);
        @(negedge i_controller_clk);
        i_wb_cyc = 1;
        i_wb_stb = 1;
        i_wb_we = 1;
        i_wb_addr = 0;
        i_wb_data = "_ANGELO_";//64'h88_77_66_55_44_33_22_11;
        @(negedge i_controller_clk);
        i_wb_addr = 1;
        i_wb_data = "_JACOBO_";//64'h00_ff_ee_dd_cc_bb_aa_99;
        @(negedge i_controller_clk);
        i_wb_stb = 0;
        i_wb_data = 0;
        /*
        #100_000;
        wait(!o_wb_stall);
        i_wb_stb = 1;
        i_wb_data = 64'h88_77_66_55_44_33_22_11;
        @(negedge i_controller_clk);
        i_wb_data = 64'h00_ff_ee_dd_cc_bb_aa_99;
        @(negedge i_controller_clk);
        i_wb_data = 64'h88_77_66_55_44_33_22_11;
        @(negedge i_controller_clk);
        i_wb_data = 64'h00_ff_ee_dd_cc_bb_aa_99;
        @(negedge i_controller_clk);
        i_wb_data = 64'h88_77_66_55_44_33_22_11;
        @(negedge i_controller_clk);
        i_wb_data = 64'h00_ff_ee_dd_cc_bb_aa_99;
        i_wb_stb = 0;
        */
        wait(!o_wb_stall);
        @(negedge i_controller_clk);
        i_wb_stb = 1;
        i_wb_we = 0;
        i_wb_addr = 0;
        //i_wb_data = 64'h88_77_66_55_44_33_22_11;
        @(negedge i_controller_clk);
        i_wb_addr = 1;
        @(negedge i_controller_clk);
        i_wb_stb = 0;
        //wait(ddr3_controller.o_wb_ack);
        
        #100_000;
        $stop;
    end
    
    
endmodule
