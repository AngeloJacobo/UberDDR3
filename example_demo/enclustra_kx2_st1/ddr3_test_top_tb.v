////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_test_top.v
// Project: Testbench for ddr3_test_top.v
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

`timescale 1ps / 1ps

module ddr3_test_top_tb;    
    // PHY Interface to DDR3 Device
    wire[1:0] ddr3_cke; // CKE
    wire[1:0] ddr3_cs_n; // chip select signal
    wire[1:0] ddr3_odt; // on-die termination
    wire ddr3_ras_n; // RAS#
    wire ddr3_cas_n; // CAS#
    wire ddr3_we_n; // WE#
    wire ddr3_reset_n;
    wire[$bits(DUT.ddr3_addr)-1:0] ddr3_addr;
    wire[$bits(DUT.ddr3_ba)-1:0] ddr3_ba;
    wire[$bits(DUT.ddr3_dm)-1:0] ddr3_dm;
    wire[$bits(DUT.ddr3_dq)-1:0] ddr3_dq;
    wire[$bits(DUT.ddr3_dqs_p)-1:0] ddr3_dqs_p;
    wire[$bits(DUT.ddr3_dqs_n)-1:0] ddr3_dqs_n;
    wire[1:0] ddr3_clk_p, ddr3_clk_n;
    // clocks and reset
    reg i_clk200_p;
    reg i_rst_n;
    initial begin
        i_clk200_p = 0;
        i_rst_n = 0;
        #1000;
        i_rst_n = 1;
    end
    always #2_500 i_clk200_p = !i_clk200_p; // 200MHz


    enclustra_ddr3_test #(
        .MICRON_SIM(1), 
        .ODELAY_SUPPORTED(1),
        .DATA_MASK(1)
    ) 
    DUT (
        .i_clk200_p(i_clk200_p),
        .i_clk200_n(!i_clk200_p),
        .i_rst_n(i_rst_n),
        // DDR3 I/O Interface
        .ddr3_clk_p(ddr3_clk_p),
        .ddr3_clk_n(ddr3_clk_n),
        .ddr3_reset_n(ddr3_reset_n),
        .ddr3_cke(ddr3_cke),
        .ddr3_cs_n(ddr3_cs_n),
        .ddr3_ras_n(ddr3_ras_n),
        .ddr3_cas_n(ddr3_cas_n),
        .ddr3_we_n(ddr3_we_n),
        .ddr3_addr(ddr3_addr),
        .ddr3_ba(ddr3_ba),
        .ddr3_dq(ddr3_dq),
        .ddr3_dqs_p(ddr3_dqs_p),
        .ddr3_dqs_n(ddr3_dqs_n),
        .ddr3_dm(ddr3_dm),
        .ddr3_odt(ddr3_odt),
        // UART line
        .rx(0),
        .tx(),
        // Debug LEDs
        .led()
    );

    // DDR3 Device 
    ddr3_module ddr3_module(
        .reset_n(ddr3_reset_n),
        .ck(ddr3_clk_p), //[1:0]
        .ck_n(ddr3_clk_n), //[1:0]
        .cke(ddr3_cke), //[1:0]
        .s_n(ddr3_cs_n), //[1:0]
        .ras_n(ddr3_ras_n),
        .cas_n(ddr3_cas_n),
        .we_n(ddr3_we_n),
        .ba(ddr3_ba),
        .addr({0,ddr3_addr}),
        .odt(ddr3_odt), //[1:0]
        .dqs({ddr3_dm[0], ddr3_dm,ddr3_dm[0],ddr3_dqs_p}), //ddr3_module uses last 8 MSB [16:9] as datamask
        .dqs_n(ddr3_dqs_n),
        .dq(ddr3_dq)
    );
    assign ddr3_cke[1]=0,
            ddr3_cs_n[1]=1,
            ddr3_odt[1]=0,
            ddr3_clk_p[1]=0,
            ddr3_clk_n[1]=0; 

endmodule

