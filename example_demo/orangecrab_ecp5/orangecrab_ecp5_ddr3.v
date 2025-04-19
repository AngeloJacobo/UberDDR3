////////////////////////////////////////////////////////////////////////////////
//
// Filename: orangecrab_ecp5_ddr3.v
// Project: UberDDR3 - An Open Source DDR3 Controller
//
// Purpose: Example demo of UberDDR3 for Orangecrab ECP5. Mechanism:
//          - Green LEDs will light up once UberDDR3 is done calibrating (else red light)
//          - if UART (9600 Baud Rate)receives small letter ASCII (a-z), this value will be written to DDR3 
//          - if UART receives capital letter ASCII (A-Z), the small letter equivalent will be retrieved from DDR3 by doing
//          - a read request, once read data is available this will be sent to UART to be streamed out.
//          THUS:
//          - Sendng "abcdefg" to the UART terminal will store that small latter to DDR3
//          - Then sending "ABCDEFG" to the UART terminal will return the small letter equivalent: "abcdefg"
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

   module orangecrab_ecp5_ddr3 #(parameter MICRON_SIM = 0)
	(
	input wire i_clk, // 48MHz
	input wire i_rst_n,
	// DDR3 I/O Interface
    output wire ddr3_clk_p, ddr3_clk_n,
    output wire ddr3_reset_n,
    output wire ddr3_cke, // CKE
    output wire ddr3_cs_n, // chip select signal
    output wire ddr3_ras_n, // RAS#
    output wire ddr3_cas_n, // CAS#
    output wire ddr3_we_n, // WE#
    output wire[16-1:0] ddr3_addr,
    output wire[3-1:0] ddr3_ba,
    inout wire[16-1:0] ddr3_dq,
    inout wire[2-1:0] ddr3_dqs_p, ddr3_dqs_n,
    output wire[2-1:0] ddr3_dm,
    output wire ddr3_odt, // on-die termination
    output wire[6-1:0] ddram_vccio,
    output wire[2-1:0] ddram_gnd,
    // UART line
	input wire rx,
	output wire tx,
	//Debug LEDs
	output wire rgb_led0_r, rgb_led0_g, rgb_led0_b
    );
    // Note from https://orangecrab-fpga.github.io/orangecrab-hardware/docs/r0.2.1/:
    // Virtual VCCIO and GND are connected to VCCIO and GND on the PCB. 
    // They should be driven HIGH and LOW respectively to reduce SSO noise on the DDR3 I/O bank.
    assign ddram_vccio = 6'b111111;
    assign ddram_gnd = 2'b00;

    wire i_controller_clk, i_ddr3_clk, i_ddr3_clk_90;
    wire m_axis_tvalid;
    wire rx_empty;
    wire tx_full;
    wire o_wb_ack;
    wire[7:0] o_wb_data;
    wire[7:0] rd_data;
    wire o_wb_stall;
    reg i_wb_stb = 0, i_wb_we;
    wire[31:0] o_debug1;
    reg[7:0] i_wb_data;
    reg[7:0] i_wb_addr;

    // o_debug1 taps on value of state_calibrate (can be traced inside ddr3_controller module)
    assign rgb_led0_r = !(o_debug1[4:0] != 23); // red light when not yet done
    assign rgb_led0_g = !(o_debug1[4:0] == 23); // green light when done
    assign rgb_led0_b = 1'b1; // always off

    always @(posedge i_controller_clk) begin
        begin
            i_wb_stb <= 0;
            i_wb_we <= 0;
            i_wb_addr <= 0;
            i_wb_data <= 0;
            if(!o_wb_stall && m_axis_tvalid) begin
                if(rd_data >= 97 && rd_data <= 122) begin //write to DDR3 if ASCII is small letter
                    i_wb_stb <= 1;                 
                    i_wb_we <= 1;                  
                    i_wb_addr <= ~rd_data ;                
                    i_wb_data <= rd_data; 
                end
                else if(rd_data >= 65 && rd_data <= 90) begin //read from DDR3 if ASCII is capital letter
                    i_wb_stb <= 1; //make request
                    i_wb_we <= 0; //read
                    i_wb_addr <= ~(rd_data + 8'd32);
                end
            end
        end
    end
     
    wire clk_locked;
    // generated from ecppll:
    // ecppll -n clk_wiz --clkin_name CLKI --clkin 48 --clkout0_name CLKOP --clkout0 24 --clkout1_name CLKOS --clkout1 24 --phase1 90 --clkout2_name CLKOS2 --clkout2 6 -f clk_wiz_ecppll.v --reset
    clk_wiz clk_wiz_inst
    (
        .reset(!i_rst_n), // 0:inactive, 1:reset
        .CLKI(i_clk), // 48 MHz, 0 deg
        .CLKOP(i_ddr3_clk), // 24 MHz, 0 deg
        .CLKOS(i_ddr3_clk_90), // 24 MHz, 90 deg
        .CLKOS2(i_controller_clk), // 6 MHz, 0 deg
        .locked(clk_locked)
    );
    
    // UART TX/RXmodule from https://github.com/ben-marshall/uart
    uart_tx #(
        .BIT_RATE(9600),
        .CLK_HZ(6_000_000),
        .PAYLOAD_BITS(8),
        .STOP_BITS(1)
        ) uart_tx_inst (
        .clk(i_controller_clk), // Top level system clock input.
        .resetn(i_rst_n && clk_locked && o_debug1[4:0] == 23), // Asynchronous active low reset.
        .uart_txd(), // UART transmit pin.
        .uart_tx_busy(), // Module busy sending previous item.
        .uart_tx_en(o_wb_ack), // Send the data on uart_tx_data
        .uart_tx_data(o_wb_data) // The data to be sent
    );
    uart_rx #(
        .BIT_RATE(9600),
        .CLK_HZ(6_000_000),
        .PAYLOAD_BITS(8),
        .STOP_BITS(1)
    ) uart_rx_inst (
        .clk(i_controller_clk), // Top level system clock input.
        .resetn(i_rst_n && clk_locked && o_debug1[4:0] == 23), // Asynchronous active low reset.
        .uart_rxd(rx), // UART Recieve pin.
        .uart_rx_en(o_debug1[4:0] == 23), // Recieve enable
        .uart_rx_break(), // Did we get a BREAK message?
        .uart_rx_valid(m_axis_tvalid), // Valid data recieved/available.
        .uart_rx_data(rd_data)   // The recieved data.
    );

    // DDR3 Controller 
    ddr3_top #(
        .CONTROLLER_CLK_PERIOD(25_000), //ps, clock period of the controller interface
        .DDR3_CLK_PERIOD(6_250), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
        .ROW_BITS(13), //width of row address
        .COL_BITS(10), //width of column address
        .BA_BITS(3), //width of bank address
        .BYTE_LANES(2), //number of DDR3 modules to be controlled
        .AUX_WIDTH(16), //width of aux line (must be >= 4) 
        .WB2_ADDR_BITS(32), //width of 2nd wishbone address bus 
        .WB2_DATA_BITS(32), //width of 2nd wishbone data bus
        .MICRON_SIM(MICRON_SIM), //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
        .SECOND_WISHBONE(0), //set to 1 if 2nd wishbone is needed 
        .ECC_ENABLE(0), // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC ) 
        .WB_ERROR(0), // set to 1 to support Wishbone error (asserts at ECC double bit error)
        .DLL_OFF(1), // 1 = DLL off for low frequency ddr3 clock 
        .BIST_MODE(1) // 0 = No BIST, 1 = run through all address space ONCE , 2 = run through all address space for every test (burst w/r, random w/r, alternating r/w)
        ) ddr3_top
        (
            //clock and reset
            .i_controller_clk(i_controller_clk),
            .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
            .i_ref_clk(1'b0),
            .i_ddr3_clk_90(i_ddr3_clk_90),
            .i_rst_n(i_rst_n && clk_locked), 
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
            .o_wb_err(), //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
            .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
            .o_aux(),
            // Wishbone 2 (PHY) inputs
            .i_wb2_cyc(), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb2_stb(), //request a transfer
            .i_wb2_we(), //write-enable (1 = write, 0 = read)
            .i_wb2_addr(), //burst-addressable {row,bank,col} 
            .i_wb2_data(), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_wb2_sel(), //byte strobe for write (1 = write the byte)
            // Wishbone 2 (Controller) outputs
            .o_wb2_stall(), //1 = busy, cannot accept requests
            .o_wb2_ack(), //1 = read/write request has completed
            .o_wb2_data(), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
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
            .o_debug1(o_debug1),
            .uart_tx(tx)
        );

endmodule

