////////////////////////////////////////////////////////////////////////////////
//
// Filename: spd_reader_top.v
// Project:	Top-level file for SPD reader (intended for AX7325B FPGA board)
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
`timescale 1ns / 1ps

module spd_reader_top (
    // clock and reset
    input wire sys_clk_p,
    input wire sys_clk_n,
    input wire i_rst_n,
    // i2c interface
    inout wire i2c_scl,
    inout wire i2c_sda,
    // uart tx interface
    output wire uart_tx,
    // fan
    output wire fan_pwm,
    //Debug LEDs
    output wire[3:0] led
);

    wire clk_locked;
    wire main_clk_100;
    wire find_i2c_address_done, read_spd_done;

    assign fan_pwm = 1'b0; // turn on fan from the start
    assign led[0] = find_i2c_address_done; // lights up once done
    assign led[1] = find_i2c_address_done;
    assign led[2] = read_spd_done; 
    assign led[3] = read_spd_done; 

    //===========================================================================
    //Differentia system clock to single end clock
    //===========================================================================
    wire sys_clk; // 200MHz
    IBUFGDS u_ibufg_sys_clk   
    (
        .I  (sys_clk_p),            
        .IB (sys_clk_n),          
        .O  (sys_clk)        
    );   

    //===========================================================================
    // Generate 100MHz
    //===========================================================================
    clk_wiz clk_wiz_inst
    (
    // Clock out ports
    .clk_out1(main_clk_100),
    // Status and control signals
    .reset(!i_rst_n),
    .locked(clk_locked),
    // Clock in ports
    .clk_in1(sys_clk)
    );

    //===========================================================================
    // Instantiate SPD reader
    //===========================================================================
    spd_reader spd_reader_inst (
        .i_clk(main_clk_100),
        .i_rst_n(i_rst_n && clk_locked),
        .i2c_scl(i2c_scl),
        .i2c_sda(i2c_sda),
        .uart_tx(uart_tx),
        .find_i2c_address_done(find_i2c_address_done),
        .read_spd_done(read_spd_done)
    );  


endmodule


