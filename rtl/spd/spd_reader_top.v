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
    output wire i2c_lsb,
    // fan
    output wire fan_pwm
);
    assign fan_pwm = 1'b0; // turn on fan
    assign i2c_lsb = 1'b0;
    wire clk_locked;
    wire main_clk_100;


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
        .i2c_sda(i2c_sda)
    );  


endmodule


