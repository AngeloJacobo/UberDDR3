`timescale 1ns / 1ps

module spd_reader_tb;
    reg clk, rst_n;
    wire scl, sda;

    // spd_reader DUT (
    //     .i_clk(clk),
    //     .i_rst_n(rst_n),
    //     .i2c_scl(scl),
    //     .i2c_sda(sda)
    // );  
    spd_reader_top DUT (
        // clock and reset
        .sys_clk_p(clk),
        .sys_clk_n(!clk),
        .i_rst_n(rst_n),
        // i2c interface
        .i2c_scl(scl),
        .i2c_sda(sda)
    );

    initial begin
        clk = 0;
        rst_n = 0;
        #100;
        rst_n = 1;
        wait(DUT.spd_reader_inst.read_spd_done);
        #10_000;
        $stop;
    end
    always #2.5 clk = !clk; // 200MHz

    pullup pullup_scl(scl); // pullup scl line
    pullup pullup_sda(sda); // pullup sda line

    i2c_slave i2c_slave(
        .scl(scl),
        .sda(sda)
    );
endmodule