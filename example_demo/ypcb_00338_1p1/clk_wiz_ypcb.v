`default_nettype none
`timescale 1ps / 1ps

module clk_wiz_ypcb (
    input  wire clk50,
    output wire locked,
    output wire controller_clk,
    output wire ddr3_clk,
    output wire ddr3_clk_90,
    output wire ref_clk
);
    wire clkfb;
    wire clk100_raw;
    wire clk100_90_raw;
    wire clk25_raw;
    wire clk200_raw;

    PLLE2_BASE #(
        .BANDWIDTH("OPTIMIZED"),
        .CLKFBOUT_MULT(20),
        .CLKFBOUT_PHASE(0.000),
        .CLKIN1_PERIOD(20.000),
        .CLKOUT0_DIVIDE(10),
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE(0.000),
        .CLKOUT1_DIVIDE(10),
        .CLKOUT1_DUTY_CYCLE(0.500),
        .CLKOUT1_PHASE(90.000),
        .CLKOUT2_DIVIDE(40),
        .CLKOUT2_DUTY_CYCLE(0.500),
        .CLKOUT2_PHASE(0.000),
        .CLKOUT3_DIVIDE(5),
        .CLKOUT3_DUTY_CYCLE(0.500),
        .CLKOUT3_PHASE(0.000),
        .DIVCLK_DIVIDE(1),
        .REF_JITTER1(0.010),
        .STARTUP_WAIT("FALSE")
    ) pll_inst (
        .CLKFBOUT(clkfb),
        .CLKOUT0(clk100_raw),
        .CLKOUT1(clk100_90_raw),
        .CLKOUT2(clk25_raw),
        .CLKOUT3(clk200_raw),
        .CLKOUT4(),
        .CLKOUT5(),
        .LOCKED(locked),
        .CLKFBIN(clkfb),
        .CLKIN1(clk50),
        .PWRDWN(1'b0),
        .RST(1'b0)
    );

    BUFG clk100_bufg (
        .I(clk100_raw),
        .O(ddr3_clk)
    );

    BUFG clk100_90_bufg (
        .I(clk100_90_raw),
        .O(ddr3_clk_90)
    );

    BUFG clk25_bufg (
        .I(clk25_raw),
        .O(controller_clk)
    );

    BUFG clk200_bufg (
        .I(clk200_raw),
        .O(ref_clk)
    );
endmodule

`default_nettype wire
