`timescale 1ps/1ps

module clk_wiz
 (
  input         clk_in1,
  output        clk_out1,
  output        clk_out2,
  output        clk_out3,
  output        clk_out4,
  input         reset,
  output        locked
 );
  wire        clk_out1_clk_wiz_0;
  wire        clk_out2_clk_wiz_0;
  wire        clk_out3_clk_wiz_0;
  wire        clk_out4_clk_wiz_0;

  wire clkfbout;

  PLLE2_ADV
  #(.BANDWIDTH            ("OPTIMIZED"),
    .COMPENSATION         ("INTERNAL"),
    .STARTUP_WAIT         ("FALSE"),
    .DIVCLK_DIVIDE        (1),
    .CLKFBOUT_MULT        (4), // 200 MHz * 4 = 800 MHz
    .CLKFBOUT_PHASE       (0.000),
    .CLKOUT0_DIVIDE       (8), // 800 MHz / 8 = 100 MHz
    .CLKOUT0_PHASE        (0.000),
    .CLKOUT0_DUTY_CYCLE   (0.500),
    .CLKOUT1_DIVIDE       (2), // 800 MHz / 2 = 400 MHz
    .CLKOUT1_PHASE        (0.000),
    .CLKOUT1_DUTY_CYCLE   (0.500),
    .CLKOUT2_DIVIDE       (4), // 800 MHz / 4 = 200 MHz
    .CLKOUT2_PHASE        (0.000),
    .CLKOUT2_DUTY_CYCLE   (0.500),
    .CLKOUT3_DIVIDE       (2), // 800 MHz / 2 = 400 MHz
    .CLKOUT3_PHASE        (90),
    .CLKOUT3_DUTY_CYCLE   (0.500),
    .CLKIN1_PERIOD        (5.000) // 200 MHz input
  )
  plle2_adv_inst
   (
    .CLKFBOUT            (clkfbout),
    .CLKOUT0             (clk_out1_clk_wiz_0),
    .CLKOUT1             (clk_out2_clk_wiz_0),
    .CLKOUT2             (clk_out3_clk_wiz_0),
    .CLKOUT3             (clk_out4_clk_wiz_0),
    .CLKFBIN             (clkfbout),
	.CLKIN1              (clk_in1),
    .LOCKED              (locked),
    .RST                 (reset)
  );
  BUFG clkout1_buf
   (.O   (clk_out1),
    .I   (clk_out1_clk_wiz_0));
  BUFG clkout2_buf
   (.O   (clk_out2),
    .I   (clk_out2_clk_wiz_0));
  BUFG clkout3_buf
   (.O   (clk_out3),
    .I   (clk_out3_clk_wiz_0));
  BUFG clkout4_buf
   (.O   (clk_out4),
    .I   (clk_out4_clk_wiz_0));

endmodule
