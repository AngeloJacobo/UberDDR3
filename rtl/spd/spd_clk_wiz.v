`timescale 1ps/1ps

module clk_wiz
 (
  input         clk_in1,
  output        clk_out1,
  input         reset,
  output        locked
 );
  wire        clk_out1_clk_wiz_0;


  wire clkfbout;

  PLLE2_ADV
  #(.BANDWIDTH            ("OPTIMIZED"),
    .COMPENSATION         ("INTERNAL"),
    .STARTUP_WAIT         ("FALSE"),
    .DIVCLK_DIVIDE        (1),
    .CLKFBOUT_MULT        (5), // 200 MHz * 5 = 1000 MHz
    .CLKFBOUT_PHASE       (0.000),
    .CLKOUT0_DIVIDE       (10), // 1000 MHz / 10 = 100 MHz
    .CLKOUT0_PHASE        (0.000),
    .CLKOUT0_DUTY_CYCLE   (0.500),
    .CLKIN1_PERIOD        (5.000) // 200 MHz input
  )
  plle2_adv_inst
   (
    .CLKFBOUT            (clkfbout),
    .CLKOUT0             (clk_out1_clk_wiz_0),
    .CLKFBIN             (clkfbout),
	  .CLKIN1              (clk_in1),
    .LOCKED              (locked),
    .RST                 (reset)
  );
  BUFG clkout1_buf
   (.O   (clk_out1),
    .I   (clk_out1_clk_wiz_0));
endmodule
