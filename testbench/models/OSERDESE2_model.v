`timescale 1 ps / 1 ps 

module OSERDESE2_model (
  // Clocks and reset
  input wire CLK,
  input wire CLKDIV,
  input wire RST,
  // D1 - D8: Parallel data inputs
  input wire D1,
  input wire D2,
  input wire D3,
  input wire D4,
  input wire D5,
  input wire D6,
  input wire D7,
  input wire D8,
  // Buffer input/output for tristate controlle
  input wire T1,
  output reg TQ,
  // Serial output
  output wire OFB,
  output reg OQ,

  // NOT MODELLED
  output wire SHIFTOUT1,
  output wire SHIFTOUT2,
  output wire TBYTEOUT,
  output wire TFB,
  input wire OCE,
  input wire TCE,
  input wire SHIFTIN1,
  input wire SHIFTIN2,
  input wire T2,
  input wire T3,
  input wire T4,
  input wire TBYTEIN
);
  parameter DATA_RATE_OQ = "DDR";
  parameter DATA_RATE_TQ = "DDR";
  parameter integer DATA_WIDTH = 4;
  parameter [0:0] INIT_OQ = 1'b0;
  parameter [0:0] INIT_TQ = 1'b0;
  parameter integer TRISTATE_WIDTH = 4;
  `ifdef NO_TEST_MODEL
      parameter TEST_MODEL = 0;
  `else
      parameter TEST_MODEL = 1;
  `endif

  // stop simulation if this modelfile does not support the settings
  initial begin
    if(DATA_RATE_OQ == "SDR" && DATA_WIDTH != 4) begin
      $display("DATA_WIDTH must be 4 if DATA_RATE_OQ is SDR");
      $stop;
    end
    if(DATA_RATE_OQ == "DDR" && DATA_WIDTH != 8) begin
      $display("DATA_WIDTH must be 8 if DATA_RATE_OQ is DDR");
      $stop;
    end
  end

  reg[7:0] D_clkdiv_q;
  reg[7:0] D_clk_q;
  reg[2:0] counter = 0;
  reg clk_delayed;
  reg D1_delayed;
  reg D2_delayed;
  reg D3_delayed;
  reg D4_delayed;
  reg D5_delayed;
  reg D6_delayed;
  reg D7_delayed;
  reg D8_delayed;

  always @(CLK) clk_delayed <= #100 CLK;
  always @(D1) D1_delayed <= #100 D1;
  always @(D2) D2_delayed <= #100 D2;
  always @(D3) D3_delayed <= #100 D3;
  always @(D4) D4_delayed <= #100 D4;
  always @(D5) D5_delayed <= #100 D5;
  always @(D6) D6_delayed <= #100 D6;
  always @(D7) D7_delayed <= #100 D7;
  always @(D8) D8_delayed <= #100 D8;
  always @(T1) TQ <= #100 T1;

  generate
    //---------------------------------------------------------------------------------------//
    //----------------------------------- DATA RATE = DDR -----------------------------------//
    //---------------------------------------------------------------------------------------//
    if(DATA_RATE_OQ == "DDR") begin
      // reset the counter on CLKDIV posedge to make sure first CLK posedge has counter == 0
      always @(posedge CLKDIV) begin
        if(RST) begin
          counter <= 0;
        end
      end

      // serialize out the D_clk_q on both edges
      always @(posedge clk_delayed or negedge clk_delayed) begin
        OQ <= D_clk_q[counter];
        if(!(counter == 0 && !clk_delayed)) begin // should never happen where counter will increment up from zero @negedge (only @posedge will 0 increments to 1)
          counter <= counter + 1; // counts from 0->1->2->...->7->0..
        end
      end

      always @(posedge CLK) begin
        if(counter == 0) begin // store D1-D8 at first CLK posedge after CLKDIV posedge (in short the time when counter == 0)
          D_clkdiv_q <= {D8,D7,D6,D5,D4,D3,D2,D1};
          D_clk_q <= D_clkdiv_q;
        end
        if(RST) begin
          D_clkdiv_q <= 0;
          D_clk_q <= 0;
        end
      end
      // OFB output is just same as OQ
      assign OFB = OQ;

      if(TEST_MODEL == 1) begin // if model needs to be tested if it matches with the outputs from actual OSERDES primitive
        wire OQ_test, TQ_test;
        reg unequal = 0;

        OSERDESE2 #(
            .DATA_RATE_OQ("DDR"), // DDR, SDR
            .DATA_RATE_TQ("BUF"), // DDR, SDR
            .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
            .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
            .TRISTATE_WIDTH(1)
        )
        OSERDESE2_test_model_ddr(
            .OFB(), // 1-bit output: Feedback path for data
            .OQ(OQ_test), // 1-bit output: Data path output
            .CLK(CLK), // 1-bit input: High speed clock
            .CLKDIV(CLKDIV), // 1-bit input: Divided clock
            // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
            .D1(D1),
            .D2(D2),
            .D3(D3),
            .D4(D4),
            .D5(D5),
            .D6(D6),
            .D7(D7),
            .D8(D8), 
            .TCE(1'b0),
            .OCE(1'b1), // 1-bit input: Output data clock enable
            .RST(RST), // 1-bit input: Reset
              // unused signals but were added here to make vivado happy
            .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
            .SHIFTOUT2(),
            .TBYTEOUT(), // 1-bit output: Byte group tristate
            .TFB(), // 1-bit output: 3-state control
            .TQ(TQ_test), // 1-bit output: 3-state control
            // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
            .SHIFTIN1(0),
            .SHIFTIN2(0),
            // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
            .T1(T1),
            .T2(0),
            .T3(0),
            .T4(0),
            .TBYTEIN(0)
            // 1-bit input: Byte group tristate
        );

        // check if OQ and TQ matches with the actual OSERDES primitive, if not then stop simulation
        always @* begin
          #1;
          if((OQ !== OQ_test) && (RST === 0) && ($time > 500_000)) begin
              $display("OSERDES OQ MODEL does not match: time = %t", $time);
              unequal <= 1;
              $stop;
          end
          if((TQ !== TQ_test) && (RST === 0) && ($time > 500_000)) begin
              $display("OSERDES TQ MODEL does not match: time = %t", $time);
              unequal <= 1;
              $stop;
          end
        end
        initial begin
          $display("---------------------------------------- TESTING OSERDESE2 Model ----------------------------------------");
        end
      end // end of if(TEST_MODEL == 1)
    end // end of if(DATA_RATE_OQ == "DDR") 


    //---------------------------------------------------------------------------------------//
    //----------------------------------- DATA RATE = SDR -----------------------------------//
    //---------------------------------------------------------------------------------------//
    if(DATA_RATE_OQ == "SDR") begin
      // reset the counter on CLKDIV posedge to make sure first CLK posedge has counter == 0
      always @(posedge CLKDIV) begin
        if(RST) begin
          counter <= 0;
        end
      end

      // serialize out the D_clk_q on both edges
      always @(posedge clk_delayed) begin
        case(counter) 
          0: OQ <= D_clk_q[0];
          1: OQ <= D_clk_q[1];
          2: OQ <= D_clk_q[2];
          3: OQ <= D_clk_q[3];
        endcase
        counter <= (counter == 3)? 0: counter + 1; // mod-4 counter
      end

      always @(posedge CLK) begin
        if(counter == 0) begin // store D1-D8 at first CLK posedge after CLKDIV posedge (in short the time when counter == 0)
          D_clkdiv_q <= {D4,D3,D2,D1};
        end
        if(counter == 0) begin
          D_clk_q <= D_clkdiv_q;
        end
        if(RST) begin
          D_clkdiv_q <= 0;
          D_clk_q <= 0;
        end
      end
      // OFB output is just same as OQ
      assign OFB = OQ;

      if(TEST_MODEL == 1) begin // if model needs to be tested if it matches with the outputs from actual OSERDES primitive
        wire OQ_test, TQ_test;
        reg unequal = 0;

        OSERDESE2 #(
            .DATA_RATE_OQ("SDR"), // DDR, SDR
            .DATA_RATE_TQ("SDR"), // DDR, SDR
            .DATA_WIDTH(4), // Parallel data width (2-8,10,14)
            .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
            .TRISTATE_WIDTH(1)
        )
        OSERDESE2_test_model_sdr(
            .OFB(), // 1-bit output: Feedback path for data
            .OQ(OQ_test), // 1-bit output: Data path output
            .CLK(CLK), // 1-bit input: High speed clock
            .CLKDIV(CLKDIV), // 1-bit input: Divided clock
            // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
            .D1(D1),
            .D2(D2),
            .D3(D3),
            .D4(D4),
            .TCE(1'b0),
            .OCE(1'b1), // 1-bit input: Output data clock enable
            .RST(RST), // 1-bit input: Reset
              // unused signals but were added here to make vivado happy
            .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
            .SHIFTOUT2(),
            .TBYTEOUT(), // 1-bit output: Byte group tristate
            .TFB(), // 1-bit output: 3-state control
            .TQ(TQ_test), // 1-bit output: 3-state control
            // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
            .SHIFTIN1(0),
            .SHIFTIN2(0),
            // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
            .T1(T1),
            .T2(0),
            .T3(0),
            .T4(0),
            .TBYTEIN(0)
            // 1-bit input: Byte group tristate
        );

        // check if OQ and TQ matches with the actual OSERDES primitive, if not then stop simulation
        always @* begin
          #1;
          if((OQ !== OQ_test) && (RST === 0) && ($time > 500_000)) begin
              $display("OSERDES OQ MODEL does not match: time = %t", $time);
              unequal <= 1;
              $stop;
          end
          if((TQ !== TQ_test) && (RST === 0) && ($time > 500_000)) begin
              $display("OSERDES TQ MODEL does not match: time = %t", $time);
              unequal <= 1;
              $stop;
          end
        end
        initial begin
          $display("---------------------------------------- TESTING OSERDESE2 Model ----------------------------------------");
        end
      end // end of if(TEST_MODEL == 1)
    end // end of if(DATA_RATE_OQ == "SDR") 

  endgenerate


endmodule

