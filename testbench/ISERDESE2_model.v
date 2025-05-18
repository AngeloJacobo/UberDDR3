`timescale 1 ps / 1 ps 

module ISERDESE2_model (
  input wire CLK,
  input wire CLKB,
  input wire CLKDIV,
  input wire RST,
  input wire BITSLIP,
  input wire DDLY,

  output reg Q1,
  output reg Q2,
  output reg Q3,
  output reg Q4,
  output reg Q5,
  output reg Q6,
  output reg Q7,
  output reg Q8,

  // NOT MODELLED
  output wire O,
  output wire SHIFTOUT1,
  output wire SHIFTOUT2,
  input wire CE1,
  input wire CE2,
  input wire CLKDIVP,
  input wire D,
  input wire DYNCLKDIVSEL,
  input wire DYNCLKSEL,
  input wire OCLK,
  input wire OCLKB,
  input wire OFB,
  input wire SHIFTIN1,
  input wire SHIFTIN2
);

  parameter DATA_RATE = "DDR";
  parameter integer DATA_WIDTH = 4;
  parameter [0:0] INIT_Q1 = 1'b0;
  parameter [0:0] INIT_Q2 = 1'b0;
  parameter [0:0] INIT_Q3 = 1'b0;
  parameter [0:0] INIT_Q4 = 1'b0;
  parameter INTERFACE_TYPE = "MEMORY";
  parameter IOBDELAY = "NONE";
  parameter integer NUM_CE = 2;
  parameter OFB_USED = "FALSE";
  parameter [0:0] SRVAL_Q1 = 1'b0;
  parameter [0:0] SRVAL_Q2 = 1'b0;
  parameter [0:0] SRVAL_Q3 = 1'b0;
  parameter [0:0] SRVAL_Q4 = 1'b0;
  `ifdef NO_TEST_MODEL
      parameter TEST_MODEL = 0;
  `else
      parameter TEST_MODEL = 1;
  `endif
  
  // stop simulation if this modelfile does not support the settings
  initial begin
    if(DATA_RATE != "DDR" || DATA_WIDTH != 8) begin
      $display("DATA_RATE must be 8 and DATA_WIDTH must be 8!");
      $stop;
    end
    if(INTERFACE_TYPE != "NETWORKING") begin
      $display("INTERFACE_TYPE must be NETWORKING!");
      $stop;
    end
    if(IOBDELAY != "IFD") begin
      $display("IOBDELAY must be IFD!");
      $stop;
    end
    if(OFB_USED != "FALSE") begin
      $display("OFB_USED must be FALSE!");
      $stop;
    end
  end

  reg[7:0] Q_clk_0, Q_clk_1;
  reg[2:0] counter;
  reg clk_delayed, clkdiv_delayed;
  reg[2:0] bitslip_counter = 0;

  always @(CLK) clk_delayed <= #100 CLK;
  always @(CLKDIV) clkdiv_delayed <= #100 CLKDIV;
  always @(posedge CLKDIV) begin
    if(RST) begin
      counter <= 0;
    end
    if(BITSLIP) begin
      bitslip_counter <= bitslip_counter + 1;
    end
  end


  always @(posedge clk_delayed or negedge clk_delayed) begin
    counter <= counter + 1;
  end
  
  always @(posedge CLK or negedge CLK) begin
    case(counter) 
      3'd4 + bitslip_counter[2:0]: Q_clk_0[7] <= DDLY;
      3'd5 + bitslip_counter[2:0]: Q_clk_0[6] <= DDLY;
      3'd6 + bitslip_counter[2:0]: Q_clk_0[5] <= DDLY;
      3'd7 + bitslip_counter[2:0]: Q_clk_0[4] <= DDLY;
      3'd0 + bitslip_counter[2:0]: Q_clk_0[3] <= DDLY;
      3'd1 + bitslip_counter[2:0]: Q_clk_0[2] <= DDLY;
      3'd2 + bitslip_counter[2:0]: Q_clk_0[1] <= DDLY;
      3'd3 + bitslip_counter[2:0]: begin  
        Q_clk_0[0] <= DDLY;
        Q_clk_1 <= {Q_clk_0[7:1],DDLY};
      end
    endcase
  end
  always @(posedge clkdiv_delayed) begin
    Q8 <= Q_clk_1[7];
    Q7 <= Q_clk_1[6];
    Q6 <= Q_clk_1[5];
    Q5 <= Q_clk_1[4];
    Q4 <= Q_clk_1[3];
    Q3 <= Q_clk_1[2];
    Q2 <= Q_clk_1[1];
    Q1 <= Q_clk_1[0];
  end

  generate 
    if(TEST_MODEL == 1) begin
      wire Q1_test, Q2_test, Q3_test, Q4_test, Q5_test, Q6_test, Q7_test, Q8_test;
      reg unequal = 0;

      ISERDESE2 #(
        .DATA_RATE("DDR"), // DDR, SDR
        .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
        // INIT_Q1 - INIT_Q4: Initial value on the Q outputs (0/1)
        .INIT_Q1(1'b0),
        .INIT_Q2(1'b0),
        .INIT_Q3(1'b0),
        .INIT_Q4(1'b0),
        .INTERFACE_TYPE("NETWORKING"), // MEMORY, MEMORY_DDR3, MEMORY_QDR, NETWORKING, OVERSAMPLE
        .IOBDELAY("IFD"), // NONE, BOTH, IBUF, IFD
        .NUM_CE(1),// Number of clock enables (1,2)
        .OFB_USED("FALSE"), // Select OFB path (FALSE, TRUE)
        // SRVAL_Q1 - SRVAL_Q4: Q output values when SR is used (0/1)
        .SRVAL_Q1(1'b0),
        .SRVAL_Q2(1'b0),
        .SRVAL_Q3(1'b0),
        .SRVAL_Q4(1'b0)
      )
      ISERDESE2_test_model (
          .O(),
          // 1-bit output: Combinatorial output
          // Q1 - Q8: 1-bit (each) output: Registered data outputs
          .Q1(Q1_test),//56
          .Q2(Q2_test), //48
          .Q3(Q3_test),
          .Q4(Q4_test),   
          .Q5(Q5_test),
          .Q6(Q6_test),
          .Q7(Q7_test), 
          .Q8(Q8_test),
          // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
          .SHIFTOUT1(),
          .SHIFTOUT2(),
          .BITSLIP(BITSLIP),
          // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
          // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
          // to Q8 output ports will shift, as in a barrel-shifter operation, one
          // position every time Bitslip is invoked (DDR operation is different from
          // SDR).
          // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
          .CE1(1'b1),
          .CE2(1'b1),
          .CLKDIVP(), // 1-bit input: TBD
          // Clocks: 1-bit (each) input: ISERDESE2 clock input ports
          .CLK(CLK), // 1-bit input: High-speed clock
          .CLKB(CLKB), // 1-bit input: High-speed secondary clock
          .CLKDIV(CLKDIV), // 1-bit input: Divided clock
          .OCLK(), // 1-bit input: High speed output clock used when INTERFACE_TYPE="MEMORY"
          // Dynamic Clock Inversions: 1-bit (each) input: Dynamic clock inversion pins to switch clock polarity
          .DYNCLKDIVSEL(), // 1-bit input: Dynamic CLKDIV inversion
          .DYNCLKSEL(), // 1-bit input: Dynamic CLK/CLKB inversion
          // Input Data: 1-bit (each) input: ISERDESE2 data input ports
          .D(), // 1-bit input: Data input
          .DDLY(DDLY), // 1-bit input: Serial data from IDELAYE2
          .OFB(), // 1-bit input: Data feedback from OSERDESE2
          .OCLKB(), // 1-bit input: High speed negative edge output clock
          .RST(RST), // 1-bit input: Active high asynchronous reset
          // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
          .SHIFTIN1(),
          .SHIFTIN2()
      );
      // check if OQ and TQ matches with the actual OSERDES primitive, if not then stop simulation
      always @* begin
          #1;
          if(({Q8,Q7,Q6,Q5,Q4,Q3,Q2,Q1} !== {Q8_test,Q7_test,Q6_test,Q5_test,Q4_test,Q3_test,Q2_test,Q1_test}) && (RST === 0) && ($time > 500_000)) begin
              $display("ISERDES MODEL does not match: time = %t", $time);
              unequal <= 1;
              // $stop;
          end
      end
      initial begin
        $display("---------------------------------------- TESTING ISERDESE2 Model ----------------------------------------");
      end
    end
  endgenerate

endmodule

