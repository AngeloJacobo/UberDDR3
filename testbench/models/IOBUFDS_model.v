`timescale 1 ps / 1 ps

module IOBUFDS_model (
  output O,
  inout IO,
  inout IOB,
  input I,
  input T
);
  `ifdef NO_TEST_MODEL
      parameter TEST_MODEL = 0;
  `else
      parameter TEST_MODEL = 1;
  `endif
  parameter IBUF_LOW_PWR = "FALSE";

  assign IO  = T ? 1'bz :  I;
  assign IOB = T ? 1'bz : ~I;
  reg o_out;
  
  always @(IO or IOB) begin
    if (IO == 1'b1 && IOB == 1'b0)
      o_out <= 1'b1;
    else if (IO == 1'b0 && IOB == 1'b1)
      o_out <= 1'b0;
    else if ((IO === 1'bz || IO == 1'b0) && (IOB === 1'bz || IOB == 1'b1))
        o_out <= 1'bx;
    else if ((IO === 1'bx) || (IOB == 1'bx))
      o_out <= 1'bx;
  end

  assign O  =  o_out;


  generate 
    if(TEST_MODEL == 1) begin
      wire O_test, IO_test, IOB_test;
      reg unequal = 0;
      bufif0 (IO_test, IO, 1'b0);
      bufif0 (IOB_test, IOB, 1'b0);

      IOBUFDS IOBUFDS_test_model (
          .O(O_test), // Buffer output
          .IO(IO_test), // Diff_p inout (connect directly to top-level port)
          .IOB(IOB_test), // Diff_n inout (connect directly to top-level port)
          .I(I), // Buffer input
          .T(T) // 3-state enable input, high=input, low=output
        ); 

      always @* begin
          #1;
          if((O !== O_test) && ($time > 500_000)) begin 
              $display("IOBUFDS MODEL O does not match: time = %t", $time);
              unequal <= 1;
              $stop;
          end
          if(((IO != IO_test) || (IOB != IOB_test)) && ($time > 500_000)) begin 
              $display("IOBUFDS MODEL IO/IOB does not match: time = %t", $time);
              unequal <= 1;
              $stop;
          end
      end

      initial begin
          $display("---------------------------------------- TESTING IOBUFDS Model ----------------------------------------");
      end
    end
  endgenerate

endmodule

`endcelldefine
