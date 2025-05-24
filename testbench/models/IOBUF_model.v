`timescale  1 ps / 1 ps



module IOBUF_model (
    output O, 
    inout IO, 
    input I, 
    input T
);

    parameter IBUF_LOW_PWR = "TRUE";
    parameter SLEW = "SLOW";
    `ifdef NO_TEST_MODEL
        parameter TEST_MODEL = 0;
    `else
        parameter TEST_MODEL = 1;
    `endif


    bufif0 T1 (IO, I, T);
    buf B1 (O, IO);

    generate
        if(TEST_MODEL == 1) begin
            reg unequal = 0;
            wire O_test, IO_test;
            bufif0 (IO_test, IO, 1'b0);

            IOBUF #(
                .IBUF_LOW_PWR("FALSE"), // Low Power - "TRUE", High Performance = "FALSE"
                .SLEW("FAST") // Specify the output slew rate
            ) IOBUF_test_model (
                .O(O_test),// Buffer output
                .IO(IO_test), // Buffer inout port (connect directly to top-level port)
                .I(I), // Buffer input
                .T(T) // 3-state enable input, high=read, low=write
            );
            always @* begin
            #1;
            if((O !== O_test) && ($time > 500_000)) begin 
                $display("IOBUF MODEL O does not match: time = %t", $time);
                unequal <= 1;
                $stop;
            end
            if((IO != IO_test) && ($time > 500_000)) begin
                $display("IOBUF MODEL IO does not match: time = %t", $time);
                unequal <= 1;
                $stop;
            end
            end

            initial begin
                $display("---------------------------------------- TESTING IOBUF Model ----------------------------------------");
            end
        end
    endgenerate
    
endmodule


