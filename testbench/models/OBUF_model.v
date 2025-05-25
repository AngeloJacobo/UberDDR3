`timescale  1 ps / 1 ps


module OBUF_model (
    output O, 
    input I
);
parameter SLEW ="FAST";
`ifdef NO_TEST_MODEL
    parameter TEST_MODEL = 0;
`else
    parameter TEST_MODEL = 1;
`endif

bufif0 B1 (O, I, 0);

generate
    if(TEST_MODEL == 1) begin
        wire O_test;
        reg unequal = 0;

        OBUF #(
        .SLEW("FAST") // Specify the output slew rate
        ) OBUF_test_model (
            .O(O_test), // Buffer output (connect directly to top-level port)
            .I(I) // Buffer input
        );

        always @* begin
            #1;
            if((O !== O_test) && ($time > 500_000)) begin 
                $display("OBUF MODEL O does not match: time = %t", $time);
                unequal <= 1;
                $stop;
            end
        end

        initial begin
            $display("---------------------------------------- TESTING OBUF Model ----------------------------------------");
        end
    end
endgenerate

    
endmodule





