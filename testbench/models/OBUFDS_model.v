
`timescale 1 ps/1 ps

module OBUFDS_model (
    output wire O, 
    output wire OB, 
    input wire I
);
    `ifdef NO_TEST_MODEL
        parameter TEST_MODEL = 0;
    `else
        parameter TEST_MODEL = 1;
    `endif

    bufif0 (O, I, 1'b0);
    notif0 (OB, I, 1'b0);

    generate
        if(TEST_MODEL == 1) begin
            wire O_test, OB_test;
            reg unequal = 0;

            OBUFDS OBUFDS_test_model (
                .O(O_test), // Diff_p output (connect directly to top-level port)
                .OB(OB_test), // Diff_n output (connect directly to top-level port)
                .I(I) // Buffer input
            );

            always @* begin
                #1;
                if((O !== O_test) && ($time > 500_000)) begin
                    $display("OBUFDS MODEL O does not match: time = %t", $time);
                    unequal <= 1;
                    $stop;
                end
                if((OB !== OB_test) && ($time > 500_000)) begin
                    $display("OBUFDS MODEL OB does not match: time = %t", $time);
                    unequal <= 1;
                    $stop;
                end
            end

            initial begin
                $display("---------------------------------------- TESTING OBUFDS Model ----------------------------------------");
            end
        end
    endgenerate
endmodule

