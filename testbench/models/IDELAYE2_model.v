`timescale  1 ps / 1 ps

module IDELAYE2_model (
    output reg DATAOUT, 
    input wire C, 
    input wire[4:0] CNTVALUEIN, 
    input wire LD, 
    input wire IDATAIN, 

    // NOT MODELLED
    input wire[4:0] CNTVALUEOUT, 
    input wire CE, 
    input wire CINVCTRL, 
    input wire DATAIN, 
    input wire INC, 
    input wire LDPIPEEN, 
    input wire REGRST
);

    parameter CINVCTRL_SEL = "FALSE";
    parameter DELAY_SRC = "IDATAIN";
    parameter HIGH_PERFORMANCE_MODE    = "FALSE";
    parameter IDELAY_TYPE  = "FIXED";
    parameter integer IDELAY_VALUE = 0;
    parameter PIPE_SEL = "FALSE";
    parameter real REFCLK_FREQUENCY = 200.0;
    parameter SIGNAL_PATTERN    = "DATA";
    `ifdef NO_TEST_MODEL
        parameter TEST_MODEL = 0;
    `else
        parameter TEST_MODEL = 1;
    `endif

    // stop simulation if this modelfile does not support the settings
    initial begin
        if(DELAY_SRC != "IDATAIN") begin
            $display("DELAY_SRC must be IDATAIN!");
            $stop;
        end
        if(IDELAY_TYPE != "VAR_LOAD") begin
            $display("IDELAY_TYPE must be VAR_LOAD!");
            $stop;
        end
        if(REFCLK_FREQUENCY != 200) begin
            $display("REFCLK_FREQUENCY must be 200!");
            $stop;
        end
    end
    integer delay_value;
    initial DATAOUT = 0;
    always @(IDATAIN) DATAOUT <= #(delay_value) IDATAIN;

    initial delay_value = 600;
    always @(posedge C) begin
        if(LD) begin
            delay_value <= 600 + 78*CNTVALUEIN;
        end
    end
    generate 
        if(TEST_MODEL == 1) begin
            wire DATAOUT_test;
            reg unequal = 0;

            IDELAYE2 #(
                .DELAY_SRC("IDATAIN"), // Delay input (IDATAIN, DATAIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), //Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .IDELAY_TYPE("VAR_LOAD"), //FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .IDELAY_VALUE(0), //Input delay tap setting (0-31)
                .PIPE_SEL("FALSE"),  //Select pipelined mode, FALSE, TRUE
                .REFCLK_FREQUENCY(200.0), //IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("CLOCK") //DATA, CLOCK input signal
            )
            IDELAYE2_test_model (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(DATAOUT_test), // 1-bit output: Delayed data output
                .C(C), // 1-bit input: Clock input
                .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(1'b0),// 1-bit input: Dynamic clock inversion input
                .CNTVALUEIN(CNTVALUEIN), // 5-bit input: Counter value input
                .DATAIN(), //1-bit input: Internal delay data input
                .IDATAIN(IDATAIN), // 1-bit input: Data input from the I/O
                .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                .LD(LD), // 1-bit input: Load IDELAY_VALUE input
                .LDPIPEEN(1'b0), // 1-bit input: Enable PIPELINE register to load data input
                .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
            );

            // check if delayed signal matches with the actual IDELAY primitive, if not then stop simulation
            always @* begin
                #100;
                if((DATAOUT_test !== DATAOUT) && ($time > 500_000)) begin
                    $display("IDELAYE2 MODEL does not match: time = %t", $time);
                    unequal <= 1;
                    $stop;
                end
            end
            initial begin
                $display("---------------------------------------- TESTING IDELAYE2 Model ----------------------------------------");
            end
        end
    endgenerate
endmodule 

