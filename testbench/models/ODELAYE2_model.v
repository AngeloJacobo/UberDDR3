`timescale  1 ps / 1 ps


module ODELAYE2_model (
    output reg DATAOUT, 
    input wire C, 
    input wire[4:0] CNTVALUEIN, 
    input wire LD, 
    input wire ODATAIN, 

    // NOT MODELLED
    output wire[4:0] CNTVALUEOUT, 
    input wire CE, 
    input wire CINVCTRL, 
    input wire CLKIN, 
    input wire INC, 
    input wire LDPIPEEN,
    input wire REGRST
);

parameter CINVCTRL_SEL = "FALSE";
parameter DELAY_SRC = "ODATAIN";
parameter HIGH_PERFORMANCE_MODE    = "FALSE";
parameter [0:0] IS_C_INVERTED = 1'b0;
parameter [0:0] IS_ODATAIN_INVERTED = 1'b0;
parameter ODELAY_TYPE  = "FIXED";
parameter integer ODELAY_VALUE = 0;
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
    if(DELAY_SRC != "ODATAIN") begin
        $display("DELAY_SRC must be ODATAIN!");
        $stop;
    end
    if(ODELAY_TYPE != "VAR_LOAD" && ODELAY_TYPE != "FIXED") begin
        $display("ODELAY_TYPE must be VAR_LOAD or FIXED!");
        $stop;
    end
    if(REFCLK_FREQUENCY != 200) begin
        $display("REFCLK_FREQUENCY must be 200!");
        $stop;
    end
end

integer delay_value;
always @(ODATAIN) DATAOUT <= #(delay_value) ODATAIN;
generate
    //---------------------------------------------------------------------------------------//
    //----------------------------------- ODELAY_TYPE = VAR_LOAD ----------------------------//
    //---------------------------------------------------------------------------------------//
    if(ODELAY_TYPE == "VAR_LOAD") begin
        initial delay_value = 600;
        always @(posedge C) begin
            if(LD) begin
                delay_value <= 600 + 78*CNTVALUEIN;
            end
        end

        if(TEST_MODEL == 1) begin
            wire DATAOUT_test;
            reg unequal = 0;

            ODELAYE2 #(
                .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter to 5ps ("TRUE"), Reduced power but high jitter 9ns ("FALSE")
                .ODELAY_TYPE("VAR_LOAD"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .ODELAY_VALUE(0), // Output delay tap setting (0-31)
                .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
            )
            ODELAYE2_test_model_var_load (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(DATAOUT_test), // 1-bit output: Delayed data/clock output
                .C(C), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(1'b0), // 1-bit input: Dynamic clock inversion input
                .CLKIN(1'b0), // 1-bit input: Clock delay input
                .CNTVALUEIN(CNTVALUEIN), // 5-bit input: Counter value input
                .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                .LD(LD), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                            // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                .LDPIPEEN(1'b0), // 1-bit input: Enables the pipeline register to load data
                .ODATAIN(ODATAIN), // 1-bit input: Output delay data input
                .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
            );

            // check if delayed signal matches with the actual ODELAY primitive, if not then stop simulation
            always @* begin
                #1;
                if((DATAOUT_test !== DATAOUT) && ($time > 500_000)) begin
                    $display("ODELAYE2 MODEL does not match: time = %t", $time);
                    unequal <= 1;
                    $stop;
                end
            end
            initial begin
                $display("---------------------------------------- TESTING ODELAYE2 Model ----------------------------------------");
            end
        end
    end
    //---------------------------------------------------------------------------------------//
    //----------------------------------- ODELAY_TYPE = FIXED -------------------------------//
    //---------------------------------------------------------------------------------------//
    else if(ODELAY_TYPE == "FIXED") begin
        initial delay_value = 600 + 78*ODELAY_VALUE;
        if(TEST_MODEL == 1) begin
            wire DATAOUT_test;
            reg unequal = 0;

            ODELAYE2 #(
                .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter to 5ps ("TRUE"), Reduced power but high jitter 9ns ("FALSE")
                .ODELAY_TYPE("FIXED"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .ODELAY_VALUE(ODELAY_VALUE), // Output delay tap setting (0-31)
                .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
            )
            ODELAYE2_test_model_fixed (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(DATAOUT_test), // 1-bit output: Delayed data/clock output
                .C(C), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(1'b0), // 1-bit input: Dynamic clock inversion input
                .CLKIN(1'b0), // 1-bit input: Clock delay input
                .CNTVALUEIN(0), // 5-bit input: Counter value input
                .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                .LD(LD), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                            // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                .LDPIPEEN(1'b0), // 1-bit input: Enables the pipeline register to load data
                .ODATAIN(ODATAIN), // 1-bit input: Output delay data input
                .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
            );
            // check if delayed signal matches with the actual ODELAY primitive, if not then stop simulation
            always @* begin
                #1;
                if((DATAOUT_test !== DATAOUT) && ($time > 500_000)) begin
                    $display("ODELAYE2 MODEL does not match: time = %t", $time);
                    unequal <= 1;
                    $stop;
                end
            end
            initial begin
                $display("---------------------------------------- TESTING ODELAYE2 Model ----------------------------------------");
            end
        end
    end
endgenerate
    
endmodule // ODELAYE2

`endcelldefine
