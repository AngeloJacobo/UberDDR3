`default_nettype none
`timescale 1ps / 1ps

module iserdes_soft #(parameter LATTICE_ECP5 = 1) (
    input wire CLK, // High-speed clock (data sampling clock)
    input wire CLKDIV, // Divided clock (must be synchronous to CLK, typically CLK/4 for DDR)
    input wire RST, // Active high reset
    output reg Q1, // First data bit
    output reg Q2, // Second data bit
    output reg Q3, // Third data bit
    output reg Q4, // Fourth data bit
    output reg Q5, // Fifth data bit
    output reg Q6, // Sixth data bit
    output reg Q7, // Seventh data bit
    output reg Q8, // Eighth data bit
    input wire D, // Serialized input data
    input wire bitslip // bitslip changes starting_index to shift left the data
);
    
    // Reset signal synchronized to CLKDIV domain
    reg reset_clk_div = 1'b1; 
    reg[2:0] starting_index = 0;
    reg [1:0] counter_clk = 2'd0; // 2-bit counter to track which data pair to output
    wire [1:0] iq_pair; // 2-bit register to hold deserialized data input
    reg Q1_clk = 0,
        Q2_clk = 0,
        Q3_clk = 0,
        Q4_clk = 0,
        Q5_clk = 0,
        Q6_clk = 0,
        Q7_clk = 0,
        Q8_clk = 0;
    reg[7:0] Q_clk, Q_clk_temp;
    // Synchronize reset signal to CLKDIV domain
    always @(posedge CLKDIV) begin
        if (RST) begin
            reset_clk_div <= 1'b1;
            starting_index <= 3'd0;
        end else begin
            reset_clk_div <= 1'b0;
            starting_index <= bitslip? starting_index + 1 : starting_index; // increment when bitslip is issued
        end
    end
    
    // 2-bit counter increments on each CLK cycle to select the correct data pair
    always @(posedge CLK) begin
        if (reset_clk_div) begin
            counter_clk <= 0; // Reset counter when reset is active
        end else begin
            counter_clk <= counter_clk + 2'd1; // Increment counter every clock cycle
        end
    end
    
    // Capture and store deserialized data pairs
    always @(posedge CLK) begin
        case (counter_clk)
            2'd0: begin // First 2 bits
                Q1_clk <= iq_pair[0]; 
                Q2_clk <= iq_pair[1]; 
                if(starting_index == 6) begin
                    Q_clk <= Q_clk_temp; // 3 -> 0 -> 1 -> 2: {2,1.0,3}
                end
                if(starting_index == 7) begin 
                    Q_clk <= {Q7_clk,Q_clk_temp[6:0]}; // [7] is relevant
                end
                if(starting_index == 0) begin
                    Q_clk_temp <= {Q8_clk, Q7_clk, Q6_clk, Q5_clk, Q4_clk, Q3_clk, Q2_clk, Q1_clk}; // 0 -> 1 -> 2 -> 3: {3,2,1,0}
                end
                if(starting_index == 1) begin
                    Q_clk_temp <= {Q1_clk, Q8_clk, Q7_clk, Q6_clk, Q5_clk, Q4_clk, Q3_clk, Q2_clk}; // [6:0]] lsb is relevant
                end
            end
            2'd1: begin // Second 2 bits
                Q3_clk <= iq_pair[0];
                Q4_clk <= iq_pair[1]; 
                if(starting_index == 0) begin
                    Q_clk <= Q_clk_temp; // 0 -> 1 -> 2 -> 3: {3,2,1,0}
                end
                if(starting_index == 1) begin
                    Q_clk <= {Q1_clk,Q_clk_temp[6:0]}; // [7] is relevant
                end
                if(starting_index == 2) begin
                    Q_clk_temp <= {Q2_clk, Q1_clk, Q8_clk, Q7_clk, Q6_clk, Q5_clk, Q4_clk, Q3_clk}; // 1 -> 2 -> 3 -> 0: {0,3,2,1}
                end
                if(starting_index == 3) begin
                    Q_clk_temp <= {Q3_clk, Q2_clk, Q1_clk, Q8_clk, Q7_clk, Q6_clk, Q5_clk, Q4_clk}; // [6:0] is relevant
                end
            end
            2'd2: begin // Third 2 bits
                Q5_clk <= iq_pair[0];
                Q6_clk <= iq_pair[1]; 
                if(starting_index == 2) begin
                    Q_clk <= Q_clk_temp; // 1 -> 2 -> 3 -> 0: {0,3,2,1}
                end
                 if(starting_index == 3) begin
                    Q_clk <= {Q3_clk,Q_clk_temp[6:0]}; // [7] is relevant
                end
                if(starting_index == 4) begin
                    Q_clk_temp <= {Q4_clk, Q3_clk, Q2_clk, Q1_clk, Q8_clk, Q7_clk, Q6_clk, Q5_clk}; // 2 -> 3 -> 0 -> 1: {1,0.3,2}
                end
                if(starting_index == 5) begin
                    Q_clk_temp <= {Q5_clk, Q4_clk, Q3_clk, Q2_clk, Q1_clk, Q8_clk, Q7_clk, Q6_clk}; // 2 -> 3 -> 0 -> 1: {1,0.3,2}
                end
            end
            2'd3: begin // Fourth 2 bits
                Q7_clk <= iq_pair[0];
                Q8_clk <= iq_pair[1]; 
                if(starting_index == 4) begin
                    Q_clk <= Q_clk_temp; // 2 -> 3 -> 0 -> 1: {1,0.3,2}
                end
                if(starting_index == 5) begin
                    Q_clk <= {Q5_clk,Q_clk_temp[6:0]}; // [7] is relevant
                end
                if(starting_index == 6) begin
                    Q_clk_temp <= {Q6_clk, Q5_clk, Q4_clk, Q3_clk, Q2_clk, Q1_clk, Q8_clk, Q7_clk}; // 3 -> 0 -> 1 -> 2: {2,1.0,3}
                end
                if(starting_index == 7) begin
                    Q_clk_temp <= {Q7_clk, Q6_clk, Q5_clk, Q4_clk, Q3_clk, Q2_clk, Q1_clk, Q8_clk}; // 3 -> 0 -> 1 -> 2: {2,1.0,3}
                end
                // once counter_clk 0-to-3 is done, then the whole 8-bit data is complete thus we store it to Q_clk
                // Q_clk will then be sampled by next CLKDIV posedge
                // This makes sure the CLKDIV posedge samples only once counter_clk 0-to-3 is complete
            end
        endcase
    end
    
    // register the Q*_clk to CLKDIV domain
    always @(posedge CLKDIV) begin
        // 0
        Q1 <= Q_clk[0];
        Q2 <= Q_clk[1];
        // 1
        Q3 <= Q_clk[2];
        Q4 <= Q_clk[3];
        // 2
        Q5 <= Q_clk[4];
        Q6 <= Q_clk[5];
        // 3
        Q7 <= Q_clk[6];
        Q8 <= Q_clk[7];
    end
    generate
        if(LATTICE_ECP5) begin
            // Instantiate input DDR flip-flop to capture serialized data
            IDDRX1F IDDRX1F_inst (
                .SCLK(CLK), 
                .RST(reset_clk_div),
                .Q0(iq_pair[0]), 
                .Q1(iq_pair[1]), 
                .D(D) 
            );
        end
        else begin // XILINX
            IDDR 
            #(.DDR_CLK_EDGE("OPPOSITE_EDGE")) IDDR_inst 
            (
                .Q1(iq_pair[0]), // 1-bit output for positive edge of clock
                .Q2(iq_pair[1]), // 1-bit output for negative edge of clock
                .C(CLK),   // 1-bit clock input
                .CE(1'b1), // 1-bit clock enable input
                .D(D),   // 1-bit DDR data input
                .R(reset_clk_div),   // 1-bit reset
                .S(1'b0)    // 1-bit set
            );
        end
    endgenerate
        
endmodule
