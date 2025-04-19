`default_nettype none
`timescale 1ps / 1ps

module oserdes_soft #(parameter LATTICE_ECP5 = 1) (
    input wire CLK, // High-speed clock (data sampling clock)
    input wire CLKDIV, // Divided clock (must be synchronous to CLK, typically CLK/4 for DDR)
    input wire RST, // Active high reset
    input wire D1, // First data bit
    input wire D2, // Second data bit
    input wire D3, // Third data bit
    input wire D4, // Fourth data bit
    input wire D5, // Fifth data bit
    input wire D6, // Sixth data bit
    input wire D7, // Seventh data bit
    input wire D8, // Eighth data bit
    output wire OQ // Serialized output data
);
    
    // Reset signal synchronized to CLKDIV domain
    reg reset_clk_div = 1'b1; 
    reg[1:0] counter_clk = 2'd0; // 2-bit counter to track which data pair to output
    reg[1:0] oq_pair = 2'd0; // 2-bit register to hold serialized data output
    
    // Synchronize reset signal to CLKDIV domain
    always @(posedge CLKDIV) begin
        if (RST) begin
            reset_clk_div <= 1'b1;
        end else begin
            reset_clk_div <= 1'b0;
        end
    end
    
    // 2-bit counter increments on each CLK cycle to select the correct data pair
    always @(posedge CLK) begin
        if (reset_clk_div) begin
            counter_clk <= 2'd0; // Reset counter when reset is active
        end else begin
            counter_clk <= counter_clk + 2'd1; // Increment counter every clock cycle
        end
    end
    
    // Multiplexer logic: Selects two bits at a time from the 8-bit input data
    always @(posedge CLK) begin
        case (counter_clk)
            2'd0: oq_pair <= {D2, D1}; // First 2 bits
            2'd1: oq_pair <= {D4, D3}; // Second 2 bits
            2'd2: oq_pair <= {D6, D5}; // Third 2 bits
            2'd3: oq_pair <= {D8, D7}; // Fourth 2 bits
        endcase
    end
    
    generate 
        if(LATTICE_ECP5) begin
            // Instantiating ODDRX1F primitive for DDR output data serialization
            ODDRX1F ODDRX1F_inst (
                .SCLK(CLK), // High-speed clock
                .RST(reset_clk_div), // Reset signal synchronized to CLKDIV
                .D0(oq_pair[0]), // First bit of selected pair
                .D1(oq_pair[1]), // Second bit of selected pair
                .Q(OQ) // Serialized DDR output
            );
        end
        else begin // XILINX
            ODDR 
            #(.DDR_CLK_EDGE("SAME_EDGE")) ODDR_inst
            (
                .C(CLK), // High-speed clock
                .R(reset_clk_div), // Reset signal synchronized to CLKDIV
                .S(1'b0), // Set
                .CE(1'b1),
                .D1(oq_pair[0]), // First bit of selected pair
                .D2(oq_pair[1]), // Second bit of selected pair
                .Q(OQ) // Serialized DDR output
            );
        end
    endgenerate
    
endmodule
