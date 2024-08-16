module ecc_formal;
    parameter K = 8,
        P0_LSB = 0;

    // function to find number of check bits
     function integer calculate_m;
        input integer k;
        integer m;
        begin
            m=1;
            while (2**m < m+k+1) m=m+1;
            calculate_m = m;
        end
    endfunction

    // anyseq indicates nets that are controllable by engine
    (*anyseq*)wire[K-1:0] d_i; // information input
    (*anyseq*) wire[1:0] corrupted; // 0 or 3 = not corrupted bit, 1 = 1 corrupted bit, 2 = 2 corrupted bits
    (*anyseq*) wire[$clog2(K+calculate_m(K))-1:0] corrupted_bit1, corrupted_bit2; // which bit will be corrupted

    wire[K-1:0] q_o_dec;
    wire[K+calculate_m(K):0] q_o_enc;
    reg[K+calculate_m(K):0] q_o_enc_corrupted;
    wire sb_err_o;
    wire db_err_o;

    ecc_enc #(
        .K(K), //Information bit vector size
        .P0_LSB(P0_LSB) //0: p0 is located at MSB
                    //1: p0 is located at LSB
    ) ecc_enc_inst (
        .d_i(d_i),      //information bit vector input
        .q_o(q_o_enc),  //encoded data word output
        .p_o(),      //parity vector output
        .p0_o()      //extended parity bit
    );

    ecc_dec #(
        .K(K), //Information bit vector size
        .LATENCY(0), //0: no latency (combinatorial design)
                            //1: registered outputs
                            //2: registered inputs+outputs
        .P0_LSB(P0_LSB) //0: p0 is located at MSB
                            //1: p0 is located at LSB
    ) ecc_dec_inst (
        //clock/reset ports (if LATENCY > 0)
        .rst_ni(1'b1),     //asynchronous reset
        .clk_i(1'b0),      //clock input
        .clkena_i(1'b0),   //clock enable input
        //data ports
        .d_i(q_o_enc_corrupted),        //encoded code word input
        .q_o(q_o_dec),        //information bit vector output
        .syndrome_o(), //syndrome vector output
        //flags
        .sb_err_o(sb_err_o),   //single bit error detected
        .db_err_o(db_err_o),   //double bit error detected
        .sb_fix_o()    //repaired error in the information bits
    );

    `ifdef FORMAL
        (*gclk*) reg f_clk = 0; // reference: https://symbiyosys.readthedocs.io/en/latest/verilog.html#global-clock
        reg[9:0] f_counter = 0;

        // corrupt the information based on the value of "corrupted" which is controllable by formal engine:
        // 0 = no corrupted bits , 1 = 1 corrupted bit, 2 = 2 corrupted bits, 3 = no corrupted bits
        always @* begin
            q_o_enc_corrupted = q_o_enc;
            if(corrupted == 1) begin 
                q_o_enc_corrupted[corrupted_bit1] = !q_o_enc_corrupted[corrupted_bit1]; //corrupt 1 random bit
                assume(corrupted_bit1 != (K+calculate_m(K))); //
            end
            else if (corrupted == 2) begin // flip 2 bits
                q_o_enc_corrupted[corrupted_bit1] = !q_o_enc_corrupted[corrupted_bit1]; //corrupt 2 random bits 
                q_o_enc_corrupted[corrupted_bit2] = !q_o_enc_corrupted[corrupted_bit2];
            end
            assume(corrupted_bit1 != corrupted_bit2); // corrupted bit should be different (in case of 2 corrupted bits)
            assume(corrupted_bit1 <= (K+calculate_m(K))); // corrupted bit should be within the index of q_o_enc_corrupted
            assume(corrupted_bit2 <= (K+calculate_m(K))); // corrupted bit should be within the index of q_o_enc_corrupted
        end

        // main contract of this design
        always @* begin
            // if no corrupted bits, then decoded info must be equal to original info, and error flags should be low
            // OR there is 1 corrupted bit but its the MSB p0 that is corrupted 
            if( (corrupted == 0 || corrupted == 3) || ( (corrupted == 1) && (corrupted_bit1 == (K+calculate_m(K))) ) ) begin
                assert(d_i == q_o_dec);
                assert(!sb_err_o);
                assert(!db_err_o);
            end
            // if 1 corrupted bit, then decoded info must still be equal to original info, single-bit error flag must be high, double-bit error flag must be low
            else if(corrupted == 1) begin
                assert(d_i == q_o_dec);
                assert(sb_err_o);
                assert(!db_err_o);
            end
            // if 2 corrupted bits, then single-bit error flag must be low, double-bit error flag must be high
            else if(corrupted == 2) begin
                assert(!sb_err_o);
                assert(db_err_o);
            end
        end

        // cover 10 cycles
        always @(posedge f_clk) begin
            f_counter <= f_counter + 1;
            assume(corrupted == f_counter[1:0]); // number of corrupted bits change per clock cycle
            cover((f_counter == 10));
        end

        // simulate random information
        always @(posedge f_clk) begin
            assume(d_i != $past(d_i,1)); 
            assume(d_i != $past(d_i,2)); 
            assume(d_i != $past(d_i,3)); 
            assume(d_i != $past(d_i,4)); 
            assume(d_i != $past(d_i,5)); 
            assume(d_i != $past(d_i,6)); 
            assume(d_i != $past(d_i,7)); 
            assume(d_i != $past(d_i,8)); 
            assume(d_i != $past(d_i,9)); 
            assume(d_i != $past(d_i,10)); 
        end

    `endif
endmodule