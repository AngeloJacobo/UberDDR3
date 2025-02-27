////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_test.v
// Project: Test the UberDDR3 by sending traffic via the Wishbone interface
//
// Purpose: Sends traffic over Wishbone interface of UberDDR3. This has 3 tests:
//  - burst write/read
//  - random write/read
//  - alternating write/read
// Uses MicroBlaze to report via UART the number of read matches, mismatches, and
// total time elapsed. Report summary is sent every second.
//
// Engineer: Angelo C. Jacobo
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2023-2025  Angelo Jacobo
// 
//     This program is free software: you can redistribute it and/or modify
//     it under the terms of the GNU General Public License as published by
//     the Free Software Foundation, either version 3 of the License, or
//     (at your option) any later version.
// 
//     This program is distributed in the hope that it will be useful,
//     but WITHOUT ANY WARRANTY; without even the implied warranty of
//     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//     GNU General Public License for more details.
// 
//     You should have received a copy of the GNU General Public License
//     along with this program.  If not, see <https://www.gnu.org/licenses/>.
//
////////////////////////////////////////////////////////////////////////////////

// `default_nettype none
`timescale 1ps / 1ps

module ddr3_test #(
    parameter   WB_ADDR_BITS = 25,
                WB_DATA_BITS = 512,
                WB_SEL_BITS = WB_DATA_BITS / 8,
                AUX_WIDTH = 4,
                DATA_MASK = 1,
    parameter[0:0] MICRON_SIM = 0
    ) 
    (
        input wire i_clk, // ddr3 test clock
        input wire i_clk100, // microblaze clock
        input wire i_rst_n,
        //
        // Wishbone inputs
        output reg o_wb_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        output reg o_wb_stb, //request a transfer
        output reg o_wb_we, //write-enable (1 = write, 0 = read)
        output reg[WB_ADDR_BITS - 1:0] o_wb_addr, //burst-addressable {row,bank,col} 
        output reg[WB_DATA_BITS - 1:0] o_wb_data, //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        output reg[WB_SEL_BITS - 1:0] o_wb_sel, //byte strobe for write (1 = write the byte)
        output reg[AUX_WIDTH - 1:0]  o_aux, //for AXI-interface compatibility (given upon strobe)
        //
        // Wishbone outputs
        input wire i_wb_stall, //1 = busy, cannot accept requests
        input wire i_wb_ack, //1 = read/write request has completed
        input wire i_wb_err, //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
        input wire[WB_DATA_BITS - 1:0] i_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        input wire[AUX_WIDTH - 1:0]  i_aux, //for AXI-interface compatibility (given upon strobe)
        //
        // Done Calibration pin
        input wire i_calib_complete,
        // 
        // UART line
        input wire rx,
	    output wire tx,
        // Button for fault-injection
        input wire btn,
        //
        // Debug
        output wire timer_pulse,
        output wire wrong_data_counter_non_zero
    );
    localparam IDLE=0,
                BURST_WRITE=1,
                BURST_READ=2,
                RANDOM_WRITE=3,
                RANDOM_READ=4,
                ALTERNATE_WRITE_READ=5,
                DONE_TEST=6;
    localparam SIM_ADDRESS_INCR_LOG2 = WB_ADDR_BITS-2-6; // 2^(WB_ADDR_BITS-2)/64
    localparam HALF_ADDRESS = 13;
    localparam SIM_ADDRESS_START = {(WB_ADDR_BITS){1'b1}} - 99; // minus odd number so result is even (similar to default address start of zero)
    (* mark_debug = "true" *) reg[3:0] state=IDLE;
    reg[3:0] rest_counter=0;
    wire[WB_DATA_BITS-1:0] correct_data;
    wire[WB_DATA_BITS-1:0] wb_data_randomized;
    reg[WB_ADDR_BITS-1:0] write_test_address_counter = 0, read_test_address_counter = 0;
    reg[WB_ADDR_BITS-1:0] check_test_address_counter = 0; 
    reg[$clog2(WB_SEL_BITS)-1:0] write_by_byte_counter = 0;
    (* mark_debug = "true" *) reg[63:0] correct_read_data_counter = 0, wrong_read_data_counter = 0; // 64-bit counter for correct and wrong read data, this make sure the counter will not overflow when several day's worth of DDR3 test is done on hardware
    reg increment_wrong_read_data_counter = 0;
    reg increment_correct_read_data_counter = 0;
    (* mark_debug = "true" *) reg[WB_DATA_BITS-1:0] wrong_data, expected_data;
    reg[63:0] time_counter = 0; 
    (* mark_debug = "true" *) reg[31:0] injected_faults_counter = 0;
    assign timer_pulse = time_counter[27]; // 1.34 sec
    assign wrong_data_counter_non_zero = wrong_read_data_counter != 0; // pulse when there is wrong data

    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            state <= IDLE;
            rest_counter <= 0;
            o_wb_cyc <= 0;
            o_wb_stb <= 0;
            o_wb_we <= 0;
            o_wb_addr <= 0;
            o_wb_data <= 0;
            o_wb_sel <= 0;
            o_aux <= 0;
            write_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
            rest_counter <= 0;
            read_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
            write_by_byte_counter <= 0;
            injected_faults_counter <= 0;
        end
        else begin
            case(state)
                IDLE: if(i_calib_complete) begin // wait until DDR3 is done calibrating
                        rest_counter = rest_counter + 1;
                        if(rest_counter == 4'hf) begin // rest for 16 cycles before starting test
                            state <= BURST_WRITE;
                            o_wb_cyc <= 1'b1;
                        end
                    end
                    else begin
                        o_wb_cyc <= 0;
                        o_wb_stb <= 0;
                        o_wb_we <= 0;
                        o_wb_addr <= 0;
                        o_wb_data <= 0;
                        o_wb_sel <= 0;
                        o_aux <= 0;
                        write_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                        rest_counter <= 0;
                        read_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                        write_by_byte_counter <= 0;
                        injected_faults_counter <= 0;
                    end

                BURST_WRITE: if(!i_wb_stall) begin // Test 1: Burst write (per byte write to test datamask feature), then burst read
                                o_wb_stb <= 1'b1; 
                                o_aux <= 2; // write
                                o_wb_we <= 1; 
                                if(DATA_MASK) begin // If datamasking is available, test datamask by writing 8 bytes at a time
                                    o_wb_sel <= {{WB_SEL_BITS-8{1'b0}}, 8'hff} << write_by_byte_counter; // write_by_byte_counter increments by 8 from 0 to (WB_SEL_BITS-8)
                                    o_wb_addr <= write_test_address_counter;
                                    o_wb_data <= {WB_SEL_BITS{8'haa}}; // fill data initially by 8'haa
                                    o_wb_data[8*write_by_byte_counter +: 64] <= btn_pulse? {64{1'b0}} : wb_data_randomized[8*write_by_byte_counter +: 64]; // place the real data at the datamasked bytes
                                    injected_faults_counter <= btn_pulse? injected_faults_counter + 1 : injected_faults_counter;
                                    if(write_by_byte_counter == (WB_SEL_BITS-8)) begin // once every 64bytes of data is written, go to next address
                                         write_test_address_counter <= write_test_address_counter + 1;  
                                        /* verilator lint_off WIDTHEXPAND */
                                        if( write_test_address_counter == {(WB_ADDR_BITS){1'b1}} ) begin  // wait until all address space is writtten
                                        /* verilator lint_on WIDTHEXPAND */
                                            write_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                                            state <= BURST_READ;
                                        end 
                                    end
                                    write_by_byte_counter <= write_by_byte_counter + 8;
                                end
                                else begin // Burst write to all bytes (all datamask on)
                                    o_wb_sel <= {WB_SEL_BITS{1'b1}};
                                    o_wb_addr <= write_test_address_counter;
                                    o_wb_data <= btn_pulse? {WB_DATA_BITS{1'b0}} : wb_data_randomized;
                                    injected_faults_counter <= btn_pulse? injected_faults_counter + 1 : injected_faults_counter;
                                    write_test_address_counter <= write_test_address_counter + 1;  
                                    /* verilator lint_off WIDTHEXPAND */
                                    if( write_test_address_counter == {WB_ADDR_BITS{1'b1}} ) begin  // wait until all address space is writtten
                                    /* verilator lint_on WIDTHEXPAND */
                                        write_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                                        state <= BURST_READ;
                                    end 
                                end
                            end
                        
                BURST_READ: if(!i_wb_stall) begin
                                o_wb_stb <= 1'b1; 
                                o_aux <= 3; // read
                                o_wb_we <= 0; 
                                o_wb_addr <= read_test_address_counter;
                                read_test_address_counter <= read_test_address_counter + 1; 
                                /* verilator lint_off WIDTHEXPAND */
                                if( read_test_address_counter == {(WB_ADDR_BITS){1'b1}} ) begin // wait until all address space is read
                                /* verilator lint_on WIDTHEXPAND */
                                    read_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                                    state <= RANDOM_WRITE;
                                end  
                            end
                            
                RANDOM_WRITE: if(!i_wb_stall) begin // Test 2: Random write (increments row address to force precharge-act-r/w) then random read
                                    o_wb_stb <= 1'b1; 
                                    o_aux <= 2; // write
                                    o_wb_sel <= {WB_SEL_BITS{1'b1}};
                                    o_wb_we <= 1; 
                                    // swap the halves of address counter, since address mapping is {row,bank,col} then every increment of address counter will now increment the {row, bank} preventing burst operation and forcing precharge-activate before write/read
                                    o_wb_addr[WB_ADDR_BITS-1:HALF_ADDRESS] <= write_test_address_counter[HALF_ADDRESS-1:0]; // [25:13] <= [12:0] 
                                    o_wb_addr[HALF_ADDRESS-1:0] <= write_test_address_counter[WB_ADDR_BITS-1:HALF_ADDRESS]; // [12:0] <= [25:13] 
                                    o_wb_data <= btn_pulse? {WB_DATA_BITS{1'b0}} : wb_data_randomized;
                                    injected_faults_counter <= btn_pulse? injected_faults_counter + 1 : injected_faults_counter;
                                    write_test_address_counter <= write_test_address_counter + 1;  
                                    /* verilator lint_off WIDTHEXPAND */
                                    if( write_test_address_counter == {(WB_ADDR_BITS){1'b1}} ) begin // wait until all address space is writtten
                                    /* verilator lint_on WIDTHEXPAND */
                                        write_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                                        state <= RANDOM_READ;
                                    end
                                end
                        
                RANDOM_READ: if(!i_wb_stall) begin
                                o_wb_stb <= 1'b1; 
                                o_aux <= 3; // read
                                o_wb_we <= 0; 
                                // swap the halves of address counter, since address mapping is {row,bank,col} then every increment of address counter will now increment the {row, bank} preventing burst operation and forcing precharge-activate before write/read
                                o_wb_addr[WB_ADDR_BITS-1:HALF_ADDRESS] <= read_test_address_counter[HALF_ADDRESS-1:0]; // [25:13] <= [12:0] 
                                o_wb_addr[HALF_ADDRESS-1:0] <= read_test_address_counter[WB_ADDR_BITS-1:HALF_ADDRESS]; // [12:0] <= [25:13]
                                read_test_address_counter <=  read_test_address_counter + 1;  
                                /* verilator lint_off WIDTHEXPAND */
                                if( read_test_address_counter == {(WB_ADDR_BITS){1'b1}} ) begin // wait until all address space is read
                                /* verilator lint_on WIDTHEXPAND */
                                    read_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                                    state <= ALTERNATE_WRITE_READ;
                                end
                                end
                                
                ALTERNATE_WRITE_READ: if(!i_wb_stall) begin
                                o_wb_stb <= 1'b1; 
                                o_aux <= 2 + (o_wb_we? 1:0); //2 (write), 3 (read)
                                o_wb_sel <= {WB_SEL_BITS{1'b1}};
                                o_wb_we <= !o_wb_we; // alternating write-read
                                o_wb_addr <= write_test_address_counter; 
                                o_wb_data <= btn_pulse? {WB_DATA_BITS{1'b0}} : wb_data_randomized;
                                injected_faults_counter <= btn_pulse? injected_faults_counter + 1 : injected_faults_counter;
                                // if current operation is write, then dont increment address since we wil read the same address next
                                if(o_wb_we) begin // current operation is read thus increment address
                                    write_test_address_counter <= write_test_address_counter + 1;  
                                end
                                /* verilator lint_off WIDTHEXPAND */
                                if( (o_wb_addr == {(WB_ADDR_BITS){1'b1}}) && !o_wb_we ) begin // only 
                                /* verilator lint_on WIDTHEXPAND */
                                    write_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                                    state <= DONE_TEST;
                                    rest_counter <= 0;
                                end
                            end         
                DONE_TEST: begin
                                o_wb_stb <= 0;
                                rest_counter <= rest_counter + 1;
                                if(rest_counter == 4'hf) begin // rest for 16 cycles before repeating test
                                    state <= BURST_WRITE;
                                end
                            end
            endcase
        end
    end
    // Uses different operations (XOR, addition, subtraction, bit rotation) to generate different values per byte.
    assign wb_data_randomized = {
        {(WB_SEL_BITS/8){write_test_address_counter[0 +: 8] ^ 8'hA5,  // Byte 7
        write_test_address_counter[0 +: 8] | 8'h1A,  // Byte 6
        write_test_address_counter[0 +: 8] & 8'h33,  // Byte 5
        write_test_address_counter[0 +: 8] ^ 8'h5A,  // Byte 4
        write_test_address_counter[0 +: 8] & 8'h21,  // Byte 3
        write_test_address_counter[0 +: 8] | 8'hC7,  // Byte 2
        write_test_address_counter[0 +: 8] ^ 8'h7E,  // Byte 1
        write_test_address_counter[0 +: 8] ^ 8'h3C}}   // Byte 0
    };

    /******************************************************* Test Receiver *******************************************************/
    assign correct_data = {
        {(WB_SEL_BITS/8){check_test_address_counter[0 +: 8] ^ 8'hA5,  // Byte 7
        check_test_address_counter[0 +: 8] | 8'h1A,  // Byte 6
        check_test_address_counter[0 +: 8] & 8'h33,  // Byte 5
        check_test_address_counter[0 +: 8] ^ 8'h5A,  // Byte 4
        check_test_address_counter[0 +: 8] & 8'h21,  // Byte 3
        check_test_address_counter[0 +: 8] | 8'hC7,  // Byte 2
        check_test_address_counter[0 +: 8] ^ 8'h7E,  // Byte 1
        check_test_address_counter[0 +: 8] ^ 8'h3C }}  // Byte 0
    };

    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            check_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
            correct_read_data_counter <= 64'd0;
            wrong_read_data_counter <= 64'd0;
            wrong_data <= 512'd0;
            expected_data <= 512'd0;
            increment_wrong_read_data_counter <= 0;
        end
        else begin
            if(i_calib_complete) begin          
                increment_wrong_read_data_counter <= 1'b0;
                increment_correct_read_data_counter <= 1'b0;
                if ( i_wb_ack && i_aux[2:0] == 3'd3 ) begin //o_aux = 3 is for read requests from DDR3 test
                    if(i_wb_data == correct_data) begin // if read data matches the expected, increment correct_read_data_counter
                        increment_correct_read_data_counter <= 1'b1;
                    end
                    else begin
                        increment_wrong_read_data_counter <= 1'b1;
                        wrong_data <= i_wb_data;
                        expected_data <= correct_data;
                    end
                    /* verilator lint_off WIDTHEXPAND */
                    check_test_address_counter <= check_test_address_counter + 1;
                    if(check_test_address_counter+1'b1 == {(WB_ADDR_BITS){1'b0}}) begin // if next address returns to zero, then if in MICRON_SIM jump to SIM_ADDRESS_START
                        check_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : {(WB_ADDR_BITS){1'b0}};
                    end
                    /* verilator lint_on WIDTHEXPAND */
                end
            end
            else begin
                check_test_address_counter <= MICRON_SIM? SIM_ADDRESS_START : 0;
                correct_read_data_counter <= 64'd0;
                wrong_read_data_counter <= 64'd0;
                wrong_data <= 512'd0;
                expected_data <= 512'd0;
            end
            if(increment_wrong_read_data_counter) begin
                wrong_read_data_counter <= wrong_read_data_counter + 64'd1;
            end
            if(increment_correct_read_data_counter) begin
                correct_read_data_counter <= correct_read_data_counter + 64'd1;
            end
        end

    end
    /*********************************************************************************************************************************************/
    // 64-bit counter to know how much time had passed and also debounce of btn for fault-injection
    (* mark_debug = "true" *) reg[27:0] btn_debounce_delay;
    (* mark_debug = "true" *) reg btn_pulse_long, btn_pulse_long_prev;
    (* mark_debug = "true" *) wire btn_pulse;
    assign btn_pulse = btn_pulse_long && !btn_pulse_long_prev; // if current btn_pulse is high but previously low (posedge) then make pulse
    
    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            btn_pulse_long_prev <= 1'b0;
            btn_debounce_delay <= 0;
            btn_pulse_long <= 0;
        end
        else begin
            btn_pulse_long_prev <= btn_pulse_long;
            if(btn && !btn_pulse_long) begin // when btn asserts and  btn_pulse_long is still low
                btn_pulse_long <= 1'b1;
            end
            if(btn_debounce_delay[27]) begin // if ~1.3s had passed, set btn_pulse_long low and reset delay
                btn_pulse_long <= 0;
                btn_debounce_delay <= 0;
            end
            else begin 
                btn_debounce_delay <= btn_pulse_long? btn_debounce_delay + 1 : 0;
            end
        end
    end

    always @(posedge i_clk100, negedge i_rst_n) begin
        if(!i_rst_n) begin
            time_counter <= 64'd0;
        end
        else begin
            time_counter <= time_counter + 1;
        end
    end 

    design_1_wrapper microblaze_inst
    (   .clk_in1_0(i_clk100),
        .correct_read_data_counter_0(correct_read_data_counter),
        .reset_rtl_0(i_rst_n),
        .time_counter_0(time_counter),
        .injected_faults_counter_0(injected_faults_counter),
        .uart_rtl_0_rxd(rx),
        .uart_rtl_0_txd(tx),
        .wrong_read_data_counter_0(wrong_read_data_counter)
    );
endmodule

