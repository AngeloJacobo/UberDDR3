//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/01/2023 08:50:24 AM
// Design Name: 
// Module Name: ddr3_dimm_micron_sim
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ps / 1ps
`define den8192Mb
`define sg125
`define x8

module ddr3_dimm_micron_sim;
`ifdef den1024Mb
    `include "1024Mb_ddr3_parameters.vh"
`elsif den2048Mb
    `include "2048Mb_ddr3_parameters.vh"
`elsif den4096Mb
    `include "4096Mb_ddr3_parameters.vh"
`elsif den8192Mb
    `include "8192Mb_ddr3_parameters.vh"
`else
    // NOTE: Intentionally cause a compile fail here to force the users
    //       to select the correct component density before continuing
    ERROR: You must specify component density with +define+den____Mb.
`endif

 localparam CONTROLLER_CLK_PERIOD = 10, //ns, period of clock input to this DDR3 controller module
            DDR3_CLK_PERIOD = 2.5, //ns, period of clock input to DDR3 RAM device 
            LANES = 8, //8 lanes of DQ
            AUX_WIDTH = 16, // AUX lines
            OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
            OPT_BUS_ABORT = 1;

 reg i_controller_clk, i_ddr3_clk, i_ref_clk;
 reg i_rst_n;
 // Wishbone Interface
 reg i_wb_cyc; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
 reg i_wb_stb; //request a transfer
 reg i_wb_we; //write-enable (1 = write, 0 = read)
 reg[$bits(ddr3_top.i_wb_addr)-1:0] i_wb_addr; //burst-addressable {row,bank,col} 
 reg[$bits(ddr3_top.i_wb_data)-1:0] i_wb_data; //write data, for a 4:1 controller data width is 8 times the number of pins on the device
 wire o_wb_stall; //1 = busy, cannot accept requests
 wire o_wb_ack; //1 = read/write request has completed
 wire[$bits(ddr3_top.o_wb_data)-1:0] o_wb_data; //read data, for a 4:1 controller data width is 8 times the number of pins on the device
 reg[$bits(ddr3_top.i_aux)-1:0] i_aux;
 wire[$bits(ddr3_top.o_aux)-1:0] o_aux;
 // PHY Interface to DDR3 Device
  wire ck_en; // CKE
  wire cs_n; // chip select signal
  wire odt; // on-die termination
  wire ras_n; // RAS#
  wire cas_n; // CAS#
  wire we_n; // WE#
  wire reset_n;
  wire[$bits(ddr3_top.o_ddr3_addr)-1:0] addr;
  wire[$bits(ddr3_top.o_ddr3_ba_addr)-1:0] ba_addr;
  wire[$bits(ddr3_top.io_ddr3_dq)-1:0] dq;
  wire[$bits(ddr3_top.io_ddr3_dqs)-1:0] dqs;
  wire[$bits(ddr3_top.io_ddr3_dqs_n)-1:0] dqs_n;
  wire o_ddr3_clk_p, o_ddr3_clk_n;
  integer index;
  
// DDR3 Controller 
ddr3_top #(
    .ROW_BITS(ROW_BITS),   //width of row address
    .COL_BITS(COL_BITS), //width of column address
    .BA_BITS(BA_BITS), //width of bank address
    .DQ_BITS(DQ_BITS),  //width of DQ
    .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ns, period of clock input to this DDR3 controller module
    .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ns, period of clock input to DDR3 RAM device 
    .LANES(LANES), //8 lanes of DQ
    .AUX_WIDTH(AUX_WIDTH),
    .OPT_LOWPOWER(OPT_LOWPOWER), //1 = low power, 0 = low logic
    .OPT_BUS_ABORT(OPT_BUS_ABORT)  //1 = can abort bus, 0 = no absort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
    ) ddr3_top
    (
        //clock and reset
        .i_controller_clk(i_controller_clk),
        .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
        .i_ref_clk(i_ref_clk),
        .i_rst_n(i_rst_n), 
        // Wishbone inputs
        .i_wb_cyc(i_wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb_stb(i_wb_stb), //request a transfer
        .i_wb_we(i_wb_we), //write-enable (1 = write, 0 = read)
        .i_wb_addr(i_wb_addr), //burst-addressable {row,bank,col} 
        .i_wb_data(i_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb_sel(), //byte strobe for write (1 = write the byte)
        .i_aux(i_aux), //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
        .o_wb_ack(o_wb_ack), //1 = read/write request has completed
        .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        .o_aux(o_aux),
        // PHY Interface (to be added later)
        .o_ddr3_clk_p(o_ddr3_clk_p),
        .o_ddr3_clk_n(o_ddr3_clk_n),
        .o_ddr3_cke(ck_en), // CKE
        .o_ddr3_cs_n(cs_n), // chip select signal
        .o_ddr3_odt(odt), // on-die termination
        .o_ddr3_ras_n(ras_n), // RAS#
        .o_ddr3_cas_n(cas_n), // CAS#
        .o_ddr3_we_n(we_n), // WE#
        .o_ddr3_reset_n(reset_n),
        .o_ddr3_addr(addr),
        .o_ddr3_ba_addr(ba_addr),
        .io_ddr3_dq(dq),
        .io_ddr3_dqs(dqs),
        .io_ddr3_dqs_n(dqs_n)
        ////////////////////////////////////
    );
    
    always #5000 i_controller_clk = !i_controller_clk;
    always #1250 i_ddr3_clk = !i_ddr3_clk;
    always #2500 i_ref_clk = !i_ref_clk;

    initial begin
        i_controller_clk = 1;
        i_ddr3_clk = 1;
        i_ref_clk = 1;
    end
    
    
/*
    // 1 lane DDR3
    ddr3 ddr3_0(
        .rst_n(reset_n),
        .ck(o_ddr3_clk_p),
        .ck_n(o_ddr3_clk_n),
        .cke(ck_en),
        .cs_n(cs_n),
        .ras_n(ras_n),
        .cas_n(cas_n),
        .we_n(we_n),
        .dm_tdqs(),
        .ba(ba_addr),
        .addr(addr),
        .dq(dq),
        .dqs(dqs),
        .dqs_n(dqs_n),
        .tdqs_n(),
        .odt(odt)
    );
    */
    // DDR3 Device 
    ddr3_dimm ddr3_dimm(
        .reset_n(reset_n),
        .ck(o_ddr3_clk_p),
        .ck_n(o_ddr3_clk_n),
        .cke(ck_en),
        .s_n(cs_n), 
        .ras_n(ras_n),
        .cas_n(cas_n),
        .we_n(we_n),
        .ba(ba_addr),
        .addr(addr),
        .odt(odt),
        .dqs(dqs),
        .dqs_n(dqs_n),
        .dq(dq)
    );
    
    reg[511:0] write_data = 0, expected_read_data = 0;
    integer address = 0, read_address = 0;
    integer start_address = 0, start_read_address;
    integer number_of_writes=0, number_of_reads=0, number_of_successful=0, number_of_failed=0;
    integer random_start = $random; //starting seed for random accesss
    integer number_of_injected_errors = 0;

    localparam MAX_READS = (2**COL_BITS)*(2**BA_BITS + 1)/8; //1 row = 2**(COL_BITS) addresses/8 burst = 128 words per row. Times 8 to pass all 8 banks
      initial begin
        //toggle reset for 1 slow clk 
        @(posedge i_controller_clk)
        i_rst_n = 0;
        i_wb_cyc = 0;
        i_wb_stb = 0;
        i_wb_we = 0;
        i_aux = 0;
        i_wb_addr = 0;
        i_wb_data = 0;
        @(posedge i_controller_clk)
        i_rst_n = 1;
        wait(ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE);
        
        // test 1 phase 1: Write random word sequentially
        // write to row 1
        number_of_injected_errors = 0;
        start_address = 0;
        address = start_address;
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk);
            if(!o_wb_stall) begin 
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                  write_data[index*32 +: 32] = $random(address + index); //each $random only has 32 bits
                end
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 1; 
                i_aux = 1;
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                i_wb_data = write_data;
                if(address == start_address + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin //inject error at last row
                    number_of_injected_errors = number_of_injected_errors + 1;
                    i_wb_data = 64'h123456789;
                end
                //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                number_of_writes = number_of_writes + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        
        //Read sequentially
        address = start_address;
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(!o_wb_stall) begin 
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 0; 
                i_aux = 0;
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                //$display("Read: Address = %0d", i_wb_addr);
                number_of_reads = number_of_reads + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        @(posedge i_controller_clk);
        i_wb_stb = 0;
        $display("\nDONE TEST 1: FIRST ROW\n");
        #100_000;
        
        @(posedge i_controller_clk);
        // write to middle row
        start_address = ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS)/2)*($bits(ddr3_top.i_wb_data)/32)/8; //start at the middle row
        address = start_address; 
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk);
            if(!o_wb_stall) begin 
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                  write_data[index*32 +: 32] = $random(address + index); //each $random only has 32 bits
                end
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 1; 
                i_aux = 1;
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                i_wb_data = write_data;
                if(address == start_address + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin //inject error at last row
                    number_of_injected_errors = number_of_injected_errors + 1;
                    i_wb_data = 64'h123456789;
                end
                //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                number_of_writes = number_of_writes + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        
        // Read sequentially
        address = start_address;
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(!o_wb_stall) begin 
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 0; 
                i_aux = 0;
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                //$display("Read: Address = %0d", i_wb_addr);
                number_of_reads = number_of_reads + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        @(posedge i_controller_clk);
        i_wb_stb = 0;
        $display("\nDONE TEST 1: MIDDLE ROW\n");
        #100_000;


         // write to last row (then go back to first row)
        start_address = ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS) - (2**COL_BITS)*(2**BA_BITS))*($bits(ddr3_top.i_wb_data)/32)/8; //start at the last row
        address = start_address; 
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk);
            if(!o_wb_stall) begin 
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                  write_data[index*32 +: 32] = $random(address + index); //each $random only has 32 bits
                end
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 1; 
                i_aux = 1;
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                i_wb_data = write_data;
                if(address == start_address + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin//inject error at last row
                    number_of_injected_errors = number_of_injected_errors + 1;
                    i_wb_data = 64'h123456789;
                end
                //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                number_of_writes = number_of_writes + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        
        // Read sequentially
        address = start_address;
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(!o_wb_stall) begin 
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 0; 
                i_aux = 0;
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                //$display("Read: Address = %0d", i_wb_addr);
                number_of_reads = number_of_reads + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        @(posedge i_controller_clk);
        i_wb_stb = 0;
        $display("\nDONE TEST 1: LAST ROW\n");
        #100_000;
       
        
        
        // Test 2:Random Access
        // write randomly
        address = random_start; //this will just be used as the seed to generate a random number 
        while(address < random_start + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk);
            if(!o_wb_stall) begin 
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                  write_data[index*32 +: 32] = $random(address + index); //each $random only has 32 bits
                end
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 1; 
                i_aux = 1;
                i_wb_addr = $random(~address); //write at random address
                i_wb_data = write_data; //write random data
                if(address == random_start + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin //inject error at last row
                    number_of_injected_errors = number_of_injected_errors + 1;
                    i_wb_data = 64'h123456789;
                end
                //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                number_of_writes = number_of_writes + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        
        // Read sequentially
        // Read the random words written at the random addresses
        address = random_start;
        while(address < random_start + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(!o_wb_stall) begin 
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 0; 
                i_aux = 0;
                i_wb_addr = $random(~address);
                //$display("Read: Address = %0d", i_wb_addr);
                number_of_reads = number_of_reads + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
        end
        @(posedge i_controller_clk);
        i_wb_stb = 0;
        $display("\nDONE TEST 1: LAST ROW\n");
        #100_000;
       
        
        /*
        // write
        //wait until ready to access
        wait(!o_wb_stall);
        @(negedge i_controller_clk);
        i_wb_cyc = 1;
        i_wb_stb = 1;
        i_wb_we = 1;
        i_wb_addr = 0;
        i_wb_data = "BURST_8 BURST_7 BURST_6 BURST_5 BURST_4 BURST_3 BURST_2 BURST_1 ";
        //i_wb_data = 512'h77777777_77777777__66666666_66666666__55555555_55555555__44444444_44444444__33333333_33333333__22222222_22222222__11111111_11111111__00000000_00000000;
        @(negedge i_controller_clk);
        i_wb_addr = 1;
        i_wb_data = "SAMPLE8 SAMPLE7 SAMPLE6 SAMPLE5 SAMPLE4 SAMPLE3 SAMPLE2 SAMPLE1 SAMPLE0";
        //i_wb_data = 512'h77665544_33221100__77665544_33221100__77665544_33221100__77665544_33221100__77665544_33221100__77665544_33221100__77665544_33221100__77665544_33221100;
        @(negedge i_controller_clk);
        i_wb_stb = 0;
        i_wb_data = 0;
        
        //read
        wait(!o_wb_stall);
        @(negedge i_controller_clk);
        i_wb_stb = 1;
        i_wb_we = 0;
        i_wb_addr = 0;
        @(negedge i_controller_clk);
        i_wb_addr = 1;
        @(negedge i_controller_clk);
        i_wb_stb = 0;
        */
      
        #1000_000;
        $display("\n\n------- SUMMARY -------\nNumber of Writes = %0d\nNumber of Reads = %0d\nNumber of Success = %0d\nNumber of Fails = %0d\nNumber of Injected Errors = %0d\n", 
                                                number_of_writes, number_of_reads,number_of_successful, number_of_failed, number_of_injected_errors); 
        $stop;
    end
    
    //check read data
    initial begin
        start_read_address = 0; //start at first row
        read_address = start_read_address;
        
        while(read_address < start_read_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(o_wb_ack && ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE && o_aux == 0) begin
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                    expected_read_data[index*32 +: 32] = $random(read_address + index); //each $random only has 32 bits
                end
                if(expected_read_data == o_wb_data) begin
                    //$display("SUCCESSFUL: Address = %0d, expected data = %h, read data = %h", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data);
                    number_of_successful = number_of_successful + 1;
                end
                else begin
                    $display("FAILED: Address = %0d, expected data = %h, read data = %h @ %t", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data, $time);
                    number_of_failed = number_of_failed + 1;
                end            
                read_address = read_address + ($bits(ddr3_top.i_wb_data)/32); 
           end
        end
        
        start_read_address = ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS)/2)*($bits(ddr3_top.i_wb_data)/32)/8; //start at the middle row
        read_address = start_read_address;
        while(read_address < start_read_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(o_wb_ack && ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE && o_aux == 0) begin
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                    expected_read_data[index*32 +: 32] = $random(read_address + index); //each $random only has 32 bits
                end
                if(expected_read_data == o_wb_data) begin
                    //$display("SUCCESSFUL: Address = %0d, expected data = %h, read data = %h", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data);
                    number_of_successful = number_of_successful + 1;
                end
                else begin
                    $display("FAILED: Address = %0d, expected data = %h, read data = %h @ %t", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data, $time);
                    number_of_failed = number_of_failed + 1;
                end            
                read_address = read_address + ($bits(ddr3_top.i_wb_data)/32); 
           end
        end
        
        start_read_address = ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS) - (2**COL_BITS)*(2**BA_BITS))*($bits(ddr3_top.i_wb_data)/32)/8; //start at the last row
        read_address = start_read_address;
        while(read_address < start_read_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(o_wb_ack && ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE && o_aux == 0) begin
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                    expected_read_data[index*32 +: 32] = $random(read_address + index); //each $random only has 32 bits
                end
                if(expected_read_data == o_wb_data) begin
                    //$display("SUCCESSFUL: Address = %0d, expected data = %h, read data = %h", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data);
                    number_of_successful = number_of_successful + 1;
                end
                else begin
                    $display("FAILED: Address = %0d, expected data = %h, read data = %h @ %t", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data, $time);
                    number_of_failed = number_of_failed + 1;
                end            
                read_address = read_address + ($bits(ddr3_top.i_wb_data)/32); 
           end
        end
        
        // Read the random words written at the random addresses//read the random words at random addresses 
        read_address = random_start;
        while(read_address < random_start + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk);
           if(o_wb_ack && ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE && o_aux == 0) begin
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                    expected_read_data[index*32 +: 32] = $random(read_address + index); //each $random only has 32 bits
                end
                if(expected_read_data == o_wb_data) begin
                    //$display("SUCCESSFUL: Address = %0d, expected data = %h, read data = %h", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data);
                    number_of_successful = number_of_successful + 1;
                end
                else begin
                    $display("FAILED: Address = %0d, expected data = %h, read data = %h @ %t", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data, $time);
                    number_of_failed = number_of_failed + 1;
                end            
                read_address = read_address + ($bits(ddr3_top.i_wb_data)/32); 
           end
        end
        
                
                
    end
    
    reg[8*3-1:0] command_used; //store command in ASCII
    reg[3*8*2-1:0] prev_cmd; //stores previous 2 commands
    reg[32*2-1:0] prev_time;
    reg[31:0] time_now;
    reg[3:0] repeats = 0; 
    //display commands issued
    always @(posedge o_ddr3_clk_p) begin
        if(!cs_n) begin //command is center-aligned to positive edge of clock, a valid command always has low cs_n
            case({cs_n, ras_n, cas_n, we_n})
                 4'b0000: command_used = "MRS";
                 4'b0001: command_used = "REF";
                 4'b0010: command_used = "PRE";
                 4'b0011: command_used = "ACT";
                 4'b0100: command_used = " WR";
                 4'b0101: command_used = " RD";
                 4'b0111: command_used = "NOP";
                 4'b1000: command_used = "DES";
                 4'b0110: command_used = "ZQC";
                 default: command_used = "???";
            endcase
            time_now = $time;
            if(command_used == " WR" || command_used == " RD") begin
                $write("[%5d ps] %s @ (%0d, %5d) -> ",(time_now-prev_time[0 +: 32]), command_used, ba_addr, addr); //show bank and column address of being read/write
            end
            else if(command_used == "ACT") 
                $write("[%5d ps] %s @ (%0d, %5d) -> ",(time_now-prev_time[0 +: 32]), command_used, ba_addr, addr); //show bank and row address of being activated
            else if(command_used == "PRE") 
                $write("[%5d ps] %s @ (%0d) -> ",(time_now-prev_time[0 +: 32]), command_used, ba_addr); //show bank that is being precharged
            else 
                $write("[%5d ps] %s -> ",(time_now-prev_time[0 +: 32]), command_used); //show bank that is being precharged
            prev_cmd <= {prev_cmd[0 +: 3*8], command_used[0 +: 3*8]};
            prev_time <= {prev_time[0 +: 32], time_now};
            repeats <= repeats + 1;
            if(repeats == 4) begin
                $write("\n");
                repeats <= 0;
            end
        end
    end
    /*
    // check delays between command if just enough
    always @* begin
        case({command_used, prev_cmd[0 +: 3*8]}) 
            {"PRE","ACT"};
            {"ACT"," RD"};
            {"ACT"," WR"};
            {" WR"," WR"}: 
            {" WR"," RD"}:
            {" RD"," RD"};
            {" RD"," WR"};
        endcase
    end
        */
endmodule


