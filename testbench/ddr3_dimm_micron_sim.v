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
    .ROW_BITS(14),   //width of row address
    .COL_BITS(10), //width of column address
    .BA_BITS(3), //width of bank address
    .DQ_BITS(8),  //width of DQ
    .CONTROLLER_CLK_PERIOD(10), //ns, period of clock input to this DDR3 controller module
    .DDR3_CLK_PERIOD(2.5), //ns, period of clock input to DDR3 RAM device 
    .LANES(8), //8 lanes of DQ
    .OPT_LOWPOWER(1), //1 = low power, 0 = low logic
    .OPT_BUS_ABORT(1)  //1 = can abort bus, 0 = no absort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
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
        .i_aux(), //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
        .o_wb_ack(o_wb_ack), //1 = read/write request has completed
        .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
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
    integer start_of_test = 0;
    reg[511:0] write_data = 0, expected_read_data = 0;
    integer address = 0, read_address = 0;
    integer number_of_writes=0, number_of_reads=0, number_of_successful=0, number_of_failed=0;
    localparam MAX_READS = 64;
      initial begin
        start_of_test = 0;
        //toggle reset for 1 slow clk 
        @(negedge i_controller_clk)
        i_rst_n = 0;
        i_wb_cyc = 0;
        i_wb_stb = 0;
        i_wb_we = 0;
        i_wb_addr = 0;
        i_wb_data = 0;
        @(negedge i_controller_clk)
        i_rst_n = 1;
        wait(ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE);
        
        // test 1 phase 1: Write random word sequentially
        start_of_test = 1;
        address = 0;
        while(address < MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(negedge i_controller_clk);
            if(!o_wb_stall) begin 
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                  write_data[index*32 +: 32] = $random(address + index); //each $random only has 32 bits
                end
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 1; 
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                i_wb_data = write_data;
                $display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                number_of_writes = number_of_writes + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
            else begin
                i_wb_cyc = 1;
                i_wb_stb = 0;
                i_wb_we = 0; 
                i_wb_addr = 0;
                i_wb_data = 0;
            end
        end
        
        // test 1 phase 2: Read sequentially
        start_of_test = 2;
        address = 0;
        while(address < MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(negedge i_controller_clk);
           if(!o_wb_stall) begin 
                i_wb_cyc = 1;
                i_wb_stb = 1;
                i_wb_we = 0; 
                i_wb_addr = address/ ($bits(ddr3_top.i_wb_data)/32);
                $display("Read: Address = %0d", i_wb_addr);
                number_of_reads = number_of_reads + 1;
                address = address + ($bits(ddr3_top.i_wb_data)/32); 
            end
            else begin
                i_wb_cyc = 1;
                i_wb_stb = 0;
                i_wb_we = 0; 
                i_wb_addr = 0;
            end
        end
        @(negedge i_controller_clk);
        i_wb_stb = 0;
        
        
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
        $display("\n\n------- SUMMARY -------\nNumber of Writes = %0d\nNumber of Reads = %0d\nNumber of Success = %0d\nNumber of Fails = %0d\n", number_of_writes, number_of_reads,number_of_successful, number_of_failed); 
        $stop;
    end
    
    //check read data
    initial begin
        read_address = 0;
        while(read_address < MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(negedge i_controller_clk);
           if(o_wb_ack && start_of_test) begin
                for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                    expected_read_data[index*32 +: 32] = $random(read_address + index); //each $random only has 32 bits
                end
                if(expected_read_data == o_wb_data) begin
                    $display("SUCCESSFUL: Address = %0d, expected data = %h, read data = %h", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data);
                    number_of_successful = number_of_successful + 1;
                end
                else begin
                    $display("FAILED: Address = %0d, expected data = %h, read data = %h", (read_address/($bits(ddr3_top.i_wb_data)/32)), expected_read_data, o_wb_data);
                    number_of_failed = number_of_failed + 1;
                end            
                read_address = read_address + ($bits(ddr3_top.i_wb_data)/32); 
           end
        end
    end


endmodule


