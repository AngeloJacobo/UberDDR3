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
`define x16
//`define USE_CLOCK_WIZARD
`define TWO_LANES_x8
//`define EIGHT_LANES_x8
`define RAM_8Gb

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

`ifdef TWO_LANES_x8
    localparam LANES = 2,
                ODELAY_SUPPORTED = 1;
`endif 

`ifdef EIGHT_LANES_x8
    localparam LANES = 8,
                ODELAY_SUPPORTED = 1;;
`endif


 localparam CONTROLLER_CLK_PERIOD = 10_000, //ps, period of clock input to this DDR3 controller module
            DDR3_CLK_PERIOD = 2500, //ps, period of clock input to DDR3 RAM device 
            AUX_WIDTH = 16, // AUX lines
            OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
            OPT_BUS_ABORT = 1;

 reg i_controller_clk, i_ddr3_clk, i_ref_clk, i_ddr3_clk_90;
 reg i_rst_n;
 // Wishbone Interface
 reg i_wb_cyc; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
 reg i_wb_stb; //request a transfer
 reg i_wb_we; //write-enable (1 = write, 0 = read)
 reg[$bits(ddr3_top.i_wb_addr)-1:0] i_wb_addr; //burst-addressable {row,bank,col} 
 reg[$bits(ddr3_top.i_wb_data)-1:0] i_wb_data; //write data, for a 4:1 controller data width is 8 times the number of pins on the device
 reg[ddr3_top.wb_sel_bits - 1:0] i_wb_sel; //byte strobe for write (1 = write the byte)
 wire o_wb_stall; //1 = busy, cannot accept requests
 wire o_wb_ack; //1 = read/write request has completed
 wire[$bits(ddr3_top.o_wb_data)-1:0] o_wb_data; //read data, for a 4:1 controller data width is 8 times the number of pins on the device
 reg[$bits(ddr3_top.i_aux)-1:0] i_aux;
 wire[$bits(ddr3_top.o_aux)-1:0] o_aux;
 // PHY Interface to DDR3 Device
  wire[1:0] ck_en; // CKE
  wire[1:0] cs_n; // chip select signal
  wire[1:0] odt; // on-die termination
  wire ras_n; // RAS#
  wire cas_n; // CAS#
  wire we_n; // WE#
  wire reset_n;
  wire[$bits(ddr3_top.o_ddr3_addr)-1:0] addr;
  wire[$bits(ddr3_top.o_ddr3_ba_addr)-1:0] ba_addr;
  wire[$bits(ddr3_top.o_ddr3_dm)-1:0] ddr3_dm;
  wire[$bits(ddr3_top.io_ddr3_dq)-1:0] dq;
  wire[$bits(ddr3_top.io_ddr3_dqs)-1:0] dqs;
  wire[$bits(ddr3_top.io_ddr3_dqs_n)-1:0] dqs_n;
  wire o_ddr3_clk_p, o_ddr3_clk_n;
  integer index;
  // Wishbone 2 (PHY) inputs
  reg i_wb2_cyc; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
  reg i_wb2_stb; //request a transfer
  reg i_wb2_we; //write-enable (1 = write, 0 = read)
  reg[$bits(ddr3_top.i_wb2_addr)-1:0] i_wb2_addr; //memory-mapped register to be accessed 
  reg[$bits(ddr3_top.i_wb2_data)-1:0] i_wb2_data; //write data
  reg[$bits(ddr3_top.i_wb2_sel)-1:0] i_wb2_sel; //byte strobe for write (1 = write the byte)
  // Wishbone 2 (Controller) outputs
  wire o_wb2_stall; //1 = busy, cannot accept requests
  wire o_wb2_ack; //1 = read/write request has completed
  wire[$bits(ddr3_top.o_wb2_data)-1:0] o_wb2_data; //read data
  
  wire clk_locked;
  
  `ifdef USE_CLOCK_WIZARD
      // Use clock wizard
      reg i_clk;
      always #5_000 i_clk = !i_clk;
      initial begin
        i_clk = 0;
      end
        clk_wiz_0 mod1
         (
          // Clock out ports
          .clk_out1(i_controller_clk), 
          .clk_out2(i_ddr3_clk), 
          .clk_out3(i_ref_clk), 
          .clk_out4(i_ddr3_clk_90), 
          // Status and control signals
          .reset(!i_rst_n),
          .locked(clk_locked),
         // Clock in ports
          .clk_in1(i_clk)
         );
       
   `else
        assign clk_locked = 1;
        always #(CONTROLLER_CLK_PERIOD/2) i_controller_clk = !i_controller_clk;
        always #(DDR3_CLK_PERIOD/2) i_ddr3_clk = !i_ddr3_clk;
        always #2500 i_ref_clk = !i_ref_clk;
        initial begin //90 degree phase shifted ddr3_clk
            #(DDR3_CLK_PERIOD/4);
            while(1) begin
                #(DDR3_CLK_PERIOD/2) i_ddr3_clk_90 = !i_ddr3_clk_90;
            end
        end
        initial begin
            i_controller_clk = 1;
            i_ddr3_clk = 1;
            i_ref_clk = 1;
            i_ddr3_clk_90 = 1;
        end
   `endif
   
// DDR3 Controller 
ddr3_top #(
    .ROW_BITS(ROW_BITS),   //width of row address
    .COL_BITS(COL_BITS), //width of column address
    .BA_BITS(BA_BITS), //width of bank address
    .DQ_BITS(8),  //width of DQ
    .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ns, period of clock input to this DDR3 controller module
    .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ns, period of clock input to DDR3 RAM device 
    .ODELAY_SUPPORTED(ODELAY_SUPPORTED), //set to 1 when ODELAYE2 is supported
    .LANES(LANES), //8 lanes of DQ
    .AUX_WIDTH(AUX_WIDTH),
    .OPT_LOWPOWER(OPT_LOWPOWER), //1 = low power, 0 = low logic
    .OPT_BUS_ABORT(OPT_BUS_ABORT),  //1 = can abort bus, 0 = no absort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
    .MICRON_SIM(1)
    ) ddr3_top
    (
        //clock and reset
        .i_controller_clk(i_controller_clk),
        .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
        .i_ref_clk(i_ref_clk),
        .i_ddr3_clk_90(i_ddr3_clk_90),
        .i_rst_n(i_rst_n && clk_locked), 
        // Wishbone inputs
        .i_wb_cyc(i_wb_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb_stb(i_wb_stb), //request a transfer
        .i_wb_we(i_wb_we), //write-enable (1 = write, 0 = read)
        .i_wb_addr(i_wb_addr), //burst-addressable {row,bank,col} 
        .i_wb_data(i_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb_sel(i_wb_sel), //byte strobe for write (1 = write the byte)
        .i_aux(i_aux), //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
        .o_wb_ack(o_wb_ack), //1 = read/write request has completed
        .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        .o_aux(o_aux),
        // Wishbone 2 (PHY) inputs
        .i_wb2_cyc(i_wb2_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .i_wb2_stb(i_wb2_stb), //request a transfer
        .i_wb2_we(i_wb2_we), //write-enable (1 = write, 0 = read)
        .i_wb2_addr(i_wb2_addr), //burst-addressable {row,bank,col} 
        .i_wb2_data(i_wb2_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        .i_wb2_sel(i_wb2_sel), //byte strobe for write (1 = write the byte)
        // Wishbone 2 (Controller) outputs
        .o_wb2_stall(o_wb2_stall), //1 = busy, cannot accept requests
        .o_wb2_ack(o_wb2_ack), //1 = read/write request has completed
        .o_wb2_data(o_wb2_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        // PHY Interface (to be added later)
        .o_ddr3_clk_p(o_ddr3_clk_p),
        .o_ddr3_clk_n(o_ddr3_clk_n),
        .o_ddr3_cke(ck_en[0]), // CKE
        .o_ddr3_cs_n(cs_n[0]), // chip select signal
        .o_ddr3_odt(odt[0]), // on-die termination
        .o_ddr3_ras_n(ras_n), // RAS#
        .o_ddr3_cas_n(cas_n), // CAS#
        .o_ddr3_we_n(we_n), // WE#
        .o_ddr3_reset_n(reset_n),
        .o_ddr3_addr(addr),
        .o_ddr3_ba_addr(ba_addr),
        .io_ddr3_dq(dq),
        .io_ddr3_dqs(dqs),
        .io_ddr3_dqs_n(dqs_n),
        .o_ddr3_dm(ddr3_dm)
        
        ////////////////////////////////////
    );
    
   
`ifdef TWO_LANES_x8
    // 1 lane DDR3
    ddr3 ddr3_0(
        .rst_n(reset_n),
        .ck(o_ddr3_clk_p),
        .ck_n(o_ddr3_clk_n),
        .cke(ck_en[0]),
        .cs_n(cs_n[0]),
        .ras_n(ras_n),
        .cas_n(cas_n),
        .we_n(we_n),
        .dm_tdqs(ddr3_dm),
        .ba(ba_addr),
        .addr(addr),
        .dq(dq),
        .dqs(dqs),
        .dqs_n(dqs_n),
        .tdqs_n(),
        .odt(odt[0])
    );
    assign ck_en[1]=0,
           cs_n[1]=1,
           odt[1]=0; 
`endif

`ifdef EIGHT_LANES_x8
    // DDR3 Device 
    ddr3_module ddr3_module(
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
        .dqs({ddr3_dm[0], ddr3_dm,ddr3_dm[0],dqs}), //ddr3_module uses last 8 MSB [16:9] as datamask
        .dqs_n(dqs_n),
        .dq(dq)
    );
 `endif
    
    reg[511:0] write_data = 0, expected_read_data = 0;
    integer address = 0, read_address = 0, address_inner = 0;
    integer start_address = 0, start_read_address;
    integer number_of_writes=0, number_of_reads=0, number_of_successful=0, number_of_failed=0;
    integer random_start = $random; //starting seed for random accesss
    integer number_of_injected_errors = 0;
    integer number_of_op = 0;
    integer time_started = 0;
    localparam MAX_READS = (2**COL_BITS)*(2**BA_BITS + 1)/8; //1 row = 2**(COL_BITS) addresses/8 burst = 128 words per row. Times 8 to pass all 8 banks
      initial begin
        //toggle reset for 1 slow clk 
        @(posedge i_controller_clk) begin
            i_rst_n <= 0;
            // Wishbone 1
            i_wb_cyc <= 1;
            i_wb_stb <= 0;
            i_wb_we <= 0;
            i_wb_sel <= -1; //write to all lanes
            i_aux <= 0;
            i_wb_addr <= 0;
            i_wb_data <= 0;
            // Wishbone 2
            i_wb2_cyc <= 0; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            i_wb2_stb <= 0; //request a transfer
            i_wb2_we <= 0; //write-enable (1 = write, 0 = read)
            i_wb2_addr <= 0; //memory-mapped register to be accessed 
            i_wb2_data <= 0; //write data
            i_wb2_sel <= 0; 
        end

        @(posedge i_controller_clk) begin
            i_rst_n <= 1;
        end
        wait(ddr3_top.ddr3_controller_inst.state_calibrate == ddr3_top.ddr3_controller_inst.DONE_CALIBRATE);

        // test 1 phase 1: Write random word sequentially
        // write to row 1
        number_of_op <= 0;
        time_started <= $time;
        number_of_injected_errors <= 0;
        start_address <= 0;
        #1; //just to make sure the non-blocking are assignments are all over
        address <= start_address;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
                if(!i_wb_stb || !o_wb_stall) begin 
                    for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                      i_wb_data[index*32 +: 32] <= $random(address + index); //each $random only has 32 bits
                    end
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 1; 
                    i_aux <= 1;
                    i_wb_addr <= address/ ($bits(ddr3_top.i_wb_data)/32);
                    if(address == start_address + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin //inject error at last row
                        number_of_injected_errors <= number_of_injected_errors + 1;
                        i_wb_data <= 64'h123456789;
                    end
                    //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                    number_of_writes <= number_of_writes + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        
        //Read sequentially
        address <= start_address;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
           @(posedge i_controller_clk) begin
               if(!i_wb_stb || !o_wb_stall) begin 
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 0; 
                    i_aux <= 0;
                    i_wb_addr <= address/ ($bits(ddr3_top.i_wb_data)/32);
                    //$display("Read: Address = %0d", i_wb_addr);
                    number_of_reads <= number_of_reads + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        /*while(i_wb_stb) begin
           @(posedge i_controller_clk) begin
               if (!o_wb_stall) i_wb_stb <= 1'b0;
          end
        end*/

        $display("\n--------------------------------\nDONE TEST 1: FIRST ROW\nNumber of Operations: %0d\nTime Started: %0d ns\nTime Done: %0d ns\nAverage Rate: %0d ns/request\n--------------------------------\n\n",
            number_of_op,time_started/1000, $time/1000, ($time-time_started)/(number_of_op*1000));
       // #100_000;
        
        /*@(posedge i_controller_clk) begin
            // write to middle row
            start_address <= ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS)/2)*($bits(ddr3_top.i_wb_data)/32)/8; //start at the middle row
        end*/
        
        #1; //just to make sure the non-blocking are assignments are all over
        start_address <= ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS)/2)*($bits(ddr3_top.i_wb_data)/32)/8; //start at the middle row
        #1;
        address <= start_address;
        number_of_op <= 0; 
        time_started <= $time;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
                if(!i_wb_stb || !o_wb_stall) begin 
                    for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                      i_wb_data[index*32 +: 32] <= $random(address + index); //each $random only has 32 bits
                    end
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 1; 
                    i_aux <= 1;
                    i_wb_addr <= address/ ($bits(ddr3_top.i_wb_data)/32);
                    if(address == start_address + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin //inject error at last row
                        number_of_injected_errors <= number_of_injected_errors + 1;
                        i_wb_data <= 64'h123456789;
                    end
                    //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                    number_of_writes <= number_of_writes + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        
        // Read sequentially
        address <= start_address;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
               if(!i_wb_stb || !o_wb_stall) begin 
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 0; 
                    i_aux <= 0;
                    i_wb_addr <= address/ ($bits(ddr3_top.i_wb_data)/32);
                    //$display("Read: Address = %0d", i_wb_addr);
                    number_of_reads <= number_of_reads + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        /*while(i_wb_stb) begin
           @(posedge i_controller_clk) begin
               if (!o_wb_stall) i_wb_stb <= 1'b0;
          end
        end*/
        $display("\n--------------------------------\nDONE TEST 1: MIDDLE ROW\nNumber of Operations: %0d\nTime Started: %0d ns\nTime Done: %0d ns\nAverage Rate: %0d ns/request\n--------------------------------\n\n",
            number_of_op,time_started/1000, $time/1000, ($time-time_started)/(number_of_op*1000));
        //#100_000;


         // write to last row (then go back to first row)
        start_address <= ((2**COL_BITS)*(2**ROW_BITS)*(2**BA_BITS) - (2**COL_BITS)*(2**BA_BITS))*($bits(ddr3_top.i_wb_data)/32)/8; //start at the last row
        #1; //just to make sure the non-blocking are assignments are all over
        address <= start_address; 
        number_of_op <= 0; 
        time_started <= $time;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
                if(!i_wb_stb || !o_wb_stall) begin 
                    for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                      i_wb_data[index*32 +: 32] <= $random(address + index); //each $random only has 32 bits
                    end
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 1; 
                    i_aux <= 1;
                    i_wb_addr <= address/ ($bits(ddr3_top.i_wb_data)/32);
                    if(address == start_address + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin//inject error at last row
                        number_of_injected_errors <= number_of_injected_errors + 1;
                        i_wb_data <= 64'h123456789;
                    end
                    //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                    number_of_writes <= number_of_writes + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        
        // Read sequentially
        address <= start_address;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < start_address + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
               if(!i_wb_stb || !o_wb_stall) begin 
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 0; 
                    i_aux <= 0;
                    i_wb_addr <= address/ ($bits(ddr3_top.i_wb_data)/32);
                    //$display("Read: Address = %0d", i_wb_addr);
                    number_of_reads <= number_of_reads + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        /*while(i_wb_stb) begin
           @(posedge i_controller_clk) begin
               if (!o_wb_stall) i_wb_stb <= 1'b0;
          end
        end*/
        $display("\n--------------------------------\nDONE TEST 1: LAST ROW\nNumber of Operations: %0d\nTime Started: %0d ns\nTime Done: %0d ns\nAverage Rate: %0d ns/request\n--------------------------------\n\n",
            number_of_op,time_started/1000, $time/1000, ($time-time_started)/(number_of_op*1000));
        //#100_000;
       
        
        
        // Test 2:Random Access
        // write randomly
        address <= random_start; //this will just be used as the seed to generate a random number 
        number_of_op <= 0; 
        time_started <= $time;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < random_start + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
                if(!i_wb_stb || !o_wb_stall) begin 
                    for (index = 0; index < $bits(ddr3_top.i_wb_data)/32; index = index + 1) begin
                      i_wb_data[index*32 +: 32] <= $random(address + index); //each $random only has 32 bits
                    end
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 1; 
                    i_aux <= 1;
                    i_wb_addr <= $random(~address); //write at random address
                    if(address == random_start + ($bits(ddr3_top.i_wb_data)/32)*(MAX_READS-1)) begin //inject error at last row
                        number_of_injected_errors <= number_of_injected_errors + 1;
                        i_wb_data <= 64'h123456789;
                    end
                    //$display("Write: Address = %0d, Data = %h", i_wb_addr, i_wb_data);
                    number_of_writes <= number_of_writes + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
            #1; //just to make sure the non-blocking are assignments are all over
        end
        
        // Read sequentially
        // Read the random words written at the random addresses
        address <= random_start;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < random_start + MAX_READS*($bits(ddr3_top.i_wb_data)/32)) begin
            @(posedge i_controller_clk) begin
               if(!i_wb_stb || !o_wb_stall) begin 
                    i_wb_cyc <= 1;
                    i_wb_stb <= 1;
                    i_wb_we <= 0; 
                    i_aux <= 0;
                    i_wb_addr <= $random(~address);
                    //$display("Read: Address = %0d", i_wb_addr);
                    number_of_reads <= number_of_reads + 1;
                    number_of_op <= number_of_op + 1;
                    address <= address + ($bits(ddr3_top.i_wb_data)/32); 
                end
            end
        end
        while(i_wb_stb) begin
           @(posedge i_controller_clk) begin
               if (!o_wb_stall) i_wb_stb <= 1'b0;
          end
        end
        $display("\n--------------------------------\nDONE TEST 2: RANDOM\nNumber of Operations: %0d\nTime Started: %0d ns\nTime Done: %0d ns\nAverage Rate: %0d ns/request\n--------------------------------\n\n",
            number_of_op,time_started/1000, $time/1000, ($time-time_started)/(number_of_op*1000));
            
        #100_000;
        // Test 3: Read from wishbone 2 (PHY)
        // Wishbone 2
        i_wb2_cyc <= 0; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        i_wb2_stb <= 0; //request a transfer
        i_wb2_we <= 0; //write-enable (1 = write, 0 = read)
        i_wb2_addr <= 0; //memory-mapped register to be accessed 
        i_wb2_data <= 0; //write data
        i_wb2_sel <= 0; 
        address <= 0;
        address_inner <= 0;
        #1; //just to make sure the non-blocking are assignments are all over
        while(address < 9 ) begin
            if(address <= 3) begin
                while(address_inner < 7) begin
                    @(posedge i_controller_clk) begin
                        if(!i_wb2_stb || !o_wb2_stall) begin 
                            i_wb2_cyc <= 1;
                            i_wb2_stb <= 1; //0,1,2,3,4,5,6,7,8
                            i_wb2_we <= 0; 
                            i_wb2_addr <= address | address_inner << 4;
                            address_inner <= address_inner + 1; 
                        end
                    end
                    #1;
                end //end of while
                
                @(posedge i_controller_clk) begin
                    if(!i_wb2_stb || !o_wb2_stall) begin 
                        i_wb2_cyc <= 1;
                        i_wb2_stb <= 1; //0,1,2,3,4,5,6,7,8
                        i_wb2_we <= 0; 
                        i_wb2_addr <= address | address_inner << 4;
                        address <= address + 1;
                        address_inner <= 0;
                    end
                 end //end of @posedge 
             end //end of if(address <= 3)
             
             else begin
                @(posedge i_controller_clk) begin
                    if(!i_wb2_stb || !o_wb2_stall) begin 
                        i_wb2_cyc <= 1;
                        i_wb2_stb <= 1;
                        i_wb2_we <= 0; 
                        i_wb2_addr <= address;
                        address <= address + 1; 
                    end
                 end
             end

            #1; //just to make sure the non-blocking are assignments are all over
        end
        while(i_wb2_stb) begin
           @(posedge i_controller_clk) begin
               if (!o_wb2_stall) i_wb2_stb <= 1'b0;
          end
        end
      
        #1000_000;
        $display("\n\n------- SUMMARY -------\nNumber of Writes = %0d\nNumber of Reads = %0d\nNumber of Success = %0d\nNumber of Fails = %0d\nNumber of Injected Errors = %0d\n", 
                                                number_of_writes, number_of_reads,number_of_successful, number_of_failed, number_of_injected_errors); 
        $display("\n\nTEST CALIBRATION\n[-]: write_test_address_counter = %0d", ddr3_top.ddr3_controller_inst.write_test_address_counter);
        $display("[-]: read_test_address_counter = %0d", ddr3_top.ddr3_controller_inst.read_test_address_counter);
        $display("[-]: correct_read_data = %0d", ddr3_top.ddr3_controller_inst.correct_read_data);
        $display("[-]: wrong_read_data = %0d", ddr3_top.ddr3_controller_inst.wrong_read_data);
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

    //receive wb2 data
    integer wb2_addr=0, wb2_addr_lane=0;
    initial begin
        while(wb2_addr <= 9) begin
            @(posedge i_controller_clk);
            if(o_wb2_ack) begin
                case(wb2_addr) 
                    0: begin
                            if(wb2_addr_lane == 0) $display("\n\nWishbone 2 (PHY) Test:");
                            $display("[0]: odelay_data_cntvaluein[%0d] = %0d", wb2_addr_lane, o_wb2_data);
                            if(wb2_addr_lane < 7) begin
                                wb2_addr_lane = wb2_addr_lane + 1;
                            end
                            else begin
                                wb2_addr = wb2_addr + 1;
                                wb2_addr_lane = 0;
                            end
                       end
                     1: begin
                            $display("[1]: odelay_dqs_cntvaluein[%0d] = %0d", wb2_addr_lane, o_wb2_data);
                            if(wb2_addr_lane < 7) begin
                                wb2_addr_lane = wb2_addr_lane + 1;
                            end
                            else begin
                                wb2_addr = wb2_addr + 1;
                                wb2_addr_lane = 0;
                            end
                       end
                     2: begin
                            $display("[2]: idelay_data_cntvaluein[%0d] = %0d", wb2_addr_lane, o_wb2_data);
                            if(wb2_addr_lane < 7) begin
                                wb2_addr_lane = wb2_addr_lane + 1;
                            end
                            else begin
                                wb2_addr = wb2_addr + 1;
                                wb2_addr_lane = 0;
                            end
                       end
                    3: begin
                            $display("[3]: idelay_dqs_cntvaluein[%0d] = %0d", wb2_addr_lane, o_wb2_data);
                            if(wb2_addr_lane < 7) begin
                                wb2_addr_lane = wb2_addr_lane + 1;
                            end
                            else begin
                                wb2_addr = wb2_addr + 1;
                                wb2_addr_lane = 0;
                            end
                       end
                    4: begin
                            $display("[4]: i_phy_idelayctrl_rdy = %0d", o_wb2_data[0]);
                            $display("[4]: state_calibrate = %0d", o_wb2_data[5:1]);
                            $display("[4]: instruction_address = %0d", o_wb2_data[10:6]);
                            $display("[4]: added_read_pipe_max = %0d", o_wb2_data[14:11]);
                             wb2_addr = wb2_addr + 1;
                        end
                    5: begin
                            $display("[5]: added_read_pipe[0] = %0d", o_wb2_data[3:0]);
                            $display("[5]: added_read_pipe[1] = %0d", o_wb2_data[7:4]);
                            $display("[5]: added_read_pipe[2] = %0d", o_wb2_data[11:8]);
                            $display("[5]: added_read_pipe[3] = %0d", o_wb2_data[15:12]);
                            $display("[5]: added_read_pipe[4] = %0d", o_wb2_data[19:16]);
                            $display("[5]: added_read_pipe[5] = %0d", o_wb2_data[23:20]);
                            $display("[5]: added_read_pipe[6] = %0d", o_wb2_data[27:24]);
                            $display("[5]: added_read_pipe[7] = %0d", o_wb2_data[31:28]);
                             wb2_addr = wb2_addr + 1;
                        end
                    6: begin
                            $display("[6]: dqs_store = %b_%b_%b_%b", o_wb2_data[31:24], o_wb2_data[23:16], o_wb2_data[15:8], o_wb2_data[7:0]);
                             wb2_addr = wb2_addr + 1;
                        end
                    7: begin
                            $display("[7]: i_phy_iserdes_bitslip_reference = %b_%b_%b_%b", o_wb2_data[31:24], o_wb2_data[23:16], o_wb2_data[15:8], o_wb2_data[7:0]);
                             wb2_addr = wb2_addr + 1;
                        end
                    8: begin
                            $display("[8]: read_data_store = %h", o_wb2_data);
                             wb2_addr = wb2_addr + 1;
                        end
                    9: begin
                            $display("[9]: write_pattern = %h", o_wb2_data);
                             wb2_addr = wb2_addr + 1;
                        end
                endcase        
               
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
        if(!cs_n[0]) begin //command is center-aligned to positive edge of clock, a valid command always has low cs_n
            case({cs_n[0], ras_n, cas_n, we_n})
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


