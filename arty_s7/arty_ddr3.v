`timescale 1ns / 1ps

   module arty_ddr3
	(
	input wire i_clk, 
	input wire i_rst,
	// DDR3 I/O Interface
    output wire ddr3_clk_p, ddr3_clk_n,
    output wire ddr3_reset_n,
    output wire ddr3_cke, // CKE
    output wire ddr3_cs_n, // chip select signal
    output wire ddr3_ras_n, // RAS#
    output wire ddr3_cas_n, // CAS#
    output wire ddr3_we_n, // WE#
    output wire[14-1:0] ddr3_addr,
    output wire[3-1:0] ddr3_ba,
    inout wire[16-1:0] ddr3_dq,
    inout wire[2-1:0] ddr3_dqs_p, ddr3_dqs_n,
    output wire[2-1:0] ddr3_dm,
    output wire ddr3_odt, // on-die termination
    // UART line
	input wire rx,
	output wire tx,
	//Debug LEDs
	output wire[3:0] led
    );
     
     wire i_controller_clk, i_ddr3_clk, i_ref_clk, i_ddr3_clk_90;
     wire m_axis_tvalid;
     wire rx_empty;
     wire tx_full;
     wire o_wb_ack;
     wire[7:0] o_wb_data;
     wire o_aux;
     wire[7:0] rd_data;
     wire o_wb_stall;
     reg i_wb_stb = 0, i_wb_we;
     wire[63:0] o_debug1;
     reg[7:0] i_wb_data;
     reg[7:0] i_wb_addr;
     assign led[0] = (o_debug1[4:0] == 23); //light up if at DONE_CALIBRATE
     assign led[1] = (o_debug1[4:0] == 23); //light up if at DONE_CALIBRATE
     assign led[2] = (o_debug1[4:0] == 23); //light up if at DONE_CALIBRATE
     assign led[3] = (o_debug1[4:0] == 23); //light up if at DONE_CALIBRATE
     
     
    always @(posedge i_controller_clk) begin
        begin
            i_wb_stb <= 0;
            i_wb_we <= 0;
            i_wb_addr <= 0;
            i_wb_data <= 0;
            if(!o_wb_stall && m_axis_tvalid) begin
                if(rd_data >= 97 && rd_data <= 122) begin //write
                    i_wb_stb <= 1;                 
                    i_wb_we <= 1;                  
                    i_wb_addr <= ~rd_data ;                
                    i_wb_data <= rd_data; 
                end
                else if(rd_data >= 65 && rd_data <= 90) begin //read
                    i_wb_stb <= 1; //make request
                    i_wb_we <= 0; //read
                    i_wb_addr <= ~(rd_data + 8'd32);
                end
            end
        end
    end
     
    (* mark_debug = "true" *) wire clk_locked;
    clk_wiz_0 clk_wiz_inst
    (
    // Clock out ports
    .clk_out1(i_controller_clk), //83.333 Mhz
    .clk_out2(i_ddr3_clk), // 333.333 MHz
    .clk_out3(i_ref_clk), //200MHz
    .clk_out4(i_ddr3_clk_90), // 333.333 MHz with 90degree shift
    // Status and control signals
    .reset(i_rst),
    .locked(clk_locked),
    // Clock in ports
    .clk_in1(i_clk)
    );

    uart #(.DATA_WIDTH(8)) uart_m
    (
         .clk(i_controller_clk),
         .rst(i_rst),
         .s_axis_tdata(o_wb_data),
         .s_axis_tvalid(o_wb_ack),
         .s_axis_tready(),
         .m_axis_tdata(rd_data),
         .m_axis_tvalid(m_axis_tvalid),
         .m_axis_tready(1),
         .rxd(rx),
         .txd(tx),
        .prescale(1085) //9600 Baud Rate
    );
       
    
    // DDR3 Controller 
    ddr3_top #(
        .CONTROLLER_CLK_PERIOD(12_000), //ps, clock period of the controller interface
        .DDR3_CLK_PERIOD(3_000), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
        .ROW_BITS(14), //width of row address
        .COL_BITS(10), //width of column address
        .BA_BITS(3), //width of bank address
        .DQ_BITS(8),  //width of DQ
        .LANES(2), //number of DDR3 modules to be controlled
        .AUX_WIDTH(4), //width of aux line (must be >= 4) 
        .WB2_ADDR_BITS(32), //width of 2nd wishbone address bus 
        .WB2_DATA_BITS(32), //width of 2nd wishbone data bus
        .OPT_LOWPOWER(1), //1 = low power, 0 = low logic
        .OPT_BUS_ABORT(1),  //1 = can abort bus, 0 = no absort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
        .MICRON_SIM(0), //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
        .ODELAY_SUPPORTED(0), //set to 1 when ODELAYE2 is supported
        .SECOND_WISHBONE(0) //set to 1 if 2nd wishbone is needed 
        ) ddr3_top
        (
            //clock and reset
            .i_controller_clk(i_controller_clk),
            .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
            .i_ref_clk(i_ref_clk),
            .i_ddr3_clk_90(i_ddr3_clk_90),
            .i_rst_n(!i_rst && clk_locked), 
            // Wishbone inputs
            .i_wb_cyc(1), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb_stb(i_wb_stb), //request a transfer
            .i_wb_we(i_wb_we), //write-enable (1 = write, 0 = read)
            .i_wb_addr(i_wb_addr), //burst-addressable {row,bank,col} 
            .i_wb_data(i_wb_data), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_wb_sel(16'hffff), //byte strobe for write (1 = write the byte)
            .i_aux(i_wb_we), //for AXI-interface compatibility (given upon strobe)
            // Wishbone outputs
            .o_wb_stall(o_wb_stall), //1 = busy, cannot accept requests
            .o_wb_ack(o_wb_ack), //1 = read/write request has completed
            .o_wb_data(o_wb_data), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
            .o_aux(o_aux),
            // Wishbone 2 (PHY) inputs
            .i_wb2_cyc(), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb2_stb(), //request a transfer
            .i_wb2_we(), //write-enable (1 = write, 0 = read)
            .i_wb2_addr(), //burst-addressable {row,bank,col} 
            .i_wb2_data(), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_wb2_sel(), //byte strobe for write (1 = write the byte)
            // Wishbone 2 (Controller) outputs
            .o_wb2_stall(), //1 = busy, cannot accept requests
            .o_wb2_ack(), //1 = read/write request has completed
            .o_wb2_data(), //read data, for a 4:1 controller data width is 8 times the number of pins on the device
            // PHY Interface (to be added later)
            // DDR3 I/O Interface
            .o_ddr3_clk_p(ddr3_clk_p),
            .o_ddr3_clk_n(ddr3_clk_n),
            .o_ddr3_reset_n(ddr3_reset_n),
            .o_ddr3_cke(ddr3_cke), // CKE
            .o_ddr3_cs_n(ddr3_cs_n), // chip select signal (controls rank 1 only)
            .o_ddr3_ras_n(ddr3_ras_n), // RAS#
            .o_ddr3_cas_n(ddr3_cas_n), // CAS#
            .o_ddr3_we_n(ddr3_we_n), // WE#
            .o_ddr3_addr(ddr3_addr),
            .o_ddr3_ba_addr(ddr3_ba),
            .io_ddr3_dq(ddr3_dq),
            .io_ddr3_dqs(ddr3_dqs_p),
            .io_ddr3_dqs_n(ddr3_dqs_n),
            .o_ddr3_dm(ddr3_dm),
            .o_ddr3_odt(ddr3_odt), // on-die termination
            .o_debug1(o_debug1),
            .o_debug2(),
            .o_debug3()
            ////////////////////////////////////
        );

endmodule

