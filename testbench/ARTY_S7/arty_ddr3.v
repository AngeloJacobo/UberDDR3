`timescale 1ns / 1ps

   module arty_ddr3
	(
	input wire i_clk, i_rst,
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
    inout wire[(8*2)-1:0] ddr3_dq,
    inout wire[(8*2)/8-1:0] ddr3_dqs_p, ddr3_dqs_n,
    output wire[2-1:0] ddr3_dm,
    output wire ddr3_odt, // on-die termination
    // UART line
	input wire rx,
	output wire tx,
	//Debug LEDs
	output wire[2:0] led
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
     reg[7:0] i_wb_addr, i_wb_data;
     assign led[0] = (o_debug1[5:1] == 12);
     assign led[1] = (o_debug1[5:1] == 13);
     assign led[2] = (o_debug1[5:1] == 14); //light up if at DONE_CALIBRATE
     
     
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
                    i_wb_addr <= rd_data;                
                    i_wb_data <= rd_data; 
                end
                else if(rd_data >= 65 && rd_data <= 90) begin //read
                    i_wb_stb <= 1; //make request
                    i_wb_we <= 0; //read
                    i_wb_addr <= rd_data + 8'd32;
                end
                /*
                case(rd_data)
                     97: begin //a
                            i_wb_stb <= 1;
                            i_wb_we <= 1; 
                            i_wb_addr <= 0;
                            i_wb_data <= 8'h31; //write "1"
                         end
                     98: begin //b
                            i_wb_stb <= 1; //make request
                            i_wb_we <= 0; //read
                            i_wb_addr <= 0;
                         end
                     99: begin //c
                            i_wb_stb <= 1;
                            i_wb_we <= 1; 
                            i_wb_addr <= 1;
                            i_wb_data <= 8'h32; //write "2"
                         end
                     100: begin //d
                            i_wb_stb <= 1; //make request
                            i_wb_we <= 0; //read
                            i_wb_addr <= 1;
                         end
                     101: begin //e
                            i_wb_stb <= 1;
                            i_wb_we <= 1; 
                            i_wb_addr <= 2;
                            i_wb_data <= 8'h39; //write "9"
                         end
                     102: begin //f
                            i_wb_stb <= 1; //make request
                            i_wb_we <= 0; //read
                            i_wb_addr <= 2;
                         end
                endcase
                */
              end
        end
     end
     
     
     wire clk_locked;
     clk_wiz_0 clk_wiz_inst
     (
      // Clock out ports
      .clk_out1(i_controller_clk), //83.333 Mhz
      .clk_out2(i_ddr3_clk), // 333.333 MHz
      .clk_out3(i_ref_clk), //200MHz
      .clk_out4(i_ddr3_clk_90),
      // Status and control signals
      .reset(i_rst),
      .locked(clk_locked),
     // Clock in ports
      .clk_in1(i_clk)
     );

     /*
	 uart #(.DBIT(8),.SB_TICK(16),.DVSR(638),.DVSR_WIDTH(10),.FIFO_W(2)) m0 //DBIT=databits , SB_TICK=stop_bits tick(16 per bit) , DVSR= clk/(16*BaudRate) , DVSR_WIDTH=array size needed by DVSR,FIFO_WIDTH+fifo size(2^x) )
	(
		.clk(i_controller_clk),
		.rst_n(!i_rst),
		.rd_uart(!rx_empty),
		.wr_uart(o_wb_ack && !o_aux),
		.wr_data(o_wb_data),
		.rx(rx),
		.tx(tx),
		.rd_data(rd_data),
		.rx_empty(rx_empty),
		.tx_full(tx_full)
    );
    */
    
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
    .prescale(1085)
);


    
    
    // DDR3 Controller 
    ddr3_top #(
        .ROW_BITS(14),   //width of row address
        .COL_BITS(10), //width of column address
        .BA_BITS(3), //width of bank address
        .DQ_BITS(8),  //width of DQ
        .CONTROLLER_CLK_PERIOD(12), //ns, period of clock input to this DDR3 controller module
        .DDR3_CLK_PERIOD(3), //ns, period of clock input to DDR3 RAM device 
        .ODELAY_SUPPORTED(0), //set to 1 when ODELAYE2 is supported
        .LANES(2), //8 lanes of DQ
        .AUX_WIDTH(16),
        .WB2_ADDR_BITS(32),
        .WB2_DATA_BITS(32),
        .OPT_LOWPOWER(1), //1 = low power, 0 = low logic
        .OPT_BUS_ABORT(1),  //1 = can abort bus, 0 = no absort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
        .MICRON_SIM(0) //simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
        ) ddr3_top
        (
            //clock and reset
            .i_controller_clk(i_controller_clk),
            .i_ddr3_clk(i_ddr3_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
            .i_ref_clk(i_ref_clk),
            .i_ddr3_clk_90(i_ddr3_clk_90),
            .i_rst_n(!i_rst || clk_locked), 
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
            .i_wb2_cyc(0), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb2_stb(0), //request a transfer
            .i_wb2_we(), //write-enable (1 = write, 0 = read)
            .i_wb2_addr(), //burst-addressable {row,bank,col} 
            .i_wb2_data(0), //write data, for a 4:1 controller data width is 8 times the number of pins on the device
            .i_wb2_sel(0), //byte strobe for write (1 = write the byte)
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
            .o_debug1(o_debug1)
            ////////////////////////////////////
        );
        /*
        ila_0 m_ila(
            .clk(i_,
            .probe0(clk_locked),
            .probe1(i_rst),
            .probe2,
            .probe3,
            .probe4,
            .probe5,
            .probe6,
            .probe7,
            .probe8
        );*/

	 

endmodule
