`default_nettype none
`timescale 1ps / 1ps

module ddr3_top #(
    parameter real CONTROLLER_CLK_PERIOD = 10, //ns, period of clock input to this DDR3 controller module
                   DDR3_CLK_PERIOD = 2.5, //ns, period of clock input to DDR3 RAM device 
    parameter      ROW_BITS = 14,   //width of row address
                   COL_BITS = 10, //width of column address
                   BA_BITS = 3, //width of bank address
                   DQ_BITS = 8,  //width of DQ
                   LANES = 8, //8 lanes of DQ
                   AUX_WIDTH = 16, 
                   WB2_ADDR_BITS = 32,
                   WB2_DATA_BITS = 32,
    parameter[0:0] OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
                   OPT_BUS_ABORT = 1,  //1 = can abort bus, 0 = no abort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
                   MICRON_SIM = 0, //simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
                   ODELAY_SUPPORTED = 1, //set to 1 when ODELAYE2 is supported
                    
    parameter // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
                serdes_ratio = $rtoi(CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD),
                wb_addr_bits = ROW_BITS + COL_BITS + BA_BITS - $clog2(serdes_ratio*2),
                wb_data_bits = DQ_BITS*LANES*serdes_ratio*2,
                wb_sel_bits = wb_data_bits / 8,
                wb2_sel_bits = WB2_DATA_BITS / 8,
                //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
                cmd_len = 4 + 3 + BA_BITS + ROW_BITS
    ) 
    (
        input wire i_controller_clk, i_ddr3_clk, i_ref_clk, //i_controller_clk = CONTROLLER_CLK_PERIOD, i_ddr3_clk = DDR3_CLK_PERIOD, i_ref_clk = 200MHz
        input wire i_ddr3_clk_90, //required only when ODELAY_SUPPORTED is zero
        input wire i_rst_n,
        // Wishbone inputs
        input wire i_wb_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb_stb, //request a transfer
        input wire i_wb_we, //write-enable (1 = write, 0 = read)
        input wire[wb_addr_bits - 1:0] i_wb_addr, //burst-addressable {row,bank,col} 
        input wire[wb_data_bits - 1:0] i_wb_data, //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        input wire[wb_sel_bits - 1:0] i_wb_sel, //byte strobe for write (1 = write the byte)
        input wire[AUX_WIDTH - 1:0]  i_aux, //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        output wire o_wb_stall, //1 = busy, cannot accept requests
        output wire o_wb_ack, //1 = read/write request has completed
        output wire[wb_data_bits - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output wire[AUX_WIDTH - 1:0]  o_aux, //for AXI-interface compatibility (given upon strobe)
        //
        // Wishbone 2 (PHY) inputs
        input wire i_wb2_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb2_stb, //request a transfer
        input wire i_wb2_we, //write-enable (1 = write, 0 = read)
        input wire[WB2_ADDR_BITS - 1:0] i_wb2_addr, // memory-mapped register to be accessed
        input wire[WB2_DATA_BITS - 1:0] i_wb2_data, //write data
        input wire[wb2_sel_bits - 1:0] i_wb2_sel, //byte strobe for write (1 = write the byte)
        // Wishbone 2 (Controller) outputs
        output wire o_wb2_stall, //1 = busy, cannot accept requests
        output wire o_wb2_ack, //1 = read/write request has completed
        output wire[WB2_DATA_BITS - 1:0] o_wb2_data, //read data
        //
        // DDR3 I/O Interface
        output wire o_ddr3_clk_p, o_ddr3_clk_n,
        output wire o_ddr3_reset_n,
        output wire o_ddr3_cke, // CKE
        output wire o_ddr3_cs_n, // chip select signal
        output wire o_ddr3_ras_n, // RAS#
        output wire o_ddr3_cas_n, // CAS#
        output wire o_ddr3_we_n, // WE#
        output wire[ROW_BITS-1:0] o_ddr3_addr,
        output wire[BA_BITS-1:0] o_ddr3_ba_addr,
        inout wire[(DQ_BITS*LANES)-1:0] io_ddr3_dq,
        inout wire[(DQ_BITS*LANES)/8-1:0] io_ddr3_dqs, io_ddr3_dqs_n,
        output wire[LANES-1:0] o_ddr3_dm,
        output wire o_ddr3_odt, // on-die termination
        output wire[31:0] o_debug1,
        output wire[31:0] o_debug2
    );

    // Wire connections between controller and phy
    wire[cmd_len*serdes_ratio-1:0] cmd;
    wire dqs_tri_control, dq_tri_control;
    wire toggle_dqs;
    wire[wb_data_bits-1:0] data;
    wire[wb_sel_bits-1:0] dm;
    wire[LANES-1:0] bitslip;
    wire[DQ_BITS*LANES*8-1:0] iserdes_data;
    wire[LANES*8-1:0] iserdes_dqs;
    wire[LANES*8-1:0] iserdes_bitslip_reference;
    wire idelayctrl_rdy;
    wire[4:0] odelay_data_cntvaluein, odelay_dqs_cntvaluein;
    wire[4:0] idelay_data_cntvaluein, idelay_dqs_cntvaluein;
    wire[LANES-1:0] odelay_data_ld, odelay_dqs_ld;
    wire[LANES-1:0] idelay_data_ld, idelay_dqs_ld;
    wire write_leveling_calib;
    
    //module instantiations
    ddr3_controller #(
            .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ns, period of clock input to this DDR3 controller module
            .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ns, period of clock input to DDR3 RAM device 
            .ODELAY_SUPPORTED(ODELAY_SUPPORTED),
            .ROW_BITS(ROW_BITS), //width of row address
            .COL_BITS(COL_BITS), //width of column address
            .BA_BITS(BA_BITS), //width of bank address
            .DQ_BITS(DQ_BITS),  //width of DQ
            .LANES(LANES), //8 lanes of DQ
            .AUX_WIDTH(AUX_WIDTH), //
            .WB2_ADDR_BITS(WB2_ADDR_BITS),
            .WB2_DATA_BITS(WB2_DATA_BITS),
            .OPT_LOWPOWER(OPT_LOWPOWER), //1 = low power, 0 = low logic
            .OPT_BUS_ABORT(OPT_BUS_ABORT),  //1 = can abort bus, 0 = no abort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
            .MICRON_SIM(MICRON_SIM) //simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
        ) ddr3_controller_inst (
            .i_controller_clk(i_controller_clk), //i_controller_clk has period of CONTROLLER_CLK_PERIOD 
            .i_rst_n(i_rst_n), //200MHz input clock
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
            .o_aux(o_aux), //for AXI-interface compatibility (returned upon ack)
            // Wishbone 2 (PHY) inputs
            .i_wb2_cyc(i_wb2_cyc), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
            .i_wb2_stb(i_wb2_stb), //request a transfer
            .i_wb2_we(i_wb2_we), //write-enable (1 = write, 0 = read)
            .i_wb2_addr(i_wb2_addr), // memory-mapped register to be accessed 
            .i_wb2_data(i_wb2_data), //write data
            .i_wb2_sel(i_wb2_sel), //byte strobe for write (1 = write the byte)
            // Wishbone 2 (Controller) outputs
            .o_wb2_stall(o_wb2_stall), //1 = busy, cannot accept requests
            .o_wb2_ack(o_wb2_ack), //1 = read/write request has completed
            .o_wb2_data(o_wb2_data), //read data
            //
            // PHY interface
            .i_phy_iserdes_data(iserdes_data),
            .i_phy_iserdes_dqs(iserdes_dqs),
            .i_phy_iserdes_bitslip_reference(iserdes_bitslip_reference),
            .i_phy_idelayctrl_rdy(idelayctrl_rdy),
            .o_phy_cmd(cmd),
            .o_phy_dqs_tri_control(dqs_tri_control), 
            .o_phy_dq_tri_control(dq_tri_control),
            .o_phy_toggle_dqs(toggle_dqs),
            .o_phy_data(data),
            .o_phy_dm(dm),
            .o_phy_odelay_data_cntvaluein(odelay_data_cntvaluein),
            .o_phy_odelay_dqs_cntvaluein(odelay_dqs_cntvaluein),
            .o_phy_idelay_data_cntvaluein(idelay_data_cntvaluein), 
            .o_phy_idelay_dqs_cntvaluein(idelay_dqs_cntvaluein),
            .o_phy_odelay_data_ld(odelay_data_ld),
            .o_phy_odelay_dqs_ld(odelay_dqs_ld),
            .o_phy_idelay_data_ld(idelay_data_ld), 
            .o_phy_idelay_dqs_ld(idelay_dqs_ld),
            .o_phy_bitslip(bitslip),
            .o_phy_write_leveling_calib(write_leveling_calib),
            .o_debug1(o_debug1),
            .o_debug2(o_debug2)
        );
    ddr3_phy #(
            .ROW_BITS(ROW_BITS), //width of row address
            .BA_BITS(BA_BITS), //width of bank address
            .DQ_BITS(DQ_BITS),  //width of DQ
            .LANES(LANES), //8 lanes of DQ
            .CONTROLLER_CLK_PERIOD(CONTROLLER_CLK_PERIOD), //ns, period of clock input to this DDR3 controller module
            .DDR3_CLK_PERIOD(DDR3_CLK_PERIOD), //ns, period of clock input to DDR3 RAM device 
            .ODELAY_SUPPORTED(ODELAY_SUPPORTED)
        ) ddr3_phy_inst (
            .i_controller_clk(i_controller_clk), 
            .i_ddr3_clk(i_ddr3_clk),
            .i_ref_clk(i_ref_clk),
            .i_ddr3_clk_90(i_ddr3_clk_90), 
            .i_rst_n(i_rst_n),
            // Controller Interface
            .i_controller_cmd(cmd),
            .i_controller_dqs_tri_control(dqs_tri_control), 
            .i_controller_dq_tri_control(dq_tri_control),
            .i_controller_toggle_dqs(toggle_dqs),
            .i_controller_data(data),
            .i_controller_dm(dm),
            .i_controller_odelay_data_cntvaluein(odelay_data_cntvaluein),
            .i_controller_odelay_dqs_cntvaluein(odelay_dqs_cntvaluein),
            .i_controller_idelay_data_cntvaluein(idelay_data_cntvaluein),
            .i_controller_idelay_dqs_cntvaluein(idelay_dqs_cntvaluein),
            .i_controller_odelay_data_ld(odelay_data_ld), 
            .i_controller_odelay_dqs_ld(odelay_dqs_ld),
            .i_controller_idelay_data_ld(idelay_data_ld), 
            .i_controller_idelay_dqs_ld(idelay_dqs_ld),
            .i_controller_bitslip(bitslip),
            .i_controller_write_leveling_calib(write_leveling_calib),
            .o_controller_iserdes_data(iserdes_data),
            .o_controller_iserdes_dqs(iserdes_dqs),
            .o_controller_iserdes_bitslip_reference(iserdes_bitslip_reference),
            .o_controller_idelayctrl_rdy(idelayctrl_rdy),
            // DDR3 I/O Interface
            .o_ddr3_clk_p(o_ddr3_clk_p),
            .o_ddr3_clk_n(o_ddr3_clk_n),
            .o_ddr3_reset_n(o_ddr3_reset_n),
            .o_ddr3_cke(o_ddr3_cke), // CKE
            .o_ddr3_cs_n(o_ddr3_cs_n), // chip select signal
            .o_ddr3_ras_n(o_ddr3_ras_n), // RAS#
            .o_ddr3_cas_n(o_ddr3_cas_n), // CAS#
            .o_ddr3_we_n(o_ddr3_we_n), // WE#
            .o_ddr3_addr(o_ddr3_addr),
            .o_ddr3_ba_addr(o_ddr3_ba_addr),
            .io_ddr3_dq(io_ddr3_dq),
            .io_ddr3_dqs(io_ddr3_dqs),
            .io_ddr3_dqs_n(io_ddr3_dqs_n),
            .o_ddr3_dm(o_ddr3_dm),
            .o_ddr3_odt(o_ddr3_odt) // on-die termination
        );
        
endmodule

