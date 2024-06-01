module ddr3_axi_tb;

reg i_controller_clk, i_ddr3_clk, i_ref_clk, i_ddr3_clk_90;
reg i_rst_n;

// AXI Interface
// AXI write address channel signals
reg s_axi_awvalid;
wire s_axi_awready;
reg [dut.AXI_ID_WIDTH-1:0] s_axi_awid;
reg [dut.AXI_ADDR_WIDTH-1:0] s_axi_awaddr;
// AXI write data channel signals
reg s_axi_wvalid;
wire s_axi_wready;
reg [dut.AXI_DATA_WIDTH-1:0] s_axi_wdata;
reg [dut.AXI_DATA_WIDTH/8-1:0] s_axi_wstrb;
reg s_axi_wlast;
// AXI write response channel signals
wire s_axi_bvalid;
reg s_axi_bready;
wire [dut.AXI_ID_WIDTH-1:0] s_axi_bid;
wire [1:0] s_axi_bresp;
// AXI read address channel signals
reg s_axi_arvalid;
wire s_axi_arready;
reg [dut.AXI_ID_WIDTH-1:0] s_axi_arid;
reg [dut.AXI_ADDR_WIDTH-1:0] s_axi_araddr;
// AXI read data channel signals
wire s_axi_rvalid;  // rd rslt valid
reg s_axi_rready;  // rd rslt ready
wire [dut.AXI_ID_WIDTH-1:0]   s_axi_rid; // response id
wire [dut.AXI_DATA_WIDTH-1:0] s_axi_rdata;// read data
wire s_axi_rlast; // read last
wire [1:0] s_axi_rresp; // read response

// DDR3 Pins
wire o_ddr3_clk_p; 
wire o_ddr3_clk_n;
wire o_ddr3_reset_n;
wire o_ddr3_cke; 
wire o_ddr3_cs_n; 
wire o_ddr3_ras_n; 
wire o_ddr3_cas_n;
wire o_ddr3_we_n;
wire[dut.ROW_BITS-1:0] o_ddr3_addr;
wire[dut.BA_BITS-1:0] o_ddr3_ba_addr;
wire[(dut.DQ_BITS*dut.BYTE_LANES)-1:0] io_ddr3_dq;
wire[dut.BYTE_LANES-1:0] io_ddr3_dqs, io_ddr3_dqs_n;
wire[dut.BYTE_LANES-1:0] o_ddr3_dm;
wire o_ddr3_odt;

 localparam CONTROLLER_CLK_PERIOD = 10_000, //ps, period of clock input to this DDR3 controller module
            DDR3_CLK_PERIOD = 2500; //ps, period of clock input to DDR3 RAM device 
 

// Clocks and reset
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
        i_rst_n = 0;
        #1_000_000;
        i_rst_n = 1;
    end

initial begin
    // initialize AXI
    s_axi_awvalid = 0;
    s_axi_awid = 0;
    s_axi_awaddr = 0;

    s_axi_wvalid = 0;
    s_axi_wdata = 0;
    s_axi_wstrb = 0;
    s_axi_wlast = 0;

    s_axi_bready = 0;

    s_axi_arvalid = 0;
    s_axi_arid = 0;
    s_axi_araddr = 0;

    s_axi_rready = 0;

    //wait until done calibrate
    wait(dut.ddr3_top_inst.ddr3_controller_inst.state_calibrate == 23); 

    // write data to address 3 (0-15 = address 0, 16-31 = address 1, 32-47 = address 2)
    @(negedge i_controller_clk);
    s_axi_awvalid = 1;
    s_axi_awid = 0;
    s_axi_awaddr = 33;
    @(negedge i_controller_clk);
    // while(!s_axi_awready) begin
    //     @(negedge i_controller_clk);
    // end
    s_axi_awvalid = 0;
    s_axi_awid = 0;
    s_axi_awaddr = 0;

    s_axi_wvalid = 1;
    s_axi_wdata = 128'hAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_0000_1111; // data 1
    s_axi_wstrb = -1;

    @(negedge i_controller_clk);
    while(!s_axi_wready) begin
        @(negedge i_controller_clk);
    end
    s_axi_wdata = 128'h2222_3333_4444_5555_6666_7777_8888_9999; // data 2

    @(negedge i_controller_clk);
    while(!s_axi_wready) begin
        @(negedge i_controller_clk);
    end
    s_axi_wdata = 100; // data 3

    @(negedge i_controller_clk);
    while(!s_axi_wready) begin
        @(negedge i_controller_clk);
    end
    s_axi_wdata = 2000; // data 4
    s_axi_wlast = 1;

    @(negedge i_controller_clk);
    while(!s_axi_wready) begin
        @(negedge i_controller_clk);
    end
    s_axi_wvalid = 0;
    s_axi_wdata = 0;
    s_axi_wstrb = 0;
    s_axi_wlast = 0;
    // DONE write data to address 3 

    // wait for write response
    wait(s_axi_bvalid);
    @(negedge i_controller_clk);
    s_axi_bready = 1;
    @(negedge i_controller_clk);
    s_axi_bready = 0;
    // done waiting for write response

    #1000_000;
    // read data request from address 2 (0-15 = address 0, 16-31 = address 1, 32-47 = address 2)
    @(negedge i_controller_clk);
    s_axi_arvalid = 1;
    s_axi_arid = 2;
    s_axi_araddr = 46;
    @(negedge i_controller_clk);
    s_axi_arvalid = 0;
    s_axi_arid = 0;
    s_axi_araddr = 0;
    // done read data request from address 3

    // wait for read data
    wait(s_axi_rvalid);
    @(negedge i_controller_clk);
    @(negedge i_controller_clk);
    @(negedge i_controller_clk);
    @(negedge i_controller_clk);
    s_axi_rready = 1;
    @(negedge i_controller_clk);
    @(negedge i_controller_clk);
    @(negedge i_controller_clk);
    @(negedge i_controller_clk);
    s_axi_rready = 0;
    #1000_000;
    $finish;

end
ddr3_top_axi #(
    .CONTROLLER_CLK_PERIOD(10_000), //ps, clock period of the controller interface
    .DDR3_CLK_PERIOD(2_500), //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
    .ROW_BITS(14),   //width of row address
    .COL_BITS(10), //width of column address
    .BA_BITS(3), //width of bank address
    .BYTE_LANES(2), //number of byte lanes of DDR3 RAM
    .AXI_ID_WIDTH(4), // The AXI id width used for R&W, an int between 1-16
    .MICRON_SIM(1), //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
    .ODELAY_SUPPORTED(0), //set to 1 when ODELAYE2 is supported
    .SECOND_WISHBONE(0) //set to 1 if 2nd wishbone for debugging is needed 
) dut
    (
        .i_controller_clk(i_controller_clk), 
        .i_ddr3_clk(i_ddr3_clk), 
        .i_ref_clk(i_ref_clk), //i_controller_clk = CONTROLLER_CLK_PERIOD, i_ddr3_clk = DDR3_CLK_PERIOD, i_ref_clk = 200MHz
        .i_ddr3_clk_90(i_ddr3_clk_90), //required only when ODELAY_SUPPORTED is zero
        .i_rst_n(i_rst_n),
        //
        // AXI Interface
        // AXI write address channel signals
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_awid(s_axi_awid),
        .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awlen(3), // 4 transfers in a transaction
        .s_axi_awsize($clog2(128)),
        .s_axi_awburst(1), //incrementing burst address
        .s_axi_awlock(0),
        .s_axi_awcache(0),
        .s_axi_awprot(0),
        .s_axi_awqos(0),
        // AXI write data channel signals
        .s_axi_wvalid(s_axi_wvalid),
        .s_axi_wready(s_axi_wready), 
        .s_axi_wdata(s_axi_wdata),
        .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wlast(s_axi_wlast),
        // AXI write response channel signals
        .s_axi_bvalid(s_axi_bvalid), 
        .s_axi_bready(s_axi_bready),
        .s_axi_bid(s_axi_bid),
        .s_axi_bresp(s_axi_bresp),
        // AXI read address channel signals
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_arid(s_axi_arid),
        .s_axi_araddr(s_axi_araddr),
        .s_axi_arlen(3), // only 1 transfer in a transaction
        .s_axi_arsize($clog2(128)),
        .s_axi_arburst(1), //incrementing burst address
        .s_axi_arlock(0), 
        .s_axi_arcache(0),
        .s_axi_arprot(0),
        .s_axi_arqos(0),
        // AXI read data channel signals
        .s_axi_rvalid(s_axi_rvalid),  // rd rslt valid
        .s_axi_rready(s_axi_rready),  // rd rslt ready
        .s_axi_rid(s_axi_rid), // response id
        .s_axi_rdata(s_axi_rdata),// read data
        .s_axi_rlast(s_axi_rlast),   // read last
        .s_axi_rresp(s_axi_rresp),   // read response
        //
        // DDR3 I/O Interface
        .o_ddr3_clk_p(o_ddr3_clk_p),
        .o_ddr3_clk_n(o_ddr3_clk_n),
        .o_ddr3_reset_n(o_ddr3_reset_n),
        .o_ddr3_cke(o_ddr3_cke), 
        .o_ddr3_cs_n(o_ddr3_cs_n), 
        .o_ddr3_ras_n(o_ddr3_ras_n), 
        .o_ddr3_cas_n(o_ddr3_cas_n),
        .o_ddr3_we_n(o_ddr3_we_n),
        .o_ddr3_addr(o_ddr3_addr),
        .o_ddr3_ba_addr(o_ddr3_ba_addr),
        .io_ddr3_dq(io_ddr3_dq),
        .io_ddr3_dqs(io_ddr3_dqs), 
        .io_ddr3_dqs_n(io_ddr3_dqs_n),
        .o_ddr3_dm(o_ddr3_dm),
        .o_ddr3_odt(o_ddr3_odt)
        //
    );

ddr3 ddr3_0(
        .rst_n(o_ddr3_reset_n),
        .ck(o_ddr3_clk_p),
        .ck_n(o_ddr3_clk_n),
        .cke(o_ddr3_cke),
        .cs_n(o_ddr3_cs_n),
        .ras_n(o_ddr3_ras_n),
        .cas_n(o_ddr3_cas_n),
        .we_n(o_ddr3_we_n),
        .dm_tdqs(o_ddr3_dm),
        .ba(o_ddr3_ba_addr),
        .addr({0,o_ddr3_addr}),
        .dq(io_ddr3_dq),
        .dqs(io_ddr3_dqs),
        .dqs_n(io_ddr3_dqs_n),
        .tdqs_n(),
        .odt(o_ddr3_odt)
    );

    
endmodule