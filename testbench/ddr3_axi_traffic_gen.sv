module ddr3_axi_traffic_gen;

reg i_controller_clk, i_ddr3_clk, i_ref_clk, i_ddr3_clk_90;
reg i_rst_n;

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
        wait(done);
        #1_000_000;
        $finish;    
    end

wire [31 : 0] m_axi_lite_ch1_awaddr;
wire [2 : 0] m_axi_lite_ch1_awprot;
wire m_axi_lite_ch1_awvalid;
wire m_axi_lite_ch1_awready;
wire [31 : 0] m_axi_lite_ch1_wdata;
wire [3 : 0] m_axi_lite_ch1_wstrb;
wire m_axi_lite_ch1_wvalid;
wire m_axi_lite_ch1_wready;
wire [1 : 0] m_axi_lite_ch1_bresp;
wire m_axi_lite_ch1_bvalid;
wire m_axi_lite_ch1_bready;
wire [31 : 0] m_axi_lite_ch1_araddr;
wire m_axi_lite_ch1_arvalid;
wire m_axi_lite_ch1_arready;
wire [31 : 0] m_axi_lite_ch1_rdata;
wire m_axi_lite_ch1_rvalid;
wire [1 : 0] m_axi_lite_ch1_rresp;
wire m_axi_lite_ch1_rready;

wire done;
wire [31 : 0] status;

axi_traffic_gen_1 axi_traffic_gen_inst(
  .s_axi_aclk(i_controller_clk),
  .s_axi_aresetn(i_rst_n && (dut.ddr3_top_inst.ddr3_controller_inst.state_calibrate == 23)), //stay reset until calibration is done
  .m_axi_lite_ch1_awaddr(m_axi_lite_ch1_awaddr),
  .m_axi_lite_ch1_awprot(m_axi_lite_ch1_awprot),
  .m_axi_lite_ch1_awvalid(m_axi_lite_ch1_awvalid),
  .m_axi_lite_ch1_awready(m_axi_lite_ch1_awready),
  .m_axi_lite_ch1_wdata(m_axi_lite_ch1_wdata),
  .m_axi_lite_ch1_wstrb(m_axi_lite_ch1_wstrb),  // assuming full byte enable for simplicity
  .m_axi_lite_ch1_wvalid(m_axi_lite_ch1_wvalid),
  .m_axi_lite_ch1_wready(m_axi_lite_ch1_wready),
  .m_axi_lite_ch1_bresp(m_axi_lite_ch1_bresp),
  .m_axi_lite_ch1_bvalid(m_axi_lite_ch1_bvalid),
  .m_axi_lite_ch1_bready(m_axi_lite_ch1_bready),
  .m_axi_lite_ch1_araddr(m_axi_lite_ch1_araddr),
  .m_axi_lite_ch1_arvalid(m_axi_lite_ch1_arvalid),
  .m_axi_lite_ch1_arready(m_axi_lite_ch1_arready),
  .m_axi_lite_ch1_rdata(m_axi_lite_ch1_rdata),
  .m_axi_lite_ch1_rvalid(m_axi_lite_ch1_rvalid),
  .m_axi_lite_ch1_rresp(m_axi_lite_ch1_rresp),
  .m_axi_lite_ch1_rready(m_axi_lite_ch1_rready),
  .done(done),
  .status(status)
);

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
) dut (
    .i_controller_clk(i_controller_clk), 
    .i_ddr3_clk(i_ddr3_clk), 
    .i_ref_clk(i_ref_clk), //i_controller_clk = CONTROLLER_CLK_PERIOD, i_ddr3_clk = DDR3_CLK_PERIOD, i_ref_clk = 200MHz
    .i_ddr3_clk_90(i_ddr3_clk_90), //required only when ODELAY_SUPPORTED is zero
    .i_rst_n(i_rst_n),
    
    // AXI Interface
    // AXI write address channel signals
    .s_axi_awvalid(m_axi_lite_ch1_awvalid),
    .s_axi_awready(m_axi_lite_ch1_awready),
    .s_axi_awid(4'b0000),  // AXI-Lite doesn't have ID, so set to 0
    .s_axi_awaddr(m_axi_lite_ch1_awaddr),
    .s_axi_awlen(8'b00000000), // AXI-Lite doesn't use burst length
    .s_axi_awsize(3'b010), // Assuming 32-bit size
    .s_axi_awburst(2'b01), // AXI-Lite doesn't use burst, set to incrementing
    .s_axi_awlock(1'b0), // AXI-Lite doesn't use lock, set to 0
    .s_axi_awcache(4'b0000), // Assuming normal non-cacheable memory
    .s_axi_awprot(m_axi_lite_ch1_awprot ), // Set to normal, non-secure, data access
    .s_axi_awqos(4'b0000), // Quality of Service, set to 0

    // AXI write data channel signals
    .s_axi_wvalid(m_axi_lite_ch1_wvalid),
    .s_axi_wready(m_axi_lite_ch1_wready),
    .s_axi_wdata({128'd0,m_axi_lite_ch1_wdata}),
    .s_axi_wstrb({0,m_axi_lite_ch1_wstrb}), // Assuming full byte enable
    .s_axi_wlast(m_axi_lite_ch1_wvalid), // AXI-Lite only has single beat transfers

    // AXI write response channel signals
    .s_axi_bvalid(m_axi_lite_ch1_bvalid),
    .s_axi_bready(m_axi_lite_ch1_bready),
    .s_axi_bid(), // AXI-Lite doesn't have ID, so set to 0
    .s_axi_bresp(m_axi_lite_ch1_bresp),

    // AXI read address channel signals
    .s_axi_arvalid(m_axi_lite_ch1_arvalid), // No read transactions in this example
    .s_axi_arready(m_axi_lite_ch1_arready),
    .s_axi_arid(4'b0000),
    .s_axi_araddr(m_axi_lite_ch1_araddr),
    .s_axi_arlen(8'b00000000),
    .s_axi_arsize(3'b010),
    .s_axi_arburst(2'b01),
    .s_axi_arlock(1'b0),
    .s_axi_arcache(4'b0000),
    .s_axi_arprot(3'b000),
    .s_axi_arqos(4'b0000),

    // AXI read data channel signals
    .s_axi_rvalid(m_axi_lite_ch1_rvalid),
    .s_axi_rready(m_axi_lite_ch1_rready), // No read transactions in this example
    .s_axi_rid(),
    .s_axi_rdata(m_axi_lite_ch1_rdata),
    .s_axi_rlast(),
    .s_axi_rresp(m_axi_lite_ch1_rresp),
    
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