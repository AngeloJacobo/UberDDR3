`default_nettype none
`timescale 1ps / 1ps

module ypcb_00338_1p1_ddr3 (
    input  wire        clk50,
    input  wire        SYS_RSTN,
    output wire  [2:0] led_3bits_tri_o,

    output wire [14:0] ddram_a,
    output wire  [2:0] ddram_ba,
    output wire        ddram_cas_n,
    output wire        ddram_cke,
    output wire        ddram_clk_n,
    output wire        ddram_clk_p,
    output wire        ddram_cs_n,
    inout  wire [63:0] ddram_dq,
    inout  wire  [7:0] ddram_dqs_n,
    inout  wire  [7:0] ddram_dqs_p,
    output wire        ddram_odt,
    output wire        ddram_ras_n,
    output wire        ddram_reset_n,
    output wire        ddram_we_n
);
    localparam integer ROW_BITS = 15;
    localparam integer COL_BITS = 10;
    localparam integer BA_BITS = 3;
    localparam integer BYTE_LANES = 8;
    localparam integer AUX_WIDTH = 4;
    localparam integer WB_ADDR_BITS = ROW_BITS + COL_BITS + BA_BITS - 3;
    localparam integer WB_DATA_BITS = 8 * BYTE_LANES * 8;
    localparam integer WB_SEL_BITS = WB_DATA_BITS / 8;

    wire controller_clk;
    wire ddr3_clk;
    wire ddr3_clk_90;
    wire ref_clk;
    wire pll_locked;
    wire calib_complete;
    wire [31:0] debug1;
    wire [0:0] ddr3_clk_p_w;
    wire [0:0] ddr3_clk_n_w;
    wire [0:0] ddr3_cke_w;
    wire [0:0] ddr3_cs_n_w;
    wire [0:0] ddr3_odt_w;
    wire [BYTE_LANES - 1:0] ddr3_dm_w;
    wire uart_tx;

    reg [25:0] heartbeat_counter = 26'd0;

    clk_wiz_ypcb clk_wiz_inst (
        .clk50(clk50),
        .locked(pll_locked),
        .controller_clk(controller_clk),
        .ddr3_clk(ddr3_clk),
        .ddr3_clk_90(ddr3_clk_90),
        .ref_clk(ref_clk)
    );

    always @(posedge controller_clk) begin
        if (!SYS_RSTN || !pll_locked || !calib_complete) begin
            heartbeat_counter <= 26'd0;
        end else begin
            heartbeat_counter <= heartbeat_counter + 26'd1;
        end
    end

    assign led_3bits_tri_o[0] = pll_locked;
    assign led_3bits_tri_o[1] = calib_complete;
    assign led_3bits_tri_o[2] = calib_complete && heartbeat_counter[25];

    assign ddram_clk_p = ddr3_clk_p_w[0];
    assign ddram_clk_n = ddr3_clk_n_w[0];
    assign ddram_cke = ddr3_cke_w[0];
    assign ddram_cs_n = ddr3_cs_n_w[0];
    assign ddram_odt = ddr3_odt_w[0];

    ddr3_top #(
        .CONTROLLER_CLK_PERIOD(40_000),
        .DDR3_CLK_PERIOD(10_000),
        .ROW_BITS(ROW_BITS),
        .COL_BITS(COL_BITS),
        .BA_BITS(BA_BITS),
        .BYTE_LANES(BYTE_LANES),
        .AUX_WIDTH(AUX_WIDTH),
        .WB2_ADDR_BITS(7),
        .WB2_DATA_BITS(32),
        .DUAL_RANK_DIMM(0),
        .SPEED_BIN(0),
        .SDRAM_CAPACITY(5),
        .TRCD(13_750),
        .TRP(13_750),
        .TRAS(35_000),
        .ODELAY_SUPPORTED(0),
        .SECOND_WISHBONE(0),
        .DLL_OFF(1),
        .WB_ERROR(0),
        .BIST_MODE(1),
        .ECC_ENABLE(0)
    ) ddr3_top_inst (
        .i_controller_clk(controller_clk),
        .i_ddr3_clk(ddr3_clk),
        .i_ref_clk(ref_clk),
        .i_ddr3_clk_90(ddr3_clk_90),
        .i_rst_n(SYS_RSTN && pll_locked),

        .i_wb_cyc(1'b1),
        .i_wb_stb(1'b0),
        .i_wb_we(1'b0),
        .i_wb_addr({WB_ADDR_BITS{1'b0}}),
        .i_wb_data({WB_DATA_BITS{1'b0}}),
        .i_wb_sel({WB_SEL_BITS{1'b1}}),
        .i_aux({AUX_WIDTH{1'b0}}),
        .o_wb_stall(),
        .o_wb_ack(),
        .o_wb_err(),
        .o_wb_data(),
        .o_aux(),

        .i_wb2_cyc(1'b0),
        .i_wb2_stb(1'b0),
        .i_wb2_we(1'b0),
        .i_wb2_addr(7'd0),
        .i_wb2_data(32'd0),
        .i_wb2_sel(4'd0),
        .o_wb2_stall(),
        .o_wb2_ack(),
        .o_wb2_data(),

        .o_ddr3_clk_p(ddr3_clk_p_w),
        .o_ddr3_clk_n(ddr3_clk_n_w),
        .o_ddr3_reset_n(ddram_reset_n),
        .o_ddr3_cke(ddr3_cke_w),
        .o_ddr3_cs_n(ddr3_cs_n_w),
        .o_ddr3_ras_n(ddram_ras_n),
        .o_ddr3_cas_n(ddram_cas_n),
        .o_ddr3_we_n(ddram_we_n),
        .o_ddr3_addr(ddram_a),
        .o_ddr3_ba_addr(ddram_ba),
        .io_ddr3_dq(ddram_dq),
        .io_ddr3_dqs(ddram_dqs_p),
        .io_ddr3_dqs_n(ddram_dqs_n),
        .o_ddr3_dm(ddr3_dm_w),
        .o_ddr3_odt(ddr3_odt_w),
        .o_calib_complete(calib_complete),
        .o_debug1(debug1),
        .i_user_self_refresh(1'b0),
        .uart_tx(uart_tx)
    );

    wire unused = ^debug1 ^ ^ddr3_dm_w ^ uart_tx;
endmodule

`default_nettype wire
