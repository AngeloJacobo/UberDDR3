`default_nettype none
`timescale 1ps / 1ps

module ypcb_00338_1p1_ddr3 (
    input  wire        clk50,
    input  wire        rst_n,

    output wire [0:0]  ddr3_ck_p,
    output wire [0:0]  ddr3_ck_n,
    output wire        ddr3_reset_n,
    output wire [0:0]  ddr3_cke,
    output wire [0:0]  ddr3_cs_n,
    output wire        ddr3_ras_n,
    output wire        ddr3_cas_n,
    output wire        ddr3_we_n,
    output wire [14:0] ddr3_addr,
    output wire [2:0]  ddr3_ba,
    inout  wire [63:0] ddr3_dq,
    inout  wire [7:0]  ddr3_dqs_p,
    inout  wire [7:0]  ddr3_dqs_n,
    output wire [0:0]  ddr3_odt,

    output wire [2:0]  led
);
    localparam integer BYTE_LANES = 1;
    localparam integer WB_ADDR_BITS = 15 + 10 + 3 - 3;
    localparam integer WB_DATA_BITS = 8 * BYTE_LANES * 8;
    localparam integer WB_SEL_BITS = WB_DATA_BITS / 8;

    wire controller_clk;
    wire ddr3_clk;
    wire ref_clk;
    wire ddr3_clk_90;
    wire clk_locked;
    wire calib_complete;
    wire [31:0] debug1;
    wire uart_tx_unused;
    wire [BYTE_LANES-1:0] ddr3_dm_unused;

    wire bist_done = calib_complete && (debug1[4:0] == 5'd23);

    assign led[0] = bist_done;
    assign led[1] = !bist_done;
    assign led[2] = clk_locked;

    clk_wiz clk_wiz_inst (
        .clk_in1(clk50),
        .clk_out1(controller_clk),
        .clk_out2(ddr3_clk),
        .clk_out3(ref_clk),
        .clk_out4(ddr3_clk_90),
        .reset(!rst_n),
        .locked(clk_locked)
    );

    ddr3_top #(
        .CONTROLLER_CLK_PERIOD(12_000),
        .DDR3_CLK_PERIOD(3_000),
        .ROW_BITS(15),
        .COL_BITS(10),
        .BA_BITS(3),
        .BYTE_LANES(BYTE_LANES),
        .AUX_WIDTH(4),
        .WB2_ADDR_BITS(32),
        .WB2_DATA_BITS(32),
        .DUAL_RANK_DIMM(0),
        .MICRON_SIM(0),
        .ODELAY_SUPPORTED(0),
        .SECOND_WISHBONE(0),
        .DLL_OFF(0),
        .WB_ERROR(0),
        .BIST_MODE(1),
        .BIST_TEST_DATAMASK(0),
        .ECC_ENABLE(0),
        .SPEED_BIN(1),
        .SDRAM_CAPACITY(4)
    ) ddr3_top_inst (
        .i_controller_clk(controller_clk),
        .i_ddr3_clk(ddr3_clk),
        .i_ref_clk(ref_clk),
        .i_ddr3_clk_90(ddr3_clk_90),
        .i_rst_n(rst_n && clk_locked),

        .i_wb_cyc(1'b1),
        .i_wb_stb(1'b0),
        .i_wb_we(1'b0),
        .i_wb_addr({WB_ADDR_BITS{1'b0}}),
        .i_wb_data({WB_DATA_BITS{1'b0}}),
        .i_wb_sel({WB_SEL_BITS{1'b1}}),
        .i_aux(4'b0),
        .o_wb_stall(),
        .o_wb_ack(),
        .o_wb_err(),
        .o_wb_data(),
        .o_aux(),

        .i_wb2_cyc(1'b0),
        .i_wb2_stb(1'b0),
        .i_wb2_we(1'b0),
        .i_wb2_addr(32'b0),
        .i_wb2_data(32'b0),
        .i_wb2_sel(4'b0),
        .o_wb2_stall(),
        .o_wb2_ack(),
        .o_wb2_data(),

        .o_ddr3_clk_p(ddr3_ck_p),
        .o_ddr3_clk_n(ddr3_ck_n),
        .o_ddr3_reset_n(ddr3_reset_n),
        .o_ddr3_cke(ddr3_cke),
        .o_ddr3_cs_n(ddr3_cs_n),
        .o_ddr3_ras_n(ddr3_ras_n),
        .o_ddr3_cas_n(ddr3_cas_n),
        .o_ddr3_we_n(ddr3_we_n),
        .o_ddr3_addr(ddr3_addr),
        .o_ddr3_ba_addr(ddr3_ba),
        .io_ddr3_dq(ddr3_dq[7:0]),
        .io_ddr3_dqs(ddr3_dqs_p[0:0]),
        .io_ddr3_dqs_n(ddr3_dqs_n[0:0]),
        .o_ddr3_dm(ddr3_dm_unused),
        .o_ddr3_odt(ddr3_odt),
        .o_calib_complete(calib_complete),
        .o_debug1(debug1),
        .i_user_self_refresh(1'b0),
        .uart_tx(uart_tx_unused)
    );
endmodule

`default_nettype wire
