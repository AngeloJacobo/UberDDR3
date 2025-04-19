////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_phy.v
// Project: UberDDR3 - An Open Source DDR3 Controller
//
// Purpose: PHY component for the DDR3 controller. Handles the primitives such
// as IOSERDES, IODELAY, and IOBUF. These generates the signals connected to 
// the DDR3 RAM.
//
// Engineer: Angelo C. Jacobo
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2023-2025  Angelo Jacobo
// 
//     This program is free software: you can redistribute it and/or modify
//     it under the terms of the GNU General Public License as published by
//     the Free Software Foundation, either version 3 of the License, or
//     (at your option) any later version.
// 
//     This program is distributed in the hope that it will be useful,
//     but WITHOUT ANY WARRANTY; without even the implied warranty of
//     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//     GNU General Public License for more details.
// 
//     You should have received a copy of the GNU General Public License
//     along with this program.  If not, see <https://www.gnu.org/licenses/>.
//
////////////////////////////////////////////////////////////////////////////////

`default_nettype none
`timescale 1ps / 1ps
//`define DEBUG_DQS // uncomment to route the raw DQS to output port for debugging

module ddr3_phy_ecp5 #(
    parameter     CONTROLLER_CLK_PERIOD = 10_000, //ps, clock period of the controller interface
                  DDR3_CLK_PERIOD = 2_500, //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
                  ROW_BITS = 14,   //width of row address
                  BA_BITS = 3,
                  DQ_BITS = 8,
                  LANES = 8,
                  DUAL_RANK_DIMM = 0, // enable dual rank DIMM (1 =  enable, 0 = disable)
    parameter[0:0] ODELAY_SUPPORTED = 1, //set to 1 when ODELAYE2 is supported
                   USE_IO_TERMINATION = 0, //use IOBUF_DCIEN and IOBUFDS_DCIEN when 1
                   NO_IOSERDES_LOOPBACK = 1, // don't use IOSERDES loopback for bitslip training
                   LATTICE_ECP5 = 1, // 1 = Lattice ECP PHY, 0 = Xilinx PHY
              // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
    parameter serdes_ratio = 4, // this controller is fixed as a 4:1 memory controller (CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD = 4)
              wb_data_bits = DQ_BITS*LANES*serdes_ratio*2,
              wb_sel_bits = wb_data_bits / 8,
              //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
              cmd_len = 4 + 3 + BA_BITS + ROW_BITS + 2*DUAL_RANK_DIMM
    )(
        input wire i_controller_clk, i_ddr3_clk, i_ref_clk,
        input wire i_ddr3_clk_90, //required only when ODELAY_SUPPORTED is zero
        input wire i_rst_n,
        // Controller Interface
        input wire i_controller_reset,
        input wire[cmd_len*serdes_ratio-1:0] i_controller_cmd,
        input wire i_controller_dqs_tri_control, i_controller_dq_tri_control,
        input wire i_controller_toggle_dqs,
        input wire[wb_data_bits-1:0] i_controller_data,
        input wire[wb_sel_bits-1:0] i_controller_dm,
        input wire[4:0] i_controller_odelay_data_cntvaluein,i_controller_odelay_dqs_cntvaluein,
        input wire[4:0] i_controller_idelay_data_cntvaluein,i_controller_idelay_dqs_cntvaluein,
        input wire[LANES-1:0] i_controller_odelay_data_ld, i_controller_odelay_dqs_ld,
        input wire[LANES-1:0] i_controller_idelay_data_ld, i_controller_idelay_dqs_ld,
        input wire[LANES-1:0] i_controller_bitslip,
        input wire i_controller_write_leveling_calib,
        output wire[DQ_BITS*LANES*8-1:0] o_controller_iserdes_data,
        output wire[LANES*8-1:0] o_controller_iserdes_dqs,
        output wire[LANES*8-1:0] o_controller_iserdes_bitslip_reference,
        output wire o_controller_idelayctrl_rdy,
        // DDR3 I/O Interface
        output wire[DUAL_RANK_DIMM:0] o_ddr3_clk_p,o_ddr3_clk_n,
        output wire o_ddr3_reset_n,
        output wire[DUAL_RANK_DIMM:0] o_ddr3_cke, // CKE
        output wire[DUAL_RANK_DIMM:0] o_ddr3_cs_n, // chip select signal
        output wire o_ddr3_ras_n, // RAS#
        output wire o_ddr3_cas_n, // CAS#
        output wire o_ddr3_we_n, // WE#
        output wire[ROW_BITS-1:0] o_ddr3_addr,
        output wire[BA_BITS-1:0] o_ddr3_ba_addr,
        inout wire[(DQ_BITS*LANES)-1:0] io_ddr3_dq,
        inout wire[(DQ_BITS*LANES)/8-1:0] io_ddr3_dqs, io_ddr3_dqs_n,
        output wire[LANES-1:0] o_ddr3_dm,
        output wire[DUAL_RANK_DIMM:0] o_ddr3_odt, // on-die termination
        // DEBUG PHY
        output wire[(DQ_BITS*LANES)/8-1:0] o_ddr3_debug_read_dqs_p,
        output wire[(DQ_BITS*LANES)/8-1:0] o_ddr3_debug_read_dqs_n
    );

    // cmd bit assignment
    localparam CMD_CS_N_2 = cmd_len - 1,
                CMD_CS_N =  DUAL_RANK_DIMM[0]? cmd_len - 2 : cmd_len - 1,
                CMD_RAS_N = DUAL_RANK_DIMM[0]? cmd_len - 3 : cmd_len - 2,
                CMD_CAS_N = DUAL_RANK_DIMM[0]? cmd_len - 4 : cmd_len - 3,
                CMD_WE_N =  DUAL_RANK_DIMM[0]? cmd_len - 5 : cmd_len - 4,
                CMD_ODT =   DUAL_RANK_DIMM[0]? cmd_len - 6 : cmd_len - 5,
                CMD_CKE_2 = DUAL_RANK_DIMM[0]? cmd_len - 7 : cmd_len - 6,
                CMD_CKE =   DUAL_RANK_DIMM[0]? cmd_len - 8 : cmd_len - 6,
                CMD_RESET_N = DUAL_RANK_DIMM[0]? cmd_len - 9 : cmd_len - 7,
                CMD_BANK_START = BA_BITS + ROW_BITS - 1,
                CMD_ADDRESS_START = ROW_BITS - 1;
    localparam SYNC_RESET_DELAY = 52_000/CONTROLLER_CLK_PERIOD; //52_000 ps of reset pulse width required for IDELAYCTRL 
    localparam READ_DATA_DELAY = ( (DDR3_CLK_PERIOD/4)/25 > 127)? 127 : (DDR3_CLK_PERIOD/4)/25,
                WRITE_DQS_DELAY = ( (DDR3_CLK_PERIOD/4)/25 > 127)? 127 : (DDR3_CLK_PERIOD/4)/25,
                READ_DQS_DELAY = ( (DDR3_CLK_PERIOD/4)/25 > 127)? 127 : (DDR3_CLK_PERIOD/4)/25;
    localparam DATA_IDELAY_TAP = ((DDR3_CLK_PERIOD/4))/78.125; // delay incoming data by 90 degrees of DDR3_CLK_PERIOD
    genvar gen_index;
    wire[cmd_len-1:0] oserdes_cmd, //serialized(4:1) i_controller_cmd_slot_x 
                      cmd;//delayed oserdes_cmd
    wire[(DQ_BITS*LANES)-1:0] oserdes_data, odelay_data, idelay_data, read_dq;
    wire[LANES-1:0] oserdes_dm, odelay_dm;
    wire[LANES-1:0] odelay_dqs_p, odelay_dqs_n, read_dqs, idelay_dqs;
    wire[DQ_BITS*LANES-1:0] oserdes_dq_tri_control;
    wire[LANES-1:0] oserdes_dqs_p, oserdes_dqs_n;
    wire[LANES-1:0] oserdes_dqs_tri_control;
    wire[LANES-1:0] oserdes_bitslip_reference;
    reg[$clog2(SYNC_RESET_DELAY):0] delay_before_release_reset;
    reg sync_rst = 0;
    wire ddr3_clk;
    reg toggle_dqs_q; //past value of i_controller_toggle_dqs
    wire ddr3_clk_delayed;
    wire idelayctrl_rdy;
    wire dci_locked;
    reg[LANES*8-1:0] o_controller_iserdes_bitslip_reference_reg;
    reg[LANES - 1 : 0] shift_bitslip_index;
    
    // initial value of bitslip reference
    initial begin
        o_controller_iserdes_bitslip_reference_reg = {LANES{8'b0001_1110}};
        shift_bitslip_index = 0;
    end
                
    assign o_controller_idelayctrl_rdy = 1'b1;
    
`ifdef DEBUG_DQS
    assign o_ddr3_debug_read_dqs_p = io_ddr3_dqs;
    assign o_ddr3_debug_read_dqs_n = io_ddr3_dqs_n;
`else
    assign o_ddr3_debug_read_dqs_p = 0;
    assign o_ddr3_debug_read_dqs_n = 0;
`endif

    //synchronous reset
    always @(posedge i_controller_clk) begin
        if(!i_rst_n || i_controller_reset) begin
            sync_rst <= 1'b1;
            delay_before_release_reset <= SYNC_RESET_DELAY[$clog2(SYNC_RESET_DELAY):0];
            toggle_dqs_q <= 0;
        end
        else begin
            delay_before_release_reset <= (delay_before_release_reset == 0)? 0: delay_before_release_reset - 1;
            sync_rst <= !(delay_before_release_reset == 0);
            toggle_dqs_q <= i_controller_toggle_dqs;
        end
    end

    //PHY cmd 
    generate
        for(gen_index = 0; gen_index < cmd_len; gen_index = gen_index + 1) begin
            oserdes_soft #(.LATTICE_ECP5(LATTICE_ECP5)) oserdes_soft_cmd(
                .CLK(i_ddr3_clk), // High speed clock
                .CLKDIV(i_controller_clk), // Divided clock
                .RST(sync_rst), // Active high reset
                .D1(i_controller_cmd[cmd_len*0 + gen_index]),
                .D2(i_controller_cmd[cmd_len*0 + gen_index]),
                .D3(i_controller_cmd[cmd_len*1 + gen_index]),
                .D4(i_controller_cmd[cmd_len*1 + gen_index]),
                .D5(i_controller_cmd[cmd_len*2 + gen_index]),
                .D6(i_controller_cmd[cmd_len*2 + gen_index]),
                .D7(i_controller_cmd[cmd_len*3 + gen_index]),
                .D8(i_controller_cmd[cmd_len*3 + gen_index]),
                .OQ(oserdes_cmd[gen_index]) // Data path output
            );
        end
    endgenerate 

 
    assign o_ddr3_cs_n = oserdes_cmd[CMD_CS_N];
    assign o_ddr3_cke = oserdes_cmd[CMD_CKE];
    assign o_ddr3_odt = oserdes_cmd[CMD_ODT];
    assign o_ddr3_ras_n = oserdes_cmd[CMD_RAS_N],
           o_ddr3_cas_n = oserdes_cmd[CMD_CAS_N],
           o_ddr3_we_n = oserdes_cmd[CMD_WE_N],
           o_ddr3_reset_n = oserdes_cmd[CMD_RESET_N],
           o_ddr3_ba_addr = oserdes_cmd[CMD_BANK_START:CMD_ADDRESS_START+1],
           o_ddr3_addr = oserdes_cmd[CMD_ADDRESS_START:0];
    
    assign o_ddr3_clk_p = !i_ddr3_clk;
    assign o_ddr3_clk_n = i_ddr3_clk;
    
    // PHY data and dm
    generate
        // Output data: oserdes_soft -> BB
        // Input data: BB -> DELAYG -> iserdes_soft
        for(gen_index = 0; gen_index < (DQ_BITS*LANES); gen_index = gen_index + 1) begin
            oserdes_soft #(.LATTICE_ECP5(LATTICE_ECP5)) oserdes_soft_data(
                .CLK(i_ddr3_clk), // High speed clock
                .CLKDIV(i_controller_clk), // Divided clock
                .RST(sync_rst), // Active high reset
                .D1(i_controller_data[gen_index + (DQ_BITS*LANES)*0]),
                .D2(i_controller_data[gen_index + (DQ_BITS*LANES)*1]),
                .D3(i_controller_data[gen_index + (DQ_BITS*LANES)*2]),
                .D4(i_controller_data[gen_index + (DQ_BITS*LANES)*3]),
                .D5(i_controller_data[gen_index + (DQ_BITS*LANES)*4]),
                .D6(i_controller_data[gen_index + (DQ_BITS*LANES)*5]),
                .D7(i_controller_data[gen_index + (DQ_BITS*LANES)*6]),
                .D8(i_controller_data[gen_index + (DQ_BITS*LANES)*7]),
                .OQ(oserdes_data[gen_index]) // Data path output
            );

            if(LATTICE_ECP5) begin
                BB BB_data (
                    .I(oserdes_data[gen_index]),
                    .O(read_dq[gen_index]),
                    .T(i_controller_dq_tri_control),
                    .B(io_ddr3_dq[gen_index])
                );

                DELAYG #(
                    .DEL_MODE("USER_DEFINED"),
                    .DEL_VALUE(READ_DATA_DELAY)
                ) DELAYG_data
                (
                    .A(read_dq[gen_index]),
                    .Z(idelay_data[gen_index])
                );
            end // end of LATTICE_ECP5
            else begin // XILINX
                IOBUF IOBUF_data (
                    .I(oserdes_data[gen_index]), 
                    .O(read_dq[gen_index]),
                    .T(i_controller_dq_tri_control), 
                    .IO(io_ddr3_dq[gen_index])
                );
                
                IDELAYE2 #(
                .DELAY_SRC("IDATAIN"), // Delay input (IDATAIN, DATAIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), //Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .IDELAY_TYPE("FIXED"), //FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .IDELAY_VALUE(DATA_IDELAY_TAP > 31? 31 : DATA_IDELAY_TAP), //Input delay tap setting (0-31)
                .PIPE_SEL("FALSE"),  //Select pipelined mode, FALSE, TRUE
                .REFCLK_FREQUENCY(200.0), //IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") //DATA, CLOCK input signal
                )
                IDELAYE2_data (
                    .CNTVALUEOUT(), // 5-bit output: Counter value output
                    .DATAOUT(idelay_data[gen_index]), // 1-bit output: Delayed data output
                    .C(i_controller_clk), // 1-bit input: Clock input
                    .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                    .CINVCTRL(1'b0),// 1-bit input: Dynamic clock inversion input
                    .CNTVALUEIN(0), // 5-bit input: Counter value input
                    .DATAIN(0), //1-bit input: Internal delay data input
                    .IDATAIN(read_dq[gen_index]), // 1-bit input: Data input from the I/O
                    .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                    .LD(0), // 1-bit input: Load IDELAY_VALUE input
                    .LDPIPEEN(1'b0), // 1-bit input: Enable PIPELINE register to load data input
                    .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
                );

            end // end of XILINX
            
            iserdes_soft #(.LATTICE_ECP5(LATTICE_ECP5)) iserdes_soft_data(
                .CLK(i_ddr3_clk), // High speed clock
                .CLKDIV(i_controller_clk), // Divided clock
                .RST(sync_rst), // Active high reset
                .Q1(o_controller_iserdes_data[(DQ_BITS*LANES)*0 + gen_index]),
                .Q2(o_controller_iserdes_data[(DQ_BITS*LANES)*1 + gen_index]),
                .Q3(o_controller_iserdes_data[(DQ_BITS*LANES)*2 + gen_index]),
                .Q4(o_controller_iserdes_data[(DQ_BITS*LANES)*3 + gen_index]),
                .Q5(o_controller_iserdes_data[(DQ_BITS*LANES)*4 + gen_index]),
                .Q6(o_controller_iserdes_data[(DQ_BITS*LANES)*5 + gen_index]),
                .Q7(o_controller_iserdes_data[(DQ_BITS*LANES)*6 + gen_index]),
                .Q8(o_controller_iserdes_data[(DQ_BITS*LANES)*7 + gen_index]),
                .D(idelay_data[gen_index]), // Data path output
                .bitslip(i_controller_bitslip[gen_index/8])
            );
        end
        
        // data mask: oserdes -> o_ddr3_dm
        for(gen_index = 0; gen_index < LANES; gen_index = gen_index + 1) begin
            oserdes_soft #(.LATTICE_ECP5(LATTICE_ECP5)) oserdes_soft_dm(
                .CLK(i_ddr3_clk), // High speed clock
                .CLKDIV(i_controller_clk), // Divided clock
                .RST(sync_rst), // Active high reset
                .D1(i_controller_dm[gen_index + LANES*0]),
                .D2(i_controller_dm[gen_index + LANES*1]),
                .D3(i_controller_dm[gen_index + LANES*2]),
                .D4(i_controller_dm[gen_index + LANES*3]),
                .D5(i_controller_dm[gen_index + LANES*4]),
                .D6(i_controller_dm[gen_index + LANES*5]),
                .D7(i_controller_dm[gen_index + LANES*6]),
                .D8(i_controller_dm[gen_index + LANES*7]),
                .OQ(o_ddr3_dm[gen_index]) // Data path output
            );
        end

        // dqs output: oserdes_soft -> DELAYG -> BB
        // dqs input: BB -> DELAYG -> iserdes_soft
        for(gen_index = 0; gen_index < LANES; gen_index = gen_index + 1) begin
            if(LATTICE_ECP5) begin
                // oserdes_soft #(.LATTICE_ECP5(LATTICE_ECP5)) oserdes_soft_dqs_p(
                //     .CLK(i_ddr3_clk), // High speed clock
                //     .CLKDIV(i_controller_clk), // Divided clock
                //     .RST(sync_rst), // Active high reset
                //     .D1(1'b1), 
                //     .D2(1'b0),
                //     .D3(1'b1),
                //     .D4(1'b0),
                //     .D5(1'b1),
                //     .D6(1'b0),
                //     .D7(1'b1),
                //     .D8(1'b0),
                //     .OQ(oserdes_dqs_p[gen_index]) // Data path output
                // );

                // oserdes_soft #(.LATTICE_ECP5(LATTICE_ECP5)) oserdes_soft_dqs_n(
                //     .CLK(i_ddr3_clk), // High speed clock
                //     .CLKDIV(i_controller_clk), // Divided clock
                //     .RST(sync_rst), // Active high reset
                //     .D1(1'b0), //the last part will still have half dqs series
                //     .D2(1'b1),
                //     .D3(1'b0),
                //     .D4(1'b1),
                //     .D5(1'b0),
                //     .D6(1'b1),
                //     .D7(1'b0),
                //     .D8(1'b1),
                //     .OQ(oserdes_dqs_n[gen_index]) // Data path output
                // );

                // DELAYG #(
                //     .DEL_MODE("USER_DEFINED")
                //     ,.DEL_VALUE(WRITE_DQS_DELAY)
                // ) DELAYG_odqs_p
                // (
                //     .A(oserdes_dqs_p[gen_index]),
                //     .Z(odelay_dqs_p[gen_index])
                // );

                // DELAYG #(
                //     .DEL_MODE("USER_DEFINED")
                //     ,.DEL_VALUE(WRITE_DQS_DELAY)
                // ) DELAYG_odqs_n
                // (
                //     .A(oserdes_dqs_n[gen_index]),
                //     .Z(odelay_dqs_n[gen_index])
                // );
                
                BB BB_dqs_p (
                    .I(i_ddr3_clk_90),
                    .O(),
                    .T(i_controller_dqs_tri_control),
                    .B(io_ddr3_dqs[gen_index])
                );
                BB BB_dqs_n (
                    .I(!i_ddr3_clk_90),
                    .O(),
                    .T(i_controller_dqs_tri_control),
                    .B(io_ddr3_dqs_n[gen_index])
                );
            end // end of LATTICE_ECP5
            else begin // XILINX 
                IOBUF IOBUF_dqs_p(
                    .I(i_ddr3_clk_90), 
                    .O(),
                    .T(i_controller_dqs_tri_control), 
                    .IO(io_ddr3_dqs[gen_index])
                );

                IOBUF IOBUF_dqs_n(
                    .I(!i_ddr3_clk_90), 
                    .O(),
                    .T(i_controller_dqs_tri_control), 
                    .IO(io_ddr3_dqs_n[gen_index])
                );
            end // end of XILINX
      
        end
     endgenerate 
     
     generate 
        if(!LATTICE_ECP5) begin
            IDELAYCTRL IDELAYCTRL_inst (
                .RDY(), // 1-bit output: Ready output
                .REFCLK(i_ref_clk), // 1-bit input: Reference clock input.The frequency of REFCLK must be 200 MHz to guarantee the tap-delay value specified in the applicable data sheet.
                .RST(sync_rst) // 1-bit input: Active high reset input, To ,Minimum Reset pulse width is 52ns
            );
        end
     endgenerate
endmodule
