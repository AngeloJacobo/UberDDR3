`default_nettype none
`timescale 1ps / 1ps
//`define DEBUG_DQS

module ddr3_phy #(
   parameter real CONTROLLER_CLK_PERIOD = 12, //ns, period of clock input to this DDR3 controller module
                  DDR3_CLK_PERIOD = 3, //ns, period of clock input to DDR3 RAM device 
   parameter      ROW_BITS = 14,
                  BA_BITS = 3,
                  DQ_BITS = 8,
                  LANES = 8,
    parameter[0:0] ODELAY_SUPPORTED = 1, //set to 1 when ODELAYE2 is supported
                   USE_IO_TERMINATION = 0, //use IOBUF_DCIEN and IOBUFDS_DCIEN when 1
              // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
    parameter serdes_ratio = $rtoi(CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD),
              wb_data_bits = DQ_BITS*LANES*serdes_ratio*2,
              wb_sel_bits = wb_data_bits / 8,
              //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
              cmd_len = 4 + 3 + BA_BITS + ROW_BITS
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
        output wire o_ddr3_clk_p,o_ddr3_clk_n,
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
        // DEBUG PHY
        output wire[(DQ_BITS*LANES)/8-1:0] o_ddr3_debug_read_dqs_p,
        output wire[(DQ_BITS*LANES)/8-1:0] o_ddr3_debug_read_dqs_n
    );

    // cmd bit assignment
    localparam CMD_CS_N = cmd_len - 1, 
               CMD_RAS_N = cmd_len - 2,
               CMD_CAS_N= cmd_len - 3,
               CMD_WE_N = cmd_len - 4,
               CMD_ODT = cmd_len - 5,
               CMD_CKE = cmd_len - 6, 
               CMD_RESET_N = cmd_len - 7,
               CMD_BANK_START = BA_BITS + ROW_BITS - 1,
               CMD_ADDRESS_START = ROW_BITS - 1;
    localparam SYNC_RESET_DELAY = $rtoi($ceil(1000/CONTROLLER_CLK_PERIOD)); //52 ns of reset pulse width required for IDELAYCTRL 
    //cmd needs to be center-aligned to the positive edge of the 
    //ddr3_clk. This means cmd needs to be delayed by half the ddr3
    //clk period. Subtract by 600ps to include the IODELAY insertion
    //delay. Divide by a delay resolution of 78.125ps per tap to get 
    //the needed tap value.
    localparam CMD_ODELAY_TAP = ((DDR3_CLK_PERIOD*1000/2) - 600)/78.125;

    // Data does not have to be delayed (DQS is the on that has to be
    // delayed and center-aligned to the center eye of data)
    localparam DATA_ODELAY_TAP = 0; 

    //DQS needs to be edge-aligned to the center eye of the data. 
    //This means DQS needs to be delayed by a quarter of the ddr3
    //clk period relative to the data. Subtract by 600ps to include
    //the IODELAY insertion delay. Divide by a delay resolution of 
    //78.125ps per tap to get the needed tap value. Then add the tap
    //value used in data to have the delay relative to the data.
    localparam DQS_ODELAY_TAP = ((DDR3_CLK_PERIOD*1000/4))/78.125 + DATA_ODELAY_TAP;
    
    //Incoming DQS should be 90 degree delayed relative to incoming data
    localparam DATA_IDELAY_TAP = 0; //600ps delay
    localparam DQS_IDELAY_TAP = ((DDR3_CLK_PERIOD*1000/4))/78.125 + DATA_IDELAY_TAP;
    
    genvar gen_index;
    wire[cmd_len-1:0] oserdes_cmd, //serialized(4:1) i_controller_cmd_slot_x 
                      cmd;//delayed oserdes_cmd
    wire[(DQ_BITS*LANES)-1:0] oserdes_data, odelay_data, idelay_data, read_dq;
    wire[LANES-1:0] oserdes_dm, odelay_dm;
    wire[LANES-1:0] odelay_dqs, read_dqs, idelay_dqs;
    wire[DQ_BITS*LANES-1:0] oserdes_dq_tri_control;
    wire[LANES-1:0] oserdes_dqs;
    wire[LANES-1:0] oserdes_dqs_tri_control;
    wire[LANES-1:0] oserdes_bitslip_reference;
    reg[$clog2(SYNC_RESET_DELAY):0] delay_before_release_reset;
    reg sync_rst = 0;
    wire ddr3_clk;
    reg toggle_dqs_q; //past value of i_controller_toggle_dqs
    wire ddr3_clk_delayed;
    wire idelayctrl_rdy;
    wire dci_locked;
    
    assign o_controller_idelayctrl_rdy = idelayctrl_rdy && dci_locked;
    
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
            // OSERDESE2: Output SERial/DESerializer with bitslip
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            OSERDESE2 #(
                .DATA_RATE_OQ("SDR"), // DDR, SDR
                .DATA_RATE_TQ("SDR"), // DDR, SDR
                .DATA_WIDTH(4), // Parallel data width (2-8,10,14)
                .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
                .TRISTATE_WIDTH(1)
            )
            OSERDESE2_cmd(
                .OFB(), // 1-bit output: Feedback path for data
                .OQ(oserdes_cmd[gen_index]), // 1-bit output: Data path output
                .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                .D1(i_controller_cmd[cmd_len*0 + gen_index]),
                .D2(i_controller_cmd[cmd_len*1 + gen_index]),
                .D3(i_controller_cmd[cmd_len*2 + gen_index]),
                .D4(i_controller_cmd[cmd_len*3 + gen_index]),
                .OCE(1'b1), // 1-bit input: Output data clock enable
                .RST(sync_rst), // 1-bit input: Reset
                // unused signals but were added here to make vivado happy
                .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                .SHIFTOUT2(),
                .TBYTEOUT(), // 1-bit output: Byte group tristate
                .TFB(), // 1-bit output: 3-state control
                .TQ(), // 1-bit output: 3-state control
                .D5(),
                .D6(),
                .D7(),
                .D8(),
                // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                .SHIFTIN1(0),
                .SHIFTIN2(0),
                // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                .T1(0),
                .T2(0),
                .T3(0),
                .T4(0),
                .TBYTEIN(0),
                // 1-bit input: Byte group tristate
                .TCE(0)
                // 1-bit input: 3-state clock enable
            );
            // End of OSERDESE2_inst instantiation
      
        end
    endgenerate 

    assign o_ddr3_cs_n = oserdes_cmd[CMD_CS_N],
           o_ddr3_ras_n = oserdes_cmd[CMD_RAS_N],
           o_ddr3_cas_n = oserdes_cmd[CMD_CAS_N],
           o_ddr3_we_n = oserdes_cmd[CMD_WE_N],
           o_ddr3_odt = oserdes_cmd[CMD_ODT],
           o_ddr3_cke = oserdes_cmd[CMD_CKE],
           o_ddr3_reset_n = oserdes_cmd[CMD_RESET_N],
           o_ddr3_ba_addr = oserdes_cmd[CMD_BANK_START:CMD_ADDRESS_START+1],
           o_ddr3_addr = oserdes_cmd[CMD_ADDRESS_START:0];
    
    if(ODELAY_SUPPORTED) begin
        // OSERDESE2: Output SERial/DESerializer with bitslip
        //7 Series
        // Xilinx HDL Libraries Guide, version 13.4
        OSERDESE2 #(
            .DATA_RATE_OQ("DDR"), // DDR, SDR
            .DATA_RATE_TQ("SDR"), // DDR, SDR
            .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
            .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
            .TRISTATE_WIDTH(1)
        )
        OSERDESE2_clk(
            .OFB(ddr3_clk), // 1-bit output: Feedback path for data
            .OQ(), // 1-bit output: Data path output
            .CLK(i_ddr3_clk), // 1-bit input: High speed clock
            .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
            // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
            .D1(1'b1),
            .D2(1'b0),
            .D3(1'b1),
            .D4(1'b0),
            .D5(1'b1),
            .D6(1'b0),
            .D7(1'b1),
            .D8(1'b0),
            .OCE(1'b1), // 1-bit input: Output data clock enable
            .RST(sync_rst), // 1-bit input: Reset
             // unused signals but were added here to make vivado happy
            .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
            .SHIFTOUT2(),
            .TBYTEOUT(), // 1-bit output: Byte group tristate
            .TFB(), // 1-bit output: 3-state control
            .TQ(), // 1-bit output: 3-state control
            // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
            .SHIFTIN1(0),
            .SHIFTIN2(0),
            // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
            .T1(0),
            .T2(0),
            .T3(0),
            .T4(0),
            .TBYTEIN(0),
            // 1-bit input: Byte group tristate
            .TCE(0)
            // 1-bit input: 3-state clock enable
        );
        // End of OSERDESE2_inst instantiation

        (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
            //Delay the DQ
            // Delay resolution: 1/(32 x 2 x F REF ) = 78.125ps
            ODELAYE2 #(
                .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter to 5ps ("TRUE"), Reduced power but high jitter 9ns ("FALSE")
                .ODELAY_TYPE("FIXED"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .ODELAY_VALUE(CMD_ODELAY_TAP), // Output delay tap setting (0-31)
                .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
            )
            ODELAYE2_clk (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(ddr3_clk_delayed), // 1-bit output: Delayed data/clock output
                .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(1'b0), // 1-bit input: Dynamic clock inversion input
                .CLKIN(1'b0), // 1-bit input: Clock delay input
                .CNTVALUEIN(5'd0), // 5-bit input: Counter value input
                .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                .LD(1'b0), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                            // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                .LDPIPEEN(1'b0), // 1-bit input: Enables the pipeline register to load data
                .ODATAIN(ddr3_clk), // 1-bit input: Output delay data input
                .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
            );
        
        // OBUFDS: Differential Output Buffer
        // 7 Series
        // Xilinx HDL Libraries Guide, version 13.4
        OBUFDS OBUFDS_inst (
        .O(o_ddr3_clk_p), // Diff_p output (connect directly to top-level port)
        .OB(o_ddr3_clk_n), // Diff_n output (connect directly to top-level port)
        .I(ddr3_clk_delayed) // Buffer input
        );
        // End of OBUFDS_inst instantiation
    end
    else begin //ODELAY is not supported
        // OBUFDS: Differential Output Buffer
        // 7 Series
        // Xilinx HDL Libraries Guide, version 13.4
        OBUFDS OBUFDS_inst (
        .O(o_ddr3_clk_p), // Diff_p output (connect directly to top-level port)
        .OB(o_ddr3_clk_n), // Diff_n output (connect directly to top-level port)
        .I(!i_ddr3_clk) // Buffer input
        );
    end
    
    
    // PHY data and dm
    generate
        // data: oserdes -> odelay -> iobuf
        for(gen_index = 0; gen_index < (DQ_BITS*LANES); gen_index = gen_index + 1) begin
            
            if (ODELAY_SUPPORTED) begin
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_data(
                    .OFB(oserdes_data[gen_index]), // 1-bit output: Feedback path for data
                    .OQ(), // 1-bit output: Data path output
                    .TQ(oserdes_dq_tri_control[gen_index]),
                    .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(i_controller_data[gen_index + (DQ_BITS*LANES)*0]),
                    .D2(i_controller_data[gen_index + (DQ_BITS*LANES)*1]),
                    .D3(i_controller_data[gen_index + (DQ_BITS*LANES)*2]),
                    .D4(i_controller_data[gen_index + (DQ_BITS*LANES)*3]),
                    .D5(i_controller_data[gen_index + (DQ_BITS*LANES)*4]),
                    .D6(i_controller_data[gen_index + (DQ_BITS*LANES)*5]),
                    .D7(i_controller_data[gen_index + (DQ_BITS*LANES)*6]),
                    .D8(i_controller_data[gen_index + (DQ_BITS*LANES)*7]),
                    .T1(i_controller_dq_tri_control),
                    .TCE(1'b1),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                    // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0)
                    // 1-bit input: Byte group tristate
                );
                // End of OSERDESE2_inst instantiation
            
                // ODELAYE2: Output Fixed or Variable Delay Element
                // 7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                //odelay adds an insertion delay of 600ps to the actual delay setting: https://support.xilinx.com/s/article/42133?language=en_US
                (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
                //Delay the DQ
                // Delay resolution: 1/(32 x 2 x F REF ) = 78.125ps
                ODELAYE2 #(
                    .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                    .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter to 5ps ("TRUE"), Reduced power but high jitter 9ns ("FALSE")
                    .ODELAY_TYPE("VAR_LOAD"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                    .ODELAY_VALUE(DATA_ODELAY_TAP), // Output delay tap setting (0-31)
                    .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                    .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
                )
                ODELAYE2_data (
                    .CNTVALUEOUT(), // 5-bit output: Counter value output
                    .DATAOUT(odelay_data[gen_index]), // 1-bit output: Delayed data/clock output
                    .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                    .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                    .CINVCTRL(1'b0), // 1-bit input: Dynamic clock inversion input
                    .CLKIN(1'b0), // 1-bit input: Clock delay input
                    .CNTVALUEIN(i_controller_odelay_data_cntvaluein), // 5-bit input: Counter value input
                    .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                    .LD(i_controller_odelay_data_ld[gen_index/8]), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                                // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                    .LDPIPEEN(1'b0), // 1-bit input: Enables the pipeline register to load data
                    .ODATAIN(oserdes_data[gen_index]), // 1-bit input: Output delay data input
                    .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
                );

                if(USE_IO_TERMINATION) begin 
                    // IOBUF_DCIEN: Single-ended Bi-directional Buffer with Digital Controlled Impedance (DCI)
                    // and Input path enable/disable
                    // May only be placed in High Performance (HP) Banks
                    // 7 Series
                    // Xilinx HDL Libraries Guide, version 13.4
                    IOBUF_DCIEN #(
                    .IBUF_LOW_PWR("FALSE"), // Low Power - "TRUE", High Performance = "FALSE"
                    .SLEW("FAST"), // Specify the output slew rate
                    .USE_IBUFDISABLE("FALSE") // Use IBUFDISABLE function, "TRUE" or "FALSE"
                    ) IOBUF_DCIEN_data (
                        .O(read_dq[gen_index]), // Buffer output
                        .IO(io_ddr3_dq[gen_index]), // Buffer inout port (connect directly to top-level port)
                        .DCITERMDISABLE(1'b0), // DCI Termination enable input
                        .I(odelay_data[gen_index]), // Buffer input
                        .IBUFDISABLE(1'b0), // Input disable input, low=disable
                        .T(oserdes_dq_tri_control[gen_index]) // 3-state enable input, high=input, low=output
                    );
                    // End of IOBUF_DCIEN_inst instantiation

                 end
                 else begin                         
                    // IOBUF: Single-ended Bi-directional Buffer
                    //All devices
                    // Xilinx HDL Libraries Guide, version 13.4
                    IOBUF #(
                        //.DRIVE(12), // Specify the output drive strength
                        .IBUF_LOW_PWR("FALSE"), // Low Power - "TRUE", High Performance = "FALSE"
                        //.IOSTANDARD("SSTL15"), // Specify the I/O standard
                        .SLEW("FAST") // Specify the output slew rate
                    ) IOBUF_data (
                        .O(read_dq[gen_index]),// Buffer output
                        .IO(io_ddr3_dq[gen_index]), // Buffer inout port (connect directly to top-level port)
                        .I(odelay_data[gen_index]), // Buffer input
                        .T(oserdes_dq_tri_control[gen_index]) // 3-state enable input, high=read, low=write
                    );
                 end
            end
            else begin //ODELAY is not supported
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_data(
                    .OFB(), // 1-bit output: Feedback path for data
                    .OQ(oserdes_data[gen_index]), // 1-bit output: Data path output
                    .TQ(oserdes_dq_tri_control[gen_index]),
                    .CLK(i_ddr3_clk_90), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(i_controller_data[gen_index + (DQ_BITS*LANES)*0]),
                    .D2(i_controller_data[gen_index + (DQ_BITS*LANES)*1]),
                    .D3(i_controller_data[gen_index + (DQ_BITS*LANES)*2]),
                    .D4(i_controller_data[gen_index + (DQ_BITS*LANES)*3]),
                    .D5(i_controller_data[gen_index + (DQ_BITS*LANES)*4]),
                    .D6(i_controller_data[gen_index + (DQ_BITS*LANES)*5]),
                    .D7(i_controller_data[gen_index + (DQ_BITS*LANES)*6]),
                    .D8(i_controller_data[gen_index + (DQ_BITS*LANES)*7]),
                    .T1(i_controller_dq_tri_control),
                    .TCE(1'b1),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                    // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0)
                    // 1-bit input: Byte group tristate
                );
                // End of OSERDESE2_inst instantiation
                
                // IOBUF: Single-ended Bi-directional Buffer
                //All devices
                // Xilinx HDL Libraries Guide, version 13.4
                IOBUF #(
                    //.DRIVE(12), // Specify the output drive strength
                    .IBUF_LOW_PWR("FALSE"), // Low Power - "TRUE", High Performance = "FALSE"
                    //.IOSTANDARD("SSTL15"), // Specify the I/O standard
                    .SLEW("FAST") // Specify the output slew rate
                ) IOBUF_data (
                    .O(read_dq[gen_index]),// Buffer output
                    .IO(io_ddr3_dq[gen_index]), // Buffer inout port (connect directly to top-level port)
                    .I(oserdes_data[gen_index]), // Buffer input
                    .T(oserdes_dq_tri_control[gen_index]) // 3-state enable input, high=read, low=write
                );
            end

            // IDELAYE2: Input Fixed or Variable Delay Element
            // 7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
            IDELAYE2 #(
                .DELAY_SRC("IDATAIN"), // Delay input (IDATAIN, DATAIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), //Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .IDELAY_TYPE("VAR_LOAD"), //FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .IDELAY_VALUE(DATA_IDELAY_TAP), //Input delay tap setting (0-31)
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
                .CNTVALUEIN(i_controller_idelay_data_cntvaluein), // 5-bit input: Counter value input
                .DATAIN(), //1-bit input: Internal delay data input
                .IDATAIN(read_dq[gen_index]), // 1-bit input: Data input from the I/O
                .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                .LD(i_controller_idelay_data_ld[gen_index/8]), // 1-bit input: Load IDELAY_VALUE input
                .LDPIPEEN(1'b0), // 1-bit input: Enable PIPELINE register to load data input
                .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
            );
            // End of IDELAYE2_inst instantiation

            // End of IOBUF_inst instantiation                 
            // ISERDESE2: Input SERial/DESerializer with bitslip
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            ISERDESE2 #(
                .DATA_RATE("DDR"), // DDR, SDR
                .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                // INIT_Q1 - INIT_Q4: Initial value on the Q outputs (0/1)
                .INIT_Q1(1'b0),
                .INIT_Q2(1'b0),
                .INIT_Q3(1'b0),
                .INIT_Q4(1'b0),
                .INTERFACE_TYPE("NETWORKING"), // MEMORY, MEMORY_DDR3, MEMORY_QDR, NETWORKING, OVERSAMPLE
                .IOBDELAY("IFD"), // NONE, BOTH, IBUF, IFD
                .NUM_CE(1),// Number of clock enables (1,2)
                .OFB_USED("FALSE"), // Select OFB path (FALSE, TRUE)
                // SRVAL_Q1 - SRVAL_Q4: Q output values when SR is used (0/1)
                .SRVAL_Q1(1'b0),
                .SRVAL_Q2(1'b0),
                .SRVAL_Q3(1'b0),
                .SRVAL_Q4(1'b0)
            )
            ISERDESE2_data (
                .O(),
                // 1-bit output: Combinatorial output
                // Q1 - Q8: 1-bit (each) output: Registered data outputs
                .Q1(o_controller_iserdes_data[(DQ_BITS*LANES)*7 + gen_index]),//56
                .Q2(o_controller_iserdes_data[(DQ_BITS*LANES)*6 + gen_index]), //48
                .Q3(o_controller_iserdes_data[(DQ_BITS*LANES)*5 + gen_index]),
                .Q4(o_controller_iserdes_data[(DQ_BITS*LANES)*4 + gen_index]),   
                .Q5(o_controller_iserdes_data[(DQ_BITS*LANES)*3 + gen_index]),
                .Q6(o_controller_iserdes_data[(DQ_BITS*LANES)*2 + gen_index]),
                .Q7(o_controller_iserdes_data[(DQ_BITS*LANES)*1 + gen_index]), 
                .Q8(o_controller_iserdes_data[(DQ_BITS*LANES)*0 + gen_index]),
                // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
                .SHIFTOUT1(),
                .SHIFTOUT2(),
                .BITSLIP(i_controller_bitslip[gen_index/8]),
                // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
                // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
                // to Q8 output ports will shift, as in a barrel-shifter operation, one
                // position every time Bitslip is invoked (DDR operation is different from
                // SDR).
                // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
                .CE1(1'b1),
                .CE2(1'b1),
                .CLKDIVP(), // 1-bit input: TBD
                // Clocks: 1-bit (each) input: ISERDESE2 clock input ports
                .CLK(i_ddr3_clk), // 1-bit input: High-speed clock
                .CLKB(!i_ddr3_clk), // 1-bit input: High-speed secondary clock
                .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                .OCLK(), // 1-bit input: High speed output clock used when INTERFACE_TYPE="MEMORY"
                // Dynamic Clock Inversions: 1-bit (each) input: Dynamic clock inversion pins to switch clock polarity
                .DYNCLKDIVSEL(), // 1-bit input: Dynamic CLKDIV inversion
                .DYNCLKSEL(), // 1-bit input: Dynamic CLK/CLKB inversion
                // Input Data: 1-bit (each) input: ISERDESE2 data input ports
                .D(), // 1-bit input: Data input
                .DDLY(idelay_data[gen_index]), // 1-bit input: Serial data from IDELAYE2
                .OFB(), // 1-bit input: Data feedback from OSERDESE2
                .OCLKB(), // 1-bit input: High speed negative edge output clock
                .RST(sync_rst), // 1-bit input: Active high asynchronous reset
                // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
                .SHIFTIN1(),
                .SHIFTIN2()
            );
            // End of ISERDESE2_inst instantiation
  
        end
        
        // data mask: oserdes -> odelay -> obuf
        for(gen_index = 0; gen_index < LANES; gen_index = gen_index + 1) begin
 
            
            if(ODELAY_SUPPORTED) begin
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_dm(
                    .OFB(oserdes_dm[gen_index]), // 1-bit output: Feedback path for data
                    .OQ(), // 1-bit output: Data path output
                    .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(i_controller_dm[gen_index + LANES*0]),
                    .D2(i_controller_dm[gen_index + LANES*1]),
                    .D3(i_controller_dm[gen_index + LANES*2]),
                    .D4(i_controller_dm[gen_index + LANES*3]),
                    .D5(i_controller_dm[gen_index + LANES*4]),
                    .D6(i_controller_dm[gen_index + LANES*5]),
                    .D7(i_controller_dm[gen_index + LANES*6]),
                    .D8(i_controller_dm[gen_index + LANES*7]), 
                    .TCE(1'b0),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                     // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    .TQ(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T1(0),
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0)
                    // 1-bit input: Byte group tristate
                );
                // End of OSERDESE2_inst instantiation
            
                // ODELAYE2: Output Fixed or Variable Delay Element
                // 7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                //odelay adds an insertion delay of 600ps to the actual delay setting: https://support.xilinx.com/s/article/42133?language=en_US
                (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
                //Delay the DQ
                // Delay resolution: 1/(32 x 2 x F REF ) = 78.125ps
                ODELAYE2 #(
                    .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                    .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter to 5ps ("TRUE"), Reduced power but high jitter 9ns ("FALSE")
                    .ODELAY_TYPE("VAR_LOAD"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                    .ODELAY_VALUE(DATA_ODELAY_TAP), // Output delay tap setting (0-31)
                    .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                    .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
                )
                ODELAYE2_dm (
                    .CNTVALUEOUT(), // 5-bit output: Counter value output
                    .DATAOUT(odelay_dm[gen_index]), // 1-bit output: Delayed data/clock output
                    .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                    .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                    .CINVCTRL(1'b0), // 1-bit input: Dynamic clock inversion input
                    .CLKIN(1'b0), // 1-bit input: Clock delay input
                    .CNTVALUEIN(i_controller_odelay_data_cntvaluein), // 5-bit input: Counter value input
                    .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                    .LD(i_controller_odelay_data_ld[gen_index]), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                                // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                    .LDPIPEEN(1'b0), // 1-bit input: Enables the pipeline register to load data
                    .ODATAIN(oserdes_dm[gen_index]), // 1-bit input: Output delay data input
                    .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
                );
                
                // OBUF: Single-ended Output Buffer
                // 7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OBUF #(
                //.IOSTANDARD("SSTL_15"), // Specify the output I/O standard
                .SLEW("FAST") // Specify the output slew rate
                ) OBUF_dm (
                    .O(o_ddr3_dm[gen_index]), // Buffer output (connect directly to top-level port)
                    .I(odelay_dm[gen_index]) // Buffer input
                );
                // End of OBUF_inst instantiation
            end
            else begin
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b0), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_dm(
                    .OFB(), // 1-bit output: Feedback path for data
                    .OQ(oserdes_dm[gen_index]), // 1-bit output: Data path output
                    .CLK(i_ddr3_clk_90), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(i_controller_dm[gen_index + LANES*0]),
                    .D2(i_controller_dm[gen_index + LANES*1]),
                    .D3(i_controller_dm[gen_index + LANES*2]),
                    .D4(i_controller_dm[gen_index + LANES*3]),
                    .D5(i_controller_dm[gen_index + LANES*4]),
                    .D6(i_controller_dm[gen_index + LANES*5]),
                    .D7(i_controller_dm[gen_index + LANES*6]),
                    .D8(i_controller_dm[gen_index + LANES*7]), 
                    .TCE(1'b0),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                     // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    .TQ(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T1(0),
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0)
                    // 1-bit input: Byte group tristate
                );
                // End of OSERDESE2_inst instantiation
            
                // OBUF: Single-ended Output Buffer
                // 7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OBUF #(
                //.IOSTANDARD("SSTL_15"), // Specify the output I/O standard
                .SLEW("FAST") // Specify the output slew rate
                ) OBUF_dm (
                    .O(o_ddr3_dm[gen_index]), // Buffer output (connect directly to top-level port)
                    .I(oserdes_dm[gen_index]) // Buffer input
                );
                // End of OBUF_inst instantiation
            
            end
        end

        // dqs: odelay -> iobuf
        for(gen_index = 0; gen_index < LANES; gen_index = gen_index + 1) begin
`ifndef DEBUG_DQS  //remove the logic for dqs if needs to be debugged (directed to output instead)  
            if(ODELAY_SUPPORTED) begin 
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b1), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_dqs(
                    .OFB(oserdes_dqs[gen_index]), // 1-bit output: Feedback path for data
                    .OQ(), // 1-bit output: Data path output
                    .TQ(oserdes_dqs_tri_control[gen_index]),
                    .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(1'b1 && (i_controller_toggle_dqs || toggle_dqs_q)), //the last part will still have half dqs series
                    .D2(1'b0 && (i_controller_toggle_dqs || toggle_dqs_q)),
                    .D3(1'b1 && (i_controller_toggle_dqs || toggle_dqs_q) && !i_controller_write_leveling_calib),
                    .D4(1'b0 && (i_controller_toggle_dqs || toggle_dqs_q)),
                    .D5(1'b1 && i_controller_toggle_dqs && !i_controller_write_leveling_calib),
                    .D6(1'b0 && i_controller_toggle_dqs),
                    .D7(1'b1 && i_controller_toggle_dqs && !i_controller_write_leveling_calib),
                    .D8(1'b0 && i_controller_toggle_dqs),
                    .T1(i_controller_dqs_tri_control),
                    .TCE(1'b1),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                     // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0)
                    // 1-bit input: Byte group tristate
                );
                // End of OSERDESE2_inst instantiation
            
            
                // ODELAYE2: Output Fixed or Variable Delay Element
                // 7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
                //Delay the DQ
                ODELAYE2 #(
                    .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                    .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter ("TRUE"), Reduced power ("FALSE")
                    .ODELAY_TYPE("VAR_LOAD"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                    .ODELAY_VALUE(DQS_ODELAY_TAP), // delay to align odelay_dqs to oserdes_dqs due to 600ps insertion delay: (1/800MHz - 600ps)/78.125ps = 8.32 taps
                    .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                    .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
                )
                ODELAYE2_dqs (
                    .CNTVALUEOUT(), // 5-bit output: Counter value output
                    .DATAOUT(odelay_dqs[gen_index]), // 1-bit output: Delayed data/clock output
                    .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                    .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                    .CINVCTRL(1'b0), // 1-bit input: Dynamic clock inversion input
                    .CLKIN(1'b0), // 1-bit input: Clock delay input
                    .CNTVALUEIN(i_controller_odelay_dqs_cntvaluein), // 5-bit input: Counter value input
                    .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                    .LD(i_controller_odelay_dqs_ld[gen_index]), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                                // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                    .LDPIPEEN(1'b0), // 1-bit input: Enables the pipeline register to load data
                    .ODATAIN(oserdes_dqs[gen_index]), // 1-bit input: Output delay data input
                    .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
                );
                
                if(USE_IO_TERMINATION) begin 
                    // IOBUFDS_DCIEN: Differential Bi-directional Buffer with Digital Controlled Impedance (DCI)
                    // and Input path enable/disable
                    // May only be placed in High Performance (HP) Banks
                    // 7 Series
                    // Xilinx HDL Libraries Guide, version 13.4
                    IOBUFDS_DCIEN #(
                        .IBUF_LOW_PWR("FALSE"), // Low Power - "TRUE", High Performance = "FALSE"
                        .SLEW("FAST"), // Specify the output slew rate
                        .USE_IBUFDISABLE("FALSE") // Use IBUFDISABLE function, "TRUE" or "FALSE"
                    ) IOBUFDS_DCIEN_inst (
                        .O(read_dqs[gen_index]),  // Buffer output
                        .IO(io_ddr3_dqs[gen_index]), // Diff_p inout (connect directly to top-level port)
                        .IOB(io_ddr3_dqs_n[gen_index]), // Diff_n inout (connect directly to top-level port)
                        .DCITERMDISABLE(1'b0), // DCI Termination enable input
                        .I(odelay_dqs[gen_index]), // Buffer input
                        .IBUFDISABLE(1'b0), // Input disable input, low=disable
                        .T(oserdes_dqs_tri_control[gen_index]) // 3-state enable input, high=input, low=output
                    );
                    // End of IOBUFDS_DCIEN_inst instantiation

                end
                else begin
                    // IOBUFDS: Differential Bi-directional Buffer
                    //7 Series
                    // Xilinx HDL Libraries Guide, version 13.4
                    IOBUFDS #(
                        //.DIFF_TERM("FALSE"), // Differential Termination ("TRUE"/"FALSE")
                        .IBUF_LOW_PWR("FALSE") // Low Power - "TRUE", High Performance = "FALSE"
                        //.IOSTANDARD("DIFF_SSTL15") // Specify the I/O standard. CONSULT WITH DATASHEET
                        //.SLEW("FAST") // Specify the output slew rate
                    ) IOBUFDS_dqs (
                        .O(read_dqs[gen_index]), // Buffer output
                        .IO(io_ddr3_dqs[gen_index]), // Diff_p inout (connect directly to top-level port)
                        .IOB(io_ddr3_dqs_n[gen_index]), // Diff_n inout (connect directly to top-level port)
                        .I(odelay_dqs[gen_index]), // Buffer input
                        .T(/*!dqs_tri_control[gen_index]*/oserdes_dqs_tri_control[gen_index]) // 3-state enable input, high=input, low=output
                    ); // End of IOBUFDS_inst instantiation
                end
                
            end
            
            else begin //ODELAY not supported
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b1), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_dqs(
                    .OFB(), // 1-bit output: Feedback path for data
                    .OQ(oserdes_dqs[gen_index]), // 1-bit output: Data path output
                    .TQ(oserdes_dqs_tri_control[gen_index]),
                    .CLK(!i_ddr3_clk), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(1'b1 && (i_controller_toggle_dqs || toggle_dqs_q)), //the last part will still have half dqs series
                    .D2(1'b0 && (i_controller_toggle_dqs || toggle_dqs_q)),
                    .D3(1'b1 && (i_controller_toggle_dqs || toggle_dqs_q) && !i_controller_write_leveling_calib),
                    .D4(1'b0 && (i_controller_toggle_dqs || toggle_dqs_q)),
                    .D5(1'b1 && i_controller_toggle_dqs && !i_controller_write_leveling_calib),
                    .D6(1'b0 && i_controller_toggle_dqs),
                    .D7(1'b1 && i_controller_toggle_dqs && !i_controller_write_leveling_calib),
                    .D8(1'b0 && i_controller_toggle_dqs),
                    .T1(i_controller_dqs_tri_control),
                    .TCE(1'b1),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                     // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0)
                    // 1-bit input: Byte group tristate
                );
                // End of OSERDESE2_inst instantiation
                
                // IOBUFDS: Differential Bi-directional Buffer
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                IOBUFDS #(
                    //.DIFF_TERM("FALSE"), // Differential Termination ("TRUE"/"FALSE")
                    .IBUF_LOW_PWR("FALSE") // Low Power - "TRUE", High Performance = "FALSE"
                    //.IOSTANDARD("DIFF_SSTL15") // Specify the I/O standard. CONSULT WITH DATASHEET
                    //.SLEW("FAST") // Specify the output slew rate
                ) IOBUFDS_dqs (
                    .O(read_dqs[gen_index]), // Buffer output
                    .IO(io_ddr3_dqs[gen_index]), // Diff_p inout (connect directly to top-level port)
                    .IOB(io_ddr3_dqs_n[gen_index]), // Diff_n inout (connect directly to top-level port)
                    .I(oserdes_dqs[gen_index]), // Buffer input
                    .T(/*!dqs_tri_control[gen_index]*/oserdes_dqs_tri_control[gen_index]) // 3-state enable input, high=input, low=output
                ); // End of IOBUFDS_inst instantiation
                
            end
            (* mark_debug = "true" *) wire[4:0] IDELAYE2_dqs_CNTVALUEOUT;
            // IDELAYE2: Input Fixed or Variable Delay Element
            // 7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
            IDELAYE2 #(
                .DELAY_SRC("IDATAIN"), // Delay input (IDATAIN, DATAIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), //Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .IDELAY_TYPE("VAR_LOAD"), //FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .IDELAY_VALUE(DQS_IDELAY_TAP), //Input delay tap setting (0-31)
                .PIPE_SEL("FALSE"),  //Select pipelined mode, FALSE, TRUE
                .REFCLK_FREQUENCY(200.0), //IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("CLOCK") //DATA, CLOCK input signal
            )
            IDELAYE2_dqs (
                .CNTVALUEOUT(IDELAYE2_dqs_CNTVALUEOUT), // 5-bit output: Counter value output
                .DATAOUT(idelay_dqs[gen_index]), // 1-bit output: Delayed data output
                .C(i_controller_clk), // 1-bit input: Clock input
                .CE(1'b0), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(1'b0),// 1-bit input: Dynamic clock inversion input
                .CNTVALUEIN(i_controller_idelay_dqs_cntvaluein), // 5-bit input: Counter value input
                .DATAIN(), //1-bit input: Internal delay data input
                .IDATAIN(read_dqs[gen_index]), // 1-bit input: Data input from the I/O
                .INC(1'b0), // 1-bit input: Increment / Decrement tap delay input
                .LD(i_controller_idelay_dqs_ld[gen_index]), // 1-bit input: Load IDELAY_VALUE input
                .LDPIPEEN(1'b0), // 1-bit input: Enable PIPELINE register to load data input
                .REGRST(1'b0) // 1-bit input: Active-high reset tap-delay input
            );
            // End of IDELAYE2_inst instantiation
            
              // End of IOBUF_inst instantiation                 
            // ISERDESE2: Input SERial/DESerializer with bitslip
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            ISERDESE2 #(
                .DATA_RATE("DDR"), // DDR, SDR
                .DATA_WIDTH(serdes_ratio*2), // Parallel data width (2-8,10,14)
                // INIT_Q1 - INIT_Q4: Initial value on the Q outputs (0/1)
                .INIT_Q1(1'b0),
                .INIT_Q2(1'b0),
                .INIT_Q3(1'b0),
                .INIT_Q4(1'b0),
                .INTERFACE_TYPE("NETWORKING"), // MEMORY, MEMORY_DDR3, MEMORY_QDR, NETWORKING, OVERSAMPLE
                .IOBDELAY("IFD"), // NONE, BOTH, IBUF, IFD
                .NUM_CE(1),// Number of clock enables (1,2)
                .OFB_USED("FALSE"), // Select OFB path (FALSE, TRUE)
                // SRVAL_Q1 - SRVAL_Q4: Q output values when SR is used (0/1)
                .SRVAL_Q1(1'b0),
                .SRVAL_Q2(1'b0),
                .SRVAL_Q3(1'b0),
                .SRVAL_Q4(1'b0)
            )
            ISERDESE2_dqs (
                .O(),
                // 1-bit output: Combinatorial output
                // Q1 - Q8: 1-bit (each) output: Registered data outputs
                .Q1(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 7]),
                .Q2(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 6]),
                .Q3(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 5]),
                .Q4(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 4]),   
                .Q5(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 3]),
                .Q6(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 2]), //
                .Q7(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 1]), //3
                .Q8(o_controller_iserdes_dqs[serdes_ratio*2*gen_index + 0]), //2
                // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
                .SHIFTOUT1(),
                .SHIFTOUT2(),
                .BITSLIP(i_controller_bitslip[gen_index]),
                // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
                // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
                // to Q8 output ports will shift, as in a barrel-shifter operation, one
                // position every time Bitslip is invoked (DDR operation is different from
                // SDR).
                // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
                .CE1(1'b1),
                .CE2(1'b1),
                .CLKDIVP(), // 1-bit input: TBD
                // Clocks: 1-bit (each) input: ISERDESE2 clock input ports
                .CLK(i_ddr3_clk), // 1-bit input: High-speed clock
                .CLKB(!i_ddr3_clk), // 1-bit input: High-speed secondary clock
                .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                .OCLK(), // 1-bit input: High speed output clock used when INTERFACE_TYPE="MEMORY"
                // Dynamic Clock Inversions: 1-bit (each) input: Dynamic clock inversion pins to switch clock polarity
                .DYNCLKDIVSEL(), // 1-bit input: Dynamic CLKDIV inversion
                .DYNCLKSEL(), // 1-bit input: Dynamic CLK/CLKB inversion
                // Input Data: 1-bit (each) input: ISERDESE2 data input ports
                .D(), // 1-bit input: Data input
                .DDLY(idelay_dqs[gen_index]), // 1-bit input: Serial data from IDELAYE2
                .OFB(), // 1-bit input: Data feedback from OSERDESE2
                .OCLKB(), // 1-bit input: High speed negative edge output clock
                .RST(sync_rst), // 1-bit input: Active high asynchronous reset
                // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
                .SHIFTIN1(),
                .SHIFTIN2()
            );
            // End of ISERDESE2_inst instantiation
`endif
                      
            //ISERDES train
            // End of IOBUF_inst instantiation                 
            // ISERDESE2: Input SERial/DESerializer with bitslip
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            ISERDESE2 #(
                .DATA_RATE("DDR"), // DDR, SDR
                .DATA_WIDTH(serdes_ratio*2), // Parallel data width (2-8,10,14)
                // INIT_Q1 - INIT_Q4: Initial value on the Q outputs (0/1)
                .INIT_Q1(1'b0),
                .INIT_Q2(1'b0),
                .INIT_Q3(1'b0),
                .INIT_Q4(1'b0),
                .INTERFACE_TYPE("NETWORKING"), // MEMORY, MEMORY_DDR3, MEMORY_QDR, NETWORKING, OVERSAMPLE
                .IOBDELAY("NONE"), // NONE, BOTH, IBUF, IFD
                .NUM_CE(1),// Number of clock enables (1,2)
                .OFB_USED("TRUE"), // Select OFB path (FALSE, TRUE)
                // SRVAL_Q1 - SRVAL_Q4: Q output values when SR is used (0/1)
                .SRVAL_Q1(1'b0),
                .SRVAL_Q2(1'b0),
                .SRVAL_Q3(1'b0),
                .SRVAL_Q4(1'b0)
            )
            ISERDESE2_train (
                .O(),
                // 1-bit output: Combinatorial output
                // Q1 - Q8: 1-bit (each) output: Registered data outputs
                .Q1(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 7]),
                .Q2(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 6]),
                .Q3(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 5]),
                .Q4(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 4]),   
                .Q5(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 3]),
                .Q6(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 2]),
                .Q7(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 1]),
                .Q8(o_controller_iserdes_bitslip_reference[gen_index*serdes_ratio*2 + 0]),
                // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
                .SHIFTOUT1(),
                .SHIFTOUT2(),
                .BITSLIP(i_controller_bitslip[gen_index]),
                // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
                // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
                // to Q8 output ports will shift, as in a barrel-shifter operation, one
                // position every time Bitslip is invoked (DDR operation is different from
                // SDR).
                // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
                .CE1(1'b1),
                .CE2(1'b1),
                .CLKDIVP(), // 1-bit input: TBD
                // Clocks: 1-bit (each) input: ISERDESE2 clock input ports
                .CLK(i_ddr3_clk), // 1-bit input: High-speed clock
                .CLKB(!i_ddr3_clk), // 1-bit input: High-speed secondary clock
                .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                .OCLK(), // 1-bit input: High speed output clock used when INTERFACE_TYPE="MEMORY"
                // Dynamic Clock Inversions: 1-bit (each) input: Dynamic clock inversion pins to switch clock polarity
                .DYNCLKDIVSEL(), // 1-bit input: Dynamic CLKDIV inversion
                .DYNCLKSEL(), // 1-bit input: Dynamic CLK/CLKB inversion
                // Input Data: 1-bit (each) input: ISERDESE2 data input ports
                .D(), // 1-bit input: Data input
                .DDLY(), // 1-bit input: Serial data from IDELAYE2
                .OFB(oserdes_bitslip_reference[gen_index]), // 1-bit input: Data feedback from OSERDESE2
                .OCLKB(), // 1-bit input: High speed negative edge output clock
                .RST(sync_rst), // 1-bit input: Active high asynchronous reset
                // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
                .SHIFTIN1(),
                .SHIFTIN2()
            );
            // End of ISERDESE2_inst instantiation
            
                // OSERDESE2: Output SERial/DESerializer with bitslip
                //7 Series
                // Xilinx HDL Libraries Guide, version 13.4
                OSERDESE2 #(
                    .DATA_RATE_OQ("DDR"), // DDR, SDR
                    .DATA_RATE_TQ("BUF"), // DDR, SDR
                    .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                    .INIT_OQ(1'b1), // Initial value of OQ output (1'b0,1'b1)
                    .TRISTATE_WIDTH(1)
                )
                OSERDESE2_train(
                    .OFB(oserdes_bitslip_reference[gen_index]), // 1-bit output: Feedback path for data
                    .OQ(), // 1-bit output: Data path output
                    .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                    .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                    // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                    .D1(1'b0),
                    .D2(1'b0),
                    .D3(1'b0),
                    .D4(1'b0),
                    .D5(1'b1),
                    .D6(1'b1),
                    .D7(1'b1),
                    .D8(1'b1),
                    .OCE(1'b1), // 1-bit input: Output data clock enable
                    .RST(sync_rst), // 1-bit input: Reset
                     // unused signals but were added here to make vivado happy
                    .SHIFTOUT1(), // SHIFTOUT1 / SHIFTOUT2: 1-bit (each) output: Data output expansion (1-bit each)
                    .SHIFTOUT2(),
                    .TBYTEOUT(), // 1-bit output: Byte group tristate
                    .TFB(), // 1-bit output: 3-state control
                    .TQ(), // 1-bit output: 3-state control
                    // SHIFTIN1 / SHIFTIN2: 1-bit (each) input: Data input expansion (1-bit each)
                    .SHIFTIN1(0),
                    .SHIFTIN2(0),
                    // T1 - T4: 1-bit (each) input: Parallel 3-state inputs
                    .T1(0),
                    .T2(0),
                    .T3(0),
                    .T4(0),
                    .TBYTEIN(0),
                    // 1-bit input: Byte group tristate
                    .TCE(0)
                    // 1-bit input: 3-state clock enable
                );
                // End of OSERDESE2_inst instantiation  
    
    
        end
     endgenerate 
     
     /*
    // OSERDESE2: Output SERial/DESerializer with bitslip
    //7 Series
    // Xilinx HDL Libraries Guide, version 13.4
    OSERDESE2 #(
        .DATA_RATE_OQ("DDR"), // DDR, SDR
        .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
        .INIT_OQ(1'b1) // Initial value of OQ output (1'b0,1'b1)
    )
    OSERDESE2_train(
        .OFB(test_OFB), // 1-bit output: Feedback path for data
        .OQ(), // 1-bit output: Data path output
        .CLK(i_ddr3_clk), // 1-bit input: High speed clock
        .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
        // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
        .D1(1'b0),
        .D2(1'b0),
        .D3(1'b0),
        .D4(1'b0),
        .D5(1'b1),
        .D6(1'b1),
        .D7(1'b1),
        .D8(1'b1),
        .OCE(1'b1), // 1-bit input: Output data clock enable
        .RST(sync_rst) // 1-bit input: Reset
    );
    // End of OSERDESE2_inst instantiation  
     */
     /*
    // OSERDESE2: Output SERial/DESerializer with bitslip
    //7 Series
    // Xilinx HDL Libraries Guide, version 13.4
    OSERDESE2 #(
        .DATA_RATE_OQ("DDR"), // DDR, SDR
        .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
        .INIT_OQ(1'b1) // Initial value of OQ output (1'b0,1'b1)
    )
    OSERDESE2_dqs(
        .OFB(oserdes_dqs), // 1-bit output: Feedback path for data
        .OQ(), // 1-bit output: Data path output
        .CLK(i_ddr3_clk), // 1-bit input: High speed clock
        .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
        // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
        .D1(1'b1 && i_controller_toggle_dqs),
        .D2(1'b0 && i_controller_toggle_dqs),
        .D3(1'b1 && i_controller_toggle_dqs),
        .D4(1'b0 && i_controller_toggle_dqs),
        .D5(1'b1 && i_controller_toggle_dqs),
        .D6(1'b0 && i_controller_toggle_dqs),
        .D7(1'b1 && i_controller_toggle_dqs),
        .D8(1'b0 && i_controller_toggle_dqs),
        .OCE(1'b1), // 1-bit input: Output data clock enable
        .RST(sync_rst) // 1-bit input: Reset
    );
    // End of OSERDESE2_inst instantiation
    */
    // IDELAYCTRL: IDELAYE2/ODELAYE2 Tap Delay Value Control
    // 7 Series
    // Xilinx HDL Libraries Guide, version 13.4
    (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
    IDELAYCTRL IDELAYCTRL_inst (
        .RDY(idelayctrl_rdy), // 1-bit output: Ready output
        .REFCLK(i_ref_clk), // 1-bit input: Reference clock input.The frequency of REFCLK must be 200 MHz to guarantee the tap-delay value specified in the applicable data sheet.
        .RST(sync_rst) // 1-bit input: Active high reset input, To ,Minimum Reset pulse width is 52ns
    );
    // End of IDELAYCTRL_inst instantiation


    // DCIRESET: Digitially Controlled Impedence Reset Component
    //7 Series
    // Xilinx HDL Libraries Guide, version 13.4
    DCIRESET DCIRESET_inst (
        .LOCKED(dci_locked), // 1-bit output: LOCK status output (When low, DCI I/O impedance is being calibrated and DCI I/Os are unavailable)
        .RST(sync_rst) // 1-bit input: Active-high asynchronous reset input
    );
    // End of DCIRESET_inst instantiation
         
    endmodule
