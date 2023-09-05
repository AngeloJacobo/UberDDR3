// Background:
// This DDR3 controller will be used with a DDR3-1600 with Kintex 7 FPGA Board (XC7K160T-3FFG676E). 
// The goal will be to:
//  - Run this at 1600Mbps (Maximum Physical Interface (PHY) Rate for a 4:1 
//          memory controller based on "DC and AC Switching Characteristics" for Kintex 7)
//  - Parameterize everything
//  - Interface should be (nearly) bus agnostic   
//  - High (sustained) data throughput. Sequential writes should be able to continue without interruption 


//`define FORMAL_COVER //change delay in reset sequence to fit in cover statement
//`define COVER_DELAY 1 //fixed delay used in formal cover for reset sequence
`default_nettype none
`timescale 1ps / 1ps


// THESE DEFINES WILL BE MODIFIED AS PARAMETERS LATER ON
`define DDR3_1600_11_11_11 // DDR3-1600 (11-11-11) speed bin
`define RAM_8Gb //DDR3 Capacity
//`define RAM_2Gb 
//`define RAM_4Gb 
//`define RAM_8Gb
`define x8 //DDR3 organization (DQ bus width) 
//`define x4
//`define x16

//NOTE IN FORMAL INDUCTION: Make formal induction finish in shorter time by lowering the delays between commands. 
//A good basis on the formal depth is the value of PRE_STALL_DELAY.
//The value of prestall delay is the longest possible
//clock cycles needed to finish 2 requests. Since the
//fifo used in the formal induction has 2 locations
//only (pertains to the request stored on the two
// pipeline stages of bank access), we need to flush
// those two requests on the fifo first, and the max
// time for two request is also the value of
// PRE_STALL_DELAY
                   
module ddr3_controller #(
    parameter real CONTROLLER_CLK_PERIOD = 10, //ns, period of clock input to this DDR3 controller module
                   DDR3_CLK_PERIOD = 2.5, //ns, period of clock input to DDR3 RAM device 
    parameter      ROW_BITS = 14,   //width of row address
                   COL_BITS = 10, //width of column address
                   BA_BITS = 3, //width of bank address
                   DQ_BITS = 8,  //width of DQ
                   LANES = 8, //8 lanes of DQ
                   AUX_WIDTH = 16, 
                   WB2_ADDR_BITS = 7,
                   WB2_DATA_BITS = 32,
    /* verilator lint_off UNUSEDPARAM */
    parameter[0:0] OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
                   OPT_BUS_ABORT = 1,  //1 = can abort bus, 0 = no abort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
   /* verilator lint_on UNUSEDPARAM */
                   MICRON_SIM = 0, //simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
                   ODELAY_SUPPORTED = 1, //set to 1 when ODELAYE2 is supported
    parameter // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
                serdes_ratio = $rtoi(CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD),
                wb_data_bits = DQ_BITS*LANES*serdes_ratio*2,
                wb_addr_bits = ROW_BITS + COL_BITS + BA_BITS - $clog2(serdes_ratio*2),
                wb_sel_bits = wb_data_bits / 8,
                wb2_sel_bits = WB2_DATA_BITS / 8,
                //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
                cmd_len = 4 + 3 + BA_BITS + ROW_BITS,
                lanes_clog2 = $clog2(LANES) == 0? 1: $clog2(LANES)
    ) 
    (
        input wire i_controller_clk, //i_controller_clk has period of CONTROLLER_CLK_PERIOD 
        (* mark_debug = "true" *) input wire i_rst_n, //200MHz input clock
        // Wishbone inputs
        input wire i_wb_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb_stb, //request a transfer
        input wire i_wb_we, //write-enable (1 = write, 0 = read)
        input wire[wb_addr_bits - 1:0] i_wb_addr, //burst-addressable {row,bank,col} 
        input wire[wb_data_bits - 1:0] i_wb_data, //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        input wire[wb_sel_bits - 1:0] i_wb_sel, //byte strobe for write (1 = write the byte)
        input wire[AUX_WIDTH - 1:0]  i_aux, //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        output reg o_wb_stall, //1 = busy, cannot accept requests
        output wire o_wb_ack, //1 = read/write request has completed
        output wire[wb_data_bits - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output wire[AUX_WIDTH - 1:0] o_aux, //for AXI-interface compatibility (returned upon ack)
        //
        // Wishbone 2 (PHY) inputs
        input wire i_wb2_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        (* mark_debug = "true" *) input wire i_wb2_stb, //request a transfer
        input wire i_wb2_we, //write-enable (1 = write, 0 = read)
        input wire[WB2_ADDR_BITS - 1:0] i_wb2_addr, //memory-mapped register to be accessed 
        input wire[wb2_sel_bits - 1:0] i_wb2_sel, //byte strobe for write (1 = write the byte)
        input wire[WB2_DATA_BITS - 1:0] i_wb2_data, //write data
        // Wishbone 2 (Controller) outputs
        output reg o_wb2_stall, //1 = busy, cannot accept requests
        (* mark_debug = "true" *) output reg o_wb2_ack, //1 = read/write request has completed
        output reg[WB2_DATA_BITS - 1:0] o_wb2_data, //read data
        //
        // PHY interface
        (* mark_debug = "true" *) input wire[DQ_BITS*LANES*8 - 1:0] i_phy_iserdes_data,
        (* mark_debug = "true" *)  input wire[LANES*serdes_ratio*2 - 1:0] i_phy_iserdes_dqs,
        input wire[LANES*serdes_ratio*2 - 1:0] i_phy_iserdes_bitslip_reference,
        (* mark_debug = "true" *) input wire i_phy_idelayctrl_rdy,
        output wire[cmd_len*serdes_ratio-1:0] o_phy_cmd,
        (* mark_debug = "true" *) output wire o_phy_dqs_tri_control, o_phy_dq_tri_control,
        output wire o_phy_toggle_dqs,
        (* mark_debug = "true" *) output wire[wb_data_bits-1:0] o_phy_data,
        output wire[wb_sel_bits-1:0] o_phy_dm, 
        output wire[4:0] o_phy_odelay_data_cntvaluein, o_phy_odelay_dqs_cntvaluein,
        (* mark_debug = "true" *) output wire[4:0] o_phy_idelay_data_cntvaluein, o_phy_idelay_dqs_cntvaluein,
        output reg[LANES-1:0] o_phy_odelay_data_ld, o_phy_odelay_dqs_ld,
        output reg[LANES-1:0] o_phy_idelay_data_ld, 
        (* mark_debug = "true" *) output reg[LANES-1:0] o_phy_idelay_dqs_ld,
        output reg[LANES-1:0] o_phy_bitslip,
        output reg o_phy_write_leveling_calib,
        // Debug port
        output	wire	[31:0]	o_debug1,
        output	wire	[31:0]	o_debug2,
        output	wire	[31:0]	o_debug3
    );

    
    /************************************************************* Command Parameters *************************************************************/
    //DDR3 commands {cs_n, ras_n, cas_n, we_n} (JEDEC DDR3 doc pg. 33 )
    localparam[3:0]CMD_MRS = 4'b0000, // Mode Register Set
                      CMD_REF = 4'b0001, // Refresh
                      CMD_PRE = 4'b0010, // Precharge (A10-AP: 0 = Single Bank Precharge, 1 = Precharge All Banks)
                      CMD_ACT = 4'b0011, // Bank Activate
                      CMD_WR  = 4'b0100, // Write (A10-AP: 0 = no Auto-Precharge) (A12-BC#: 1 = Burst Length 8) 
                      CMD_RD  = 4'b0101, //Read  (A10-AP: 0 = no Auto-Precharge) (A12-BC#: 1 = Burst Length 8) 
                      CMD_NOP = 4'b0111, // No Operation
                      CMD_ZQC = 4'b0110; // ZQ Calibration (A10-AP: 0 = ZQ Calibration Short, 1 = ZQ Calibration Long)

    localparam RST_DONE = 27, // Command bit that determines if reset seqeunce had aready finished. non-persistent (only needs to be toggled once), 
                  REF_IDLE = 27, // No refresh is about to start and no ongoing refresh. (same bit as RST_DONE)
                  USE_TIMER = 26, // Command bit that determines if timer will be used (if delay is zero, USE_TIMER must be LOW)
                  A10_CONTROL = 25, //Command bit that determines if A10 AutoPrecharge will be high
                  CLOCK_EN = 24, //Clock-enable to DDR3
                  RESET_N = 23, //Reset_n to DDR3
                  DDR3_CMD_START = 22, //Start of DDR3 command slot
                  DDR3_CMD_END = 19, //end of DDR3 command slot
                  MRS_BANK_START = 18; //start of bank value in MRS value
                     
    // ddr3 command partitioning
    /* verilator lint_off UNUSEDPARAM */
    localparam CMD_CS_N = cmd_len - 1,
               CMD_RAS_N = cmd_len - 2,
               CMD_CAS_N= cmd_len - 3,
               CMD_WE_N = cmd_len - 4,
               CMD_ODT = cmd_len - 5,
               CMD_CKE = cmd_len - 6, 
               CMD_RESET_N = cmd_len - 7,
               CMD_BANK_START = BA_BITS + ROW_BITS - 1,
               CMD_ADDRESS_START = ROW_BITS - 1;
    /* verilator lint_on UNUSEDPARAM */          
    localparam READ_SLOT = get_slot(CMD_RD),
                WRITE_SLOT = get_slot(CMD_WR),
                ACTIVATE_SLOT = get_slot(CMD_ACT),
                PRECHARGE_SLOT = get_slot(CMD_PRE);
                
    // Data does not have to be delayed (DQS is the on that has to be
    // delayed and center-aligned to the center eye of data)
    localparam DATA_INITIAL_ODELAY_TAP = 0; 

    //DQS needs to be edge-aligned to the center eye of the data. 
    //This means DQS needs to be delayed by a quarter of the ddr3
    //clk period relative to the data. Subtract by 600ps to include
    //the IODELAY insertion delay. Divide by a delay resolution of 
    //78.125ps per tap to get the needed tap value. Then add the tap
    //value used in data to have the delay relative to the data.
    localparam DQS_INITIAL_ODELAY_TAP = $rtoi(((DDR3_CLK_PERIOD*1000/4))/78.125 + DATA_INITIAL_ODELAY_TAP);
    
    //Incoming DQS should be 90 degree delayed relative to incoming data
    localparam DATA_INITIAL_IDELAY_TAP = 0; //600ps delay
    localparam DQS_INITIAL_IDELAY_TAP = $rtoi(((DDR3_CLK_PERIOD*1000/4))/78.125 + DATA_INITIAL_IDELAY_TAP);
    /*********************************************************************************************************************************************/


    /********************************************************** Timing Parameters ***********************************************************************************/
    localparam DELAY_SLOT_WIDTH = 19; //Bitwidth of the delay slot and mode register slot on the reset/refresh rom will be at the same size as the Mode Register
    localparam POWER_ON_RESET_HIGH      =     200_000; // 200us reset must be active at initialization
    localparam INITIAL_CKE_LOW      =       500_000; // 500us cke must be low before activating
    `ifdef DDR3_1600_11_11_11 //DDR3-1600 (11-11-11) speed bin
        localparam tRCD     =       13.750; // ns Active to Read/Write command time
        localparam tRP      =      13.750; // ns Precharge command period
        localparam tRAS     =      35; // ns ACT to PRE command period
    `endif

    `ifdef RAM_1Gb
        localparam tRFC         =           110.0;      // ns Refresh command  to ACT or REF 
    `elsif RAM_2Gb
        localparam tRFC         =           160.0;      // ns Refresh command  to ACT or REF 
    `elsif RAM_4Gb
        localparam tRFC         =           300.0;      // ns Refresh command  to ACT or REF 
    `else
        localparam tRFC             =       350.0;      // ns Refresh command  to ACT or REF 
    `endif
    localparam tREFI = 7800; //ns Average periodic refresh interval
    localparam tXPR = max(5*DDR3_CLK_PERIOD, tRFC+10); // ns Exit Reset from CKE HIGH to a valid command
    localparam tWR = 15.0; // ns Write Recovery Time
    localparam tWTR = max(nCK_to_ns(4), 7.5); //ns Delay from start of internal write transaction to internal read command
    localparam[DELAY_SLOT_WIDTH - 1:0] tWLMRD = nCK_to_cycles(40); // nCK First DQS/DQS# rising edge after write leveling mode is programmed
    localparam tWLO = 7.5; //ns Write leveling output delay
    localparam tWLOE = 2;
    localparam tRTP = max(nCK_to_ns(4), 7.5); //ns Internal Command to PRECHARGE Command delay
    localparam tCCD = 4; //nCK CAS to CAS command delay
    /* verilator lint_off WIDTHEXPAND */
    localparam tMOD = max_int(nCK_to_cycles(12), ns_to_cycles(15)); //cycles (controller)  Mode Register Set command update delay
    localparam tZQinit = max_int(nCK_to_cycles(512), ns_to_cycles(640));//cycles (controller)  Power-up and RESET calibration time
    /* verilator lint_on WIDTHEXPAND */
    localparam CL_nCK = 6; //create a function for this
    localparam CWL_nCK = 5; //create a function for this
    localparam DELAY_MAX_VALUE = ns_to_cycles(INITIAL_CKE_LOW); //Largest possible delay needed by the reset and refresh sequence
    localparam DELAY_COUNTER_WIDTH= $clog2(DELAY_MAX_VALUE); //Bitwidth needed by the maximum possible delay, this will be the delay counter width
    localparam CALIBRATION_DELAY = 2;
                                    
    /*********************************************************************************************************************************************/
    

    /********************************************************** Computed Delay Parameters **********************************************************/
    localparam[3:0] PRECHARGE_TO_ACTIVATE_DELAY =  find_delay(ns_to_nCK(tRP), PRECHARGE_SLOT, ACTIVATE_SLOT); //3
    localparam[3:0] ACTIVATE_TO_PRECHARGE_DELAY = find_delay(ns_to_nCK(tRAS), ACTIVATE_SLOT, PRECHARGE_SLOT);
    localparam[3:0] ACTIVATE_TO_WRITE_DELAY = find_delay(ns_to_nCK(tRCD), ACTIVATE_SLOT, WRITE_SLOT); //3
    localparam[3:0] ACTIVATE_TO_READ_DELAY = find_delay(ns_to_nCK(tRCD), ACTIVATE_SLOT, READ_SLOT); //2
    localparam[3:0] READ_TO_WRITE_DELAY = find_delay((CL_nCK + tCCD + 2 - CWL_nCK), READ_SLOT, WRITE_SLOT); //2
    localparam[3:0] READ_TO_READ_DELAY = 0;
    localparam[3:0] READ_TO_PRECHARGE_DELAY =  find_delay(ns_to_nCK(tRTP), READ_SLOT, PRECHARGE_SLOT);  //1
    localparam[3:0] WRITE_TO_WRITE_DELAY = 0;
    localparam[3:0] WRITE_TO_READ_DELAY = find_delay((CWL_nCK + 4 + ns_to_nCK(tWTR)), WRITE_SLOT, READ_SLOT); //4
    localparam[3:0] WRITE_TO_PRECHARGE_DELAY = find_delay((CWL_nCK + 4 + ns_to_nCK(tWR)), WRITE_SLOT, PRECHARGE_SLOT); //5
    localparam PRE_REFRESH_DELAY = WRITE_TO_PRECHARGE_DELAY + 1; 
    `ifdef FORMAL 
        (*keep*) wire[3:0] f_PRECHARGE_TO_ACTIVATE_DELAY, f_ACTIVATE_TO_PRECHARGE_DELAY, f_ACTIVATE_TO_WRITE_DELAY, f_ACTIVATE_TO_READ_DELAY,
                    f_READ_TO_WRITE_DELAY, f_READ_TO_READ_DELAY, f_READ_TO_PRECHARGE_DELAY, f_WRITE_TO_WRITE_DELAY, 
                    f_WRITE_TO_READ_DELAY, f_WRITE_TO_PRECHARGE_DELAY; 
        assign f_PRECHARGE_TO_ACTIVATE_DELAY = PRECHARGE_TO_ACTIVATE_DELAY;
        assign f_ACTIVATE_TO_PRECHARGE_DELAY = ACTIVATE_TO_PRECHARGE_DELAY;                
        assign f_ACTIVATE_TO_WRITE_DELAY = ACTIVATE_TO_WRITE_DELAY;
        assign f_ACTIVATE_TO_READ_DELAY = ACTIVATE_TO_READ_DELAY;
        assign f_READ_TO_WRITE_DELAY = READ_TO_WRITE_DELAY;
        assign f_READ_TO_READ_DELAY = READ_TO_READ_DELAY;
        assign f_READ_TO_PRECHARGE_DELAY =  READ_TO_PRECHARGE_DELAY;
        assign f_WRITE_TO_WRITE_DELAY = WRITE_TO_WRITE_DELAY;
        assign f_WRITE_TO_READ_DELAY = WRITE_TO_READ_DELAY;
        assign f_WRITE_TO_PRECHARGE_DELAY = WRITE_TO_PRECHARGE_DELAY;
    `endif

    //MARGIN_BEFORE_ANTICIPATE is the number of columns before the column
    //end when the anticipate can start
    //the worst case scenario is when the anticipated bank needs to be precharged
    //thus the margin must satisfy tRP (for precharge) and tRCD (for activate). 
    //Also, worscase is when the anticipated bank still has the leftover of the 
    //WRITE_TO_PRECHARGE_DELAY thus consider also this.
    localparam MARGIN_BEFORE_ANTICIPATE = PRECHARGE_TO_ACTIVATE_DELAY + ACTIVATE_TO_WRITE_DELAY + WRITE_TO_PRECHARGE_DELAY;
    localparam STAGE2_DATA_DEPTH = (CWL_nCK - (3 - WRITE_SLOT + 1))/4 + 1; //this is always >= 1 (5 - (3 - 3 + 1))/4.0 -> floor(1) + 1 = floor(4
    `ifdef FORMAL
        wire stage2_data_depth;
        assign stage2_data_depth = STAGE2_DATA_DEPTH;
        always @* begin
            assert(STAGE2_DATA_DEPTH-2 >= 0);
        end
    `endif
    localparam READ_DELAY = $rtoi($floor((CL_nCK - (3 - READ_SLOT + 1))/4.0 ));
    localparam READ_ACK_PIPE_WIDTH = READ_DELAY + 1 + 2 + 1 + 1;
    localparam MAX_ADDED_READ_ACK_DELAY = 16;
    localparam DELAY_BEFORE_WRITE_LEVEL_FEEDBACK = STAGE2_DATA_DEPTH + ns_to_cycles(tWLO+tWLOE) + 10;  //plus 10 controller clocks for possible bus latency and 
                                                                                                      //the delay for receiving feedback DQ from IOBUF -> IDELAY -> ISERDES
    /*********************************************************************************************************************************************/
   
    
    /********************************************************** Read/Write Calibration Parameters **********************************************************/
    localparam IDLE = 0,
                BITSLIP_DQS_TRAIN_1 = 1,
                MPR_READ = 2,
                COLLECT_DQS = 3,
                ANALYZE_DQS = 4,
                CALIBRATE_DQS = 5,
                BITSLIP_DQS_TRAIN_2 = 6,
                START_WRITE_LEVEL = 7,
                WAIT_FOR_FEEDBACK = 8,
                ISSUE_WRITE_1 = 9, 
                ISSUE_WRITE_2 = 10,
                ISSUE_READ = 11,
                READ_DATA = 12,
                ANALYZE_DATA = 13, 
                CHECK_STARTING_DATA = 14,
                BITSLIP_DQS_TRAIN_3 = 15,
                DONE_CALIBRATE = 16;
                
     localparam STORED_DQS_SIZE = 5, //must be >= 2           
                REPEAT_DQS_ANALYZE = 1,
                REPEAT_CLK_SAMPLING = 20; // repeat DQS read to find the accurate starting position of DQS

    /*********************************************************************************************************************************************/


    /************************************************************* Set Mode Registers Parameters *************************************************************/
    // MR2 (JEDEC DDR3 doc pg. 30)
    localparam[2:0] PASR = 3'b000; //Partial Array Self-Refresh: Full Array
    localparam[2:0] CWL = 3'b000; //CAS write Latency: 8 (1.5 ns > tCK(avg) >= 1.25 ns) CREATE A FUNCTION FOR THIS
    localparam[0:0] ASR = 1'b1; //Auto Self-Refresh: on
    localparam[0:0] SRT = 1'b0; //Self-Refresh Temperature Range:0 (If ASR = 1, SRT bit must be set to 0)
    localparam[1:0] RTT_WR = 2'b00; //Dynamic ODT: off
    localparam[2:0] MR2_SEL = 3'b010; //Selected Mode Register
    localparam[18:0] MR2 = {MR2_SEL, 5'b00000, RTT_WR, 1'b0, SRT, ASR, CWL, PASR}; 

    // MR3 (JEDEC DDR3 doc pg. 32)
    localparam[1:0] MPR_LOC = 2'b00; //Data location for MPR Reads: Predefined Pattern 0_1_0_1_0_1_0_1
    localparam[0:0] MPR_EN = 1'b1; //MPR Enable: Enable MPR reads and calibration during initialization
    localparam[0:0] MPR_DIS = 1'b0; //MPR Enable: Enable MPR reads and calibration during initialization
    localparam[2:0] MR3_SEL = 3'b011; //MPR Selected
    localparam[18:0] MR3_MPR_EN = {MR3_SEL, 13'b0_0000_0000_0000, MPR_EN, MPR_LOC}; 
    localparam[18:0] MR3_MPR_DIS = {MR3_SEL, 13'b0_0000_0000_0000, MPR_DIS, MPR_LOC}; 
    
    // MR1 (JEDEC DDR3 doc pg. 27)
    localparam DLL_EN = 1'b0; //DLL Enable/Disable: Enabled(0)
    localparam[1:0] DIC = 2'b00; //Output Driver Impedance Control (IS THIS THE SAME WITH RTT_NOM???????????? Search later)
    localparam[2:0] RTT_NOM = 3'b011; //RTT Nominal: 40ohms (RQZ/6) is the impedance of the PCB trace
    localparam[0:0] WL_EN = 1'b1; //Write Leveling Enable: Disabled
    localparam[0:0] WL_DIS = 1'b0; //Write Leveling Enable: Disabled
    localparam[1:0] AL = 2'b00; //Additive Latency: Disabled
    localparam[0:0] TDQS = 1'b1; //Termination Data Strobe: Disabled (provides additional termination resistance outputs. 
                                 //When the TDQS function is disabled, the DM function is provided (vice-versa).TDQS function is only 
                                 //available for X8 DRAM and must be disabled for X4 and X16. 
    localparam[0:0]  QOFF = 1'b0; //Output Buffer Control: Enabled
    localparam[2:0] MR1_SEL = 3'b001; //Selected Mode Register
    localparam[18:0] MR1_WL_EN = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, WL_EN, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};
    localparam[18:0] MR1_WL_DIS = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, WL_DIS, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};

    //MR0 (JEDEC DDR3 doc pg. 24)
    localparam[1:0] BL = 2'b00; //Burst Length: 8 (Fixed)
    localparam[3:0] CL = 4'b0100; //CAS Read Latency: 10, can support DDR-1600 speedbin 8-8-8, 9-9-9, and 10-10-10 (Check JEDEC DDR doc pg. 162) CREATE A FUNCTION FOR THIS
    localparam[0:0] RBT = 1'b0; //Read Burst Type: Nibble Sequential
    localparam[0:0] DLL_RST = 1'b1; //DLL Reset: Yes (this is self-clearing and must be applied after DLL enable)
    localparam[2:0] WR = WRA_mode_register_value($rtoi($ceil(tWR/DDR3_CLK_PERIOD))); //Write recovery for autoprecharge (
    localparam[0:0] PPD = 1'b0; //DLL Control for Precharge PD: Slow exit (DLL off)
    localparam[2:0] MR0_SEL = 3'b000;
    localparam[18:0] MR0 = {MR0_SEL, 3'b000, PPD, WR, DLL_RST, 1'b0, CL[3:1], RBT, CL[0], BL};
    /*********************************************************************************************************************************************/
    localparam INITIAL_RESET_INSTRUCTION = {5'b01000 , CMD_NOP , { {(DELAY_SLOT_WIDTH-3){1'b0}} , 3'd5} }; 

    /************************************************************* Registers and Wires *************************************************************/
    integer index;
    (* mark_debug = "true" *)  reg[4:0] instruction_address = 0; //address for accessing rom instruction
    reg[27:0] instruction = INITIAL_RESET_INSTRUCTION; //instruction retrieved from reset instruction rom
    reg[ DELAY_COUNTER_WIDTH - 1:0] delay_counter = INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]; //counter used for delays
    reg delay_counter_is_zero = (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0); //counter is now zero so retrieve next delay
    reg reset_done = 0; //high if reset has already finished
    reg pause_counter = 0;
    wire issue_read_command;
    wire issue_write_command;
    reg stage2_update = 1;
    reg stage2_stall = 0;
    reg stage1_stall = 0;
    reg[(1<<BA_BITS)-1:0] bank_status_q, bank_status_d; //bank_status[bank_number]: determine current state of bank (1=active , 0=idle)
    //bank_active_row[bank_number] = stores the active row address in the specified bank
    reg[ROW_BITS-1:0] bank_active_row_q[(1<<BA_BITS)-1:0], bank_active_row_d[(1<<BA_BITS)-1:0]; 

    //pipeline stage 1 regs
    reg stage1_pending = 0;
    reg[AUX_WIDTH-1:0] stage1_aux = 0;
    reg stage1_we = 0;
    reg[wb_data_bits - 1:0] stage1_data = 0;
    reg[wb_sel_bits - 1:0] stage1_dm = 0;
    reg[COL_BITS-1:0] stage1_col = 0;
    reg[BA_BITS-1:0] stage1_bank = 0;
    reg[ROW_BITS-1:0] stage1_row = 0;
    reg[BA_BITS-1:0] stage1_next_bank = 0;
    reg[ROW_BITS-1:0] stage1_next_row = 0;
    wire[wb_addr_bits-1:0] wb_addr_plus_anticipate;
    
    //pipeline stage 2 regs
    reg stage2_pending = 0;
    reg[AUX_WIDTH-1:0] stage2_aux = 0;
    reg stage2_we = 0;
    reg[wb_sel_bits - 1:0] stage2_dm_unaligned = 0, stage2_dm_unaligned_temp = 0;
    reg[wb_sel_bits - 1:0] stage2_dm[STAGE2_DATA_DEPTH-1:0];
    reg[wb_data_bits - 1:0] stage2_data_unaligned = 0, stage2_data_unaligned_temp = 0;
    reg[wb_data_bits - 1:0] stage2_data[STAGE2_DATA_DEPTH-1:0];
    reg [DQ_BITS*8 - 1:0] unaligned_data[LANES-1:0];
    reg [8 - 1:0] unaligned_dm[LANES-1:0];
    reg[COL_BITS-1:0] stage2_col = 0;
    reg[BA_BITS-1:0] stage2_bank = 0;
    reg[ROW_BITS-1:0] stage2_row = 0;
    
    //delay counter for every banks
    reg[3:0] delay_before_precharge_counter_q[(1<<BA_BITS)-1:0], delay_before_precharge_counter_d[(1<<BA_BITS)-1:0]; //delay counters
    reg[3:0] delay_before_activate_counter_q[(1<<BA_BITS)-1:0], delay_before_activate_counter_d[(1<<BA_BITS)-1:0] ;
    reg[3:0] delay_before_write_counter_q[(1<<BA_BITS)-1:0], delay_before_write_counter_d[(1<<BA_BITS)-1:0] ;
    reg[3:0] delay_before_read_counter_q[(1<<BA_BITS)-1:0] , delay_before_read_counter_d[(1<<BA_BITS)-1:0] ;
    
    //commands to be sent to PHY (4 slots per controller clk cycle)
    reg[cmd_len-1:0] cmd_d[3:0];
    initial begin
        o_phy_bitslip = 0;
    end
    reg cmd_odt_q = 0, cmd_odt, cmd_ck_en, cmd_reset_n;  
    reg o_wb_stall_q = 1, o_wb_stall_d;
    reg precharge_slot_busy;
    reg activate_slot_busy;
    reg[1:0] write_dqs_q;
    reg write_dqs_d;
    reg[STAGE2_DATA_DEPTH:0] write_dqs;
    reg[STAGE2_DATA_DEPTH:0] write_dqs_val;
    reg write_dq_q, write_dq_d;
    reg[STAGE2_DATA_DEPTH+1:0] write_dq;  
    
    (* mark_debug = "true" *) reg[$clog2(DONE_CALIBRATE):0] state_calibrate;
    reg[STORED_DQS_SIZE*8-1:0] dqs_store = 0;
    reg[$clog2(STORED_DQS_SIZE):0] dqs_count_repeat = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_start_index = 0;
    (* mark_debug ="true" *) reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_start_index_stored = 0;
    (* mark_debug ="true" *) reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index = 0;
    (* mark_debug ="true" *) reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index_orig = 0;
    (* mark_debug ="true" *) reg[$clog2(STORED_DQS_SIZE*8)-1:0] dq_target_index[LANES-1:0];
    (* mark_debug ="true" *) wire[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index_value;
    reg[$clog2(REPEAT_DQS_ANALYZE):0] dqs_start_index_repeat=0;
    reg[1:0] train_delay;
    (* mark_debug = "true" *) reg[3:0] delay_before_read_data = 0;
    reg[$clog2(DELAY_BEFORE_WRITE_LEVEL_FEEDBACK):0] delay_before_write_level_feedback = 0;
    reg initial_dqs = 0;
    (* mark_debug = "true" *) reg[lanes_clog2-1:0] lane = 0;
    reg[$clog2(8*LANES)-1:0] lane_times_8 = 0;
    /* verilator lint_off UNUSEDSIGNAL */
    reg[15:0] dqs_bitslip_arrangement = 0;
    /* verilator lint_off UNUSEDSIGNAL */
    (* mark_debug = "true" *) reg[3:0] added_read_pipe_max = 0;
    (* mark_debug = "true" *) reg[3:0] added_read_pipe[LANES - 1:0];
    
    //contains the ack shift reg for both read and write
    reg[AUX_WIDTH:0] shift_reg_read_pipe_q[READ_ACK_PIPE_WIDTH-1:0]; 
    reg[AUX_WIDTH:0] shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH-1:0]; //1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
    reg index_read_pipe; //tells which delay_read_pipe will be updated 
    reg index_wb_data; //tells which o_wb_data_q will be sent to o_wb_data
    reg[15:0] delay_read_pipe[1:0]; //delay when each lane will retrieve i_phy_iserdes_data
    reg[wb_data_bits - 1:0] o_wb_data_q[1:0]; //store data retrieved from i_phy_iserdes_data to be sent to o_wb_data
    reg[AUX_WIDTH:0] o_wb_ack_read_q[MAX_ADDED_READ_ACK_DELAY-1:0];
 
    reg write_calib_stb = 0;
    reg[AUX_WIDTH-1:0] write_calib_aux = 0;
    reg write_calib_we = 0;
    reg[COL_BITS-1:0] write_calib_col = 0;
    reg[wb_data_bits-1:0] write_calib_data = 0;
    reg write_calib_odt = 0;
    reg write_calib_dqs = 0;
    reg write_calib_dq = 0;
    reg prev_write_level_feedback = 1;
    reg[wb_data_bits-1:0] read_data_store = 0;
    reg[127:0] write_pattern = 0;
    (* mark_debug = "true" *) reg[$clog2(64):0] data_start_index[LANES-1:0];       
    reg[4:0] odelay_data_cntvaluein[LANES-1:0]; 
    reg[4:0] odelay_dqs_cntvaluein[LANES-1:0];
    reg[4:0] idelay_data_cntvaluein[LANES-1:0];
    reg[4:0] idelay_data_cntvaluein_prev;
    reg[4:0] idelay_dqs_cntvaluein[LANES-1:0];
    reg[$clog2(REPEAT_CLK_SAMPLING):0] sample_clk_repeat = 0;
    reg stored_write_level_feedback = 0;
    reg[5:0] start_index_check = 0;
    reg[63:0] read_lane_data = 0;
    reg odelay_cntvalue_repeated = 0;
    // Wishbone 2
    reg wb2_stb = 0;
    reg wb2_update = 0;
    reg wb2_we = 0;
    reg[WB2_ADDR_BITS-1:0] wb2_addr = 0;
    reg[WB2_DATA_BITS-1:0] wb2_data = 0;
    reg[wb2_sel_bits-1:0] wb2_sel = 0;
    reg[4:0] wb2_phy_odelay_data_cntvaluein;
    reg[4:0] wb2_phy_odelay_dqs_cntvaluein;
    reg[4:0] wb2_phy_idelay_data_cntvaluein;
    reg[4:0] wb2_phy_idelay_dqs_cntvaluein;
    reg[LANES-1:0] wb2_phy_odelay_data_ld;
    reg[LANES-1:0] wb2_phy_odelay_dqs_ld;
    reg[LANES-1:0] wb2_phy_idelay_data_ld;
    reg[LANES-1:0] wb2_phy_idelay_dqs_ld;
    reg[LANES-1:0] write_level_fail = 0;
    reg[lanes_clog2-1:0] wb2_write_lane;
    reg sync_rst = 0;
    
    // initial block for all regs
    initial begin
        for(index=0; index < (1<<BA_BITS); index=index+1) begin
            bank_status_q[index] = 0;  
            bank_status_d[index] = 0;
            bank_active_row_q[index] = 0; 
            bank_active_row_d[index] = 0; 
        end

        for(index = 0; index < STAGE2_DATA_DEPTH; index = index+1) begin
            stage2_data[index] =  0;               
            stage2_dm[index] = 0;
        end

        for(index=0; index <(1<<BA_BITS); index=index+1) begin
            delay_before_precharge_counter_q[index] = 0;  
            delay_before_activate_counter_q[index] = 0;
            delay_before_write_counter_q[index] = 0; 
            delay_before_read_counter_q[index] = 0; 
        end

        for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
            shift_reg_read_pipe_q[index] = 0;
            shift_reg_read_pipe_d[index] = 0;
        end

        //set all commands to all 1's makig CS_n high (thus commands are initially NOP)
        for(index=0; index < 4; index=index+1) begin
            cmd_d[index] = -1;
        end

        for(index = 0; index < LANES; index = index + 1) begin
            odelay_data_cntvaluein[index] = DATA_INITIAL_ODELAY_TAP[4:0];
            odelay_dqs_cntvaluein[index] = DQS_INITIAL_ODELAY_TAP[4:0];
            idelay_data_cntvaluein[index] = DATA_INITIAL_IDELAY_TAP[4:0];
            idelay_dqs_cntvaluein[index] = DQS_INITIAL_IDELAY_TAP[4:0];
            dq_target_index[index] = 0;
        end
    end
    /*********************************************************************************************************************************************/

    
    /******************************************* Reset Sequence (JEDEC DDR3 doc pg. 19) *******************************************/
    // This reset and refresh sequence logic is designed for simplicity. This uses a Read-Only Memory (ROM)) 
    // to store the commands and time delay. A constant function is used store instructions instead of registers
    // to ensure that ROM wil not change values during formal verification induction. 
    // This idea is sourced from https://zipcpu.com/formal/2019/11/18/genuctrlr.html
    // Instruction format:
        // RST_DONE/REF_IDLE = 27; //RST_DONE =  non-persistent, only needs to be toggled once, command bit that determines if reset seqeunce had aready finished
                                                                //REF_IDLE = No refresh is about to start and no ongoing refresh.
        // USE_TIMER = 26; // Command bit that determines if timer will be used (if delay is zero, USE_TIMER must be LOW)
        // A10_CONTROL = 25, //Command bit that determines if A10 Precharge All Bank will be high
        // CLOCK_EN = 24; //Clock-enable to DDR3
        // RESET_N = 23; //Reset_n to DDR3
        // DDR3_CMD = 22:19 
        // Timer-Delay or MRS = 18:0 //timer delay and MRS shares same slot, thus MRS commands cannot have delays
        
        // NOTE: The timer delay is a delay in clock cycles AFTER EXECUTING COMMAND, not the ACTUAL CYCLES of the command 
        // (delay of 1 means 2 clock cycles of command execution) //initial reset instruction has low rst_n, low cke, and has delay of 5
    function [27:0] read_rom_instruction(input[4:0] func_instruction_address); begin
        case(func_instruction_address) 
    
            5'd0: 
             if (MICRON_SIM)
                read_rom_instruction = {5'b01000 , CMD_NOP , ns_to_cycles(POWER_ON_RESET_HIGH/1000)}; 
             else
                read_rom_instruction = {5'b01000 , CMD_NOP , ns_to_cycles(POWER_ON_RESET_HIGH)}; 
                //0. RESET# needs to be maintained low for minimum 200us with power-up initialization. CKE is pulled
                    //“Low” anytime before RESET# being de-asserted (min. time 10 ns). .

            5'd1: 
             if (MICRON_SIM)
                 read_rom_instruction =  {5'b01001 , CMD_NOP, ns_to_cycles(INITIAL_CKE_LOW/1000)}; 
             else
                 read_rom_instruction =  {5'b01001 , CMD_NOP, ns_to_cycles(INITIAL_CKE_LOW)}; 
                //1. After RESET# is de-asserted, wait for another 500 us until CKE becomes active. During this time, the
                    //DRAM will start internal state initialization; this will be done independently of external clocks. 
                    // .... Also, a NOP or Deselect command must be registered (with tIS set up time to clock) before
                    //CKE goes active.

            5'd2: read_rom_instruction = {5'b01011 , CMD_NOP, ns_to_cycles(tXPR)}; 
            //2. After CKE is being registered high, wait minimum of Reset CKE Exit time, tXPR.
            
            5'd3: read_rom_instruction = {{2'b00,MR2[10], 2'b11}, CMD_MRS, MR2}; 
            //3. Issue MRS command to load MR2. 
            
            5'd4: read_rom_instruction = {{2'b00,MR3_MPR_DIS[10], 2'b11}, CMD_MRS, MR3_MPR_DIS}; 
            //4. All banks must first be in the idle state (all banks precharged and tRP met) before doing MPR calibration, thus issue first disabled MR3
            
            5'd5: read_rom_instruction = {{2'b00,MR1_WL_DIS[10], 2'b11}, CMD_MRS, MR1_WL_DIS}; 
            //5. Issue MRS command to load MR1, enable DLL,and disable WL. 
            
            5'd6: read_rom_instruction = {{2'b00,MR0[10], 2'b11}, CMD_MRS, MR0}; 
            //6. Issue MRS command to load MR0 and reset DLL.
            
            5'd7: read_rom_instruction = {5'b01011, CMD_NOP, tMOD[DELAY_SLOT_WIDTH-1:0]};
            //7. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
           
            5'd8: read_rom_instruction = {5'b01111, CMD_ZQC, tZQinit[DELAY_SLOT_WIDTH-1:0]}; 
            //8. ZQ Calibration command is used to calibrate DRAM Ron & ODT values. ZQCL command triggers the calibration engine 
            //inside the DRAM and, once calibration is achieved, the calibrated values area transferred from the calibration engine to 
            //DRAM IO, which gets reflected as updated output driver
            
             // Precharge all banks before enabling MPR
            5'd9: read_rom_instruction = {5'b01111, CMD_PRE, ns_to_cycles(tRP)}; 
            //9. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            5'd10: read_rom_instruction = {{2'b00,MR3_MPR_EN[10], 2'b11}, CMD_MRS, MR3_MPR_EN}; 
            //10. Issue MRS command to load MR3. Prior to enabling the MPR for read calibration, all banks must be in the idle state (all banks 
            // precharged and tRP met). Once the MPR is enabled, any subsequent RD or RDA commands will be redirected to the MultiPurpose Register. 
            
            5'd11: read_rom_instruction = {5'b01011, CMD_NOP, tMOD[DELAY_SLOT_WIDTH-1:0]};
            //11. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            5'd12: read_rom_instruction = {5'b01011, CMD_NOP, CALIBRATION_DELAY[DELAY_SLOT_WIDTH-1:0]}; 
            //12. Delay for read calibration
            
            5'd13: read_rom_instruction = {{2'b00,MR3_MPR_DIS[10], 2'b11}, CMD_MRS, MR3_MPR_DIS}; 
            //13. Disable MPR after read calibration
            
            5'd14: read_rom_instruction = {{2'b00,MR1_WL_EN[10], 2'b11}, CMD_MRS, MR1_WL_EN}; 
            //14. Issue MRS command to load MR1, and enable WL. 
            
            5'd15: read_rom_instruction = {5'b01011, CMD_NOP, tWLMRD[DELAY_SLOT_WIDTH-1:0]};
            //15. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            5'd16: read_rom_instruction = {5'b01011, CMD_NOP, CALIBRATION_DELAY[DELAY_SLOT_WIDTH-1:0]}; 
            //16. Delay for write calibration
            
            5'd17: read_rom_instruction = {{2'b00,MR1_WL_DIS[10], 2'b11}, CMD_MRS, MR1_WL_DIS}; 
            //17. Issue MRS command to load MR1, and disable WL. 
            
            5'd18: read_rom_instruction = {5'b01011, CMD_NOP, tMOD[DELAY_SLOT_WIDTH-1:0]};
            //18. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            // Perform first refresh and any subsequent refresh (so instruction 12 to 15 will be re-used for the refresh sequence)
            5'd19: read_rom_instruction = {5'b01111, CMD_PRE, ns_to_cycles(tRP)}; 
            //19. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            5'd20: read_rom_instruction = {5'b01011, CMD_REF, ns_to_cycles(tRFC)};
            //20. A delay between the Refresh Command and the next valid command, except NOP or DES, must be greater than or equal to the minimum 
            //Refresh cycle time tRFC(min) 
            
            5'd21: read_rom_instruction = {5'b11011, CMD_NOP, ns_to_cycles(tREFI)};
            //21. Reset ends now. The refresh interval also starts to count.
            
            5'd22: read_rom_instruction = {5'b01011, CMD_NOP, PRE_REFRESH_DELAY[DELAY_SLOT_WIDTH-1:0]}; 
            // 22. Extra delay needed before starting the refresh sequence. 
                // (this already sets the wishbone stall high to make sure no user request is on-going when refresh seqeunce starts)
            
            default: read_rom_instruction = {5'b00011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b0}}}; 
        endcase
    end
    endfunction
    /*********************************************************************************************************************************************/
    

    /******************************************* Reset Sequence ROM Controller *******************************************/
    always @(posedge i_controller_clk) begin
        sync_rst <= !i_rst_n;
    end
    always @(posedge i_controller_clk) begin
        if(sync_rst) begin
            instruction_address <= 0;
            `ifdef FORMAL_COVER
                instruction_address <= 21;
            `endif
            instruction <= INITIAL_RESET_INSTRUCTION;
            delay_counter <= INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0];
            delay_counter_is_zero <= (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0);
            reset_done <= 1'b0;
        end
        else begin 
            //update counter after reaching zero
            if(delay_counter_is_zero) begin 
                delay_counter <= instruction[DELAY_COUNTER_WIDTH - 1:0]; //retrieve delay value of current instruction, we count to zero thus minus 1
            end
            
            //else: decrement delay counter when current instruction needs delay
            //don't decrement (has infinite time) when last bit of
            //delay_counter is 1 (for r/w calibration and prestall delay)
            //address will only move forward for these kinds of delay only
            //when skip_reset_seq_delay is toggled
            else if(instruction[USE_TIMER] /*&& delay_counter != {(DELAY_COUNTER_WIDTH){1'b1}}*/ && !pause_counter) delay_counter <= delay_counter - 1; 
            
            //delay_counter of 1 means we will need to update the delay_counter next clock cycle (delay_counter of zero) so we need to retrieve 
            //now the next instruction. The same thing needs to be done when current instruction does not need the timer delay.
            if(delay_counter == 1 || !instruction[USE_TIMER]/* || skip_reset_seq_delay*/) begin
                delay_counter_is_zero <= 1; 
                instruction <= read_rom_instruction(instruction_address);
                instruction_address <= (instruction_address == 5'd22)? 5'd19:instruction_address+1; //wrap back of address to repeat refresh sequence 
            end
            //we are now on the middle of a delay 
            else delay_counter_is_zero <=0; 
            //instruction[RST_DONE] is non-persistent thus we need to register it once it goes high
            reset_done <= instruction[RST_DONE]? 1'b1:reset_done; 
        end
    end
    /*********************************************************************************************************************************************/


    /******************************************************* Track Bank Status and Issue Command *******************************************************/
    //process request transaction 
    always @(posedge i_controller_clk) begin
        if(sync_rst) begin
            o_wb_stall <= 1'b1; 
            o_wb_stall_q <= 1'b1;
            //set stage 1 to 0
            stage1_pending <= 0;
            stage1_aux <= 0;
            stage1_we <= 0;
            stage1_dm <= 0;
            stage1_col <= 0;
            stage1_bank <= 0;
            stage1_row <= 0;
            stage1_next_bank <= 0;
            stage1_next_row <= 0;
            stage1_data <= 0;
            //set stage2 to 0
            stage2_pending <= 0;
            stage2_aux <= 0;
            stage2_we <= 0;
            stage2_col <= 0;
            stage2_bank <= 0;
            stage2_row <= 0;
            cmd_odt_q <= 0;
            stage2_data_unaligned <= 0;
            stage2_data_unaligned_temp <= 0;
            stage2_dm_unaligned <= 0;
            stage2_dm_unaligned_temp <= 0;
            for(index=0; index<LANES; index=index+1) begin
                unaligned_data[index] <= 0;
                unaligned_dm[index] <= 0;
            end
            //set delay counters to 0
            for(index=0; index<(1<<BA_BITS); index=index+1) begin
                delay_before_precharge_counter_q[index] <= 0;  
                delay_before_activate_counter_q[index] <= 0;
                delay_before_write_counter_q[index] <= 0; 
                delay_before_read_counter_q[index] <= 0; 
            end
            //reset bank status and active row
            for( index=0; index < (1<<BA_BITS); index=index+1) begin
                    bank_status_q[index] <= 0;  
                    bank_active_row_q[index] <= 0; 
            end
             //reset data
            for(index = 0; index < STAGE2_DATA_DEPTH; index = index+1) begin
                stage2_data[index] <=  0;               
                stage2_dm[index] <= 0;
            end
        end
        
        // can only start accepting requests  when reset is done
        else if(reset_done) begin 
            o_wb_stall <= o_wb_stall_d || state_calibrate != DONE_CALIBRATE;
            o_wb_stall_q <= o_wb_stall_d; //working even at calibration stage
            //o_wb_stall <= stage2_stall || state_calibrate != DONE_CALIBRATE;
            cmd_odt_q <= cmd_odt;

            //update delay counter 
            for(index=0; index< (1<<BA_BITS); index=index+1) begin
                delay_before_precharge_counter_q[index] <= delay_before_precharge_counter_d[index];  
                delay_before_activate_counter_q[index] <= delay_before_activate_counter_d[index];
                delay_before_write_counter_q[index] <= delay_before_write_counter_d[index]; 
                delay_before_read_counter_q[index] <= delay_before_read_counter_d[index]; 
            end

            //update bank status and active row
            for(index=0; index < (1<<BA_BITS); index=index+1) begin
                bank_status_q[index] <= bank_status_d[index];
                bank_active_row_q[index] <= bank_active_row_d[index];
            end

            if(instruction_address == 20) begin ///current instruction at precharge
                cmd_odt_q <= 1'b0;
                //all banks will be in idle after refresh
                for( index=0; index < (1<<BA_BITS); index=index+1) begin
                    bank_status_q[index] <= 0;  
                end
            end
            
            //refresh sequence is on-going
            if(!instruction[REF_IDLE]) begin
                //no transaction will be pending during refresh
                o_wb_stall <= 1'b1; 
            end
            
            //if pipeline is not stalled (or a request is left on the prestall
            //delay address 19 or if in calib), move pipeline to stage 2
            if(!o_wb_stall_q && stage2_update) begin //ITS POSSIBLE ONLY NEXT CLK WILL STALL SUPPOSE TO GO LOW
                stage1_pending <= 1'b0; //no request initially unless overridden by the actual stb request
                stage2_pending <= stage1_pending;
                stage2_aux <= stage1_aux;
                stage2_we <= stage1_we;
                stage2_col <= stage1_col;
                stage2_bank <= stage1_bank;
                stage2_row <= stage1_row;
                if(ODELAY_SUPPORTED) begin
                    stage2_data_unaligned <= stage1_data;
                    stage2_dm_unaligned <= ~stage1_dm; //inverse each bit (1 must mean "masked" or not written)
                end
                else begin
                    stage2_data_unaligned_temp <= stage1_data;
                    stage2_dm_unaligned_temp <= ~stage1_dm; //inverse each bit (1 must mean "masked" or not written)
                end
                //stage2_data -> shiftreg(CWL) -> OSERDES(DDR) -> ODELAY -> RAM
            end
            if(!ODELAY_SUPPORTED) begin
                stage2_data_unaligned <= stage2_data_unaligned_temp; //delayed by 1 clock cycle 
                stage2_dm_unaligned <= stage2_dm_unaligned_temp;  //delayed by 1 clock cycle 
            end

            // when not in refresh, transaction can only be processed when i_wb_cyc is high and not stall
            if(i_wb_cyc && !o_wb_stall) begin 
                //stage1 will not do the request (pending low) when the
                //request is on the same bank as the current request. This
                //will ensure stage1 bank will be different from stage2 bank
                stage1_pending <= i_wb_stb;//actual request flag
                stage1_aux <= i_aux; //aux ID for AXI compatibility
                stage1_we <= i_wb_we; //write-enable
                stage1_dm <= i_wb_sel; //byte selection
                stage1_col <= { i_wb_addr[(COL_BITS- $clog2(serdes_ratio*2)-1):0], {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                stage1_bank <=  i_wb_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2))]; //bank_address
                stage1_row <= i_wb_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) ]; //row_address
                //stage1_next_bank will not increment unless stage1_next_col
                //overwraps due to MARGIN_BEFORE_ANTICIPATE. Thus, anticipated
                //precharge and activate will happen only at the end of the
                //current column with a margin dictated by
                //MARGIN_BEFORE_ANTICIPATE  
                /* verilator lint_off WIDTH */
                {stage1_next_row , stage1_next_bank} <= wb_addr_plus_anticipate >> (COL_BITS- $clog2(serdes_ratio*2));
                //anticipated next row and bank to be accessed 
                /* verilator lint_on WIDTH */
                stage1_data <= i_wb_data;
            end
            else if(state_calibrate != DONE_CALIBRATE) begin
                stage1_pending <= write_calib_stb;//actual request flag
                stage1_we <= write_calib_we; //write-enable
                stage1_dm <= {wb_sel_bits{1'b1}};
                stage1_aux <= write_calib_aux; //aux ID for AXI compatibility
                stage1_col <= write_calib_col; //column address (n-burst word-aligned)
                stage1_bank <=  0; //bank_address
                stage1_row <= 0; //row_address
                {stage1_next_row , stage1_next_bank} <= 0; //anticipated next row and bank to be accessed 
                stage1_data <= write_calib_data;
            end
            
            for(index = 0; index < LANES; index = index + 1) begin
                /* verilator lint_off WIDTH */
                {unaligned_data[index], { 
                stage2_data[0][((DQ_BITS*LANES)*7 + 8*index) +: 8], stage2_data[0][((DQ_BITS*LANES)*6 + 8*index) +: 8], 
                stage2_data[0][((DQ_BITS*LANES)*5 + 8*index) +: 8], stage2_data[0][((DQ_BITS*LANES)*4 + 8*index) +: 8], 
                stage2_data[0][((DQ_BITS*LANES)*3 + 8*index) +: 8], stage2_data[0][((DQ_BITS*LANES)*2 + 8*index) +: 8], 
                stage2_data[0][((DQ_BITS*LANES)*1 + 8*index) +: 8], stage2_data[0][((DQ_BITS*LANES)*0 + 8*index) +: 8] }} 
                <= ( {  stage2_data_unaligned[((DQ_BITS*LANES)*7 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*6 + 8*index) +: 8],
                        stage2_data_unaligned[((DQ_BITS*LANES)*5 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*4 + 8*index) +: 8], 
                        stage2_data_unaligned[((DQ_BITS*LANES)*3 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*2 + 8*index) +: 8],
                        stage2_data_unaligned[((DQ_BITS*LANES)*1 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*0 + 8*index) +: 8] }
                        << data_start_index[index]) | unaligned_data[index];

                {unaligned_dm[index], {
                stage2_dm[0][LANES*7 + index], stage2_dm[0][LANES*6 + index], 
                stage2_dm[0][LANES*5 + index], stage2_dm[0][LANES*4 + index], 
                stage2_dm[0][LANES*3 + index], stage2_dm[0][LANES*2 + index],
                stage2_dm[0][LANES*1 + index], stage2_dm[0][LANES*0 + index] }} 
                <= ( {  stage2_dm_unaligned[LANES*7 + index], stage2_dm_unaligned[LANES*6 + index],
                        stage2_dm_unaligned[LANES*5 + index], stage2_dm_unaligned[LANES*4 + index], 
                        stage2_dm_unaligned[LANES*3 + index], stage2_dm_unaligned[LANES*2 + index],
                        stage2_dm_unaligned[LANES*1 + index], stage2_dm_unaligned[LANES*0 + index] }
                        << (data_start_index[index]>>3)) | unaligned_dm[index];
                /* verilator lint_on WIDTH */
            end
            for(index = 0; index < STAGE2_DATA_DEPTH-1; index = index+1) begin
                stage2_data[index+1] <=  stage2_data[index];              
                stage2_dm[index+1] <= stage2_dm[index];
            end

            //abort any outgoing ack when cyc is low
            if(!i_wb_cyc && state_calibrate == DONE_CALIBRATE) begin
                stage2_pending <= 0;
                stage1_pending <= 0;
            end
        end
    end
    assign o_phy_data = stage2_data[STAGE2_DATA_DEPTH-1];             
    assign o_phy_dm = stage2_dm[STAGE2_DATA_DEPTH-1];
    /* verilator lint_off WIDTH */
    assign wb_addr_plus_anticipate = i_wb_addr + MARGIN_BEFORE_ANTICIPATE;
    /* verilator lint_on WIDTH */
    // DIAGRAM FOR ALL RELEVANT TIMING PARAMETERS:
    //
    //                          tRTP
    //  -------------------------------------------------------------
    //  |                                                 tCCD      |
    //  |                                  -----> Read ---------> Read
    //  v                                  |       ^                |
    // Precharge ------> Activate -------->|       | tWTR           | tRTW
    //  ^          tRP               tRCD  |       |                v
    //  |                                  ------> Write -------> Write
    //  |                                                 tCCD      |
    //  -------------------------------------------------------------
    //                          tWR (after data burst)
    //note: all delays after write counts only after the data burst (except for write-to-write tCCD)
    //
    //Pipeline Stages:
    //  wishbone inputs --> stage1 --> stage2 --> cmd
    always @* begin
        cmd_odt = cmd_odt_q || write_calib_odt;
        cmd_ck_en = instruction[CLOCK_EN];
        cmd_reset_n = instruction[RESET_N];
        stage1_stall = 1'b0;
        stage2_stall = 1'b0;
        stage2_update = 1'b1; //always update stage 2 UNLESS it has a pending request (stage2_pending high)
        o_wb_stall_d = 1'b0; //wb_stall going high is determined on stage 1 (higher priority), wb_stall going low is determined at stage2 (lower priority)
        precharge_slot_busy = 0; //flag that determines if stage 2 is issuing precharge (thus stage 1 cannot issue precharge)
        activate_slot_busy = 0; //flag that determines if stage 2 is issuing activate (thus stage 1 cannot issue activate)
        write_dqs_d = write_calib_dqs;
        write_dq_d = write_calib_dq;
        for(index=0; index < (1<<BA_BITS); index=index+1) begin
            bank_status_d[index] = bank_status_q[index];
            bank_active_row_d[index] = bank_active_row_q[index];
        end
        //set cmd_0 to reset instruction, the remainings are NOP
        //delay_counter_is_zero signifies start of new reset instruction (the time when the command must be issued)
        cmd_d[PRECHARGE_SLOT] = {(!delay_counter_is_zero), instruction[DDR3_CMD_START-1:DDR3_CMD_END], cmd_odt, instruction[CLOCK_EN], instruction[RESET_N], 
                        instruction[MRS_BANK_START:(MRS_BANK_START-BA_BITS+1)], instruction[ROW_BITS-1:0]};
        cmd_d[PRECHARGE_SLOT][10] = instruction[A10_CONTROL];
        cmd_d[READ_SLOT] = {(!issue_read_command), CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}};  
        cmd_d[WRITE_SLOT] = {(!issue_write_command),CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}}; 
        cmd_d[ACTIVATE_SLOT] = {1'b1,CMD_ACT[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}}; 
            
        // decrement delay counters for every bank
        for(index=0; index< (1<<BA_BITS); index=index+1) begin
            delay_before_precharge_counter_d[index] = (delay_before_precharge_counter_q[index] == 0)? 0: delay_before_precharge_counter_q[index] - 1;
            delay_before_activate_counter_d[index] = (delay_before_activate_counter_q[index] == 0)? 0: delay_before_activate_counter_q[index] - 1;
            delay_before_write_counter_d[index] = (delay_before_write_counter_q[index] == 0)? 0:delay_before_write_counter_q[index] - 1;
            delay_before_read_counter_d[index] = (delay_before_read_counter_q[index] == 0)? 0:delay_before_read_counter_q[index] - 1;
        end
        for(index = 1; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
            shift_reg_read_pipe_d[index-1] = shift_reg_read_pipe_q[index];
        end
        shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH-1] = 0;


        //USE _d in ALL
        //if there is a pending request, issue the appropriate commands
        if(stage2_pending) begin 
            stage2_stall = 1; //initially high when stage 2 is pending 
            stage2_update = 0;

            //right row is already active so go straight to read/write
            if(bank_status_q[stage2_bank] &&  bank_active_row_q[stage2_bank] == stage2_row) begin //read/write operation
                //write request
                if(stage2_we && delay_before_write_counter_q[stage2_bank] == 0) begin       
                    stage2_stall = 0;
                    stage2_update = 1;
                    cmd_odt = 1'b1;
                    shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH-1] = {stage2_aux, 1'b1}; 

                    //write acknowledge will use the same logic pipeline as the read acknowledge. 
                    //This would mean write ack latency will be the same for
                    //read ack latency. If it takes 8 clocks for read ack, write
                    //ack latency will be the same. This simplifies the logic
                    //for write ack as there will be no need to analyze the
                    //contents of the shift_reg_read_pipe just to determine
                    //where best to place the write ack on the pipeline (since
                    //the order of ack must be maintaned). But this would mean
                    //the latency for write is fixed regardless if there is an 
                    //outstanding read ack or none on the pipeline 
                    
                    //set-up delay before precharge, read, and write
                    if(delay_before_precharge_counter_q[stage2_bank] <= WRITE_TO_PRECHARGE_DELAY) begin
                        //it is possible that the delay_before_precharge is
                        //set to tRAS (activate to precharge delay). And if we
                        //overwrite delay_before_precharge, we might overwrite
                        //the delay to a lower value which will violate the
                        //tRAS requirement. Thus, we must first check if the
                        //delay_before_precharge is set to a value not more
                        //than the WRITE_TO_PRECHARGE_DELAY
                        delay_before_precharge_counter_d[stage2_bank] = WRITE_TO_PRECHARGE_DELAY;
                    end
                    for(index=0; index < (1<<BA_BITS); index=index+1) begin //the write to read delay applies to all banks (odt must be turned off properly before reading)
                        delay_before_read_counter_d[index] = WRITE_TO_READ_DELAY;
                    end
                    delay_before_read_counter_d[stage2_bank] = WRITE_TO_READ_DELAY;     
                    delay_before_write_counter_d[stage2_bank] = WRITE_TO_WRITE_DELAY;
                    //issue read command
                    if(COL_BITS <= 10) begin
                        cmd_d[WRITE_SLOT] = {1'b0, CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank,{{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_col[9:0]};  
                    end
                    else begin
                        cmd_d[WRITE_SLOT] = {1'b0, CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank,{{ROW_BITS-32'd12}{1'b0}} , 
                            stage2_col[(COL_BITS <= 10) ? 0 : 10] , 1'b0 , stage2_col[9:0]};  
                    end
                    //turn on odt at same time as write cmd
                    cmd_d[0][CMD_ODT] = cmd_odt;
                    cmd_d[1][CMD_ODT] = cmd_odt;
                    cmd_d[2][CMD_ODT] = cmd_odt;
                    cmd_d[3][CMD_ODT] = cmd_odt;
                    write_dqs_d=1;
                    write_dq_d=1;
                   // write_data = 1;
                end
                
                //read request
                else if(!stage2_we && delay_before_read_counter_q[stage2_bank]==0) begin     
                    stage2_stall = 0;
                    stage2_update = 1;
                    cmd_odt = 1'b0;
                    //set-up delay before precharge, read, and write
                    if(delay_before_precharge_counter_q[stage2_bank] <= READ_TO_PRECHARGE_DELAY) begin
                        delay_before_precharge_counter_d[stage2_bank] = READ_TO_PRECHARGE_DELAY;
                    end
                    delay_before_read_counter_d[stage2_bank] = READ_TO_READ_DELAY;     
                    delay_before_write_counter_d[stage2_bank] = READ_TO_WRITE_DELAY;
                    shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH-1] = {stage2_aux, 1'b1}; 

                    //issue read command
                    if(COL_BITS <= 10) begin
                        cmd_d[READ_SLOT] = {1'b0, CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_col[9:0]};  
                    end
                    else begin
                        cmd_d[READ_SLOT] =  {1'b0, CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, {{ROW_BITS-32'd12}{1'b0}} , 
                            stage2_col[(COL_BITS <= 10) ? 0 : 10] , 1'b0 , stage2_col[9:0]};  
                    end
                    //turn off odt at same time as read cmd
                    cmd_d[0][CMD_ODT] = cmd_odt;
                    cmd_d[1][CMD_ODT] = cmd_odt;
                    cmd_d[2][CMD_ODT] = cmd_odt;
                    cmd_d[3][CMD_ODT] = cmd_odt;
                end
            end
            
            //bank is idle so activate it
            else if(!bank_status_q[stage2_bank] && delay_before_activate_counter_q[stage2_bank] == 0) begin 
                activate_slot_busy = 1'b1;
                delay_before_precharge_counter_d[stage2_bank] = ACTIVATE_TO_PRECHARGE_DELAY;
                //set-up delay before read and write
                if(delay_before_read_counter_q[stage2_bank] <= ACTIVATE_TO_READ_DELAY) begin
                    delay_before_read_counter_d[stage2_bank] = ACTIVATE_TO_READ_DELAY;
                end
                delay_before_write_counter_d[stage2_bank] = ACTIVATE_TO_WRITE_DELAY;
                //issue activate command
                cmd_d[ACTIVATE_SLOT] = {1'b0, CMD_ACT[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank , stage2_row};
                //update bank status and active row
                bank_status_d[stage2_bank] = 1'b1;
                bank_active_row_d[stage2_bank] = stage2_row;
            end
            //bank is not idle but wrong row is activated so do precharge
            else if(bank_status_q[stage2_bank] &&  bank_active_row_q[stage2_bank] != stage2_row &&  delay_before_precharge_counter_q[stage2_bank] ==0) begin       
                precharge_slot_busy = 1'b1;
                //set-up delay before activate
                delay_before_activate_counter_d[stage2_bank] = PRECHARGE_TO_ACTIVATE_DELAY;
                //issue precharge command
                cmd_d[PRECHARGE_SLOT] = {1'b0, CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, { {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_row[9:0] } };
                //update bank status and active row
                bank_status_d[stage2_bank] = 1'b0; 
            end
        end //end of stage 2 pending

        //pending request on stage 1
        if(stage1_pending && !((stage1_next_bank == stage2_bank) && stage2_pending)) begin
            //stage 1 will mainly be for anticipation, but it can also handle
            //precharge and activate request. This will depend if the request
            //is on the end of the row and must start the anticipation. For
            //example, we have 10 rows in a bank:
            //[R][R][R][R][R][R][R][A][A][A]
            //
            //R = Request, A = Anticipate
            //Unless we are near the third to the last column, stage 1 will
            //issue Activate and Precharge on the CURRENT bank. Else, stage
            //1 will issue Activate and Precharge for the NEXT bank
            if(bank_status_q[stage1_next_bank] &&  bank_active_row_q[stage1_next_bank] != stage1_next_row && delay_before_precharge_counter_q[stage1_next_bank] ==0 && !precharge_slot_busy) begin    
                //set-up delay before read and write
                 delay_before_activate_counter_d[stage1_next_bank] = PRECHARGE_TO_ACTIVATE_DELAY;
                cmd_d[PRECHARGE_SLOT] = {1'b0, CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank, { {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage1_next_row[9:0] } };
                bank_status_d[stage1_next_bank] = 1'b0; 
            end //end of anticipate precharge
            
            //anticipated bank is idle so do activate
            else if(!bank_status_q[stage1_next_bank] && delay_before_activate_counter_q[stage1_next_bank] == 0 && !activate_slot_busy) begin 
                delay_before_precharge_counter_d[stage1_next_bank] = ACTIVATE_TO_PRECHARGE_DELAY;
                //set-up delay before read and write
                if(delay_before_read_counter_d[stage1_next_bank] <= ACTIVATE_TO_READ_DELAY) begin
                    delay_before_read_counter_d[stage1_next_bank] = ACTIVATE_TO_READ_DELAY;
                end
                delay_before_write_counter_d[stage1_next_bank] = ACTIVATE_TO_WRITE_DELAY;
                cmd_d[ACTIVATE_SLOT] = {1'b0, CMD_ACT[2:0] , cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank , stage1_next_row};
                bank_status_d[stage1_next_bank] = 1'b1;
                bank_active_row_d[stage1_next_bank] = stage1_next_row;
            end //end of anticipate activate
            
        end //end of stage1 anticipate

        // control stage 1 stall
        if(stage1_pending) begin //raise stall only if stage2 will still be busy next clock
            // Stage1 bank and row will determine if transaction will be
            // stalled (bank is idle OR wrong row is active). 
            if(!bank_status_d[stage1_bank] || (bank_status_d[stage1_bank] && bank_active_row_d[stage1_bank] != stage1_row)) begin 
                stage1_stall = 1;
            end
            else if(!stage1_we && delay_before_read_counter_d[stage1_bank] != 0) begin
                stage1_stall = 1;
            end
            else if(stage1_we && delay_before_write_counter_d[stage1_bank] != 0) begin
                stage1_stall = 1;
            end
            //different request type will need a delay of more than 1 clk cycle so stall the pipeline 
            //if(stage1_we != stage2_we) begin
            //    stage1_stall = 1;
            //end
        end

        //control stage 2 stall
        if(stage2_pending) begin
            //control stage2 stall in advance
            if(bank_status_d[stage2_bank] &&  bank_active_row_d[stage2_bank] == stage2_row) begin //read/write operation
                //write request
                if(stage2_we && delay_before_write_counter_d[stage2_bank] == 0) begin //if counter is 1 now, then next clock it will be zero thus lower stall at next cycle too      
                    stage2_stall = 0; //to low stall next stage, but not yet at this stage
                end
                //read request
                else if(!stage2_we && delay_before_read_counter_d[stage2_bank]==0) begin //if counter is 1 now, then next clock it will be zero thus lower stall at next cycle too      
                    stage2_stall = 0;
                end
            end
        end

        // control logic for stall
        if(o_wb_stall_q) o_wb_stall_d = stage2_stall;
        else if(!i_wb_stb) o_wb_stall_d = 0;
        else if(!stage1_pending) o_wb_stall_d = stage2_stall;
        else o_wb_stall_d = stage1_stall;
        
        if(!i_wb_cyc) o_wb_stall_d = 0;

    // Vivado Benchmarking
    // LUT = 1254, FF = 2878
    // WNS = 0.924 ns (200MHz clk)
    end //end of always block
    assign o_phy_cmd = {cmd_d[3], cmd_d[2], cmd_d[1], cmd_d[0]};
    /*********************************************************************************************************************************************/


    /******************************************************* Align Read Data from ISERDES *******************************************************/
    always @(posedge i_controller_clk) begin
        if(sync_rst) begin
            index_read_pipe <= 0;
            index_wb_data <= 0;
            write_dqs_val <= 0;
            write_dqs_q <= 0;
            write_dqs <= 0;
            write_dq_q <= 0;
            write_dq <= 0;
            for(index = 0; index < 2; index = index + 1) begin
                delay_read_pipe[index] <= 0;
            end
            for(index = 0; index < 2; index = index + 1) begin
                o_wb_data_q[index] <= 0;
            end
            for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                shift_reg_read_pipe_q[index] <= 0;
            end
            for(index = 0; index < MAX_ADDED_READ_ACK_DELAY ; index = index + 1) begin
                o_wb_ack_read_q[index] <= 0;
            end
        end
        else begin
            if(ODELAY_SUPPORTED) begin
                write_dqs_val[0] <= write_dqs_d || write_dqs_q[0];
            end
            else begin 
                write_dqs_val[0] <= write_dqs_d || write_dqs_q[0] || write_dqs_q[1];
            end
            write_dqs_q[0] <= write_dqs_d;
            write_dqs_q[1] <= write_dqs_q[0];
            write_dqs[0] <= write_dqs_d || write_dqs_q[0] || write_dqs_q[1]; //high for 3 clk cycles
            
            write_dq_q <= write_dq_d;
            write_dq[0] <= write_dq_d || write_dq_q; //high for 2 clk cycles
            for(index = 0; index < STAGE2_DATA_DEPTH; index = index+1) begin //increase by 1 to accomodate postamble            
                write_dqs[index+1] <= write_dqs[index]; 
                write_dqs_val[index+1] <= write_dqs_val[index];
            end 
            for(index = 0; index < STAGE2_DATA_DEPTH+1; index = index+1) begin //increase by 1 to accomodate postamble            
                write_dq[index+1] <= write_dq[index]; 
            end 
            for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                shift_reg_read_pipe_q[index] <= shift_reg_read_pipe_d[index];
            end

            for(index = 0; index < 2; index = index + 1) begin
                delay_read_pipe[index] <= (delay_read_pipe[index] >> 1);
            end
            if(shift_reg_read_pipe_q[1][0]) begin //delay is over and data is now starting to release from iserdes BUT NOT YET ALIGNED
                index_read_pipe <= !index_read_pipe; //control which delay_read_pipe would get updated (we have 3 pipe to store read data)ss
                delay_read_pipe[index_read_pipe][added_read_pipe_max] <= 1'b1; //update delay_read_pipe
            end
            for(index = 0; index < LANES; index = index + 1) begin
                /* verilator lint_off WIDTH */
                if(delay_read_pipe[0][added_read_pipe_max != added_read_pipe[index]]) begin //same lane
                /* verilator lint_on WIDTH */
                    o_wb_data_q[0][((DQ_BITS*LANES)*0 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*0 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*1 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*1 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*2 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*2 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*3 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*3 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*4 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*4 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*5 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*5 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*6 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*6 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*7 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*7 + 8*index) +: 8]; //update each lane of the burst
                end
                /* verilator lint_off WIDTH */
                if(delay_read_pipe[1][added_read_pipe_max != added_read_pipe[index]]) begin
                /* verilator lint_on WIDTH */
                    o_wb_data_q[1][((DQ_BITS*LANES)*0 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*0 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*1 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*1 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*2 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*2 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*3 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*3 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*4 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*4 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*5 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*5 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*6 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*6 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*7 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*7 + 8*index) +: 8]; //update each lane of the burst
                end
            end
            if(o_wb_ack_read_q[0][0]) begin 
                index_wb_data <= !index_wb_data;
            end
            for(index = 1; index < MAX_ADDED_READ_ACK_DELAY; index = index + 1) begin
                o_wb_ack_read_q[index-1] <= o_wb_ack_read_q[index];
            end
            o_wb_ack_read_q[MAX_ADDED_READ_ACK_DELAY-1] <= 0;
            o_wb_ack_read_q[added_read_pipe_max] <= shift_reg_read_pipe_q[0];

            //abort any outgoing ack when cyc is low
            if(!i_wb_cyc && state_calibrate == DONE_CALIBRATE) begin
                for(index = 0; index < MAX_ADDED_READ_ACK_DELAY; index = index + 1) begin
                    o_wb_ack_read_q[index] <= 0;
                end
                for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                    shift_reg_read_pipe_q[index] <= 0;
                end
            end
       end
    end
    assign o_wb_ack = o_wb_ack_read_q[0][0] && state_calibrate == DONE_CALIBRATE;
    //o_wb_ack_read_q[0][0] is needed internally for write calibration but it must not go outside (since it is not an actual user wb request unless we are in DONE_CALIBRATE) 
    assign o_aux = o_wb_ack_read_q[0][AUX_WIDTH:1]; 
    assign o_wb_data = o_wb_data_q[index_wb_data];
    assign o_phy_dqs_tri_control = !write_dqs[STAGE2_DATA_DEPTH];
    assign o_phy_dq_tri_control = !write_dq[STAGE2_DATA_DEPTH+1];
    generate 
        if(STAGE2_DATA_DEPTH >= 2) begin: TOGGLE_DQS
            assign o_phy_toggle_dqs = write_dqs_val[STAGE2_DATA_DEPTH-2]; 
        end
        else begin: TOGGLE_DQS_DEPTH_LESS_2
            assign o_phy_toggle_dqs = write_dqs_d || write_dqs_q[0]; 
        end
    endgenerate
    /*********************************************************************************************************************************************/
    

    /******************************************************* Read/Write Calibration Sequence *******************************************************/
    always @(posedge i_controller_clk) begin
        if(sync_rst) begin
            state_calibrate <= IDLE;
            train_delay <= 0;
            dqs_store <= 0;
            dqs_count_repeat <= 0;
            dqs_start_index <= 0;
            dqs_target_index <= 0;
            dqs_target_index_orig <= 0;
            o_phy_bitslip <= 0;
            o_phy_odelay_data_ld <= 0;
            o_phy_odelay_dqs_ld <= 0;
            o_phy_idelay_data_ld <= 0;
            o_phy_idelay_dqs_ld <= 0;
            lane_times_8 <= 0;
            idelay_data_cntvaluein_prev <= 0;
            initial_dqs <= 1;
            lane <= 0;
            dqs_bitslip_arrangement <= 0;
            write_calib_dqs <= 0;
            write_calib_dq <= 0;
            write_calib_odt <= 0;
            prev_write_level_feedback <= 1;
            write_calib_stb <= 0;//actual request flag
            write_calib_aux <= 0; //AUX ID
            write_calib_we <= 0; //write-enable
            write_calib_col <= 0;
            write_calib_data <= 0;
            pause_counter <= 0;
            read_data_store <= 0;
            write_pattern <= 0;
            added_read_pipe_max <= 0;
            dqs_start_index_stored <= 0;
            dqs_start_index_repeat <= 0;        
            delay_before_write_level_feedback <= 0;
            delay_before_read_data <= 0;
            read_lane_data <= 0;
            o_phy_write_leveling_calib <= 0;
            odelay_cntvalue_repeated <= 0;
            write_level_fail <= 0;
            for(index = 0; index < LANES; index = index + 1) begin
                added_read_pipe[index] <= 0;
                data_start_index[index] <= 0;
                odelay_data_cntvaluein[index] <= DATA_INITIAL_ODELAY_TAP[4:0];
                odelay_dqs_cntvaluein[index] <= DQS_INITIAL_ODELAY_TAP[4:0];
                idelay_data_cntvaluein[index] <= DATA_INITIAL_IDELAY_TAP[4:0];
                idelay_dqs_cntvaluein[index] <= DQS_INITIAL_IDELAY_TAP[4:0];
                dq_target_index[index] <= 0;
            end
        end
        else begin
            write_calib_stb <= 0;//actual request flag
            write_calib_aux <= 0; //AUX ID
            write_calib_we <= 0; //write-enable
            write_calib_col <= 0;
            write_calib_data <= 0;
            write_calib_dq <= 0;
            train_delay <= (train_delay==0)? 0:(train_delay - 1);
            delay_before_read_data <= (delay_before_read_data == 0)? 0: delay_before_read_data - 1;
            delay_before_write_level_feedback <= (delay_before_write_level_feedback == 0)? 0: delay_before_write_level_feedback - 1;
            o_phy_bitslip <= 0;
            o_phy_odelay_data_ld <= 0;
            o_phy_odelay_dqs_ld <= 0;
            o_phy_idelay_data_ld <= 0;
            o_phy_idelay_dqs_ld <= 0;
            /* verilator lint_off WIDTH */
            lane_times_8 <= lane << 3;
            /* verilator lint_on WIDTH */
            idelay_data_cntvaluein_prev <= idelay_data_cntvaluein[lane];

            if(wb2_update) begin
                odelay_data_cntvaluein[wb2_write_lane] <=  wb2_phy_odelay_data_ld[wb2_write_lane]? wb2_phy_odelay_data_cntvaluein : odelay_data_cntvaluein[wb2_write_lane];
                odelay_dqs_cntvaluein[wb2_write_lane] <= wb2_phy_odelay_dqs_ld[wb2_write_lane]? wb2_phy_odelay_dqs_cntvaluein : odelay_dqs_cntvaluein[wb2_write_lane];
                idelay_data_cntvaluein[wb2_write_lane] <= wb2_phy_idelay_data_ld[wb2_write_lane]? wb2_phy_idelay_data_cntvaluein : idelay_data_cntvaluein[wb2_write_lane];
                idelay_dqs_cntvaluein[wb2_write_lane] <= wb2_phy_idelay_dqs_ld[wb2_write_lane]? wb2_phy_idelay_dqs_cntvaluein : idelay_dqs_cntvaluein[wb2_write_lane];
                o_phy_odelay_data_ld <= wb2_phy_odelay_data_ld;
                o_phy_odelay_dqs_ld <= wb2_phy_odelay_dqs_ld;
                o_phy_idelay_data_ld <= wb2_phy_idelay_data_ld;
                o_phy_idelay_dqs_ld <= wb2_phy_idelay_dqs_ld;
                lane <= wb2_write_lane;
            end
            else if(state_calibrate != DONE_CALIBRATE) begin
                // increase cntvalue every load to prepare for possible next load
                odelay_data_cntvaluein[lane] <= o_phy_odelay_data_ld[lane]? odelay_data_cntvaluein[lane] + 1: odelay_data_cntvaluein[lane];
                odelay_dqs_cntvaluein[lane] <= o_phy_odelay_dqs_ld[lane]? odelay_dqs_cntvaluein[lane] + 1: odelay_dqs_cntvaluein[lane];
                idelay_data_cntvaluein[lane] <= o_phy_idelay_data_ld[lane]? idelay_data_cntvaluein[lane] + 1: idelay_data_cntvaluein[lane];
                idelay_dqs_cntvaluein[lane] <= o_phy_idelay_dqs_ld[lane]? idelay_dqs_cntvaluein[lane] + 1: idelay_dqs_cntvaluein[lane];
            end
            if(initial_dqs) begin
                dqs_target_index <= dqs_target_index_value;
                dq_target_index[lane] <= dqs_target_index_value;
                dqs_target_index_orig <= dqs_target_index_value;
            end
            if(idelay_dqs_cntvaluein[lane] == 0) begin //go back to previous odd
                dqs_target_index <= dqs_target_index_orig - 2;
            end
            if(idelay_data_cntvaluein[lane] == 0 && idelay_data_cntvaluein_prev == 31) begin
                dq_target_index[lane] <= dqs_target_index_orig - 2;
            end
            
            // FSM
            case(state_calibrate) 
                IDLE: if(i_phy_idelayctrl_rdy && instruction_address == 13) begin //we are now inside instruction 15 with maximum delay
                        state_calibrate <= BITSLIP_DQS_TRAIN_1;
                        lane <= 0;
                        o_phy_odelay_data_ld <= {LANES{1'b1}};
                        o_phy_odelay_dqs_ld <= {LANES{1'b1}};
                        o_phy_idelay_data_ld <= {LANES{1'b1}};
                        o_phy_idelay_dqs_ld <= {LANES{1'b1}};
                        pause_counter <= 1; //pause instruction address @13 until read calibration finishes
                        write_calib_dqs <= 0;
                        write_calib_odt <= 0;
                        o_phy_write_leveling_calib <= 0;
                      end
                      else if(instruction_address == 13) begin
                        pause_counter <= 1; //pause instruction address @13 until read calibration finishes
                      end
  BITSLIP_DQS_TRAIN_1: if(train_delay == 0) begin
                        /* Bitslip cannot be asserted for two consecutive CLKDIV cycles; Bitslip must be
                        deasserted for at least one CLKDIV cycle between two Bitslip assertions.The user 
                        logic should wait for at least two CLKDIV cycles in SDR mode or three CLKDIV cycles 
                        in DDR mode, before analyzing the received data pattern and potentially issuing 
                        another Bitslip command. If the ISERDESE2 is reset, the Bitslip logic is also reset
                        and returns back to its initial state.
                        */
                        if(i_phy_iserdes_bitslip_reference[lane*serdes_ratio*2 +: 8] == 8'b0111_1000) begin //initial arrangement
                            state_calibrate <= MPR_READ;
                            initial_dqs <= 1;
                            dqs_start_index_repeat <= 0;
                            dqs_start_index_stored <= 0;
                        end                
                        else begin
                            o_phy_bitslip[lane] <= 1;
                            train_delay <= 3;
                        end        
                      end
                      
            MPR_READ: if(delay_before_read_data == 0) begin //align the incoming DQS during reads to the controller clock 
                             //issue_read_command = 1;
                             /* verilator lint_off WIDTH */
                             delay_before_read_data <= READ_DELAY + 1 + 2 + 1 - 1; ///1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
                             /* verilator lint_on WIDTH */
                             state_calibrate <= COLLECT_DQS;
                             dqs_count_repeat <= 0;
                      end    
                      
        COLLECT_DQS: if(delay_before_read_data == 0) begin
                        dqs_store <= {i_phy_iserdes_dqs[serdes_ratio*2*lane +: 8], dqs_store[(STORED_DQS_SIZE*8-1):8]}; 
                        dqs_count_repeat <= dqs_count_repeat + 1;
                        if(dqs_count_repeat == STORED_DQS_SIZE - 1) begin
                            state_calibrate <= ANALYZE_DQS;
                            dqs_start_index_stored <= dqs_start_index;
                            dqs_start_index <= 0;
                        end
                      end
                      
         ANALYZE_DQS: if(dqs_store[dqs_start_index +: 10] == 10'b01_01_01_01_00) begin
                        dqs_start_index_repeat <= (dqs_start_index == dqs_start_index_stored)? dqs_start_index_repeat + 1: 0; //increase dqs_start_index_repeat when index is the same as before      
                         if(dqs_start_index_repeat == REPEAT_DQS_ANALYZE) begin //the same index appeared  REPEAT_DQS_ANALYZE times in a row, thus can proceed to CALIBRATE_DQS 
                            initial_dqs <= 0;
                            dqs_start_index_repeat <= 0;

                            state_calibrate <= CALIBRATE_DQS;
                         end
                        else begin
                            state_calibrate <= MPR_READ;
                        end
                      end 
                      else begin
                        if(dqs_start_index == (STORED_DQS_SIZE*8-1) ) begin //if we reached end then most likely we hit a glitch where 01_01_01_01_00 is muddied
                            o_phy_idelay_data_ld[lane] <= 1;
                            o_phy_idelay_dqs_ld[lane] <= 1;
                            state_calibrate <= MPR_READ;
                            delay_before_read_data <= 10; //wait for sometime to make sure idelay load settles
                        end
                        else begin
                            dqs_start_index <= dqs_start_index + 1;
                        end
                      end

        CALIBRATE_DQS: if(dqs_start_index_stored == dqs_target_index) begin
                            added_read_pipe[lane] <= { {( 4 - ($clog2(STORED_DQS_SIZE*8) - (3+1)) ){1'b0}} , dq_target_index[lane][$clog2(STORED_DQS_SIZE*8)-1:(3+1)] } 
                                                        + { 3'b0 , (dq_target_index[lane][3:0] >= (5+8)) };
                            dqs_bitslip_arrangement <= 16'b0011_1100_0011_1100 >> dq_target_index[lane][2:0];
                            state_calibrate <= BITSLIP_DQS_TRAIN_2;
                       end
                       else begin
                            o_phy_idelay_data_ld[lane] <= 1;
                            o_phy_idelay_dqs_ld[lane] <= 1;
                            state_calibrate <= MPR_READ;
                            delay_before_read_data <= 10; //wait for sometime to make sure idelay load settles
                       end
                       
  BITSLIP_DQS_TRAIN_2: if(train_delay == 0) begin //train again the ISERDES to capture the DQ correctly
                            if(i_phy_iserdes_bitslip_reference[lane*serdes_ratio*2 +: 8] == dqs_bitslip_arrangement[7:0]) begin
                                /* verilator lint_off WIDTH */
                                if(lane == LANES - 1) begin
                                /* verilator lint_on WIDTH */
                                    pause_counter <= 0; //read calibration now complete so continue the reset instruction sequence
                                    lane <= 0;
                                    odelay_cntvalue_repeated <= 0;
                                    prev_write_level_feedback <= 1'b1;
                                    sample_clk_repeat <= 0;
                                    stored_write_level_feedback <= 0;
                                    o_phy_write_leveling_calib <= 1;
                                    state_calibrate <= START_WRITE_LEVEL;
                                 end
                                 else begin
                                     lane <= lane + 1;
                                     state_calibrate <= BITSLIP_DQS_TRAIN_1;
                                 end
                                 added_read_pipe_max <= added_read_pipe_max > added_read_pipe[lane]? added_read_pipe_max:added_read_pipe[lane];
                            end
                            else begin
                                o_phy_bitslip[lane] <= 1;
                                train_delay <= 3;
                            end
                       end
                      
    START_WRITE_LEVEL: if(!ODELAY_SUPPORTED) begin //skip write levelling if ODELAY is not supported
                            pause_counter <= 0;
                            lane <= 0;
                            state_calibrate <= ISSUE_WRITE_1;
                       end
                       else if(instruction_address == 17) begin
                            write_calib_dqs <= 1'b1;
                            write_calib_odt <= 1'b1;
                            delay_before_write_level_feedback <= DELAY_BEFORE_WRITE_LEVEL_FEEDBACK[$clog2(DELAY_BEFORE_WRITE_LEVEL_FEEDBACK):0];
                            state_calibrate <= WAIT_FOR_FEEDBACK;
                            pause_counter <= 1; // pause instruction address @17 until write calibration finishes
                       end  

    WAIT_FOR_FEEDBACK: if(delay_before_write_level_feedback == 0) begin
                            /* verilator lint_off WIDTH */ //_verilator warning: Bit extraction of var[511:0] requires 9 bit index, not 3 bits (but [lane<<3] is much simpler and cleaner)
                            sample_clk_repeat <= (i_phy_iserdes_data[lane_times_8] == stored_write_level_feedback)? sample_clk_repeat + 1 : 0; //sample_clk_repeat should get the same response 
                            stored_write_level_feedback <= i_phy_iserdes_data[lane_times_8];
                            write_calib_dqs <= 0;
                            if(sample_clk_repeat == REPEAT_CLK_SAMPLING) begin
                                sample_clk_repeat <= 0;
                                prev_write_level_feedback <= stored_write_level_feedback;
                                if(({prev_write_level_feedback, stored_write_level_feedback} == 2'b01) || write_level_fail[lane]) begin
                                    /* verilator lint_on WIDTH */
                                    /* verilator lint_off WIDTH */
                                    if(lane == LANES - 1) begin
                                    /* verilator lint_on WIDTH */
                                            write_calib_odt <= 0;
                                            pause_counter <= 0; //write calibration now complete so continue the reset instruction sequence
                                            lane <= 0;
                                            o_phy_write_leveling_calib <= 0;
                                            state_calibrate <= ISSUE_WRITE_1;
                                    end
                                    else begin
                                        lane <= lane + 1;
                                        odelay_cntvalue_repeated <= 0;
                                        prev_write_level_feedback <= 1'b1;
                                        sample_clk_repeat <= 0;
                                        state_calibrate <= START_WRITE_LEVEL; 
                                    end
                                end
                                else begin
                                    o_phy_odelay_data_ld[lane] <= 1;
                                    o_phy_odelay_dqs_ld[lane] <= 1;
                                    write_level_fail[lane] <= (odelay_cntvalue_repeated && odelay_data_cntvaluein[lane] == 2);
                                    state_calibrate <= START_WRITE_LEVEL; 
                                end
                             end     
                         end
                            
        ISSUE_WRITE_1: if(instruction_address == 22 && !o_wb_stall_q) begin
                        write_calib_stb <= 1;//actual request flag
                        write_calib_aux <= 1; //AUX ID to determine later if ACK is for read or write
                        write_calib_we <= 1; //write-enable
                        write_calib_col <= 0;
                        write_calib_data <= { {LANES{8'h91}}, {LANES{8'h77}}, {LANES{8'h29}}, {LANES{8'h8c}}, {LANES{8'hd0}}, {LANES{8'had}}, {LANES{8'h51}}, {LANES{8'hc1}} }; 
                        state_calibrate <= ISSUE_WRITE_2;
                       end    
        ISSUE_WRITE_2: begin
                        write_calib_stb <= 1;//actual request flag
                        write_calib_aux <= 1; //AUX ID to determine later if ACK is for read or write
                        write_calib_we <= 1; //write-enable
                        write_calib_col <= 8;
                        write_calib_data <= { {LANES{8'h80}}, {LANES{8'hdb}}, {LANES{8'hcf}}, {LANES{8'hd2}}, {LANES{8'h75}}, {LANES{8'hf1}}, {LANES{8'h2c}}, {LANES{8'h3d}} }; 
                        state_calibrate <= ISSUE_READ;
                       end    
          ISSUE_READ: if(!o_wb_stall_q && write_calib_stb == 0) begin
                        write_calib_stb <= 1;//actual request flag
                        write_calib_aux <= 0; //AUX ID to determine later if ACK is for read or write
                        write_calib_we <= 0; //write-enable
                        state_calibrate <= READ_DATA;
                      end   
                      
           READ_DATA: if(o_wb_ack_read_q[0] == {{(AUX_WIDTH){1'b0}}, 1'b1}) begin //wait for the read ack (which has UAX ID of 0}
                         read_data_store <= o_wb_data;
                         state_calibrate <= ANALYZE_DATA;
                         data_start_index[lane] <= 0;
                         // Possible Patterns (strong autocorrel stat)
                         //0x80dbcfd275f12c3d   
                         //0x9177298cd0ad51c1
                         //0x01b79fa4ebe2587b
                         //0x22ee5319a15aa382
                         write_pattern <= 128'h80dbcfd275f12c3d_9177298cd0ad51c1;
                      end   
                 
        ANALYZE_DATA: if(write_pattern[data_start_index[lane] +: 64] == {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                        read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                        read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] }) begin   
                            /* verilator lint_off WIDTH */
                            if(lane == LANES - 1) begin
                            /* verilator lint_on WIDTH */
                                state_calibrate <= DONE_CALIBRATE;
                            end        
                            else begin
                                lane <= lane + 1;
                                data_start_index[lane+1] <= 0;
                            end
                      end 
                      else begin
                            data_start_index[lane] <= data_start_index[lane] + 8;
                            if(data_start_index[lane] == 56) begin //reached the end but no byte in write-pattern matches the data read, issue might be reading at wrong DQS toggle 
                                data_start_index[lane] <= 0;        //so we need to recalibrate the bitslip
                                start_index_check <= 0;
                                state_calibrate <= CHECK_STARTING_DATA;
                            end
                      end     

                      //check if the data starts not at bit 0 (happens if the DQS toggles early than DQ, this means we are calibrated to read at same 
                      //time as DQS toggles but since DQ is late then we need to look which DQS toggle does DQ actually start)
 CHECK_STARTING_DATA: begin
                        if(read_lane_data[start_index_check +: 16] == write_pattern[0 +: 16]) begin //check if first 
                            state_calibrate <= BITSLIP_DQS_TRAIN_3;
                            added_read_pipe[lane] <= { {( 4 - ($clog2(STORED_DQS_SIZE*8) - (3+1)) ){1'b0}} , dq_target_index[lane][$clog2(STORED_DQS_SIZE*8)-1:(3+1)] } 
                                                        + { 3'b0 , (dq_target_index[lane][3:0] >= (5+8)) };
                            dqs_bitslip_arrangement <= 16'b0011_1100_0011_1100 >> dq_target_index[lane][2:0];
                            state_calibrate <= BITSLIP_DQS_TRAIN_3;
                        end
                        else begin
                            start_index_check <= start_index_check + 16;
                            dq_target_index[lane] <= dq_target_index[lane] + 2;
                        end
                      end
      
BITSLIP_DQS_TRAIN_3: if(train_delay == 0) begin //train again the ISERDES to capture the DQ correctly
                        if(i_phy_iserdes_bitslip_reference[lane*serdes_ratio*2 +: 8] == dqs_bitslip_arrangement[7:0]) begin
                             state_calibrate <= ISSUE_WRITE_1; //finished bitslip calibration so we can now issue again new write and then read 
                             added_read_pipe_max <= added_read_pipe_max > added_read_pipe[lane]? added_read_pipe_max:added_read_pipe[lane];
                        end
                        else begin
                            o_phy_bitslip[lane] <= 1;
                            train_delay <= 3;
                        end
                    end
                            
      DONE_CALIBRATE: begin
                        state_calibrate <= DONE_CALIBRATE;
                        if(instruction_address == 19) begin //pre-stall delay to finish all remaining requests
                            pause_counter <= 1; // pause instruction address until pre-stall delay before refresh sequence finishes
                            //skip to instruction address 20 (precharge all before refresh) when no pending requests anymore
                            //toggle it for 1 clk cycle only
                            if(!stage1_pending && !stage2_pending && o_wb_stall) begin 
                               pause_counter <= 0; // pre-stall delay done since all remaining requests are completed
                            end
                        end
                      end

            endcase
        `ifdef FORMAL_COVER
            state_calibrate <= DONE_CALIBRATE;
        `endif
        
             read_lane_data <= {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                    read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                    read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] };
             //maximum value has been reached and will go back to zero at next load
             if(odelay_data_cntvaluein[lane] == 31) begin
                odelay_cntvalue_repeated <= 1; 
             end
        end
    end      
    assign issue_read_command = (state_calibrate == MPR_READ && delay_before_read_data == 0);
    assign issue_write_command = 0;
    assign o_phy_odelay_data_cntvaluein = odelay_data_cntvaluein[lane]; 
    assign o_phy_odelay_dqs_cntvaluein = odelay_dqs_cntvaluein[lane];
    assign o_phy_idelay_data_cntvaluein = idelay_data_cntvaluein[lane];
    assign o_phy_idelay_dqs_cntvaluein = idelay_dqs_cntvaluein[lane];
    assign dqs_target_index_value = dqs_start_index_stored[0]? dqs_start_index_stored + 2: dqs_start_index_stored + 1;
    reg[31:0] wb_data_to_wb2 = 0;
    always @(posedge i_controller_clk) begin
        if(o_wb_ack_read_q[0][0]) wb_data_to_wb2 <= o_wb_data[31:0]; //save data read
    end
    /*********************************************************************************************************************************************/


    /******************************************************* Wishbone 2 (PHY) Interface *******************************************************/

   always @(posedge i_controller_clk) begin
        if(sync_rst) begin
            wb2_stb <= 0;
            wb2_we <= 0; //data to be written which must have high i_wb2_sel are: {LANE_NUMBER, CNTVALUEIN}
            wb2_addr <= 0;
            wb2_data <= 0;
            wb2_sel <= 0;
        end
        else begin
            if(i_wb2_cyc && !o_wb2_stall) begin 
                wb2_stb <= i_wb2_stb;
                wb2_we <= i_wb2_we; //data to be written which must have high i_wb2_sel are: {LANE_NUMBER, CNTVALUEIN} 
                wb2_addr <= i_wb2_addr;
                wb2_data <= i_wb2_data;
                wb2_sel <= i_wb2_sel;
            end
            else if(!o_wb2_stall) begin
                wb2_stb <= 0;
                wb2_we <= 0;
                wb2_addr <= 0;
                wb2_data <= 0;
                wb2_sel <= 0;
            end
        end
   end 

   always @(posedge i_controller_clk) begin
       if(sync_rst) begin
           wb2_phy_odelay_data_cntvaluein <= 0;
           wb2_phy_odelay_data_ld <= 0;
           wb2_phy_odelay_dqs_cntvaluein <= 0;
           wb2_phy_odelay_dqs_ld <= 0;
           wb2_phy_idelay_data_cntvaluein <= 0;
           wb2_phy_idelay_data_ld <= 0;
           wb2_phy_idelay_dqs_cntvaluein <= 0;
           wb2_phy_idelay_dqs_ld <= 0;
           wb2_update <= 0;
           wb2_write_lane <= 0;
           o_wb2_ack <= 0;
           o_wb2_stall <= 1;
           o_wb2_data <= 0;
       end
       else begin
           wb2_phy_odelay_data_ld <= 0; 
           wb2_phy_odelay_dqs_ld <= 0;
           wb2_phy_idelay_data_ld <= 0;
           wb2_phy_idelay_dqs_ld <= 0;
           wb2_update <= 0;
           wb2_write_lane <= 0;
           o_wb2_ack <= wb2_stb && i_wb2_cyc; //always ack right after request
           o_wb2_stall <= 0; //never stall
           if(wb2_stb && i_wb2_cyc) begin
                case(wb2_addr[3:0]) 
                    //read/write odelay cntvalue for DQ line
                    0: if(wb2_we) begin 
                            wb2_phy_odelay_data_cntvaluein <= wb2_data[4:0]; //save first 5 bits as CNTVALUEIN for the ODELAYE2 for DQ
                            wb2_phy_odelay_data_ld <= 1 << (wb2_data[5 +: lanes_clog2]); //raise the lane to be loaded with new cntvaluein
                            wb2_update <= wb2_sel[$rtoi($ceil( (lanes_clog2 + 5)/8.0 )) - 1:0]; //only update when sel bit is high (data is valid)
                       end
                       else begin
                            o_wb2_data <= { {(WB2_DATA_BITS-5){1'b0}} , odelay_data_cntvaluein[wb2_addr[4 +: lanes_clog2]] };//use next bits of address as lane number to be read
                       end

                    //read/write odelay cntvalue for DQS line
                    1: if(wb2_we) begin 
                            wb2_phy_odelay_dqs_cntvaluein <= wb2_data[4:0]; //save first 5 bits as CNTVALUEIN for the ODELAYE2 for DQS
                            wb2_phy_odelay_dqs_ld <= 1 << (wb2_data[5 +: lanes_clog2]); //raise the lane to be loaded with new cntvaluein
                            wb2_update <= wb2_sel[$rtoi($ceil( (lanes_clog2 + 5)/8.0 )) - 1:0]; //only update when sel bit is high (data is valid)
                       end
                       else begin
                            o_wb2_data <= { {(WB2_DATA_BITS-5){1'b0}} , odelay_dqs_cntvaluein[wb2_addr[4 +: lanes_clog2]] };//use next bits of address as lane number to be read
                       end
                       
                    //read/write idelay cntvalue for DQ line
                    2: if(wb2_we) begin 
                            wb2_phy_idelay_data_cntvaluein <= wb2_data[4:0]; //save first 5 bits as CNTVALUEIN for the IDELAYE2 for DQ
                            wb2_phy_idelay_data_ld <= 1 << (wb2_data[5 +: lanes_clog2]); //save next 5 bits for lane number to be loaded with new delay
                            wb2_update <= wb2_sel[$rtoi($ceil( (lanes_clog2 + 5)/8.0 )) - 1:0]; //only update when sel bit is high (data is valid)
                       end
                       else begin
                            o_wb2_data <= { {(WB2_DATA_BITS-5){1'b0}} , idelay_data_cntvaluein[wb2_addr[4 +: lanes_clog2]] }; //use next bits of address as lane number to be read
                       end

                    //read/write idelay cntvalue for DQS line
                    3: if(wb2_we) begin 
                            wb2_phy_idelay_dqs_cntvaluein <= wb2_data[4:0]; //save first 5 bits as CNTVALUEIN for the IDELAYE2 for DQS
                            wb2_phy_idelay_dqs_ld <= 1 << (wb2_data[5 +: lanes_clog2]); //save next 5 bits for lane number to be loaded with new delay
                            wb2_update <= wb2_sel[$rtoi($ceil( (lanes_clog2 + 5)/8.0 )) - 1:0]; //only update when sel bit is high (data is valid)
                       end
                       else begin
                            o_wb2_data <= { {(WB2_DATA_BITS-5){1'b0}} , idelay_dqs_cntvaluein[wb2_addr[4 +: lanes_clog2]] }; //use next bits of address as lane number to be read
                       end

                    4: if(!wb2_we) begin
                            o_wb2_data[0] <= i_phy_idelayctrl_rdy; //1 bit, should be high when IDELAYE2 is ready
                            o_wb2_data[1 +: 5] <= state_calibrate; //5 bits, FSM state of the calibration sequence
                            o_wb2_data[1 + 5 +: 5] <= instruction_address; //5 bits, address of the reset sequence
                            o_wb2_data[1 + 5 + 5 +: 4] <= added_read_pipe_max; //4 bit, max added read delay (must have a max value of 1)
                       end

                    5: if(!wb2_we) begin
                            for(index = 0; index < LANES; index = index + 1) begin
                             o_wb2_data[4*index +: 4] <= added_read_pipe[index];
                            end
                            //added read pipe delay for lanes 0-to-3 (4 bits each lane the max is just 1 for each)
                        end

                    6: if(!wb2_we) begin
                            o_wb2_data <= dqs_store[31:0]; //show last 4 sets of received 8-bit DQS during MPR (repeated 4 times, must have a value of 10'b01_01_01_01_00 somewhere)
                        end

                    7: if(!wb2_we) begin
                            for(index = 0; 8*index < 32 && index < LANES; index = index + 1) begin
                                 o_wb2_data[8*index +: 8] <= i_phy_iserdes_bitslip_reference[8*index +: 8]; //show the 8-bit bitslip reference for lanes 0[7:0], 1[15:8], 2[23:16], 3[31:24]
                            end
                        end

                    8: if(!wb2_we) begin
                            o_wb2_data <= read_data_store[31:0]; //first 32 bits of the data read after first write using the write_pattern 128'h80dbcfd275f12c3d_9177298cd0ad51c1
                        end

                    9: if(!wb2_we) begin
                            o_wb2_data <= write_pattern[31:0]; //first 32 bit of the patern written on the first write just for checking (128'h80dbcfd275f12c3d_9177298cd0ad51c1)
                        end
                        
                    10: if(!wb2_we) begin //0x28 (data read back)
                            o_wb2_data <= wb_data_to_wb2[31:0]; //first 32 bit of the patern written on the first write just for checking (128'h80dbcfd275f12c3d_9177298cd0ad51c1)
                        end
                    11: if(!wb2_we) begin //0x2c (data write)
                            o_wb2_data <= stage2_data_unaligned[31:0]; //first 32 bit of the patern written on the first write just for checking (128'h80dbcfd275f12c3d_9177298cd0ad51c1)
                        end   
                    12: if(!wb2_we) begin //0x30
                            o_wb2_data <= {stage1_we,stage1_col[6:0],stage1_data[7:0],{8'b0,stage1_dm[7:0]}}; //check if proper request is received
                        end   
                    13: if(!wb2_we) begin //0x30
                            o_wb2_data <= 32'hf7; //lane 1
                        end
                    14: if(!wb2_we) begin //0x30
                            o_wb2_data <= {{(32-LANES){1'b0}} , write_level_fail}; //lane 1
                        end
                        
              default: if(!wb2_we) begin //read 
                           o_wb2_data <= {(WB2_DATA_BITS/2){2'b10}}; //return alternating 1s and 0s when address to be read is invalid 
                       end
                endcase

                wb2_write_lane <= wb2_data[5 +: lanes_clog2]; //save next 5 bits for lane number to be loaded with new delay
            end //end of if(wb2_stb)
        end//end of else
    end//end of always
    // Logic connected to debug port
    // Logic connected to debug port
    wire debug_trigger;
    //assign o_debug1 = {debug_trigger, state_calibrate[4:0], instruction_address[4:0], i_phy_iserdes_dqs[7:0], o_phy_dqs_tri_control, 
    //    o_phy_dq_tri_control, i_phy_iserdes_dqs[15:8], lane[2:0]};
    //assign o_debug1 = {debug_trigger, o_wb2_stall, { {(3-lanes_clog2){1'b0}} , lane[lanes_clog2-1:0] } , dqs_start_index_stored[2:0], dqs_target_index[2:0], delay_before_read_data[2:0], 
    //            o_phy_idelay_dqs_ld[lane], state_calibrate[4:0], dqs_store[11:0]};
    //assign o_debug1 = {debug_trigger, 2'b00, delay_before_read_data[3:0] ,i_phy_idelayctrl_rdy, 2'b00, lane, dqs_start_index_stored[4:0], 
    //    dqs_target_index[4:0], instruction_address[4:0], state_calibrate[4:0], o_wb2_stall};       
    //assign o_debug1 = {debug_trigger,stage1_we,stage1_col[5:0],stage1_data[7:0],{8'b0,stage1_dm[7:0]}};
    /*assign o_debug2 = {debug_trigger, idelay_dqs_cntvaluein[lane][4:0], idelay_data_cntvaluein[lane][4:0],{i_phy_iserdes_dqs[15:0]}, 
                o_phy_dqs_tri_control, o_phy_dq_tri_control,
                (i_phy_iserdes_data == 0), (i_phy_iserdes_data == {(DQ_BITS*LANES*8){1'b1}}), (i_phy_iserdes_data < { {(DQ_BITS*LANES*4){1'b0}}, {(DQ_BITS*LANES*4){1'b1}} } )
                }; */
    /*assign o_debug3 = {debug_trigger, delay_before_write_level_feedback[4:0], odelay_data_cntvaluein[lane][4:0], odelay_dqs_cntvaluein[lane][4:0], 
            state_calibrate[4:0], prev_write_level_feedback, i_phy_iserdes_data[48], i_phy_iserdes_data[40], i_phy_iserdes_data[32], i_phy_iserdes_data[24]
            , i_phy_iserdes_data[16], i_phy_iserdes_data[8], i_phy_iserdes_data[0], {2'b0,lane} };
    */
    
    /*assign o_debug3 = {debug_trigger, lane[2:0], delay_before_read_data[3:0], i_phy_iserdes_data[448 +: 3], i_phy_iserdes_data[384 +: 3], i_phy_iserdes_data[320 +: 3], 
                        i_phy_iserdes_data[256 +: 3], i_phy_iserdes_data[192 +: 3], i_phy_iserdes_data[128 +: 3], i_phy_iserdes_data[64 +: 3], i_phy_iserdes_data[0 +: 3]};*/
    //assign o_debug3 = {debug_trigger, i_phy_iserdes_data[192 +: 7], i_phy_iserdes_data[128 +: 8], i_phy_iserdes_data[64 +: 8], i_phy_iserdes_data[0 +: 8]};
    //assign o_debug3 = {debug_trigger,  i_phy_iserdes_data[48 +: 7], i_phy_iserdes_data[32 +: 8], i_phy_iserdes_data[16 +: 8], i_phy_iserdes_data[0 +: 8]};
    assign o_debug1 = {debug_trigger,i_phy_iserdes_dqs[7:0],state_calibrate[4:0], instruction_address[4:0],o_phy_idelay_dqs_ld[lane],o_phy_idelay_data_ld[lane],
                        o_phy_odelay_data_ld[lane],o_phy_odelay_dqs_ld[lane], delay_before_read_data[2:0], delay_before_write_level_feedback[4:0],lane};
    assign o_debug2 = {debug_trigger,i_phy_iserdes_data[62:32]};
    assign o_debug3 = {debug_trigger,i_phy_iserdes_data[30:0]};
    assign debug_trigger = o_wb_ack_read_q[0][0];
    (* mark_debug = "true" *) wire dq_all_zeroes;
    assign dq_all_zeroes = (i_phy_iserdes_data == {(DQ_BITS*LANES*8){1'b0}});
    /*********************************************************************************************************************************************/


    /******************************************************* Functions *******************************************************/
    //convert nanoseconds time input to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    //output is set at same length as a MRS command (19 bits) to maximize the time slot
    function [DELAY_SLOT_WIDTH - 1:0] ns_to_cycles (
`ifdef YOSYS
    input integer ns
`else
    input real ns //YOSYS ERROR: syntax error, unexpected TOK_REAL
`endif
    );                
            /* verilator lint_off WIDTHTRUNC */              
            ns_to_cycles = $rtoi($ceil(ns*1.0/CONTROLLER_CLK_PERIOD)); 
            /* verilator lint_on WIDTHTRUNC */
    endfunction

    //convert nCK input (number of DDR3 clock cycles) to number of controller clock cycles (referenced to serdes_ratio)
    function [DELAY_SLOT_WIDTH - 1:0] nCK_to_cycles (input integer nCK); 
            /* verilator lint_off WIDTHTRUNC */
            nCK_to_cycles =  $rtoi($ceil(nCK*1.0/serdes_ratio)); 
            /* verilator lint_on WIDTHTRUNC */
    endfunction
    
    
    //convert nanoseconds time input  to number of DDR clock cycles (referenced to DDR3_CLK_PERIOD)
    function integer ns_to_nCK (
`ifdef YOSYS 
    input integer ns
`else
    input real ns //YOSYS ERROR: syntax error, unexpected TOK_REAL
`endif
    );
        ns_to_nCK = $rtoi($ceil(ns*1.0/DDR3_CLK_PERIOD)); 
    endfunction
    
    //convert DDR clock cycles to nanoseconds (referenced to DDR3_CLK_PERIOD)
`ifdef YOSYS
    function integer nCK_to_ns (input integer nCK); 
        nCK_to_ns = $rtoi($ceil(nCK*1.0*DDR3_CLK_PERIOD)); 
`else
    function real nCK_to_ns (input integer nCK); //YOSYS ERROR: syntax error, unexpected TOK_REAL
        nCK_to_ns = $ceil(nCK*1.0*DDR3_CLK_PERIOD); 
`endif
    endfunction
    
    // functions used to infer some localparam values
`ifdef YOSYS
    function integer max(input integer a, input integer b);
`else
    function real max(input real a, input real b); //YOSYS ERROR: syntax error, unexpected TOK_REAL
`endif
        if(a >= b) max = a;
        else max = b;
    endfunction
    
    function integer max_int(input integer a, input integer b);
        if(a >= b) max_int = a;
        else max_int = b;
    endfunction
                      
    //Find the 3-bit value for the Mode Register 0  WR (Write recovery for auto-precharge)
    function[2:0] WRA_mode_register_value(input integer WRA); 
            //WR_min (write recovery for autoprecharge) in clock cycles is calculated by dividing tWR(in ns) by tCK(in ns) and rounding up to the next integer.
            //The WR value in the mode register must be programmed to be equal or larger than WRmin.
        case(WRA+1) 
            1,2,3,4,5: WRA_mode_register_value = 3'b001;
                    6: WRA_mode_register_value = 3'b010;
                    7: WRA_mode_register_value = 3'b011;
                    8: WRA_mode_register_value = 3'b100;
                 9,10: WRA_mode_register_value = 3'b101;
                11,12: WRA_mode_register_value = 3'b110;
                13,14: WRA_mode_register_value = 3'b111;
                15,16: WRA_mode_register_value = 3'b000;
          default: begin
                    WRA_mode_register_value = 3'b000; //defaulting to largest write recovery cycles: 16 cycles
                   end
        endcase
    endfunction
    
    function[1:0] get_slot (input[3:0] cmd); //cmd can either be CMD_PRE,CMD_ACT, CMD_WR, CMD_RD
        integer delay;
        reg[1:0] slot_number, read_slot, write_slot, anticipate_activate_slot, anticipate_precharge_slot;
        begin
            // find read command slot number
            delay = CL_nCK;
            for(slot_number = 0 ;  delay != 0 ; delay = delay - 1) begin
                    slot_number = slot_number - 1'b1;
            end 
            read_slot = slot_number;
            
            // find write command slot number
            delay = CWL_nCK;
            for(slot_number = 0 ;  delay != 0; delay = delay - 1) begin
                    slot_number = slot_number - 1'b1;
            end 
            write_slot = slot_number;
            
            // find anticipate activate command slot number
            if(CL_nCK > CWL_nCK) slot_number = read_slot;
            else slot_number = write_slot;
            `ifdef SUPPORT_REAL
            delay = ns_to_nCK(tRCD); 
            `else
            delay = ns_to_nCK($rtoi(tRCD)); 
            `endif
            for(slot_number = slot_number;  delay != 0; delay = delay - 1) begin
                    slot_number = slot_number - 1'b1;
            end 
            anticipate_activate_slot = slot_number;
            // if computed anticipate_activate_slot is same with either write_slot or read_slot, decrement slot number until 
            while(anticipate_activate_slot == write_slot || anticipate_activate_slot == read_slot) begin 
                anticipate_activate_slot = anticipate_activate_slot - 1'b1;
            end
            
            //the remaining slot will be for precharge command
            anticipate_precharge_slot = 0;
            while(anticipate_precharge_slot == write_slot || anticipate_precharge_slot == read_slot || anticipate_precharge_slot == anticipate_activate_slot) begin
                anticipate_precharge_slot = anticipate_precharge_slot  - 1'b1;
            end
            case(cmd)
                CMD_RD: get_slot = read_slot;
                CMD_WR: get_slot = write_slot;
                CMD_ACT: get_slot = anticipate_activate_slot;
                CMD_PRE: get_slot = anticipate_precharge_slot;
                default: begin
                            `ifdef FORMAL
                                assert(0); //force FORMAL to fail if this is ever reached
                            `endif
                         end
            endcase
        end
    endfunction
    
    //find the delay to be used by delay_before_xxxx_counter. 
    // - delay_nCK = delay required between the two commands in DDR3 clock cycles
    // - start_slot = slot number of the first command
    // - end_slot = slot number of the second command
    // returns the number of controller clock cycles to satisfy the delay required between the two commands
    function [3:0] find_delay(input integer delay_nCK, input reg[1:0] start_slot, input reg[1:0] end_slot);
        integer k; //error: variable declaration assignments are only allowed at the module level
        begin
            k = 0;
            /* verilator lint_off WIDTH */
            while( ((4 - start_slot) + end_slot + 4*k) < delay_nCK) begin
            /* verilator lint_on WIDTH */
                k = k + 1;
            end
            find_delay = k[3:0];
        end
    endfunction
    /*********************************************************************************************************************************************/


`ifndef YOSYS
    ///YOSYS: System task `$display' called with invalid/unsupported format specifier
    initial begin
        $display("TEST FUNCTIONS\n-----------------------------\n");
        $display("Test ns_to_cycles() function:");
        $display("\tns_to_cycles(15) = %0d [exact]", ns_to_cycles(15) );
        $display("\tns_to_cycles(14.5) = %0d [round-off]", ns_to_cycles(14.5) );
        $display("\tns_to_cycles(11) = %0d [round-up]\n", ns_to_cycles(11) );
        
        $display("Test nCK_to_cycles() function:");
        $display("\tns_to_cycles(16) = %0d [exact]", nCK_to_cycles(16) );
        $display("\tns_to_cycles(15) = %0d [round-off]", nCK_to_cycles(15) );
        $display("\tns_to_cycles(13) = %0d [round-up]\n", nCK_to_cycles(13) );
        
        $display("Test ns_to_nCK() function:");
        $display("\tns_to_cycles(15) = %0d [exact]", ns_to_nCK(15) );
        $display("\tns_to_cycles(14.875) = %0d [round-off]", ns_to_nCK(14.875) );
        $display("\tns_to_cycles(13.875) = %0d [round-up] \n", ns_to_nCK(13.875) );
        
        $display("Test nCK_to_ns() function:");
        $display("\tns_to_cycles(4) =  %f [exact]", nCK_to_ns(4) );
        $display("\tns_to_cycles(14.875) = %f [round-off]", nCK_to_ns(3) );
        $display("\tns_to_cycles(13.875) = %f [round-up]\n", nCK_to_ns(5) );
        
        $display("Test nCK_to_ns() function:");
        $display("\tns_to_cycles(4) = %f [exact]", nCK_to_ns(4) );
        $display("\tns_to_cycles(14.875) = %f [round-off]", nCK_to_ns(3) );
        $display("\tns_to_cycles(13.875) = %f [round-up]\n", nCK_to_ns(5) );
        
        $display("Test $floor() function:");
        $display("\t$floor(5/2) = %f", $floor(5/2) );
        $display("\t$floor(9/4) = %f", $floor(9/4) );
        $display("\t$floor(9/4) = %f", $floor(8/4) );
        $display("\t$floor(9/5) = %f\n", $floor(9/5) );

        $display("\nDISPLAY CONTROLLER PARAMETERS\n-----------------------------\n");
        $display("MICRON_SIM = %0d", MICRON_SIM);
        $display("ODELAY_SUPPORTED = %0d", ODELAY_SUPPORTED);
        $display("CONTROLLER_CLK_PERIOD = %.2f", CONTROLLER_CLK_PERIOD);
        $display("DDR3_CLK_PERIOD = %.2f", DDR3_CLK_PERIOD);
        $display("ROW_BITS = %0d", ROW_BITS);
        $display("COL_BITS = %0d", COL_BITS);
        $display("BA_BITS = %0d", BA_BITS);
        $display("DQ_BITS = %0d", DQ_BITS);
        $display("LANES = %0d", LANES);
        $display("AUX_WIDTH = %0d", AUX_WIDTH);
        $display("WB2_ADDR_BITS = %0d", WB2_ADDR_BITS);
        $display("WB2_DATA_BITS = %0d", WB2_DATA_BITS);

        $display("serdes_ratio = %0d", serdes_ratio);
        $display("wb_addr_bits = %0d", wb_addr_bits);
        $display("wb_data_bits = %0d", wb_data_bits);
        $display("wb_sel_bits  = %0d", wb_sel_bits);
        $display("wb2_sel_bits = %0d", wb2_sel_bits);
        $display("cmd_len = %0d", cmd_len );
        $display("DELAY_COUNTER_WIDTH = %0d", DELAY_COUNTER_WIDTH);
        $display("DELAY_SLOT_WIDTH = %0d", DELAY_SLOT_WIDTH);

        //$display("$bits(instruction):%0d - $bits(CMD_MRS):%0d - $bits(MR0):%0d  =  5 = %0d",  $bits(instruction), $bits(CMD_MRS) , $bits(MR0), ($bits(instruction) - $bits(CMD_MRS) - $bits(MR0)));
        $display("serdes_ratio = %0d",serdes_ratio);
        $display("wb_addr_bits = %0d",wb_addr_bits);
        $display("wb_data_bits = %0d",wb_data_bits);
        $display("wb_sel_bits = %0d\n\n",wb_sel_bits);

        $display("READ_SLOT = %0d", READ_SLOT);
        $display("WRITE_SLOT = %0d", WRITE_SLOT);
        $display("ACTIVATE_SLOT = %0d", ACTIVATE_SLOT);
        $display("PRECHARGE_SLOT = %0d", PRECHARGE_SLOT);
        
        $display("\n\nDELAYS:");
        $display("\tns_to_nCK(tRCD): %0d", ns_to_nCK(tRCD));
        $display("\tns_to_nCK(tRP): %0d", ns_to_nCK(tRP));
        $display("\tns_to_nCK(tRTP): %0d", ns_to_nCK(tRTP));
        $display("\ttCCD: %0d", tCCD);
        $display("\t(CL_nCK + tCCD + 2 - CWL_nCK): %0d", (CL_nCK + tCCD + 2 - CWL_nCK));
        $display("\t(CWL_nCK + 4 + ns_to_nCK(tWR)): %0d", (CWL_nCK + 4 + ns_to_nCK(tWR)));
        $display("\t(CWL_nCK + 4 + ns_to_nCK(tWTR)): %0d", (CWL_nCK + 4 + ns_to_nCK(tWTR)));
        
        $display("\n\nPRECHARGE_TO_ACTIVATE_DELAY = %0d", PRECHARGE_TO_ACTIVATE_DELAY);
        $display("ACTIVATE_TO_WRITE_DELAY = %0d", ACTIVATE_TO_WRITE_DELAY);
        $display("ACTIVATE_TO_READ_DELAY =  %0d", ACTIVATE_TO_READ_DELAY);
        $display("ACTIVATE_TO_PRECHARGE_DELAY =  %0d", ACTIVATE_TO_PRECHARGE_DELAY);
        $display("READ_TO_WRITE_DELAY = %0d", READ_TO_WRITE_DELAY);
        $display("READ_TO_READ_DELAY = %0d", READ_TO_READ_DELAY);
        $display("READ_TO_PRECHARGE_DELAY = %0d", READ_TO_PRECHARGE_DELAY);
        $display("WRITE_TO_WRITE_DELAY = %0d", WRITE_TO_WRITE_DELAY);
        $display("WRITE_TO_READ_DELAY = %0d", WRITE_TO_READ_DELAY);
        $display("WRITE_TO_PRECHARGE_DELAY = %0d", WRITE_TO_PRECHARGE_DELAY);
        $display("STAGE2_DATA_DEPTH = %0d", STAGE2_DATA_DEPTH);
        $display("READ_ACK_PIPE_WIDTH = %0d", READ_ACK_PIPE_WIDTH);
    end
`endif
    
    
`ifdef FORMAL
    `define TEST_CONTROLLER_PIPELINE

    `ifdef FORMAL_COVER
        initial assume(!i_rst_n); 
        reg[24:0] f_wb_inputs[31:0];
        reg[9:0] f_reset_counter = 0;
        reg[4:0] f_index = 0;
        reg f_past_valid = 0; 
        initial begin
            /*
            // Sequential read to row 0 then jump to row 2
            f_wb_inputs[0] = {1'b0, {14'd0,3'd1, 7'd0}}; //read 
            f_wb_inputs[1] = {1'b0, {14'd0,3'd1, 7'd1}}; //read on same bank (tCCD)
            f_wb_inputs[2] = {1'b0, {14'd0,3'd1, 7'd2}}; //write on same bank (tRTW)
            f_wb_inputs[3] = {1'b0, {14'd0,3'd1, 7'd3}}; //write on same bank (tCCD)
            f_wb_inputs[4] = {1'b0, {14'd0,3'd1, 7'd4}}; //read on different bank 
            f_wb_inputs[5] = {1'b0, {14'd0,3'd1, 7'd5}}; //write on same bank (tRTW)
            f_wb_inputs[6] = {1'b0, {14'd2,3'd1, 7'd6}}; //write on different bank (already activated)
            f_wb_inputs[7] = {1'b0, {14'd2,3'd1, 7'd7}}; //write (tCCD)
            f_wb_inputs[8] = {1'b0, {14'd2,3'd1, 7'd8}}; //write on different bank (already activated but wrong row)
            f_wb_inputs[9] = {1'b0, {14'd2,3'd1, 7'd9}}; //write (tCCD)
            f_wb_inputs[10] = {1'b0, {14'd3,3'd1, 7'd10}}; //write (tCCD)
            f_wb_inputs[11] = {1'b0, {14'd3,3'd1, 7'd11}}; //read (same bank but wrong row so precharge first) 
            f_wb_inputs[12] = {1'b0, {14'd3,3'd1, 7'd12}}; //read (tCCD)
            f_wb_inputs[13] = {1'b0, {14'd3,3'd1, 7'd13}}; //read (tCCD)
            */

            f_wb_inputs[0] = {1'b0, {14'd0,3'd1, 7'd0}}; //read 
            f_wb_inputs[1] = {1'b0, {14'd0,3'd1, 7'd1}}; //read on same bank (tCCD)
            f_wb_inputs[2] = {1'b1, {14'd0,3'd1, 7'd2}}; //write on same bank (tRTW)
            f_wb_inputs[3] = {1'b1, {14'd0,3'd1, 7'd3}}; //write on same bank (tCCD)
            f_wb_inputs[4] = {1'b0, {14'd0,3'd2, 7'd0}}; //read on different bank 
            f_wb_inputs[5] = {1'b1, {14'd0,3'd2, 7'd1}}; //write on same bank (tRTW)
            f_wb_inputs[6] = {1'b1, {14'd0,3'd1, 7'd4}}; //write on different bank (already activated)
            f_wb_inputs[7] = {1'b1, {14'd0,3'd1, 7'd5}}; //write (tCCD)
            f_wb_inputs[8] = {1'b1, {14'd1,3'd2, 7'd0}}; //write on different bank (already activated but wrong row)
            f_wb_inputs[9] = {1'b1, {14'd1,3'd2, 7'd1}}; //write (tCCD)
            f_wb_inputs[10] = {1'b1, {14'd1,3'd2, 7'd2}}; //write (tCCD)
            f_wb_inputs[11] = {1'b0, {14'd2,3'd2, 7'd0}}; //read (same bank but wrong row so precharge first) 
            f_wb_inputs[12] = {1'b0, {14'd2,3'd2, 7'd1}}; //read (tCCD)
            f_wb_inputs[13] = {1'b0, {14'd2,3'd2, 7'd2}}; //read (tCCD)
            /*
            f_wb_inputs[0] = {1'b0, {14'd0,3'd1, 7'd0}}; //read 
            f_wb_inputs[1] = {1'b0, {14'd0,3'd1, 7'd1}}; //read on same bank (tCCD)
            f_wb_inputs[2] = {1'b1, {14'd0,3'd2, 7'd0}}; //write on the anticipated bank 
            f_wb_inputs[3] = {1'b1, {14'd0,3'd2, 7'd1}}; //write on same bank (tCCD)
            f_wb_inputs[4] = {1'b0, {14'd0,3'd3, 7'd0}}; //read on the anticipated bank 
            f_wb_inputs[5] = {1'b0, {14'd0,3'd3, 7'd1}}; //read on same bank (tCCD)
            f_wb_inputs[6] = {1'b1, {14'd0,3'd7, 7'd0}}; //write on the un-anticipated idle bank (activate first) 
            f_wb_inputs[7] = {1'b1, {14'd0,3'd1, 7'd1}}; //write on the un-anticipated active bank and row (write)
            f_wb_inputs[8] = {1'b1, {14'd1,3'd7, 7'd0}}; //write on the un-anticipated active bank but wrong row (precharge first) 
            */
            /*
            f_wb_inputs[0] = {1'b0, {14'd0,3'd1, 7'd0}}; //read 
            f_wb_inputs[1] = {1'b0, {14'd0,3'd1, 7'd1}}; //read 
            f_wb_inputs[2] = {1'b0, {14'd0,3'd1, 7'd2}}; //read 
            f_wb_inputs[3] = {1'b0, {14'd0,3'd1, 7'd3}}; //read 
            f_wb_inputs[4] = {1'b0, {14'd0,3'd1, 7'd4}}; //read 
            f_wb_inputs[5] = {1'b0, {14'd0,3'd1, 7'd5}}; //read 
            f_wb_inputs[6] = {1'b0, {14'd0,3'd1, 7'd6}}; //write 
            f_wb_inputs[7] = {1'b0, {14'd0,3'd1, 7'd7}}; //write 
            f_wb_inputs[8] = {1'b0, {14'd0,3'd1, 7'd8}}; //write 
            f_wb_inputs[9] = {1'b0, {14'd0,3'd1, 7'd9}}; //write 
            f_wb_inputs[10] = {1'b0, {14'd0,3'd1, 7'd10}}; //write 
            f_wb_inputs[11] = {1'b0, {14'd0,3'd1, 7'd11}}; //write 
            */
           /*
            f_wb_inputs[0] = {1'b0, {14'd1,3'd1, 7'd120}}; //write on same bank (tRTW)
            f_wb_inputs[1] = {1'b0, {14'd1,3'd1, 7'd121}}; //write on different bank (already activated)
            f_wb_inputs[2] = {1'b0, {14'd1,3'd1, 7'd122}}; //write (tCCD)
            f_wb_inputs[3] = {1'b0, {14'd1,3'd1, 7'd123}}; //write on different bank (already activated but wrong row)
            f_wb_inputs[4] = {1'b0, {14'd1,3'd1, 7'd124}}; //write (tCCD)
            f_wb_inputs[5] = {1'b0, {14'd1,3'd1, 7'd125}}; //write (tCCD)
            f_wb_inputs[6] = {1'b0, {14'd1,3'd1, 7'd126}}; //read (same bank but wrong row so precharge first) 
            f_wb_inputs[7] = {1'b0, {14'd1,3'd1, 7'd127}}; //read (tCCD)
            f_wb_inputs[8] = {1'b0, {14'd1,3'd2, 7'd0}}; //read (tCCD)
            f_wb_inputs[9] = {1'b0, {14'd1,3'd2, 7'd1}}; //read (tCCD)
            f_wb_inputs[10] = {1'b0, {14'd1,3'd2, 7'd2}}; //read (tCCD)
            */
        end
        initial begin
            f_reset_counter = 0;
        end
        always @(posedge i_controller_clk) begin
                if(!o_wb_stall) begin
                    f_index <= f_index + 1; //number of requests accepted
                end
                f_reset_counter <= f_reset_counter + 1;
        end
        
        always @(posedge i_controller_clk) begin
            assume(i_wb_cyc == 1);
            assume(i_wb_stb == 1);
            if(f_past_valid) begin
                assume(i_rst_n);
            end
            assume(i_wb_we == f_wb_inputs[f_index][24]);
            assume(i_wb_addr == f_wb_inputs[f_index][23:0]);
            cover(f_index == 10);
            if(f_index != 0) begin
                assume(i_rst_n); //dont reset just to skip a request forcefully
            end
        end
    `endif //endif for FORMAL_COVER


     `ifdef TEST_TIME_PARAMETERS
        // Test time parameter violations
        reg[6:0] f_precharge_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_activate_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_read_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_write_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_timer = 0;
        (*anyconst*) reg[2:0] bank_const;
        reg f_past_valid = 0;

        initial assume(!i_rst_n); 
        always @(posedge i_controller_clk)  f_past_valid <= 1;

        always @(posedge i_controller_clk) begin
            f_timer <= f_timer + 4;
            if(f_past_valid) begin
                assume($past(f_timer) < f_timer); //assume that counter will never overflow
            end
        end

        always @(posedge i_controller_clk, negedge i_rst_n) begin
            if(!i_rst_n) begin
                for(index=0; index < (1<<BA_BITS); index=index+1) begin
                    f_precharge_time_stamp[index] <= 0;
                    f_activate_time_stamp[index] <= 0;
                    f_read_time_stamp[index] <= 0;
                    f_write_time_stamp[index] <= 0;
                end
            end
            else begin
                //check if a DDR3 command is issued
                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0010) begin //PRECHARGE
                    f_precharge_time_stamp[cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + PRECHARGE_SLOT; 
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0011) begin //ACTIVATE
                    f_activate_time_stamp[cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + ACTIVATE_SLOT; 
                end

                if(cmd_d[WRITE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0100) begin //WRITE
                    f_write_time_stamp[cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + WRITE_SLOT;
                    //Check tCCD (write-to-write delay)
                    assert((f_timer+WRITE_SLOT) - f_write_time_stamp[bank_const] >= tCCD); 
                end

                if(cmd_d[READ_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0101) begin //READ
                    f_read_time_stamp[cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + READ_SLOT;
                    //Check tCCD (read-to-read delay)
                    assert((f_timer+READ_SLOT) - f_read_time_stamp[bank_const] >= tCCD); 
                end
            end
        end

        always @* begin
            // make sure saved time stamp is valid
            assert(f_precharge_time_stamp[bank_const] <= f_timer);
            assert(f_activate_time_stamp[bank_const] <= f_timer);
            assert(f_read_time_stamp[bank_const] <= f_timer);
            assert(f_write_time_stamp[bank_const] <= f_timer);
                
            // Check tRTP (Internal READ Command to PRECHARGE Command delay in SAME BANK)
            if(f_precharge_time_stamp[bank_const] > f_read_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_read_time_stamp[bank_const]) >= ns_to_nCK(10));
            end

            // Check tWTR (Delay from start of internal write transaction to internal read command)
            if(f_read_time_stamp[bank_const] > f_write_time_stamp[bank_const]) begin
                assert((f_read_time_stamp[bank_const] - f_write_time_stamp[bank_const]) >= (CWL_nCK + 3'd4 + ns_to_nCK(tWTR)));
            end

            // Check tRCD (ACT to internal read delay time)
            if(f_read_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_read_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ns_to_nCK(tRCD));
            end 
            
            // Check tRCD (ACT to internal write delay time)
            if(f_write_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_write_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ns_to_nCK(tRCD));
            end

            // Check tRP (PRE command period)
            if(f_activate_time_stamp[bank_const] > f_precharge_time_stamp[bank_const]) begin
                assert((f_activate_time_stamp[bank_const] - f_precharge_time_stamp[bank_const]) >= ns_to_nCK(tRP));
            end
            
            // Check tRAS (ACTIVE to PRECHARGE command period)
            if(f_precharge_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ns_to_nCK(tRAS));
            end

            // Check tWR (WRITE recovery time for write-to-precharge)
            if(f_precharge_time_stamp[bank_const] > f_write_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_write_time_stamp[bank_const]) >= (CWL_nCK + 3'd4 + ns_to_nCK(tWR)));
            end

            // Check delay from read-to-write
            if(f_write_time_stamp[bank_const] > f_read_time_stamp[bank_const]) begin
                assert((f_write_time_stamp[bank_const] - f_read_time_stamp[bank_const]) >= (CL_nCK + tCCD + 3'd2 - CWL_nCK));
            end

        end

        // extra assertions to make sure engine starts properly
        always @* begin
            assert(instruction_address <= 22);
            assert(state_calibrate <= DONE_CALIBRATE);

            if(!o_wb_stall) begin
                assert(state_calibrate == DONE_CALIBRATE);
                assert(instruction_address == 22 || (instruction_address == 19 && delay_counter == 0));
            end

            if(instruction_address == 19 && delay_counter != 0 && state_calibrate == DONE_CALIBRATE) begin
                if(stage1_pending || stage2_pending) begin
                    assert(pause_counter);
                end
            end

            if(stage1_pending || stage2_pending) begin
               assert(state_calibrate > ISSUE_WRITE_1); 
               assert(instruction_address == 22 || instruction_address == 19);
            end

            if(instruction_address < 13) begin
                assert(state_calibrate == IDLE);
            end

            if(state_calibrate > IDLE && state_calibrate <= BITSLIP_DQS_TRAIN_2) begin
                assert(instruction_address == 13);
                assert(pause_counter);
            end


            if(state_calibrate > START_WRITE_LEVEL  && state_calibrate <= WAIT_FOR_FEEDBACK) begin
                assert(instruction_address == 17);
                assert(pause_counter);
            end
            
            if(pause_counter) begin
                assert(delay_counter != 0);
            end
            
            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate < DONE_CALIBRATE) begin
                assume(instruction_address == 22); //write-then-read calibration will not take more than tREFI (7.8us, delay a address 22)
                assert(reset_done);
            end

            if(state_calibrate == DONE_CALIBRATE) begin
                assert(reset_done);
                assert(instruction_address >= 19);
            end

            if(reset_done) begin
                assert(instruction_address >= 19);
            end

            if(!reset_done) begin
                assert(!stage1_pending && !stage2_pending);
                assert(o_wb_stall);
            end
            if(reset_done) begin
                assert(instruction_address >= 19 && instruction_address <= 22);
            end
            //delay_counter is zero at first clock of new instruction address, the actual delay_clock wil start at next clock cycle 
            if(instruction_address == 19 && delay_counter != 0) begin
                assert(o_wb_stall);
            end

            if(instruction_address == 19 && pause_counter) begin //pre-stall delay to finish all remaining requests
               assert(delay_counter == PRE_REFRESH_DELAY); 
               assert(reset_done);
               assert(DONE_CALIBRATE);
            end
        end

        /*
        always @(posedge i_controller_clk) begin
            if(f_past_valid) begin
                if($past(instruction_address) == 22 && instruction_address == 19) begin
                    assert(state_calibrate == DONE_CALIBRATE);
                end
            end
        end
        */
    `endif //endif for TEST_TIME_PARAMETERS


    `ifdef TEST_CONTROLLER_PIPELINE 
        // wires and registers used in this formal section
        `ifdef TEST_DATA
            localparam F_TEST_CMD_DATA_WIDTH = $bits(i_wb_data) + $bits(i_wb_sel) + $bits(i_aux) + $bits(i_wb_addr) + $bits(i_wb_we);
        `else
            localparam F_TEST_CMD_DATA_WIDTH = $bits(i_wb_addr) + $bits(i_wb_we);
        `endif
        localparam F_MAX_STALL = max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY) + 1 + PRECHARGE_TO_ACTIVATE_DELAY + 1 + max(ACTIVATE_TO_WRITE_DELAY,ACTIVATE_TO_READ_DELAY) + 1 ;
                                    //worst case delay (Precharge -> Activate-> R/W)
                                    //add 1 to each delay since they end at zero
        localparam F_MAX_ACK_DELAY = F_MAX_STALL + (READ_ACK_PIPE_WIDTH + 2); //max_stall + size of shift_reg_read_pipe_q + o_wb_ack_read_q (assume to be two via read_pipe_max) 

        (*keep*) wire[3:0] f_max_stall, f_max_ack_delay;
        assign f_max_stall = F_MAX_STALL;
        assign f_max_ack_delay = F_MAX_ACK_DELAY;

        reg f_past_valid = 0; 
        reg[$bits(instruction_address) - 1: 0] f_addr = 0, f_read = 0 ; 
        reg[$bits(instruction) - 1:0] f_read_inst = INITIAL_RESET_INSTRUCTION;
        reg[3:0] f_count_refreshes = 0; //count how many refresh cycles had already passed
        reg[24:0] f_wb_inputs[31:0];
        reg[4:0] f_index = 0;
        reg[5:0] f_counter = 0;

        reg[4:0] f_index_1 = 0;
        reg[4:0] f_index_2 = 0;
        reg[F_TEST_CMD_DATA_WIDTH - 1:0] f_write_data;
        reg f_write_fifo = 0, f_read_fifo = 0;
        reg[ROW_BITS-1:0] f_bank_active_row[(1<<BA_BITS)-1:0]; 
        reg[(1<<BA_BITS)-1:0] f_bank_status;
        (*keep*) reg[(1<<BA_BITS)-1:0] f_bank_status_2; 
        wire f_empty, f_full;
        wire[F_TEST_CMD_DATA_WIDTH - 1:0] f_read_data;
        wire[F_TEST_CMD_DATA_WIDTH - 1:0] f_read_data_next;

        wire[$bits(instruction) - 1:0]  a= read_rom_instruction(f_const_addr); //retrieve an instruction based on engine's choice
        wire[1:0] f_write_slot;
        wire[1:0] f_read_slot;
        wire[1:0] f_precharge_slot;
        wire[1:0] f_activate_slot;
        (*anyconst*) reg[$bits(instruction_address) - 1: 0] f_const_addr;
        
        initial assume(!i_rst_n); 
        
        always @* begin
            //assert(tMOD + tZQinit > nCK_to_cycles(tDLLK)); //Initialization sequence requires that tDLLK is satisfied after MRS to mode register 0 and ZQ calibration
            assert(MR0[18] != 1'b1); //last Mode Register bit should never be zero 
            assert(MR1_WL_EN[18] != 1'b1); //(as this is used for A10-AP control for non-MRS 
            assert(MR1_WL_DIS[18] != 1'b1); //(as this is used for A10-AP control for non-MRS 
            assert(MR2[18] != 1'b1); //commands in the reset sequence)
            assert(MR3_MPR_EN[18] != 1'b1);
            assert(MR3_MPR_DIS[18] != 1'b1);
            assert(DELAY_COUNTER_WIDTH <= $bits(MR0)); //bitwidth of mode register should be enough for the delay counter
            //sanity checking to ensure 5 bits is allotted for extra instruction {reset_finished, use_timer , stay_command , cke , reset_n } 
            assert(($bits(instruction) - $bits(CMD_MRS) - $bits(MR0)) == 5 ); 
            assert(DELAY_SLOT_WIDTH >= DELAY_COUNTER_WIDTH); //width occupied by delay timer slot on the reset rom must be able to occupy the maximum possible delay value on the reset sequence
        end
        
        always @(posedge i_controller_clk)  f_past_valid <= 1;
        
        
        //The idea below is sourced from https://zipcpu.com/formal/2019/11/18/genuctrlr.html
        //We will form a packet of information describing each instruction as it goes through the pipeline and make assertions along the way.
        //2-stage Pipeline: f_addr (update address)  ->  f_read (read instruction from rom)  
        
        //pipeline stage logic: f_addr (update address)  ->  f_read (read instruction from rom)  
        always @(posedge i_controller_clk, negedge i_rst_n) begin
            if(!i_rst_n) begin
                f_addr <= 0;
                f_read <= 0;
            end
            //move the pipeline forward when counter is about to go zero and we are not yet at end of reset sequence
            else if((delay_counter == 1 || !instruction[USE_TIMER])) begin             
                f_addr <= (f_addr == 22)? 19:f_addr + 1;
                f_read <= f_addr;
            end     
        end
        
        // assert f_addr and f_read as shadows of next and current instruction address 
        always @* begin
            assert(f_addr == instruction_address); //f_addr is the shadow of instruction_address (thus f_addr is the address of NEXT instruction)
            f_read_inst = read_rom_instruction(f_read); //f_read is the address of CURRENT instruction 
            assert(f_read_inst == read_rom_instruction(f_read)); // needed for induction to make sure the engine will not create his own instruction
        if(f_addr == 0) begin
            f_read_inst = INITIAL_RESET_INSTRUCTION; //will only happen at the very start:  f_addr (0)  ->  f_read (0)  where we are reading the initial reset instruction and not the rom
        end
        assert(f_read_inst == instruction);  // f_read_inst is the shadow of current instruction 
        end
        
        // main assertions for the reset sequence 
        always @(posedge i_controller_clk) begin
                if(!i_rst_n || !$past(i_rst_n)) begin
                    assert(f_addr == 0);
                    assert(f_read == 0);
                    assert(instruction_address == 0);
                    assert(delay_counter == (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]));
                    assert(delay_counter_is_zero == (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0));
                end
                else if(f_past_valid) begin
                    //if counter is zero previously and current instruction needs timer delay, then this cycle should now have the new updated counter value
                    if( $past(delay_counter_is_zero) && $past(f_read_inst[USE_TIMER]) ) begin 
                            assert(delay_counter == f_read_inst[DELAY_COUNTER_WIDTH - 1:0]); 
                    end
                     //delay_counter_is_zero can be high when counter is zero and current instruction needs delay
                     if($past(f_read_inst[USE_TIMER]) && !$past(pause_counter) ) begin
                         assert( delay_counter_is_zero  == (delay_counter == 0) ); 
                     end
                     //delay_counter_is_zero will go high this cycle when we received a don't-use-timer instruction
                     else if(!$past(f_read_inst[USE_TIMER]) && !$past(pause_counter)) begin
                         assert(delay_counter_is_zero); 
                     end
                    
                    //we are on the middle of a delay thus all values must remain constant while only delay_counter changes (decrement)
                    if(!delay_counter_is_zero) begin 
                        assert(f_addr == $past(f_addr));
                        assert(f_read == $past(f_read));
                        assert(f_read_inst == $past(f_read_inst));
                    end
                    
                    //if delay is not yet zero and timer delay is enabled, then delay_counter should decrement
                    if(!$past(delay_counter_is_zero) && $past(f_read_inst[USE_TIMER]) && !$past(pause_counter) ) begin
                        assert(delay_counter == $past(delay_counter) - 1); 
                        assert(delay_counter < $past(delay_counter) ); //just to make sure delay_counter will never overflow back to all 1's
                    end
                    
                    //sanity checking for the comment "delay_counter will be zero AT NEXT CLOCK CYCLE when counter is now one"
                if($past(delay_counter) == 1) begin
                    assert(delay_counter == 0 && delay_counter_is_zero); 
                end
                //assert the relationship between the stages FOR RESET SEQUENCE
                if(!reset_done) begin
                    if(f_addr == 0) begin
                        assert(f_read == 0); //will only happen at the very start:  f_addr (0)  ->  f_read (0)  
                    end
                    else if(f_read == 0) begin 
                        assert(f_addr <= 1); //will only happen at the very first two cycles: f_addr (1)  ->  f_read (0) or f_addr (0)  ->  f_read (0)  
                    end
                    //else if($past(reset_done)) assert(f_read == $past(f_read)); //reset instruction does not repeat after reaching end address thus it must saturate when pipeline reaches end
                    else begin
                        assert(f_read + 1 == f_addr); //address increments continuously
                    end
                    assert($past(f_read) < 21); //only instruction address 0-to-13 is for reset sequence (reset_done is asserted at address 14)
                end
                        
                //assert the relationship between the stages FOR REFRESH SEQUENCE
                else begin
                    if(f_read == 22) begin
                        assert(f_addr == 19); //if current instruction is 22, then next instruction must be at 19 (instruction address wraps from 15 to 12)
                    end
                    else if(f_addr == 19) begin
                        assert(f_read == 22); //if next instruction is at 12, then current instruction must be at 15 (instruction address wraps from 15 to 12)
                    end
                    else begin
                        assert(f_read + 1 == f_addr); //if there is no need to wrap around, then instruction address must increment 
                    end
                    assert((f_read >= 19 && f_read <= 22) ); //refresh sequence is only on instruction address 19,20,21,22
                end
                
                // reset_done must retain high when it was already asserted once
                if($past(reset_done)) begin
                    assert(reset_done);
                end
                
                // reset is already done at address 21 and up
                if($past(f_read) >= 21 ) begin
                    assert(reset_done);
                end
                
                //if reset is done, the REF_IDLE must only be high at instruction address 14 (on the middle of tREFI)
                if(reset_done &&  f_read_inst[REF_IDLE]) begin
                    assert(f_read == 21);
                end
                        
            end

        end
        
        
        // assertions on the instructions stored on the rom
        always @* begin
             //there MUST BE no instruction which USE_TIMER is high but delay is zero since it can cause the logic to lock-up (delay must be at least 1)    
            if(a[USE_TIMER]) begin
                assert( a[DELAY_COUNTER_WIDTH - 1:0] > 0);      
            end
        end
        
        // assertion on FSM calibration
        always @* begin
            if(instruction_address < 13) begin
                assert(state_calibrate == IDLE);
            end

            if(state_calibrate > IDLE && state_calibrate <= BITSLIP_DQS_TRAIN_2) begin
                assert(instruction_address == 13);
                assert(pause_counter);
            end


            if(state_calibrate > START_WRITE_LEVEL  && state_calibrate <= WAIT_FOR_FEEDBACK) begin
                assert(instruction_address == 17);
                assert(pause_counter);
            end
            
            if(pause_counter) begin
                assert(delay_counter != 0);
            end
            
            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate < DONE_CALIBRATE) begin
                assume(instruction_address == 22); //write-then-read calibration will not take more than tREFI (7.8us, delay a address 22)
                assert(reset_done);
            end

            if(state_calibrate == DONE_CALIBRATE) begin
                assert(reset_done);
                assert(instruction_address >= 19);
            end

            if(reset_done) begin
                assert(instruction_address >= 19);
            end
        end
        
        always @* begin
            //make sure each command has distinct slot number (except for read/write which can have the same or different slot number)
            //assert((WRITE_SLOT != ACTIVATE_SLOT != PRECHARGE_SLOT) && (READ_SLOT != ACTIVATE_SLOT != PRECHARGE_SLOT) );
            assert(WRITE_SLOT != ACTIVATE_SLOT);
            assert(WRITE_SLOT != PRECHARGE_SLOT);
            assert(READ_SLOT != ACTIVATE_SLOT);
            assert(READ_SLOT != PRECHARGE_SLOT);
            //make sure slot number for read command is correct
        end
        //create a formal assertion that says during refresh ack should be low always
        //make an assertion that there will be no request pending before actual refresh starts at instruction 4'd12
            

        mini_fifo #(
            .FIFO_WIDTH(1), //the fifo will have 2**FIFO_WIDTH positions
            .DATA_WIDTH(F_TEST_CMD_DATA_WIDTH) //each FIFO position can store DATA_WIDTH bits
       ) fifo_1 (
            .i_clk(i_controller_clk), 
            .i_rst_n(i_rst_n && i_wb_cyc), //reset outstanding request at reset or when cyc goes low
            .read_fifo(f_read_fifo), 
            .write_fifo(f_write_fifo),
            .empty(f_empty), 
            .full(f_full),
            .write_data(f_write_data),
            .read_data(f_read_data),
            .read_data_next(f_read_data_next)
       ); 

        always @* begin
            if(state_calibrate == DONE_CALIBRATE && i_wb_cyc) begin
                if(f_full) begin
                    assert(stage1_pending && stage2_pending);//there are 2 contents
                end
                if(stage1_pending && stage2_pending) begin
                    assert(f_full);
                end

                if(!f_empty && !f_full) begin
                    assert(stage1_pending ^ stage2_pending);//there is 1 content
                end
                if(stage1_pending ^ stage2_pending) begin
                    assert(!f_empty && !f_full);
                end

                if(f_empty) begin
                    assert(stage1_pending == 0 && stage2_pending==0); //there is 0 content
                end
                if(stage1_pending == 0 && stage2_pending == 0) begin
                    assert(f_empty);
                end
            end

            if(state_calibrate < ISSUE_WRITE_1) begin
                assert(!stage1_pending && !stage2_pending);
            end
            if(stage1_pending && state_calibrate == ISSUE_READ) begin
                assert(stage1_we);
            end
            if(stage2_pending && state_calibrate == ISSUE_READ) begin
                assert(stage2_we);
            end
            if(state_calibrate == ANALYZE_DATA) begin
                assert(!stage1_pending && !stage2_pending);
            end
        end

        always @(posedge i_controller_clk) begin
            if(f_past_valid) begin
                //switch from calibrate to done
                if(state_calibrate == DONE_CALIBRATE && $past(state_calibrate) != DONE_CALIBRATE) begin
                    assert($past(state_calibrate) == ANALYZE_DATA);
                    assert(f_empty);
                    assert(!stage1_pending);
                    assert(!stage2_pending);
                    //assert(f_bank_status == 1); //only first bank is activated
                    //assert(bank_status_q == 1);
                end
                if(stage1_pending && $past(state_calibrate) == READ_DATA && state_calibrate == READ_DATA) begin
                    assert(!stage1_we);
                end
                //if(instruction_address == 21 || ($past(instruction_address) == 20 && $past(instruction_address,2) == 19) || instruction_address < 19) begin //calibration
               //    assert(f_bank_status == 0);
               //    assert(bank_status_q == 0);
               // end
               if(!reset_done) begin
                    assert(f_bank_status == 0);
                    assert(bank_status_q == 0);
               end
               if(state_calibrate != DONE_CALIBRATE) begin
                    assert(f_bank_status == 0 || f_bank_status == 1); //only first bank is activated
                    assert(bank_status_q == 0 || f_bank_status == 1);
               end
            end
        end

        //wishbone request should have a corresponding DDR3 command at the output
        //wishbone request will be written to fifo, then once a DDR3 command is
        //issued the fifo will be read to check if the DDR3 command matches the
        //corresponding wishbone request
        reg[ROW_BITS-1:0] f_read_data_col;
        reg[BA_BITS-1:0] f_read_data_bank;
        reg[AUX_WIDTH-1:0] f_read_data_aux;
        reg[wb_sel_bits-1:0] f_read_data_wb_sel;
        always @* begin
            //write the wb request to fifo
            if(i_wb_stb && i_wb_cyc && !o_wb_stall && state_calibrate == DONE_CALIBRATE) begin
                f_write_fifo = 1;
                `ifdef TEST_DATA
                    f_write_data = {i_wb_data, i_wb_sel, i_aux, i_wb_addr,i_wb_we};
                `else
                    f_write_data = {i_wb_addr,i_wb_we};
                `endif
            end 
            else begin
                f_write_fifo = 0;
            end
            f_read_fifo = 0;
            //check if a DDR3 command is issued
            if(i_wb_cyc) begin //only if already done calibrate and controller can accept wb request 

                if(cmd_d[WRITE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0100) begin //WRITE
                    if(state_calibrate == DONE_CALIBRATE) begin
                       assert(f_bank_status[cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == 1'b1); //the bank that will be written must initially be active 
                       f_read_data_col = {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}; //column address must match 
                       assert(cmd_d[WRITE_SLOT][CMD_ADDRESS_START:0] == f_read_data_col);

                       f_read_data_bank = f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]; //bank must match 
                       assert(cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1] == f_read_data_bank);

                       `ifdef TEST_DATA
                           f_read_data_aux = f_read_data[$bits(i_wb_addr) + 1 +: AUX_WIDTH]; //UAX ID must match 
                           assert(stage2_aux == f_read_data_aux);

                           f_read_data_wb_sel = (f_read_data[$bits(i_wb_addr) + AUX_WIDTH + 1 +: $bits(i_wb_sel)]); 
                           assert(stage2_dm_unaligned == ~f_read_data_wb_sel); //data mask mst match inverse of wb sel
                           assert(stage2_data_unaligned == f_read_data[$bits(i_wb_sel) + $bits(i_wb_addr) + AUX_WIDTH + 1 +: $bits(i_wb_data)]); //actual data must match 
                       `endif

                       assert(f_read_data[0]); //i_wb_we must be high
                       f_read_fifo = 1; //advance read pointer to prepare for next read
                    end
                    else if(state_calibrate > ISSUE_WRITE_1) begin
                        assert(stage2_aux == 1);
                    end
                    //assert(f_bank_active_row[cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == current_row); //column to be written must be the current active row
                end

                if(cmd_d[READ_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0101) begin //READ
                   if(state_calibrate == DONE_CALIBRATE) begin
                       assert(f_bank_status[cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == 1'b1); //the bank that will be read must initially be active 
                       f_read_data_col = {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}; //column address must match 
                       assert(cmd_d[READ_SLOT][CMD_ADDRESS_START:0] == f_read_data_col);

                       f_read_data_bank = f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]; //bank must match 
                       assert(cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1] == f_read_data_bank);

                       `ifdef TEST_DATA
                           f_read_data_aux = f_read_data[$bits(i_wb_addr) + 1 +: AUX_WIDTH]; //UAX ID must match 
                           assert(stage2_aux == f_read_data_aux);
                       `endif

                       assert(!f_read_data[0]); //i_wb_we must be low
                       f_read_fifo = 1; //advance read pointer to prepare for next read
                   end
                    else if(state_calibrate > ISSUE_WRITE_1) begin
                        assert(stage2_aux == 0);
                    end
                    //assert(f_bank_active_row[cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == current_row);//column to be written must be the current active row
                end

                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0010) begin //PRECHARGE
                   if(state_calibrate == DONE_CALIBRATE && (instruction_address == 22 || instruction_address == 19)) begin
                        assert(f_bank_status[cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == 1'b1); //the bank that should be precharged must initially be active 
                   end
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0011) begin //ACTIVATE
                   if(state_calibrate == DONE_CALIBRATE) begin
                       assert(f_bank_status[cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == 1'b0); //the bank that should be activated must initially be precharged 
                   end
                end

                if(reset_done) begin
                    assert(cmd_d[PRECHARGE_SLOT][CMD_CKE] && cmd_d[PRECHARGE_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                    assert(cmd_d[ACTIVATE_SLOT][CMD_CKE] && cmd_d[ACTIVATE_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                    assert(cmd_d[READ_SLOT][CMD_CKE] && cmd_d[READ_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                    assert(cmd_d[WRITE_SLOT][CMD_CKE] && cmd_d[WRITE_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                end
            end
            if(state_calibrate == DONE_CALIBRATE) begin
                assert(reset_done);
            end
            if(state_calibrate != DONE_CALIBRATE) begin
                assert(o_wb_stall); //if not yet finished calibrating, stall should never go low
            end
            if(state_calibrate != DONE_CALIBRATE) begin
                assert(f_empty); //if not yet finished calibrating, stall should never go low
            end
            if(!f_empty) begin
                assert(state_calibrate == DONE_CALIBRATE);
            end
        end

    //`ifdef UNDER_CONSTRUCTION
        //make assertions on what is inside the fifo
        always @* begin
            if(!f_empty && !f_full) begin //make assertion when there is only 1 data on the pipe
                if(stage1_pending) begin //request is still on stage1
                    assert(stage1_bank == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                    assert(stage1_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    assert(stage1_we == f_read_data[0]); //i_wb_we must be high
                end
                if(stage2_pending) begin //request is now on stage2
                    assert(stage2_bank == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                    assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    assert(stage2_we == f_read_data[0]); //i_wb_we must be high
                end
            end
            if(f_full) begin //both stages have request
                //stage2 is the request on the tip of the fifo
                assert(stage2_bank == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                assert(stage2_we == f_read_data[0]); //i_wb_we must be high
                //stage1 is the request on the other element of the fifo
                //(since the fifo only has 2 elements, the other element that
                //is not the tip will surely be the 2nd request that is being
                //handles by stage1)
                assert(stage1_bank == f_read_data_next[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                assert(stage1_col == {f_read_data_next[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                assert(stage1_we == f_read_data_next[0]); //i_wb_we must be high
            end
        end
        
    //`endif

        always @* begin
            assert(f_bank_status == bank_status_q);
        end
       
        (*keep*) reg[31:0] bank; 
        always @(posedge i_controller_clk, negedge i_rst_n) begin
            if(!i_rst_n) begin
                //reset bank status and active row
                for(index=0; index < (1<<BA_BITS); index=index+1) begin
                        f_bank_status[index] <= 0;  
                        f_bank_status_2[index] = 0;  
                        f_bank_active_row[index] <= 0; 
                end
            end
            else begin
                //check if a DDR3 command is issued
                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0010) begin //PRECHARGE
                    bank = cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1];
                    if(cmd_d[PRECHARGE_SLOT][10]) begin //A10 precharge all banks
                        for(index=0; index < (1<<BA_BITS); index=index+1) begin
                                f_bank_status_2[index] = 0;  
                        end
                    end
                    else begin
                        //f_bank_status <= f_bank_status & ~(1<<bank); //set to zero to idle bank
                        //f_bank_status[bank] <= 0; //set to zero to idle bank
                        f_bank_status_2 = f_bank_status_2 & ~(1<<bank); //set to zero to idle bank
                    end
                    assert(bank <= 7);
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0011) begin //ACTIVATE
                    bank = cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1];
                   // f_bank_status <= f_bank_status | (1<<bank); //bank will be turned active
                    //f_bank_status[bank] <= 1;
                    assert(bank <= 7);
                    f_bank_status_2 = f_bank_status_2 | (1<<bank); //bank will be turned active
                    f_bank_active_row[bank] <= cmd_d[ACTIVATE_SLOT][CMD_ADDRESS_START:0]; //save row to be activated 
                end
                f_bank_status <= f_bank_status_2;

            end
        end

        assign f_write_slot = WRITE_SLOT;
        assign f_read_slot = READ_SLOT;
        assign f_precharge_slot = PRECHARGE_SLOT;
        assign f_activate_slot = ACTIVATE_SLOT;

        always @(posedge i_controller_clk) begin
            if(!f_empty) begin//there is an ongoing wb request
                assert(stage1_pending || stage2_pending);
            end
            if((stage1_pending || stage2_pending) && state_calibrate == DONE_CALIBRATE && i_wb_cyc) begin
                assert(!f_empty || f_write_fifo);
            end
        end
        always @(posedge i_controller_clk) begin
                if(f_past_valid) begin
                    if(instruction_address != 22 && $past(instruction_address) != 22) begin
                        assert(!f_write_fifo); //must have no new request when not inside tREFI 
                    end
                    if(instruction_address != 22 && $past(instruction_address) != 22) begin
                        assert(o_wb_stall);
                    end
                    //delay_counter is zero at first clock of new instruction address, the actual delay_clock wil start at next clock cycle 
                    if(instruction_address == 19 && delay_counter != 0) begin
                        assert(o_wb_stall);
                    end
                    if(instruction_address == 20 || instruction_address == 21) begin //no pending request at precharge all and refresh command
                        assert(!stage1_pending);
                        assert(!stage2_pending);
                    end
                    if($past(o_wb_stall_q) && stage1_pending) begin //if pipe did not move forward
                       assert(stage1_we == $past(stage1_we));
                       assert(stage1_aux == $past(stage1_aux));
                       assert(stage1_bank == $past(stage1_bank));
                       assert(stage1_col == $past(stage1_col));
                       assert(stage1_row == $past(stage1_row));
                       assert(stage1_dm == $past(stage1_dm));
                    end
                end
        end
        
        always @* begin
            if(instruction_address != 22 && instruction_address != 19) begin
               assert(!stage1_pending && !stage2_pending); //must be pending except in tREFI and in prestall delay
            end

            if(!reset_done) begin 
                assert(stage1_pending == 0 && stage2_pending == 0);
            end

            if(state_calibrate <= ISSUE_READ) begin
                for(index = 0; index < 1; index = index + 1) begin
                    assert(o_wb_ack_read_q[index] == 0);
                end
                for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                    assert(shift_reg_read_pipe_q[index] == 0);
                end
            end

            if( state_calibrate < ISSUE_WRITE_1 ) begin
                assert(bank_status_q == 0);
            end

            if(!DONE_CALIBRATE) begin
                assert(o_wb_ack == 0); //o_wb_ack must not go high before done calibration
            end

            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate < DONE_CALIBRATE) begin
                if(stage1_pending) begin
                    assert(stage1_we == stage1_aux); //if write, then aux id must be 1 else 0
                end
                if(stage2_pending) begin
                    assert(stage2_we == stage2_aux); //if write, then aux id must be 1 else 0
                end
            end

            assert(state_calibrate <= DONE_CALIBRATE);
        end
        
        
        wire[3:0] f_nreqs, f_nacks, f_outstanding, f_ackwait_count, f_stall_count;
        wire[3:0] f_nreqs_2, f_nacks_2, f_outstanding_2;
        reg[READ_ACK_PIPE_WIDTH+1:0] f_ack_pipe_after_stage2;
        reg[AUX_WIDTH:0] f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH+1:0];
        integer f_ack_pipe_marker;

        integer f_sum_of_pending_acks = 0;
        always @* begin
                if(!i_rst_n) begin
                    assume(f_nreqs == 0);
                    assume(f_nacks == 0);
                end

                if(state_calibrate != IDLE) assume(added_read_pipe_max == 1);
                f_sum_of_pending_acks = stage1_pending + stage2_pending;
                for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                    f_sum_of_pending_acks = f_sum_of_pending_acks + shift_reg_read_pipe_q[index][0] + 0;
                end
                for(index = 0; index < 2; index = index + 1) begin //since added_read_pipe_max is assumed to be one, only the first two bits of o_wb_ack_read_q is relevant
                    f_sum_of_pending_acks = f_sum_of_pending_acks + o_wb_ack_read_q[index][0] + 0;
                end
                
                //the remaining o_wb_ack_read_q (>2) should stay zero at
                //all instance
                for(index = 2; index < MAX_ADDED_READ_ACK_DELAY ; index = index + 1) begin
                    assert(o_wb_ack_read_q[index] == 0);
                end
                f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH+1] = o_wb_ack_read_q[0]; //last stage of f_aux_ack_pipe_after_stage2 is also the last ack stage
                f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH] = o_wb_ack_read_q[1];
                for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                    f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH - 1 - index] = shift_reg_read_pipe_q[index];
                end
                f_ack_pipe_after_stage2 = {
                    o_wb_ack_read_q[0][0], 
                    o_wb_ack_read_q[1][0], 
                    shift_reg_read_pipe_q[0][0], 
                    shift_reg_read_pipe_q[1][0],
                    shift_reg_read_pipe_q[2][0],
                    shift_reg_read_pipe_q[3][0],
                    shift_reg_read_pipe_q[4][0]
                    };

                if(f_ackwait_count > F_MAX_STALL) begin
                    assert(|f_ack_pipe_after_stage2[(READ_ACK_PIPE_WIDTH+1) : (f_ackwait_count - F_MAX_STALL - 1)]); //at least one stage must be high
                end


                if(i_rst_n && state_calibrate == DONE_CALIBRATE) begin
                    assert(f_outstanding == f_sum_of_pending_acks || !i_wb_cyc);
                end
                else if(!i_rst_n) begin
                    assert(f_sum_of_pending_acks == 0);
                end
                if(state_calibrate != DONE_CALIBRATE && i_rst_n) begin
                    assert(f_outstanding == 0 || !i_wb_cyc);
                end
                if(state_calibrate <= ISSUE_WRITE_1 && i_rst_n) begin
                    //not inside tREFI, prestall delay, nor precharge
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                    assert(f_sum_of_pending_acks == 0);
                end
                if(state_calibrate == READ_DATA && i_rst_n) begin
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                    assert(f_sum_of_pending_acks <= 3);

                    if((f_sum_of_pending_acks > 1) && o_wb_ack_read_q[0]) begin
                        assert(o_wb_ack_read_q[0] == {1, 1'b1});
                    end

                    f_ack_pipe_marker = 0;
                    for(index = 0; index < READ_ACK_PIPE_WIDTH + 2; index = index + 1) begin //check each ack stage starting from last stage
                        if(f_aux_ack_pipe_after_stage2[index][0]) begin //if ack is high
                            if(f_aux_ack_pipe_after_stage2[index][AUX_WIDTH:1] == 0) begin //ack for read
                                assert(f_ack_pipe_marker == 0); //read ack must be the last ack on the pipe(f_pipe_marker must still be zero)
                                f_ack_pipe_marker = f_ack_pipe_marker + 1;
                                assert(!stage1_pending && !stage2_pending); //a single read request must be the last request on this calibration
                            end
                            else begin //ack for write
                                assert(f_aux_ack_pipe_after_stage2[index][AUX_WIDTH:1] == 1);
                                f_ack_pipe_marker = f_ack_pipe_marker + 1;
                            end
                        end
                    end
                    assert(f_ack_pipe_marker <= 3);
                end

                if(state_calibrate == ANALYZE_DATA && i_rst_n) begin
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                    assert(f_sum_of_pending_acks == 0);
                end
                if(state_calibrate != DONE_CALIBRATE  && i_rst_n) begin //if not yet done calibration, no request should be accepted
                    assert(f_nreqs == 0);
                    assert(f_nacks == 0);
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                end

               if(state_calibrate == ISSUE_WRITE_2 || state_calibrate == ISSUE_READ) begin
                   if(write_calib_stb == 1) begin
                        assert(write_calib_aux == 1);          
                        assert(write_calib_we == 1);
                    end
               end
                if(!stage1_pending) begin
                    assert(!stage1_stall);
                end

                if(!stage2_pending) begin
                    assert(!stage2_stall);
                end
        end
        always @(posedge i_controller_clk) begin
            if(f_past_valid) begin
                if(instruction_address != 22 && instruction_address != 19 && $past(i_wb_cyc) && i_rst_n) begin
                   assert(f_nreqs == $past(f_nreqs));           
                end
                if(state_calibrate == DONE_CALIBRATE && $past(state_calibrate) != DONE_CALIBRATE && i_rst_n) begin//just started DONE_CALBRATION
                    assert(f_nreqs == 0);
                    assert(f_nacks == 0);
                    assert(f_outstanding == 0); 
                    assert(f_sum_of_pending_acks == 0);
                end
                if((!stage1_pending || !stage2_pending) && $past(state_calibrate) == DONE_CALIBRATE && state_calibrate == DONE_CALIBRATE 
                    && instruction_address == 22 && $past(instruction_address == 22)) begin
                        assert(!o_wb_stall);//if even 1 of the stage is empty, o_wb_stall must be low
                end
            end
        end

        //test the delay_before*
        always @* begin 
            for(index=0; index< (1<<BA_BITS); index=index+1) begin
                assert(delay_before_precharge_counter_q[index] <= max(ACTIVATE_TO_PRECHARGE_DELAY, max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY)));
                assert(delay_before_activate_counter_q[index] <= PRECHARGE_TO_ACTIVATE_DELAY); 
                assert(delay_before_write_counter_q[index] <= max(READ_TO_WRITE_DELAY,ACTIVATE_TO_WRITE_DELAY));
                assert(delay_before_read_counter_q[index] <= max(WRITE_TO_READ_DELAY,ACTIVATE_TO_READ_DELAY));
            end
            if(stage2_pending) begin
                if(delay_before_precharge_counter_q[stage2_bank] == max(ACTIVATE_TO_PRECHARGE_DELAY, max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY))) begin
                  assert(f_stall_count == 0);
                  //assert(f_ackwait_count == 0);
                end
                if(delay_before_activate_counter_q[stage2_bank] == PRECHARGE_TO_ACTIVATE_DELAY && !bank_status_q[stage2_bank]) begin
                  assert(f_stall_count <= (max(ACTIVATE_TO_PRECHARGE_DELAY, max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY)) + 1));
                  //assert(f_ackwait_count <= (max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY) + 2));
                end

                //if there is still no pending ack 
                if(!(|f_ack_pipe_after_stage2)) begin
                    //At f_ackwait_count == F_MAX_STALL, the
                    //r/w command must be issued already (or stage2_update is high) 
                    if(stage2_update) begin
                        assert(f_ackwait_count <= F_MAX_STALL);
                    end
                    if(delay_before_precharge_counter_q[stage2_bank] == max(ACTIVATE_TO_PRECHARGE_DELAY, max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY))) begin
                      assert(f_ackwait_count == 0);
                    end
                    if(delay_before_activate_counter_q[stage2_bank] == PRECHARGE_TO_ACTIVATE_DELAY && !bank_status_q[stage2_bank]) begin
                      assert(f_ackwait_count <= (max(ACTIVATE_TO_PRECHARGE_DELAY, max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY)) + 1));
                    end

                    /*
                      for(index = 0; index <= PRECHARGE_TO_ACTIVATE_DELAY; index= index +1 ) begin
                        if(delay_before_activate_counter_q[stage2_bank] == PRECHARGE_TO_ACTIVATE_DELAY - index) begin
                            assert(f_ackwait_count <= (max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY) + 1 + index));
                        end
                      end
                      */
                end
            end
        end


        // Test time parameter violations
        reg[6:0] f_precharge_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_activate_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_read_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_write_time_stamp[(1<<BA_BITS)-1:0]; 
        reg[6:0] f_timer = 0;
        (*anyconst*) reg[2:0] bank_const;


        always @(posedge i_controller_clk) begin
            f_timer <= f_timer + 4;
            if(f_past_valid) begin
                assume($past(f_timer) < f_timer); //assume that counter will never overflow
            end
        end

        always @(posedge i_controller_clk, negedge i_rst_n) begin
            if(!i_rst_n) begin
                for(index=0; index < (1<<BA_BITS); index=index+1) begin
                    f_precharge_time_stamp[index] <= 0;
                    f_activate_time_stamp[index] <= 0;
                    f_read_time_stamp[index] <= 0;
                    f_write_time_stamp[index] <= 0;
                end
            end
            else begin
                //check if a DDR3 command is issued
                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0010) begin //PRECHARGE
                    f_precharge_time_stamp[cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + PRECHARGE_SLOT; 
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0011) begin //ACTIVATE
                    f_activate_time_stamp[cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + ACTIVATE_SLOT; 
                end

                if(cmd_d[WRITE_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0100) begin //WRITE
                    f_write_time_stamp[cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + WRITE_SLOT;
                    //Check tCCD (write-to-write delay)
                    assert((f_timer+WRITE_SLOT) - f_write_time_stamp[bank_const] >= tCCD); 
                end

                if(cmd_d[READ_SLOT][CMD_CS_N:CMD_WE_N] == 4'b0101) begin //READ
                    f_read_time_stamp[cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] <= f_timer + READ_SLOT;
                    //Check tCCD (read-to-read delay)
                    assert((f_timer+READ_SLOT) - f_read_time_stamp[bank_const] >= tCCD); 
                end
            end
        end

        always @* begin
            // make sure saved time stamp is valid
            assert(f_precharge_time_stamp[bank_const] <= f_timer);
            assert(f_activate_time_stamp[bank_const] <= f_timer);
            assert(f_read_time_stamp[bank_const] <= f_timer);
            assert(f_write_time_stamp[bank_const] <= f_timer);
                
            // Check tRTP (Internal READ Command to PRECHARGE Command delay in SAME BANK)
            if(f_precharge_time_stamp[bank_const] > f_read_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_read_time_stamp[bank_const]) >= ns_to_nCK(10));
            end

            // Check tWTR (Delay from start of internal write transaction to internal read command)
            if(f_read_time_stamp[bank_const] > f_write_time_stamp[bank_const]) begin
                assert((f_read_time_stamp[bank_const] - f_write_time_stamp[bank_const]) >= (CWL_nCK + 3'd4 + ns_to_nCK(tWTR)));
            end

            // Check tRCD (ACT to internal read delay time)
            if(f_read_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_read_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ns_to_nCK(tRCD));
            end 
            
            // Check tRCD (ACT to internal write delay time)
            if(f_write_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_write_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ns_to_nCK(tRCD));
            end

            // Check tRP (PRE command period)
            if(f_activate_time_stamp[bank_const] > f_precharge_time_stamp[bank_const]) begin
                assert((f_activate_time_stamp[bank_const] - f_precharge_time_stamp[bank_const]) >= ns_to_nCK(tRP));
            end
            
            // Check tRAS (ACTIVE to PRECHARGE command period)
            if(f_precharge_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ns_to_nCK(tRAS));
            end

            // Check tWR (WRITE recovery time for write-to-precharge)
            if(f_precharge_time_stamp[bank_const] > f_write_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_write_time_stamp[bank_const]) >= (CWL_nCK + 3'd4 + ns_to_nCK(tWR)));
            end

            // Check delay from read-to-write
            if(f_write_time_stamp[bank_const] > f_read_time_stamp[bank_const]) begin
                assert((f_write_time_stamp[bank_const] - f_read_time_stamp[bank_const]) >= (CL_nCK + tCCD + 3'd2 - CWL_nCK));
            end

        end

        // extra assertions to make sure engine starts properly
        always @* begin
            assert(instruction_address <= 22);
            assert(state_calibrate <= DONE_CALIBRATE);

            if(!o_wb_stall) begin
                assert(state_calibrate == DONE_CALIBRATE);
                assert(instruction_address == 22 || (instruction_address == 19 && delay_counter == 0));
            end

            if(instruction_address == 19 && delay_counter != 0 && state_calibrate == DONE_CALIBRATE) begin
                if(stage1_pending || stage2_pending) begin
                    assert(pause_counter);
                end
            end

            if(stage1_pending || stage2_pending) begin
               assert(state_calibrate > ISSUE_WRITE_1); 
               assert(instruction_address == 22 || instruction_address == 19);
            end

            if(instruction_address < 13) begin
                assert(state_calibrate == IDLE);
            end

            if(state_calibrate > IDLE && state_calibrate <= BITSLIP_DQS_TRAIN_2) begin
                assert(instruction_address == 13);
                assert(pause_counter);
            end


            if(state_calibrate > START_WRITE_LEVEL  && state_calibrate <= WAIT_FOR_FEEDBACK) begin
                assert(instruction_address == 17);
                assert(pause_counter);
            end
            
            if(pause_counter) begin
                assert(delay_counter != 0);
            end
            
            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate < DONE_CALIBRATE) begin
                assume(instruction_address == 22); //write-then-read calibration will not take more than tREFI (7.8us, delay a address 22)
                assert(reset_done);
            end

            if(state_calibrate == DONE_CALIBRATE) begin
                assert(reset_done);
                assert(instruction_address >= 19);
            end

            if(reset_done) begin
                assert(instruction_address >= 19);
            end

            if(!reset_done) begin
                assert(!stage1_pending && !stage2_pending);
                assert(o_wb_stall);
            end
            if(reset_done) begin
                assert(instruction_address >= 19 && instruction_address <= 22);
            end
            //delay_counter is zero at first clock of new instruction address, the actual delay_clock wil start at next clock cycle 
            if(instruction_address == 19 && delay_counter != 0) begin
                assert(o_wb_stall);
            end

            if(instruction_address == 19 && pause_counter) begin //pre-stall delay to finish all remaining requests
               assert(delay_counter == PRE_REFRESH_DELAY); 
               assert(reset_done);
               assert(DONE_CALIBRATE);
            end
        end

        // verify the wishbone 2
        localparam F_TEST_WB2_DATA_WIDTH = wb2_sel_bits + 5 + lanes_clog2 + 4 + 1; //WB2_SEL + CNTVALUEIN + LANE_NUMBER + MEMORY_MAPPED_ADDRESS + REQUEST_TYPE
        reg f_read_fifo_2, f_write_fifo_2;
        wire f_empty_2, f_full_2;
        reg[F_TEST_WB2_DATA_WIDTH - 1:0] f_write_data_2 = 0; 
        reg[F_TEST_WB2_DATA_WIDTH - 1:0] f_read_data_2, f_read_data_2_q;  
        reg f_o_wb2_ack_q = 0; //registered o_wb2_ack
        (*keep*) reg[LANES-1:0] f_delay_ld = 0;

        //accept request
        always @* begin
            if(f_empty_2 && i_wb2_cyc) begin
                assert(!wb2_stb && !o_wb2_ack);
            end
            if(!wb2_stb && !o_wb2_ack) begin
                assert(f_empty_2);
            end
            f_write_data_2 = 0;
            f_write_fifo_2 = 0;
            if(i_wb2_stb && !o_wb2_stall && i_wb2_cyc) begin //if there is request
                if(i_wb2_we) begin //write request
                    f_write_data_2 = {i_wb2_sel, i_wb2_data[4:0], i_wb2_data[5 +: lanes_clog2], i_wb2_addr[3:0], i_wb2_we}; //CNTVALUEIN + LANE_NUMBER + MEMORY_MAPPED_ADDRESS + REQUEST_TYPE
                    assume(i_wb2_data[5 +: lanes_clog2] < LANES);
                end 
                else begin //read request
                    f_write_data_2 = {i_wb2_addr[4 +: lanes_clog2],  i_wb2_addr[3:0], i_wb2_we}; //LANE_NUMBER + MEMORY_MAPPED_ADDRESS + REQUEST_TYPE
                    assume(i_wb2_addr[4 +: lanes_clog2] < LANES);
                end
                f_write_fifo_2 = 1;
            end

            if(state_calibrate != DONE_CALIBRATE && i_wb2_stb) begin
                /* must not be a read/write to delays when not yet done calibrating */
                assume(i_wb2_addr[3:0] > 3);
            end
        end
        
        //verify outcome of request
        always @(posedge i_controller_clk, negedge i_rst_n) begin
            if(!i_rst_n) begin
                f_o_wb2_ack_q <= 0;
                f_read_data_2_q <= 0;
            end
            else begin
                f_o_wb2_ack_q <= o_wb2_ack && f_read_data_2[0] && i_wb2_cyc;
                f_read_data_2_q <= f_read_data_2;
            end
        end
        always @* begin
            if(i_rst_n) begin
                if(wb2_stb && o_wb2_ack) begin
                    assert(f_full_2 || !i_wb2_cyc);
                end
                if(f_full_2) begin
                    assert(wb2_stb && o_wb2_ack);
                    assert(f_outstanding_2 == 2 || !i_wb2_cyc);
                end
                if(f_outstanding_2 == 2) begin
                    assert(f_full_2 || !i_wb2_cyc);
                end
                if(f_empty_2) begin
                    assert(f_outstanding_2 == 0 || !i_wb2_cyc);
                end
                if(f_outstanding_2 == 0) begin
                    assert(f_empty_2 || !i_wb2_cyc);
                end
            end
            assert(f_outstanding_2 <= 2);
            f_read_fifo_2 = 0;
           if(o_wb2_ack && !f_read_data_2[0] && i_rst_n) begin //read request
                f_read_fifo_2 = 1;
           end

           if(o_wb2_ack && f_read_data_2[0] && i_rst_n) begin
                f_read_fifo_2 = 1;
           end
        end

        //check request action at wb_ack
        always @(posedge i_controller_clk) begin
            if(f_past_valid) begin
                assert(!o_wb2_stall || !i_rst_n || !$past(i_rst_n)); //never stall
                //write request
                if(f_o_wb2_ack_q &&  i_rst_n && (&f_read_data_2_q[5 + lanes_clog2 + 4 + 1 +: $rtoi($ceil( (lanes_clog2 + 5)/8.0 ))])) begin //the sel bits must be high
                    case(f_read_data_2_q[4:1]) //memory-mapped address
                        0: begin
                             assert(o_phy_odelay_data_ld == (1 << f_read_data_2_q[5 +: lanes_clog2])); //the phy lane to be loaded must be high 
                             assert(o_phy_odelay_data_cntvaluein == f_read_data_2_q[(5 + lanes_clog2) +: 5]); //the phy interface for cntvalue must already be updated 
                             assert($past(wb2_update));
                           end 
                        1: begin
                             assert(o_phy_odelay_dqs_ld == (1 << f_read_data_2_q[5 +: lanes_clog2])); //the phy lane to be loaded must be high 
                             assert(o_phy_odelay_dqs_cntvaluein == f_read_data_2_q[(5 + lanes_clog2) +: 5]); //the phy interface for cntvalue must already be updated 
                             assert($past(wb2_update));
                           end 
                        2: begin
                             assert(o_phy_idelay_data_ld == (1 << f_read_data_2_q[5 +: lanes_clog2])); //the phy lane to be loaded must be high 
                             assert(o_phy_idelay_data_cntvaluein == f_read_data_2_q[(5 + lanes_clog2) +: 5]); //the phy interface for cntvalue must already be updated 
                             assert($past(wb2_update));
                           end 
                        3: begin
                             assert(o_phy_idelay_dqs_ld == (1 << f_read_data_2_q[5 +: lanes_clog2])); //the phy lane to be loaded must be high 
                             assert(o_phy_idelay_dqs_cntvaluein == f_read_data_2_q[(5 + lanes_clog2) +: 5]); //the phy interface for cntvalue must already be updated 
                             assert($past(wb2_update));
                           end 
                    endcase
                end  
                else if(i_rst_n) begin
                    assert(!$past(wb2_update) || !$past(i_wb2_cyc));
                end

                //read request
               if(o_wb2_ack && !f_read_data_2[0] && i_rst_n && i_wb2_cyc && !(f_o_wb2_ack_q && f_read_data_2_q[1 +: (4 + lanes_clog2)] == f_read_data_2[1 +: (4 + lanes_clog2)] )) begin 
                    case(f_read_data_2[4:1]) //memory-mapped address
                        0: begin
                             assert(o_wb2_data == odelay_data_cntvaluein[f_read_data_2[5 +: lanes_clog2]]); //the stored delay must match the wb2 output 
                           end 
                        1: begin
                             assert(o_wb2_data == odelay_dqs_cntvaluein[f_read_data_2[5 +: lanes_clog2]]); //the stored delay must match the wb2 output 
                           end 
                        2: begin
                             assert(o_wb2_data == idelay_data_cntvaluein[f_read_data_2[5 +: lanes_clog2]]); //the stored delay must match the wb2 output 
                           end 
                        3: begin
                             assert(o_wb2_data == idelay_dqs_cntvaluein[f_read_data_2[5 +: lanes_clog2]]); //the stored delay must match the wb2 output 
                           end 

                        4: begin
                             assert(o_wb2_data[0] == $past(i_phy_idelayctrl_rdy));
                             assert(o_wb2_data[5:1] == $past(state_calibrate));
                             assert(o_wb2_data[10:6] == $past(instruction_address));
                             assert(o_wb2_data[14:11] == $past(added_read_pipe_max));
                           end

                        5: begin
                            for(index = 0; index < LANES; index = index + 1) begin
                             assert(o_wb2_data[4*index +: 4] == $past(added_read_pipe[index]));
                            end
                           end

                        6: begin
                             assert(o_wb2_data == $past(dqs_store[31:0]));
                           end

                        7: begin
                                for(index = 0; 8*index < 32 && index < LANES; index = index + 1) begin
                                     assert(o_wb2_data[8*index +: 8] == $past(i_phy_iserdes_bitslip_reference[8*index +: 8])); 
                                end
                            end
                        8: begin
                             assert(o_wb2_data == $past(read_data_store[31:0])); 
                           end

                        9: begin
                             assert(o_wb2_data == $past(write_pattern[31:0])); 
                           end
                    endcase
               end
            end
        end

        wire[2:0] f_read_data_2_lane;
        assign f_read_data_2_lane = f_read_data_2[5 +: lanes_clog2];
        always @(posedge i_controller_clk) begin
           if(f_past_valid) begin
               for(index = 0; index < LANES; index = index + 1) begin
                    if(o_phy_bitslip[index]) begin
                        /* Bitslip cannot be asserted for two consecutive CLKDIV cycles; Bitslip must be
                        deasserted for at least one CLKDIV cycle between two Bitslip assertions. 
                        */
                        assert(!$past(o_phy_bitslip[index]));
                    end
               end
           end
        end

        mini_fifo #(
            .FIFO_WIDTH(1), //the fifo will have 2**FIFO_WIDTH positions
            .DATA_WIDTH(F_TEST_WB2_DATA_WIDTH) //each FIFO position can store DATA_WIDTH bits
       ) fifo_2 (
            .i_clk(i_controller_clk), 
            .i_rst_n(i_rst_n && i_wb2_cyc), //reset outstanding request at reset or when cyc goes low
            .read_fifo(f_read_fifo_2), 
            .write_fifo(f_write_fifo_2),
            .empty(f_empty_2), 
            .full(f_full_2),
            .write_data(f_write_data_2),
            .read_data(f_read_data_2)
       ); 
    
    //assumption on when to do request (so as not to violate the
    //F_MAX_STALL property of fwb_slave) 
    always @* begin
        if(!(state_calibrate == DONE_CALIBRATE && instruction_address == 22)) begin //if in initialization/refresh sequence, no request should come in to the controller wishbone 
            assume(!i_wb_stb);
        end
    end
    fwb_slave #(
            // {{{
            .AW(wb_addr_bits), 
            .DW(wb_data_bits),
            .F_MAX_STALL(F_MAX_STALL),
            .F_MAX_ACK_DELAY(F_MAX_ACK_DELAY),
            .F_LGDEPTH(4),
            .F_MAX_REQUESTS(10),
            // OPT_BUS_ABORT: If true, the master can drop CYC at any time
            // and must drop CYC following any bus error
            .OPT_BUS_ABORT(1),
            //
            // If true, allow the bus to be kept open when there are no
            // outstanding requests.  This is useful for any master that
            // might execute a read modify write cycle, such as an atomic
            // add.
            .F_OPT_RMW_BUS_OPTION(1),
            //
            // 
            // If true, allow the bus to issue multiple discontinuous
            // requests.
            // Unlike F_OPT_RMW_BUS_OPTION, these requests may be issued
            // while other requests are outstanding
            .F_OPT_DISCONTINUOUS(1),
            //
            //
            // If true, insist that there be a minimum of a single clock
            // delay between request and response.  This defaults to off
            // since the wishbone specification specifically doesn't
            // require this.  However, some interfaces do, so we allow it
            // as an option here.
            .F_OPT_MINCLOCK_DELAY(1),
            // }}}
        ) wb_properties (
            // {{{
            .i_clk(i_controller_clk), 
            .i_reset(!i_rst_n),
            // The Wishbone bus
            .i_wb_cyc(i_wb_cyc), 
            .i_wb_stb(i_wb_stb), 
            .i_wb_we(i_wb_we),
            .i_wb_addr(i_wb_addr),
            .i_wb_data(i_wb_data),
            .i_wb_sel(i_wb_sel),
            //
            .i_wb_ack(o_wb_ack),
            .i_wb_stall(o_wb_stall),
            .i_wb_idata(o_wb_data),
            .i_wb_err(1'b0),
            // Some convenience output parameters
            .f_nreqs(f_nreqs), 
            .f_nacks(f_nacks),
            .f_outstanding(f_outstanding),
            .f_ackwait_count(f_ackwait_count),
            .f_stall_count(f_stall_count)
            // }}}
            // }}}
        );

    fwb_slave #(
            // {{{
            .AW(WB2_ADDR_BITS), 
            .DW(WB2_DATA_BITS),
            .F_MAX_STALL(2),
            .F_MAX_ACK_DELAY(2),
            .F_LGDEPTH(4),
            .F_MAX_REQUESTS(10),
            // OPT_BUS_ABORT: If true, the master can drop CYC at any time
            // and must drop CYC following any bus error
            .OPT_BUS_ABORT(1),
            //
            // If true, allow the bus to be kept open when there are no
            // outstanding requests.  This is useful for any master that
            // might execute a read modify write cycle, such as an atomic
            // add.
            .F_OPT_RMW_BUS_OPTION(1),
            //
            // 
            // If true, allow the bus to issue multiple discontinuous
            // requests.
            // Unlike F_OPT_RMW_BUS_OPTION, these requests may be issued
            // while other requests are outstanding
            .F_OPT_DISCONTINUOUS(1),
            //
            //
            // If true, insist that there be a minimum of a single clock
            // delay between request and response.  This defaults to off
            // since the wishbone specification specifically doesn't
            // require this.  However, some interfaces do, so we allow it
            // as an option here.
            .F_OPT_MINCLOCK_DELAY(1),
            // }}}
        ) wb2_properties (
            // {{{
            .i_clk(i_controller_clk), 
            .i_reset(!i_rst_n),
            // The Wishbone bus
            .i_wb_cyc(i_wb2_cyc), 
            .i_wb_stb(i_wb2_stb), 
            .i_wb_we(i_wb2_we),
            .i_wb_addr(i_wb2_addr),
            .i_wb_data(i_wb2_data),
            .i_wb_sel(i_wb2_sel),
            //
            .i_wb_ack(o_wb2_ack),
            .i_wb_stall(o_wb2_stall),
            .i_wb_idata(o_wb2_data),
            .i_wb_err(1'b0),
            // Some convenience output parameters
            .f_nreqs(f_nreqs_2), 
            .f_nacks(f_nacks_2),
            .f_outstanding(f_outstanding_2),
            // }}}
            // }}}
        );
    `endif //endif for TEST_CONTROLLER_PIPELINE
`endif //endif for FORMAL
endmodule

`ifdef FORMAL
//FiFO with only 2 elements for verifying the contents of the controller
//2-stage pipeline
module mini_fifo #(
        parameter FIFO_WIDTH = 1, //the fifo will have 2**FIFO_WIDTH positions
        parameter DATA_WIDTH = 8 //each FIFO position can store DATA_WIDTH bits
   )(
        input wire i_clk, i_rst_n,
        input wire read_fifo, write_fifo,
        output reg empty, full,
        input wire[DATA_WIDTH - 1:0] write_data,
        output wire[DATA_WIDTH - 1:0] read_data,
        output wire[DATA_WIDTH - 1:0] read_data_next
   ); 
    reg[FIFO_WIDTH-1:0] write_pointer=0, read_pointer=0;
    reg[DATA_WIDTH - 1:0] fifo_reg[2**FIFO_WIDTH-1:0];
    initial begin
        empty = 1;
        full = 0;
    end

    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            empty <= 1;
            full <=0;
            read_pointer <= 0;
            write_pointer <= 0;
        end
        else begin
            if(read_fifo) begin
                `ifdef FORMAL
                    assert(!empty);
                `endif
                if(!write_fifo) full <= 0;
                //advance read pointer
                read_pointer <= read_pointer + 1;
                if(read_pointer + 1'b1 == write_pointer && !write_fifo) empty <= 1;
             end
            if(write_fifo) begin
                 `ifdef FORMAL
                    if(!read_fifo) assert(!full);
                  `endif
                  if(!read_fifo) empty <= 0;
                  //write to FiFo
                  fifo_reg[write_pointer] <= write_data;
                  //advance read pointer
                  write_pointer <= write_pointer + 1;
                  if(write_pointer + 1'b1 == read_pointer && !read_fifo) full <= 1'b1; //fifo should never be full
            end
        end
    end
    assign read_data = fifo_reg[read_pointer];
    assign read_data_next = fifo_reg[!read_pointer]; //data after current pointer

    `ifdef FORMAL
    //mini-FiFo assertions
    always @* begin
        if(empty || full) begin
            assert(write_pointer == read_pointer); 
        end
        if(write_pointer == read_pointer) begin
            assert(empty || full);
        end
        assert(!(empty && full));
        //TASK ADD MORE ASSERTIONS
    end
    `endif

endmodule

`endif

