// Background:
// This DDR3 controller will be used with a DDR3-1600 with Kintex 7 FPGA Board (XC7K160T-3FFG676E). 
// The goal will be to:
//  - Run this at 1600Mbps (Maximum Physical Interface (PHY) Rate for a 4:1 
//          memory controller based on "DC and AC Switching Characteristics" for Kintex 7)
//  - Parameterize everything
//  - Interface should be (nearly) bus agnostic   
//  - High (sustained) data throughput. Sequential writes should be able to continue without interruption 


//`define FORMAL_COVER //change delay in reset sequence to fit in cover statement
`define COVER_DELAY 3 //fixed delay used in formal cover for reset sequence
`default_nettype none


// THESE DEFINES WILL BE MODIFIED AS PARAMETERS LATER ON
`define DDR3_1600_11_11_11 // DDR3-1600 (11-11-11) speed bin
`define RAM_8Gb //DDR3 Capacity
//`define RAM_2Gb 
//`define RAM_4Gb 
//`define RAM_8Gb
`define x8 //DDR3 organization (DQ bus width) 
//`define x4
//`define x16

                   
module ddr3_controller #(
    parameter ROW_BITS = 14,   //width of row address
                COL_BITS = 10, //width of column address
                BA_BITS = 3, //width of bank address
                DQ_BITS = 8,  //width of DQ
                CONTROLLER_CLK_PERIOD = 5, //ns, period of clock input to this DDR3 controller module
                DDR3_CLK_PERIOD = 1.25, //ns, period of clock input to DDR3 RAM device 
                LANES = 8, //8 lanes of DQ
                OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
                OPT_BUS_ABORT = 1,  //1 = can abort bus, 0 = no abort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
                
                // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
                serdes_ratio = $rtoi(CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD),
                wb_addr_bits = ROW_BITS + COL_BITS + BA_BITS - $clog2(DQ_BITS*(serdes_ratio)*2 / 8),
                wb_data_bits = DQ_BITS*LANES*serdes_ratio*2,
                wb_sel_bits = wb_data_bits / 8
    ) 
    (
        input wire i_controller_clk, i_ddr3_clk, i_ddr3_clk_n, //i_controller_clk has period of CONTROLLER_CLK_PERIOD, i_ddr3_clk has period of DDR3_CLK_PERIOD 
        // i_ddr3_clk_n is used for ISERDES
        /* The only valid clocking arrangements for the ISERDESE2 block using the networking
            interface type are:
            • CLK driven by BUFIO, CLKDIV driven by BUFR
            • CLK driven by MMCM or PLL, CLKDIV driven by CLKOUT[0:6] of same MMCM or
        PLL
        */
        input wire i_rst_n, //200MHz input clock
        // Wishbone inputs
        input wire i_wb_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb_stb, //request a transfer
        input wire i_wb_we, //write-enable (1 = write, 0 = read)
        input wire[wb_addr_bits - 1:0] i_wb_addr, //burst-addressable {row,bank,col} 
        input wire[wb_data_bits - 1:0] i_wb_data, //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        input wire[wb_sel_bits - 1:0] i_wb_sel, //byte strobe for write (1 = write the byte)
        input wire i_aux, //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        output reg o_wb_stall, //1 = busy, cannot accept requests
        output wire o_wb_ack, //1 = read/write request has completed
        output wire[wb_data_bits - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output reg o_aux, //for AXI-interface compatibility (returned upon ack)
        // PHY Interface (to be added later)
        output wire ck_en, // CKE
        output wire cs_n, // chip select signal
        output wire odt, // on-die termination
        output wire ras_n, // RAS#
        output wire cas_n, // CAS#
        output wire we_n, // WE#
        output wire reset_n,
        output wire[ROW_BITS-1:0] addr,
        output wire[BA_BITS-1:0] ba_addr,
        input wire[(DQ_BITS*LANES)-1:0] dq,
        input wire[(DQ_BITS*LANES)/8-1:0] dqs, dqs_n
        ////////////////////////////////////
    );

    
    ////////////////////////////////////////////////////////////// COMMAND PARAMETERS //////////////////////////////////////////////////////////////

    //DDR3 commands {cs_n, ras_n, cas_n, we_n} (JEDEC DDR3 doc pg. 33 )
    localparam[3:0]CMD_MRS = 4'b0000, // Mode Register Set
                      CMD_REF = 4'b0001, // Refresh
                      CMD_PRE = 4'b0010, // Precharge (A10-AP: 0 = Single Bank Precharge, 1 = Precharge All Banks)
                      CMD_ACT = 4'b0011, // Bank Activate
                      CMD_WR  = 4'b0100, // Write (A10-AP: 0 = no Auto-Precharge) (A12-BC#: 1 = Burst Length 8) 
                      CMD_RD  = 4'b0101, //Read  (A10-AP: 0 = no Auto-Precharge) (A12-BC#: 1 = Burst Length 8) 
                      CMD_NOP = 4'b0111, // No Operation
                      CMD_DES = 4'b1000, // Deselect command performs the same function as No Operation command (JEDEC DDR3 doc pg. 34 NOTE 11)
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
                     
                         // ddr3_metadata partitioning
    localparam CMD_LEN = 4 + 3 + BA_BITS + ROW_BITS, //4 is the width of a single ddr3 command (precharge,actvate, etc.) plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
               CMD_CS_N = CMD_LEN - 1, 
               CMD_RAS_N = CMD_LEN - 2,
               CMD_CAS_N= CMD_LEN - 3,
               CMD_WE_N = CMD_LEN - 4,
               CMD_ODT = CMD_LEN - 5,
               CMD_CK_EN = CMD_LEN - 6, 
               CMD_RESET_N = CMD_LEN - 7,
               CMD_BANK_START = BA_BITS + ROW_BITS - 1,
               CMD_ROW_ADDRESS_START = ROW_BITS - 1;
               
    localparam READ_SLOT = get_slot(CMD_RD),
                WRITE_SLOT = get_slot(CMD_WR),
                ACTIVATE_SLOT = get_slot(CMD_ACT),
                PRECHARGE_SLOT = get_slot(CMD_PRE);

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



    /////////////////////////////////////////////////////////// TIMING PARAMETERS ////////////////////////////////////////////////////////////////////////////////////
    localparam DELAY_SLOT_WIDTH = 19; //Bitwidth of the delay slot and mode register slot on the reset/refresh rom will be at the same size as the Mode Register
    localparam POWER_ON_RESET_HIGH      =     200_000; // 200us reset must be active at initialization
    localparam INITIAL_CKE_LOW      =       500_000; // 500us cke must be low before activating

    `ifdef DDR3_1600_11_11_11 //DDR3-1600 (11-11-11) speed bin
        //localparam tRAS     =       35.0; // ns Minimum Active to Precharge command time
        //localparam tRC      =       48.750; //ns Active to Active/Auto Refresh command time
        localparam tRCD     =       13.750; // ns Active to Read/Write command time
        localparam tRP      =      13.750; // ns Precharge command period
        
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
    localparam tXPR = max(5*DDR3_CLK_PERIOD,tRFC+10); // ns Exit Reset from CKE HIGH to a valid command
    localparam tMRD = 4; // nCK Mode Register Set command cycle time
    localparam tWR = 15.0; // ns Write Recovery Time
    localparam tWTR = max(nCK_to_ns(4), 7.5); //ns Delay from start of internal write transaction to internal read command
    //localparam tDLLK = 512.0; //nCK DLL Locking time
    localparam[DELAY_SLOT_WIDTH - 1:0] tWLMRD = nCK_to_cycles(40); // nCK First DQS/DQS# rising edge after write leveling mode is programmed
    localparam tWLO = 7.5; //ns Write leveling output delay
    localparam tWLOE = 2;
    localparam tRTP = max(nCK_to_ns(4), 7.5); //ns Internal Command to PRECHARGE Command delay
    localparam tCCD = 4; //nCK CAS to CAS command delay
    localparam[DELAY_SLOT_WIDTH - 1:0] tMOD = max(nCK_to_cycles(12), ns_to_cycles(15)); //cycles (controller)  Mode Register Set command update delay
    localparam[DELAY_SLOT_WIDTH - 1:0] tZQinit = max(nCK_to_cycles(512), ns_to_cycles(640));//cycles (controller)  Power-up and RESET calibration time
    //localparam[DELAY_SLOT_WIDTH - 1:0] tZQoper = max(nCK_to_cycles(256), ns_to_cycles(320)); //cycles (controller) Normal operation Full calibration time
    localparam CL_nCK = 11; //create a function for this
    localparam CWL_nCK = 8; //create a function for this
    localparam DELAY_MAX_VALUE = ns_to_cycles(INITIAL_CKE_LOW); //Largest possible delay needed by the reset and refresh sequence
    localparam DELAY_COUNTER_WIDTH= $clog2(DELAY_MAX_VALUE); //Bitwidth needed by the maximum possible delay, this will be the delay counter width
    localparam READ_CAL_DELAY = 100;
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    
    ////////////////////////////////////////////////////////////// SET MODE REGISTERS //////////////////////////////////////////////////////////////

    // MR2 (JEDEC DDR3 doc pg. 30)
    localparam[2:0] PASR = 3'b000; //Partial Array Self-Refresh: Full Array
    localparam[2:0] CWL = 3'b011; //CAS write Latency: 8 (1.5 ns > tCK(avg) >= 1.25 ns) CREATE A FUNCTION FOR THIS
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
    localparam[ROW_BITS+BA_BITS-1:0] MR3_RD_ADDR = 0;
    
    // MR1 (JEDEC DDR3 doc pg. 27)
    localparam DLL_EN = 1'b0; //DLL Enable/Disable: Enabled(0)
    localparam[1:0] DIC = 2'b00; //Output Driver Impedance Control (IS THIS THE SAME WITH RTT_NOM???????????? Search later)
    localparam[2:0] RTT_NOM = 3'b011; //RTT Nominal: 40ohms (RQZ/6) is the impedance of the PCB trace
    localparam[0:0] WL_EN = 1'b1; //Write Leveling Enable: Disabled
    localparam[0:0] WL_DIS = 1'b0; //Write Leveling Enable: Disabled
    localparam[1:0] AL = 2'b00; //Additive Latency: Disabled
    localparam[0:0] TDQS = 1'b1; //Termination Data Strobe: Disabled (provides additional termination resistance outputs. When the TDQS function is disabled, the DM function is provided (vice-versa).TDQS function is only available for X8 DRAM and must be disabled for X4 and X16. 
    localparam[0:0]  QOFF = 1'b0; //Output Buffer Control: Enabled
    localparam[2:0] MR1_SEL = 3'b001; //Selected Mode Register
    localparam[18:0] MR1_WL_EN = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, WL_EN, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};
    localparam[18:0] MR1_WL_DIS = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, WL_DIS, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};

    //MR0 (JEDEC DDR3 doc pg. 24)
    localparam[1:0] BL = 2'b00; //Burst Length: 8 (Fixed)
    localparam[3:0] CL = 4'b1110; //CAS Read Latency: 10, can support DDR-1600 speedbin 8-8-8, 9-9-9, and 10-10-10 (Check JEDEC DDR doc pg. 162) CREATE A FUNCTION FOR THIS
    localparam[0:0] RBT = 1'b0; //Read Burst Type: Nibble Sequential
    localparam[0:0] DLL_RST = 1'b1; //DLL Reset: Yes (this is self-clearing and must be applied after DLL enable)
    localparam[2:0] WR = WRA_mode_register_value($ceil(tWR/DDR3_CLK_PERIOD)); //Write recovery for autoprecharge (
    localparam[0:0] PPD = 1'b0; //DLL Control for Precharge PD: Slow exit (DLL off)
    localparam[2:0] MR0_SEL = 3'b000;
    localparam[18:0] MR0 = {MR0_SEL, 3'b000, PPD, WR, DLL_RST, 1'b0, CL[3:1], RBT, CL[0], BL};

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


    localparam PRE_STALL_DELAY = 10;

    
    //////////////////////////////////////////////////////// RESET and Initialization Procedure (JEDEC DDR3 doc pg. 19) ////////////////////////////////////////////////////////
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
        
        // NOTE: The timer delay is a delay in clock cycles AFTER EXECUTING COMMAND, not the ACTUAL CYCLES of the command (delay of 1 means 2 clock cycles of command execution)
    function [27:0] read_rom_instruction(input[5:0] instruction_address);
        case(instruction_address) 
    
            5'd0: read_rom_instruction = {5'b01000 , CMD_NOP , ns_to_cycles(/*POWER_ON_RESET_HIGH*/200)}; 
            //0. RESET# needs to be maintained low for minimum 200us with power-up initialization. CKE is pulled
                //“Low” anytime before RESET# being de-asserted (min. time 10 ns). .
            
            5'd1: read_rom_instruction =  {5'b01001 , CMD_NOP, ns_to_cycles(/*INITIAL_CKE_LOW*/500)}; 
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
            
            5'd7: read_rom_instruction = {5'b01011, CMD_NOP, tMOD};
            //7. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
           
            5'd8: read_rom_instruction = {5'b01111, CMD_ZQC, tZQinit}; 
            //8. ZQ Calibration command is used to calibrate DRAM Ron & ODT values. ZQCL command triggers the calibration engine 
            //inside the DRAM and, once calibration is achieved, the calibrated values area transferred from the calibration engine to 
            //DRAM IO, which gets reflected as updated output driver
            
             // Precharge all banks before enabling MPR
            5'd9: read_rom_instruction = {5'b01111, CMD_PRE, ns_to_cycles(tRP)}; 
            //9. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            5'd10: read_rom_instruction = {{2'b00,MR3_MPR_EN[10], 2'b11}, CMD_MRS, MR3_MPR_EN}; 
            //10. Issue MRS command to load MR3. Prior to enabling the MPR for read calibration, all banks must be in the idle state (all banks 
            // precharged and tRP met). Once the MPR is enabled, any subsequent RD or RDA commands will be redirected to the MultiPurpose Register. 
            
            5'd11: read_rom_instruction = {5'b01011, CMD_NOP, tMOD};
            //11. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            5'd12: read_rom_instruction = {5'b01011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b1}}}; 
            //12. Delay for read calibration
            
            5'd13: read_rom_instruction = {{2'b00,MR3_MPR_DIS[10], 2'b11}, CMD_MRS, MR3_MPR_DIS}; 
            //13. Disable MPR after read calibration
            
            5'd14: read_rom_instruction = {{2'b00,MR1_WL_EN[10], 2'b11}, CMD_MRS, MR1_WL_EN}; 
            //14. Issue MRS command to load MR1, and enable WL. 
            
            5'd15: read_rom_instruction = {5'b01011, CMD_NOP, tWLMRD};
            //15. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            5'd16: read_rom_instruction = {5'b01011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b1}}}; 
            //16. Delay for write calibration
            
            5'd17: read_rom_instruction = {{2'b00,MR1_WL_DIS[10], 2'b11}, CMD_MRS, MR1_WL_DIS}; 
            //17. Issue MRS command to load MR1, and disable WL. 
            
            5'd18: read_rom_instruction = {5'b01011, CMD_NOP, tMOD};
            //18. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            // Perform first refresh and any subsequent refresh (so instruction 12 to 15 will be re-used for the refresh sequence)
            5'd19: read_rom_instruction = {5'b01111, CMD_PRE, ns_to_cycles(tRP)}; 
            //19. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            5'd20: read_rom_instruction = {5'b01011, CMD_REF, ns_to_cycles(tRFC)};
            //20. A delay between the Refresh Command and the next valid command, except NOP or DES, must be greater than or equal to the minimum 
            //Refresh cycle time tRFC(min) 
            
            5'd21: read_rom_instruction = {5'b11011, CMD_NOP, ns_to_cycles(tREFI)};
            //21. Reset ends now. The refresh interval also starts to count.
            
            5'd22: read_rom_instruction = {5'b01011, CMD_NOP, PRE_STALL_DELAY[DELAY_SLOT_WIDTH-1:0]}; 
            // 22. Extra delay needed before starting the refresh sequence. (this already sets the wishbone stall high to make sure no user request is on-going when refresh seqeunce starts)
            
            default: read_rom_instruction = {5'b00011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b0}}}; 
        endcase
    endfunction
    
    //initial reset instruction has low rst_n, low cke, and has delay of 5
    localparam INITIAL_RESET_INSTRUCTION = {5'b01000 , CMD_NOP , { {(DELAY_SLOT_WIDTH-3){1'b0}} , 3'd5} }; 
    
    reg[4:0] instruction_address = 0; //address for accessing rom instruction
    reg[27:0] instruction = INITIAL_RESET_INSTRUCTION; //instruction retrieved from reset instruction rom
    reg[ DELAY_COUNTER_WIDTH - 1:0] delay_counter = INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]; //counter used for delays
    reg delay_counter_is_zero = (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0); //counter is now zero so retrieve next delay
    reg reset_done = 0; //high if reset has already finished
    reg skip_reset_seq_delay = 0; //flag to skip delay and go to next reset instruction
    wire issue_read_command;
    wire issue_write_command;
    always @(posedge i_controller_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            instruction_address <= 0;
            instruction <= INITIAL_RESET_INSTRUCTION;
            delay_counter <= INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0];
            delay_counter_is_zero <= (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0);
            reset_done <= 1'b0;
        end
        else begin 
            //update counter after reaching zero
            if(delay_counter_is_zero) begin 
                `ifndef FORMAL_COVER
                    delay_counter <= instruction[DELAY_COUNTER_WIDTH - 1:0]; //retrieve delay value of current instruction, we count to zero thus minus 1
                `else
                    //if(instruction[DELAY_COUNTER_WIDTH - 1:0] > `COVER_DELAY) delay_counter <= `COVER_DELAY; //use fixed low value delay to cover the whole reset seqeunce using formal verification
                    //else delay_counter <= instruction[DELAY_COUNTER_WIDTH - 1:0] ; //use delay from rom if that is smaller than the COVER_DELAY macro
                    if(instruction[DELAY_COUNTER_WIDTH - 1:0]!= DELAY_MAX_VALUE) delay_counter <= 3;
                    else delay_counter <= instruction[DELAY_COUNTER_WIDTH - 1:0];
                `endif
                //RECEIVE THE COMMANDS
            end
            
            //else: decrement delay counter when current instruction needs delay
            else if(instruction[USE_TIMER]) delay_counter <= delay_counter - 1; 
            
            //delay_counter of 1 means we will need to update the delay_counter next clock cycle (delay_counter of zero) so we need to retrieve 
            //now the next instruction. The same thing needs to be done when current instruction does not need the timer delay.
            if(delay_counter == 1 || !instruction[USE_TIMER] || skip_reset_seq_delay) begin
                delay_counter_is_zero <= 1; 
                instruction <= read_rom_instruction(instruction_address);
                instruction_address <= (instruction_address == 5'd22)? 5'd19:instruction_address+1; //instruction_address 15 must wrap back to instruction_address 12 for the refresh sequence
            end
            //we are now on the middle of a delay 
            else delay_counter_is_zero <=0; 
            //instruction[RST_DONE] is non-persistent thus we need to register it once it goes high
            reset_done <= instruction[RST_DONE]? 1'b1:reset_done; 
        end
        
    end

    //////////////////////////////////////////////////////// Track Bank Status and Active Row ////////////////////////////////////////////////////////
    //delay constants    
    localparam PRECHARGE_TO_ACTIVATE_DELAY =  find_delay(ns_to_nCK(tRP), PRECHARGE_SLOT, ACTIVATE_SLOT); //3
    localparam ACTIVATE_TO_WRITE_DELAY = find_delay(ns_to_nCK(tRCD), ACTIVATE_SLOT, WRITE_SLOT); //3
    localparam ACTIVATE_TO_READ_DELAY = find_delay(ns_to_nCK(tRCD), ACTIVATE_SLOT, READ_SLOT); //2
    localparam READ_TO_WRITE_DELAY = find_delay((CL_nCK + tCCD + 3'd2 - CWL_nCK), READ_SLOT, WRITE_SLOT); //2
    localparam READ_TO_READ_DELAY = 0;
    localparam READ_TO_PRECHARGE_DELAY =  find_delay(ns_to_nCK(tRTP), READ_SLOT, PRECHARGE_SLOT);  //1
    localparam WRITE_TO_WRITE_DELAY = 0;
    localparam WRITE_TO_READ_DELAY = find_delay((CWL_nCK + 3'd4 + ns_to_nCK(tWTR)), WRITE_SLOT, READ_SLOT); //4
    localparam WRITE_TO_PRECHARGE_DELAY = find_delay((CWL_nCK + 3'd4 + ns_to_nCK(tWR)), WRITE_SLOT, PRECHARGE_SLOT); //5
    localparam WRITE_TO_ODT_OFF = find_delay((CWL_nCK + 3'd4 + ns_to_nCK(tWR)), WRITE_SLOT, PRECHARGE_SLOT); //5
     
    //MARGIN_BEFORE_ANTICIPATE is the number of columns before the column
    //end when the anticipate can start
    //the worst case scenario is when the anticipated bank needs to be precharged
    //thus the margin must satisfy tRP (for precharge) and tRCD (for activate). 
    //Also, worscase is when the anticipated bank still has the leftover of the 
    //WRITE_TO_PRECHARGE_DELAY thus consider also this.
    localparam MARGIN_BEFORE_ANTICIPATE = PRECHARGE_TO_ACTIVATE_DELAY + ACTIVATE_TO_WRITE_DELAY + WRITE_TO_PRECHARGE_DELAY;
    localparam STAGE2_DATA_DEPTH = ($rtoi($floor((CWL_nCK - (3 - WRITE_SLOT + 1))/4.0 ))) + 1; //this is always >= 1
    localparam READ_DELAY = $rtoi($floor((CL_nCK - (3 - READ_SLOT + 1))/4.0 ));
    localparam DELAY_BEFORE_WRITE_LEVEL_FEEDBACK = STAGE2_DATA_DEPTH + ns_to_cycles(tWLO+tWLOE) + 10;  //plus 10 controller clocks for possible bus latency and 
                                                                                            //the delay for receiving feedback DQ from IOBUF -> IDELAY -> ISERDES
    
    reg[(1<<BA_BITS)-1:0] bank_status_q, bank_status_d; //bank_status[bank_number]: determine current state of bank (1=active , 0=idle)
    reg[ROW_BITS-1:0] bank_active_row_q[(1<<BA_BITS)-1:0], bank_active_row_d[(1<<BA_BITS)-1:0]; //bank_active_row[bank_number] = stores the active row address in the specified bank
    integer index;
     //clear bank_status and bank_active_row to zero
    initial begin
        for(index=0; index< (1<<BA_BITS); index=index+1) begin
            bank_status_q[index] = 0;  
            bank_status_d[index] = 0;
            bank_active_row_q[index] = 0; 
            bank_active_row_d[index] = 0; 
        end
    end

    //pipeline stage 1 regs
    reg stage1_pending = 0;
    reg stage1_we = 0;
    reg[wb_data_bits - 1:0] stage1_data = 0;
    reg[COL_BITS-1:0] stage1_col = 0;
    reg[BA_BITS-1:0] stage1_bank = 0;
    reg[ROW_BITS-1:0] stage1_row = 0;
    reg[COL_BITS-1:0] stage1_next_col = 0;
    reg[BA_BITS-1:0] stage1_next_bank = 0;
    reg[ROW_BITS-1:0] stage1_next_row = 0;
    
    //pipeline stage 2 regs
    reg stage2_pending = 0;
    reg stage2_we = 0;
    reg [wb_data_bits - 1:0] stage2_data [STAGE2_DATA_DEPTH:0];
    reg [wb_data_bits*2 - 1:0] stage2_data_unaligned = 0;
    reg [wb_data_bits - 1:0] unaligned_data = 0;
    //reset data
    initial begin
        for(index = 0; index <= STAGE2_DATA_DEPTH; index = index+1) begin
            stage2_data[index] <=  0;               
        end
    end
    reg[COL_BITS-1:0] stage2_col = 0;
    reg[BA_BITS-1:0] stage2_bank = 0;
    reg[ROW_BITS-1:0] stage2_row = 0;
    
    //delay counter for every banks
    reg[3:0] delay_before_precharge_counter_q[(1<<BA_BITS)-1:0], delay_before_precharge_counter_d[(1<<BA_BITS)-1:0]; //delay counters
    reg[3:0] delay_before_activate_counter_q[(1<<BA_BITS)-1:0], delay_before_activate_counter_d[(1<<BA_BITS)-1:0] ;
    reg[3:0] delay_before_write_counter_q[(1<<BA_BITS)-1:0], delay_before_write_counter_d[(1<<BA_BITS)-1:0] ;
    reg[3:0] delay_before_read_counter_q[(1<<BA_BITS)-1:0] , delay_before_read_counter_d[(1<<BA_BITS)-1:0] ;
    reg[3:0] delay_before_odt_off_q, delay_before_odt_off_d;
    reg[3:0] delay_before_read_ack_q, delay_before_read_ack_d;
    //set all delay counters to zero
     initial begin
        for(index=0; index<(1<<BA_BITS); index=index+1) begin
            delay_before_precharge_counter_q[index] = 0;  
            delay_before_activate_counter_q[index] = 0;
            delay_before_write_counter_q[index] = 0; 
            delay_before_read_counter_q[index] = 0; 
        end
        delay_before_odt_off_q = 0;
        delay_before_read_ack_q = 0;
    end
    
    //commands to be sent to PHY (4 slots per controller clk cycle)
    (* keep *) reg[CMD_LEN-1:0] cmd_q[3:0], cmd_d[3:0];
    //set all commands to all 1's makig CS_n high (thus commands are initially NOP)
    initial begin
        for(index=0; index< 4; index=index+1) begin
            cmd_q[index] = -1;
            cmd_d[index] = -1;
        end
    end
    reg cmd_odt_q = 0, cmd_odt, cmd_ck_en, cmd_reset_n;  
    reg o_wb_stall_d;
    reg o_wb_ack_d;
    reg pipe_stall;
    reg precharge_slot_busy;
    reg activate_slot_busy;
    reg[1:0] write_dqs_q;
    reg write_dqs_d;
    reg[STAGE2_DATA_DEPTH+1:0] write_dqs;
    reg write_dqs_val;
    reg write_dq_q, write_dq_d;
    reg[STAGE2_DATA_DEPTH+1:0] write_dq;
    // FOR PHY INTERFACE
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
                DONE_CALIBRATE = 14;
                
     localparam STORED_DQS_SIZE = 5, //must be >= 2           
                REPEAT_DQS_ANALYZE = 5; // repeat DQS read to find the accurate starting position of DQS
                
    wire[(DQ_BITS*LANES)-1:0] oserdes_data, odelay_data, idelay_data, read_dq;
    wire[LANES-1:0] odelay_dqs, read_dqs, idelay_dqs;
    wire[7:0] dqs_Q[LANES-1:0];//
    wire idelayctrl_rdy;
    reg[LANES-1:0] odelay_ce=0, odelay_inc=0, odelay_ld=0;
    reg[LANES-1:0] idelay_ce=0, idelay_inc=0, idelay_ld=0;
    wire oserdes_dqs;
    genvar gen_index;
    reg[CMD_LEN-1:0] aligned_cmd;
    wire[CMD_LEN-1:0] oserdes_cmd;
    wire[CMD_LEN-1:0] cmd;
    reg[1:0] serial_index,serial_index_q;
    wire[DQ_BITS*LANES*8-1:0] iserdes_data;
    wire[7:0] test_Q[LANES-1:0];
    wire test_OFB;
    reg[LANES-1:0] bitslip;
    
    reg[$clog2(DONE_CALIBRATE):0] state_calibrate;
    reg[STORED_DQS_SIZE*8-1:0] dqs_store = 0;
    reg[$clog2(STORED_DQS_SIZE):0] dqs_count_repeat = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_start_index = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_start_index_stored = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index = 0;
    reg[$clog2(REPEAT_DQS_ANALYZE):0] dqs_start_index_repeat=0;
    reg[1:0] train_delay;
    reg[CMD_LEN-1:0] cmd_reset_seq[3:0];
    reg[3:0] delay_before_read_data = 0;
    reg[$clog2(DELAY_BEFORE_WRITE_LEVEL_FEEDBACK):0] delay_before_write_level_feedback = 0;
    reg initial_dqs = 0;
    reg[$clog2(DQ_BITS*LANES):0] lane = 0;
    reg[7:0] dqs_bitslip_arrangement = 0;
    reg[3:0] added_read_pipe_max = 0;
    reg[3:0] added_read_pipe[LANES - 1:0];
    
    reg[(READ_DELAY + 1 + 2 + 1):0] shift_reg_read_pipe_q, shift_reg_read_pipe_d; ///1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
    reg index_read_pipe; //tells which delay_read_pipe will be updated 
    reg[1:0] index_wb_data; //tells which o_wb_data_q will be sent to o_wb_data
    reg[15:0] delay_read_pipe[1:0]; //delay when each lane will retrieve iserdes_data
    reg[wb_data_bits - 1:0] o_wb_data_q[1:0]; //store data retrieved from iserdes_data to be sent to o_wb_data
    reg[15:0] o_wb_ack_read_q;
 
    reg write_calib_stb = 0;
    reg write_calib_we = 0;
    reg[3:0] write_calib_col = 0;
    reg[63:0] write_calib_data = 0;
    reg write_calib_odt = 0;
    reg write_calib_dqs = 0;
    reg write_calib_dq = 0;
    reg prev_write_level_feedback = 1;
    reg[63:0] read_data_store = 0;
    reg[127:0] write_pattern = 0;
    reg[$clog2(64):0] data_start_index = 0;     
    reg calib_stall;      
    //process request transaction 
    always @(posedge i_controller_clk, negedge i_rst_n) begin
        if(!i_rst_n ) begin
            o_wb_stall <= 1'b1; 
            calib_stall <= 1'b1;
            //set stage 1 to 0
            stage1_pending <= 0;
            stage1_we <= 0;
            stage1_col <= 0;
            stage1_bank <= 0;
            stage1_row <= 0;
            stage1_next_bank <= 0;
            stage1_next_row <= 0;
            stage1_next_col <= 0;
            //set stage2 to 0
            stage2_pending <= 0;
            stage2_we <= 0;
            stage2_col <= 0;
            stage2_bank <= 0;
            stage2_row <= 0;
            delay_before_odt_off_q <= 0;
            delay_before_read_ack_q <= 0;
            cmd_odt_q <= 0;
            stage2_data_unaligned <= 0;
            unaligned_data <= 0;
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
            for(index = 0; index <= STAGE2_DATA_DEPTH; index = index+1) begin
                stage2_data[index] <=  0;               
            end
        end
        
        // can only start accepting requests  when reset is done
        else if(reset_done) begin 
            o_wb_stall <= o_wb_stall_d || state_calibrate != DONE_CALIBRATE;
            calib_stall <= o_wb_stall_d;
            cmd_odt_q <= cmd_odt;

            //update delay counter 
            for(index=0; index< (1<<BA_BITS); index=index+1) begin
                delay_before_precharge_counter_q[index] <= delay_before_precharge_counter_d[index];  
                delay_before_activate_counter_q[index] <= delay_before_activate_counter_d[index];
                delay_before_write_counter_q[index] <= delay_before_write_counter_d[index]; 
                delay_before_read_counter_q[index] <= delay_before_read_counter_d[index]; 
            end
            delay_before_odt_off_q <= delay_before_odt_off_d;
            delay_before_read_ack_q <= delay_before_read_ack_d;
            //update cmd
            for( index=0; index < 4; index=index+1) begin
                cmd_q[index] <= cmd_d[index];
            end
            //update bank status and active row
            for(index=0; index < (1<<BA_BITS); index=index+1) begin
                bank_status_q[index] <= bank_status_d[index];
                bank_active_row_q[index] <= bank_active_row_d[index];
            end

            //refresh sequence is on-going
            if(!instruction[REF_IDLE]) begin
                //all banks will be in idle after refresh
                for( index=0; index < (1<<BA_BITS); index=index+1) begin
                    bank_status_q[index] <= 0;  
                end
                //no transaction will be pending during refresh
                o_wb_stall <= 1'b1; 
                cmd_odt_q <= 1'b0;
                stage2_pending <= 0;
                stage1_pending <= 0;
            end
            //move pipeline forward 
            else if(!pipe_stall) begin
                stage2_pending <= stage1_pending;
                stage1_pending <= 0; //move pending request to stage 2 thus stage 1 will not be pending anymore UNLESS there is a wb request at this clk cycle
            end
            
            //if pipeline is not stalled, move pipeline forward
            if(!pipe_stall) begin
                stage2_we <= stage1_we;
                stage2_col <= stage1_col;
                stage2_bank <= stage1_bank;
                stage2_row <= stage1_row;
                stage2_data_unaligned <= stage1_data;
                //stage2_data -> shiftreg(CWL) -> OSERDES(DDR) -> ODELAY -> RAM
            end
            
            
            // when not in refresh, transaction can only be processed when i_wb_cyc is high and not stall
            if(i_wb_cyc && !o_wb_stall) begin 
                //stage1 will not do the request (pending low) when the
                //request is on the same bank as the current request. This
                //will ensure stage1 bank will be different from stage2 bank
                stage1_pending <= i_wb_stb;//actual request flag
                stage1_we <= i_wb_we; //write-enable
                stage1_col <= { i_wb_addr[(COL_BITS- $clog2(serdes_ratio*2)-1):0], {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                stage1_bank <=  i_wb_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2))]; //bank_address
                stage1_row <= i_wb_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) ]; //row_address
                //stage1_next_bank will not increment unless stage1_next_col
                //overwraps due to MARGIN_BEFORE_ANTICIPATE. Thus, anticipated
                //precharge and activate will happen only at the end of the
                //current column with a margin dictated by
                //MARGIN_BEFORE_ANTICIPATE  
                {stage1_next_row , stage1_next_bank, stage1_next_col[COL_BITS-1:$clog2(serdes_ratio*2)] } <= i_wb_addr + MARGIN_BEFORE_ANTICIPATE; //anticipated next row and bank to be accessed 
                stage1_data <= i_wb_data;
            end
            else if(write_calib_stb) begin
                stage1_pending <= write_calib_stb;//actual request flag
                stage1_we <= write_calib_we; //write-enable
                stage1_col <= write_calib_col; //column address (n-burst word-aligned)
                stage1_bank <=  0; //bank_address
                stage1_row <= 0; //row_address
                {stage1_next_row , stage1_next_bank, stage1_next_col[COL_BITS-1:$clog2(serdes_ratio*2)] } <= 0; //anticipated next row and bank to be accessed 
                stage1_data <= write_calib_data;
            end
            {unaligned_data, stage2_data[0]} <= (stage2_data_unaligned << data_start_index) | unaligned_data;
            for(index = 1; index <= STAGE2_DATA_DEPTH; index = index+1) begin
                stage2_data[index] <=  stage2_data[index-1];              
            end
        end
    end

                  
    always @(posedge i_controller_clk, negedge i_rst_n) begin
        if(!i_rst_n ) begin
            shift_reg_read_pipe_q <= 0;
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
  
        end
        else begin
            write_dqs_val <= write_dqs_d || write_dqs_q[0];
            write_dqs_q[0] <= write_dqs_d;
            write_dqs_q[1] <= write_dqs_q[0];
            write_dqs[0] <= write_dqs_d || write_dqs_q[1] || write_dqs_q[0]; //high for 3 clk cycles
            
            write_dq_q <= write_dq_d;
            write_dq[0] <= write_dq_d || write_dq_q; //high for 2 clk cycles
            for(index = 1; index <= STAGE2_DATA_DEPTH+1; index = index+1) begin //increase by 1 to accomodate postamble            
                write_dqs[index] <= write_dqs[index-1]; 
            end 
            for(index = 1; index <= STAGE2_DATA_DEPTH+1; index = index+1) begin //increase by 1 to accomodate postamble            
                write_dq[index] <= write_dq[index-1]; 
            end 
            
            shift_reg_read_pipe_q <= shift_reg_read_pipe_d;
            for(index = 0; index < 2; index = index + 1) begin
                delay_read_pipe[index] <= (delay_read_pipe[index] >> 1);
            end
            if(shift_reg_read_pipe_q[1]) begin //delay is over and data is now strating to release from iserdes BUT NOT YET ALIGNED
                index_read_pipe <= !index_read_pipe; //control which delay_read_pipe would get updated (we have 3 pipe to store read data)ss
                delay_read_pipe[index_read_pipe][added_read_pipe_max] <= 1'b1; //update delay_read_pipe
            end
            for(index = 0; index < LANES; index = index + 1) begin
                //if(delay_before_read_ack_q == (added_read_pipe_max - added_read_pipe[index] + 1)) begin //same lane
                if(delay_read_pipe[0][added_read_pipe_max != added_read_pipe[index]]) begin //same lane
                    o_wb_data_q[0][((DQ_BITS*LANES)*0 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*0 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*1 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*1 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*2 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*2 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*3 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*3 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*4 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*4 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*5 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*5 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*6 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*6 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[0][((DQ_BITS*LANES)*7 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*7 + 8*index) +: 8]; //update each lane of the burst
                end
                if(delay_read_pipe[1][added_read_pipe_max != added_read_pipe[index]]) begin
                    o_wb_data_q[1][((DQ_BITS*LANES)*0 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*0 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*1 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*1 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*2 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*2 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*3 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*3 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*4 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*4 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*5 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*5 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*6 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*6 + 8*index) +: 8]; //update each lane of the burst
                    o_wb_data_q[1][((DQ_BITS*LANES)*7 + 8*index) +: 8] <= iserdes_data[((DQ_BITS*LANES)*7 + 8*index) +: 8]; //update each lane of the burst
                end

                if(o_wb_ack_read_q[0]) begin 
                    index_wb_data <= !index_wb_data;
                end
                for(index = 0; index < 15; index = index + 1) begin
                    o_wb_ack_read_q[index] <= o_wb_ack_read_q[index+1];
                end
                o_wb_ack_read_q[added_read_pipe_max] <= shift_reg_read_pipe_q[0];
            end
       end
    end
    assign o_wb_ack = o_wb_ack_read_q[0];
    assign o_wb_data = o_wb_data_q[index_wb_data];
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
        o_wb_ack_d = 0; //ack goes high for every r/w request
        o_wb_stall_d = 0; //wb_stall going high is determined on stage 1 (higher priority), wb_stall going low is determined at stage2 (lower priority)
        pipe_stall = 0; //pipe_stall will follow i_wb_stall(so stall when stage 2 needs delay) but goes low after actual read/write request (move pipe forward when stage2 finishes request) 
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
        cmd_d[READ_SLOT] = {(!issue_read_command), CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS}{1'b0}}};  
        cmd_d[WRITE_SLOT] = {(!issue_write_command),CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS}{1'b0}}}; 
        cmd_d[ACTIVATE_SLOT] = {1'b1,CMD_ACT[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS}{1'b0}}}; 
        //for(index=1; index < 4; index=index+1) begin
         //       cmd_d[index][CMD_ODT] = (delay_before_odt_off_q != 0)? 1'b1: 1'b0; //ODT remains the same value
        //end
            
        // decrement delay counters for every bank
        for(index=0; index< (1<<BA_BITS); index=index+1) begin
            delay_before_precharge_counter_d[index] = (delay_before_precharge_counter_q[index] == 0)? 0: delay_before_precharge_counter_q[index] - 1;
            delay_before_activate_counter_d[index] = (delay_before_activate_counter_q[index] == 0)? 0: delay_before_activate_counter_q[index] - 1;
            delay_before_write_counter_d[index] = (delay_before_write_counter_q[index] == 0)? 0:delay_before_write_counter_q[index] - 1;
            delay_before_read_counter_d[index] = (delay_before_read_counter_q[index] == 0)? 0:delay_before_read_counter_q[index] - 1;
        end
        //delay_before_odt_off_d = (delay_before_odt_off_q == 0)? 0 : delay_before_odt_off_q - 1;
        delay_before_read_ack_d = (delay_before_read_ack_q == 0)? 0 : delay_before_read_ack_q - 1;
        o_wb_ack_d = delay_before_read_ack_q == 1;

        shift_reg_read_pipe_d = shift_reg_read_pipe_q>>1;
        //if there is a pending request, issue the appropriate commands
        if(stage2_pending) begin 
            o_wb_stall_d = o_wb_stall; 
            pipe_stall = o_wb_stall;
            //right row is already active so go straight to read/write
            if(bank_status_q[stage2_bank] &&  bank_active_row_q[stage2_bank] == stage2_row) begin //read/write operation
                //write request
                if(stage2_we && delay_before_write_counter_q[stage2_bank] == 0) begin       
                    o_wb_stall_d = 0;         
                    o_wb_ack_d = 1;
                    pipe_stall = 0; //move pipeline forward since write access is already done
                    cmd_odt = 1'b1;
                    //set-up delay before precharge, read, and write
                    delay_before_precharge_counter_d[stage2_bank] = WRITE_TO_PRECHARGE_DELAY;
                    delay_before_read_counter_d[stage2_bank] = WRITE_TO_READ_DELAY;     
                    delay_before_write_counter_d[stage2_bank] = WRITE_TO_WRITE_DELAY;
                    //delay_before_odt_off_d = STAGE2_DATA_DEPTH;
                    //issue read command
                    if(COL_BITS <= 10) begin
                        cmd_d[WRITE_SLOT] = {1'b0, CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS-4'd11}{1'b0}} , 1'b0 , stage2_col[9:0]};  
                    end
                    else begin
                        cmd_d[WRITE_SLOT] =  {1'b0, CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS-4'd12}{1'b0}} , stage2_col[10] , 1'b0 , stage2_col[9:0]};  
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
                    o_wb_stall_d = 0;     
                    pipe_stall = 0; //move pipeline forward since read access is already done
                    cmd_odt = 1'b0;
                    //set-up delay before precharge, read, and write
                    delay_before_precharge_counter_d[stage2_bank] = READ_TO_PRECHARGE_DELAY;
                    delay_before_read_counter_d[stage2_bank] = READ_TO_READ_DELAY;     
                    delay_before_write_counter_d[stage2_bank] = READ_TO_WRITE_DELAY;
                    //delay_before_read_ack_d = READ_DELAY + 1 + 2 + 1; ///1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
                    delay_before_read_ack_d = READ_DELAY + 1 + 2 + 1; ///1=issue command delay (OSERDES delay), 2 =  ISERDES delay, 1 = to register output
                 
                    shift_reg_read_pipe_d[READ_DELAY + 1 + 2 + 1] = 1'b1; 
                    //issue read command
                    if(COL_BITS <= 10) begin
                        cmd_d[READ_SLOT] = {1'b0, CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS-4'd11}{1'b0}} , 1'b0 , stage2_col[9:0]};  
                    end
                    else begin
                        cmd_d[READ_SLOT] =  {1'b0, CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, {{ROW_BITS+BA_BITS-4'd12}{1'b0}} , stage2_col[10] , 1'b0 , stage2_col[9:0]};  
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
                //set-up delay before read and write
                delay_before_read_counter_d[stage2_bank] = ACTIVATE_TO_READ_DELAY;
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
                cmd_d[PRECHARGE_SLOT] = {1'b0, CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, { {{ROW_BITS-4'd11}{1'b0}} , 1'b0 , stage2_row[9:0] } };
                //update bank status and active row
                bank_status_d[stage2_bank] = 1'b0; 
            end
        end //end of stage 2 pending

        //pending request on stage 1
        if(stage1_pending && (stage1_next_bank != stage2_bank)) begin
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
                delay_before_read_counter_d[stage1_next_bank] = ACTIVATE_TO_READ_DELAY;
                delay_before_write_counter_d[stage1_next_bank] = ACTIVATE_TO_WRITE_DELAY;
                cmd_d[PRECHARGE_SLOT] = {1'b0, CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank, { {{ROW_BITS-4'd11}{1'b0}} , 1'b0 , stage1_next_row[9:0] } };
                bank_status_d[stage1_next_bank] = 1'b0; 
            end //end of anticipate precharge
            
            //anticipated bank is idle so do activate
            else if(!bank_status_q[stage1_next_bank] && delay_before_activate_counter_q[stage1_next_bank] == 0 && !activate_slot_busy) begin 
                //set-up delay before read and write
                delay_before_read_counter_d[stage1_next_bank] = ACTIVATE_TO_READ_DELAY;
                delay_before_write_counter_d[stage1_next_bank] = ACTIVATE_TO_WRITE_DELAY;
                cmd_d[ACTIVATE_SLOT] = {1'b0, CMD_ACT[2:0] , cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank , stage1_next_row};
                bank_status_d[stage1_next_bank] = 1'b1;
                bank_active_row_d[stage1_next_bank] = stage1_next_row;
            end //end of anticipate activate
            
        end //end of stage1 pending

        if(stage1_pending) begin
            // Stage1 bank and row will determine if transaction will be
            // stalled (bank is idle OR wrong row is active).  
            if(!bank_status_q[stage1_bank] || (bank_status_q[stage1_bank] && bank_active_row_q[stage1_bank] != stage1_row)) begin 
                o_wb_stall_d = 1;
            end
            //different request type will need a delay of more than 1 clk cycle so stall the pipeline 
            if(stage1_we != stage2_we) o_wb_stall_d = 1;
        end
        
            
            
    // Vivado Benchmarking
    // LUT = 1254, FF = 2878
    // WNS = 0.924 ns (200MHz clk)
    end //end of always block
    
   //////////////////////////////////////////////////////////////////////// PHY Interface ////////////////////////////////////////////////////////////////////////////////////////////////////

    /*
    always @(posedge i_ddr3_clk) begin
        if(!i_rst_n) begin
            serial_index <=0;
        end
        else begin 
            serial_index <= serial_index + 1;
            serial_index_q <= serial_index;
        end
    end
    */
    //PHY cmd 
    generate
        for(gen_index = 0; gen_index < CMD_LEN; gen_index = gen_index + 1) begin
            // OSERDESE2: Output SERial/DESerializer with bitslip
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            OSERDESE2 #(
                .DATA_RATE_OQ("SDR"), // DDR, SDR
                .DATA_WIDTH(4), // Parallel data width (2-8,10,14)
                .INIT_OQ(1'b0) // Initial value of OQ output (1'b0,1'b1)
            )
            OSERDESE2_cmd(
                .OFB(oserdes_cmd[gen_index]), // 1-bit output: Feedback path for data
                .OQ(), // 1-bit output: Data path output
                .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                .D1(cmd_d[0][gen_index]),
                .D2(cmd_d[1][gen_index]),
                .D3(cmd_d[2][gen_index]),
                .D4(cmd_d[3][gen_index]),
                .OCE(1), // 1-bit input: Output data clock enable
                .RST(!i_rst_n) // 1-bit input: Reset
            );
            // End of OSERDESE2_inst instantiation
        

        (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
        //Delay the DQ
        // Delay resolution: 1/(32 x 2 x F REF ) = 78.125ps
        ODELAYE2 #(
            .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
            .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter to 5ps ("TRUE"), Reduced power but high jitter 9ns ("FALSE")
            .ODELAY_TYPE("FIXED"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
            .ODELAY_VALUE(0), // Output delay tap setting (0-31)
            .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
            .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
        )
        ODELAYE2_cmd (
            .CNTVALUEOUT(), // 5-bit output: Counter value output
            .DATAOUT(cmd[gen_index]), // 1-bit output: Delayed data/clock output
            .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
            .CE(0), // 1-bit input: Active high enable increment/decrement input
            .CINVCTRL(0), // 1-bit input: Dynamic clock inversion input
            .CLKIN(0), // 1-bit input: Clock delay input
            .CNTVALUEIN(0), // 5-bit input: Counter value input
            .INC(0), // 1-bit input: Increment / Decrement tap delay input
            .LD(0), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                        // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
            .LDPIPEEN(0), // 1-bit input: Enables the pipeline register to load data
            .ODATAIN(oserdes_cmd[gen_index]), // 1-bit input: Output delay data input
            .REGRST(0) // 1-bit input: Active-high reset tap-delay input
        );
        end
    endgenerate 

    assign  {cs_n, ras_n, cas_n, we_n, odt, ck_en, reset_n, ba_addr, addr} = cmd;

            
    // PHY data
    generate
        // data: oserdes -> odelay -> iobuf
        for(gen_index = 0; gen_index < (DQ_BITS*LANES); gen_index = gen_index + 1) begin
            // OSERDESE2: Output SERial/DESerializer with bitslip
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            OSERDESE2 #(
                .DATA_RATE_OQ("DDR"), // DDR, SDR
                .DATA_WIDTH(8), // Parallel data width (2-8,10,14)
                .INIT_OQ(1'b0) // Initial value of OQ output (1'b0,1'b1)
            )
            OSERDESE2_data(
                .OFB(oserdes_data[gen_index]), // 1-bit output: Feedback path for data
                .OQ(), // 1-bit output: Data path output
                .CLK(i_ddr3_clk), // 1-bit input: High speed clock
                .CLKDIV(i_controller_clk), // 1-bit input: Divided clock
                // D1 - D8: 1-bit (each) input: Parallel data inputs (1-bit each)
                .D1(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*0]),
                .D2(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*1]),
                .D3(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*2]),
                .D4(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*3]),
                .D5(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*4]),
                .D6(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*5]),
                .D7(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*6]),
                .D8(stage2_data[STAGE2_DATA_DEPTH-1][gen_index + (DQ_BITS*LANES)*7]),
                .OCE(1), // 1-bit input: Output data clock enable
                .RST(!i_rst_n) // 1-bit input: Reset
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
                .ODELAY_TYPE("VARIABLE"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .ODELAY_VALUE(4), // Output delay tap setting (0-31)
                .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
            )
            ODELAYE2_data (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(odelay_data[gen_index]), // 1-bit output: Delayed data/clock output
                .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                .CE(odelay_ce[$rtoi($floor(gen_index/8))]), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(0), // 1-bit input: Dynamic clock inversion input
                .CLKIN(0), // 1-bit input: Clock delay input
                .CNTVALUEIN(0), // 5-bit input: Counter value input
                .INC(odelay_inc[$rtoi($floor(gen_index/8))]), // 1-bit input: Increment / Decrement tap delay input
                .LD(odelay_ld[$rtoi($floor(gen_index/8))]), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                            // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                .LDPIPEEN(0), // 1-bit input: Enables the pipeline register to load data
                .ODATAIN(oserdes_data[gen_index]), // 1-bit input: Output delay data input
                .REGRST(0) // 1-bit input: Active-high reset tap-delay input
            );

            // IOBUF: Single-ended Bi-directional Buffer
            //All devices
            // Xilinx HDL Libraries Guide, version 13.4
            IOBUF #(
                .DRIVE(12), // Specify the output drive strength
                .IBUF_LOW_PWR("TRUE"), // Low Power - "TRUE", High Performance = "FALSE"
                .IOSTANDARD("SSTL18"), // Specify the I/O standard
                .SLEW("FAST") // Specify the output slew rate
            ) IOBUF_data (
                .O(read_dq[gen_index]),// Buffer output
                .IO(dq[gen_index]), // Buffer inout port (connect directly to top-level port)
                .I(odelay_data[gen_index]), // Buffer input
                .T(!write_dq[STAGE2_DATA_DEPTH+1]) // 3-state enable input, high=read, low=write
            );
            
            // IDELAYE2: Input Fixed or Variable Delay Element
            // 7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
            IDELAYE2 #(
                .DELAY_SRC("IDATAIN"), // Delay input (IDATAIN, DATAIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), //Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .IDELAY_TYPE("VARIABLE"), //FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .IDELAY_VALUE(4), //Input delay tap setting (0-31)
                .PIPE_SEL("FALSE"),  //Select pipelined mode, FALSE, TRUE
                .REFCLK_FREQUENCY(200.0), //IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") //DATA, CLOCK input signal
            )
            IDELAYE2_data (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(idelay_data[gen_index]), // 1-bit output: Delayed data output
                .C(i_controller_clk), // 1-bit input: Clock input
                .CE(idelay_ce[$rtoi($floor(gen_index/8))]), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(0),// 1-bit input: Dynamic clock inversion input
                .CNTVALUEIN(0), // 5-bit input: Counter value input
                .DATAIN(), //1-bit input: Internal delay data input
                .IDATAIN(read_dq[gen_index]), // 1-bit input: Data input from the I/O
                .INC(idelay_inc[$rtoi($floor(gen_index/8))]), // 1-bit input: Increment / Decrement tap delay input
                .LD(idelay_ld[$rtoi($floor(gen_index/8))]), // 1-bit input: Load IDELAY_VALUE input
                .LDPIPEEN(0), // 1-bit input: Enable PIPELINE register to load data input
                .REGRST(0) // 1-bit input: Active-high reset tap-delay input
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
                .IOBDELAY("NONE"), // NONE, BOTH, IBUF, IFD
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
                .Q1(iserdes_data[(DQ_BITS*LANES)*7 + gen_index]),//56
                .Q2(iserdes_data[(DQ_BITS*LANES)*6 + gen_index]), //48
                .Q3(iserdes_data[(DQ_BITS*LANES)*5 + gen_index]),
                .Q4(iserdes_data[(DQ_BITS*LANES)*4 + gen_index]),   
                .Q5(iserdes_data[(DQ_BITS*LANES)*3 + gen_index]),
                .Q6(iserdes_data[(DQ_BITS*LANES)*2 + gen_index]),
                .Q7(iserdes_data[(DQ_BITS*LANES)*1 + gen_index]), 
                .Q8(iserdes_data[(DQ_BITS*LANES)*0 + gen_index]),
                // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
                .SHIFTOUT1(),
                .SHIFTOUT2(),
                .BITSLIP(bitslip[$rtoi($floor(gen_index/8))]),
                // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
                // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
                // to Q8 output ports will shift, as in a barrel-shifter operation, one
                // position every time Bitslip is invoked (DDR operation is different from
                // SDR).
                // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
                .CE1(1),
                .CE2(1),
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
                .D(idelay_data[gen_index]), // 1-bit input: Data input
                .DDLY(), // 1-bit input: Serial data from IDELAYE2
                .OFB(), // 1-bit input: Data feedback from OSERDESE2
                .OCLKB(), // 1-bit input: High speed negative edge output clock
                .RST(!i_rst_n), // 1-bit input: Active high asynchronous reset
                // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
                .SHIFTIN1(),
                .SHIFTIN2()
            );
            // End of ISERDESE2_inst instantiation
  
        end
        //800MHz = 
        // dqs: odelay -> iobuf
        for(gen_index = 0; gen_index < LANES; gen_index = gen_index + 1) begin
        
            
            // ODELAYE2: Output Fixed or Variable Delay Element
            // 7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
            //Delay the DQ
            ODELAYE2 #(
                .DELAY_SRC("ODATAIN"), // Delay input (ODATAIN, CLKIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), // Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .ODELAY_TYPE("VARIABLE"), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .ODELAY_VALUE(8), // delay to align odelay_dqs to oserdes_dqs due to 600ps insertion delay: (1/800MHz - 600ps)/78.125ps = 8.32 taps
                .REFCLK_FREQUENCY(200.0), // IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") // DATA, CLOCK input signal
            )
            ODELAYE2_dqs (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(odelay_dqs[gen_index]), // 1-bit output: Delayed data/clock output
                .C(i_controller_clk), // 1-bit input: Clock input, when using OSERDESE2, C is connected to CLKDIV
                .CE(odelay_ce[gen_index]), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(0), // 1-bit input: Dynamic clock inversion input
                .CLKIN(0), // 1-bit input: Clock delay input
                .CNTVALUEIN(0), // 5-bit input: Counter value input
                .INC(odelay_inc[gen_index]), // 1-bit input: Increment / Decrement tap delay input
                .LD(odelay_ld[gen_index]), // 1-bit input: Loads ODELAY_VALUE tap delay in VARIABLE mode, in VAR_LOAD or
                            // VAR_LOAD_PIPE mode, loads the value of CNTVALUEIN
                .LDPIPEEN(0), // 1-bit input: Enables the pipeline register to load data
                .ODATAIN(oserdes_dqs), // 1-bit input: Output delay data input
                .REGRST(0) // 1-bit input: Active-high reset tap-delay input
            );
  
            
            // IOBUFDS: Differential Bi-directional Buffer
            //7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            IOBUFDS #(
                .DIFF_TERM("FALSE"), // Differential Termination ("TRUE"/"FALSE")
                .IBUF_LOW_PWR("TRUE"), // Low Power - "TRUE", High Performance = "FALSE"
                .IOSTANDARD("SSTL18"), // Specify the I/O standard. CONSULT WITH DATASHEET
                .SLEW("FAST") // Specify the output slew rate
            ) IOBUFDS_inst (
                .O(read_dqs[gen_index]), // Buffer output
                .IO(dqs[gen_index]), // Diff_p inout (connect directly to top-level port)
                .IOB(dqs_n[gen_index]), // Diff_n inout (connect directly to top-level port)
                .I(odelay_dqs[gen_index]), // Buffer input
                .T(!write_dqs[STAGE2_DATA_DEPTH]) // 3-state enable input, high=input, low=output
            ); // End of IOBUFDS_inst instantiation
            
            // IDELAYE2: Input Fixed or Variable Delay Element
            // 7 Series
            // Xilinx HDL Libraries Guide, version 13.4
            (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
            IDELAYE2 #(
                .DELAY_SRC("IDATAIN"), // Delay input (IDATAIN, DATAIN)
                .HIGH_PERFORMANCE_MODE("TRUE"), //Reduced jitter ("TRUE"), Reduced power ("FALSE")
                .IDELAY_TYPE("VARIABLE"), //FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
                .IDELAY_VALUE(8), //Input delay tap setting (0-31)
                .PIPE_SEL("FALSE"),  //Select pipelined mode, FALSE, TRUE
                .REFCLK_FREQUENCY(200.0), //IDELAYCTRL clock input frequency in MHz (190.0-210.0).
                .SIGNAL_PATTERN("DATA") //DATA, CLOCK input signal
            )
            IDELAYE2_dqs (
                .CNTVALUEOUT(), // 5-bit output: Counter value output
                .DATAOUT(idelay_dqs[gen_index]), // 1-bit output: Delayed data output
                .C(i_controller_clk), // 1-bit input: Clock input
                .CE(idelay_ce[gen_index]), // 1-bit input: Active high enable increment/decrement input
                .CINVCTRL(0),// 1-bit input: Dynamic clock inversion input
                .CNTVALUEIN(0), // 5-bit input: Counter value input
                .DATAIN(), //1-bit input: Internal delay data input
                .IDATAIN(read_dqs[gen_index]), // 1-bit input: Data input from the I/O
                .INC(idelay_inc[gen_index]), // 1-bit input: Increment / Decrement tap delay input
                .LD(idelay_ld[gen_index]), // 1-bit input: Load IDELAY_VALUE input
                .LDPIPEEN(0), // 1-bit input: Enable PIPELINE register to load data input
                .REGRST(0) // 1-bit input: Active-high reset tap-delay input
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
                .IOBDELAY("NONE"), // NONE, BOTH, IBUF, IFD
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
                .Q1(dqs_Q[gen_index][7]),
                .Q2(dqs_Q[gen_index][6]),
                .Q3(dqs_Q[gen_index][5]),
                .Q4(dqs_Q[gen_index][4]),   
                .Q5(dqs_Q[gen_index][3]),
                .Q6(dqs_Q[gen_index][2]),
                .Q7(dqs_Q[gen_index][1]),
                .Q8(dqs_Q[gen_index][0]),
                // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
                .SHIFTOUT1(),
                .SHIFTOUT2(),
                .BITSLIP(bitslip[gen_index]),
                // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
                // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
                // to Q8 output ports will shift, as in a barrel-shifter operation, one
                // position every time Bitslip is invoked (DDR operation is different from
                // SDR).
                // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
                .CE1(1),
                .CE2(1),
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
                .D(idelay_dqs[gen_index]), // 1-bit input: Data input
                .DDLY(), // 1-bit input: Serial data from IDELAYE2
                .OFB(), // 1-bit input: Data feedback from OSERDESE2
                .OCLKB(), // 1-bit input: High speed negative edge output clock
                .RST(!i_rst_n), // 1-bit input: Active high asynchronous reset
                // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
                .SHIFTIN1(),
                .SHIFTIN2()
            );
            // End of ISERDESE2_inst instantiation
            
                      
            //ISERDES train
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
                .Q1(test_Q[gen_index][7]),
                .Q2(test_Q[gen_index][6]),
                .Q3(test_Q[gen_index][5]),
                .Q4(test_Q[gen_index][4]),   
                .Q5(test_Q[gen_index][3]),
                .Q6(test_Q[gen_index][2]),
                .Q7(test_Q[gen_index][1]),
                .Q8(test_Q[gen_index][0]),
                // SHIFTOUT1-SHIFTOUT2: 1-bit (each) output: Data width expansion output ports
                .SHIFTOUT1(),
                .SHIFTOUT2(),
                .BITSLIP(bitslip[gen_index]),
                // 1-bit input: The BITSLIP pin performs a Bitslip operation synchronous to
                // CLKDIV when asserted (active High). Subsequently, the data seen on the Q1
                // to Q8 output ports will shift, as in a barrel-shifter operation, one
                // position every time Bitslip is invoked (DDR operation is different from
                // SDR).
                // CE1, CE2: 1-bit (each) input: Data register clock enable inputs
                .CE1(1),
                .CE2(1),
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
                .OFB(test_OFB), // 1-bit input: Data feedback from OSERDESE2
                .OCLKB(), // 1-bit input: High speed negative edge output clock
                .RST(!i_rst_n), // 1-bit input: Active high asynchronous reset
                // SHIFTIN1-SHIFTIN2: 1-bit (each) input: Data width expansion input ports
                .SHIFTIN1(),
                .SHIFTIN2()
            );
            // End of ISERDESE2_inst instantiation
        end
     endgenerate 
     
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
        .OCE(1), // 1-bit input: Output data clock enable
        .RST(!i_rst_n) // 1-bit input: Reset
    );
    // End of OSERDESE2_inst instantiation  
     
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
        .D1(1'b1 && write_dqs_val),
        .D2(1'b0 && write_dqs_val),
        .D3(1'b1 && write_dqs_val),
        .D4(1'b0 && write_dqs_val),
        .D5(1'b1 && write_dqs_val),
        .D6(1'b0 && write_dqs_val),
        .D7(1'b1 && write_dqs_val),
        .D8(1'b0 && write_dqs_val),
        .OCE(1), // 1-bit input: Output data clock enable
        .RST(!i_rst_n) // 1-bit input: Reset
    );
    // End of OSERDESE2_inst instantiation

    // IDELAYCTRL: IDELAYE2/ODELAYE2 Tap Delay Value Control
    // 7 Series
    // Xilinx HDL Libraries Guide, version 13.4
    (* IODELAY_GROUP = 0 *) // Specifies group name for associated IDELAYs/ODELAYs and IDELAYCTRL
    IDELAYCTRL IDELAYCTRL_inst (
        .RDY(idelayctrl_rdy), // 1-bit output: Ready output
        .REFCLK(i_controller_clk), // 1-bit input: Reference clock input.The frequency of REFCLK must be 200 MHz to guarantee the tap-delay value specified in the applicable data sheet.
        .RST(!i_rst_n) // 1-bit input: Active high reset input, To ,Minimum Reset pulse width is 52ns
    );
    // End of IDELAYCTRL_inst instantiation

         

    //set all commands to all 1's makig CS_n high (thus commands are initially NOP)
    initial begin
        for(index=0; index< 4; index=index+1) begin
            cmd_reset_seq[index] = -1;
            cmd_reset_seq[index][CMD_ODT] = 0;
        end
    end
     
    always @(posedge i_controller_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            state_calibrate <= IDLE;
            train_delay <= 0;
            dqs_store <= 0;
            dqs_count_repeat <= 0;
            dqs_start_index <= 0;
            dqs_target_index <= 0;
            for(index = 0; index < LANES; index = index + 1) begin
                idelay_ce[index] <= 0;
                odelay_ce[index] <= 0;
                idelay_inc[index] <= 0;
                odelay_inc[index] <= 0;
                bitslip[index] <= 0;
            end
            initial_dqs <= 1;
            lane <= 0;
            dqs_bitslip_arrangement <= 0;
            write_calib_dqs <= 0;
            write_calib_dq <= 0;
            write_calib_odt <= 0;
            prev_write_level_feedback <= 1;
            write_calib_stb <= 0;//actual request flag
            write_calib_we <= 0; //write-enable
            write_calib_col <= 0;
            write_calib_data <= 0;
            read_data_store <= 0;
            write_pattern = 0;
            data_start_index <= 0;
        end
        else begin
            write_calib_stb <= 0;//actual request flag
            write_calib_we <= 0; //write-enable
            write_calib_col <= 0;
            write_calib_data <= 0;
            skip_reset_seq_delay <= 0;
            write_calib_dqs <= 0;
            write_calib_dq <= 0;
            train_delay <= (train_delay==0)? 0:(train_delay - 1);
            delay_before_read_data <= (delay_before_read_data == 0)? 0: delay_before_read_data - 1;
            delay_before_write_level_feedback <= (delay_before_write_level_feedback == 0)? 0: delay_before_write_level_feedback - 1;
            if(initial_dqs) dqs_target_index <= dqs_start_index_stored[0]? dqs_start_index_stored + 2: dqs_start_index_stored + 1;
            for(index=0; index < LANES; index=index+1) begin
                idelay_ce[index] <= 0;
                odelay_ce[index] <= 0;
                idelay_inc[index] <= 0;
                odelay_inc[index] <= 0;
                bitslip[index] <= 0;
            end
            for(index=0; index < LANES; index=index+1) begin
                    cmd_reset_seq[index] <= -1;
                    cmd_reset_seq[index][CMD_ODT] <= 0;
            end

            //set all cmd_d to NOP
            for(index=0; index < 4; index=index+1) begin
                    cmd_reset_seq[index] <= -1;
                    cmd_reset_seq[index][CMD_ODT] <= 0;
            end
            
            // FSM
            case(state_calibrate) 
                IDLE: if(idelayctrl_rdy && instruction_address == 13) begin //we are now inside instruction 15 with maximum delay
                        state_calibrate <= BITSLIP_DQS_TRAIN_1;
                        lane <= 0;
                      end
  BITSLIP_DQS_TRAIN_1: if(train_delay == 0) begin
                        /* Bitslip cannot be asserted for two consecutive CLKDIV cycles; Bitslip must be
                        deasserted for at least one CLKDIV cycle between two Bitslip assertions.The user 
                        logic should wait for at least two CLKDIV cycles in SDR mode or three CLKDIV cycles 
                        in DDR mode, before analyzing the received data pattern and potentially issuing 
                        another Bitslip command. If the ISERDESE2 is reset, the Bitslip logic is also reset
                        and returns back to its initial state.
                        */
                        if(test_Q[lane] == 8'b0111_1000) begin //initial arrangement
                            state_calibrate <= MPR_READ;
                            initial_dqs <= 1;
                            dqs_start_index_repeat <= 0;
                            dqs_start_index_stored <= 0;
                        end                
                        else begin
                            bitslip[lane] <= 1;
                            train_delay <= 3;
                        end        
                      end
                      
            MPR_READ: begin //align the incoming DQS during reads to the controller clock 
                             //skip_reset_seq_delay = 1;
                             //cmd_reset_seq[0] =  {1'b0, CMD_RD[2:0], 1'b0, 1'b1, 1'b1, MR3_RD_ADDR}; //read command
                             //issue_read_command = 1;
                             delay_before_read_data <= READ_DELAY + 1 + 2 + 1; ///1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
                             state_calibrate <= COLLECT_DQS;
                             dqs_count_repeat <= 0;
                      end    
                      
        COLLECT_DQS: if(delay_before_read_data == 0) begin
                        dqs_store <= {dqs_Q[lane], dqs_store[(STORED_DQS_SIZE*8-1):8]}; 
                        dqs_count_repeat = dqs_count_repeat + 1;
                        if(dqs_count_repeat == STORED_DQS_SIZE) begin
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
                            //dqs_start_index_stored <= dqs_start_index;
                            state_calibrate <= MPR_READ;
                        end
                      end 
                      else begin
                        dqs_start_index <= dqs_start_index + 1;
                      end

        CALIBRATE_DQS: if(dqs_start_index_stored == dqs_target_index) begin
                            added_read_pipe[lane] = dqs_target_index[$clog2(STORED_DQS_SIZE*8)-1:3] + (dqs_target_index[2:0] >= 5);
                            dqs_bitslip_arrangement <= 16'b0011_1100_0011_1100 >> dqs_target_index[2:0];
                            state_calibrate <= BITSLIP_DQS_TRAIN_2;
                       end
                       else begin
                            idelay_ce[lane] <= 1;
                            idelay_inc[lane] <= 1;
                            state_calibrate <= MPR_READ;
                       end

  BITSLIP_DQS_TRAIN_2: if(train_delay == 0) begin //train again the ISERDES to capture the DQ correctly
                            if(test_Q[lane] == dqs_bitslip_arrangement) begin
                                if(lane == LANES - 1) begin
                                    skip_reset_seq_delay <= 1;
                                    lane <= 0;
                                    prev_write_level_feedback <= 1'b1;
                                    state_calibrate <= START_WRITE_LEVEL;
                                 end
                                 else begin
                                     lane <= lane + 1;
                                     state_calibrate <= BITSLIP_DQS_TRAIN_1;
                                 end
                                 added_read_pipe_max <= added_read_pipe_max > added_read_pipe[lane]? added_read_pipe_max:added_read_pipe[lane];
                            end
                            else begin
                                bitslip[lane] <= 1;
                                train_delay <= 3;
                            end
                       end
                    
    START_WRITE_LEVEL: if(instruction_address == 17) begin
                            write_calib_dqs <= 1'b1;
                            write_calib_odt <= 1'b1;
                            delay_before_write_level_feedback <= DELAY_BEFORE_WRITE_LEVEL_FEEDBACK;
                            state_calibrate <= WAIT_FOR_FEEDBACK;
                       end
                       
    WAIT_FOR_FEEDBACK: if(delay_before_write_level_feedback == 0) begin
                            prev_write_level_feedback <= iserdes_data[lane<<3];
                            if({prev_write_level_feedback, iserdes_data[lane<<3]} == 2'b01) begin
                                if(lane == LANES - 1) begin
                                    write_calib_odt <= 0;
                                    skip_reset_seq_delay <= 1;
                                    state_calibrate <= ISSUE_WRITE_1;
                                end
                                else begin
                                    lane <= lane + 1;
                                    prev_write_level_feedback <= 1'b1;
                                    state_calibrate <= START_WRITE_LEVEL; 
                                end
                            end
                            else begin
                                odelay_ce[lane] <= 1'b1;
                                odelay_inc[lane] <= 1'b1;
                                state_calibrate <= START_WRITE_LEVEL; 
                            end
                        end     
                                  
        ISSUE_WRITE_1: if(instruction_address == 22) begin
                        write_calib_stb <= 1;//actual request flag
                        write_calib_we <= 1; //write-enable
                        write_calib_col <= 0;
                        write_calib_data <= 64'h77_66_55_44_33_22_11_00; 
                        state_calibrate <= ISSUE_WRITE_2;
                       end    
        ISSUE_WRITE_2: begin
                        write_calib_stb <= 1;//actual request flag
                        write_calib_we <= 1; //write-enable
                        write_calib_col <= 8;
                        write_calib_data <= 64'hff_ee_dd_cc_bb_aa_99_88;
                        state_calibrate <= ISSUE_READ;
                       end    
                                    
          ISSUE_READ: if(!o_wb_stall_d) begin
                        write_calib_stb <= 1;//actual request flag
                        write_calib_we <= 0; //write-enable
                        state_calibrate <= READ_DATA;
                      end   
                      
           READ_DATA: if(o_wb_ack_read_q[0]) begin
                         read_data_store <= o_wb_data;
                         state_calibrate <= ANALYZE_DATA;
                         data_start_index <= 0;
                         write_pattern <= 128'hff_ee_dd_cc_bb_aa_99_88_77_66_55_44_33_22_11_00;
                      end              
                        
        ANALYZE_DATA: if(write_pattern[data_start_index +: 64] == read_data_store) begin            
                        state_calibrate <= DONE_CALIBRATE;
                      end 
                      else begin
                        data_start_index <= data_start_index + 8;
                      end             
       DONE_CALIBRATE: state_calibrate <= DONE_CALIBRATE;

            endcase
        end
    end      
    assign issue_read_command = (state_calibrate == MPR_READ);
    assign issue_write_command = 0;
   //////////////////////////////////////////////////////////////////////// End of PHY Interface  //////////////////////////////////////////////////////////////////////// 
   
   
    //Good reference for intialization and ODT
    //https://www.systemverilog.io/design/ddr4-initialization-and-calibration/
    //notes:
    //ODT must be statically held low at all times (except for write of course) when RTT_NOM is enabled via MR1.
    
    //////////////////////////////////////////////////////////////////////// FUNCTIONS ////////////////////////////////////////////////////////////////////////////////////////////////////
    //convert nanoseconds time input to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] ns_to_cycles (input integer ns); //output is set at same length as a MRS command (19 bits) to maximize the time slot
        ns_to_cycles = $rtoi($ceil(ns*1.0/CONTROLLER_CLK_PERIOD)); //Without $rtoi: YOSYS ERROR: Non-constant expression in constant function
    endfunction

    //convert nCK input (number of DDR3 clock cycles) to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] nCK_to_cycles (input integer nCK); //Without $rtoi: YOSYS ERROR: syntax error, unexpected TOK_REAL
        nCK_to_cycles = $rtoi($ceil(nCK*1.0/serdes_ratio)) ; 
    endfunction
    
    
    //convert nanoseconds time input  to number of DDR clock cycles (referenced to DDR3_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] ns_to_nCK (input integer ns); 
        ns_to_nCK = $rtoi($ceil(ns*1.0/DDR3_CLK_PERIOD)); //Without $rtoi: YOSYS ERROR: Non-constant expression in constant function
    endfunction
    
    //convert nanoseconds time input  to number of DDR clock cycles (referenced to DDR3_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] nCK_to_ns (input integer nCK); 
        nCK_to_ns = $rtoi($ceil(nCK*1.0*DDR3_CLK_PERIOD)); //Without $rtoi: YOSYS ERROR: Non-constant expression in constant function
    endfunction
    
       // functions used to infer some localparam values
    function integer max(input integer a, input integer b);
        if(a >= b) max = a;
        else    max = b;
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
        integer slot_number;
        integer delay;
        integer read_slot, write_slot, anticipate_activate_slot, anticipate_precharge_slot;
        begin
            // find read command slot number
            delay = CL_nCK;
            for(slot_number = 0 ;  delay != 0 ; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            read_slot = slot_number[1:0];
            
            // find write command slot number
            delay = CWL_nCK;
            for(slot_number = 0 ;  delay != 0; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            write_slot = slot_number[1:0];
            
            // find anticipate activate command slot number
            if(CL_nCK > CWL_nCK) slot_number = read_slot;
            else slot_number = write_slot;
            delay = ns_to_nCK(tRCD);
            for(slot_number = slot_number;  delay != 0; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            anticipate_activate_slot = slot_number[1:0];
            // if computed anticipate_activate_slot is same with either write_slot or read_slot, decrement slot number until 
            while(anticipate_activate_slot[1:0] == write_slot[1:0] || anticipate_activate_slot[1:0] == read_slot[1:0]) begin 
                anticipate_activate_slot[1:0] = anticipate_activate_slot[1:0] - 1'b1;
            end
            
            //the remaining slot will be for precharge command
            anticipate_precharge_slot = 0;
            while(anticipate_precharge_slot == write_slot || anticipate_precharge_slot == read_slot || anticipate_precharge_slot == anticipate_activate_slot) begin
                anticipate_precharge_slot[1:0] = anticipate_precharge_slot[1:0]  - 1'b1;
            end
            case(cmd)
                CMD_RD: get_slot = read_slot;
                CMD_WR: get_slot = write_slot;
                CMD_ACT: get_slot = anticipate_activate_slot;
                CMD_PRE: get_slot = anticipate_precharge_slot;
            endcase
        end
    endfunction
    
    //find the delay to be used by delay_before_xxxx_counter. 
    // - delay_nCK = delay required between the two commands in DDR3 clock cycles
    // - start_slot = slot number of the first command
    // - end_slot = slot number of the second command
    // returns the number of controller clock cycles to satisfy the delay required between the two commands
    function integer find_delay(input integer delay_nCK, input integer start_slot, input integer end_slot);
        integer k; //error: variable declaration assignments are only allowed at the module level
        begin
            k = 0;
            while( ((4 - start_slot) + end_slot + 4*k) < delay_nCK) begin
                k = k + 1;
            end
            find_delay = k;
        end
    endfunction
    
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifndef YOSYS
    ///YOSYS: System task `$display' called with invalid/unsupported format specifier
    initial begin
        $display("Test ns_to_cycles() function:");
        $display("\tns_to_cycles(15) = 3 = %0d [exact]", ns_to_cycles(15) );
        $display("\tns_to_cycles(14.5) = 3 = %0d [round-off]", ns_to_cycles(14.5) );
        $display("\tns_to_cycles(11) = 3 = %0d [round-up]\n", ns_to_cycles(11) );
        
        $display("Test nCK_to_cycles() function:");
        $display("\tns_to_cycles(16) = 4 = %0d [exact]", nCK_to_cycles(16) );
        $display("\tns_to_cycles(15) = 4 = %0d [round-off]", nCK_to_cycles(15) );
        $display("\tns_to_cycles(13) = 4 = %0d [round-up]\n", nCK_to_cycles(13) );
        
        $display("Test ns_to_nCK() function:");
        $display("\tns_to_cycles(15) = 12 = %0d [exact]", ns_to_nCK(15) );
        $display("\tns_to_cycles(14.875) = 12 = %0d [round-off]", ns_to_nCK(14.875) );
        $display("\tns_to_cycles(13.875) = 12 = %0d [round-up]", ns_to_nCK(13.875) );
        $display("\tns_to_nCK(tRCD) =  11 = %0d [WRONG]", ns_to_nCK(tRCD));
        $display("\ttRTP =  7.5 = %f ", tRTP);
        $display("\tns_to_nCK(tRTP) =  6= %f [WRONG]\n", ns_to_nCK(tRTP) );
        
        $display("Test nCK_to_ns() function:");
        $display("\tns_to_cycles(4)  = 5 = %0d [exact]", nCK_to_ns(4) );
        $display("\tns_to_cycles(14.875) = 4 = %0d [round-off]", nCK_to_ns(3) );
        $display("\tns_to_cycles(13.875) = 7 = %0d [round-up]\n", nCK_to_ns(5) );
        
        $display("Test nCK_to_ns() function:");
        $display("\tns_to_cycles(4)  = 5 = %0d [exact]", nCK_to_ns(4) );
        $display("\tns_to_cycles(14.875) = 4 = %0d [round-off]", nCK_to_ns(3) );
        $display("\tns_to_cycles(13.875) = 7 = %0d [round-up]\n", nCK_to_ns(5) );
        
        
        $display("Test $floor() function:");
        $display("\t$floor(5/2) = 2.5 = %0d", $floor(5/2) );
        $display("\t$floor(9/4) = 2.25 = %0d", $floor(9/4) );
        $display("\t$floor(9/4) = 2 = %0d", $floor(8/4) );
        $display("\t$floor(9/5) = 1.8 = %0d\n", $floor(9/5) );

        $display("\nDELAY_COUNTER_WIDTH = %0d", DELAY_COUNTER_WIDTH);
        $display("DELAY_SLOT_WIDTH = %0d", DELAY_SLOT_WIDTH);

        //$display("$bits(instruction):%0d - $bits(CMD_MRS):%0d - $bits(MR0):%0d  =  5 = %0d",  $bits(instruction), $bits(CMD_MRS) , $bits(MR0), ($bits(instruction) - $bits(CMD_MRS) - $bits(MR0)));
        $display("serdes_ratio = %0d",serdes_ratio);
        $display("wb_addr_bits = %0d",wb_addr_bits);
        $display("wb_data_bits = %0d",wb_data_bits);
        $display("wb_sel_bits = %0d\n\n",wb_sel_bits);
        //$display("request_row_width = %0d =  %0d", ROW_BITS,  $bits(i_wb_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) ]));
        //$display("request_col_width = %0d = %0d", COL_BITS, $bits({ i_wb_addr[(COL_BITS- $clog2(serdes_ratio*2)-1):0], {{$clog2(serdes_ratio*2)}{1'b0}} }));
        //$display("request_bank_width = %0d = %0d", BA_BITS, $bits(i_wb_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2))]));

        $display("READ_SLOT = %0d", READ_SLOT);
        $display("WRITE_SLOT = %0d", WRITE_SLOT);
        $display("ACTIVATE_SLOT = %0d", ACTIVATE_SLOT);
        $display("PRECHARGE_SLOT = %0d", PRECHARGE_SLOT);
        
        $display("\n\nDELAYS:");
        $display("\tns_to_nCK(tRCD): %0d", ns_to_nCK(tRCD));
        $display("\tns_to_nCK(tRP): %0d", ns_to_nCK(tRP));
        $display("\tns_to_nCK(tRTP): %0d", ns_to_nCK(tRTP));
        $display("\ttCCD: %0d", tCCD);
        $display("\t(CL_nCK + tCCD + 3'd2 - CWL_nCK): %0d", (CL_nCK + tCCD + 3'd2 - CWL_nCK));
        $display("\t(CWL_nCK + 3'd4 + ns_to_nCK(tWR)): %0d", (CWL_nCK + 3'd4 + ns_to_nCK(tWR)));
        $display("\t(CWL_nCK + 3'd4 + ns_to_nCK(tWTR)): %0d", (CWL_nCK + 3'd4 + ns_to_nCK(tWTR)));
        $display("\t$signed(4'b1100)>>>4: %b", $signed(4'b1100) >>> 4);
        
        $display("\n\nPRECHARGE_TO_ACTIVATE_DELAY = 3 = %0d", PRECHARGE_TO_ACTIVATE_DELAY);
        $display("ACTIVATE_TO_WRITE_DELAY = 3 = %0d", ACTIVATE_TO_WRITE_DELAY);
        $display("ACTIVATE_TO_READ_DELAY = 2 = %0d", ACTIVATE_TO_READ_DELAY);
        $display("READ_TO_WRITE_DELAY = 2 = %0d", READ_TO_WRITE_DELAY);
        $display("READ_TO_READ_DELAY = 0 = %0d", READ_TO_READ_DELAY);
        $display("READ_TO_PRECHARGE_DELAY = 1 =%0d", READ_TO_PRECHARGE_DELAY);
        $display("WRITE_TO_WRITE_DELAY = 0 = %0d", WRITE_TO_WRITE_DELAY);
        $display("WRITE_TO_READ_DELAY = 4 = %0d", WRITE_TO_READ_DELAY);
        $display("WRITE_TO_PRECHARGE_DELAY = 5 = %0d", WRITE_TO_PRECHARGE_DELAY);
        
    end
`endif
    
    
`ifdef  FORMAL
    initial assume(!i_rst_n); 
    
    always @* begin
        //assert(tMOD + tZQinit > nCK_to_cycles(tDLLK)); //Initialization sequence requires that tDLLK is satisfied after MRS to mode register 0 and ZQ calibration
        assert(MR0[18] != 1'b1); //last Mode Register bit should never be zero 
        assert(MR1[18] != 1'b1); //(as this is used for A10-AP control for non-MRS 
        assert(MR2[18] != 1'b1); //commands in the reset sequence)
        assert(MR3[18] != 1'b1);
        assert(DELAY_COUNTER_WIDTH <= $bits(MR0)); //bitwidth of mode register should be enough for the delay counter
        assert(($bits(instruction) - $bits(CMD_MRS) - $bits(MR0)) == 5 ); //sanity checking to ensure 5 bits is allotted for extra instruction {reset_finished, use_timer , stay_command , cke , reset_n } 
        assert(DELAY_SLOT_WIDTH >= DELAY_COUNTER_WIDTH); //width occupied by delay timer slot on the reset rom must be able to occupy the maximum possible delay value on the reset sequence
    end
    
    reg f_past_valid = 0; 
    always @(posedge i_controller_clk)  f_past_valid <= 1;
    
    
    //The idea below is sourced from https://zipcpu.com/formal/2019/11/18/genuctrlr.html
    //We will form a packet of information describing each instruction as it goes through the pipeline and make assertions along the way.
    //2-stage Pipeline: f_addr (update address)  ->  f_read (read instruction from rom)  
    reg[$bits(instruction_address) - 1: 0] f_addr = 0, f_read = 0 ; 
    reg[$bits(instruction) - 1:0] f_read_inst = INITIAL_RESET_INSTRUCTION;
    
    //pipeline stage logic: f_addr (update address)  ->  f_read (read instruction from rom)  
    always @(posedge i_controller_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            f_addr <= 0;
            f_read <= 0;
        end
        else if((delay_counter == 1 || !instruction[USE_TIMER]) /*&& !reset_done*/ )begin //move the pipeline forward when counter is about to go zero and we are not yet at end of reset sequence
            f_addr <= (f_addr == 15)? 12:f_addr + 1;
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
                if( $past(delay_counter_is_zero) && $past(f_read_inst[USE_TIMER]) /*&& !$past(reset_done)*/)  
                    `ifndef FORMAL_COVER
                        assert(delay_counter == (f_read_inst[DELAY_COUNTER_WIDTH - 1:0]));
                    `else
                        //use fixed low value delay to cover the whole reset seqeunce using formal verification
                        if(instruction[DELAY_COUNTER_WIDTH - 1:0] > `COVER_DELAY) assert(delay_counter == `COVER_DELAY); 
                        //use delay from rom if that is smaller than the COVER_DELAY macro
                        else assert(delay_counter == f_read_inst[DELAY_COUNTER_WIDTH - 1:0]); 
                    `endif

                 //delay_counter_is_zero can be high when counter is zero and current instruction needs delay
                if($past(f_read_inst[USE_TIMER]) /*&& !$past(reset_done)*/) assert( delay_counter_is_zero  == (delay_counter == 0) ); 
                 //delay_counter_is_zero will go high this cycle when we received a don't-use-timer instruction
                else if(!$past(f_read_inst[USE_TIMER]) /*&& !$past(reset_done)*/) assert(delay_counter_is_zero); 
                
                //we are on the middle of a delay thus all values must remain constant while only delay_counter changes (decrement)
                if(!delay_counter_is_zero) begin 
                    assert(f_addr == $past(f_addr));
                    assert(f_read == $past(f_read));
                    assert(f_read_inst == $past(f_read_inst));
                end
                
                //if delay is not yet zero and timer delay is enabled, then delay_counter should decrement
                if(!$past(delay_counter_is_zero) && $past(f_read_inst[USE_TIMER])) begin
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
            assert($past(f_read) <= 14); //only instruction address 0-to-13 is for reset sequence (reset_done is asserted at address 14)
                end
                
                //assert the relationship between the stages FOR REFRESH SEQUENCE
                else begin
                    if(f_read == 15) assert(f_addr == 12); //if current instruction is 15, then next instruction must be at 12 (instruction address wraps from 15 to 12)
                    else if(f_addr == 12) assert(f_read == 15); //if next instruction is at 12, then current instruction must be at 15 (instruction address wraps from 15 to 12)
                    else assert(f_read + 1 == f_addr); //if there is no need to wrap around, then instruction address must increment 
                    assert((f_read >= 12 && f_read <= 15) ); //refresh sequence is only on instruction address 12, 13, 14, and 15
                end
                
                // reset_done must retain high when it was already asserted once
                if($past(reset_done)) assert(reset_done);
                
                // reset is already done at address 14 and up
                if($past(f_read) >= 14 ) assert(reset_done);
                
                //if reset is done, the REF_IDLE must only be high at instruction address 14 (on the middle of tREFI)
                if(reset_done &&  f_read_inst[REF_IDLE]) assert(f_read == 14);
                    
            end

    end
    
    
    // assertions on the instructions stored on the rom
    (*anyconst*) reg[$bits(instruction_address) - 1: 0] f_const_addr;
    wire[$bits(instruction) - 1:0]  a= read_rom_instruction(f_const_addr); //retrieve an instruction based on engine's choice
    always @* begin
     //there MUST BE no instruction which USE_TIMER is high but delay is zero since it can cause the logic to lock-up (delay must be at least 1)    
    if(a[USE_TIMER]) begin
        assert( a[DELAY_COUNTER_WIDTH - 1:0] > 0);      
    end
    end
    
    
    //cover statements
    `ifdef FORMAL_COVER
    reg[3:0] f_count_refreshes = 0; //count how many refresh cycles had already passed
    always @(posedge i_controller_clk) begin
        if($past(f_read) == 15 && f_read == 12) f_count_refreshes = f_count_refreshes + 1; //every time address wrap around refresh is completed
    end
    always @(posedge i_controller_clk) begin
        cover(f_count_refreshes == 5);
        //cover($past(instruction[RST_DONE]) && !instruction[RST_DONE] && i_rst_n); //MUST FAIL: find an instance where RST_DONE will go low after it already goes high (except when i_rst_n is activated)
    end
    `endif
    
    always @* begin
        //make sure each command has distinct slot number (except for read/write which can have the same or different slot number)
        assert((WRITE_SLOT != ACTIVATE_SLOT != PRECHARGE_SLOT) && (READ_SLOT != ACTIVATE_SLOT != PRECHARGE_SLOT) );
        //make sure slot number for read command is correct
    end
    //create a formal assertion that says during refresh ack should be low always
    //make an assertion that there will be no request pending before actual refresh starts at instruction 4'd12
        
        
    reg[24:0] f_wb_inputs[31:0];
    reg[4:0] f_index = 0;
    reg[5:0] f_counter = 0;
    reg[9:0] f_reset_counter = 0;
    initial begin
    /*
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
        */
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
        
    end
    always @(posedge i_controller_clk) begin
            if(!o_wb_stall) begin
                f_index <= f_index + 1;
                f_counter <= 0;
            end
            else begin
                f_counter <= f_counter + 1;
            end
            if(o_wb_stall && i_rst_n) begin
                f_reset_counter = f_reset_counter + 1;
            end
            else f_reset_counter = 10;
    end
    
    always @* begin
        assume(i_wb_cyc == 1);
        assume(i_wb_stb == 1);
        if(f_past_valid) assume(i_rst_n);
        assume(i_wb_we == f_wb_inputs[f_index][24]);
        assume(i_wb_addr == f_wb_inputs[f_index][23:0]);
        cover(f_index == 12);
        //cover(f_reset_counter == 10);
    end
    

`endif
endmodule

