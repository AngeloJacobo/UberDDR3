// Background:
// This DDR3 controller will be used with a DDR3-1600 with Kintex 7 FPGA Board (XC7K160T-3FFG676E). 
// The goal will be to:
//  - Run this at 1600Mbps (Maximum Physical Interface (PHY) Rate for a 4:1 
//          memory controller based on "DC and AC Switching Characteristics" for Kintex 7)
//  - Parameterize everything
//  - Interface should be (nearly) bus agnostic   
//  - High (sustained) data throughput. Sequential writes should be able to continue without interruption 


`define FORMAL_COVER //change delay in reset sequence to fit in cover statement
`define COVER_DELAY 3 //fixed delay used in formal cover for reset sequence
`default_nettype none


// THESE DEFINES WILL BE MODIFIED AS PARAMETERS LATER ON
`define DDR3_1600_11_11_11 // DDR3-1600 (11-11-11) speed bin
`define RAM_1Gb //DDR3 Capacity
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
                wb_sel_bits = (DQ_BITS*LANES*serdes_ratio)*2 / 8
    ) 
    (
        input wire i_clk, i_rst_n, //200MHz input clock
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
        output reg o_wb_ack, //1 = read/write request has completed
        output reg[wb_data_bits - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output reg o_aux //for AXI-interface compatibility (returned upon ack)
        // PHY Interface (to be added later)
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
                         RESET_N = 23; //Reset_n to DDR3
                         
                         // ddr3_metadata partitioning
    localparam CMD_START = 4 + BA_BITS + ROW_BITS - 1, //4 is the width of a CMD, CMD_START is also the CS_n bit
                          BANK_START = BA_BITS + ROW_BITS - 1,
                          ROW_ADDRESS_START = ROW_BITS - 1;
                          
                          //3 stages 
    localparam PRECHARGE = 0,
                ACTIVATE = 1,
                READ_WRITE = 2;
    localparam READ_SLOT = get_slot(CMD_RD),
                WRITE_SLOT = get_slot(CMD_WR),
                ACTIVATE_SLOT = get_slot(CMD_ACT),
                PRECHARGE_SLOT = get_slot(CMD_PRE);

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
    localparam[0:0] MPR_EN = 1'b0; //MPR Enable: Enable MPR reads and calibration during initialization
    localparam[2:0] MR3_SEL = 3'b011; //MPR Selected
    localparam[18:0] MR3 = {MR3_SEL, 13'b0_0000_0000_0000, MPR_EN, MPR_LOC}; 

    // MR1 (JEDEC DDR3 doc pg. 27)
    localparam DLL_EN = 1'b0; //DLL Enable/Disable: Enabled(0)
    localparam[1:0] DIC = 2'b00; //Output Driver Impedance Control (IS THIS THE SAME WITH RTT_NOM???????????? Search later)
    localparam[2:0] RTT_NOM = 3'b011; //RTT Nominal: 40ohms (RQZ/6) is the impedance of the PCB trace
    localparam[0:0] WL_EN = 1'b0; //Write Leveling Enable: Disabled
    localparam[1:0] AL = 2'b00; //Additive Latency: Disabled
    localparam[0:0] TDQS = 1'b0; //Termination Data Strobe: Disabled (provides additional termination resistance outputs. When the TDQS function is disabled, the DM function is provided (vice-versa).TDQS function is only available for X8 DRAM and must be disabled for X4 and X16. 
    localparam[0:0]  QOFF = 1'b0; //Output Buffer Control: Enabled
    localparam[2:0] MR1_SEL = 3'b001; //Selected Mode Register
    localparam[18:0] MR1 = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, WL_EN, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};

    //MR0 (JEDEC DDR3 doc pg. 24)
    localparam[1:0] BL = 2'b00; //Burst Length: 8 (Fixed)
    localparam[3:0] CL = 4'b1100; //CAS Read Latency: 10, can support DDR-1600 speedbin 8-8-8, 9-9-9, and 10-10-10 (Check JEDEC DDR doc pg. 162) CREATE A FUNCTION FOR THIS
    localparam[0:0] RBT = 1'b0; //Read Burst Type: Nibble Sequential
    localparam[0:0] DLL_RST = 1'b1; //DLL Reset: Yes (this is self-clearing and must be applied after DLL enable)
    localparam[2:0] WR = WRA_mode_register_value($ceil(tWR/DDR3_CLK_PERIOD)); //Write recovery for autoprecharge (
    localparam[0:0] PPD = 1'b0; //DLL Control for Precharge PD: Slow exit (DLL off)
    localparam[2:0] MR0_SEL = 3'b000;
    localparam[18:0] MR0 = {MR0_SEL, 3'b000, PPD, WR, DLL_RST, 1'b0, CL[3:1], RBT, CL[0], BL};

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


    /////////////////////////////////////////////////////////// TIMING PARAMETERS ////////////////////////////////////////////////////////////////////////////////////

    localparam POWER_ON_RESET_HIGH      =       200_000; // 200us reset must be active at initialization
    localparam INITIAL_CKE_LOW      =       500_000; // 500us cke must be low before activating

    `ifdef DDR3_1600_11_11_11 //DDR3-1600 (11-11-11) speed bin
        localparam tRAS     =       35.0; // ns Minimum Active to Precharge command time
        localparam tRC      =       48.750; //ns Active to Active/Auto Refresh command time
        localparam tRCD     =       13.750; // ns Active to Read/Write command time
        localparam tRP      =       13.750; // ns Precharge command period
        
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
    localparam tDLLK = 512.0; //nCK DLL Locking time
    localparam[DELAY_SLOT_WIDTH - 1:0] tMOD = max(nCK_to_cycles(12), ns_to_cycles(15)); //cycles (controller)  Mode Register Set command update delay
    localparam[DELAY_SLOT_WIDTH - 1:0] tZQinit = max(nCK_to_cycles(512), ns_to_cycles(640));//cycles (controller)  Power-up and RESET calibration time
    localparam[DELAY_SLOT_WIDTH - 1:0] tZQoper = max(nCK_to_cycles(256), ns_to_cycles(320)); //cycles (controller) Normal operation Full calibration time
    localparam CL_nCK = 10;
    localparam CWL_nCK = 8;
    localparam DELAY_MAX_VALUE = ns_to_cycles(INITIAL_CKE_LOW); //Largest possible delay needed by the reset and refresh sequence
    localparam DELAY_COUNTER_WIDTH= $clog2(DELAY_MAX_VALUE); //Bitwidth needed by the maximum possible delay, this will be the delay counter width
    localparam DELAY_SLOT_WIDTH = $bits(MR0); //Bitwidth of the delay slot and mode register slot on the reset/refresh rom will be at the same size as the Mode Register

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
    function [27:0] read_rom_instruction(input[3:0] instruction_address);
        case(instruction_address) 
    
            4'd0: read_rom_instruction = {5'b01000 , CMD_NOP , ns_to_cycles(POWER_ON_RESET_HIGH)}; 
            //0. RESET# needs to be maintained low for minimum 200us with power-up initialization. CKE is pulled
                //“Low” anytime before RESET# being de-asserted (min. time 10 ns). .
            
            4'd1: read_rom_instruction =  {5'b01001 , CMD_NOP, ns_to_cycles(INITIAL_CKE_LOW)}; 
            //1. After RESET# is de-asserted, wait for another 500 us until CKE becomes active. During this time, the
                //DRAM will start internal state initialization; this will be done independently of external clocks. 
                // .... Also, a NOP or Deselect command must be registered (with tIS set up time to clock) before
                //CKE goes active.

            4'd2: read_rom_instruction = {5'b01011 , CMD_NOP, ns_to_cycles(tXPR)}; 
            //2. After CKE is being registered high, wait minimum of Reset CKE Exit time, tXPR.
            
            4'd3: read_rom_instruction = {5'b00011, CMD_MRS, MR2}; 
            //3. Issue MRS command to load MR2. 
            
            4'd4: read_rom_instruction = {5'b01011, CMD_NOP, nCK_to_cycles(tMRD)}; 
            //4. Delay of tMRD between MRS commands
            
            4'd5: read_rom_instruction = {5'b00011, CMD_MRS, MR3}; 
            //5. Issue MRS command to load MR3. Prior to enabling the MPR for read calibration, all banks must be in the idle state (all banks 
                // precharged and tRP met). Once the MPR is enabled, any subsequent RD or RDA commands will be redirected to the MultiPurpose Register. 
                
            4'd6: read_rom_instruction = {5'b01011, CMD_NOP, nCK_to_cycles(tMRD)}; 
            //6. Delay of tMRD between MRS commands
            
            4'd7: read_rom_instruction = {5'b00011, CMD_MRS, MR1}; 
            //7. Issue MRS command to load MR1 and enable DLL. 
            
            4'd8: read_rom_instruction = {5'b01011, CMD_NOP, nCK_to_cycles(tMRD)};
            //8. Delay of tMRD between MRS commands
            
            4'd9: read_rom_instruction = {5'b00011, CMD_MRS, MR0}; 
            //9. Issue MRS command to load MR0 and reset DLL.
            
            4'd10: read_rom_instruction = {5'b01011, CMD_NOP, tMOD};
            //10. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            4'd11: read_rom_instruction = {5'b01011, CMD_ZQC, tZQinit}; 
            //11. ZQ Calibration command is used to calibrate DRAM Ron & ODT values. ZQCL command triggers the calibration engine 
            //inside the DRAM and, once calibration is achieved, the calibrated values area transferred from the calibration engine to 
            //DRAM IO, which gets reflected as updated output driver
            
             // Perform first refresh and any subsequent refresh (so instruction 12 to 15 will be re-used for the refresh sequence)
            4'd12: read_rom_instruction = {5'b01011, CMD_PRE, ns_to_cycles(tRP)}; 
            //12. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            4'd13: read_rom_instruction = {5'b01011, CMD_REF, ns_to_cycles(tRFC)};
            //13. A delay between the Refresh Command and the next valid command, except NOP or DES, must be greater than or equal to the minimum 
            //Refresh cycle time tRFC(min) 
            
            4'd14: read_rom_instruction = {5'b11011, CMD_NOP, ns_to_cycles(tREFI)};
            //14. Reset ends now. The refresh interval also starts to count.
            
            4'd15: read_rom_instruction = {5'b01011, CMD_NOP, PRE_STALL_DELAY[DELAY_SLOT_WIDTH-1:0]}; 
            // 15. Extra delay needed before starting the refresh sequence. (this already sets the wishbone stall high to make sure no user request is on-going when refresh seqeunce starts)
            
            default: read_rom_instruction = {5'b00011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b0}}}; 
        endcase
    endfunction
    
    //initial reset instruction has low rst_n, low cke, and has delay of 5
    localparam INITIAL_RESET_INSTRUCTION = {5'b01000 , CMD_NOP , { {(DELAY_SLOT_WIDTH-3){1'b0}} , 3'd5} }; 
    
    reg[3:0] instruction_address = 0; //address for accessing rom instruction
    reg[27:0] instruction = INITIAL_RESET_INSTRUCTION; //instruction retrieved from reset instruction rom
    reg[ DELAY_COUNTER_WIDTH - 1:0] delay_counter = INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]; //counter used for delays
    reg delay_counter_is_zero = (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0); //counter is now zero so retrieve next delay
    reg reset_done = 0; //high if reset has already finished
    
    always @(posedge i_clk, negedge i_rst_n) begin
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
                    if(instruction[DELAY_COUNTER_WIDTH - 1:0] > `COVER_DELAY) delay_counter <= `COVER_DELAY; //use fixed low value delay to cover the whole reset seqeunce using formal verification
                    else delay_counter <= instruction[DELAY_COUNTER_WIDTH - 1:0] ; //use delay from rom if that is smaller than the COVER_DELAY macro
                `endif
                //RECEIVE THE COMMANDS
            end
            
            //else: decrement delay counter when current instruction needs delay
            else if(instruction[USE_TIMER]) delay_counter <= delay_counter - 1; 
            
            //delay_counter of 1 means we will need to update the delay_counter next clock cycle (delay_counter of zero) so we need to retrieve 
            //now the next instruction. The same thing needs to be done when current instruction does not need the timer delay.
            if(delay_counter == 1 || !instruction[USE_TIMER]) begin
                delay_counter_is_zero <= 1; 
                instruction <= read_rom_instruction(instruction_address);
                instruction_address <= (instruction_address == 4'd15)? 4'd12:instruction_address+1; //instruction_address 15 must wrap back to instruction_address 12 for the refresh sequence
            end
            //we are now on the middle of a delay 
            else delay_counter_is_zero <=0; 
            //instruction[RST_DONE] is non-persistent thus we need to register it once it goes high
            reset_done <= instruction[RST_DONE]? 1'b1:reset_done; 
        end
        
    end
    //////////////////////////////////////////////////////// Track Bank Status and Active Row ////////////////////////////////////////////////////////
    // 
    reg[(1<<BA_BITS)-1:0] bank_status; //bank_status[bank_number]: determine current state of bank (1=active , 0=idle)
    reg[ROW_BITS-1:0] bank_active_row[(1<<BA_BITS)-1:0]; //bank_active_row[bank_number] = stores the active row address in the specified bank
    integer index;
    
     //clear bank_status and bank_active_row to zero
    initial begin
        for(index=0; index< (1<<BA_BITS); index=index+1) begin
            bank_status[index] = 0;  
            bank_active_row[index] = 0; 
        end
    end
    
    
    reg request_pending = 0;
    reg request_we = 0;
    reg[COL_BITS-1:0] request_col = 0;
    reg[BA_BITS-1:0] request_bank = 0;
    reg[ROW_BITS-1:0] request_row = 0;
    reg[BA_BITS-1:0] next_bank = 0;
    reg[ROW_BITS-1:0] next_row = 0;
    localparam[ns_to_nCK(tRP):0] tRP_delay = {1'b1, {{ns_to_nCK(tRP)-(4-PRECHARGE_SLOT)}{1'b0}}};
    localparam[ns_to_nCK(tRCD):0] tRCD_delay = {1'b1, {{ns_to_nCK(tRCD)-(4-ACTIVATE_SLOT)}{1'b0}}};
	reg[$bits(tRP_thread)-1:0] delay_before_activate = -1; //initially all 1s, depends on tRP after executing precharge command
	reg[$bits(tRCD_delay)-1:0] delay_before_read_or_write = -1; //initially all 1s, depends on tRCD after executing activate command
	reg[31:0] delay_before_precharge = -1; //initially all 1s, depends on tRTP and tWR (start counts only after 8th data burst)
    reg[2:0] stage; //[2] = READ_WRITE, [1] = ACTIVATE, [0] = PRECHARGE
    reg[CMD_START:0] ddr3_metadata; //stores metadata of the command: {ddr3 command, bank address, row address}

    //process request transaction 
    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n ) begin
            o_wb_stall <= 1'b1; 
            request_pending <= 0;
            request_we <= 0;
            request_col <= 0;
            request_bank <= 0;
            request_row <= 0;
        end
        // can only start accepting requests  when reset is done
        else if(reset_done) begin
            //refresh sequence is on-going 
            if(!instruction[REF_IDLE]) begin 
                //all banks will be in idle after refresh
                for(index=0; index< (1<<BA_BITS); index=index+1) begin
                    bank_status[index] = 0;  
                end
                //no transaction will be pending during refresh
                o_wb_stall <= 1'b1; 
                request_pending <= 0;
                request_we <= 0;
                request_col <= 0;
                request_bank <= 0;
                request_row <= 0;
            end
            
            // when not in refresh, transaction can only be processed when i_wb_cyc is high and not stall
            if(i_wb_cyc && !o_wb_stall) begin 
                o_wb_stall <= i_wb_stb;  // accept request only when stb is high and stall is low 
                request_pending <= i_wb_stb; // accept request only when stb is high and stall is low 
                request_we <= i_wb_we; //write-enable
                request_col <= { i_wb_addr[(COL_BITS- $clog2(serdes_ratio*2)-1):0], {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                request_bank <=  i_wb_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2))]; //bank_address
                request_row <= i_wb_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) ]; //row_address
                {next_row , next_bank} <= i_wb_addr[ (wb_addr_bits-1) : (wb_addr_bits - ROW_BITS - BA_BITS) ]; //anticipated next row and bank to be accessed 
            end

            stage <= 3'b000;

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
            //                          tWR (after 8th data burst)
            //
            //
            //
		    // Example scenario on how this works:
            // Say we have done precharge this clock cycle, the delay before
            // the next activate is dictated by tRP. Say tRP needs 12nCK (DD3
            // clock cycles) and the slot number for precharge is 2:
            //  0  1  2  3
            // [ ][ ][P][0]
            // [0][0][0][0]
            // [0][0][0][0]
            // [0][0][1][ ]
            // [A][ ][ ][ ]
            // The 0s represent the delay and the 1 represents the end of the
            // tRP delay of 10nCK. Using shift register this is represented
            // as:
            // 1_0000000000 (10 zeroes, zeroes start from row after precharge 
            // cmd since the precharge command itself covers the 1st row delay)
            //
            // This shift register will be shifted by 4 arithmetically so that
            // the 1s on the MSB will be preserved. Now say the slot number of
            // activate command (ACTIVATE_SLOT) is 0, we will wait until the 
            // 1s in the thread reaches this slot WHICH MEANS THE DELAY IS OVER
            // FOR tRP AND THUS CAN START ACTIVATE:
            // 1_0000[0000] -> 11111_[0000] -> 1111111[1111]
            //
            // Notice how [1111] hits the slot 0 (assumed ACTIVATE_SLOT),
            // this signifies that the activate command can start anytime.
            // Notice also that since this is arithmetically right shifted the
            // 1s are preserved and the thread will remain all 1s until it is
            // overwritten

			delay_before_activate <= $signed(delay_before_activate) >>> 4; //shift right arithmetic (empty slots will be filled by 1s)
			delay_before_read_or_write <= $signed(delay_before_read_or_write) >>> 4; //shift right arithmetic (empty slots will be filled by 1s)
			delay_before_precharge <= $signed(delay_before_precharge) >>> 4; //shift right arithmetic (empty slots will be filled by 1s)
			
            //if there is a pending request, update the current stage
            if(request_pending) begin 
                //bank is not idle but wrong row is activated so do precharge
                if(bank_status[request_bank] && bank_active_row[request_bank] != request_row && delay_before_precharge[PRECHARGE_SLOT]) begin                    
                    stage <= 0;
                    stage <= stage[PRECHARGE_SLOT];
                    delay_before_activate <= tRP_delay; //use signed to turn MSB to 1s
                    bank_status[request_bank] = 1'b0; 
                end
                //bank is idle so activate it
                else if(!bank_status[request_bank] && delay_before_activate[ACTIVATE_SLOT]) begin 
                    stage <= 0;
                    stage <= stage[PRECHARGE_SLOT];
                    delay_before_read_or_write <= tRCD_delay;
                    bank_status[request_bank] <= 1'b1;
                    bank_active_row[request_bank] <= request_row;
                end
                //right row is already active so go straight to read/write
                else if(request_we && delay_before_read_or_write[READ_SLOT] || !request_we && delay_before_read_or_write[WRITE_SLOT]) begin//write operation
                    stage <= 0;
                    stage <= stage[PRECHARGE_SLOT];
                        // add delays needed before next precharge
				end
            end

            // Output commands to DDR3 based on stage value
            precharge_cmd = { !stage[PRECHARGE], CMD_PRE, request_bank, { {{ROW_BITS-4'd11}{1'b0}} , 1'b0 , request_row[9:0]} };
            activate_cmd = {!stage[ACTIVATE], CMD_ACT , request_bank , request_row};
            if(COL_BITS <= 10)
                read_write_cmd[BANK_START: 0] = { {{ROW_BITS-4'd11}{1'b0}} , 1'b0 , request_col[9:0]};  
            else
                read_write_cmd[BANK_START: 0] = { {{ROW_BITS-4'd12}{1'b0}} , request_col[10] , 1'b0 , request_col[9:0]};  

            cmd[PRECHARGE_SLOT] <= precharge_cmd; 
            cmd[ACTIVATE_SLOT] <= activate_cmd;
            cmd[READ_SLOT] <= {!(!request_we && stage[READ_WRITE]), CMD_RD, read_write_cmd};
            cmd[WRITE_SLOT] <= {!(request_we && stage[READ_WRITE]), CMD_WR, read_write_cmd} 
        end

    end


    //Good reference for intialization and ODT
    //https://www.systemverilog.io/design/ddr4-initialization-and-calibration/
    //notes:
    //ODT must be statically held low at all times (except for write of course) when RTT_NOM is enabled via MR1.
    
    //////////////////////////////////////////////////////////////////////// FUNCTIONS ////////////////////////////////////////////////////////////////////////////////////////////////////
    //convert nanoseconds time input to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] ns_to_cycles (input[DELAY_SLOT_WIDTH - 1:0] ns); //output is set at same length as a MRS command (19 bits) to maximize the time slot
        ns_to_cycles = $rtoi($ceil(ns*1.0/CONTROLLER_CLK_PERIOD)); //Without $rtoi: YOSYS ERROR: Non-constant expression in constant function
    endfunction

    //convert nCK input (number of DDR3 clock cycles) to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] nCK_to_cycles (input  nCK); //Without $rtoi: YOSYS ERROR: syntax error, unexpected TOK_REAL
        nCK_to_cycles = $rtoi($ceil(nCK*1.0/serdes_ratio)) ; 
    endfunction
    
    //convert nanoseconds time input  to number of DDR clock cycles (referenced to DDR3_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] ns_to_nCK (input[DELAY_SLOT_WIDTH - 1:0] ns); 
        ns_to_nCK = $rtoi($ceil(ns*1.0/DDR3_CLK_PERIOD)); //Without $rtoi: YOSYS ERROR: Non-constant expression in constant function
    endfunction
    
    // functions used to infer some localparam values
    function integer max(input integer a, input integer b);
        if(a >= b) max = a;
        else    max = b;
    endfunction

    function[2:0] WRA_mode_register_value(input integer WRA); //Find the 3-bit value for the Mode Register 0  WR (Write recovery for auto-precharge)
            //WR_min (write recovery for autoprecharge) in clock cycles is calculated by dividing tWR(in ns) by tCK(in ns) and rounding up to the next integer.
            //The WR value in the mode register must be programmed to be equal or larger than WRmin.
        case(WRA) 
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
        integer read_slot, write_slot, activate_slot, precharge_slot;
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
            
            // find activate command slot number
            if(CL_nCK > CWL_nCK) slot_number = read_slot;
            else slot_number = write_slot;
            delay = ns_to_nCK(tRCD);
            for(slot_number = slot_number;  delay != 0; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            activate_slot = slot_number[1:0];
            // if computed activate_slot is same with either write_slot or read_slot, decrement slot number until 
            while(activate_slot[1:0] == write_slot[1:0] || activate_slot[1:0] == read_slot[1:0]) begin 
                activate_slot[1:0] = activate_slot[1:0] - 1'b1;
            end
            
            //the remaining slot will be for precharge command
            precharge_slot = 0;
            while(precharge_slot == write_slot || precharge_slot == read_slot || precharge_slot == activate_slot) begin
                precharge_slot[1:0] = precharge_slot[1:0]  - 1'b1;
            end
            case(cmd)
                CMD_RD: get_slot = read_slot;
                CMD_WR: get_slot = write_slot;
                CMD_ACT: get_slot = activate_slot;
                CMD_PRE: get_slot = precharge_slot;
            endcase
        end
    endfunction
    
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


    ///YOSYS: System task `$display' called with invalid/unsupported format specifier
    initial begin
        $display("DELAY_MAX_VALUE = %0d", DELAY_MAX_VALUE);
        $display("tRCD = %0d", ns_to_nCK(tRCD));
        $display("DELAY_COUNTER_WIDTH = %0d", DELAY_COUNTER_WIDTH);
        $display("DELAY_SLOT_WIDTH = %0d", DELAY_SLOT_WIDTH);
        $display("read_rom_instruction precharge all = %h", read_rom_instruction(12));
        $display("INITIAL_RESET_INSTRUCTION = %h", INITIAL_RESET_INSTRUCTION);
        
        $display("$bits(instruction) = %0d , $bits(CMD_MRS) = %0d , $bits(MR0) = %0d  -> %0d",  $bits(instruction), $bits(CMD_MRS) , $bits(MR0), ($bits(instruction) - $bits(CMD_MRS) - $bits(MR0)));
        $display("serdes_ratio = %0d",serdes_ratio);
        $display("wb_addr_bits = %0d",wb_addr_bits);
        $display("wb_data_bits = %0d",wb_data_bits);
        $display("wb_sel_bits = %0d\n\n",wb_sel_bits);
        $display("request_row_width = %0d", $bits(i_wb_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) ]));
        $display("request_bank_width = %0d", $bits(i_wb_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2))]));
        $display("request_col_width = %0d", $bits({ i_wb_addr[(COL_BITS- $clog2(serdes_ratio*2)-1):0], {{$clog2(serdes_ratio*2)}{1'b0}} }));
        

        $display("READ_SLOT = %0d", READ_SLOT);
        $display("WRITE_SLOT = %0d", WRITE_SLOT);
        $display("ACTIVATE_SLOT = %0d", ACTIVATE_SLOT);
        $display("PRECHARGE_SLOT = %0d", PRECHARGE_SLOT);

    end


    
    
`ifdef  FORMAL
    initial assume(!i_rst_n); 
    
    always @* begin
        assert(tMOD + tZQinit > nCK_to_cycles(tDLLK)); //Initialization sequence requires that tDLLK is satisfied after MRS to mode register 0 and ZQ calibration
        assert(MR0[18] != 1'b1); //last Mode Register bit should never be zero 
        assert(MR1[18] != 1'b1); //(as this is used for A10-AP control for non-MRS 
        assert(MR2[18] != 1'b1); //commands in the reset sequence)
        assert(MR3[18] != 1'b1);
        assert(DELAY_COUNTER_WIDTH <= $bits(MR0)); //bitwidth of mode register should be enough for the delay counter
        assert(($bits(instruction) - $bits(CMD_MRS) - $bits(MR0)) == 5 ); //sanity checking to ensure 5 bits is allotted for extra instruction {reset_finished, use_timer , stay_command , cke , reset_n } 
        assert(DELAY_SLOT_WIDTH >= DELAY_COUNTER_WIDTH); //width occupied by delay timer slot on the reset rom must be able to occupy the maximum possible delay value on the reset sequence
    end
    
    reg f_past_valid = 0; 
    always @(posedge i_clk)  f_past_valid <= 1;
    
    
    //The idea below is sourced from https://zipcpu.com/formal/2019/11/18/genuctrlr.html
    //We will form a packet of information describing each instruction as it goes through the pipeline and make assertions along the way.
    //2-stage Pipeline: f_addr (update address)  ->  f_read (read instruction from rom)  
    reg[$bits(instruction_address) - 1: 0] f_addr = 0, f_read = 0 ; 
    reg[$bits(instruction) - 1:0] f_read_inst = INITIAL_RESET_INSTRUCTION;
    
    //pipeline stage logic: f_addr (update address)  ->  f_read (read instruction from rom)  
    always @(posedge i_clk, negedge i_rst_n) begin
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
        if(f_addr == 0) f_read_inst = INITIAL_RESET_INSTRUCTION; //will only happen at the very start:  f_addr (0)  ->  f_read (0)  where we are reading the initial reset instruction and not the rom
        assert(f_read_inst == instruction);  // f_read_inst is the shadow of current instruction 
    end
    
    // main assertions for the reset sequence 
    always @(posedge i_clk) begin
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
                if($past(delay_counter) == 1) assert(delay_counter == 0 && delay_counter_is_zero); 
                
                //assert the relationship between the stages FOR RESET SEQUENCE
                if(!reset_done) begin
                    if(f_addr == 0) assert(f_read == 0); //will only happen at the very start:  f_addr (0)  ->  f_read (0)  
                    else if(f_read == 0) assert(f_addr <= 1); //will only happen at the very first two cycles: f_addr (1)  ->  f_read (0) or f_addr (0)  ->  f_read (0)  
                    //else if($past(reset_done)) assert(f_read == $past(f_read)); //reset instruction does not repeat after reaching end address thus it must saturate when pipeline reaches end
                    else assert(f_read + 1 == f_addr); //address increments continuously
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
        if(a[USE_TIMER]) assert( a[DELAY_COUNTER_WIDTH - 1:0] > 0);                                                                                                                     
    end
    
    
    //cover statements
    `ifdef FORMAL_COVER
    reg[3:0] f_count_refreshes = 0; //count how many refresh cycles had already passed
    always @(posedge i_clk) begin
        if($past(f_read) == 15 && f_read == 12) f_count_refreshes = f_count_refreshes + 1; //every time address wrap around refresh is completed
    end
    always @(posedge i_clk) begin
        cover(f_count_refreshes == 5);
        //cover($past(instruction[RST_DONE]) && !instruction[RST_DONE] && i_rst_n); //MUST FAIL: find an instance where RST_DONE will go low after it already goes high (except when i_rst_n is activated)
    end
    `endif
    
    always @* begin
        //make sure each command has distinct slot number (except for read/write which can have the same or different slot number)
        assert((WRITE_SLOT != ACTIVATE_SLOT != PRECHARGE_SLOT) && (READ_SLOT != ACTIVATE_SLOT != PRECHARGE_SLOT) );
        //make sure slot number for read command is correct

    end
    
        
`endif
endmodule

