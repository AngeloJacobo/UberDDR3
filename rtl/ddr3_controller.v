// Background:
// This DDR3 controller will be used with a DDR3-1600 with Kintex 7 FPGA Board (XC7K160T-3FFG676E). 
// The goal will be to:
//  - Run this at 1600Mbps (Maximum Physical Interface (PHY) Rate for a 4:1 
//          memory controller based on "DC and AC Switching Characteristics" for Kintex 7)
//  - Parameterize everything
//  - Interface should be (nearly) bus agnostic   
//  - High (sustained) data throughput. Sequential writes should be able to continue without interruption 


//`define FORMAL_COVER //change delay in reset sequence to fit in cover statement
//`define COVER_DELAY 2 //fixed delay used in formal cover for reset sequence
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
    parameter ROW_BITS = 14,   
                COL_BITS = 10,
                BA_BITS = 3,
                DQ_BITS = 8, 
                CONTROLLER_CLK_PERIOD = 5, //ns, period of clock input to this DDR3 controller module
                DDR3_CLK_PERIOD = 1.25, //ns, period of clock input to DDR3 RAM device 
                LANES = 8, //8 lanes of DQ
                OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
                OPT_BUS_ABORT = 1  //1 = can abort bus, 0 = no abort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)
    ) 
    (
        input wire i_clk, i_rst_n, //200MHz input clock
        // Wishbone inputs
        input wire i_wb_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb_stb, //request a transfer
        input wire i_wb_we, //write-enable (1 = write, 0 = read)
        input wire[ROW_BITS + COL_BITS + BA_BITS - $clog2($rtoi(DQ_BITS*LANES*(CONTROLLER_CLK_PERIOD / DDR3_CLK_PERIOD)*2 / 8)) - 1:0] i_wb_addr, //WORD-ADRESSABLE 
        input wire[$rtoi(DQ_BITS*LANES*(CONTROLLER_CLK_PERIOD / DDR3_CLK_PERIOD)*2) - 1:0] i_wb_data, //write data, for a 4:1 controller data width is 8 times the number of pins on the device
        input wire[$rtoi((DQ_BITS*LANES*CONTROLLER_CLK_PERIOD / DDR3_CLK_PERIOD)*2 / 8) - 1:0] i_wb_sel, //byte strobe for write (1 = write the byte)
        input wire i_aux, //for AXI-interface compatibility (given upon strobe)
        // Wishbone outputs
        output reg o_wb_ack, //1 = read/write request has completed
        output reg o_wb_stall, //1 = busy, cannot accept requests
        output reg[$rtoi(DQ_BITS*LANES*(CONTROLLER_CLK_PERIOD / DDR3_CLK_PERIOD)*2) - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output reg o_aux//for AXI-interface compatibility (returned upon ack)
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

    localparam RST_DONE = 27, //Command bit that determines if the command is for power-on sequence only (not on power-stable sequence)
                 RST_USE_TIMER = 26, // Command bit that determines if timer will be used
                 RST_STAY_COMMAND = 25, //Command bit that determines if command will last for entire timer duration (or if 
                 RST_CKE = 24, //Control clock-enable input to DDR3
                 RST_RESET_N = 23; //Control reset to DDR3

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

    localparam tXPR = max(5*DDR3_CLK_PERIOD,tRFC+10); // ns Exit Reset from CKE HIGH to a valid command
    localparam tMRD = 4; // nCK Mode Register Set command cycle time
    localparam tWR = 15.0; // ns Write Recovery Time
    localparam tDLLK = 512.0; //nCK DLL Locking time
    localparam[DELAY_SLOT_WIDTH - 1:0] tMOD = max(nCK_to_cycles(12), ns_to_cycles(15)); //cycles (controller)  Mode Register Set command update delay
    localparam[DELAY_SLOT_WIDTH - 1:0] tZQinit = max(nCK_to_cycles(512), ns_to_cycles(640));//cycles (controller)  Power-up and RESET calibration time
    localparam[DELAY_SLOT_WIDTH - 1:0] tZQoper = max(nCK_to_cycles(256), ns_to_cycles(320)); //cycles (controller) Normal operation Full calibration time

    localparam DELAY_MAX_VALUE = ns_to_cycles(INITIAL_CKE_LOW); //Largest possible delay needed by the reset and refresh sequence
    localparam DELAY_COUNTER_WIDTH= $clog2(DELAY_MAX_VALUE); //Bitwidth needed by the maximum possible delay, this will be the delay counter width
    localparam DELAY_SLOT_WIDTH = $bits(MR0); //Bitwidth of the delay slot and mode register slot on the reset rom will be at the same size as the Mode Register

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    localparam AP          =           10 ;  // the address bit that controls auto-precharge and precharge-all
    localparam BC           =          12;   // the address bit that controls burst chop


    
    //////////////////////////////////////////////////////// RESET and Initialization Procedure (JEDEC DDR3 doc pg. 19) ////////////////////////////////////////////////////////
    // This reset and initialization process is designed for simplicity. This uses a Read-Only Memory (ROM)) 
    // to store the reset commands and time_delay. A function is used store instructions instead of registers
    // since parameters cannot change their values during formal verification. 
    // This idea is sourced from https://zipcpu.com/formal/2019/11/18/genuctrlr.html
    // Instruction format:
        // RST_DONE = 27; //Command bit that determines if the command is for power-on sequence only (not on power-stable sequence)
        // RST_USE_TIMER = 26; // Command bit that determines if timer will be used (if delay is zero, RST_USE_TIMER must be high)
        // RST_CKE = 24; //Control clock-enable input to DDR3
        // RST_RESET_N = 23; //Control reset to DDR3
        // DDR_CMD = 22:19 
        // Timer-Delay or MRS = 18:0 //timer delay and MRS shares same slot, thus MRS commands cannot have delays
        // A10-AP Control = 18 // Address [10] for precharge-all command. Mode Register [18] is always zero thus this is allocated for A10-AP control.
        
        // NOTE: The timer delay is a "DELAY" in clock cycles AFTER EXECUTING COMMAND, not the ACTUAL CYCLES of the command (delay of 1 means 2 clock cycles of command execution
    function [27:0] read_reset_instruction(input[3:0] reset_addr);
        case(reset_addr) 
    
            4'd0: read_reset_instruction = {5'b01100 , CMD_NOP , ns_to_cycles(POWER_ON_RESET_HIGH)}; 
            //0. RESET# needs to be maintained for minimum 200us with POWER-UP INITIALIZATION. CKE is pulled
                //“Low” anytime before RESET# being de-asserted (min. time 10 ns). .
            
            4'd1: read_reset_instruction =  {5'b01101 , CMD_NOP, ns_to_cycles(INITIAL_CKE_LOW)}; 
            //1. After RESET# is de-asserted, wait for another 500 us until CKE becomes active. During this time, the
                //DRAM will start internal state initialization; this will be done independently of external clocks. 
                // .... Also, a NOP or Deselect command must be registered (with tIS set up time to clock) before
                //CKE goes active.

            4'd2: read_reset_instruction = {5'b01111 , CMD_NOP, ns_to_cycles(tXPR)}; 
            //2. After CKE is being registered high, wait minimum of Reset CKE Exit time, tXPR.
            
            4'd3: read_reset_instruction = {5'b00011, CMD_MRS, MR2}; 
            //3. Issue MRS command to load MR2. 
            
            4'd4: read_reset_instruction = {5'b01111, CMD_NOP, nCK_to_cycles(tMRD)}; //use timer if not zero delay
            //4. Delay of tMRD between MRS commands
            
            4'd5: read_reset_instruction = {5'b00011, CMD_MRS, MR3}; 
            //5. Issue MRS command to load MR3. Prior to enabling the MPR for read calibration, all banks must be in the idle state (all banks 
                // precharged and tRP met). Once the MPR is enabled, any subsequent RD or RDA commands will be redirected to the MultiPurpose Register. 
                
            4'd6: read_reset_instruction = {5'b01111, CMD_NOP, nCK_to_cycles(tMRD)}; //use timer if not zero delay
            //6. Delay of tMRD between MRS commands
            
            4'd7: read_reset_instruction = {5'b00011, CMD_MRS, MR1}; 
            //7. Issue MRS command to load MR1 and enable DLL. 
            
            4'd8: read_reset_instruction = {5'b01111, CMD_NOP, nCK_to_cycles(tMRD)}; //use timer if not zero delay
            //8. Delay of tMRD between MRS commands
            
            4'd9: read_reset_instruction = {5'b00011, CMD_MRS, MR0}; 
            //9. Issue MRS command to load MR0 and reset DLL.
            
            4'd10: read_reset_instruction = {5'b01111, CMD_NOP, tMOD};
            //10. Delay of tMOD between MRS command to a non-MRS command excluding NOP and DES 
            
            4'd11: read_reset_instruction = {5'b01011, CMD_ZQC, tZQinit}; 
            //11. ZQ Calibration command is used to calibrate DRAM Ron & ODT values. ZQCL command triggers the calibration engine 
            //inside the DRAM and, once calibration is achieved, the calibrated values area transferred from the calibration engine to 
            //DRAM IO, which gets reflected as updated output driver
                
            // Perform first refresh
            4'd12: read_reset_instruction = {5'b01011, CMD_PRE, ns_to_cycles(tRP) | {1'b1,  {(DELAY_SLOT_WIDTH-1){1'b0}}}}; //set the A10-AP high using bitwise OR
            //12. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            4'd13: read_reset_instruction = {5'b01011, CMD_REF, ns_to_cycles(tRFC)};
            //13. A delay between the Refresh Command and the next valid command, except NOP or DES, must be greater than or equal to the minimum 
            //Refresh cycle time tRFC(min) 
            
            4'd14: read_reset_instruction = {5'b10111, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b0}}}; 
            // 14. End of the reset sequence
            
            default: read_reset_instruction = {5'b10011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b0}}}; // End of the reset sequence
        endcase
    endfunction

    localparam INITIAL_RESET_INSTRUCTION = {5'b01100 , CMD_NOP , { {(DELAY_SLOT_WIDTH-3){1'b0}} , 3'd5} }; 
    
    reg[3:0] reset_addr = 0; //address for accessing reset instruction rom
    reg[27:0] reset_instruction = INITIAL_RESET_INSTRUCTION; //instruction retrieved from reset instruction rom
    reg[ DELAY_COUNTER_WIDTH - 1:0] delay_counter = INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]; //counter used for delays (shared by refresh and reset sequence)
    reg delay_counter_is_zero = (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0); //counter is now zero so retrieve next delay

    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            reset_addr <= 0;
            reset_instruction <= INITIAL_RESET_INSTRUCTION;
            delay_counter <= INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0];
            delay_counter_is_zero <= (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0);
        end
        
        else if(!reset_instruction[RST_DONE]) begin //reset rom is a one-shot sequence and will not repeat again
            //update counter after reaching zero
            if(delay_counter_is_zero) begin 
                `ifndef FORMAL_COVER
                    delay_counter <= reset_instruction[DELAY_COUNTER_WIDTH - 1:0]; //retrieve delay value of current instruction, we count to zero thus minus 1
                `else
                    delay_counter <= `COVER_DELAY; //use fixed low value delay to cover the whole reset seqeunce using formal verification
                `endif
                //RECEIVE THE COMMANDS
            end
            
            //else: decrement delay counter when current instruction needs delay
            else if(reset_instruction[RST_USE_TIMER]) delay_counter <= delay_counter - 1; 
            
            //delay_counter of 1 means we will need to update the delay_counter next clock cycle (delay_counter of zero) so we need to retrieve 
            //now the next reset_instruction. The same thing needs to be done when current instruction does not need the timer delay.
            if(delay_counter == 1 || !reset_instruction[RST_USE_TIMER]) begin
                delay_counter_is_zero <= 1; 
                reset_instruction <= read_reset_instruction(reset_addr);
                reset_addr <= reset_addr + 1; 
            end
            else delay_counter_is_zero <=0; //we are now on the middle of a delay 
        end
    end
    

    //Good reference for intialization and ODT
    //https://www.systemverilog.io/design/ddr4-initialization-and-calibration/
    //notes:
    //ODT must be statically held low at all times (except for write of course) when RTT_NOM is enabled via MR1.
    
    //////////////////////////////////////////////////////////////////////// FUNCTIONS ////////////////////////////////////////////////////////////////////////////////////////////////////
    //convert nanoseconds time input to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] ns_to_cycles (input[DELAY_SLOT_WIDTH - 1:0] ns); //output is set at same length as a MRS command (19 bits) to maximize the time slot
        ns_to_cycles = $rtoi($ceil(ns*1.0/CONTROLLER_CLK_PERIOD)); //YOSYS: ERROR: Non-constant expression in constant function
    endfunction

    //convert nCK input (number of DDR3 clock cycles) to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    function [DELAY_SLOT_WIDTH - 1:0] nCK_to_cycles (input[DELAY_SLOT_WIDTH - 1:0] nCK); 
        nCK_to_cycles = $rtoi($ceil(nCK*DDR3_CLK_PERIOD/CONTROLLER_CLK_PERIOD)) ; //YOSYS: ERROR: Non-constant expression in constant function
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
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    ///YOSYS: System task `$display' called with invalid/unsupported format specifier
    /*
    initial begin
        $display("DELAY_MAX_VALUE = %0d", DELAY_MAX_VALUE);
        $display("tRP = %0d", ns_to_cycles(tRP));
        $display("DELAY_COUNTER_WIDTH = %0d", DELAY_COUNTER_WIDTH);
        $display("DELAY_SLOT_WIDTH = %0d", DELAY_SLOT_WIDTH);
        $display("read_reset_instruction precharge all = %h", read_reset_instruction(12));
        $display("INITIAL_RESET_INSTRUCTION = %h", INITIAL_RESET_INSTRUCTION);
        
        $display("$bits(reset_instruction) = %0d , $bits(CMD_MRS) = %0d , $bits(MR0) = %0d  -> %0d",  $bits(reset_instruction), $bits(CMD_MRS) , $bits(MR0), ($bits(reset_instruction) - $bits(CMD_MRS) - $bits(MR0)));
    end
    */
    
    
`ifdef  FORMAL
    initial assume(!i_rst_n); 
    
    always @* begin
        assert(tMOD + tZQinit > nCK_to_cycles(tDLLK)); //Initialization sequence requires that tDLLK is satisfied after MRS to mode register 0 and ZQ calibration
        assert(MR0[18] != 1'b1); //last Mode Register bit should never be zero 
        assert(MR1[18] != 1'b1); //(as this is used for A10-AP control for non-MRS 
        assert(MR2[18] != 1'b1); //commands in the reset sequence)
        assert(MR3[18] != 1'b1);
        assert(DELAY_COUNTER_WIDTH <= $bits(MR0)); //bitwidth of mode register should be enough for the delay counter
        assert(($bits(reset_instruction) - $bits(CMD_MRS) - $bits(MR0)) == 5 ); //sanity checking to ensure 5 bits is allotted for extra instruction {reset_finished, use_timer , stay_command , cke , reset_n } 
        assert(DELAY_SLOT_WIDTH >= DELAY_COUNTER_WIDTH); //width occupied by delay timer slot on the reset rom must be able to occupy the maximum possible delay value on the reset sequence
    end
    
    reg f_past_valid = 0; 
    always @(posedge i_clk)  f_past_valid <= 1;
    
    
    //The idea below is sourced from https://zipcpu.com/formal/2019/11/18/genuctrlr.html
    //We will form a packet of information describing each instruction as it goes through the pipeline and make assertions along the way.
    //2-stage Pipeline: f_addr (update address)  ->  f_read (read instruction from rom)  
    reg[$bits(reset_addr) - 1: 0] f_addr = 0, f_read = 0 ; 
    reg[$bits(reset_instruction) - 1:0] f_read_inst = INITIAL_RESET_INSTRUCTION;
    
    //pipeline stage logic: f_addr (update address)  ->  f_read (read instruction from rom)  
    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            f_addr <= 0;
            f_read <= 0;
        end
        else if((delay_counter == 1 || !reset_instruction[RST_USE_TIMER]) && !f_read_inst[RST_DONE] )begin //move the pipeline forward when counter is about to go zero and we are not yet at end of reset sequence
            f_addr <= f_addr + 1;
            f_read <= f_addr;
        end     
    end
    
    // assert f_addr and f_read as shadows of next and current instruction address 
    always @* begin
        assert(f_addr == reset_addr); //f_addr is the shadow of reset_addr (thus f_addr is the address of NEXT instruction)
        f_read_inst = read_reset_instruction(f_read); //f_read is the address of CURRENT instruction 
        if(f_addr == 0) f_read_inst = INITIAL_RESET_INSTRUCTION; //will only happen at the very start:  f_addr (0)  ->  f_read (0)  where we are reading the initial reset instruction and not the rom
        assert(f_read_inst == reset_instruction);  // f_read_inst is the shadow of reset_instruction (which  is the CURRENT instruction)
    end
    
    // main assertions for the reset sequence 
    always @(posedge i_clk) begin
            if(!i_rst_n || !$past(i_rst_n)) begin
                assert(f_addr == 0);
                assert(f_read == 0);
                assert(reset_addr == 0);
                assert(delay_counter == (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]));
                assert(delay_counter_is_zero == (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0));
            end
            else if(f_past_valid) begin
                //if counter is zero previously and current instruction needs timer delay, then this cycle should now have the new updated counter value
                if( $past(delay_counter_is_zero) && $past(f_read_inst[RST_USE_TIMER])&& !$past(f_read_inst[RST_DONE]))  
                    `ifndef FORMAL_COVER
                        assert(delay_counter == (f_read_inst[DELAY_COUNTER_WIDTH - 1:0]));
                    `else
                        assert(delay_counter == `COVER_DELAY); //use fixed low value delay to cover the whole reset seqeunce using formal verification
                    `endif

                 //delay_counter_is_zero can only be high when counter is zero and when instruction does not need delay
                if($past(f_read_inst[RST_USE_TIMER]) && !$past(f_read_inst[RST_DONE])) assert( delay_counter_is_zero  == (delay_counter == 0) ); 
                else if(!$past(f_read_inst[RST_USE_TIMER]) && !$past(f_read_inst[RST_DONE])) assert(delay_counter_is_zero);  //delay_counter_is_zero will go high this cycle when we received a don't-use-timer instruction previously
                
                //we are on the middle of a delay thus all values must remain constant while only delay_counter changes (decrement)
                if(!delay_counter_is_zero) begin 
                    assert(f_addr == $past(f_addr));
                    assert(f_read == $past(f_read));
                    assert(f_read_inst == $past(f_read_inst));
                end
                
                //if delay is not yet zero and timer delay is enabled, then delay_counter should decrement
                if(!$past(delay_counter_is_zero) && $past(f_read_inst[RST_USE_TIMER])) begin
                    assert(delay_counter == $past(delay_counter) - 1); 
                    assert(delay_counter < $past(delay_counter) ); //just to make sure delay_counter will never overflow back to all 1's
                end
                
                //sanity checking for the comment "delay_counter will be zero AT NEXT CLOCK CYCLE when counter is now one"
                if($past(delay_counter) == 1) assert(delay_counter == 0 && delay_counter_is_zero); 
                
                //assert the relationship between the stages
                if(f_addr == 0) assert(f_read == 0); //will only happen at the very start:  f_addr (0)  ->  f_read (0)  
                else if(f_read == 0) assert(f_addr <= 1); //will only happen at the next cycle after the very start: f_addr (1)  ->  f_read (0) or f_addr (0)  ->  f_read (0)  
                else if(f_read_inst[RST_DONE] && $past(f_read_inst[RST_DONE])) assert(f_read == $past(f_read)); //reset instruction does not repeat after reaching end address thus it must saturate when pipeline reaches end
                else assert(f_read + 1 == f_addr); //if we are neither at the very start, nor second to the very last, nor at the very end
            end
    end
    
    
    // assertions on the instructions stored on the rom
    (*anyseq*) reg[$bits(reset_addr) - 1: 0] f_const_addr;
    wire[$bits(reset_instruction) - 1:0]  a= read_reset_instruction(f_const_addr); //retrieve an instruction based on engine's choice
    always @* begin
     //there MUST BE no instruction which RST_USE_TIMER is high but delay is zero since it can cause the logic to lock-up (delay must be at least 1)    
        if(a[RST_USE_TIMER]) assert( a[DELAY_COUNTER_WIDTH - 1:0] > 0);                                                                                                                     
    end
    
    
    //cover statements
    `ifdef FORMAL_COVER
    always @(posedge i_clk) begin
        cover(reset_instruction[RST_DONE]);
        //cover($past(reset_instruction[RST_DONE]) && !reset_instruction[RST_DONE] && i_rst_n); //MUST FAIL: find an instance where RST_DONE will go low after it already goes high (except when i_rst_n is activated)
    end
    `endif
    
        
`endif
endmodule

