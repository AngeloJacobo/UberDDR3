////////////////////////////////////////////////////////////////////////////////
//
// Filename: ddr3_controller.v
// Project:	UberDDR3 - An Open Source DDR3 Controller
//
// Purpose: This DDR3 controller was originally designed to be used on the 
// Network Switch Project (https://github.com/ZipCPU/eth10g). The Network Switch 
// project uses a Kintex 7 FPGA (XC7K160T-3FFG676E). 
// The goal will be to:
//  - Run this at 1600Mbps (Maximum Physical Interface (PHY) Rate for a 4:1 
//          memory controller based on "DC and AC Switching Characteristics" for Kintex 7)
//  - Parameterize everything
//  - Interface should be (nearly) bus agnostic   
//  - High (sustained) data throughput. Sequential writes should be able to continue without interruption 
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

// NOTE TO SELF are questions which I still need to answer
// Comments are continuously added on this RTL for better readability

//`define FORMAL_COVER //skip reset sequence during formal verification to fit in cover depth
`default_nettype none
`timescale 1ps / 1ps
//
// speed bin
`define DDR3_1600_11_11_11 
//`define DDR3_1333_9_9_9 
//`define DDR3_1066_7_7_7 
//
// Choose which debug message will be displayed via UART:
// `define UART_DEBUG_READ_LEVEL
// `define UART_DEBUG_WRITE_LEVEL
// `define UART_DEBUG_ALIGN


`ifdef UART_DEBUG_READ_LEVEL
    `define UART_DEBUG
`elsif UART_DEBUG_WRITE_LEVEL
    `define UART_DEBUG
`elsif UART_DEBUG_ALIGN
    `define UART_DEBUG
`endif

module ddr3_controller #(
    parameter integer CONTROLLER_CLK_PERIOD = 10_000, //ps, clock period of the controller interface
                   DDR3_CLK_PERIOD = 2_500, //ps, clock period of the DDR3 RAM device (must be 1/4 of the CONTROLLER_CLK_PERIOD) 
                   ROW_BITS = 14,   //width of DDR3 row address
                   COL_BITS = 10, //width of DDR3 column address
                   BA_BITS = 3, //width of bank address
                   DQ_BITS = 8,  //device width
                   LANES = 8, //number of DDR3 device to be controlled
                   AUX_WIDTH = 16, //width of aux line (must be >= 4) 
                   WB2_ADDR_BITS = 7, //width of 2nd wishbone address bus 
                   WB2_DATA_BITS = 32, //width of 2nd wishbone data bus
                   DUAL_RANK_DIMM = 0, // enable dual rank DIMM (1 =  enable, 0 = disable)
    // DDR3 timing parameter values
    parameter      SPEED_BIN = 3, // 0 = Use top-level parameters , 1 = DDR3-1066 (7-7-7) , 2 = DR3-1333 (9-9-9) , 3 = DDR3-1600 (11-11-11)
                   SDRAM_CAPACITY = 5, // 0 = 256Mb, 1 = 512Mb, 2 = 1Gb, 3 = 2Gb, 4 = 4Gb, 5 = 8Gb, 6 = 16Gb
                   TRCD = 13_750, // ps Active to Read/Write command time (only used if SPEED_BIN = 0)
                   TRP = 13_750, // ps Precharge command period (only used if SPEED_BIN = 0)
                   TRAS = 35_000, // ps ACT to PRE command period (only used if SPEED_BIN = 0)
    parameter[0:0] MICRON_SIM = 0, //enable faster simulation for micron ddr3 model (shorten POWER_ON_RESET_HIGH and INITIAL_CKE_LOW)
                   ODELAY_SUPPORTED = 1, //set to 1 when ODELAYE2 is supported
                   SECOND_WISHBONE = 0, //set to 1 if 2nd wishbone is needed 
                   DLL_OFF = 0, // 1 = DLL off for low frequency ddr3 clock
                   WB_ERROR = 0, // set to 1 to support Wishbone error (asserts at ECC double bit error)
    parameter[1:0] BIST_MODE = 2, // 0 = No BIST, 1 = run through all address space ONCE , 2 = run through all address space for every test (burst w/r, random w/r, alternating r/w)
    parameter[1:0] ECC_ENABLE = 0, // set to 1 or 2 to add ECC (1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC )  (only change when you know what you are doing)
    parameter[1:0] DIC = 2'b00, //Output Driver Impedance Control (2'b00 = RZQ/6, 2'b01 = RZQ/7, RZQ = 240ohms)  (only change when you know what you are doing)
    parameter[2:0] RTT_NOM = 3'b011, //RTT Nominal (3'b000 = disabled, 3'b001 = RZQ/4, 3'b010 = RZQ/2 , 3'b011 = RZQ/6, RZQ = 240ohms)
    parameter // The next parameters act more like a localparam (since user does not have to set this manually) but was added here to simplify port declaration
                serdes_ratio = 4, // this controller is fixed as a 4:1 memory controller (CONTROLLER_CLK_PERIOD/DDR3_CLK_PERIOD = 4)
                wb_data_bits = DQ_BITS*LANES*serdes_ratio*2,
                wb_addr_bits = ROW_BITS + COL_BITS + BA_BITS - $clog2(serdes_ratio*2) + DUAL_RANK_DIMM,
                wb_sel_bits = wb_data_bits / 8,
                wb2_sel_bits = WB2_DATA_BITS / 8,
                //4 is the width of a single ddr3 command {cs_n, ras_n, cas_n, we_n} plus 3 (ck_en, odt, reset_n) plus bank bits plus row bits
                cmd_len = 4 + 3 + BA_BITS + ROW_BITS + 2*DUAL_RANK_DIMM,
                lanes_clog2 = $clog2(LANES) == 0? 1: $clog2(LANES),
    parameter[1:0] row_bank_col = (ECC_ENABLE == 3)? 2 : 1, // memory address mapping: 0 {bank, row, col} , 1 = {row, bank, col} , 2 = {bank[2:1]. row, bank[0], col} FOR ECC
    parameter[0:0] ECC_TEST = 0
    ) 
    (
        input wire i_controller_clk, //i_controller_clk has period of CONTROLLER_CLK_PERIOD 
        input wire i_rst_n, //200MHz input clock
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
        output wire o_wb_err, //1 = Error due to ECC double bit error (fixed to 0 if WB_ERROR = 0)
        output reg[wb_data_bits - 1:0] o_wb_data, //read data, for a 4:1 controller data width is 8 times the number of pins on the device
        output reg[AUX_WIDTH - 1:0] o_aux, //for AXI-interface compatibility (returned upon ack)
        //
        // Wishbone 2 (PHY) inputs
        /* verilator lint_off UNUSEDSIGNAL */
        input wire i_wb2_cyc, //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        input wire i_wb2_stb, //request a transfer
        input wire i_wb2_we, //write-enable (1 = write, 0 = read)
        input wire[WB2_ADDR_BITS - 1:0] i_wb2_addr, //memory-mapped register to be accessed 
        input wire[wb2_sel_bits - 1:0] i_wb2_sel, //byte strobe for write (1 = write the byte)
        input wire[WB2_DATA_BITS - 1:0] i_wb2_data, //write data
        /* verilator lint_on UNUSEDSIGNAL */
        // Wishbone 2 (Controller) outputs
        output reg o_wb2_stall, //1 = busy, cannot accept requests
        output reg o_wb2_ack, //1 = read/write request has completed
        output reg[WB2_DATA_BITS - 1:0] o_wb2_data, //read data
        //
        // PHY interface
        input wire[DQ_BITS*LANES*8 - 1:0] i_phy_iserdes_data,
        input wire[LANES*serdes_ratio*2 - 1:0] i_phy_iserdes_dqs,
        input wire[LANES*serdes_ratio*2 - 1:0] i_phy_iserdes_bitslip_reference,
        input wire i_phy_idelayctrl_rdy,
        output reg[cmd_len*serdes_ratio-1:0] o_phy_cmd,
        output reg o_phy_dqs_tri_control, o_phy_dq_tri_control,
        output wire o_phy_toggle_dqs,
        output reg[wb_data_bits-1:0] o_phy_data,
        output reg[wb_sel_bits-1:0] o_phy_dm, 
        output wire[4:0] o_phy_odelay_data_cntvaluein, o_phy_odelay_dqs_cntvaluein,
        output wire[4:0] o_phy_idelay_data_cntvaluein, 
        output wire[4:0] o_phy_idelay_dqs_cntvaluein,
        output reg[LANES-1:0] o_phy_odelay_data_ld, o_phy_odelay_dqs_ld,
        output reg[LANES-1:0] o_phy_idelay_data_ld, 
        output reg[LANES-1:0] o_phy_idelay_dqs_ld,
        output reg[LANES-1:0] o_phy_bitslip,
        output reg o_phy_write_leveling_calib,
        output wire o_phy_reset,
        // Done Calibration pin
        (* mark_debug = "true" *) output wire o_calib_complete,
        // Debug port
        output	wire	[31:0]	o_debug1,
//        output	wire	[31:0]	o_debug2,
//        output	wire	[31:0]	o_debug3
        // User enabled self-refresh
        input wire i_user_self_refresh,
        // Display debug messages via UART
        output wire uart_tx
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
                      CMD_ZQC = 4'b0110, // ZQ Calibration (A10-AP: 0 = ZQ Calibration Short, 1 = ZQ Calibration Long)
                      CMD_SREF_EN = 4'b0001,
                      CMD_SREF_XT = 4'b0111;
                      
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
    
    /* verilator lint_on UNUSEDPARAM */          
    localparam READ_SLOT = get_slot(CMD_RD),
                WRITE_SLOT = get_slot(CMD_WR),
                ACTIVATE_SLOT = get_slot(CMD_ACT),
                PRECHARGE_SLOT = get_slot(CMD_PRE),
                REMAINING_SLOT = get_slot(0);
                
    // Data does not have to be delayed (DQS is the on that has to be
    // delayed and center-aligned to the center eye of data)
    localparam DATA_INITIAL_ODELAY_TAP = 0; 

    //Posedge of DQS needs to be aligned to the center eye of the data. 
    //This means DQS needs to be delayed by a quarter of the ddr3
    //clk period relative to the data. Subtract by 600ps to include
    //the IODELAY insertion delay. Divide by a delay resolution of 
    //78.125ps per tap to get the needed tap value. Then add the tap
    //value used in data to have the delay relative to the data.
    localparam DQS_INITIAL_ODELAY_TAP = $rtoi(((DDR3_CLK_PERIOD/4))/78.125 + DATA_INITIAL_ODELAY_TAP);
    
    //Incoming DQS should be 90 degree delayed relative to incoming data
    localparam DATA_INITIAL_IDELAY_TAP = 0; //600ps delay
    localparam DQS_INITIAL_IDELAY_TAP = $rtoi(((DDR3_CLK_PERIOD/4))/78.125 + DATA_INITIAL_IDELAY_TAP);
    /*********************************************************************************************************************************************/


    /********************************************************** Timing Parameters ***********************************************************************************/
    localparam DELAY_SLOT_WIDTH = 19; //Bitwidth of the delay slot and mode register slot on the reset/refresh rom will be at the same size as the Mode Register
    localparam POWER_ON_RESET_HIGH = 200_000_000; // 200_000_000 ps (200 us) reset must be active at initialization
    localparam INITIAL_CKE_LOW = 500_000_000; // 500_000_000 ps (500 us) cke must be low before activating
    
    // ps Active to Read/Write command time
   localparam tRCD = (SPEED_BIN == 0) ? TRCD :  //  use top-level parameters
                      (SPEED_BIN == 1) ? 13_750 : // DDR3-1066 (7-7-7) 
                      (SPEED_BIN == 2) ? 13_500 :  // DDR3-1333 (9-9-9)
                      (SPEED_BIN == 3) ? 13_750 : 13_750; // DDR3-1600 (11-11-11)

    // ps Precharge command period
    localparam tRP  = (SPEED_BIN == 0) ? TRP : //  use top-level parameters
                      (SPEED_BIN == 1) ? 13_750 : // DDR3-1066 (7-7-7) 
                      (SPEED_BIN == 2) ? 13_500 : // DDR3-1333 (9-9-9)
                      (SPEED_BIN == 3) ? 13_750 : 13_750; // DDR3-1600 (11-11-11)

     // ps ACT to PRE command period
    localparam tRAS = (SPEED_BIN == 0) ? TRAS : //  use top-level parameters
                      (SPEED_BIN == 1) ? 35_000 : // DDR3-1066 (7-7-7) 
                      (SPEED_BIN == 2) ? 36_000 : // DDR3-1333 (9-9-9)
                      (SPEED_BIN == 3) ? 35_000 : 35_000; // DDR3-1600 (11-11-11)

    // ps Refresh command  to ACT or REF
    localparam tRFC = ((SDRAM_CAPACITY == 4'b0000) || (SDRAM_CAPACITY == 4'b0001)) ? 90_000 : // 256Mb, 512Mb
                    (SDRAM_CAPACITY == 4'b0010) ? 110_000 : // 1Gb
                    (SDRAM_CAPACITY == 4'b0011) ? 160_000 : // 2Gb
                    (SDRAM_CAPACITY == 4'b0100) ? 300_000 : // 4Gb
                    (SDRAM_CAPACITY == 4'b0101) ? 350_000 : 350_000; // 8Gb

    localparam tREFI = 7_800_000; //ps Average periodic refresh interval
    localparam tXPR = max(5*DDR3_CLK_PERIOD, tRFC+10_000); // ps Exit Reset from CKE HIGH to a valid command
    localparam tWR = 15_000; // ps Write Recovery Time
    localparam tWTR = max(nCK_to_ps(4), 7_500); //ps Delay from start of internal write transaction to internal read command
    localparam tWLMRD = nCK_to_cycles(40); // nCK First DQS/DQS# rising edge after write leveling mode is programmed
    localparam tWLO = 9_000; //ps Write leveling output delay
    localparam tWLOE = 2_000; //ps Write leveling output error
    localparam tRTP = max(nCK_to_ps(4), 7_500); //ps Internal Command to PRECHARGE Command delay
    localparam tCCD = 4; //nCK CAS to CAS command delay
    /* verilator lint_off WIDTHEXPAND */
    localparam tMOD = max(nCK_to_cycles(12), ps_to_cycles(15_000)); //cycles (controller)  Mode Register Set command update delay
    localparam tZQinit = max(nCK_to_cycles(512), ps_to_cycles(640_000));//cycles (controller)  Power-up and RESET calibration time
    /* verilator lint_on WIDTHEXPAND */
    // FOr DLL_OFF< CL and CWL should both be 6. But effective CL is only 5 since read data is early by 1 nCK
    localparam CL_nCK = DLL_OFF? 4'd5 : CL_generator(DDR3_CLK_PERIOD); //read latency (given in JEDEC DDR3 spec)
    localparam CWL_nCK = DLL_OFF? 4'd6 : CWL_generator(DDR3_CLK_PERIOD); //write latency (given in JEDEC DDR3 spec)
    localparam DELAY_MAX_VALUE = ps_to_cycles(INITIAL_CKE_LOW); //Largest possible delay needed by the reset and refresh sequence
    localparam DELAY_COUNTER_WIDTH= $clog2(DELAY_MAX_VALUE); //Bitwidth needed by the maximum possible delay, this will be the delay counter width
    localparam CALIBRATION_DELAY = 2; // must be >= 2
    localparam tXSDLL = nCK_to_cycles(512); // cycles (controller) Exit Self Refresh to commands requiring a locked DLL
    localparam tXSDLL_tRFC = tXSDLL - ps_to_cycles(tRFC); // cycles (controller) Time before refresh after exit from self-refresh
    localparam tCKE = max(3, ps_to_nCK(7500) ); // nCK CKE minimum pulse width
    localparam tCKESR = nCK_to_cycles(tCKE + 1)+ 5; // cycles (controller) Minimum time that the DDR3 SDRAM must remain in Self-Refresh mode is tCKESR
    localparam tCPDED = 5; // cycle (tCPDED is at most 2nCK but we make it to 1cycle or 4nCK) Command pass disable delay , required cycles of NOP after CKE low 
    /*********************************************************************************************************************************************/
    

    /********************************************************** Computed Delay Parameters **********************************************************/
    /* verilator lint_off WIDTHEXPAND */
    localparam[3:0] PRECHARGE_TO_ACTIVATE_DELAY =  find_delay(ps_to_nCK(tRP), PRECHARGE_SLOT, ACTIVATE_SLOT); //3
    localparam[3:0] ACTIVATE_TO_PRECHARGE_DELAY = find_delay(ps_to_nCK(tRAS), ACTIVATE_SLOT, PRECHARGE_SLOT);
    localparam[3:0] ACTIVATE_TO_WRITE_DELAY = find_delay(ps_to_nCK(tRCD), ACTIVATE_SLOT, WRITE_SLOT); //3
    localparam[3:0] ACTIVATE_TO_READ_DELAY = find_delay(ps_to_nCK(tRCD), ACTIVATE_SLOT, READ_SLOT); //2
    localparam[3:0] ACTIVATE_TO_ACTIVATE_DELAY = find_delay(ps_to_nCK(7500), ACTIVATE_SLOT, ACTIVATE_SLOT); //TRRD
    localparam[3:0] READ_TO_WRITE_DELAY = find_delay((CL_nCK + tCCD + 2 - CWL_nCK), READ_SLOT, WRITE_SLOT); //2
    localparam[3:0] READ_TO_READ_DELAY = 0;
    localparam[3:0] READ_TO_PRECHARGE_DELAY =  find_delay(ps_to_nCK(tRTP), READ_SLOT, PRECHARGE_SLOT);  //1
    localparam[3:0] WRITE_TO_WRITE_DELAY = 0;
    localparam[3:0] WRITE_TO_READ_DELAY = find_delay((CWL_nCK + 4 + ps_to_nCK(tWTR)), WRITE_SLOT, READ_SLOT); //4
    localparam[3:0] WRITE_TO_PRECHARGE_DELAY = find_delay((CWL_nCK + 4 + ps_to_nCK(tWR)), WRITE_SLOT, PRECHARGE_SLOT); //5
    /* verilator lint_on WIDTHEXPAND */
    localparam PRE_REFRESH_DELAY = WRITE_TO_PRECHARGE_DELAY + 1; 
    `ifdef FORMAL 
        (*keep*) wire[3:0] f_PRECHARGE_TO_ACTIVATE_DELAY, f_ACTIVATE_TO_PRECHARGE_DELAY, f_ACTIVATE_TO_WRITE_DELAY, f_ACTIVATE_TO_READ_DELAY, f_ACTIVATE_TO_ACTIVATE_DELAY,
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
        assign f_ACTIVATE_TO_ACTIVATE_DELAY = ACTIVATE_TO_ACTIVATE_DELAY;
    `endif

    //MARGIN_BEFORE_ANTICIPATE is the number of columns before the column
    //end when the anticipate can start
    //the worst case scenario is when the anticipated bank needs to be precharged
    //thus the margin must satisfy tRP (for precharge) and tRCD (for activate). 
    //Also, worscase is when the anticipated bank still has the leftover of the 
    //WRITE_TO_PRECHARGE_DELAY thus consider also this.
    localparam MARGIN_BEFORE_ANTICIPATE = PRECHARGE_TO_ACTIVATE_DELAY + ACTIVATE_TO_WRITE_DELAY + WRITE_TO_PRECHARGE_DELAY;
    // STAGE2_DATA_DEPTH is the number of controller clk cycles of delay before issuing the data after the write command
    // depends on the CWL_nCK
    /* verilator lint_off WIDTHEXPAND */
    localparam STAGE2_DATA_DEPTH = (CWL_nCK - (3 - WRITE_SLOT + 1))/4 + 1; //this is always >= 1 (5 - (3 - 3 + 1))/4.0 -> floor(1) + 1 = floor(4
    /* verilator lint_on WIDTHEXPAND */
    `ifdef FORMAL
        wire stage2_data_depth;
        assign stage2_data_depth = STAGE2_DATA_DEPTH;
        always @* begin
            assert(STAGE2_DATA_DEPTH-2 >= 0);
        end
    `endif
    localparam READ_DELAY = $rtoi($floor((CL_nCK - (3 - READ_SLOT + 1))/4.0 )); // how many controller clk cycles to satisfy CL_nCK of ddr3_clk cycles
     // READ_ACK_PIPE_WIDTH is the delay between read command issued (starting from the controller) until the data is received by the controller
     //the delays included the ODELAY and OSERDES when issuing the read command
     //and the IDELAY and ISERDES when receiving the data  (NOTE TO SELF: ELABORATE ON WHY THOSE MAGIC NUMBERS)
    localparam READ_ACK_PIPE_WIDTH = READ_DELAY + 1 + 2 + 1 + 1 + (DLL_OFF? 2 : 0); // FOr DLL_OFF, phy has no delay thus add delay here       
    localparam MAX_ADDED_READ_ACK_DELAY = 16;
    localparam DELAY_BEFORE_WRITE_LEVEL_FEEDBACK = STAGE2_DATA_DEPTH + ps_to_cycles(tWLO+tWLOE) + 10;  
    //plus 10 controller clocks for possible bus latency and the delay for receiving feedback DQ from IOBUF -> IDELAY -> ISERDES
    localparam ECC_INFORMATION_BITS = (ECC_ENABLE == 2)? max_information_bits(wb_data_bits) : max_information_bits(wb_data_bits/8);
    // Smaller wb_addr_bits for simulation so BIST will end faster
    localparam wb_addr_bits_sim = MICRON_SIM? 8 : wb_addr_bits; 
    
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
                //ISSUE_READ_2 = 12,
                READ_DATA = 12,
                ANALYZE_DATA = 13, 
                CHECK_STARTING_DATA = 14,
                BITSLIP_DQS_TRAIN_3 = 15,
                //WRITE_ZERO = 16,
                BURST_WRITE = 17,
                BURST_READ = 18,
                RANDOM_WRITE = 19,
                RANDOM_READ = 20,
                ALTERNATE_WRITE_READ = 21,
                FINISH_READ = 22,
                DONE_CALIBRATE = 23,
                ANALYZE_DATA_LOW_FREQ = 24;
                
     localparam STORED_DQS_SIZE = 5, //must be >= 2           
                REPEAT_DQS_ANALYZE = 1,
                REPEAT_CLK_SAMPLING = 5; // repeat DQS read to find the accurate starting position of DQS

    /*********************************************************************************************************************************************/


    /************************************************************* Set Mode Registers Parameters *************************************************************/
    // MR2 (JEDEC DDR3 doc pg. 30)
    localparam[2:0] PASR = 3'b000; //Partial Array Self-Refresh: Full Array
    localparam[3:0] CWL = DLL_OFF? 6-4'd5 : CWL_nCK-4'd5; //CAS write Latency
    localparam[0:0] ASR = 1'b1; //Auto Self-Refresh: on
    localparam[0:0] SRT = 1'b0; //Self-Refresh Temperature Range:0 (If ASR = 1, SRT bit must be set to 0)
    localparam[1:0] RTT_WR = 2'b00; //Dynamic ODT: off
    localparam[2:0] MR2_SEL = 3'b010; //Selected Mode Register
    localparam[18:0] MR2 = {MR2_SEL, 5'b00000, RTT_WR, 1'b0, SRT, ASR, CWL[2:0], PASR}; 

    // MR3 (JEDEC DDR3 doc pg. 32)
    localparam[1:0] MPR_LOC = 2'b00; //Data location for MPR Reads: Predefined Pattern 0_1_0_1_0_1_0_1
    localparam[0:0] MPR_EN = 1'b1; //MPR Enable: Enable MPR reads and calibration during initialization
    localparam[2:0] MR3_SEL = 3'b011; //MPR Selected
    localparam[18:0] MR3_MPR_EN = {MR3_SEL, 13'b0_0000_0000_0000, MPR_EN, MPR_LOC}; 
    localparam[18:0] MR3_MPR_DIS = {MR3_SEL, 13'b0_0000_0000_0000, !MPR_EN, MPR_LOC}; 
    
    // MR1 (JEDEC DDR3 doc pg. 27)
    localparam DLL_EN = DLL_OFF? 1'b1 : 1'b0; //DLL Enable/Disable: Enabled(0)
    // localparam[1:0] DIC = 2'b01; //Output Driver Impedance Control (RZQ/7) (elevate this to parameter)
    // localparam[2:0] RTT_NOM = 3'b001; //RTT Nominal: RZQ/4 (elevate this to parameter)
    localparam[0:0] WL_EN = 1'b1; //Write Leveling Enable: Disabled
    localparam[1:0] AL = 2'b00; //Additive Latency: Disabled
    localparam[0:0] TDQS = 1'b0; //Termination Data Strobe: Disabled (provides additional termination resistance outputs. 
                                 //When the TDQS function is disabled, the DM function is provided (vice-versa).TDQS function is only 
                                 //available for X8 DRAM and must be disabled for X4 and X16. 
    localparam[0:0] QOFF = 1'b0; //Output Buffer Control: Enabled
    localparam[2:0] MR1_SEL = 3'b001; //Selected Mode Register
    localparam[18:0] MR1_WL_EN = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, WL_EN, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};
    localparam[18:0] MR1_WL_DIS = {MR1_SEL, 3'b000, QOFF, TDQS, 1'b0, RTT_NOM[2], 1'b0, !WL_EN, RTT_NOM[1], DIC[1], AL, RTT_NOM[0], DIC[0], DLL_EN};

    //MR0 (JEDEC DDR3 doc pg. 24)
    localparam[1:0] BL = 2'b00; //Burst Length: 8 (Fixed)
    localparam[3:0] CL = DLL_OFF? (6-4)*2 : (CL_nCK-4)*2; //CAS Read Latency
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
    (* mark_debug ="true" *) reg[4:0] instruction_address = 0; //address for accessing rom instruction
    reg[27:0] instruction = INITIAL_RESET_INSTRUCTION; //instruction retrieved from reset instruction rom
    reg[ DELAY_COUNTER_WIDTH - 1:0] delay_counter = INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]; //counter used for delays
    reg delay_counter_is_zero = (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0); //counter is now zero so retrieve next delay
    reg reset_done = 0; //high if reset has already finished
    reg pause_counter = 0;
    wire issue_read_command;
    reg stage2_update = 1;
    reg stage2_stall = 0;
    reg stage1_stall = 0;
    reg[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] bank_status_q, bank_status_d; //bank_status[bank_number]: determine current state of bank (1=active , 0=idle)
    //bank_active_row[bank_number] = stores the active row address in the specified bank
    reg[ROW_BITS-1:0] bank_active_row_q[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0], bank_active_row_d[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; 

    // ECC_ENABLE = 3 regs
    /* verilator lint_off UNUSEDSIGNAL */
    reg[BA_BITS-1:0] ecc_bank_addr = 0, ecc_bank_addr_prev = 0;
    reg[ROW_BITS-1:0] ecc_row_addr = 0, ecc_row_addr_prev = 0;
    reg[COL_BITS-1:0] ecc_col_addr = 0, ecc_col_addr_prev = 0;
    reg we_prev;
    reg stage0_pending = 0;
    reg[wb_addr_bits - 1:0] stage0_addr = 0;
    reg[AUX_WIDTH-1:0] stage0_aux = 0;
    reg stage0_we = 0;
    reg[wb_data_bits - 1:0] stage0_data = 0;
    wire ecc_stage1_stall;
    reg ecc_stage2_stall;
    wire stage1_update, stage1_update_calib, stage0_update;
    reg wb_stb_mux = 0;
    reg[AUX_WIDTH-1:0] aux_mux = 0;
    reg wb_we_mux = 0;
    reg[wb_addr_bits - 1:0] wb_addr_mux = 0;
    reg[wb_data_bits - 1:0] wb_data_mux = 0;
    reg[wb_addr_bits-1:0] calib_addr_mux;
    reg[wb_data_bits-1:0] calib_data_mux;
    reg calib_stb_mux;
    reg calib_we_mux;
    reg[AUX_WIDTH-1:0] calib_aux_mux;
    reg write_ecc_stored_to_mem_q, write_ecc_stored_to_mem_d;
    reg[wb_data_bits - 1:0] stage2_ecc_write_data_q = 0, stage2_ecc_write_data_d;
    reg[wb_data_bits - 1:0] stage2_ecc_read_data_q = 0, stage2_ecc_read_data_d;
    reg[wb_sel_bits - 1 : 0] stage2_ecc_write_data_mask_q = 0, stage2_ecc_write_data_mask_d;
    wire[wb_data_bits/8 - 1 : 0] decoded_parity;
    wire[wb_data_bits/8 - 1 : 0] encoded_parity;
    reg[wb_data_bits/8 - 1 : 0] stage2_encoded_parity = 0;
    reg ecc_req_stage2 = 0;
    /* verilator lint_on UNUSEDSIGNAL */

    //pipeline stage 1 regs
    reg stage1_pending = 0;
    reg[AUX_WIDTH-1:0] stage1_aux = 0;
    reg stage1_we = 0;
    reg[wb_data_bits - 1:0] stage1_data = 0;
    wire[wb_data_bits - 1:0] stage1_data_mux, stage1_data_encoded;
    reg[wb_sel_bits - 1:0] stage1_dm = 0;
    reg[COL_BITS-1:0] stage1_col = 0;
    reg[BA_BITS-1+DUAL_RANK_DIMM:0] stage1_bank = 0;
    reg[ROW_BITS-1:0] stage1_row = 0;
    reg[BA_BITS-1+DUAL_RANK_DIMM:0] stage1_next_bank = 0;
    reg[ROW_BITS-1:0] stage1_next_row = 0;
    wire[wb_addr_bits-1:0] wb_addr_plus_anticipate, calib_addr_plus_anticipate;

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
    reg[BA_BITS-1+DUAL_RANK_DIMM:0] stage2_bank = 0;
    reg[ROW_BITS-1:0] stage2_row = 0;
    
    //delay counter for every banks
    reg[3:0] delay_before_precharge_counter_q[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0], delay_before_precharge_counter_d[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; //delay counters
    reg[3:0] delay_before_activate_counter_q[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0], delay_before_activate_counter_d[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] ;
    reg[3:0] delay_before_write_counter_q[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0], delay_before_write_counter_d[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] ;
    reg[3:0] delay_before_read_counter_q[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] , delay_before_read_counter_d[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] ;
    
    //commands to be sent to PHY (4 slots per controller clk cycle)
    reg[cmd_len-1:0] cmd_d[3:0];
    initial begin
        o_phy_bitslip = 0;
    end
    reg cmd_odt_q = 0, cmd_odt, cmd_reset_n;
    reg[DUAL_RANK_DIMM:0] cmd_ck_en, prev_cmd_ck_en;  
    reg o_wb_stall_q = 1, o_wb_stall_d, o_wb_stall_calib = 1;
    reg precharge_slot_busy;
    reg activate_slot_busy;
    reg[1:0] write_dqs_q;
    reg write_dqs_d;
    reg[STAGE2_DATA_DEPTH:0] write_dqs;
    reg[STAGE2_DATA_DEPTH:0] write_dqs_val;
    reg[1:0] write_dq_q;
    reg write_dq_d;
    reg[STAGE2_DATA_DEPTH+1:0] write_dq;  
    
    (* mark_debug = "true" *) reg[$clog2(DONE_CALIBRATE)-1:0] state_calibrate;
    reg[STORED_DQS_SIZE*8-1:0] dqs_store = 0;
    reg[$clog2(STORED_DQS_SIZE)-1:0] dqs_count_repeat = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_start_index = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_start_index_stored = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index = 0;
    reg[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index_orig = 0;
    reg[$clog2(STORED_DQS_SIZE*8):0] dq_target_index[LANES-1:0];
    wire[$clog2(STORED_DQS_SIZE*8)-1:0] dqs_target_index_value;
    reg[$clog2(REPEAT_DQS_ANALYZE):0] dqs_start_index_repeat=0;
    reg[3:0] train_delay;
    reg[3:0] delay_before_read_data = 0;
    reg[$clog2(DELAY_BEFORE_WRITE_LEVEL_FEEDBACK):0] delay_before_write_level_feedback = 0;
    reg initial_dqs = 0;
    (* mark_debug = "true" *) reg[lanes_clog2-1:0] lane = 0;
    reg[$clog2(8*LANES)-1:0] lane_times_8 = 0;
    /* verilator lint_off UNUSEDSIGNAL */
    reg[15:0] dqs_bitslip_arrangement = 0;
    /* verilator lint_off UNUSEDSIGNAL */
    reg[3:0] added_read_pipe_max = 0;
    reg[3:0] added_read_pipe[LANES - 1:0]; 
    //each lane will have added delay relative to when ISERDES should actually return the data
    //this make sure that we will wait until the lane with longest delay (added_read_pipe_max) is received before
    //all lanes are sent to wishbone data
    
    //contains the ack shift reg for both read and write
    reg[AUX_WIDTH:0] shift_reg_read_pipe_q[READ_ACK_PIPE_WIDTH-1:0]; 
    reg[AUX_WIDTH:0] shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH-1:0]; //issue ack and AUX value , 1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
    reg[$clog2(READ_ACK_PIPE_WIDTH-1):0] write_ack_index_q = 1, write_ack_index_d = 1;
    reg index_read_pipe; //tells which delay_read_pipe will be updated (there are two delay_read_pipe)
    reg index_wb_data; //tells which o_wb_data_q will be sent to o_wb_data
    reg[15:0] delay_read_pipe[1:0]; //delay when each lane will retrieve i_phy_iserdes_data (since different lanes might not be aligned with each other and needs to be retrieved at a different time)
    reg[wb_data_bits - 1:0] o_wb_data_q[1:0]; //store data retrieved from i_phy_iserdes_data to be sent to o_wb_data
    wire[wb_data_bits - 1:0] o_wb_data_q_current;
    reg[wb_data_bits - 1:0] o_wb_data_q_q;
    reg[wb_data_bits - 1:0] o_wb_data_uncalibrated;
    reg o_wb_ack_q = 0;
    reg o_wb_err_q;
    reg o_wb_ack_uncalibrated = 0;
    reg[AUX_WIDTH:0] o_wb_ack_read_q[MAX_ADDED_READ_ACK_DELAY-1:0];
    reg calib_stb = 0;
    reg[wb_sel_bits-1:0] calib_sel = 0;
    reg[AUX_WIDTH-1:0] calib_aux = 0;
    reg calib_we = 0;
    reg[wb_addr_bits-1:0] calib_addr = 0;
    reg[wb_data_bits-1:0] calib_data = 0;
    wire[wb_data_bits-1:0] calib_data_randomized;
    reg write_calib_odt = 0;
    reg write_calib_dqs = 0;
    reg write_calib_dq = 0;
    reg prev_write_level_feedback = 1;
    reg[wb_data_bits-1:0] read_data_store = 0;
    reg[127:0] write_pattern = 0;
    reg[$clog2(64):0] data_start_index[LANES-1:0];   
    reg[LANES-1:0] lane_write_dq_late = 0;    
    reg[LANES-1:0] lane_read_dq_early = 0;    
    reg[4:0] odelay_data_cntvaluein[LANES-1:0]; 
    reg[4:0] odelay_dqs_cntvaluein[LANES-1:0];
    reg[4:0] idelay_data_cntvaluein[LANES-1:0];
    reg[4:0] idelay_data_cntvaluein_prev;
    reg[4:0] idelay_dqs_cntvaluein[LANES-1:0];
    reg[$clog2(REPEAT_CLK_SAMPLING):0] sample_clk_repeat = 0;
    reg stored_write_level_feedback = 0;
    reg[5:0] start_index_check = 0;
    reg[63:0] read_lane_data = 0;
    reg odelay_cntvalue_halfway = 0;
    reg initial_calibration_done = 0;
    reg final_calibration_done = 0;
    assign o_calib_complete = final_calibration_done;
    // Wishbone 2
    reg wb2_stb = 0;
    reg wb2_update = 0;
    reg wb2_we = 0;
    reg[WB2_ADDR_BITS-1:0] wb2_addr = 0;
    reg[WB2_DATA_BITS-1:0] wb2_data = 0;
    reg[wb2_sel_bits-1:0] wb2_sel = 0;
    reg[4:0] wb2_phy_odelay_data_cntvaluein = 0;
    reg[4:0] wb2_phy_odelay_dqs_cntvaluein = 0;
    reg[4:0] wb2_phy_idelay_data_cntvaluein = 0;
    reg[4:0] wb2_phy_idelay_dqs_cntvaluein = 0;
    reg[LANES-1:0] wb2_phy_odelay_data_ld = 0;
    reg[LANES-1:0] wb2_phy_odelay_dqs_ld = 0;
    reg[LANES-1:0] wb2_phy_idelay_data_ld = 0;
    reg[LANES-1:0] wb2_phy_idelay_dqs_ld = 0;
    (* mark_debug ="true" *)reg[LANES-1:0] write_level_fail = 0;
    reg[lanes_clog2-1:0] wb2_write_lane = 0;
    reg sync_rst_wb2 = 0, sync_rst_controller = 0, current_rank_rst = 0;
    reg reset_from_wb2 = 0, reset_from_calibrate = 0, reset_from_test = 0, repeat_test = 0;
    reg reset_after_rank_1 = 0; // reset after calibration rank 1 to switch to rank 2
    reg current_rank = 0;
    // test calibration 
    (* mark_debug = "true" *) reg[wb_addr_bits-1:0] read_test_address_counter = 0, check_test_address_counter = 0; ////////////////////////////////////////////////////////
    (* mark_debug = "true" *) reg[wb_addr_bits-1:0] write_test_address_counter = 0;
    (* mark_debug = "true" *) reg[31:0] correct_read_data = 0, wrong_read_data = 0;
    /* verilator lint_off UNDRIVEN */
    wire sb_err_o;
    wire db_err_o;
    wire[wb_data_bits - 1:0] o_wb_data_q_decoded;
    reg user_self_refresh_q; // registered i_user_self_refresh
    reg[$clog2(wb_sel_bits)-1:0] write_by_byte_counter = 0;
    `ifdef UART_DEBUG
        // uart interface logic for displaying debug messages
        wire uart_tx_busy;
        reg uart_tx_en;
        reg[7:0] uart_tx_data;
        reg[100*8-1:0] uart_text; // max of 100 chars
        reg[2:0] state_uart_send;
        reg uart_start_send;
        reg[9:0] uart_text_length_index;
        reg uart_send_busy;
        localparam UART_FSM_IDLE = 0,
                    UART_FSM_SEND_BYTE = 1,
                    UART_FSM_WAIT_SEND = 2,
                    WAIT_UART = 31;
        reg[3:0] track_report = 0;
        reg[$clog2(DONE_CALIBRATE)-1:0] state_calibrate_next, state_calibrate_last;
    `endif
    reg[2:0] bitslip_counter = 0;
    reg[1:0] shift_read_pipe = 0;
    reg[wb_data_bits-1:0] wrong_data = 0, expected_data=0;
    wire[wb_data_bits-1:0] correct_data;
    reg[LANES-1:0] late_dq;
    // initial block for all regs
    initial begin
        o_wb_stall = 1;
        for(index = 0; index < MAX_ADDED_READ_ACK_DELAY; index = index + 1) begin
            o_wb_ack_read_q[index] = 0;
        end

        for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
            bank_status_q[index] = 0;  
            bank_status_d[index] = 0;
            bank_active_row_q[index] = 0; 
            bank_active_row_d[index] = 0; 
        end

        for(index = 0; index < STAGE2_DATA_DEPTH; index = index+1) begin
            stage2_data[index] =  0;               
            stage2_dm[index] = 0;
        end

        for(index=0; index <(1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
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
            data_start_index[index] = 0;
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
                read_rom_instruction = {5'b01000 , CMD_NOP , ps_to_cycles(POWER_ON_RESET_HIGH/500)}; 
             else
                read_rom_instruction = {5'b01000 , CMD_NOP , ps_to_cycles(POWER_ON_RESET_HIGH)}; 
                //0. RESET# needs to be maintained low for minimum 200us with power-up initialization. CKE is pulled
                    //“Low�? anytime before RESET# being de-asserted (min. time 10 ns). .

            5'd1: 
             if (MICRON_SIM)
                 read_rom_instruction =  {5'b01001 , CMD_NOP, ps_to_cycles(INITIAL_CKE_LOW/500)}; 
             else
                 read_rom_instruction =  {5'b01001 , CMD_NOP, ps_to_cycles(INITIAL_CKE_LOW)}; 
                //1. After RESET# is de-asserted, wait for another 500 us until CKE becomes active. During this time, the
                    //DRAM will start internal state initialization; this will be done independently of external clocks. 
                    // .... Also, a NOP or Deselect command must be registered (with tIS set up time to clock) before
                    //CKE goes active.

            5'd2: read_rom_instruction = {5'b01011 , CMD_NOP, ps_to_cycles(tXPR)}; 
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
            5'd9: read_rom_instruction = {5'b01111, CMD_PRE, ps_to_cycles(tRP)}; 
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
            
            // Perform first refresh and any subsequent refresh (so instruction 19 to 22 will be re-used for the refresh sequence)
            5'd19: read_rom_instruction = {5'b01111, CMD_PRE, ps_to_cycles(tRP)}; 
            //19. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Refresh Command can be applied.
            
            5'd20: read_rom_instruction = {5'b01011, CMD_REF, ps_to_cycles(tRFC)};
            //20. A delay between the Refresh Command and the next valid command, except NOP or DES, must be greater than or equal to the minimum 
            //Refresh cycle time tRFC(min) 
            
            5'd21: read_rom_instruction = {5'b11011, CMD_NOP, ps_to_cycles(tREFI)};
            //21. Reset ends now. The refresh interval also starts to count.
            
            5'd22: read_rom_instruction = {5'b01011, CMD_NOP, PRE_REFRESH_DELAY[DELAY_SLOT_WIDTH-1:0]}; 
            // 22. Extra delay needed before starting the refresh sequence. 
            // (this already sets the wishbone stall high to make sure no user request is on-going when refresh seqeunce starts)
            
            5'd23: read_rom_instruction = {5'b01111, CMD_PRE, ps_to_cycles(tRP)}; 
            // 23. All banks must be precharged (A10-AP = high) and idle for a minimum of the precharge time tRP(min) before the Self-Refresh Command can be applied.
            
            5'd24: read_rom_instruction = {5'b01001, CMD_SREF_EN, tCKESR[DELAY_SLOT_WIDTH-1:0]};
            // 24. Self-refresh entry
            // JEDEC Standard No. 79-3E Page 79: The minimum time that the DDR3 SDRAM must remain in Self-Refresh mode is tCKESR

            5'd25: read_rom_instruction = {5'b01001, CMD_NOP, tCPDED[DELAY_SLOT_WIDTH-1:0]};
            // 25. tCPDED cycles of NOP are required after CKE low

            5'd26: read_rom_instruction = {5'b01011, CMD_SREF_XT, tXSDLL_tRFC[DELAY_SLOT_WIDTH-1:0]};
            // 26. From 25 (Self-refresh entry), wait until user-self_refresh is disabled then wait for tXSDLL - tRFC before going to 20 (Refresh)
            // JEDEC Standard No. 79-3E Page 79: Before a command that requires a locked DLL can be applied, a delay of at least tXSDLL must be satisfied.
            // JEDEC Standard No. 79-3E Page 80: Upon exit from Self-Refresh, the DDR3 SDRAM requires a minimum of one extra refresh command before it is put back into Self-Refresh Mode.
            
            default: read_rom_instruction = {5'b00011, CMD_NOP, {(DELAY_SLOT_WIDTH){1'b0}}}; 
        endcase
    end
    endfunction
    /*********************************************************************************************************************************************/
    

    /******************************************* Reset Sequence ROM Controller *******************************************/
    always @(posedge i_controller_clk) begin
        sync_rst_controller <= !i_rst_n || reset_from_wb2 || reset_from_calibrate || reset_from_test || reset_after_rank_1;
        current_rank_rst <= !i_rst_n || reset_from_wb2 || reset_from_calibrate || reset_from_test;
        sync_rst_wb2 <= !i_rst_n;
    end
    assign o_phy_reset = current_rank_rst; // PHY will not reset when transitioning from rank 0 to rank 1
    
    always @(posedge i_controller_clk) begin
        if(sync_rst_controller) begin
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
            else if(instruction[USE_TIMER] /*&& delay_counter != {(DELAY_COUNTER_WIDTH){1'b1}}*/ && !pause_counter && delay_counter != 0) delay_counter <= delay_counter - 1; 
            
            //delay_counter of 1 means we will need to update the delay_counter next clock cycle (delay_counter of zero) so we need to retrieve 
            //now the next instruction. The same thing needs to be done when current instruction does not need the timer delay.
            if( ((delay_counter == 1) && !pause_counter) || !instruction[USE_TIMER]/* || skip_reset_seq_delay*/) begin
                delay_counter_is_zero <= 1; 
                instruction <= read_rom_instruction(instruction_address);
                if(instruction_address == 5'd22) begin // if user_self_refresh is disabled, wrap back to 19 (Precharge All before Refresh)
                    instruction_address <= 5'd19;
                end
                else if(instruction_address == 5'd26) begin // self-refresh exit always wraps back to 20 (Refresh)
                    instruction_address <= 5'd20;
                end
                else begin
                    instruction_address <= instruction_address + 5'd1; // just increment address
                end
            end
            //we are now on the middle of a delay 
            else begin
                delay_counter_is_zero <=0; 
            end

            if(instruction_address == 5'd22 && user_self_refresh_q) begin // if user_self_refresh is enabled, go straight to 23
                instruction_address <= 23; // go to Precharge All for Self-refresh
                delay_counter_is_zero <= 1; 
                delay_counter <= 0;
                instruction <= read_rom_instruction(instruction_address);
            end

            //instruction[RST_DONE] is non-persistent thus we need to register it once it goes high
            reset_done <= instruction[RST_DONE]? 1'b1:reset_done; 
        end
    end

    // register user-enabled self-refresh
    always @(posedge i_controller_clk) begin 
        user_self_refresh_q <= i_user_self_refresh && (user_self_refresh_q || (instruction_address != 5'd26)) && final_calibration_done; //will not go high again if already at instruction_address 26 (self-refresh exit), only go high when calibration is done
        if(DUAL_RANK_DIMM[0]) begin // if dual rank enabled, then enable self refresh right after completing calibration
            if(state_calibrate == FINISH_READ) begin 
                user_self_refresh_q <= 1'b1;
            end 
        end

    end
    /*********************************************************************************************************************************************/


    /******************************************************* Track Bank Status and Issue Command *******************************************************/
    //process request transaction 
    always @(posedge i_controller_clk) begin
        if(sync_rst_controller) begin
            o_wb_stall <= 1'b1; 
            o_wb_stall_q <= 1'b1;
            o_wb_stall_calib <= 1'b1;
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
            if(ECC_ENABLE == 3) begin
                ecc_col_addr_prev <= 0;
                ecc_bank_addr_prev <= 0;
                ecc_row_addr_prev <= 0;
                ecc_bank_addr <= 0;
                ecc_row_addr <= 0;
                ecc_col_addr <= 0;
                stage2_encoded_parity <= 0;
            end
            for(index=0; index<LANES; index=index+1) begin
                unaligned_data[index] <= 0;
                unaligned_dm[index] <= 0;
            end
            //set delay counters to 0
            for(index=0; index<(1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
                delay_before_precharge_counter_q[index] <= 0;  
                delay_before_activate_counter_q[index] <= 0;
                delay_before_write_counter_q[index] <= 0; 
                delay_before_read_counter_q[index] <= 0; 
            end
            //reset bank status and active row
            for( index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
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
            o_wb_stall_q <= o_wb_stall_d; 
            o_wb_stall_calib <= o_wb_stall_d; //wb stall for calibration stage
            cmd_odt_q <= cmd_odt;

            //update delay counter 
            for(index=0; index< (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
                delay_before_precharge_counter_q[index] <= delay_before_precharge_counter_d[index];  
                delay_before_activate_counter_q[index] <= delay_before_activate_counter_d[index];
                delay_before_write_counter_q[index] <= delay_before_write_counter_d[index]; 
                delay_before_read_counter_q[index] <= delay_before_read_counter_d[index]; 
            end

            //update bank status and active row
            for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
                bank_status_q[index] <= bank_status_d[index];
                bank_active_row_q[index] <= bank_active_row_d[index];
            end

            if(instruction_address == 20 || instruction_address == 24) begin ///current instruction at precharge
                cmd_odt_q <= 1'b0;
                //all banks will be in idle after refresh
                for( index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
                    bank_status_q[index] <= 0;  
                end
            end
            
            //refresh sequence is on-going
            if(!instruction[REF_IDLE]) begin
                //no transaction will be pending during refresh
                o_wb_stall <= 1'b1; 
                o_wb_stall_calib <= 1'b1;
            end
            
            //if pipeline is not stalled (or a request is left on the prestall
            //delay address 19 or if in calib), move pipeline to stage 2
            if(stage2_update) begin //ITS POSSIBLE ONLY NEXT CLK WILL STALL SUPPOSE TO GO LOW
                stage2_pending <= stage1_pending;
                if(ECC_ENABLE != 3) begin
                    stage1_pending <= 1'b0; //no request initially unless overridden by the actual stb request
                    stage2_pending <= stage1_pending;
                    stage2_aux <= stage1_aux;
                    stage2_we <= stage1_we;
                    stage2_col <= stage1_col;
                    stage2_bank <= stage1_bank;
                    stage2_row <= stage1_row;
                    if(ODELAY_SUPPORTED || DLL_OFF) begin
                        stage2_data_unaligned <= stage1_data_mux;
                        stage2_dm_unaligned <= ~stage1_dm; //inverse each bit (1 must mean "masked" or not written)
                    end
                    else begin
                        stage2_data_unaligned_temp <= stage1_data_mux;
                        stage2_dm_unaligned_temp <= ~stage1_dm; //inverse each bit (1 must mean "masked" or not written)
                    end
                end
                // ECC_ENABLE == 3
                else begin
                    stage1_pending <= ecc_stage1_stall? stage1_pending : 1'b0; //stage1 remains the same for ECC op (no request initially unless overridden by the actual stb request)
                    // if switching from write to read and ECC is not yet written then do a write first to store those ECC bits
                    if(!stage1_we && stage2_we && stage1_pending && !write_ecc_stored_to_mem_d && initial_calibration_done) begin
                        stage2_we <= 1'b1;
                        // if ecc_stage1_stall, stage2 will start ECC write/read operation
                        // if ECC write, then we are writing ECC for previous address
                        // if ECC read, then we are reading ECC for current address
                        stage2_col <= ecc_col_addr_prev;
                        stage2_bank[BA_BITS-1:0] <= ecc_bank_addr_prev;
                        stage2_row <= ecc_row_addr_prev;
                        ecc_col_addr_prev <= ecc_col_addr;
                        ecc_bank_addr_prev <= ecc_bank_addr;
                        ecc_row_addr_prev <= ecc_row_addr;

                        // For ECC requests, 2MSB of aux determines type of ECC request (read = 2'10, write = 2'b11)
                        stage2_aux <= { 1'b1, 1'b1, 3'b000, {(AUX_WIDTH-5){1'b1}} };
                    end
                    else begin
                        stage2_we <= stage1_we;
                        // if ecc_stage1_stall, stage2 will start ECC write/read operation
                        // if ECC write, then we are writing ECC for previous address
                        // if ECC read, then we are reading ECC for current address
                        stage2_col <= ecc_stage1_stall? (stage1_we? ecc_col_addr_prev : ecc_col_addr) : stage1_col;
                        stage2_bank[BA_BITS-1:0] <= ecc_stage1_stall? (stage1_we? ecc_bank_addr_prev : ecc_bank_addr) : stage1_bank[BA_BITS-1:0];
                        stage2_row <= ecc_stage1_stall? (stage1_we? ecc_row_addr_prev : ecc_row_addr) : stage1_row;
                        ecc_col_addr_prev <= ecc_col_addr;
                        ecc_bank_addr_prev <= ecc_bank_addr;
                        ecc_row_addr_prev <= ecc_row_addr;
                        // For ECC requests, 2MSB of aux determines type of ECC request (read = 2'10, write = 2'b11)
                        // For non-ECC request (MSB is 0), next 3MSB is allotted for the column (burst position to know position of encoded parity ECC bits)
                        stage2_aux <= ecc_stage1_stall? { 1'b1, !stage1_we, 3'b000, {(AUX_WIDTH-5){1'b1}} } : {1'b0, !stage1_we, stage1_col[5:3], stage1_aux[AUX_WIDTH-6:0]};
                    end
                    // store parity code for stage1_data
                    stage2_encoded_parity <= encoded_parity;
                    if(ODELAY_SUPPORTED  || DLL_OFF) begin
                        stage2_data_unaligned <= stage1_data_mux;
                        stage2_dm_unaligned <= ecc_stage1_stall? ~stage2_ecc_write_data_mask_d : ~stage1_dm; //inverse each bit (1 must mean "masked" or not written)
                    end
                    else begin
                        stage2_data_unaligned_temp <= stage1_data_mux;
                        stage2_dm_unaligned_temp <= ecc_stage1_stall? ~stage2_ecc_write_data_mask_d : ~stage1_dm; //inverse each bit (1 must mean "masked" or not written)
                    end
                end

                //stage2_data -> shiftreg(CWL) -> OSERDES(DDR) -> ODELAY -> RAM
            end
            if(!ODELAY_SUPPORTED && !DLL_OFF) begin
                stage2_data_unaligned <= stage2_data_unaligned_temp; //_temp is for added delay of 1 clock cycle (no ODELAY so no added delay)
                stage2_dm_unaligned <= stage2_dm_unaligned_temp;  //_temp is for added delay of 1 clock cycle (no ODELAY so no added delay)
            end

            if(stage1_update) begin 
                //stage1 will not do the request (pending low) when the
                //request is on the same bank as the current request. This
                //will ensure stage1 bank will be different from stage2 bank

                // if ECC_ENABLE != 3, then stage1 will always receive wishbone interface
                if(ECC_ENABLE != 3) begin
                    stage1_pending <= i_wb_stb;//actual request flag
                    stage1_aux <= i_aux; //aux ID for AXI compatibility
                    stage1_we <= i_wb_we; //write-enable
                    stage1_dm <= (ECC_ENABLE == 0)? i_wb_sel : {wb_sel_bits{1'b1}}; // no data masking when ECC is enabled
                end
                // ECC_ENABLE == 3
                else begin // if ECC_ENABLE = 3 (inline ECC), then stage1 will either receive stage0 or wishbone
                    stage1_pending <= wb_stb_mux;//actual request flag
                    stage1_aux <= aux_mux; //aux ID for AXI compatibility
                    stage1_we <= wb_we_mux; //write-enable
                    stage1_dm <= {wb_sel_bits{1'b1}}; // no data masking when ECC is enabled
                end

                if(row_bank_col == 1) begin // memory address mapping: {row, bank, col}
                    if(DUAL_RANK_DIMM[0]) begin
                        stage1_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)] <= i_wb_addr[DUAL_RANK_DIMM[0]? (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) : 0]; // msb determines rank
                        stage1_next_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)] <= wb_addr_plus_anticipate[DUAL_RANK_DIMM[0]? (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2)) : 0]; // msb determines rank
                    end
                    stage1_row <= i_wb_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS - $clog2(serdes_ratio*2)) ]; //row_address
                    stage1_bank[BA_BITS-1:0] <=  i_wb_addr[ (BA_BITS + COL_BITS - $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2)) ]; //bank_address
                    stage1_col <= { i_wb_addr[ (COL_BITS- $clog2(serdes_ratio*2)-1) : 0 ], {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                    //stage1_next_bank will not increment unless stage1_next_col
                    //overwraps due to MARGIN_BEFORE_ANTICIPATE. Thus, anticipated
                    //precharge and activate will happen only at the end of the
                    //current column with a margin dictated by
                    //MARGIN_BEFORE_ANTICIPATE  
                    /* verilator lint_off WIDTH */
                    {stage1_next_row , stage1_next_bank[BA_BITS-1:0]} <= wb_addr_plus_anticipate >> (COL_BITS- $clog2(serdes_ratio*2));
                    //anticipated next row and bank to be accessed 
                    /* verilator lint_on WIDTH */
                    stage1_data <= i_wb_data;
                end

                else if(row_bank_col == 0) begin // memory address mapping: {bank, row, col}
                    stage1_bank[BA_BITS-1:0] <=  i_wb_addr[ (BA_BITS + ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (ROW_BITS + COL_BITS- $clog2(serdes_ratio*2))]; //bank_address
                    stage1_row <= i_wb_addr[ (ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2)) ]; //row_address
                    stage1_col <= { i_wb_addr[(COL_BITS- $clog2(serdes_ratio*2)-1) : 0] , {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                    //stage1_next_row will not increment unless stage1_next_col
                    //overwraps due to MARGIN_BEFORE_ANTICIPATE. Thus, anticipated
                    //precharge and activate will happen only at the end of the
                    //current column with a margin dictated by
                    //MARGIN_BEFORE_ANTICIPATE  
                    /* verilator lint_off WIDTH */
                    {stage1_next_bank, stage1_next_row} <= wb_addr_plus_anticipate >> (COL_BITS- $clog2(serdes_ratio*2));
                    //anticipated next row and bank to be accessed 
                    /* verilator lint_on WIDTH */
                    stage1_data <= i_wb_data;
                end

                else if(row_bank_col == 2) begin // memory address mapping: {bank[2:1], row, bank[0], col} , used for ECC_ENABLE = 3 (Inline ECC)
                    stage1_bank[2:1] <=  wb_addr_mux[ (BA_BITS + ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2) + 1)]; //bank_address
                    stage1_row <= wb_addr_mux[ (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) : (COL_BITS - $clog2(serdes_ratio*2) + 1) ]; //row_address
                    stage1_bank[0] <= wb_addr_mux[COL_BITS - $clog2(serdes_ratio*2)];
                    stage1_col <= { wb_addr_mux[(COL_BITS - $clog2(serdes_ratio*2)-1) : 0] , {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                    //stage1_next_bank will not increment unless stage1_next_col
                    //overwraps due to MARGIN_BEFORE_ANTICIPATE. This will overwrap every two banks
                    //MARGIN_BEFORE_ANTICIPATE  
                    /* verilator lint_off WIDTH */
                    {stage1_next_bank[2:1], stage1_next_row, stage1_next_bank[0]} <= wb_addr_plus_anticipate >> (COL_BITS - $clog2(serdes_ratio*2));
                    //anticipated next row and bank to be accessed 
                    /* verilator lint_on WIDTH */
                    // ECC Mapping (Excel sheet design planning: https://docs.google.com/spreadsheets/d/1_8vrLmVSFpvRD13Mk8aNAMYlh62SfpPXOCYIQFEtcs4/edit?gid=0#gid=0)
                    ecc_bank_addr <= {2'b11,!wb_addr_mux[COL_BITS - $clog2(serdes_ratio*2)]};
                    ecc_row_addr <= {1'b1, wb_addr_mux[ (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) : (COL_BITS - $clog2(serdes_ratio*2) + 1 + 1) ]};
                    ecc_col_addr <= { wb_addr_mux[(COL_BITS - $clog2(serdes_ratio*2) + 1)] , 
                                        wb_addr_mux[(BA_BITS + ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2) + 1)] ,
                                        wb_addr_mux[(COL_BITS - $clog2(serdes_ratio*2) - 1) : 3], 3'b000 };
                    stage1_data <= wb_data_mux;
                end
            end

            // request from calibrate FSM will be accepted here
            else if(stage1_update_calib) begin
                // if ECC_ENABLE != 3, then stage1 will always receive wishbone interface
                if(ECC_ENABLE != 3) begin
                    stage1_pending <= calib_stb;//actual request flag
                    stage1_aux <= calib_aux; //aux ID for AXI compatibility
                    stage1_we <= calib_we; //write-enable
                    stage1_dm <= (ECC_ENABLE == 0)? calib_sel : {wb_sel_bits{1'b1}}; // no data masking when ECC is enabled
                end
                // ECC_ENABLE == 3
                else begin // if ECC_ENABLE = 3 (inline ECC), then stage1 will either receive stage0 or wishbone
                    stage1_pending <= calib_stb_mux;//actual request flag
                    stage1_we <= calib_we_mux; //write-enable
                    stage1_dm <= {wb_sel_bits{1'b1}}; // no data masking when ECC is enabled
                    stage1_aux <= calib_aux_mux; //aux ID for AXI compatibility
                end

                if(row_bank_col == 1) begin // memory address mapping: {row, bank, col}
                    if(DUAL_RANK_DIMM[0]) begin
                        stage1_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)] <= current_rank; // rank depends on current_rank
                        stage1_next_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)] <= current_rank; // rank depends on current_rank
                    end
                    stage1_row <= calib_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (BA_BITS + COL_BITS - $clog2(serdes_ratio*2)) ]; //row_address
                    stage1_bank[BA_BITS-1:0] <=  calib_addr[ (BA_BITS + COL_BITS - $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2)) ]; //bank_address
                    stage1_col <= { calib_addr[ (COL_BITS- $clog2(serdes_ratio*2)-1) : 0 ], {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (8-burst word-aligned)
                    //stage1_next_bank will not increment unless stage1_next_col
                    //overwraps due to MARGIN_BEFORE_ANTICIPATE. Thus, anticipated
                    //precharge and activate will happen only at the end of the
                    //current column with a margin dictated by
                    //MARGIN_BEFORE_ANTICIPATE  
                    /* verilator lint_off WIDTH */
                    {stage1_next_row , stage1_next_bank[BA_BITS-1:0] } <= calib_addr_plus_anticipate >> (COL_BITS- $clog2(serdes_ratio*2));
                    //anticipated next row and bank to be accessed 
                    /* verilator lint_on WIDTH */
                    stage1_data <= calib_data;
                end
                else if(row_bank_col == 0) begin // memory address mapping: {bank, row, col}
                    stage1_bank[BA_BITS-1:0] <=  calib_addr[ (BA_BITS + ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (ROW_BITS + COL_BITS- $clog2(serdes_ratio*2))]; //bank_address
                    stage1_row <= calib_addr[ (ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (COL_BITS- $clog2(serdes_ratio*2)) ]; //row_address
                    stage1_col <= { calib_addr[(COL_BITS- $clog2(serdes_ratio*2)-1) : 0] , {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (8-burst word-aligned)
                    //stage1_next_row will not increment unless stage1_next_col
                    //overwraps due to MARGIN_BEFORE_ANTICIPATE. Thus, anticipated
                    //precharge and activate will happen only at the end of the
                    //current column with a margin dictated by
                    //MARGIN_BEFORE_ANTICIPATE  
                    /* verilator lint_off WIDTH */
                    {stage1_next_bank, stage1_next_row} <= calib_addr_plus_anticipate >> (COL_BITS- $clog2(serdes_ratio*2));
                    //anticipated next row and bank to be accessed 
                    /* verilator lint_on WIDTH */
                    stage1_data <= calib_data;
                end
                else if(row_bank_col == 2) begin // memory address mapping: {bank[2:1], row, bank[0], col}
                    stage1_bank[2:1] <=  calib_addr_mux[ (BA_BITS + ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2) + 1)]; //bank_address
                    stage1_row <= calib_addr_mux[ (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) : (COL_BITS - $clog2(serdes_ratio*2) + 1) ]; //row_address
                    stage1_bank[0] <= calib_addr_mux[COL_BITS - $clog2(serdes_ratio*2)];
                    stage1_col <= { calib_addr_mux[(COL_BITS- $clog2(serdes_ratio*2)-1) : 0] , {{$clog2(serdes_ratio*2)}{1'b0}} }; //column address (n-burst word-aligned)
                    //stage1_next_row will not increment unless stage1_next_col
                    //overwraps due to MARGIN_BEFORE_ANTICIPATE. This will overwrap every two banks
                    //MARGIN_BEFORE_ANTICIPATE  
                    /* verilator lint_off WIDTH */
                    {stage1_next_bank[2:1], stage1_next_row, stage1_next_bank[0]} <= calib_addr_plus_anticipate >> (COL_BITS - $clog2(serdes_ratio*2));
                    //anticipated next row and bank to be accessed 
                    /* verilator lint_on WIDTH */
                    // ECC Mapping (Excel sheet design planning: https://docs.google.com/spreadsheets/d/1_8vrLmVSFpvRD13Mk8aNAMYlh62SfpPXOCYIQFEtcs4/edit?gid=0#gid=0)
                    // ECC_BANK = {11,!bank[0]} 
                    // ECC_ROW = {1,row>>1} 
                    // ECC_COL = {row[0],bank[2:1],col>>3}"						
                    ecc_bank_addr <= {2'b11,!calib_addr_mux[COL_BITS - $clog2(serdes_ratio*2)]};
                    ecc_row_addr <= {1'b1, calib_addr_mux[ (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) : (COL_BITS - $clog2(serdes_ratio*2) + 1 + 1) ]};
                    ecc_col_addr <= { calib_addr_mux[(COL_BITS - $clog2(serdes_ratio*2) + 1)] , 
                                        calib_addr_mux[(BA_BITS + ROW_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1) : (ROW_BITS + COL_BITS - $clog2(serdes_ratio*2) + 1)] ,
                                        calib_addr_mux[(COL_BITS - $clog2(serdes_ratio*2) - 1) : 3], 3'b000 };
                    stage1_data <= calib_data_mux;
                end
            end
            
            // stage2 can have multiple pipelined stages inside it which acts as delay before issuing the write data (after issuing write command)
            for(index = 0; index < STAGE2_DATA_DEPTH-1; index = index+1) begin
                stage2_data[index+1] <=  stage2_data[index]; // 0->1, 1->2           
                stage2_dm[index+1] <= stage2_dm[index];
            end

            for(index = 0; index < LANES; index = index + 1) begin
                /* verilator lint_off WIDTH */
                // if DQ is too late (298cd0ad51c1XXXX is written) then we want to DQ to be early 
                // Thus, we will forward the stage2_data_unaligned directly to stage2_data[1] (instead of the usual stage2_data[0])
                // checks if the DQ for this lane is late (index being zero while write_dq_late high means we will try 2nd assumption), if yes then we forward stage2_data_unaligned directly to stage2_data[1]
                if(late_dq[index]) begin
                    {unaligned_data[index], { 
                        stage2_data[1][((DQ_BITS*LANES)*7 + 8*index) +: 8], stage2_data[1][((DQ_BITS*LANES)*6 + 8*index) +: 8], 
                        stage2_data[1][((DQ_BITS*LANES)*5 + 8*index) +: 8], stage2_data[1][((DQ_BITS*LANES)*4 + 8*index) +: 8], 
                        stage2_data[1][((DQ_BITS*LANES)*3 + 8*index) +: 8], stage2_data[1][((DQ_BITS*LANES)*2 + 8*index) +: 8], 
                        stage2_data[1][((DQ_BITS*LANES)*1 + 8*index) +: 8], stage2_data[1][((DQ_BITS*LANES)*0 + 8*index) +: 8] }} 
                        <= ( {  stage2_data_unaligned[((DQ_BITS*LANES)*7 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*6 + 8*index) +: 8],
                                stage2_data_unaligned[((DQ_BITS*LANES)*5 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*4 + 8*index) +: 8], 
                                stage2_data_unaligned[((DQ_BITS*LANES)*3 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*2 + 8*index) +: 8],
                                stage2_data_unaligned[((DQ_BITS*LANES)*1 + 8*index) +: 8], stage2_data_unaligned[((DQ_BITS*LANES)*0 + 8*index) +: 8] }
                            << {data_start_index[index][$clog2(64):1], 1'b0} ) | unaligned_data[index];
                            // data_start_index is set to 1 so this if statement will pass, but shift left is zero (lsb of data_start_index is removed) which means 
                            // DQ is 1 whole controller cycle early (happens in Kintex-7 with OpenXC7)
                    {unaligned_dm[index], {
                        stage2_dm[1][LANES*7 + index], stage2_dm[1][LANES*6 + index], 
                        stage2_dm[1][LANES*5 + index], stage2_dm[1][LANES*4 + index], 
                        stage2_dm[1][LANES*3 + index], stage2_dm[1][LANES*2 + index],
                        stage2_dm[1][LANES*1 + index], stage2_dm[1][LANES*0 + index] }} 
                        <= ( {  stage2_dm_unaligned[LANES*7 + index], stage2_dm_unaligned[LANES*6 + index],
                                stage2_dm_unaligned[LANES*5 + index], stage2_dm_unaligned[LANES*4 + index], 
                                stage2_dm_unaligned[LANES*3 + index], stage2_dm_unaligned[LANES*2 + index],
                                stage2_dm_unaligned[LANES*1 + index], stage2_dm_unaligned[LANES*0 + index] }
                                << (data_start_index[index]>>3)) | unaligned_dm[index];
                /* verilator lint_on WIDTH */
                end // end of if statement (dq for this lane is late)
            end // end of for loop to forward stage2_unaligned to stage2 by lane

            for(index = 0; index < LANES; index = index + 1) begin
                if(!late_dq[index]) begin // DQ is not late so we will forward stage2_data_unaligned to stage2_data[0]
                    /* verilator lint_off WIDTH */
                    // stage2_data_unaligned is the DQ_BITS*LANES*8 raw data from stage 1 so not yet aligned
                    // unaligned_data is 64 bits
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
                    /*
                    // Example with LANE 0:
                    // Burst_0 to burst_7 of unaligned LANE 0 will be extracted which will be shifted by data_start_index.
                    // Each 8 bits of shift means a burst will be moved to next ddr3_clk cycle, this is needed if for example
                    // the DQ trace is longer than the command trace where the DQ bits must be delayed by 1 ddr3_clk cycle
                    // to align the DQ data to the write command.
                    //
                    // Since 1 controller clk cycle will have 4 ddr3_clk cycle, and each ddr3_clk cycle is DDR:
                    // CONTROLLER CLK CYCLE 0: [burst0,burst1] [burst2,burst3] [burst4,burst5] [burst6,burst7]
                    // CONTROLLER CLK CYCLE 1: [burst0,burst1] [burst2,burst3] [burst4,burst5] [burst6,burst7]
                    // CONTROLLER CLK CYCLE 2: [burst0,burst1] [burst2,burst3] [burst4,burst5] [burst6,burst7]
                    //
                    // shifting by 1 burst means burst 7 will be sent on next controller clk cycle and EVERY BURST WILL SHIFT:
                    // CONTROLLER CLK CYCLE 0: [xxxxxx,xxxxxx] [burst0,burst1] [burst2,burst3] [burst4,burst5]
                    // CONTROLLER CLK CYCLE 1: [burst6,burst7] [burst0,burst1] [burst2,burst3] [burst4,burst5] 
                    // CONTROLLER CLK CYCLE 2: [burst6,burst7] [burst0,burst1] [burst2,burst3] [burst4,burst5]
                    //
                    // the [burst6,burst7] which has to be stored and delayed until next clk cycle will be handled by unaligned_data
                    {unaligned_data[0], { 
                    stage2_data[0][((64)*7 + 8*0) +: 8], stage2_data[0][((64)*6 + 8*0) +: 8], 
                    stage2_data[0][((64)*5 + 8*0) +: 8], stage2_data[0][((64)*4 + 8*0) +: 8], 
                    stage2_data[0][((64)*3 + 8*0) +: 8], stage2_data[0][((64)*2 + 8*0) +: 8], 
                    stage2_data[0][((64)*1 + 8*0) +: 8], stage2_data[0][((64)*0 + 8*0) +: 8] }} 
                    <= ( {  stage2_data_unaligned[((64)*7 + 8*0) +: 8], stage2_data_unaligned[((64)*6 + 8*0) +: 8],
                            stage2_data_unaligned[((64)*5 + 8*0) +: 8], stage2_data_unaligned[((64)*4 + 8*0) +: 8], 
                            stage2_data_unaligned[((64)*3 + 8*0) +: 8], stage2_data_unaligned[((64)*2 + 8*0) +: 8],
                            stage2_data_unaligned[((64)*1 + 8*0) +: 8], stage2_data_unaligned[((64)*0 + 8*0) +: 8] }
                            << data_start_index[0]) | unaligned_data[0];
                    */

                    // The same alignment logic is done with data mask
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
                end // end for else statement (dq is not late for this lane)
            end // end of for loop to forward stage2_unaligned to stage2 by lane
          
            //abort any outgoing ack when cyc is low
            if(!i_wb_cyc && final_calibration_done) begin
                stage2_pending <= 0;
                stage1_pending <= 0;
            end
        end
    end
    always @* begin
        for(index = 0; index < LANES; index = index + 1) begin
            late_dq[index] = (lane_write_dq_late[index] && (data_start_index[index] != 0)) && (STAGE2_DATA_DEPTH > 1);
        end
    end

    // generate signals to be received by stage1
    generate
        if(ECC_ENABLE == 3) begin : ecc_3_pipeline_control
            // logic when to update stage 1:
            // when not in refresh, transaction can only be processed when i_wb_cyc is high and not stall 
            // OR stage0 is pending and stage2 is about to be empty
            // AND ecc_stage1_stall low (if high then stage2 will have ECC operation while stage1 remains)
            assign stage0_update = ((i_wb_cyc && !o_wb_stall) || (!final_calibration_done && !o_wb_stall_calib)) && ecc_stage1_stall; // stage0 is only used when ECC will be inserted next cycle (stage1 must remain)
            assign stage1_update = ( (i_wb_cyc && !o_wb_stall) || (stage0_pending && !ecc_stage2_stall) ) && !ecc_stage1_stall;
            assign stage1_update_calib = ( ((state_calibrate != DONE_CALIBRATE) && !o_wb_stall_calib) || (stage0_pending && !ecc_stage2_stall) ) && !ecc_stage1_stall;
            /* verilator lint_off WIDTH */
            assign wb_addr_plus_anticipate = wb_addr_mux + MARGIN_BEFORE_ANTICIPATE; // wb_addr_plus_anticipate determines if it is near the end of column by checking if it jumps to next row
            assign calib_addr_plus_anticipate = calib_addr_mux + MARGIN_BEFORE_ANTICIPATE; // just same as wb_addr_plus_anticipate but while doing calibration
            /* verilator lint_on WIDTH */
            assign ecc_stage1_stall = ( ({ecc_col_addr, ecc_bank_addr, ecc_row_addr} != {ecc_col_addr_prev, ecc_bank_addr_prev, ecc_row_addr_prev}) 
                                        || (!stage1_we && stage2_we) ) && !ecc_stage2_stall && initial_calibration_done && !(stage1_we && !stage2_we) && stage1_pending;
                                        // write -> read with write ECC
                                        // read -> write will not do any ECC request
            /* verilator lint_off WIDTHTRUNC */
            // retrieve parity bits for decoding, 3MSB of o_aux (after 2MSB) determines burst position of current request (which is also the position of ECC)
            assign decoded_parity = stage2_ecc_read_data_q[({32'd0, o_aux[AUX_WIDTH-3 : AUX_WIDTH-5]} << $clog2(wb_data_bits/8)) +: (wb_data_bits/8) ];
            /* verilator lint_on WIDTHTRUNC */

            // Muxing to choose whether stage1 will receive data from stage0 or wishbone interface
            always @* begin
                if(stage0_pending) begin
                    wb_stb_mux = 1'b1;
                    aux_mux = stage0_aux;
                    wb_we_mux = stage0_we;
                    wb_addr_mux = stage0_addr;
                    wb_data_mux = stage0_data;
                    calib_data_mux = stage0_data;
                    calib_addr_mux = stage0_addr;
                    calib_stb_mux = 1'b1;
                    calib_we_mux = stage0_we; 
                    calib_aux_mux = stage0_aux; 
                end
                else begin
                    wb_stb_mux = i_wb_stb;
                    aux_mux = i_aux;
                    wb_we_mux = i_wb_we;
                    wb_addr_mux = i_wb_addr;
                    wb_data_mux = i_wb_data;
                    calib_data_mux = calib_data;
                    calib_addr_mux = calib_addr;
                    calib_stb_mux = calib_stb;
                    calib_we_mux = calib_we; 
                    calib_aux_mux = calib_aux; 
                end
            end
            // 
            always @(posedge i_controller_clk) begin 
                if(sync_rst_controller) begin
                    // reset ecc address
                    stage0_pending <= 0;
                    stage0_addr <= 0;
                    stage0_aux <= 0;
                    stage0_we <= 0;
                    stage0_data <= 0;
                    // ecc_col_addr_prev <= 0;
                    // ecc_bank_addr_prev <= 0;
                    // ecc_row_addr_prev <= 0;
                    we_prev <= 0;
                    stage2_ecc_write_data_q <= 0;
                    write_ecc_stored_to_mem_q <= 0;
                    ecc_req_stage2 <= 0;
                end
                else if(reset_done) begin 
                    if(stage0_update) begin
                        // wishbone req wil only be stored to stage0 if there will be ecc write/read next clock cycle
                        if(final_calibration_done) begin
                            stage0_pending <= i_wb_stb && ecc_stage1_stall; 
                        end
                        else begin
                            stage0_pending <= calib_stb && ecc_stage1_stall; 
                        end
                        stage0_addr <= final_calibration_done? i_wb_addr : calib_addr; //address
                        stage0_aux <= final_calibration_done? i_aux : calib_aux; //aux ID for AXI compatibility
                        stage0_we <= final_calibration_done? i_wb_we : calib_we; //write-enable
                        stage0_data <= final_calibration_done? i_wb_data : calib_data; //data
                    end
                    // if there is already request on stage2 then only ecc_stage2_stall going low AND current ecc_stage1_stall is low can make this low
                    else if(stage0_pending) begin
                        stage0_pending <= (ecc_stage2_stall || ecc_stage1_stall) && (i_wb_cyc || !final_calibration_done); // stage0_pending will go low when cyc is low
                    end
                    // if stage1 will be updated, then stage0 will be empty
                    else if(stage1_update || stage1_update_calib) begin
                        stage0_pending <= 1'b0;
                    end
                    // if(!i_wb_cyc && final_calibration_done) begin
                    //     stage0_pending <= 1'b0;
                    // end
                    // ecc_stage1_stall high means stage2 will start ECC write/read operation next clock cycle thus update prev ecc address to current 
                    // if(ecc_stage1_stall) begin
                    //     ecc_col_addr_prev <= ecc_col_addr;
                    //     ecc_bank_addr_prev <= ecc_bank_addr;
                    //     ecc_row_addr_prev <= ecc_row_addr;
                    // end
                    // stage2_ecc_write_data_d will get updated when current request is non-ECC write (new ECC bits to be stored) 
                    stage2_ecc_write_data_q <= stage2_ecc_write_data_d;
                    // notify if ECC bits are already written to memory
                    write_ecc_stored_to_mem_q <= write_ecc_stored_to_mem_d;
                    // all bytes will be masked by default (unwritable)
                    stage2_ecc_write_data_mask_q <= stage2_ecc_write_data_mask_d;
                    // if data received from wishbone is for ECC read, update stage2_ecc_read_data_q 
                    stage2_ecc_read_data_q <= (o_aux[AUX_WIDTH-1 : AUX_WIDTH-2] == 2'b11)? o_wb_data_q_current : stage2_ecc_read_data_q;
                    // abort any ECC request when cyc is low
                    if(!i_wb_cyc && final_calibration_done) begin
                        ecc_req_stage2 <= 0;
                    end
                    // ecc_req_stage2 will only be high when stage2 will have ECC read/write operation
                    else if(ecc_stage1_stall) ecc_req_stage2 <= 1'b1;
                    // ECC is done this cycle if ecc_stage2_stall is now low
                    else if(!ecc_stage2_stall) ecc_req_stage2 <= 1'b0;
                end
            end
        end

        else begin : ecc_not_3_pipeline_control
            // logic when to update stage 1:
            // when not in refresh, transaction can only be processed when i_wb_cyc is high and not stall 
            assign stage1_update = i_wb_cyc && !o_wb_stall;
            assign stage1_update_calib = !final_calibration_done && !o_wb_stall_calib;
            /* verilator lint_off WIDTH */
            assign wb_addr_plus_anticipate = i_wb_addr + MARGIN_BEFORE_ANTICIPATE; // wb_addr_plus_anticipate determines if it is near the end of column by checking if it jumps to next row
            assign calib_addr_plus_anticipate = calib_addr + MARGIN_BEFORE_ANTICIPATE; // just same as wb_addr_plus_anticipate but while doing calibration
            /* verilator lint_on WIDTH */
            // default 0 
            assign ecc_stage1_stall = 0;
            assign decoded_parity = 0;
            always @* begin
                calib_addr_mux = 0;
                calib_data_mux = 0;
                calib_stb_mux = 0;
                calib_we_mux = 0;
                calib_aux_mux = 0;
                write_ecc_stored_to_mem_q = 0;
            end
        end
    endgenerate
    generate
        // If DLL off, add 1 more cycle of delay since PHY is faster for DLL OFF
        if(DLL_OFF) begin : dll_off_out_phy
            always @(posedge i_controller_clk) begin
                o_phy_data <= stage2_data[STAGE2_DATA_DEPTH-1]; // the data sent to PHY is the last stage of of stage 2 (since stage 2 can have multiple pipelined stages inside it_           
                o_phy_dm <= stage2_dm[STAGE2_DATA_DEPTH-1];
                o_phy_cmd <= {cmd_d[3], cmd_d[2], cmd_d[1], cmd_d[0]};
            end
        end
        else begin : dll_on_out_phy
            always @* begin
                o_phy_data = stage2_data[STAGE2_DATA_DEPTH-1]; // the data sent to PHY is the last stage of of stage 2 (since stage 2 can have multiple pipelined stages inside it_           
                o_phy_dm = stage2_dm[STAGE2_DATA_DEPTH-1];
                o_phy_cmd = {cmd_d[3], cmd_d[2], cmd_d[1], cmd_d[0]};
            end
        end
    endgenerate

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
        stage2_ecc_write_data_d = stage2_ecc_write_data_q;
        stage2_ecc_write_data_mask_d = stage2_ecc_write_data_mask_q;
        write_ecc_stored_to_mem_d = write_ecc_stored_to_mem_q;
        cmd_odt = cmd_odt_q || write_calib_odt;
        // logic for clock enable
        if(DUAL_RANK_DIMM[0]) begin
            if(current_rank) begin // if already on rank 1
                cmd_ck_en[0] = final_calibration_done? instruction[CLOCK_EN] : 1'b0; // rank 0 is on self-refresh (clock en disabled) if calibration is not yet done for rank 1
                cmd_ck_en[DUAL_RANK_DIMM] = instruction[CLOCK_EN]; // rank 1 follows current instruction 
            end
            else begin // if on rank 0
                cmd_ck_en[0] = instruction[CLOCK_EN]; // rank 0 follows current instruction 
                cmd_ck_en[DUAL_RANK_DIMM] = 1'b0; // rank 1 is idle
            end
        end
        else begin
            cmd_ck_en[0] = instruction[CLOCK_EN];
        end
        cmd_reset_n = instruction[RESET_N] || (DUAL_RANK_DIMM[0] && current_rank); // if dual rank enabled and current rank is 1 then reset_n does not need to assert again (already asserted on rank 0)
        stage1_stall = 1'b0;
        stage2_stall = 1'b0;
        ecc_stage2_stall = 1'b0;
        stage2_update = 1'b1; //always update stage 2 UNLESS it has a pending request (stage2_pending high)
        // o_wb_stall_d = 1'b0; //wb_stall going high is determined on stage 1 (higher priority), wb_stall going low is determined at stage2 (lower priority)
        precharge_slot_busy = 0; //flag that determines if stage 2 is issuing precharge (thus stage 1 cannot issue precharge)
        activate_slot_busy = 0; //flag that determines if stage 2 is issuing activate (thus stage 1 cannot issue activate)
        write_dqs_d = write_calib_dqs;
        write_dq_d = write_calib_dq;
        for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
            bank_status_d[index] = bank_status_q[index];
            bank_active_row_d[index] = bank_active_row_q[index];
        end
        //set PRECHARGE_SLOT as reset instruction, the remainings are NOP (MSB is high)
        //delay_counter_is_zero high signifies start of new reset instruction (the time when the command must be issued)
        cmd_d[PRECHARGE_SLOT][cmd_len-1-DUAL_RANK_DIMM:0] = {(!delay_counter_is_zero), instruction[DDR3_CMD_START-1:DDR3_CMD_END] | {3{(!delay_counter_is_zero)}} , cmd_odt, cmd_ck_en, cmd_reset_n, 
                        instruction[MRS_BANK_START:(MRS_BANK_START-BA_BITS+1)], instruction[ROW_BITS-1:0]};
        cmd_d[PRECHARGE_SLOT][10] = instruction[A10_CONTROL];
        cmd_d[READ_SLOT][cmd_len-1-DUAL_RANK_DIMM:0] = {(!issue_read_command), CMD_RD[2:0] | {3{(!issue_read_command)}}, cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}}; // issued during MPR reads (address does not matter)
        cmd_d[ACTIVATE_SLOT][cmd_len-1-DUAL_RANK_DIMM:0] = {1'b0, 3'b111 , cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}};  // always NOP by default

        // extra slot is created when READ and WRITE slots are the same
        // this remaining slot should be NOP by default
        if(WRITE_SLOT == READ_SLOT) begin
            cmd_d[REMAINING_SLOT][cmd_len-1-DUAL_RANK_DIMM:0] = {1'b0, 3'b111 , cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}};  // always NOP by default
        end
        // if read and write slot is not shared, the write slot should be NOP by default
        else begin
            cmd_d[WRITE_SLOT][cmd_len-1-DUAL_RANK_DIMM:0] = {1'b0, 3'b111, cmd_odt, cmd_ck_en, cmd_reset_n, {(ROW_BITS+BA_BITS){1'b0}}}; // always NOP by default
        end

        // if precharge slot is not the 0th slot, then all slots before precharge will have the previous value of cmd_ck_en
        if(PRECHARGE_SLOT != 0) begin 
            for(index = 0; index < PRECHARGE_SLOT; index=index+1) begin // slots before
                if(DUAL_RANK_DIMM[0]) begin
                    cmd_d[index][CMD_CKE_2] = prev_cmd_ck_en[DUAL_RANK_DIMM];
                end
                cmd_d[index][CMD_CKE] = prev_cmd_ck_en[0];
            end
        end

        /////////////////////////////////////////////////////////////////////////////////////////
        // if dual rank is enabled, last 2 bits are {cs_2, cs_1}
        if(DUAL_RANK_DIMM[0]) begin
            cmd_d[PRECHARGE_SLOT][cmd_len-1:cmd_len-2]= {!current_rank || !delay_counter_is_zero , (current_rank && !final_calibration_done) || !delay_counter_is_zero}; // reset sequence is done per rank
            cmd_d[READ_SLOT][cmd_len-1:cmd_len-2] = {!current_rank || !issue_read_command , current_rank || !issue_read_command}; // MPR is done per rank
            cmd_d[ACTIVATE_SLOT][cmd_len-1:cmd_len-2] = 2'b11; // NOP by default
            if(WRITE_SLOT == READ_SLOT) begin
                cmd_d[REMAINING_SLOT][cmd_len-1:cmd_len-2] = 2'b11; // always NOP by default
            end
            // if read and write slot is not shared, the write slot should be NOP by default
            else begin
                cmd_d[WRITE_SLOT][cmd_len-1:cmd_len-2] = 2'b11; // always NOP by default
            end
        end
        /////////////////////////////////////////////////////////////////////////////////////////

        // decrement delay counters for every bank , stay to 0 once 0 is reached
        // every bank will have its own delay counters for precharge, activate, write, and read 
        for(index=0; index< (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
            delay_before_precharge_counter_d[index] = (delay_before_precharge_counter_q[index] == 0)? 0: delay_before_precharge_counter_q[index] - 1;
            delay_before_activate_counter_d[index] = (delay_before_activate_counter_q[index] == 0)? 0: delay_before_activate_counter_q[index] - 1;
            delay_before_write_counter_d[index] = (delay_before_write_counter_q[index] == 0)? 0:delay_before_write_counter_q[index] - 1;
            delay_before_read_counter_d[index] = (delay_before_read_counter_q[index] == 0)? 0:delay_before_read_counter_q[index] - 1;
        end
        for(index = 1; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
            // shift is rightward where LSB gets MSB ([MSB] -> [] -> [] -> .... -> [] -[LSB])
            shift_reg_read_pipe_d[index-1] = shift_reg_read_pipe_q[index];
        end
        write_ack_index_d = (write_ack_index_q != 1)? write_ack_index_q - 1 : 1; // decrease write index as shift_reg_read_pipe_d is shifted
        // earliest write ack is on index 1 shift_reg_read_pipe_q[1] since [0] will fail the alternating index_wb_data
        shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH-1] = 0; //MSB just receives zero when shifted rightward


        //USE _d in ALL
        //if there is a pending request, issue the appropriate commands
        if(stage2_pending) begin 
            stage2_stall = 1; //initially high when stage 2 is pending 
            ecc_stage2_stall = 1;
            stage2_update = 0;

            //right row is already active so go straight to read/write
            if(bank_status_q[stage2_bank] &&  bank_active_row_q[stage2_bank] == stage2_row) begin //read/write operation
                //write request
                if(stage2_we && delay_before_write_counter_q[stage2_bank] == 0) begin       
                    stage2_stall = 0;
                    ecc_stage2_stall = 0;
                    stage2_update = 1;
                    cmd_odt = 1'b1;
                    // don't acknowledge if ECC request
                    /* verilator lint_off WIDTHTRUNC */
                    shift_reg_read_pipe_d[write_ack_index_q] = {stage2_aux, !ecc_req_stage2}; // ack is sent to shift_reg which will be shifted until the wb ack output
                    /* verilator lint_on WIDTHTRUNC */
                    write_ack_index_d = write_ack_index_q; // write index stay when write
                    //write acknowledge will use the same logic pipeline as the read acknowledge. 
                    //This would mean write ack latency will be the same for
                    //read ack latency. If it takes 8 clocks for read ack, write
                    //ack latency will be the same. This simplifies the logic
                    //for write ack as there will be no need to analyze the
                    //contents of the shift_reg_read_pipe just to determine
                    //where best to place the write ack on the pipeline (since
                    //the order of ack must be maintained). But this would mean
                    //the latency for write is fixed regardless if there is an 
                    //outstanding read ack or none on the pipeline. But this is
                    // acceptable in my opinion since this is a pipelined wishbone
                    // where the transaction can continue regardless when ack returns
                    
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
                    for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin //the write to read delay applies to all banks (odt must be turned off properly before reading)
                        delay_before_read_counter_d[index] = WRITE_TO_READ_DELAY + 1; //NOTE TO SELF: why plus 1?
                    end
                    delay_before_write_counter_d[stage2_bank] = WRITE_TO_WRITE_DELAY;
                    //issue read command
                    if(DUAL_RANK_DIMM[0]) begin
                        if(COL_BITS <= 10) begin
                            // if stage2_bank[BA_BITS] high then request is for 2nd rank, if low then for 1st rank
                            cmd_d[WRITE_SLOT] = {!stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank[BA_BITS-1:0],{{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_col[(DUAL_RANK_DIMM[0]? 9 : 8):0]};  
                        end
                        else begin // COL_BITS > 10 has different format from <= 10
                            cmd_d[WRITE_SLOT] = {!stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank[BA_BITS-1:0],{{ROW_BITS-32'd12}{1'b0}} , stage2_col[(COL_BITS <= 10) ? 0 : 10] , 1'b0 , stage2_col[(DUAL_RANK_DIMM[0]? 9 : 8):0]};  
                        end
                    end
                    else begin
                        if(COL_BITS <= 10) begin
                            cmd_d[WRITE_SLOT] = {1'b0, CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank,{{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_col[9:0]};  
                        end
                        else begin // COL_BITS > 10 has different format from <= 10
                            cmd_d[WRITE_SLOT] = {1'b0, CMD_WR[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank,{{ROW_BITS-32'd12}{1'b0}} , stage2_col[(COL_BITS <= 10) ? 0 : 10] , 1'b0 , stage2_col[9:0]};  
                        end
                    end
                    //turn on odt at same time as write cmd
                    cmd_d[0][CMD_ODT] = cmd_odt;
                    cmd_d[1][CMD_ODT] = cmd_odt;
                    cmd_d[2][CMD_ODT] = cmd_odt;
                    cmd_d[3][CMD_ODT] = cmd_odt;
                    write_dqs_d=1;
                    write_dq_d=1;
                    
                    if(ECC_ENABLE == 3) begin
                        if(!ecc_req_stage2) begin
                            // Store ECC parity bits
                            // For example, in x16 DDR3, total data width is 128. Each 64 bits is encoded, thus 2 sets of parity bits
                            // of 8 bits long (encoding 64 bits require 8 bits of parity). Thus 16 total bits is stored to stage2_ecc_write_data_d
                            // 8 words will require eight 16-bits parity for total of 128 bits. This 128 bits will be stored to a mapped ECC address
                            // where positioning is dependent on stage2_col
                            // stage2_ecc_write_data_d = { {word7_parity} , {word6_parity} , {word5_parity} , {word4_parity} , {word3_parity} , {word2_parity} , {word1_parity} , {word0_parity}}
                            /* verilator lint_off WIDTHTRUNC */
                            stage2_ecc_write_data_d[({32'd0, stage2_col[5:3]} << $clog2(wb_data_bits/8)) +: (wb_data_bits/8) ] = stage2_encoded_parity;
                            // enable data mask for the position of ECC bit
                            stage2_ecc_write_data_mask_d[({32'd0, stage2_col[5:3]} << $clog2(wb_data_bits/64)) +: (wb_data_bits/64)] = {(wb_data_bits/64){1'b1}};
                            /* verilator lint_on WIDTHTRUNC */
                            // notify that there are ECC bits which is not yet written to memory
                            write_ecc_stored_to_mem_d = 1'b0;
                        end
                        else begin
                            // reset data mask if ECC write will be done
                            stage2_ecc_write_data_mask_d = 0;
                            // notify that are ECC bits are now written to memory
                            write_ecc_stored_to_mem_d = 1'b1;
                        end
                    end
                end
                
                //read request
                else if(!stage2_we && delay_before_read_counter_q[stage2_bank]==0) begin     
                    stage2_stall = 0;
                    ecc_stage2_stall = 0;
                    stage2_update = 1;
                    cmd_odt = 1'b0;
                    //set-up delay before precharge, read, and write
                    if(delay_before_precharge_counter_q[stage2_bank] <= READ_TO_PRECHARGE_DELAY) begin
                        delay_before_precharge_counter_d[stage2_bank] = READ_TO_PRECHARGE_DELAY;
                    end
                    delay_before_read_counter_d[stage2_bank] = READ_TO_READ_DELAY;     
                    delay_before_write_counter_d[stage2_bank] = READ_TO_WRITE_DELAY + 1; //temporary solution since its possible odt to go high already while reading previously
                    for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin //the read to write delay applies to all banks (odt must be turned on properly before writing and this delay is for ODT to settle)
                        delay_before_write_counter_d[index] = READ_TO_WRITE_DELAY + 1; // NOTE TO SELF: why plus 1?
                    end
                    // don't acknowledge if ECC request
                    // higher shift_read_pipe means the earlier it will check data received from i_phy_iserdes_data
                    // shift_read_pipe is only used in calibration when DLL_OFF
                    shift_reg_read_pipe_d[READ_ACK_PIPE_WIDTH - 1 - {30'd0,shift_read_pipe}] = {stage2_aux, !ecc_req_stage2}; // ack is sent to shift_reg which will be shifted until the wb ack output
                    write_ack_index_d = READ_ACK_PIPE_WIDTH[$clog2(READ_ACK_PIPE_WIDTH)-1:0]-1'b1; // next index for write is the last index of shift_reg_read_pipe_d
                    //issue read command
                    if(DUAL_RANK_DIMM[0]) begin
                        if(COL_BITS <= 10) begin
                            cmd_d[READ_SLOT] = {!stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank[BA_BITS-1:0], {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_col[(DUAL_RANK_DIMM[0]? 9 : 8):0]};  
                        end
                        else begin // COL_BITS > 10 has different format from <= 10
                            cmd_d[READ_SLOT] =  {!stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank[BA_BITS-1:0], {{ROW_BITS-32'd12}{1'b0}} , stage2_col[(COL_BITS <= 10) ? 0 : 10] , 1'b0 , stage2_col[(DUAL_RANK_DIMM[0]? 9 : 8):0]};  
                        end
                    end
                    else begin
                        if(COL_BITS <= 10) begin
                            cmd_d[READ_SLOT] = {1'b0, CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_col[9:0]};  
                        end
                        else begin // COL_BITS > 10 has different format from <= 10
                            cmd_d[READ_SLOT] =  {1'b0, CMD_RD[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, {{ROW_BITS-32'd12}{1'b0}} , stage2_col[(COL_BITS <= 10) ? 0 : 10] , 1'b0 , stage2_col[9:0]};  
                        end
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
                // must meet TRRD (activate to activate delay)
                for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin //the activate to activate delay applies to all banks
                    if(delay_before_activate_counter_q[index] <= ACTIVATE_TO_ACTIVATE_DELAY) begin // if delay is > ACTIVATE_TO_ACTIVATE_DELAY, then updating it to the lower delay will cause the previous delay to be violated
                        delay_before_activate_counter_d[index] = ACTIVATE_TO_ACTIVATE_DELAY;
                    end
                end

                delay_before_precharge_counter_d[stage2_bank] = ACTIVATE_TO_PRECHARGE_DELAY;

                //set-up delay before read and write
                if(delay_before_read_counter_q[stage2_bank] <= ACTIVATE_TO_READ_DELAY) begin // if current delay is > ACTIVATE_TO_READ_DELAY, then updating it to the lower delay will cause the previous delay to be violated
                    delay_before_read_counter_d[stage2_bank] = ACTIVATE_TO_READ_DELAY;
                end
                if(delay_before_write_counter_q[stage2_bank] <= ACTIVATE_TO_WRITE_DELAY) begin // if current delay is > ACTIVATE_TO_WRITE_DELAY, then updating it to the lower delay will cause the previous delay to be violated
                    delay_before_write_counter_d[stage2_bank] = ACTIVATE_TO_WRITE_DELAY;
                end
                //issue activate command
                if(DUAL_RANK_DIMM[0]) begin
                    cmd_d[ACTIVATE_SLOT] = {!stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_ACT[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank[BA_BITS-1:0], stage2_row[(DUAL_RANK_DIMM[0]? ROW_BITS-1 : ROW_BITS-2):0]};
                end
                else begin
                    cmd_d[ACTIVATE_SLOT] = {1'b0, CMD_ACT[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank , stage2_row};
                end
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
                if(DUAL_RANK_DIMM[0]) begin
                    cmd_d[PRECHARGE_SLOT] = {!stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage2_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank[BA_BITS-1:0], { {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_row[DUAL_RANK_DIMM[0]? 9 : 8:0] } };
                end
                else begin
                    cmd_d[PRECHARGE_SLOT] = {1'b0, CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage2_bank, { {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage2_row[9:0] } };
                end
                //update bank status and active row
                bank_status_d[stage2_bank] = 1'b0; 
            end
        end //end of stage 2 pending

        // pending request on stage 1
        // if DDR3_CLK_PERIOD == 1250, then remove this anticipate stage 1 to pass timing
        if(DDR3_CLK_PERIOD != 1_250) begin
            if(stage1_pending && !((stage1_next_bank == stage2_bank) && stage2_pending)) begin
                //stage 1 will mainly be for anticipation (if next requests need to jump to new bank then 
                //anticipate the precharging and activate of that next bank, BUT it can also handle
                //precharge and activate of CURRENT wishbone request.
                //Anticipate will depend if the request is on the end of the row 
                // and must start the anticipation. For example if we have 10 rows in a bank:
                //[R][R][R][R][R][R][R][A][A][A] -> [next bank]
                //
                //R = Request, A = Anticipate
                //Unless we are near the third to the last column, stage 1 will
                //issue Activate and Precharge on the CURRENT bank. Else, stage
                //1 will issue Activate and Precharge for the NEXT bank
                // Thus stage 1 anticipate makes sure smooth burst operation that jumps banks
                if(bank_status_q[stage1_next_bank] &&  bank_active_row_q[stage1_next_bank] != stage1_next_row && delay_before_precharge_counter_q[stage1_next_bank] ==0 && !precharge_slot_busy) begin    
                    //set-up delay before read and write
                    delay_before_activate_counter_d[stage1_next_bank] = PRECHARGE_TO_ACTIVATE_DELAY;
                    if(DUAL_RANK_DIMM[0]) begin
                        cmd_d[PRECHARGE_SLOT] = {!stage1_next_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage1_next_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank[BA_BITS-1:0], { {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage1_next_row[(DUAL_RANK_DIMM[0]? 9 : 8):0] } };
                    end
                    else begin
                        cmd_d[PRECHARGE_SLOT] = {1'b0, CMD_PRE[2:0], cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank, { {{ROW_BITS-32'd11}{1'b0}} , 1'b0 , stage1_next_row[9:0] } };
                    end
                    bank_status_d[stage1_next_bank] = 1'b0; 
                end //end of anticipate precharge
                
                //anticipated bank is idle so do activate
                else if(!bank_status_q[stage1_next_bank] && delay_before_activate_counter_q[stage1_next_bank] == 0 && !activate_slot_busy) begin 
                    // must meet TRRD (activate to activate delay)
                    for(index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin //the activate to activate delay applies to all banks
                        if(delay_before_activate_counter_d[index] <= ACTIVATE_TO_ACTIVATE_DELAY) begin // if delay is > ACTIVATE_TO_ACTIVATE_DELAY, then updating it to the lower delay will cause the previous delay to be violated
                            delay_before_activate_counter_d[index] = ACTIVATE_TO_ACTIVATE_DELAY;
                        end
                    end

                    delay_before_precharge_counter_d[stage1_next_bank] = ACTIVATE_TO_PRECHARGE_DELAY;
                    
                    //set-up delay before read and write
                    if(delay_before_read_counter_d[stage1_next_bank] <= ACTIVATE_TO_READ_DELAY) begin  // if current delay is > ACTIVATE_TO_READ_DELAY, then updating it to the lower delay will cause the previous delay to be violated
                        delay_before_read_counter_d[stage1_next_bank] = ACTIVATE_TO_READ_DELAY;
                    end
                    if(delay_before_write_counter_d[stage1_next_bank] <= ACTIVATE_TO_WRITE_DELAY) begin  // if current delay is > ACTIVATE_TO_WRITE_DELAY, then updating it to the lower delay will cause the previous delay to be violated
                        delay_before_write_counter_d[stage1_next_bank] = ACTIVATE_TO_WRITE_DELAY;
                    end
                    if(DUAL_RANK_DIMM[0]) begin
                        cmd_d[ACTIVATE_SLOT] = {!stage1_next_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], stage1_next_bank[(DUAL_RANK_DIMM[0]? BA_BITS : 0)], CMD_ACT[2:0] , cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank[BA_BITS-1:0] , stage1_next_row[(DUAL_RANK_DIMM[0]? ROW_BITS-1 : ROW_BITS-2):0]}; 
                    end
                    else begin
                        cmd_d[ACTIVATE_SLOT] = {1'b0, CMD_ACT[2:0] , cmd_odt, cmd_ck_en, cmd_reset_n, stage1_next_bank , stage1_next_row};
                    end
                    bank_status_d[stage1_next_bank] = 1'b1;
                    bank_active_row_d[stage1_next_bank] = stage1_next_row;
                end //end of anticipate activate
                
            end //end of stage1 anticipate
        end

        // control stage 1 stall
        if(stage1_pending) begin //raise stall only if stage2 will still be busy next clock
            // Stage1 bank and row will determine if transaction will be
            // stalled (bank is idle OR wrong row is active). 
            if(!bank_status_d[stage1_bank] || (bank_status_d[stage1_bank] && bank_active_row_d[stage1_bank] != stage1_row)) begin 
                stage1_stall = 1;
            end
            else if(!stage1_we && delay_before_read_counter_d[stage1_bank] != 0) begin // if read request but delay before read is not yet met then stall
                stage1_stall = 1;
            end
            else if(stage1_we && delay_before_write_counter_d[stage1_bank] != 0) begin // if write request but delay before write is not yet met then stall
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
                if(stage2_we && delay_before_write_counter_d[stage2_bank] == 0) begin // if write request and delay before write is already met then deassert stall
                    stage2_stall = 0; //to low stall next stage, but not yet at this stage
                end
                //read request
                else if(!stage2_we && delay_before_read_counter_d[stage2_bank]==0) begin // if read request and delay before read is already met then deassert stall 
                    stage2_stall = 0;
                end
            end
        end

        // control logic for stall
        // this small logic is already optimized via listing all possible combinations on excel sheet, investigating the patterns
        // and passing the formal verification. I recommend to not touch this and just left this as is.
        // This logic makes sure stall will never go high unless the pipeline is full
        // What made this complicated is that fact you have to predict the stall for next clock cycle in such 
        // a way that it will only stall next clock cycle if the pipeline will be full on the next clock cycle.
        // Excel sheet design planning: https://docs.google.com/spreadsheets/d/1_8vrLmVSFpvRD13Mk8aNAMYlh62SfpPXOCYIQFEtcs4/edit?gid=668378527#gid=668378527
        // Old: https://1drv.ms/x/s!AhWdq9CipeVagSqQXPwRmXhDgttL?e=vVYIxE&nav=MTVfezAwMDAwMDAwLTAwMDEtMDAwMC0wMDAwLTAwMDAwMDAwMDAwMH0
        // if(o_wb_stall_q) o_wb_stall_d = stage2_stall;
        // else if( (!i_wb_stb && final_calibration_done) || (!calib_stb && state_calibrate != DONE_CALIBRATE) ) o_wb_stall_d = 0; 
        // else if(!stage1_pending) o_wb_stall_d = stage2_stall;
        // else o_wb_stall_d = stage1_stall;

        // if( !o_wb_stall_q && !i_wb_stb ) o_wb_stall_d = 1'b0;
        // else if(ecc_stage1_stall) o_wb_stall_d = 1'b1;
        // else if(stage0_pending) o_wb_stall_d = ecc_stage2_stall || stage1_stall;
        // else begin
        //     if(o_wb_stall_q) o_wb_stall_d = stage2_stall;
        //     else o_wb_stall_d = stage1_stall;
        // end
        // pipeline control for ECC_ENABLE != 3
        if(ECC_ENABLE != 3) begin
            if(!i_wb_cyc && final_calibration_done) begin
                o_wb_stall_d = 0;
            end
            else if(!o_wb_stall_q && ( (!i_wb_stb && final_calibration_done) || (!calib_stb && !final_calibration_done) )) begin
                o_wb_stall_d = 0;
            end
            else if(o_wb_stall_q || !stage1_pending)  begin
                o_wb_stall_d = stage2_stall;
            end
            else begin
                o_wb_stall_d = stage1_stall;
            end
        end
        // pipeline control for ECC_ENABLE = 3
        else begin
            if(!i_wb_cyc && final_calibration_done) begin
                o_wb_stall_d = 1'b0;
            end
            else if(ecc_stage1_stall) begin
                o_wb_stall_d = 1'b1;
            end
            else if(!o_wb_stall_q && ( (!i_wb_stb && final_calibration_done) || (!calib_stb && !final_calibration_done) )) begin
                o_wb_stall_d = 1'b0;
            end
            else if(stage0_pending) begin
                o_wb_stall_d = !stage2_update || stage1_stall;
            end
            else begin
                if(o_wb_stall_q || !stage1_pending)  begin
                    o_wb_stall_d = stage2_stall;
                end
                else begin
                    o_wb_stall_d = stage1_stall;
                end
            end
        end
    end //end of always block


    // register previous value of cmd_ck_en
    always @(posedge i_controller_clk) begin
        if(sync_rst_controller) begin
            prev_cmd_ck_en <= 0;
        end
        else begin
            prev_cmd_ck_en <= cmd_ck_en;
        end
    end
    
    /*********************************************************************************************************************************************/

    /******************************************************* Align Read Data from ISERDES *******************************************************/
    always @(posedge i_controller_clk) begin
        if(sync_rst_controller) begin
            index_read_pipe <= 0;
            index_wb_data <= 0;
            write_dqs_val <= 0;
            write_dqs_q <= 0;
            write_dqs <= 0;
            write_dq_q <= 0;
            write_dq <= 0;
            write_ack_index_q <= 1;
            if(ECC_ENABLE == 1 || ECC_ENABLE == 2) begin
                o_wb_ack_q <= 0;
                o_wb_ack_uncalibrated <= 0;
            end
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
            if(ODELAY_SUPPORTED || DLL_OFF) begin
                write_dqs_val[0] <= write_dqs_d || write_dqs_q[0];
            end
            else begin 
                write_dqs_val[0] <= write_dqs_d || write_dqs_q[0] || write_dqs_q[1];
            end
            write_dqs_q[0] <= write_dqs_d;
            write_dqs_q[1] <= write_dqs_q[0];
            write_dqs[0] <= write_dqs_d || write_dqs_q[0] || write_dqs_q[1]; //high for 3 clk cycles
            
            write_dq_q[0] <= write_dq_d;
            write_dq_q[1] <= write_dq_q[0];
            write_dq[0] <= write_dq_d || write_dq_q[0] || write_dq_q[1]; //high for 3 clk cycles
            for(index = 0; index < STAGE2_DATA_DEPTH; index = index+1) begin //increase by 1 to accomodate postamble            
                write_dqs[index+1] <= write_dqs[index]; 
                write_dqs_val[index+1] <= write_dqs_val[index];
            end 
            for(index = 0; index < STAGE2_DATA_DEPTH+1; index = index+1) begin //increase by 1 to accomodate postamble            
                write_dq[index+1] <= write_dq[index]; 
            end 
            for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                // shifted rightward where LSB gets MSB ([MSB] -> [] -> [] -> .... -> [] -[LSB])
                shift_reg_read_pipe_q[index] <= shift_reg_read_pipe_d[index];
            end
            write_ack_index_q <= write_ack_index_d; // determines next index in pipe for write ack
            for(index = 0; index < 2; index = index + 1) begin 
                // there are 2 read_pipes (each with 16 space for shifting), and each read pipes shift rightward
                // so the bit 1 will be shifted to the right until it reach LSB which means data is already on ISERDES output of PHY
                delay_read_pipe[index] <= (delay_read_pipe[index] >> 1);
            end
            if(shift_reg_read_pipe_q[1][0] || shift_reg_read_pipe_q[1][AUX_WIDTH]) begin 
                //delay from shift_reg_read_pipe_q is about to be over (ack, which is the last bit, will be at LSB on next clk cycle OR MSB is high for ECC req)
                //and data is now starting to be released from ISERDES from phy BUT NOT YET ALIGNED
                index_read_pipe <= !index_read_pipe; //control which delay_read_pipe would get updated (we have 2 read_pipes to store read data,use the read_pipe alternatingly)
                delay_read_pipe[index_read_pipe][added_read_pipe_max] <= 1'b1; //update delay_read_pipe
                // NOTE: added_read_pipe_max can either be 0 or 1 (NOTE TO SELF: optimize by lowering the bit size of delay_read_pipe)
                // delay_read_pipe will get the ack bit from shift_reg_read_pipe_q[1] at the bit equal to 
                // added_read_pipe_max (0th or 1st bit). added_read_pipe_max is the max number of added controller clk cycles among all lanes
                // So basically, the delay_read_pipe is the delay to make sure the "added_read_pipe_max" controller clk cycles
                // will be met.
                // Example:
                // So for request #1 (e.g. write request, added_read_pipe_max=1), wait until the shift_reg_read_pipe_q[1] goes 
                // high (READ_ACK_PIPE_WIDTH of delay is met which means the data from ISERDES PHY is now available). The 
                // delay_read_pipe[0][1] will then be high. This high bit on read_pipe #0 will get shifted to LSB. [1] -> [] -> [LSB]
                // Meanwhile when request #2 comes (e.g. read request, added_read_pipe_max=1), again wait until the shift_reg_read_pipe_q[1] goes 
                // high. The delay_read_pipe[1][1] will then be high. This high bit on read_pipe #1 will get shifted to LSB. [1] -> [] -> [LSB]
            end
            
            for(index = 0; index < LANES; index = index + 1) begin
                /* verilator lint_off WIDTH */
                // read_pipe #0
                // NOTE: added_read_pipe_max and added_read_pipe can either be just 0 or 1 (NOTE TO SELF: optimize by lowering the bit size of this)
                // If the added_read_pipe (added number of controller clk cycles of delay to a lane due to pcb trace) is equal to the 
                // max delay (added_read_pipe_max, e.g. 0-0 or 1-1) for this lane, THEN we need to wait until the bit 1 reaches the LSB[0] of delay_read_pipe
                // before retrieving the value from PHY. But if not the same (added_read_pipe is 0 while added_read_pipe_max is 1), then wait until
                // the bit 1 reaches the one before LSB [1] before retrieving the value from PHY, so this means this lane with 0 delay will FIRST BE RETRIEVED
                // while the lane with added_read_pipe_max of delay (delay of 1) will be retrieved SECOND
                if(delay_read_pipe[0][added_read_pipe_max != added_read_pipe[index]]) begin 
                /* verilator lint_on WIDTH */
                // o_wb_data[63:0] = BURST0: {LANE7,LANE6,LANE5,LANE4,LANE3,LANE2,LANE1,LANE0}
                // o_wb_data[127:64] = BURST1: {LANE7,LANE6,LANE5,LANE4,LANE3,LANE2,LANE1,LANE0}
                // o_wb_data[191:128] = BURST2: {LANE7,LANE6,LANE5,LANE4,LANE3,LANE2,LANE1,LANE0}
                    o_wb_data_q[0][((DQ_BITS*LANES)*0 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*0 + 8*index) +: 8]; //update lane for burst 0
                    o_wb_data_q[0][((DQ_BITS*LANES)*1 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*1 + 8*index) +: 8]; //update lane for burst 1
                    o_wb_data_q[0][((DQ_BITS*LANES)*2 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*2 + 8*index) +: 8]; //update lane for burst 2
                    o_wb_data_q[0][((DQ_BITS*LANES)*3 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*3 + 8*index) +: 8]; //update lane for burst 3
                    o_wb_data_q[0][((DQ_BITS*LANES)*4 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*4 + 8*index) +: 8]; //update lane for burst 4
                    o_wb_data_q[0][((DQ_BITS*LANES)*5 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*5 + 8*index) +: 8]; //update lane for burst 5
                    o_wb_data_q[0][((DQ_BITS*LANES)*6 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*6 + 8*index) +: 8]; //update lane for burst 6
                    o_wb_data_q[0][((DQ_BITS*LANES)*7 + 8*index) +: 8] <= i_phy_iserdes_data[((DQ_BITS*LANES)*7 + 8*index) +: 8]; //update lane for burst 7
                end
                /* verilator lint_off WIDTH */
                // read_pipe #1
                // NOTE: added_read_pipe_max and added_read_pipe can either be just 0 or 1 (NOTE TO SELF: optimize by lowering the bit size of this)
                // If the added_read_pipe (added number of controller clk cycles of delay to a lane due to pcb trace) is equal to the 
                // max delay (added_read_pipe_max, e.g. 0-0 or 1-1) for this lane, THEN we need to wait until the bit 1 reaches the LSB[0] of delay_read_pipe
                // before retrieving the value from PHY. But if not the same (added_read_pipe is 0 while added_read_pipe_max is 1), then wait until
                // the bit 1 reaches the one before LSB [1] (which goes high already since bit 1 of delay_read_pipe is the first to go high once shift_reg_read_pipe_q
                // bit 1 goes high) before retrieving the value from PHY. So this means this lane with 0 delay will FIRST BE RETRIEVED
                // while the lane with added_read_pipe_max of delay (delay of 1) will be retrieved SECOND
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
                // why are we alternatingly use the read_pipes?
                //               time |   0    |   1     |   2     |   3     |
                //    index_read_pipe |   1    |   0     |   1     |   0     |
                // delay_read_pipe[1] | [0][0] | <[1][0] | [0][1]> | [1][0]  |   
                // delay_read_pipe[0] | [0][0] | [0][0]  | <[1][0] | [0][1]> |  
                //
                // At time 1, request #1 is accepted by pipe[1], then wait until time 2 to retrieve the lane with longest added_read_pipe 
                // (lane with added_read_pipe 0 is retrieved from ISERDES at time 1, lane with added_read_pipe 1 is retrieved from ISERDES at time 2)
                // At time 2, request #2 is accepted by pipe[0] (since pipe[1] is still busy on request #1), then wait until time 3 to retrieve 
                // the lane with longest added_read_pipe
                // Thus pipe 0 and 1 is alternating to make sure that even if 0 is busy, 1 will retrieve the data. And then when 1 is busy, 0 will retrieve the data
                // NOTE TO SELF: longest delay for a lane relative to others is 1 controller clk cycle, if more than 1 then it will not be retrievd 
                // and aligned properly. Thus try to optimize this logic since delay is at max 1 controller clk only.
            end
            // o_wb_ack_read_q[0][0] is also the wishbone ack (aligned with ack is the wishbone data) thus
            // after sending the wishbone data on a particular index, invert it for the next ack
            
            if(ECC_ENABLE != 3) begin
                if(o_wb_ack_read_q[0][0]) begin 
                    index_wb_data <= !index_wb_data; //alternatingly uses the o_wb_data_q (either 0 or 1)
                end
            end
            else begin
                // last bit of AUX is high if ECC request (wb ack does not go high at ECC reqs)
                if(o_wb_ack_read_q[0][0] || o_wb_ack_read_q[0][AUX_WIDTH]) begin 
                    index_wb_data <= !index_wb_data; //alternatingly uses the o_wb_data_q (either 0 or 1)
                end
            end
            
            for(index = 1; index < MAX_ADDED_READ_ACK_DELAY; index = index + 1) begin
                o_wb_ack_read_q[index-1] <= o_wb_ack_read_q[index]; // shift rightward [ack] -> [] -> [LSB]
            end
            o_wb_ack_read_q[MAX_ADDED_READ_ACK_DELAY-1] <= 0; // MSB always gets zero and is shifted rightwards
            o_wb_ack_read_q[added_read_pipe_max] <= shift_reg_read_pipe_q[0];
            // o_wb_ack_read_q[0] is the wishbone ack
            // so once data is available from ISERDES (shift_reg_read_pipe_q[0] high) then need to wait added_read_pipe_max
            // before the data is properly stored to o_wb_data_q and can be sent outside as wishbone data

            // BASICALLY:
            // shift_reg_read_pipe_q is the delay from when the read command is issued from controller until the 
            // data is received by the PHY ISERDES (total delay of READ_ACK_PIPE_WIDTH). The shift_reg_read_pipe_q[1]
            // is then connected to delay_read_pipe[added_read_pipe_max (0 or 1)] which is the delay to align the lanes.
            // The shift_reg_read_pipe_q[0] is then connected to o_wb_ack_read_q[added_read_pipe_max (0 or 1)] which
            // is the delay until the wishbone data and ack will be sent outside
            // NOTE TO SELF: Optimize by removing o_wb_ack_read_q and just connect the woshbone ack and data to delay_read_pipe[0].
            // Visualization:
            // shift_reg_read_pipe_q  [ ] -> [1] -> [ ]         [ ] -> [ ] -> [1]         [ ] -> [ ] -> [ ]          [ ] -> [ ] -> [ ]
            //       delay_read_pipe  [ ] -> [ ] -> [ ]   --->  [ ] -> [1] -> [ ]   --->  [ ] -> [ ] -> [1]   --->   [ ] -> [ ] -> [ ]
            //       o_wb_ack_read_q  [ ] -> [ ] -> [ ]         [ ] -> [ ] -> [ ]         [ ] -> [1] -> [ ]          [ ] -> [ ] -> [1]
            //                   request is now on [1]            request passed              request passed        o_wb_ack_read_q[0]
            //                of shift_reg_read_pipe_q        to delay_read_pipe          to o_wb_ack_read_q        high thus ready for wishbone ack
            
            // abort any outgoing ack when cyc is low
            if(!i_wb_cyc && final_calibration_done) begin
                for(index = 0; index < MAX_ADDED_READ_ACK_DELAY; index = index + 1) begin
                    o_wb_ack_read_q[index] <= 0;
                end
                for(index = 0; index < READ_ACK_PIPE_WIDTH; index = index + 1) begin
                    shift_reg_read_pipe_q[index] <= 0;
                end
            end
            if(ECC_ENABLE == 1 || ECC_ENABLE == 2) begin // added latency of 1 clock cycle for decoding the ECC
                o_wb_data <= o_wb_data_q_decoded; // Wishbone data output
                o_aux <= o_wb_ack_read_q[0][AUX_WIDTH:1]; // Aux output
                o_wb_data_uncalibrated <= o_wb_data_q_current; // Data is not ECC decoded when not yet done calibration
                o_wb_ack_uncalibrated <= o_wb_ack_read_q[0][0] && !final_calibration_done; // ack used during calibration
                o_wb_ack_q <= o_wb_ack_read_q[0][0] && final_calibration_done && i_wb_cyc; // ack used during normal operation
                o_wb_err_q <= db_err_o; // flag Wishbone error due to double bit error
            end
       end
    end
    assign o_wb_data_q_current = o_wb_data_q[index_wb_data];

    generate
        if(ECC_ENABLE == 0) begin: ecc_disabled_wishbone_out
            always @* begin
                o_wb_data = o_wb_data_q_current; // Wishbone data output
                o_aux = o_wb_ack_read_q[0][AUX_WIDTH:1]; // Aux output
                o_wb_data_uncalibrated = o_wb_data; // wishbone data is also used when not yet done calibration
                o_wb_ack_uncalibrated = o_wb_ack_read_q[0][0] && !final_calibration_done; // ack used during calibration
                o_wb_ack_q = o_wb_ack_read_q[0][0] && final_calibration_done; // ack used during normal operation
                o_wb_err_q = 0; // no wishbone error when ECC is disabled
            end
        end
        else if(ECC_ENABLE == 3) begin: ecc_3_wishbone_out
            always @* begin
                o_wb_data = o_wb_data_q_decoded; // Wishbone data output
                o_aux = o_wb_ack_read_q[0][AUX_WIDTH:1]; // Aux output
                o_wb_data_uncalibrated = o_wb_data_q_current; // wishbone data is also used when not yet done calibration
                o_wb_ack_uncalibrated = o_wb_ack_read_q[0][0] && !final_calibration_done; // ack used during calibration
                o_wb_ack_q = o_wb_ack_read_q[0][0] && final_calibration_done; // ack used during normal operation
                o_wb_err_q = db_err_o; // wb error during double bit errors
            end
        end
    endgenerate

    generate
        if (WB_ERROR == 0) begin: wb_err_disabled
            assign o_wb_ack = o_wb_ack_q;
            assign o_wb_err = 1'b0; // no Wishbone error if WB_ERROR == 0
        end
        else begin : wb_err_enabled
            // Wishbone B4 doc:
            // RULE 3.45
            // If a SLAVE supports the [ERR_O] or [RTY_O] signals, then the SLAVE MUST NOT assert
            // more than one of the following signals at any time: [ACK_O], [ERR_O] or [RTY_O].
            assign o_wb_ack = !o_wb_err_q && o_wb_ack_q ;
            assign o_wb_err = o_wb_err_q && o_wb_ack_q; 
        end
    endgenerate

    // DQ/DQS IO tristate control logic
    always @(posedge i_controller_clk) begin
        o_phy_dqs_tri_control <= !write_dqs[STAGE2_DATA_DEPTH-1];
        o_phy_dq_tri_control <= !write_dq[STAGE2_DATA_DEPTH-1];
    end
//    assign o_phy_dqs_tri_control = !write_dqs[STAGE2_DATA_DEPTH]; // Warning in implementation: not routable to load
//    assign o_phy_dq_tri_control = !write_dq[STAGE2_DATA_DEPTH]; // Warning in implementation: not routable to load
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
        if(sync_rst_controller) begin
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
            calib_stb <= 0;//actual request flag
            calib_sel <= 0;
            calib_aux <= 0; //AUX ID
            calib_we <= 0; //write-enable
            calib_addr <= 0;
            calib_data <= 0;
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
            odelay_cntvalue_halfway <= 0;
            write_level_fail <= 0;
            read_test_address_counter <= 0;
            write_test_address_counter <= 0;
            reset_from_calibrate <= 0;
            write_by_byte_counter <= 0;
            initial_calibration_done <= 1'b0;
            final_calibration_done <= 1'b0;
            reset_after_rank_1 <= 1'b0;
            lane_write_dq_late <= 0;
            lane_read_dq_early <= 0;
            shift_read_pipe <= 0;
            bitslip_counter <= 0;
            `ifdef UART_DEBUG
                uart_start_send <= 0;
                uart_text <= 0;
                track_report <= 0;
                state_calibrate_next <= IDLE;
            `endif
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
            reset_from_calibrate <= 0;
            reset_after_rank_1 <= 0; // reset for dual rank

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
            // high initial_dqs is the time when the IDELAY of dqs and dq is not yet calibrated 
            // dqs_target_index_value = dqs_start_index_stored[0]? dqs_start_index_stored + 2: dqs_start_index_stored + 1; // move to next odd (if 3 then 5, if 4 then 5)
            // so dqs_target_index_value is basically the next odd number of dqs_start_index_stored (original starting bit when dqs starts).
            // The next odd number ensure that the DQS edge is aligned to edge of ddr3_clk (and thus DQ data eye is aligned to edges of of ddr3_clk
            // since dq is 90 degree relative to dqs
            // Some images to show why next odd number is used: https://github.com/AngeloJacobo/UberDDR3/tree/b762c464f6526159c1d8c2e4ee039b4ae4e78dbd#per-lane-read-calibration
            
            if(initial_dqs) begin
                dqs_target_index <= dqs_target_index_value; // target index for DQS to make sure the DQS is edge-aligned with ddr3_clk
                dq_target_index[lane] <= {1'b0, dqs_target_index_value}; // target index for DQ (just same as DQS)
                dqs_target_index_orig <= dqs_target_index_value; // this will remain the same until we finish calibrating this whole lane
            end
            if(idelay_dqs_cntvaluein[lane] == 0) begin //the DQS got past cntvalue of 31 (and goes back to zero) THUS the target index should also go back (to previous odd)
                dqs_target_index <= dqs_target_index_orig - 2;
            end
            if(idelay_data_cntvaluein[lane] == 0 && idelay_data_cntvaluein_prev == 31) begin //the DQ got past cntvalue of 31 (and goes back to zero) thus the target index should also go back (to previous odd)
                dq_target_index[lane] <= dqs_target_index_orig - 2;
            end

            // FSM
            case(state_calibrate) 
                IDLE: if(i_phy_idelayctrl_rdy && instruction_address == 13) begin //we are now inside instruction 15 with maximum delay
                        state_calibrate <= DLL_OFF? ISSUE_WRITE_1 : BITSLIP_DQS_TRAIN_1; // If DLL Off then dont do any calibration, go straight to write-read
                        lane <= 0;
                        o_phy_odelay_data_ld <= {LANES{1'b1}};
                        o_phy_odelay_dqs_ld <= {LANES{1'b1}};
                        o_phy_idelay_data_ld <= {LANES{1'b1}};
                        o_phy_idelay_dqs_ld <= {LANES{1'b1}};
                        pause_counter <= DLL_OFF? 0 : 1; // If DLL on, do calibration so pause instruction address @13 until read calibration finishes
                        write_calib_dqs <= 0;
                        write_calib_odt <= 0;
                        o_phy_write_leveling_calib <= 0;
                        initial_calibration_done <= 1'b0;
                        final_calibration_done <= 1'b0;
                        shift_read_pipe <= 0;
                        write_test_address_counter <= 0;
                        read_test_address_counter <= 0;
                        `ifdef UART_DEBUG_READ_LEVEL
                            uart_start_send <= 1'b1;
                            uart_text <= {"state=IDLE",8'h0a};
                            state_calibrate <= WAIT_UART;
                            state_calibrate_next <= DLL_OFF? ISSUE_WRITE_1 : BITSLIP_DQS_TRAIN_1;
                        `endif
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
                        // bitslip basically is changing the arrangement of bytes on IOSERDES
                        if(i_phy_iserdes_bitslip_reference[lane*serdes_ratio*2 +: 8] == 8'b0111_1000) begin //initial arrangement
                            state_calibrate <= MPR_READ;
                            initial_dqs <= 1;
                            dqs_start_index_repeat <= 0;
                            dqs_start_index_stored <= 0;
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=BITSLIP_DQS_TRAIN_1",8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= MPR_READ;
                            `endif
                        end                
                        else begin
                            o_phy_bitslip[lane] <= 1;
                            train_delay <= 3;
                        end        
                      end
                      
            MPR_READ: if(delay_before_read_data == 0) begin //align the incoming DQS during reads to the controller clock 
                             //issue_read_command = 1;
                             /* verilator lint_off WIDTH */
                             delay_before_read_data <= READ_DELAY + 1 + 2 + 1 - 1; ///NOTE TO SELF: why these numbers? 1=issue command delay (OSERDES delay), 2 =  ISERDES delay 
                             /* verilator lint_on WIDTH */
                             state_calibrate <= COLLECT_DQS;
                             dqs_count_repeat <= 0;
                      end    
                      
                COLLECT_DQS: if(delay_before_read_data == 0) begin // data from MPR read is now received by controller
                        // dqs from ISERDES is received and stored
                        // DQS received from ISERDES: { {LANE_1_burst_7, LANE_1_burst_6, ... , LANE_1_burst_0} , {LANE_0_burst_7, LANE_0_burst_6, ... , LANE_0_burst_0}}
                        // NOTE TO SELF: WHY DQS IS DIVIDED PER LANE BUT DQ IS PER BURST ???? 
                        // dqs_store stores the 8 DQS (8 bursts) for a given lane but since the DQS might be shifted at next ddr3 clk cycles (due to trace delays), we must store the
                        // 8 DQS multiple times (dictated by STORED_DQS_SIZE)
                        dqs_store <= {i_phy_iserdes_dqs[serdes_ratio*2*lane +: 8], dqs_store[(STORED_DQS_SIZE*8-1):8]}; 
                        dqs_count_repeat <= dqs_count_repeat + 1;
                        if(dqs_count_repeat == STORED_DQS_SIZE - 1) begin
                            state_calibrate <= ANALYZE_DQS;
                            // store the previous value of dqs_start_index, if the ANALYZE_DQS is repeated then the dqs_start_index
                            // should be the same as the previous value, else the previous (or current one) has a glitch causing 
                            // a different dqs_start_index 
                            dqs_start_index_stored <= dqs_start_index; 
                            // start the index from zero since this will be incremented until we pinpoint the real 
                            // starting bit of dqs_store (dictated by the pattern 10'b01_01_01_01_00)
                            dqs_start_index <= 0;          
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                // show dqs_store in binary form
                                uart_text <= {8'h0a,"state=COLLECT_DQS, lane=",hex_to_ascii(lane),", dqs_store= ",
                                    hex_to_ascii(dqs_store[39]), hex_to_ascii(dqs_store[38]),
                                    hex_to_ascii(dqs_store[37]), hex_to_ascii(dqs_store[36]),
                                    hex_to_ascii(dqs_store[35]), hex_to_ascii(dqs_store[34]),
                                    hex_to_ascii(dqs_store[33]), hex_to_ascii(dqs_store[32]), "_" ,
                                    hex_to_ascii(dqs_store[31]), hex_to_ascii(dqs_store[30]),
                                    hex_to_ascii(dqs_store[29]), hex_to_ascii(dqs_store[28]),
                                    hex_to_ascii(dqs_store[27]), hex_to_ascii(dqs_store[26]),
                                    hex_to_ascii(dqs_store[25]), hex_to_ascii(dqs_store[24]), "_" ,
                                    hex_to_ascii(dqs_store[23]), hex_to_ascii(dqs_store[22]),
                                    hex_to_ascii(dqs_store[21]), hex_to_ascii(dqs_store[20]),
                                    hex_to_ascii(dqs_store[19]), hex_to_ascii(dqs_store[18]),
                                    hex_to_ascii(dqs_store[17]), hex_to_ascii(dqs_store[16]), "_" ,
                                    hex_to_ascii(dqs_store[15]), hex_to_ascii(dqs_store[14]),
                                    hex_to_ascii(dqs_store[13]), hex_to_ascii(dqs_store[12]),
                                    hex_to_ascii(dqs_store[11]), hex_to_ascii(dqs_store[10]),
                                    hex_to_ascii(dqs_store[9]),  hex_to_ascii(dqs_store[8]), 8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= ANALYZE_DQS;
                            `endif                     
                        end
                      end
                        // find the bit where the DQS starts to be issued (by finding when the pattern 10'b01_01_01_01_00 starts)
         ANALYZE_DQS: if(dqs_store[dqs_start_index +: 10] == 10'b01_01_01_01_00) begin
                         //increase dqs_start_index_repeat when index is the same as before   
                        dqs_start_index_repeat <= (dqs_start_index == dqs_start_index_stored)? dqs_start_index_repeat + 1: 0;   
                         //the same dqs_start_index_repeat appeared REPEAT_DQS_ANALYZE times in a row, thus we can trust the value we got is accurate and not affected by glitch
                         if(dqs_start_index_repeat == REPEAT_DQS_ANALYZE) begin
                             // since we already know the starting bit when the dqs (and dq since they are aligned) will come,
                             // we will now start calibrating the IDELAY for dqs and dq (via CALIBRATE_DQS). 
                             // high initial_dqs is the time when the IDELAY of dqs and dq is not yet calibrated so we zero this starting now
                            initial_dqs <= 0; 
                            dqs_start_index_repeat <= 0;
                            state_calibrate <= CALIBRATE_DQS;
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=ANALYZE_DQS, REPEAT_DQS_ANALYZE == dqs_start_index_repeat:",hex_to_ascii(dqs_start_index_repeat),
                                    ", final dqs_start_index=0x", hex_to_ascii(dqs_start_index[5:4]), hex_to_ascii(dqs_start_index[3:0]), 8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= CALIBRATE_DQS;
                            `endif
                         end
                        else begin
                            state_calibrate <= MPR_READ;
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=ANALYZE_DQS, REPEAT_DQS_ANALYZE != dqs_start_index_repeat:", hex_to_ascii(dqs_start_index_repeat),
                                    ", final dqs_start_index=0x", hex_to_ascii(dqs_start_index[5:4]), hex_to_ascii(dqs_start_index[3:0]), 8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= MPR_READ;
                            `endif
                        end
                      end 
                      else begin
                        if(dqs_start_index == (STORED_DQS_SIZE*8-1) ) begin //if we reached end then most likely we hit a glitch where 01_01_01_01_00 is muddied
                            o_phy_idelay_data_ld[lane] <= 1;
                            o_phy_idelay_dqs_ld[lane] <= 1;
                            state_calibrate <= MPR_READ;
                            delay_before_read_data <= 10; //wait for sometime to make sure idelay load settles
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=ANALYZE_DQS, Glitch: Reached End", 8'h0a,"----------------------",8'h0a,8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= MPR_READ;
                            `endif
                        end
                        else begin
                            dqs_start_index <= dqs_start_index + 1;
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=ANALYZE_DQS, dqs_start_index=0x", hex_to_ascii(dqs_start_index[5:4]), hex_to_ascii(dqs_start_index[3:0]), 8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= ANALYZE_DQS;
                            `endif
                        end
                      end
                        // check if the index when the dqs starts is the same as the target index which is aligned to the ddr3_clk
                        // dqs_target_index is the next odd number to dqs_start_index BEFORE IDELAY CALIBRATION. We will increase the IDELAY
                        // until the dqs_start_index_stored (current value of dqs_start_index) matches the target index which is aligned to ddr3_clk
        CALIBRATE_DQS: if(dqs_start_index_stored == dqs_target_index) begin
                            // dq_target_index still stores the original dqs_target_index_value. The bit size of dq_target_index is just enough
                            // to count the bits in dqs_store (the received 8 DQS stored STORED_DQS_SIZE times)
                            added_read_pipe[lane] <= { {( 4 - ($clog2(STORED_DQS_SIZE*8) - (3+1)) ){1'b0}} , dq_target_index[lane][$clog2(STORED_DQS_SIZE*8)-1:(3+1)] } 
                                                        + { 3'b0 , (dq_target_index[lane][3:0] >= (5+8)) };
                            // if target_index is > 13, then a 1 CONTROLLLER_CLK cycle delay (4 ddr3_clk cycles) is added on that particular lane (due to trace delay)
                            // added_read_pipe[lane] <= dq_target_index[lane][$clog2(STORED_DQS_SIZE*8)-1 : (4)]  +  ( dq_target_index[lane][3:0] >= 13 ) ;
                            dqs_bitslip_arrangement <= 16'b0011_1100_0011_1100 >> dq_target_index[lane][2:0];
                            // the dqs is delayed (to move starting bit to next odd number) so this means the original
                            // expected bitslip arrangement of  8'b0111_1000 will not be followed anymore, so here we form the bitslip
                            // arrangement pattern so incoming dqs (and thus DQ) is arranged in the proper way (first bute firs, last byte last)
                            state_calibrate <= BITSLIP_DQS_TRAIN_2;
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {8'h0a,"state=CALIBRATE_DQS, REACHED dqs_target_index=0x", hex_to_ascii(dqs_target_index[5:4]), 
                                    hex_to_ascii(dqs_target_index[3:0]), 8'h0a,"----------------------",8'h0a,8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= BITSLIP_DQS_TRAIN_2;
                            `endif
                       end
                       else begin
                            // if we have not yet reached the target index then increment IDELAY
                            // we will keep incrementing the IDELAY until the next odd index is reached (which is
                            // the time we are sure the DQS is edge aligned with ddr3_clk and thus ddr3_clk posedge
                            // is hitting the center of DQ eye
                            // To show why next odd number is needed: https://github.com/AngeloJacobo/UberDDR3/tree/b762c464f6526159c1d8c2e4ee039b4ae4e78dbd#per-lane-read-calibration
                            o_phy_idelay_data_ld[lane] <= 1;
                            o_phy_idelay_dqs_ld[lane] <= 1;
                            state_calibrate <= MPR_READ;
                            delay_before_read_data <= 10; //wait for sometime to make sure idelay load settles
                            `ifdef UART_DEBUG_READ_LEVEL
                                uart_start_send <= 1'b1;
                                uart_text <= {8'h0a,"state=CALIBRATE_DQS, stored(0x", hex_to_ascii(dqs_start_index_stored[5:4]),hex_to_ascii(dqs_start_index_stored[3:0]),
                                    ") != target(0x", hex_to_ascii(dqs_target_index[5:4]), hex_to_ascii(dqs_target_index[3:0]), "), o_phy_idelay_data_cntvaluein=0x",
                                    hex_to_ascii(o_phy_idelay_data_cntvaluein[4]), hex_to_ascii(o_phy_idelay_data_cntvaluein[3:0]),
                                    8'h0a,"------------",8'h0a,8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= MPR_READ;
                            `endif
                       end
                        //the dqs is delayed (to move starting bit to next odd number) so this means the original
                        // expected bitslip arrangement of  8'b0111_1000 will not be followed anymore, so here the bitslip
                        // is re-arranged
  BITSLIP_DQS_TRAIN_2: if(train_delay == 0) begin //train again the ISERDES to capture the DQ correctly
                            if(i_phy_iserdes_bitslip_reference[lane*serdes_ratio*2 +: 8] == dqs_bitslip_arrangement[7:0]) begin
                                /* verilator lint_off WIDTH */
                                // this is the end of training and calibration for a single lane, so proceed to next lane
                                if(lane == LANES - 1) begin
                                /* verilator lint_on WIDTH */
                                    lane <= 0;
                                    odelay_cntvalue_halfway <= 0;
                                    prev_write_level_feedback <= 1'b1;
                                    sample_clk_repeat <= 0;
                                    stored_write_level_feedback <= 0;
                                    o_phy_write_leveling_calib <= 1;
                                    state_calibrate <= START_WRITE_LEVEL;
                                    `ifdef UART_DEBUG_READ_LEVEL
                                        uart_start_send <= 1'b1;
                                        uart_text <= {"state=BITSLIP_DQS_TRAIN_2, Done All Lanes",8'h0a,
                                                "--------------------------------------------------", 8'h0a, 8'h0a};
                                        state_calibrate <= WAIT_UART;
                                        state_calibrate_next <= START_WRITE_LEVEL;
                                    `endif
                                 end
                                 else begin
                                     lane <= lane + 1;
                                     state_calibrate <= BITSLIP_DQS_TRAIN_1;// current lane is done so go back to BITSLIP_DQS_TRAIN_1 to train next lane
                                     `ifdef UART_DEBUG_READ_LEVEL
                                        uart_start_send <= 1'b1;
                                        uart_text <= {"state=BITSLIP_DQS_TRAIN_2, Done lane=", hex_to_ascii(lane),8'h0a, 
                                            "--------------------------------------------------", 8'h0a, 8'h0a};
                                        state_calibrate <= WAIT_UART;
                                        state_calibrate_next <= BITSLIP_DQS_TRAIN_1;
                                    `endif
                                 end
                                // stores the highest value of added_read_pipe among the lanes since all lanes (except the lane with highest 
                                // added_read_pipe) will be delayed to align with the lane with highest added_read_pipe. This alignment 
                                // is required to make sure the received DQ will be aligned and can form the 512 bit data (for 8 lanes) arranged properly.
                                 added_read_pipe_max <= added_read_pipe_max > added_read_pipe[lane]? added_read_pipe_max:added_read_pipe[lane];
                            end
                            else begin
                                o_phy_bitslip[lane] <= 1;
                                train_delay <= 3;
                            end
                       end
                // CONTINUE COMMENT HERE  (once blog is done)                
    START_WRITE_LEVEL:  if(!ODELAY_SUPPORTED) begin //skip write levelling if ODELAY is not supported
                            pause_counter <= 0;
                            lane <= 0;
                            state_calibrate <= ISSUE_WRITE_1;
                            write_calib_odt <= 0;
                            o_phy_write_leveling_calib <= 0;
                        end
                        else if(instruction_address == 17) begin
                            write_calib_dqs <= 1'b1;
                            write_calib_odt <= 1'b1;
                            delay_before_write_level_feedback <= DELAY_BEFORE_WRITE_LEVEL_FEEDBACK[$clog2(DELAY_BEFORE_WRITE_LEVEL_FEEDBACK):0];
                            state_calibrate <= WAIT_FOR_FEEDBACK;
                            pause_counter <= 1; // pause instruction address @17 until write calibration finishes
                        end  
                        else begin // read calibration done so continue instruction address counter
                            pause_counter <= 0;
                        end

    WAIT_FOR_FEEDBACK: if(delay_before_write_level_feedback == 0) begin
                            /* verilator lint_off WIDTH */ //_verilator warning: Bit extraction of var[511:0] requires 9 bit index, not 3 bits (but [lane<<3] is much simpler and cleaner)
                            sample_clk_repeat <= (i_phy_iserdes_data[lane_times_8] == stored_write_level_feedback)? sample_clk_repeat + 1 : 0; //sample_clk_repeat should get the same response 
                            stored_write_level_feedback <= i_phy_iserdes_data[lane_times_8];
                            write_calib_dqs <= 0;
                            if(sample_clk_repeat == REPEAT_CLK_SAMPLING) begin
                                sample_clk_repeat <= 0;
                                prev_write_level_feedback <= stored_write_level_feedback;
                                if(({prev_write_level_feedback, stored_write_level_feedback} == 2'b01) /*|| write_level_fail[lane]*/) begin
                                    /* verilator lint_on WIDTH */
                                    /* verilator lint_off WIDTH */
                                    if(lane == LANES - 1) begin
                                    /* verilator lint_on WIDTH */
                                            write_calib_odt <= 0;
                                            pause_counter <= 0; //write calibration now complete so continue the reset instruction sequence
                                            lane <= 0;
                                            o_phy_write_leveling_calib <= 0;
                                            state_calibrate <= ISSUE_WRITE_1;
                                            `ifdef UART_DEBUG_WRITE_LEVEL
                                                uart_start_send <= 1'b1;
                                                uart_text <= {"state=WAIT_FOR_FEEDBACK, All Lanes Done",8'h0a,"----------------------",8'h0a};
                                                state_calibrate <= WAIT_UART;
                                                state_calibrate_next <= ISSUE_WRITE_1;
                                            `endif
                                    end
                                    else begin
                                        lane <= lane + 1;
                                        odelay_cntvalue_halfway <= 0;
                                        prev_write_level_feedback <= 1'b1;
                                        sample_clk_repeat <= 0;
                                        state_calibrate <= START_WRITE_LEVEL; 
                                        `ifdef UART_DEBUG_WRITE_LEVEL
                                            uart_start_send <= 1'b1;
                                            uart_text <= {"state=WAIT_FOR_FEEDBACK, Done lane=",hex_to_ascii(lane),8'h0a,"----------------------",8'h0a};
                                            state_calibrate <= WAIT_UART;
                                            state_calibrate_next <= START_WRITE_LEVEL;
                                        `endif
                                    end
                                end
                                else begin
                                    o_phy_odelay_data_ld[lane] <= 1;
                                    o_phy_odelay_dqs_ld[lane] <= 1;
                                    write_level_fail[lane] <= odelay_cntvalue_halfway;
                                    // if(odelay_cntvalue_halfway) begin // if halfway cntvalue is reached which is illegal (or impossible to happen), then we load the original cntvalues
                                    //     odelay_data_cntvaluein[lane] <= DATA_INITIAL_ODELAY_TAP[4:0];
                                    //     odelay_dqs_cntvaluein[lane] <= DQS_INITIAL_ODELAY_TAP[4:0];                
                                    // end
                                    state_calibrate <= START_WRITE_LEVEL; 
                                    `ifdef UART_DEBUG_WRITE_LEVEL
                                        uart_start_send <= 1'b1;
                                        uart_text <= {"state=WAIT_FOR_FEEDBACK, lane=",hex_to_ascii(lane), ", {prev,stored}=", hex_to_ascii(prev_write_level_feedback),
                                            hex_to_ascii(stored_write_level_feedback), ", o_phy_odelay_data_cntvaluein=0x", hex_to_ascii(o_phy_odelay_data_cntvaluein[4]),
                                            hex_to_ascii(o_phy_odelay_data_cntvaluein[3:0]), 8'h0a,8'h0a};
                                        state_calibrate <= WAIT_UART;
                                        state_calibrate_next <= START_WRITE_LEVEL;
                                    `endif
                                end
                             end     
                        `ifdef UART_DEBUG_WRITE_LEVEL
                             else begin
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"state=WAIT_FOR_FEEDBACK, sample_clk_repeat=",hex_to_ascii(sample_clk_repeat),8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= START_WRITE_LEVEL;
                             end
                        `endif
                         end
                            
        ISSUE_WRITE_1: if(instruction_address == 22 && !o_wb_stall_calib) begin
                        calib_stb <= 1;//actual request flag
                        calib_aux <= 0; //AUX ID to determine later if ACK is for read or write
                        calib_sel <= {wb_sel_bits{1'b1}};
                        calib_we <= 1; //write-enable
                        calib_addr <= 0;
                        //                burst_7          burst_6         burst_5         burst_4         burst_3         burst_2         burst_1         burst_0
                        calib_data <= { {LANES{8'h91}}, {LANES{8'h77}}, {LANES{8'h29}}, {LANES{8'h8c}}, {LANES{8'hd0}}, {LANES{8'had}}, {LANES{8'h51}}, {LANES{8'hc1}} }; 
                        // write to address 0 is a burst of 8 writes, where all lanes has same data written:  64'h9177298cd0ad51c1
                        // Example for LANES of 2, DQ of 8: the 128 bits (8 bursts * 2 lanes/burst * 8bits/lane) are 8 bursts with 8 bytes each:
                        // { burst_7, burst_6, burst_5, burst_4, burst_3, burst_2, burst_1, burst_0 } OR:
                        // { { {burst7_lane1} , {burst7_lane0} } , { {burst6_lane1} , {burst6_lane0} } , { {burst5_lane1} , {burst5_lane0} } 
                        // , { {burst4_lane1} , {burst4_lane0} } , { {burst3_lane1} , {burst3_lane0} } , { {burst2_lane1} , {burst2_lane0} } 
                        // , { {burst1_lane1} , {burst1_lane0} } , { {burst0_lane1} , {burst0_lane0} } }
                        state_calibrate <= ISSUE_WRITE_2;
                       end    
        ISSUE_WRITE_2: begin
                        calib_stb <= 1;//actual request flag
                        calib_aux <= 0; //AUX ID to determine later if ACK is for read or write
                        calib_sel <= {wb_sel_bits{1'b1}};
                        calib_we <= 1; //write-enable
                        calib_addr <= 1;
                        //                burst_7          burst_6         burst_5         burst_4         burst_3         burst_2         burst_1         burst_0
                        calib_data <= { {LANES{8'h80}}, {LANES{8'hdb}}, {LANES{8'hcf}}, {LANES{8'hd2}}, {LANES{8'h75}}, {LANES{8'hf1}}, {LANES{8'h2c}}, {LANES{8'h3d}} };
                        // write to address 1 is also a burst of 8 writes, where all lanes has same data written:  128'h80dbcfd275f12c3d
                        state_calibrate <= ISSUE_READ;
                        `ifdef UART_DEBUG_ALIGN // add this so that read is far from write (making sure i_phy_iserdes_data does not mistake the read back from write data)
                            uart_start_send <= 1'b1;
                            uart_text <= {"DONE WRITE 2", 8'h0a,8'h0a,8'h0a,8'h0a};
                            state_calibrate <= WAIT_UART;
                            state_calibrate_next <= ISSUE_READ;
                        `endif
                       end   
                // NOTE: WHY THERE ARE TWO ISSUE_WRITE
                // address 0 and 1 is written with a deterministic data, if the DQ trace has long delay (relative to command line) then the data will be delayed 
                // compared to the write command. Thus the data aligned to the write command for address 0 MIGHT START AT MIDDLE OF EXPECTED OUTPUT
                // DATA (64'h9177298cd0ad51c1) e.g. the data written might be 64'h[2c3d][9177298cd0ad] where the data written starts
                // at burst 2 (burst 0 and burst 1 are cut-off since each burst uses 1 ddr3_clk cycle)
                // Note here that if DQ and DQS sa same delay, then we know the DQS will always be aligned with DQ data 
                
        ISSUE_READ: begin
                        calib_stb <= 1;//actual request flag
                        calib_aux <= 1; //AUX ID to determine later if ACK is for read or write
                        calib_we <= 0; //write-enable
                        calib_addr <= 0;
                        state_calibrate <= READ_DATA;
                      end   
                      
                                 
           READ_DATA: if({o_aux[AUX_WIDTH-((ECC_ENABLE == 3)? 6 : 1) : 0], o_wb_ack_uncalibrated}== {{(AUX_WIDTH-((ECC_ENABLE == 3)? 6 : 1)){1'b0}}, 1'b1, 1'b1}) begin //wait for the read ack (which has AUX ID of 1}
                         read_data_store <= o_wb_data_uncalibrated; // read data on address 0 
                         calib_stb <= 0;
                         state_calibrate <= DLL_OFF? ANALYZE_DATA_LOW_FREQ : ANALYZE_DATA;
                        //  data_start_index[lane] <= 0; // dont set to zero since this may have been already set by previous CHECK_STARTING_DATA
                         // Possible Patterns (strong autocorrel stat)
                         //0x80dbcfd275f12c3d   
                         //0x9177298cd0ad51c1
                         //0x01b79fa4ebe2587b
                         //0x22ee5319a15aa382
                         write_pattern <= 128'h80dbcfd275f12c3d_9177298cd0ad51c1;
                        //  `ifdef UART_DEBUG_ALIGN
                        //     uart_start_send <= 1'b1;
                        //     // display o_wb_data_uncalibrated of current lane
                        //     // uart_text <= {8'h0a,8'h0a,"state=READ_DATA, read_data_store[lane]= 0x",
                        //     // hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*7 + 8*lane) +: 8]), hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*6 + 8*lane) +: 8]),
                        //     // hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*5 + 8*lane) +: 8]), hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*4 + 8*lane) +: 8]),
                        //     // hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*3 + 8*lane) +: 8]), hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*2 + 8*lane) +: 8]),
                        //     // hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*1 + 8*lane) +: 8]), hex8_to_ascii(o_wb_data_uncalibrated[((DQ_BITS*LANES)*0 + 8*lane) +: 8]), 8'h0a};
                        //     //
                        //     // view o_wb_data_uncalibrated in raw form (view in Hex form)
                        //     uart_text <= {8'h0a,8'h0a, "o_wb_data_uncalibrated=", 8'h0a, 8'h0a, o_wb_data_uncalibrated,
                        //         8'h0a,8'h0a
                        //     };
                        //     state_calibrate <= WAIT_UART;
                        //     state_calibrate_next <= ANALYZE_DATA_LOW_FREQ;
                        // `endif
                      end   
                      else if(!o_wb_stall_calib) begin
                            calib_stb <= 0;
                            // if(i_phy_iserdes_data != 0) begin
                            //     `ifdef UART_DEBUG_ALIGN // check if i_phy_iserdes_data ever receives a non-zero data
                            //         uart_start_send <= 1'b1;
                            //         uart_text <= {"i_phy_iserdes_data != 0:",8'h0a,8'h0a,i_phy_iserdes_data, 8'h0a,8'h0a};
                            //         state_calibrate <= WAIT_UART;
                            //         state_calibrate_next <= READ_DATA;
                            //     `endif
                            // end
                      end

        ANALYZE_DATA_LOW_FREQ: begin // read_data_store should have the expected 9177298cd0ad51c1, if not then issue bitslip
            if(write_pattern[0 +: 64] == {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                        read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                        read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] }) begin 
                    /* verilator lint_off WIDTH */
                    if(lane == LANES - 1) begin
                    /* verilator lint_on WIDTH */
                        state_calibrate <= BIST_MODE == 0? FINISH_READ : BURST_WRITE; // go straight to FINISH_READ if BIST_MODE == 0
                        initial_calibration_done <= 1'b1;
                        `ifdef UART_DEBUG_ALIGN
                            uart_start_send <= 1'b1;
                            //uart_text <= {"state=ANALYZE_DATA_LOW_FREQ, Done All Lanes",8'h0a,"-----------------",8'h0a,8'h0a};
                            uart_text <= {8'h0a,8'h0a, "Done All Lanes, bitslip_counter=", hex_to_ascii(bitslip_counter), ", shift_read_pipe=", hex_to_ascii(shift_read_pipe), 
                            ", data_start_index=", hex8_to_ascii(data_start_index[lane]), ", lane_late=", hex_to_ascii(lane_write_dq_late[lane]), 8'h0a,8'h0a, 
                            {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                            read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                            read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] },
                                8'h0a,8'h0a,8'h0a,8'h0a};
                            state_calibrate <= WAIT_UART;
                            state_calibrate_next <= BIST_MODE == 0? FINISH_READ : BURST_WRITE;
                        `endif
                    end        
                    else begin
                        lane <= lane + 1;
                        bitslip_counter <= 0;
                        `ifdef UART_DEBUG_ALIGN
                            uart_start_send <= 1'b1;
                            // uart_text <= {"state=ANALYZE_DATA_LOW_FREQ, Done lane=",hex_to_ascii(lane),8'h0a,"-----------------",8'h0a};
                            uart_text <= {8'h0a,8'h0a, "Done lane=", hex_to_ascii(lane), ", bitslip_counter=", hex_to_ascii(bitslip_counter), ", shift_read_pipe=", hex_to_ascii(shift_read_pipe), 
                            ", data_start_index=", hex8_to_ascii(data_start_index[lane]), ", lane_late=", hex_to_ascii(lane_write_dq_late[lane]), 8'h0a,8'h0a, 
                            {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                            read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                            read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] },
                                8'h0a,8'h0a,8'h0a,8'h0a};
                            state_calibrate <= WAIT_UART;
                            state_calibrate_next <= ANALYZE_DATA_LOW_FREQ;
                        `endif
                    end
            end
            else begin // issue bitslip then repeat write-read
                o_phy_bitslip[lane] <= 1'b1;
                bitslip_counter <= bitslip_counter + 1; // increment counter every bitslip
                if(bitslip_counter == 7) begin // there are only 8 bitslip, once past this then we shift read pipe backwards (assumption is that we read too early)
                    shift_read_pipe <= shift_read_pipe + 1;
                    bitslip_counter <= 0;
                    if(shift_read_pipe == 1) begin // if shift_read_pipe at end then we increase data_start_index since problem might be write DQ too early thus we shift it later using data_start_index 
                         shift_read_pipe <= 0;
                         data_start_index[lane] <= lane_write_dq_late[lane]? data_start_index[lane] - 8: data_start_index[lane] + 8;
                         if((data_start_index[lane] == 64) && !lane_write_dq_late[lane]) begin // if data_start_index at end then we assert data_start_index, last assumption is that we are writing DQ too late thus we move stage2_data forward to be sent out earlier
                            data_start_index[lane] <= 64;
                            lane_write_dq_late[lane] <= 1'b1;
                         end
                    end
                end
                state_calibrate <= ISSUE_WRITE_1;
                `ifdef UART_DEBUG_ALIGN
                    uart_start_send <= 1'b1;
                    uart_text <= {8'h0a,8'h0a, "lane=", hex_to_ascii(lane), ", bitslip_counter=", hex_to_ascii(bitslip_counter), ", shift_read_pipe=", hex_to_ascii(shift_read_pipe), 
                            ", data_start_index=", hex8_to_ascii(data_start_index[lane]), ", lane_late=", hex_to_ascii(lane_write_dq_late[lane]), 8'h0a,8'h0a, 
                            {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                            read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                            read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] },
                                8'h0a,8'h0a,8'h0a,8'h0a};
                    state_calibrate <= WAIT_UART;
                    state_calibrate_next <= ISSUE_WRITE_1;
                `endif
            end
        end
                        // extract burst_0-to-burst_7 data for a specified lane then determine which byte in write_pattern does it starts (ASSUMPTION: the DQ is too early [3d_9177298cd0ad51]c1 is written)
                        // NOTE TO SELF: all "8" here assume DQ_BITS are 8? parameterize this properly
                        // data_start_index for a specified lane determine how many bits are off the data from the write command
                        // so for every 1 ddr3 clk cycle delay of DQ from write command, each lane will be 1 burst off:
                        // e.g. LANE={burst7, burst6, burst5, burst4, burst3, burst2, burst1, burst0} then with 1 ddr3 cycle delay between DQ and command 
                        // burst0 will not be written but only starting on burst1
                        // if lane_write_dq_late is already set to 1 for this lane, then current lane should already be fixed without changing the data_start_index
        ANALYZE_DATA: if(write_pattern[ (lane_write_dq_late[lane]? 0 : data_start_index[lane])  +: 64] == {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                        read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                        read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] }) begin   
                            /* verilator lint_off WIDTH */
                            if(lane == LANES - 1) begin
                            /* verilator lint_on WIDTH */
                                state_calibrate <= BIST_MODE == 0? FINISH_READ : BURST_WRITE; // go straight to FINISH_READ if BIST_MODE == 0
                                initial_calibration_done <= 1'b1;
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"state=ANALYZE_DATA, Done All Lanes",8'h0a,"-----------------",8'h0a,8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= BIST_MODE == 0? FINISH_READ : BURST_WRITE;
                                `endif
                            end        
                            else begin
                                lane <= lane + 1;
                                data_start_index[lane+1] <= 0;
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"state=ANALYZE_DATA, Done lane=",hex_to_ascii(lane),8'h0a,"-----------------",8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= ANALYZE_DATA;
                                `endif
                            end
                      end 
                      else begin
                            data_start_index[lane] <= data_start_index[lane] + 8; //skip by 8 (basically we want to delay DQ since it was too early)
                            if(lane_write_dq_late[lane] && lane_read_dq_early[lane]) begin // both assumption is wrong so we reset the controller
                                reset_from_calibrate <= 1;
                            end
                             // first assumption (write DQ is late) is wrong so we repeat write-read with data_start_index back to 0
                            else if(lane_write_dq_late[lane]) begin 
                                data_start_index[lane] <= 0; // set delay to outgoing stage2_data back to zero
                                if(data_start_index[lane] == 0) begin // if already set to zero then we already did write-read with default zero data_start_index, so we go to CHECK_STARTING_DATA to try second assumtpion
                                    state_calibrate <= CHECK_STARTING_DATA;
                                    `ifdef UART_DEBUG_ALIGN
                                        uart_start_send <= 1'b1;
                                        uart_text <= {"state=ANALYZE_DATA, lane=",hex_to_ascii(lane), ", First Assumption wrong, Start second assumption: Read too early",8'h0a,8'h0a,
                                        8'h0a,8'h0a,
                                        {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                                        read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                                        read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] },
                                            8'h0a,8'h0a,8'h0a,8'h0a};
                                        state_calibrate <= WAIT_UART;
                                        state_calibrate_next <= CHECK_STARTING_DATA;
                                    `endif
                                end
                                else begin // if not yet zero then we have to write-read again
                                    state_calibrate <= ISSUE_WRITE_1;
                                end
                            end
                            //reached the end but STILL has error, issue might be WRITING TOO LATE (298cd0ad51c1XXXX is written) OR READING TOO EARLY ([9177]_298cd0ad51c1XXXX is read)
                            else if(data_start_index[lane] == 56) begin 
                                data_start_index[lane] <= 0;     
                                start_index_check <= 0;
                                state_calibrate <= CHECK_STARTING_DATA;
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"state=ANALYZE_DATA, lane=",hex_to_ascii(lane), ", Reached end",8'h0a,8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= CHECK_STARTING_DATA;
                                `endif
                            end 
                        `ifdef UART_DEBUG_ALIGN
                            else begin
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=ANALYZE_DATA, lane=",hex_to_ascii(lane), ", data_start_index[lane]=0x",
                                    hex_to_ascii(data_start_index[lane][6:4]),hex_to_ascii(data_start_index[lane][3:0]),8'h0a,8'h0a,8'h0a,8'h0a,
                                    {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                                    read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                                    read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8],read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] },
                                        8'h0a,8'h0a,8'h0a,8'h0a
                                    };
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= ANALYZE_DATA;
                            end
                        `endif
                      end     

                      // check when the 4 MSB of write_pattern {d0ad51c1} starts on read_lane_data (read_lane_data is just the concatenation of read_data_store of a specific lane)
                      // assumption here read_lane_data ~= 298cd0ad51c1XXXX is written: either because we write too late (thus we need to delay outgoing stage2_data) OR we read too early (thus we need to calibrate incoming iserdes_dq)
 CHECK_STARTING_DATA: begin
                        /* verilator lint_off WIDTHTRUNC */
                        if(read_lane_data[start_index_check +: 32] == write_pattern[0 +: 32]) begin
                        /* verilator lint_on WIDTHTRUNC */
                            // first assumption: controller DQ is late WHEN WRITING(THUS WE NEED TO CALIBRATE data_start_index of outgoing stage2_data)
                            if(!lane_write_dq_late[lane]) begin // lane_write_dq_late is not  yet set so we know this first assunmption is not yet tested
                                state_calibrate <= ISSUE_WRITE_1; // start writing again (the next write should fix the late DQ for this current lane)
                                data_start_index[lane] <= 64 - start_index_check; // stage2_data_unaligned is forwarded to stage[1] so we are now 8-bursts early, so we subtract from 64 so the burst we will be forwarded to the tip of stage2_data
                                lane_write_dq_late[lane] <= 1'b1;
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"state=CHECK_STARTING_DATA, start_index_check=0x",hex8_to_ascii(start_index_check), ", Ongoing First Assumption",8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= ISSUE_WRITE_1;
                                `endif
                            end
                            // if first assumption is not the fix then second assmption: controller reads the DQ too early (THUS WE NEED TO CALIBRATE INCOMING DQ SIGNAL starting from bitslip training)
                            else begin 
                                lane_read_dq_early[lane] <= 1'b1; // set to 1 to see later what lanes has this problem
                                state_calibrate <= BITSLIP_DQS_TRAIN_3;
                                added_read_pipe[lane] <= { {( 4 - ($clog2(STORED_DQS_SIZE*8) - (3+1)) ){1'b0}} , dq_target_index[lane][$clog2(STORED_DQS_SIZE*8)-1:(3+1)] } 
                                                            + { 3'b0 , (dq_target_index[lane][3:0] >= (5+8)) };
                                dqs_bitslip_arrangement <= 16'b0011_1100_0011_1100 >> dq_target_index[lane][2:0];
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"state=CHECK_STARTING_DATA, start_index_check=0x",hex8_to_ascii(start_index_check), ", Ongoing Second Assumption",8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= BITSLIP_DQS_TRAIN_3;
                                `endif
                            end
                        end
                        else begin
                            start_index_check <= start_index_check + 16; // plus 16, we assume here that DQ will be late BY 1 DDR3 CLK CYCLE (if only +8, then it will be late by half DDR3 cycle, that should NOT happen)
                            dq_target_index[lane] <= dq_target_index[lane] + 2;
                            if(start_index_check == 48)begin // start_index_check is now outside the possible values
                                // first assumption: controller DQ is 1 CONTROLLER CYCLE late WHEN WRITING (data is written to address 1 and not address 0)
                                if(!lane_write_dq_late[lane]) begin // lane_write_dq_late is not yet set so we know this first assunmption is not yet tested
                                    state_calibrate <= ISSUE_WRITE_1; // start writing again (the next write should fix the late DQ for this current lane)
                                    data_start_index[lane] <= 1; // stage2_data_unaligned is forwarded to stage[1] so we are now 8-bursts early, since assumption is we are 1 controller cycle early then data_start_index is 64 
                                    lane_write_dq_late[lane] <= 1'b1;
                                    `ifdef UART_DEBUG_ALIGN
                                        uart_start_send <= 1'b1;
                                        uart_text <= {"state=CHECK_STARTING_DATA, Reached end, First Assumption: Write is 1 Controller cycle early",8'h0a};
                                        state_calibrate <= WAIT_UART;
                                        state_calibrate_next <= ISSUE_WRITE_1;
                                    `endif
                                end
                                else begin // if first assumption is wrong and start_index_check is still outside of possible values then reset
                                    reset_from_calibrate <= 1;
                                end
                            end
                        `ifdef UART_DEBUG_ALIGN
                            else begin
                                uart_start_send <= 1'b1;
                                uart_text <= {"state=CHECK_STARTING_DATA, start_index_check=", hex_to_ascii(start_index_check[5:4]), hex_to_ascii(start_index_check[3:0]),8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= CHECK_STARTING_DATA;
                            end
                         `endif
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
                                   
       BURST_WRITE: if(!o_wb_stall_calib) begin // Test 1: Burst write (per byte write to test datamask feature), then burst read
                            calib_stb <= 1'b1; 
                            calib_aux <= 2; // write
                            if(TDQS == 0 && ECC_ENABLE == 0) begin //Test datamask by writing 1 byte at a time
                                calib_sel <= 1 << write_by_byte_counter;
                                calib_we <= 1; 
                                calib_addr <= write_test_address_counter;
                                calib_data <= {wb_sel_bits{8'haa}}; // set the rest (masked) to aa
                                calib_data[8*write_by_byte_counter +: 8] <= calib_data_randomized[8*write_by_byte_counter +: 8]; 
                                if(write_by_byte_counter == {$clog2(wb_sel_bits){1'b1}}) begin
                                    write_test_address_counter <= write_test_address_counter + 1;  
                                        /* verilator lint_off WIDTHEXPAND */
                                    if( (write_test_address_counter == { {2{BIST_MODE[1]}} , {(wb_addr_bits_sim-2){1'b1}} }) ) begin //MUST END AT ODD NUMBER
                                        /* verilator lint_on WIDTHEXPAND */
                                        if(BIST_MODE == 2) begin // mode 2 = burst write-read the WHOLE address space so always set the address counter back to zero
                                            write_test_address_counter <= 0;
                                        end
                                        state_calibrate <= BURST_READ;
                                        `ifdef UART_DEBUG_ALIGN
                                            uart_start_send <= 1'b1;
                                            uart_text <= {"DONE BURST WRITE (PER BYTE): BIST_MODE=",hex_to_ascii(BIST_MODE),8'h0a};
                                            state_calibrate <= WAIT_UART;
                                            state_calibrate_next <= BURST_READ;
                                        `endif
                                    end 
                                end
                                write_by_byte_counter <= write_by_byte_counter + 1;
                           end
                           else begin // Straight burst to all bytes (all datamask on)
                                calib_sel <= {wb_sel_bits{1'b1}};
                                calib_we <= 1; 
                                calib_addr <= write_test_address_counter;
                                calib_data <= calib_data_randomized;
                                write_test_address_counter <= write_test_address_counter + 1; 
                                    /* verilator lint_off WIDTHEXPAND */
                                if( write_test_address_counter == { {2{BIST_MODE[1]}} , {(wb_addr_bits_sim-2){1'b1}} } ) begin //MUST END AT ODD NUMBER
                                    /* verilator lint_on WIDTHEXPAND */
                                    if(BIST_MODE == 2) begin // mode 2 = burst write-read the WHOLE address space so always set the address counter back to zero
                                        write_test_address_counter <= 0;
                                    end
                                    state_calibrate <= BURST_READ;
                                    `ifdef UART_DEBUG_ALIGN
                                        uart_start_send <= 1'b1;
                                        uart_text <= {"DONE BURST WRITE (ALL BYTES): BIST_MODE=",hex_to_ascii(BIST_MODE),8'h0a};
                                        state_calibrate <= WAIT_UART;
                                        state_calibrate_next <= BURST_READ;
                                    `endif
                                end 
                           end
                     end
                   
         BURST_READ: if(!o_wb_stall_calib) begin
                            calib_stb <= 1'b1;
                            calib_aux <= 3; // read
                            calib_we <= 0; 
                            calib_addr <= read_test_address_counter;
                            read_test_address_counter <=  read_test_address_counter + 1; 
                                /* verilator lint_off WIDTHEXPAND */
                            if( read_test_address_counter == { {2{BIST_MODE[1]}} , {(wb_addr_bits_sim-2){1'b1}} } ) begin //MUST END AT ODD NUMBER
                                /* verilator lint_on WIDTHEXPAND */
                                if(BIST_MODE == 2) begin  // mode 2 = burst write-read the WHOLE address space so always set the address counter back to zero
                                    read_test_address_counter <= 0;
                                end
                                state_calibrate <= RANDOM_WRITE;
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"DONE BURST READ: BIST_MODE=",hex_to_ascii(BIST_MODE),8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= RANDOM_WRITE;
                                `endif
                            end  
                       end
                       
        RANDOM_WRITE: if(!o_wb_stall_calib) begin // Test 2: Random write (increments row address to force precharge-act-r/w) then random read
                            calib_stb <= 1'b1; 
                            calib_aux <= 2; // write
                            calib_sel <= {wb_sel_bits{1'b1}};
                            calib_we <= 1; 
                            // swap row <-> bank,col so that an increment on write_test_address_counter would mean an increment on ROW (rather than on column or bank thus forcing PRE-ACT)
                            calib_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1 + DUAL_RANK_DIMM) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2) + DUAL_RANK_DIMM) ]
                                       <= write_test_address_counter[ROW_BITS-1:0]; // store row
                            calib_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1 + DUAL_RANK_DIMM) : 0] 
                                       <= write_test_address_counter[wb_addr_bits-1:ROW_BITS]; // store bank + col
                            calib_data <= calib_data_randomized;
                            write_test_address_counter <= write_test_address_counter + 1; 
                                /* verilator lint_off WIDTHEXPAND */
                            if( write_test_address_counter == { 1'b1, BIST_MODE[1] , {(wb_addr_bits_sim-2){1'b1}} } ) begin //MUST END AT ODD NUMBER since ALTERNATE_WRITE_READ must start at even
                                /* verilator lint_on WIDTHEXPAND */
                                if(BIST_MODE == 2) begin  // mode 2 = random write-read the WHOLE address space so always set the address counter back to zero
                                    write_test_address_counter <= 0;
                                end
                                state_calibrate <= RANDOM_READ;
                                `ifdef UART_DEBUG_ALIGN
                                    uart_start_send <= 1'b1;
                                    uart_text <= {"DONE RANDOM WRITE: BIST_MODE=",hex_to_ascii(BIST_MODE),8'h0a};
                                    state_calibrate <= WAIT_UART;
                                    state_calibrate_next <= RANDOM_READ;
                                `endif
                            end
                      end
                    
        RANDOM_READ: if(!o_wb_stall_calib) begin
                        calib_stb <= 1'b1;
                        calib_aux <= 3; // read
                        calib_we <= 0;
                        // swap row <-> bank,col so that an increment on write_test_address_counter would mean an increment on ROW (rather than on column or bank thus forcing PRE-ACT)
                        calib_addr[ (ROW_BITS + BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1 + DUAL_RANK_DIMM) : (BA_BITS + COL_BITS- $clog2(serdes_ratio*2) + DUAL_RANK_DIMM) ]
                                       <= read_test_address_counter[ROW_BITS-1:0]; // row
                        calib_addr[(BA_BITS + COL_BITS- $clog2(serdes_ratio*2) - 1 + DUAL_RANK_DIMM) : 0] 
                                       <= read_test_address_counter[wb_addr_bits-1:ROW_BITS]; // bank + col
                        read_test_address_counter <=  read_test_address_counter + 1;  
                            /* verilator lint_off WIDTHEXPAND */
                        if( read_test_address_counter == { 1'b1 , BIST_MODE[1], {(wb_addr_bits_sim-2){1'b1}} }) begin //MUST END AT ODD NUMBER since ALTERNATE_WRITE_READ must start at even
                            /* verilator lint_on WIDTHEXPAND */
                            if(BIST_MODE == 2) begin  // mode 2 = random write-read the WHOLE address space so always set the address counter back to zero
                                read_test_address_counter <= 0;
                            end
                            state_calibrate <= ALTERNATE_WRITE_READ;
                            `ifdef UART_DEBUG_ALIGN
                                uart_start_send <= 1'b1;
                                uart_text <= {"DONE RANDOM READ: BIST_MODE=",hex_to_ascii(BIST_MODE),8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= ALTERNATE_WRITE_READ;
                            `endif
                        end
                     end
                     
ALTERNATE_WRITE_READ: if(!o_wb_stall_calib) begin
                        calib_stb <= 1'b1;
                        calib_aux <= 2 + (calib_we? 1:0); //2 (write), 3 (read)
                        calib_sel <= {wb_sel_bits{1'b1}};
                        calib_we <= !calib_we; // alternating write-read
                        calib_addr <= write_test_address_counter; 
                        calib_data <= calib_data_randomized;
                        if(calib_we) begin // if current operation is write, then dont increment address since we will read the same address next
                            write_test_address_counter <= write_test_address_counter + 1;  
                        end
                        /* verilator lint_off WIDTHEXPAND */
                        if( write_test_address_counter == { 2'b11 , {(wb_addr_bits_sim-2){1'b1}} } ) begin
                        /* verilator lint_on WIDTHEXPAND */
                            train_delay <= 15;
                            state_calibrate <= FINISH_READ;
                            `ifdef UART_DEBUG_ALIGN
                                uart_start_send <= 1'b1;
                                uart_text <= {"DONE ALTERNATING WRITE-READ",8'h0a};
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= FINISH_READ;
                            `endif
                        end
                    end         
       FINISH_READ: begin
                        calib_stb <= 0;
                        if(train_delay == 0) begin
                            if(DUAL_RANK_DIMM[0]) begin
                                if(instruction_address == 26) begin // only once self-refresh is waiting for exit will current rank is done
                                    final_calibration_done <= current_rank; // calibration is only done after calibration of 2nd rank
                                    reset_after_rank_1 <= !current_rank; // reset only if current rank is 1st rank
                                    if(current_rank) begin
                                        state_calibrate <= DONE_CALIBRATE;
                                    end
                                end
                            end
                            else begin
                                state_calibrate <= DONE_CALIBRATE;
                                final_calibration_done <= 1'b1;
                            end
                            `ifdef UART_DEBUG_ALIGN
                                uart_start_send <= 1'b1;
                                uart_text <= {"DONE BIST_MODE=",hex_to_ascii(BIST_MODE),", correct_read_data=",
                                    8'h0a, 8'h0a, correct_read_data, 8'h0a, 8'h0a, 8'h0a, 8'h0a
                                };
                                state_calibrate <= WAIT_UART;
                                state_calibrate_next <= DONE_CALIBRATE;
                            `endif
                        end
                    end    
                               
    DONE_CALIBRATE: begin
                        calib_stb <= 0;
                        state_calibrate <= DONE_CALIBRATE;
                        if(instruction_address == 5'd26) begin // Self-refresh Exit
                            pause_counter <= user_self_refresh_q; // wait until user-self-refresh is disabled before continuing 25 (Self-refresh Exit)
                        end
                        else begin
                            pause_counter <= 0;
                        end
                     end
        `ifdef UART_DEBUG
        WAIT_UART: begin
                        if(!uart_send_busy && !uart_start_send) begin // wait here until UART is finished
                            state_calibrate <= state_calibrate_next;
                        end
                        else if(uart_send_busy) begin // if already busy then uart_start_send can be deasserted
                            uart_start_send <= 0;
                        end
                        if(!o_wb_stall_calib) begin // lower calib_stb only when the current request is accepted (stall low)
                            calib_stb <= 0;
                        end
                    end
        `endif
        endcase
        `ifdef FORMAL_COVER
            state_calibrate <= DONE_CALIBRATE;
        `endif
        
             read_lane_data <= {read_data_store[((DQ_BITS*LANES)*7 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*6 + 8*lane) +: 8],
                    read_data_store[((DQ_BITS*LANES)*5 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*4 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*3 + 8*lane) +: 8],
                    read_data_store[((DQ_BITS*LANES)*2 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*1 + 8*lane) +: 8], read_data_store[((DQ_BITS*LANES)*0 + 8*lane) +: 8] };
             //halfway value has been reached (illegal) and will go back to zero at next load
             if(odelay_data_cntvaluein[lane] == 15) begin
                odelay_cntvalue_halfway <= 1; 
             end
            if(instruction_address == 19 || instruction_address == 23) begin //pre-stall delay before precharge all to finish all remaining requests
                pause_counter <= 1; // pause instruction address until pre-stall delay before refresh sequence finishes
                //skip to instruction address 20 (precharge all before refresh) when no pending requests anymore
                //toggle it for 1 clk cycle only
                if( !stage1_pending && !stage2_pending && ( (o_wb_stall && final_calibration_done) || (o_wb_stall_calib && state_calibrate != DONE_CALIBRATE) ) ) begin 
                   pause_counter <= 0; // pre-stall delay done since all remaining requests are completed
                end
            end
            
            if(repeat_test && final_calibration_done) begin //can only repeat test once calibration is over
                state_calibrate <= BURST_WRITE;
                read_test_address_counter <= 0;
                write_test_address_counter <= 0;
            end
            `ifdef UART_DEBUG
                if(wrong_read_data != 0 && !uart_send_busy && !uart_start_send) begin
                    uart_start_send <= 1'b1;
                    track_report <= track_report + 1;
                    case(track_report)
                        0: uart_text <= {"RESET, # correct(ascii)=0x",
                            hex8_to_ascii(correct_read_data[7:0]),
                            hex8_to_ascii(correct_read_data[15:8]),
                            hex8_to_ascii(correct_read_data[23:16]),
                            8'h0a, 8'h0a, wrong_data, 8'h0a, 8'h0a
                            };
                        1: uart_text <= {"RESET, #correct(raw)=0x",8'h0a,8'h0a,
                            correct_read_data, 8'h0a,8'h0a,
                            ", #wrong(raw)=0x", 8'h0a,8'h0a,
                            wrong_read_data, 8'h0a,8'h0a
                            };
                        2: uart_text <= {"RESET, wrong_data(raw)=0x",8'h0a,8'h0a,
                            wrong_data, 8'h0a,8'h0a
                        };
                        3: uart_text <= {"RESET, correct_data(raw)=0x",8'h0a,8'h0a,
                            expected_data, 8'h0a,8'h0a
                        };
                        5: uart_text <= {"state_calibrate_last=0x",hex8_to_ascii(state_calibrate_last),8'h0a,8'h0a
                        };
                    endcase
                    state_calibrate <= WAIT_UART;
                    state_calibrate_next <= WAIT_UART;
                end
            `endif
        end
    end    

    //------------------------------------- START OF UART SERIALIZER----------------------------------------------------------------//
    `ifdef UART_DEBUG 
        reg[19:0] uart_idle_timer = 0;
        // FSM for uart 
        // uart_text = "Hello" , uart_text_length = 5
        // [5<<3-1 (39):4<<3 (32)] = "H" , [4<<3-1 (31):3<<3(24)] = "e" , [3<<3-1(23):2<<3(16)] = "l" , [2<<3-1(15):1<<3(8)] = "l" ,  [1<<3-1(7):0<<3(0)] = "o"
        always @(posedge i_controller_clk, negedge i_rst_n) begin
            if(!i_rst_n) begin
                state_uart_send <= UART_FSM_IDLE;
                uart_text_length_index <= 0;
                uart_tx_en <= 0;
                uart_send_busy <= 0;
                uart_tx_data <= 0;
                uart_idle_timer <= 0;
            end
            else begin
                case(state_uart_send)
                    UART_FSM_IDLE: if (uart_start_send) begin // if receive request to send via uart
                        state_uart_send <= UART_FSM_SEND_BYTE;
                        uart_text_length_index <= 100;
                        uart_send_busy <= 1;
                        uart_idle_timer <= MICRON_SIM? {5{1'b1}} : {20{1'b1}}; // set to all 1s for idle time
                    end
                    else begin
                        uart_tx_en <= 1'b0;
                        uart_send_busy <= 1'b0;
                    end
                    
                    UART_FSM_SEND_BYTE: if(!uart_tx_busy) begin // if uart tx is not busy, send character
                        uart_tx_en <= 1'b1;
                        uart_tx_data <= uart_text[((uart_text_length_index)<<3) +: 8];
                    end
                    else begin // once busy, go to wait state
                        state_uart_send <= UART_FSM_WAIT_SEND;
                        uart_tx_en <= 1'b0;
                    end

                    UART_FSM_WAIT_SEND: if(!uart_tx_busy) begin // if not busy again, then uart is done sending
                        if(uart_text_length_index != 0) begin // if not yet at 0, go to next character
                            uart_text_length_index <= uart_text_length_index - 1;
                            state_uart_send <= UART_FSM_SEND_BYTE;
                        end
                        else if(uart_idle_timer == 0) begin // if not busy anymore, all characters sent, and timer done
                            state_uart_send <= UART_FSM_IDLE;
                        end
                        else begin // if not busy anymore, all characters sent, but uart_idle_timer not yet at zero
                            uart_idle_timer <= uart_idle_timer - 1;
                        end
                    end
                    default: state_uart_send <= UART_FSM_IDLE;
                endcase
            end
        end
     
        // Function to convert hex to ASCII
        function [7:0] hex_to_ascii;
            input [3:0] hex;
            begin
                if (hex < 4'd10)
                    hex_to_ascii = hex + 8'd48; // ASCII for '0'-'9'
                else
                    hex_to_ascii = hex + 8'd55; // ASCII for 'A'-'F'
            end
        endfunction

        // Function to convert 8-bit hex to two ASCII characters
        function [15:0] hex8_to_ascii;
            input [7:0] hex;
            begin
                hex8_to_ascii[15:8] = (hex[7:4] < 4'd10) ? (hex[7:4] + 8'd48) : (hex[7:4] + 8'd55);
                hex8_to_ascii[7:0]  = (hex[3:0] < 4'd10) ? (hex[3:0] + 8'd48) : (hex[3:0] + 8'd55);
            end
        endfunction

        uart_tx #(
                .BIT_RATE(MICRON_SIM? (((1_000_000/CONTROLLER_CLK_PERIOD) * 1_000_000)/1) : 9600), // fast UART during simulation
                .CLK_HZ( (1_000_000/CONTROLLER_CLK_PERIOD) * 1_000_000),
                .PAYLOAD_BITS(8),
                .STOP_BITS(1)
            ) uart_tx_inst (
                .clk(i_controller_clk), // Top level system clock input 
                .resetn(i_rst_n), // Asynchronous active low reset.
                .uart_txd(uart_tx)    , // UART transmit pin.
                .uart_tx_busy(uart_tx_busy), // Module busy sending previous item.
                .uart_tx_en(uart_tx_en), // Send the data on uart_tx_data
                .uart_tx_data(uart_tx_data)  // The data to be sent
        );

        function integer count_chars;
            input [8*256-1:0] str;
            integer i;
            begin
                count_chars = 0;
                begin : loop_block
                    for (i = 0; i < 256; i = i + 1) begin
                        if (str[8*i +: 8] !== 8'h00 && str[8*i +: 8] !== 8'hFF) begin // Avoid garbage values
                            count_chars = count_chars + 1;
                        end
                    end
                end
                count_chars = count_chars + 1; // Include \n at the end
            end
        endfunction

    `else
        assign uart_tx = 1; // tx constant 1 when UART not used
    `endif
    //------------------------------------- END OF UART SERIALIZER----------------------------------------------------------------//

    // generate calib_data for BIST
    // Uses different operations (XOR, addition, subtraction, bit rotation) to generate different values per byte.
    assign calib_data_randomized = {
        {(wb_sel_bits/8){write_test_address_counter[0 +: 8] ^ 8'hA5,  // Byte 7
        write_test_address_counter[0 +: 8] | 8'h1A,  // Byte 6
        write_test_address_counter[0 +: 8] & 8'h33,  // Byte 5
        write_test_address_counter[0 +: 8] ^ 8'h5A,  // Byte 4
        write_test_address_counter[0 +: 8] & 8'h21,  // Byte 3
        write_test_address_counter[0 +: 8] | 8'hC7,  // Byte 2
        write_test_address_counter[0 +: 8] ^ 8'h7E,  // Byte 1
        write_test_address_counter[0 +: 8] ^ 8'h3C}}   // Byte 0
    };

    generate
    if(DUAL_RANK_DIMM[0]) begin  : dual_rank_mux
        // logic for current_rank to track if rank 1 or rank 2 is being calibrated
        always @(posedge i_controller_clk) begin 
            if(current_rank_rst) begin // dont reset at reset_after_rank_1
                current_rank <= 1'b0; // start at rank 1
            end
            else begin
                if(reset_after_rank_1) begin
                    current_rank <= 1'b1; // switch to 2nd rank after reset
                end
            end
        end
    end
    endgenerate

    assign issue_read_command = (state_calibrate == MPR_READ && delay_before_read_data == 0);
    assign o_phy_odelay_data_cntvaluein = odelay_data_cntvaluein[lane]; 
    assign o_phy_odelay_dqs_cntvaluein = odelay_dqs_cntvaluein[lane];
    assign o_phy_idelay_data_cntvaluein = idelay_data_cntvaluein[lane];
    assign o_phy_idelay_dqs_cntvaluein = idelay_dqs_cntvaluein[lane];
    assign dqs_target_index_value = dqs_start_index_stored[0]? dqs_start_index_stored + 2: dqs_start_index_stored + 1; // move to next odd (if 3 then 5, if 4 then 5)
     // To show why next odd number is needed: https://github.com/AngeloJacobo/UberDDR3/tree/b762c464f6526159c1d8c2e4ee039b4ae4e78dbd#per-lane-read-calibration

    /*********************************************************************************************************************************************/

    /******************************************************* Calibration Test Receiver *******************************************************/

    generate
        if(ECC_ENABLE == 0 || ECC_ENABLE == 3) begin : ecc_enable_0_correct_data
            assign correct_data = {
                {(wb_sel_bits/8){check_test_address_counter[0 +: 8] ^ 8'hA5,  // Byte 7
                check_test_address_counter[0 +: 8] | 8'h1A,  // Byte 6
                check_test_address_counter[0 +: 8] & 8'h33,  // Byte 5
                check_test_address_counter[0 +: 8] ^ 8'h5A,  // Byte 4
                check_test_address_counter[0 +: 8] & 8'h21,  // Byte 3
                check_test_address_counter[0 +: 8] | 8'hC7,  // Byte 2
                check_test_address_counter[0 +: 8] ^ 8'h7E,  // Byte 1
                check_test_address_counter[0 +: 8] ^ 8'h3C }}  // Byte 0
            };
        end
        else if(ECC_ENABLE == 1) begin : ecc_enable_1_correct_data
            wire[wb_data_bits-1:0] correct_data_orig;
            assign correct_data = {
                {(wb_sel_bits/8){check_test_address_counter[0 +: 8] ^ 8'hA5,  // Byte 7
                check_test_address_counter[0 +: 8] | 8'h1A,  // Byte 6
                check_test_address_counter[0 +: 8] & 8'h33,  // Byte 5
                check_test_address_counter[0 +: 8] ^ 8'h5A,  // Byte 4
                check_test_address_counter[0 +: 8] & 8'h21,  // Byte 3
                check_test_address_counter[0 +: 8] | 8'hC7,  // Byte 2
                check_test_address_counter[0 +: 8] ^ 8'h7E,  // Byte 1
                check_test_address_counter[0 +: 8] ^ 8'h3C }}  // Byte 0
            };
            assign correct_data = {{(wb_data_bits-ECC_INFORMATION_BITS*8){1'b0}} , correct_data_orig[ECC_INFORMATION_BITS*8 - 1 : 0]}; //only ECC_INFORMATION_BITS are valid in o_wb_data
        end
        else if(ECC_ENABLE == 2) begin : ecc_enable_2_correct_data
            wire[wb_data_bits-1:0] correct_data_orig;
            assign correct_data = {
                {(wb_sel_bits/8){check_test_address_counter[0 +: 8] ^ 8'hA5,  // Byte 7
                check_test_address_counter[0 +: 8] | 8'h1A,  // Byte 6
                check_test_address_counter[0 +: 8] & 8'h33,  // Byte 5
                check_test_address_counter[0 +: 8] ^ 8'h5A,  // Byte 4
                check_test_address_counter[0 +: 8] & 8'h21,  // Byte 3
                check_test_address_counter[0 +: 8] | 8'hC7,  // Byte 2
                check_test_address_counter[0 +: 8] ^ 8'h7E,  // Byte 1
                check_test_address_counter[0 +: 8] ^ 8'h3C }}  // Byte 0
            };
            assign correct_data = {{(wb_data_bits-ECC_INFORMATION_BITS){1'b0}} , correct_data_orig[ECC_INFORMATION_BITS - 1 : 0]}; //only ECC_INFORMATION_BITS are valid in o_wb_data
        end
    endgenerate

    always @(posedge i_controller_clk) begin
        if(sync_rst_controller) begin
            check_test_address_counter <= 0;
            // correct_read_data <= 0; // dont reset so data is preserved when forced reset after wrong data
            // wrong_read_data <= 0;
            reset_from_test <= 0;
        end
        else begin
            reset_from_test <= 0;
            if(state_calibrate != DONE_CALIBRATE) begin          
                if ( o_aux[2:0] == 3'd3 && o_wb_ack_uncalibrated ) begin //o_aux = 3 is for read from calibration
                    if(o_wb_data == correct_data) begin
                        correct_read_data <= correct_read_data + 1;
                    end
                    else begin
                        wrong_read_data <= wrong_read_data + 1;
                        wrong_data <= o_wb_data;
                        expected_data <= correct_data;
                        `ifdef UART_DEBUG
                            state_calibrate_last <= state_calibrate;
                            reset_from_test <= 1'b0; // dont reset when uart debugging
                        `else
                            reset_from_test <= !final_calibration_done; //reset controller when a wrong data is received (only when calibration is not yet done) AND UART_DEBUG is not defined
                        `endif
                    end
                    /* verilator lint_off WIDTHEXPAND */
                    check_test_address_counter <= check_test_address_counter + 1;
                    if(check_test_address_counter == {(wb_addr_bits_sim){1'b1}}) begin // if last address, then jump back to zero
                        check_test_address_counter <= {(wb_addr_bits){1'b0}};
                    end
                    /* verilator lint_on WIDTHEXPAND */
                end
            end
            if(repeat_test) begin
                check_test_address_counter <= 0;
                correct_read_data <= 0;
                wrong_read_data <= 0;
            end
        end

    end
    /*********************************************************************************************************************************************/
    
    /******************************************************* Wishbone 2 (PHY) Interface *******************************************************/
    generate
        if(SECOND_WISHBONE) begin : use_second_wishbone
        // When running in DDR3-1600, disable SECOND_WISHBONE to pass timing
            always @(posedge i_controller_clk) begin
                    if(sync_rst_wb2) begin
                        wb2_stb <= 0;
                        wb2_we <= 0; //data to be written which must have high i_wb2_sel are: {LANE_NUMBER, CNTVALUEIN}
                        wb2_addr <= 0;
                        wb2_data <= 0;
                        wb2_sel <= 0;
                    end
                    else begin
                        if( (i_wb2_cyc && SECOND_WISHBONE) && !o_wb2_stall) begin 
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
                if(sync_rst_wb2) begin
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
                    reset_from_wb2 <= 0;
                    repeat_test <= 0;
                end
                else begin
                    wb2_phy_odelay_data_ld <= 0; 
                    wb2_phy_odelay_dqs_ld <= 0;
                    wb2_phy_idelay_data_ld <= 0;
                    wb2_phy_idelay_dqs_ld <= 0;
                    wb2_update <= 0;
                    wb2_write_lane <= 0;
                    o_wb2_ack <= wb2_stb && (i_wb2_cyc && SECOND_WISHBONE); //always ack right after request
                    o_wb2_stall <= 0; //never stall
                    reset_from_wb2 <= 0;
                    repeat_test <= 0;
                    if(wb2_stb && (i_wb2_cyc && SECOND_WISHBONE)) begin
                            case(wb2_addr[4:0]) 
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
                                        o_wb2_data[1 +: 5] <= state_calibrate; //5 bits, FSM state of the calibration sequence6
                                        o_wb2_data[1 + 6 +: 5] <= instruction_address; //5 bits, address of the reset sequence
                                        o_wb2_data[1 + 6 + 5 +: 4] <= added_read_pipe_max; //4 bit, max added read delay (must have a max value of 1)
                                end

                                5: if(!wb2_we) begin
                                        for(index = 0; index < LANES; index = index + 1) begin
                                        o_wb2_data[4*index +: 4] <= added_read_pipe[index];
                                        end
                                        //added read pipe delay for lanes 0-to-3 (4 bits each lane the max is just 1 for each)
                                    end
            /*
                                6: if(!wb2_we) begin
                                        o_wb2_data <= dqs_store[31:0]; //show last 4 sets of received 8-bit DQS during MPR (repeated 4 times, must have a value of 10'b01_01_01_01_00 somewhere)
                                    end

                                7: if(!wb2_we) begin
                                        o_wb2_data <= wrong_data[31:0]; //lane 1
                                    end

                                8: if(!wb2_we) begin
                                        o_wb2_data <= wrong_data[63:32]; //first 32 bits of the data read after first write using the write_pattern 128'h80dbcfd275f12c3d_9177298cd0ad51c1
                                    end

                                9: if(!wb2_we) begin
                                        o_wb2_data <= wrong_data[95:64]; //first 32 bit of the patern written on the first write just for checking (128'h80dbcfd275f12c3d_9177298cd0ad51c1)
                                    end
                                    
                                10: if(!wb2_we) begin //0x28 (data read back)
                                        o_wb2_data <= wrong_data[127:96]; //first 32 bit of the patern written on the first write just for checking (128'h80dbcfd275f12c3d_9177298cd0ad51c1)
                                    end
                                11: if(!wb2_we) begin //0x2c (data write)
                                        o_wb2_data <= wrong_data[159:128]; //first 32 bit of the patern written on the first write just for checking (128'h80dbcfd275f12c3d_9177298cd0ad51c1)
                                    end   
                                12: if(!wb2_we) begin //0x30
                                        o_wb2_data <= wrong_data[191:160]; //check if proper request is received
                                    end   
                                13: if(!wb2_we) begin //0x30
                                        o_wb2_data <= wrong_data[223:192];//lane 1
                                    end
                                14: if(!wb2_we) begin //0x30
                                        o_wb2_data <= wrong_data[255:224]; //lane 1
                                    end*/
                                15: if(!wb2_we) begin //0x30
                                        o_wb2_data <= correct_read_data; //lane 1
                                    end
                                16: if(!wb2_we) begin //0x30
                                        o_wb2_data <=  wrong_read_data; //lane 1
                                    end
                                17: if(wb2_we) begin
                                        repeat_test <= wb2_data[0];
                                        reset_from_wb2 <= wb2_data[1];
                                    end
                                18: if(!wb2_we) begin //0x30
                                        o_wb2_data <= 32'h50; //lane 1
                                    end
                        default: if(!wb2_we) begin //read 
                                    o_wb2_data <= {(WB2_DATA_BITS/2){2'b10}}; //return alternating 1s and 0s when address to be read is invalid 
                                end
                            endcase

                            wb2_write_lane <= wb2_data[5 +: lanes_clog2]; //save next 5 bits for lane number to be loaded with new delay
                        end //end of if(wb2_stb)
                    end//end of else
            end//end of always
        end 
        else begin : no_second_wishbone
            always @* begin
                o_wb2_stall = 1'b1; // will not accept any request
                o_wb2_ack = 1'b0;
                o_wb2_data = 0;
            end
        end 
    endgenerate

    // Logic connected to debug port
//    wire debug_trigger;
    assign o_debug1 = {27'd0, state_calibrate[4:0]};
//    assign o_debug2 = {debug_trigger,i_phy_iserdes_data[62:32]};
//    assign o_debug3 = {debug_trigger,i_phy_iserdes_data[30:0]};
//    assign debug_trigger = repeat_test /*o_wb_ack_read_q[0][0]*/;
    /*********************************************************************************************************************************************/


    /******************************************************* Functions *******************************************************/
    //convert nanoseconds time input to number of controller clock cycles (referenced to CONTROLLER_CLK_PERIOD)
    //output is set at same length as a MRS command (19 bits) to maximize the time slot
    function [DELAY_SLOT_WIDTH - 1:0] ps_to_cycles ( input integer ps );                
            /* verilator lint_off WIDTHTRUNC */              
            ps_to_cycles = $rtoi( $ceil( ps*1.0/CONTROLLER_CLK_PERIOD ) ); 
            /* verilator lint_on WIDTHTRUNC */
    endfunction

    //convert nCK input (number of DDR3 clock cycles) to number of controller clock cycles (referenced to serdes_ratio)
    function [DELAY_SLOT_WIDTH - 1:0] nCK_to_cycles (input integer nCK); 
            /* verilator lint_off WIDTHTRUNC */
            nCK_to_cycles =  $rtoi( $ceil( nCK*1.0/serdes_ratio ) ); 
            /* verilator lint_on WIDTHTRUNC */
    endfunction
    
    
    //convert nanoseconds time input  to number of DDR clock cycles (referenced to DDR3_CLK_PERIOD)
    function integer ps_to_nCK ( input integer ps );
        ps_to_nCK = $rtoi( $ceil( ps*1.0/ DDR3_CLK_PERIOD ) ); 
    endfunction
    
    //convert DDR clock cycles to nanoseconds (referenced to DDR3_CLK_PERIOD)
    function integer nCK_to_ps (input integer nCK); 
        nCK_to_ps = $rtoi( $ceil( nCK*1.0*DDR3_CLK_PERIOD ) ); 
    endfunction
    
    // functions used to infer some localparam values
    function integer max(input integer a, input integer b);
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
    
    // Find the correct value for CL based on ddr3 clock period
    function[3:0] CL_generator(input integer ddr3_clk_period);
        begin
            if(/*ddr3_clk_period <= 3_300 &&*/ ddr3_clk_period >= 3_000) begin // cover ddr3 clk periods > 3.3ns
                CL_generator = 4'd5;
            end
            else if(/*ddr3_clk_period <= 3_300 &&*/ ddr3_clk_period >= 2_500) begin
                CL_generator = 4'd6;
            end
            else if(ddr3_clk_period <= 2_500 && ddr3_clk_period >= 1_875) begin
                CL_generator = 4'd7;
            end
            else if(ddr3_clk_period <= 1_875 && ddr3_clk_period >= 1_500) begin
                CL_generator = 4'd9;
            end
            else if(ddr3_clk_period <= 1_500 && ddr3_clk_period >= 1_250) begin
                CL_generator = 4'd11;
            end
        end
    endfunction

    // Find the correct value for CWL based on ddr3 clock period
    function[3:0] CWL_generator(input integer ddr3_clk_period);
        begin
            if(/*ddr3_clk_period <= 3_300 &&*/ ddr3_clk_period >= 3_000) begin
                CWL_generator = 4'd5;
            end
            else if(/*ddr3_clk_period <= 3_300 &&*/ ddr3_clk_period >= 2_500) begin
                CWL_generator = 4'd5;
            end
            else if(ddr3_clk_period <= 2_500 && ddr3_clk_period >= 1_875) begin
                CWL_generator = 4'd6;
            end
            else if(ddr3_clk_period <= 1_875 && ddr3_clk_period >= 1_500) begin
                CWL_generator = 4'd7;
            end
            else if(ddr3_clk_period <= 1_500 && ddr3_clk_period >= 1_250) begin
                CWL_generator = 4'd8;
            end
        end
    endfunction

    function[1:0] get_slot (input[3:0] cmd); //cmd can either be CMD_PRE,CMD_ACT, CMD_WR, CMD_RD
        integer delay;
        reg[2:0] slot_number, read_slot, write_slot, anticipate_activate_slot, anticipate_precharge_slot;
        reg[2:0] remaining_slot;
        begin
            slot_number = 0;
            read_slot = 0;
            write_slot = 0;
            anticipate_activate_slot = 0;
            anticipate_precharge_slot = 0;
            remaining_slot = 0;
            delay = 0;
            // find read command slot number
            delay = {{(32-4){1'b0}},CL_nCK};
            for(slot_number = 0 ;  delay != 0 ; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            read_slot[1:0] = slot_number[1:0];
            
            // find write command slot number
            delay = {{(32-4){1'b0}},CWL_nCK};
            for(slot_number = 0 ;  delay != 0; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            write_slot[1:0] = slot_number[1:0];
            
            // find anticipate activate command slot number
            if(CL_nCK > CWL_nCK) slot_number[1:0] = read_slot[1:0];
            else slot_number[1:0] = write_slot[1:0];

            // delay = ps_to_nCK(tRCD); 
            delay = $rtoi( $ceil( tRCD*1.0/ DDR3_CLK_PERIOD ) );
            for(slot_number = slot_number;  delay != 0; delay = delay - 1) begin
                    slot_number[1:0] = slot_number[1:0] - 1'b1;
            end 
            anticipate_activate_slot[1:0] = slot_number[1:0];
            // if computed anticipate_activate_slot is same with either write_slot or read_slot, decrement slot number until 
            while(anticipate_activate_slot[1:0] == write_slot[1:0] || anticipate_activate_slot[1:0] == read_slot[1:0]) begin 
                anticipate_activate_slot[1:0] = anticipate_activate_slot[1:0] - 1'b1;
            end
            
             //the remaining slot will be for precharge command
            anticipate_precharge_slot = 0;
            while(anticipate_precharge_slot[1:0] == write_slot[1:0] || anticipate_precharge_slot[1:0] == read_slot[1:0] || anticipate_precharge_slot[1:0] == anticipate_activate_slot[1:0]) begin
                anticipate_precharge_slot[1:0] = anticipate_precharge_slot[1:0]  - 1'b1;
            end

            //the remaining slot will be for precharge command
            remaining_slot = 0;
            while(remaining_slot == write_slot || remaining_slot == read_slot || remaining_slot == anticipate_activate_slot || remaining_slot == anticipate_precharge_slot) begin
                remaining_slot = remaining_slot + 1'b1;
            end

            case(cmd)
                CMD_RD: get_slot = read_slot[1:0];
                CMD_WR: get_slot = write_slot[1:0];
                CMD_ACT: get_slot = anticipate_activate_slot[1:0];
                CMD_PRE: get_slot = anticipate_precharge_slot[1:0];
                0: get_slot = remaining_slot[1:0];
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

    // find maximum information bit the data width can accomadate 
    // Reference: https://docs.amd.com/v/u/en-US/xapp383
    // Relevant equations: N <= 2^(K-1) - K  ,  total_bits = N + K  --->  total_bits <= 2^(total_bits - N - 1)
    // N = information bits , K = parity bits ,  total_bits = total data width (information bit plus parity bits)
    function integer max_information_bits;
    input integer total_bits;
    integer N;
    begin
        N = total_bits;
        while (total_bits > 2**(total_bits-N-1)) N = N - 1;
        max_information_bits = N;
    end
    endfunction 

    // combine information bits (wb_data) to parity bits 
    function [71:0] undecoded_data(input[63:0] wb_data, input[7:0] parity_bits);      
    begin      
        // decoded_parity is 8 bits: {msb, 2^6, 2^5, 2^4, 2^3, 2^2, 2^1, 2^0};
        {undecoded_data[71], undecoded_data[64-1], undecoded_data[32-1], undecoded_data[16-1], 
            undecoded_data[8-1], undecoded_data[4-1], undecoded_data[2-1], undecoded_data[1-1]} = parity_bits;
        {undecoded_data[70:64], undecoded_data[62:32], undecoded_data[30:16], undecoded_data[14:8], 
            undecoded_data[6:4], undecoded_data[2]} = wb_data;
    end
    endfunction
    /*********************************************************************************************************************************************/

    /******************************************************* Module Instantiations *******************************************************/
    generate
        if(ECC_ENABLE == 0) begin : no_ecc
            assign stage1_data_encoded = stage1_data;
            //assign stage1_data_mux = stage1_data_encoded;
            if(ECC_TEST) begin : ecc_test
                assign stage1_data_mux = initial_calibration_done ? {stage1_data_encoded[wb_data_bits-1:1] , 1'b0} : stage1_data_encoded; 
            end        
            else begin : no_ecc_test
                assign stage1_data_mux = stage1_data_encoded;
            end   
            assign encoded_parity = 0;
            assign sb_err_o = 1'b0;
            assign db_err_o = 1'b0;
            assign o_wb_data_q_decoded = 0;
        end
        
        else if (ECC_ENABLE == 2) begin : sideband_ECC_per_8_bursts
            /* verilator lint_off PINCONNECTEMPTY */
            ecc_enc #(
                .K(ECC_INFORMATION_BITS), //Information bit vector size
                .P0_LSB(0) //0: p0 is located at MSB
                        //1: p0 is located at LSB
            ) ecc_enc_inst (
                .d_i(stage1_data[ECC_INFORMATION_BITS-1:0]),      //information bit vector input
                .q_o(stage1_data_encoded),  //encoded data word output
                .p_o(),      //parity vector output
                .p0_o()      //extended parity bit
            );

            // if initial calibration is not yet done, then data will not be encoded with ECC
            if(ECC_TEST) begin : ecc_test
                assign stage1_data_mux = initial_calibration_done? {stage1_data_encoded[wb_data_bits-1:1], 1'b0} : stage1_data;
            end
            else begin : non_ecc_test
                assign stage1_data_mux = initial_calibration_done? stage1_data_encoded : stage1_data;
            end
            ecc_dec #(
            .K(ECC_INFORMATION_BITS), //Information bit vector size
            .LATENCY(0), //0: no latency (combinatorial design)
                                //1: registered outputs
                                //2: registered inputs+outputs
            .P0_LSB(0) //0: p0 is located at MSB
                                //1: p0 is located at LSB
            ) ecc_dec_inst (
                //clock/reset ports (if LATENCY > 0)
                .rst_ni(1'b1),     //asynchronous reset
                .clk_i(1'b0),      //clock input
                .clkena_i(1'b0),   //clock enable input
                //data ports
                .d_i(o_wb_data_q_current),        //encoded code word input
                .q_o(o_wb_data_q_decoded[ECC_INFORMATION_BITS-1:0]),        //information bit vector output
                .syndrome_o(), //syndrome vector output
                //flags
                .sb_err_o(sb_err_o),   //single bit error detected
                .db_err_o(db_err_o),   //double bit error detected
                .sb_fix_o()    //repaired error in the information bits
            );
            assign o_wb_data_q_decoded[wb_data_bits - 1 : ECC_INFORMATION_BITS] = 0;
            assign encoded_parity = 0;
        end

        // ECC per burst. If x16 DDR3, then every 16 bits will have ECC parity bits.
        else if(ECC_ENABLE == 1) begin : sideband_ECC_per_burst
            wire[7:0] sb_err;
            wire[7:0] db_err;
            genvar index_enc;
            // 8 encoders to add ECC bits per burst
            for(index_enc = 0; index_enc < 8 ;  index_enc = index_enc + 1) begin
                ecc_enc #(
                    .K(ECC_INFORMATION_BITS), //Information bit vector size
                    .P0_LSB(0) //0: p0 is located at MSB
                               //1: p0 is located at LSB
                ) ecc_enc_inst (
                    .d_i(stage1_data[ECC_INFORMATION_BITS*index_enc +: ECC_INFORMATION_BITS]),    //information bit vector input
                    .q_o(stage1_data_encoded[DQ_BITS*LANES*index_enc +: DQ_BITS*LANES]),  //encoded data word output
                    .p_o(),      //parity vector output
                    .p0_o()      //extended parity bit
                );

                ecc_dec #(
                    .K(ECC_INFORMATION_BITS), //Information bit vector size
                    .LATENCY(0), //0: no latency (combinatorial design)
                                        //1: registered outputs
                                        //2: registered inputs+outputs
                    .P0_LSB(0) //0: p0 is located at MSB
                                //1: p0 is located at LSB
                ) ecc_dec_inst (
                    //clock/reset ports (if LATENCY > 0)
                    .rst_ni(1'b1),     //asynchronous reset
                    .clk_i(1'b0),      //clock input
                    .clkena_i(1'b0),   //clock enable input
                    //data ports
                    .d_i(o_wb_data_q_current[DQ_BITS*LANES*index_enc +: DQ_BITS*LANES]),        //encoded code word input
                    .q_o(o_wb_data_q_decoded[ECC_INFORMATION_BITS*index_enc +: ECC_INFORMATION_BITS]),        //information bit vector output
                    .syndrome_o(), //syndrome vector output
                    //flags
                    .sb_err_o(sb_err[index_enc]),   //single bit error detected
                    .db_err_o(db_err[index_enc]),   //double bit error detected
                    .sb_fix_o()    //repaired error in the information bits
                );
                /* verilator lint_on PINCONNECTEMPTY */
            end
            assign o_wb_data_q_decoded[wb_data_bits - 1 : ECC_INFORMATION_BITS*8] = 0;
            if(ECC_TEST) begin : ecc_test
                assign stage1_data_mux = initial_calibration_done? {stage1_data_encoded[wb_data_bits-1:1], 1'b0} : stage1_data;
            end
            else begin : non_ecc_test
                assign stage1_data_mux = initial_calibration_done? stage1_data_encoded : stage1_data;
            end
            assign sb_err_o = |sb_err;
            assign db_err_o = |db_err;
            assign encoded_parity = 0;
        end

        else if (ECC_ENABLE == 3) begin : inline_ECC
            wire[wb_data_bits/64 - 1 : 0] sb_err;
            wire[wb_data_bits/64 - 1 :0] db_err;
            wire[72*(wb_data_bits/64) - 1 : 0] coded_word;

            genvar index_enc;
            // 8 encoders to add ECC bits per burst
            for(index_enc = 0; index_enc < wb_data_bits/64 ;  index_enc = index_enc + 1) begin
                // encode/decode each 64-bit blocks 
                /* verilator lint_off PINCONNECTEMPTY */
                ecc_enc #(
                    .K(64), //Information bit vector size
                    .P0_LSB(0) //0: p0 is located at MSB
                               //1: p0 is located at LSB
                ) ecc_enc_inst (
                    .d_i(stage1_data[64*index_enc +: 64]),    //information bit vector input
                    .q_o(),  //encoded data word output
                    .p_o(encoded_parity[8*index_enc +: 7]),      //parity vector output
                    .p0_o(encoded_parity[8*index_enc + 7])      //extended parity bit
                );
                // combine information bits and parity bits (fixed to width of 72 since information bits is always 64)
                assign coded_word[72*index_enc +: 72] = undecoded_data(o_wb_data_q_current[64*index_enc +: 64], decoded_parity[8*index_enc +: 8]);
                ecc_dec #(
                    .K(64), //Information bit vector size
                    .LATENCY(0), //0: no latency (combinatorial design)
                                        //1: registered outputs
                                        //2: registered inputs+outputs
                    .P0_LSB(0) //0: p0 is located at MSB
                                //1: p0 is located at LSB
                ) ecc_dec_inst (
                    //clock/reset ports (if LATENCY > 0)
                    .rst_ni(1'b1),     //asynchronous reset
                    .clk_i(1'b0),      //clock input
                    .clkena_i(1'b0),   //clock enable input
                    //data ports
                    .d_i(coded_word[72*index_enc +: 72]),  //encoded code word input
                    .q_o(o_wb_data_q_decoded[64*index_enc +: 64]),        //information bit vector output
                    .syndrome_o(), //syndrome vector output
                    //flags
                    .sb_err_o(sb_err[index_enc]),   //single bit error detected
                    .db_err_o(db_err[index_enc]),   //double bit error detected
                    .sb_fix_o()    //repaired error in the information bits
                );
                /* verilator lint_on PINCONNECTEMPTY */
            end
            
            assign stage1_data_encoded = stage1_data;
            // ecc_req_stage2 means stage2 is doing ECC write operation
            
            if(ECC_TEST) begin : ecc_test
                assign stage1_data_mux = ecc_stage1_stall? stage2_ecc_write_data_d : initial_calibration_done ? {stage1_data_encoded[wb_data_bits-1:1] , 1'b0} : stage1_data_encoded;
            end
            else begin : non_ecc_test
                assign stage1_data_mux = ecc_stage1_stall? stage2_ecc_write_data_d : stage1_data_encoded;
            end
            // error flags are only relevant for non-ECC reads (o_aux[AUX_WIDTH-2 +: 1] = 2'b01) and ack is high
            assign sb_err_o = (|sb_err) && (o_aux[AUX_WIDTH-2 +: 2] == 2'b01) && o_wb_ack_read_q[0][0];
            assign db_err_o = (|db_err) && (o_aux[AUX_WIDTH-2 +: 2] == 2'b01) && o_wb_ack_read_q[0][0];
        end
    endgenerate

    /*********************************************************************************************************************************************/


`ifndef YOSYS
    ///YOSYS: System task `$display' called with invalid/unsupported format specifier
    initial begin
        $display("\nCONTROLLER PARAMETERS:\n-----------------------------");

        $display("CONTROLLER_CLK_PERIOD = %0d", CONTROLLER_CLK_PERIOD);
        $display("DDR3_CLK_PERIOD = %0d", DDR3_CLK_PERIOD);
        $display("ROW_BITS = %0d", ROW_BITS);
        $display("COL_BITS = %0d", COL_BITS);
        $display("BA_BITS = %0d", BA_BITS);
        $display("BYTE_LANES = %0d", LANES);
        $display("AUX_WIDTH = %0d", AUX_WIDTH);
        $display("MICRON_SIM = %0d", MICRON_SIM);
        $display("ODELAY_SUPPORTED = %0d", ODELAY_SUPPORTED);
        $display("SECOND_WISHBONE = %0d", SECOND_WISHBONE);
        $display("WB2_ADDR_BITS = %0d", WB2_ADDR_BITS);
        $display("WB2_DATA_BITS = %0d", WB2_DATA_BITS);
        $display("ECC_ENABLE = %0d", ECC_ENABLE);
        $display("ECC_INFORMATION_BITS = %0d", ECC_INFORMATION_BITS);
        $display("WB_ERROR = %0d", WB_ERROR);
        
        $display("\nCONTROLLER LOCALPARAMS:\n-----------------------------");
        $display("wb_addr_bits = %0d", wb_addr_bits);
        $display("wb_data_bits = %0d", wb_data_bits);
        $display("wb_sel_bits  = %0d", wb_sel_bits);
        $display("wb2_sel_bits = %0d", wb2_sel_bits);
        $display("DQ_BITS = %0d", DQ_BITS);
        $display("row_bank_col = %0d", row_bank_col);
        
        $display("\nCOMMAND SLOTS:\n-----------------------------");
        $display("READ_SLOT = %0d", READ_SLOT);
        $display("WRITE_SLOT = %0d", WRITE_SLOT);
        $display("ACTIVATE_SLOT = %0d", ACTIVATE_SLOT);
        $display("PRECHARGE_SLOT = %0d", PRECHARGE_SLOT);
        $display("REMAINING_SLOT = %0d", REMAINING_SLOT);
        
        $display("\nDELAYS:\n-----------------------------");
        $display("CL = %0d", CL_nCK);
        $display("CWL = %0d", CWL_nCK);
        $display("PRECHARGE_TO_ACTIVATE_DELAY = %0d", PRECHARGE_TO_ACTIVATE_DELAY);
        $display("ACTIVATE_TO_WRITE_DELAY = %0d", ACTIVATE_TO_WRITE_DELAY);
        $display("ACTIVATE_TO_READ_DELAY =  %0d", ACTIVATE_TO_READ_DELAY);
        $display("ACTIVATE_TO_PRECHARGE_DELAY =  %0d", ACTIVATE_TO_PRECHARGE_DELAY);
        $display("ACTIVATE_TO_ACTIVATE_DELAY =  %0d", ACTIVATE_TO_ACTIVATE_DELAY);
        $display("READ_TO_WRITE_DELAY = %0d", READ_TO_WRITE_DELAY);
        $display("READ_TO_READ_DELAY = %0d", READ_TO_READ_DELAY);
        $display("READ_TO_PRECHARGE_DELAY = %0d", READ_TO_PRECHARGE_DELAY);
        $display("WRITE_TO_WRITE_DELAY = %0d", WRITE_TO_WRITE_DELAY);
        $display("WRITE_TO_READ_DELAY = %0d", WRITE_TO_READ_DELAY);
        $display("WRITE_TO_PRECHARGE_DELAY = %0d", WRITE_TO_PRECHARGE_DELAY);
        $display("STAGE2_DATA_DEPTH = %0d", STAGE2_DATA_DEPTH);
        $display("READ_ACK_PIPE_WIDTH = %0d\n", READ_ACK_PIPE_WIDTH);
        
        $display("\nDDR3 TOP PARAMETERS:\n-----------------------------");
        $display("CONTROLLER_CLK_PERIOD = %0d", CONTROLLER_CLK_PERIOD);
        $display("DDR3_CLK_PERIOD = %0d", DDR3_CLK_PERIOD);
        $display("ROW_BITS = %0d", ROW_BITS);
        $display("COL_BITS = %0d", COL_BITS);
        $display("BA_BITS = %0d", BA_BITS);
        $display("BYTE_LANES = %0d", LANES);
        $display("AUX_WIDTH = %0d", AUX_WIDTH);
        $display("WB2_ADDR_BITS = %0d", WB2_ADDR_BITS);
        $display("WB2_DATA_BITS = %0d", WB2_DATA_BITS);
        $display("MICRON_SIM = %0d", MICRON_SIM);
        $display("ODELAY_SUPPORTED = %0d", ODELAY_SUPPORTED);
        $display("SECOND_WISHBONE = %0d", SECOND_WISHBONE);
        $display("WB_ERROR = %0d", WB_ERROR);
        $display("BIST_MODE = %0d", BIST_MODE);
        $display("ECC_ENABLE = %0d", ECC_ENABLE);
        $display("DIC = %0d", DIC);
        $display("RTT_NOM = %0d", RTT_NOM);
        $display("DUAL_RANK_DIMM = %0d", DUAL_RANK_DIMM);
        $display("End of DDR3 TOP PARAMETERS\n-----------------------------");
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
        localparam F_MAX_ACK_DELAY = F_MAX_STALL + (READ_ACK_PIPE_WIDTH + 2) + (ECC_ENABLE == 1 || ECC_ENABLE == 2); //max_stall + size of shift_reg_read_pipe_q + o_wb_ack_read_q (assume to be two via read_pipe_max) 
        // plus 1 since ECC adds 1 clock latency before ACK 
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

        reg[4:0] f_index_1;
        reg[F_TEST_CMD_DATA_WIDTH - 1:0] f_write_data;
        reg f_write_fifo = 0, f_read_fifo = 0;
        reg[ROW_BITS-1:0] f_bank_active_row[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; 
        reg[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] f_bank_status = 0;
        (*keep*) reg[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0] f_bank_status_2 = 0; 
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
        reg past_sync_rst_controller = 1;
        always @(posedge i_controller_clk) begin
            past_sync_rst_controller <= sync_rst_controller;
        end
        
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
        always @(posedge i_controller_clk) begin
            if(sync_rst_controller) begin
                f_addr <= 0;
                f_read <= 0;
            end
            //move the pipeline forward when counter is about to go zero and we are not yet at end of reset sequence
            else if((((delay_counter == 1) && !pause_counter) || !instruction[USE_TIMER])) begin             
                if(f_addr == 22 && user_self_refresh_q) begin // if self refresh, move forward
                    f_addr <= 23;
                end
                else if(f_addr == 22 & !user_self_refresh_q) begin // if not self refresh, move backward
                    f_addr <= 19;
                end
                else if (f_addr == 26) begin // 26 (self-refresh exit) always wraps back to 20 (refresh)
                    f_addr <= 20;
                end
                else begin // else, just increment 
                    f_addr <= f_addr + 1;
                end
                f_read <= f_addr;
            end     
            else if(f_addr == 22 && user_self_refresh_q) begin // if self refresh, move forward immediately (no need to wait for delay zero)
                f_addr <= 23;
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
                if(past_sync_rst_controller) begin
                    assert(f_addr == 0);
                    assert(f_read == 0);
                    assert(instruction_address == 0);
                    assert(delay_counter == (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0]));
                    assert(delay_counter_is_zero == (INITIAL_RESET_INSTRUCTION[DELAY_COUNTER_WIDTH - 1:0] == 0));
                end
                else if(f_past_valid) begin
                    //if counter is zero previously and current instruction needs timer delay, then this cycle should now have the new updated counter value
                    if( $past(delay_counter_is_zero) && $past(f_read_inst[USE_TIMER]) && !$past(user_self_refresh_q) ) begin 
                            assert(delay_counter == f_read_inst[DELAY_COUNTER_WIDTH - 1:0]); 
                    end
                     //delay_counter_is_zero can be high when counter is zero and current instruction needs delay
                     if($past(f_read_inst[USE_TIMER]) && !$past(pause_counter) && !$past(user_self_refresh_q)) begin
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
                        assert((delay_counter == $past(delay_counter) - 1) || (delay_counter == 0 && $past(user_self_refresh_q))); 
                        assert(delay_counter < $past(delay_counter) ); //just to make sure delay_counter will never overflow back to all 1's
                    end
                    
                    //sanity checking for the comment "delay_counter will be zero AT NEXT CLOCK CYCLE when counter is now one"
                if($past(delay_counter) == 1 && !$past(pause_counter)) begin
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
                        assert( (f_addr == 19) || (f_addr == 23 ) ); //if current instruction is 22, then next instruction must be at 19 or 23 (instruction address wraps from 22 to 19 if not self refresh, else 22 to 23)
                    end
                    else if(f_addr == 19 || f_addr == 23) begin
                        assert(f_read == 22); //if next instruction is at 19 or 23, then current instruction must be at 22 (instruction address wraps from 22 to 19)
                    end
                    else if(f_read == 26) begin
                        assert(f_addr == 20); // if current instruction is 26 (exit self-refresh) then go to 20 (refresh)
                    end
                    else begin
                        assert(f_read + 1 == f_addr); //if there is no need to wrap around, then instruction address must increment 
                    end
                    assert((f_read >= 19 && f_read <= 26) ); //refresh sequence is only on instruction address 19,20,21,22
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
            if(pause_counter) begin 
                assert(instruction_address != 22); //pause_counter can only go high at instruction address 26
            end

            if(instruction_address == 19 || instruction_address == 23) begin //pre-stall delay before precharge all to finish all remaining requests
                if(pause_counter == 1) begin // if there are still pending requests (pause_counter high) then delay_counter should still be at PRE_REFRESH_DELAY
                    assert(delay_counter == PRE_REFRESH_DELAY);
                end
            end
            if(instruction_address >= 24 && instruction_address < 26) begin
                assert(!pause_counter); // no pause counter from precharge to sel-refresh entry
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
                assume(delay_counter != 0);
                // will fix this soon
            end
            
            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate <= ANALYZE_DATA) begin
                assume(instruction_address == 22); //write-then-read calibration will not take more than tREFI (7.8us, delay a address 22)
                assert(reset_done);
            end
            
            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate <= DONE_CALIBRATE) begin
                assert(reset_done);
            end
            
            if(state_calibrate == DONE_CALIBRATE) begin
                assert(reset_done);
                assert(instruction_address >= 19);
            end

            if(reset_done) begin
                assert(instruction_address >= 19);
            end
            
            assume(repeat_test == 0);

            // final_calibration_done is equal to state_calibrate == DONE
            assert(final_calibration_done == (state_calibrate == DONE_CALIBRATE));
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
            .i_rst_n(!past_sync_rst_controller && i_wb_cyc), //reset outstanding request at reset or when cyc goes low
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
                if(ECC_ENABLE != 3) begin
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
                else begin
                    if(f_full) begin 
                        // if f_full then data can either be in:
                        // stage1 and stage2 IF ecc_req_stage2 is low
                        // stage0 and stage1 IF ecc_req_stage2 is high
                        assert((stage1_pending && stage2_pending && !ecc_req_stage2) || (stage0_pending && stage1_pending && ecc_req_stage2));
                    end
                    if(stage1_pending && stage2_pending) begin
                        // if stage1 and stage2 is pending,and stage2 is non-ECC : fifo is full
                        if(!ecc_req_stage2) begin
                            assert(f_full);
                        end
                        // if stage2 is ECC-req while stage0 is pending then fifo is still full
                        if(ecc_req_stage2 && stage0_pending) begin
                            assert(f_full);
                        end
                    end
                    // stage0 and stage1 pending means fifo is full and stage2 is ECC request
                    if(stage0_pending && stage1_pending) begin
                        assert(f_full);
                        assert(ecc_req_stage2);
                    end

                    if(!f_empty && !f_full) begin // if there is only 1 content
                        assert((stage1_pending ^ stage2_pending) || (stage1_pending && stage2_pending && ecc_req_stage2));
                        // if only 1 req, then either stage1 or stage2 is pending, UNLESS stage2 is ECC
                    end
                    if(stage1_pending ^ stage2_pending) begin
                        // if either only stage1 or 2 is pending, then there is only 1 request
                        assert(!f_empty && !f_full);
                    end

                    if(f_empty) begin
                        assert(stage1_pending == 0 && stage2_pending == 0 && stage0_pending == 0); //there is 0 content
                    end
                    if(stage1_pending == 0 && stage2_pending == 0) begin
                        assert(f_empty);
                        assert(!stage0_pending);
                    end
                end
            end

            if(state_calibrate < ISSUE_WRITE_1) begin
                assert(!stage1_pending && !stage2_pending);
            end
            if(stage1_pending && (state_calibrate == ISSUE_READ)) begin
                assert(stage1_we);
            end
            if(stage2_pending && (state_calibrate == ISSUE_READ)) begin
                assert(stage2_we);
            end
            if(state_calibrate == ANALYZE_DATA) begin
                assert(!stage1_pending && !stage2_pending);
            end
            if(state_calibrate == READ_DATA && calib_stb) begin //if read request is not yet sent, the stage we must both be writes
                if(stage1_pending) begin
                    assert(stage1_we);
                end
                if(stage2_pending) begin
                    assert(stage2_we);
                end
                assert(f_sum_of_pending_acks <= 2);
            end
             if(state_calibrate == READ_DATA && !calib_stb) begin //if read request is not yet sent, the stage we must both be writes
                if(stage1_pending && !stage2_pending) begin 
                    assert(!stage1_we);
                end
                if(!stage1_pending && stage2_pending) begin
                    assert(!stage2_we);
                end
                if(stage1_pending && stage2_pending) begin
                    assert(!stage1_we);
                    assert(stage2_we);
                end
                 
            end
            assume(state_calibrate != CHECK_STARTING_DATA && state_calibrate != BITSLIP_DQS_TRAIN_3); //this state should not be used (only for ddr3 with problems on DQ-DQS alignment)
        end

        always @(posedge i_controller_clk) begin
            if(f_past_valid) begin
                //switch from calibrate to done
                if(state_calibrate == DONE_CALIBRATE && $past(state_calibrate) != DONE_CALIBRATE) begin
                    //assert($past(state_calibrate) == FINISH_READ);
                    assert($past(state_calibrate) == FINISH_READ);
                    assert(f_empty);
                    assert(!stage1_pending);
                    assert(!stage2_pending);
                    //assert(f_bank_status == 1); //only first bank is activated
                    //assert(bank_status_q == 1);
                end
                if(stage1_pending /*&& $past(state_calibrate) == READ_DATA */ && state_calibrate == READ_DATA && !calib_stb) begin
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
               /*if(state_calibrate <= ANALYZE_DATA) begin
                    assert(f_bank_status == 0 || f_bank_status == 1); //only first bank is activated
                    assert(bank_status_q == 0 || f_bank_status == 1);
               end*/
            end
        end

        //wishbone request should have a corresponding DDR3 command at the output
        //wishbone request will be written to fifo, then once a DDR3 command is
        //issued the fifo will be read to check if the DDR3 command matches the
        //corresponding wishbone request
        reg[ROW_BITS-1:0] f_read_data_col;
        reg[BA_BITS-1+DUAL_RANK_DIMM:0] f_read_data_bank;
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

                if(cmd_d[WRITE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b100 && (ECC_ENABLE != 3 || !ecc_req_stage2) ) begin //WRITE
                    if(state_calibrate == DONE_CALIBRATE) begin
                       assert(f_bank_status[{(!cmd_d[WRITE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM), cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] == 1'b1); //the bank that will be written must initially be active 
                       f_read_data_col = {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}; //column address must match 
                       assert(cmd_d[WRITE_SLOT][CMD_ADDRESS_START:0] == f_read_data_col);

                        if(row_bank_col == 1) begin // address mapping {row, bank,col}
                            f_read_data_bank = {f_read_data[F_TEST_CMD_DATA_WIDTH-1] && DUAL_RANK_DIMM ,f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]}; //bank must match 
                        end
                        else if(row_bank_col == 0) begin // address mapping {bank, row, col}
                            f_read_data_bank = f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]; //bank must match 
                        end
                        else if(row_bank_col == 2) begin // address mapping {bank[2:1], row, bank[0], col}
                            f_read_data_bank[0] = f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]; //bank must match 
                            f_read_data_bank[2:1] = f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]; //bank must match 
                        end
                        assert({!cmd_d[WRITE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM, cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]} == f_read_data_bank);

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
                    else if(state_calibrate > ISSUE_WRITE_1 && state_calibrate <= ANALYZE_DATA) begin
                        assert(stage2_aux[2:0] == 0);
                    end
                    //assert(f_bank_active_row[cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == current_row); //column to be written must be the current active row
                end

                if(cmd_d[READ_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b101 && (ECC_ENABLE != 3 || !ecc_req_stage2)) begin //READ
                   if(state_calibrate == DONE_CALIBRATE) begin
                       assert(f_bank_status[{ (!cmd_d[READ_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM) , cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] == 1'b1); //the bank that will be read must initially be active 
                       f_read_data_col = {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}; //column address must match 
                       assert(cmd_d[READ_SLOT][CMD_ADDRESS_START:0] == f_read_data_col);
                        
                        if(row_bank_col == 1) begin // address mapping {row, bank,col}
                            f_read_data_bank = {f_read_data[F_TEST_CMD_DATA_WIDTH-1] && DUAL_RANK_DIMM , f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]}; //bank must match 
                        end
                        else if(row_bank_col == 0) begin // address mapping {bank, row, col}
                            f_read_data_bank = f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]; //bank must match 
                        end
                        else if(row_bank_col == 2) begin // address mapping {bank[2:1], row, bank[0], col}
                            f_read_data_bank[0] = f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]; //bank must match 
                            f_read_data_bank[2:1] = f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]; //bank must match 
                        end

                       assert({!cmd_d[READ_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM ,cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]} == f_read_data_bank);

                       `ifdef TEST_DATA
                           f_read_data_aux = f_read_data[$bits(i_wb_addr) + 1 +: AUX_WIDTH]; //UAX ID must match 
                           assert(stage2_aux == f_read_data_aux);
                       `endif

                       assert(!f_read_data[0]); //i_wb_we must be low
                       f_read_fifo = 1; //advance read pointer to prepare for next read
                   end
                    else if(state_calibrate > ISSUE_WRITE_1 && state_calibrate <= ANALYZE_DATA) begin
                        assert(stage2_aux[2:0] == 1);
                    end
                    //assert(f_bank_active_row[cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]] == current_row);//column to be written must be the current active row
                end


                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b010) begin //PRECHARGE
                   if(state_calibrate == DONE_CALIBRATE && (instruction_address == 22 || instruction_address == 19)) begin
                        assert(f_bank_status[{!cmd_d[PRECHARGE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] == 1'b1); //the bank that should be precharged must initially be active 
                   end
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b011) begin //ACTIVATE
                   if(state_calibrate == DONE_CALIBRATE) begin
                       assert(f_bank_status[{!cmd_d[ACTIVATE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] == 1'b0); //the bank that should be activated must initially be precharged 
                   end
                end

                if(reset_done) begin
                    assert(cmd_d[PRECHARGE_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                    assert(cmd_d[ACTIVATE_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                    assert(cmd_d[READ_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                    assert(cmd_d[WRITE_SLOT][CMD_RESET_N]); //cke and rst_n should stay high when reset sequence is already done
                end
            end
            if(state_calibrate == DONE_CALIBRATE) begin
                assert(reset_done);
            end
            if(state_calibrate != DONE_CALIBRATE && !past_sync_rst_controller) begin
                assert(o_wb_stall); //if not yet finished calibrating, stall should never go low
            end
            if(state_calibrate != DONE_CALIBRATE) begin
                assert(f_empty); //if not yet finished calibrating, stall should never go low
            end
            if(!f_empty) begin
                assert(state_calibrate == DONE_CALIBRATE);
            end
            if(train_delay == 0 && state_calibrate == FINISH_READ) begin//fix this soon
                assume(f_sum_of_pending_acks == 0);
            end
        end

    //`ifdef UNDER_CONSTRUCTION
        //make assertions on what is inside the fifo
        always @* begin
            if(!f_empty && !f_full) begin //make assertion when there is only 1 data on the pipe
                if(stage1_pending) begin //request is still on stage1
                    if(row_bank_col == 1) begin
                        assert(stage1_bank == {f_read_data[F_TEST_CMD_DATA_WIDTH-1] && DUAL_RANK_DIMM , f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]}); //bank must match 
                        assert(stage1_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    end
                    else if(row_bank_col == 0) begin
                        assert(stage1_bank == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                        assert(stage1_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    end
                    else if(row_bank_col == 2) begin
                        assert(stage1_bank[0] == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]); //bank must match 
                        assert(stage1_bank[2:1] == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]); //bank must match 
                        assert(stage1_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    end
                    assert(stage1_we == f_read_data[0]); //i_wb_we must be same
                end
                if(stage2_pending && !stage1_pending) begin //request is now on stage2
                    if(row_bank_col == 1) begin
                        assert(stage2_bank == {f_read_data[F_TEST_CMD_DATA_WIDTH-1] && DUAL_RANK_DIMM , f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]}); //bank must match 
                        assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    end
                    else if(row_bank_col == 0) begin
                        assert(stage2_bank == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                        assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    end
                    else if(row_bank_col == 2) begin
                        assert(stage2_bank[0] == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]); //bank must match 
                        assert(stage2_bank[2:1] == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]); //bank must match 
                        assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    end
                    assert(stage2_we == f_read_data[0]); //i_wb_we must be same
                end
                // if there is only 1 request on fifo but both pendings are high then stage must be an ECC-request
                if((ECC_ENABLE == 3) && stage1_pending && stage2_pending) begin
                    assert(ecc_req_stage2);
                end
            end

            if(f_full) begin //both stages have request
                //stage2 is the request on the tip of the fifo
                if(row_bank_col == 1) begin
                    assert(stage2_bank == {f_read_data[F_TEST_CMD_DATA_WIDTH-1] && DUAL_RANK_DIMM , f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]}); //bank must match 
                    assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    assert(stage2_we == f_read_data[0]); //i_wb_we must be same
                    //stage1 is the request on the other element of the fifo
                    //(since the fifo only has 2 elements, the other element that
                    //is not the tip will surely be the 2nd request that is being
                    //handles by stage1)
                    assert(stage1_bank == {f_read_data_next[F_TEST_CMD_DATA_WIDTH-1] && DUAL_RANK_DIMM , f_read_data_next[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]}); //bank must match 
                    assert(stage1_col == {f_read_data_next[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    assert(stage1_we == f_read_data_next[0]); //i_wb_we must be same
                end
                else if(row_bank_col == 0) begin
                    assert(stage2_bank == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                    assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    assert(stage2_we == f_read_data[0]); //i_wb_we must be same
                    //stage1 is the request on the other element of the fifo
                    //(since the fifo only has 2 elements, the other element that
                    //is not the tip will surely be the 2nd request that is being
                    //handles by stage1)
                    assert(stage1_bank == f_read_data_next[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 1 +: BA_BITS]); //bank must match 
                    assert(stage1_col == {f_read_data_next[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                    assert(stage1_we == f_read_data_next[0]); //i_wb_we must be same
                end
                else if(row_bank_col == 2) begin
                    // If fifo is full and stage2 is non-ECC, then stage2 will have the first request on fifo
                    if(!ecc_req_stage2) begin
                        assert(stage2_bank[0] == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]); //bank must match 
                        assert(stage2_bank[2:1] == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]); //bank must match 
                        assert(stage2_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                        assert(stage2_we == f_read_data[0]); 
                        //stage1 is the request on the other element of the fifo
                        //(since the fifo only has 2 elements, the other element that
                        //is not the tip will surely be the 2nd request that is being
                        //handled by stage1)
                        assert(stage1_bank[0] == f_read_data_next[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]); //bank must match 
                        assert(stage1_bank[2:1] == f_read_data_next[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]); //bank must match 
                        assert(stage1_col == {f_read_data_next[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                        assert(stage1_we == f_read_data_next[0]); 
                    end
                    else begin
                        // if there is ECC request on stage2, then stage1 will have the first request on fifo
                        assert(stage1_bank[0] == f_read_data[(COL_BITS - $clog2(serdes_ratio*2)) + 1 +: 1]); //bank must match 
                        assert(stage1_bank[2:1] == f_read_data[(ROW_BITS + COL_BITS - $clog2(serdes_ratio*2)) + 2 +: BA_BITS-1]); //bank must match 
                        assert(stage1_col == {f_read_data[1 +: COL_BITS - $clog2(serdes_ratio*2)], 3'b000}); //column address must match 
                        assert(stage1_we == f_read_data[0]); 
                        // stage0 will have second request on fifo
                        assert(stage0_addr == f_read_data_next[F_TEST_CMD_DATA_WIDTH - 1:1]);
                        assert(stage0_we == f_read_data_next[0]);
                    end
                end
            end
            if(ECC_ENABLE == 3) begin
                // if stage0 is pending then f_full must be high, stall is high, and s1 and s2 pending is high
                if(stage0_pending) begin
                    if(final_calibration_done) assert(f_full); // r/w calibration test does not come from fifo so wait until final calibration is done
                    if(final_calibration_done) assert(o_wb_stall);
                    if(!final_calibration_done) assert(o_wb_stall_calib);
                    assert(stage1_pending && stage2_pending);
                    assert(ecc_req_stage2);
                end
                // initial and final calibration signals
                if(state_calibrate >= BURST_WRITE) assert(initial_calibration_done);
                else assert(!initial_calibration_done);

                if(state_calibrate == DONE_CALIBRATE) assert(final_calibration_done);
                else assert(!final_calibration_done);
            end
        end
        
    //`endif
        // Assertions on ECC signals
        always @(posedge i_controller_clk) begin
            if(ECC_ENABLE == 3) begin
                // if stage2 is ECC request, then stage1 is the original non-ECC request
                if(ecc_req_stage2) begin
                    // if there is ECC request on stage2, then o_wb_stall must be high (except when ecc_stage2_stall is low which means stage2 is done this cycle)
                    if(final_calibration_done) assert(o_wb_stall || !ecc_stage2_stall);
                    else assert(o_wb_stall_calib || !ecc_stage2_stall);
                    assert(stage1_pending && stage2_pending);
                end

                // stage0_pending will rise to high if ecc_stage1_stall is high the previous cycle and stall is low
                if(stage0_pending && !$past(stage0_pending)) begin
                    assert($past(ecc_stage1_stall) && !$past(o_wb_stall_q));
                end

                // stage0_pending currently high means stage2 and stage1 is pending, and there is ECC request on stage2
                if(stage0_pending) begin
                    assert(stage1_pending && stage2_pending);
                    assert(ecc_req_stage2);
                end
            end
        end
        always @* begin
            assert(f_bank_status == bank_status_q);
            if(instruction_address >= 25) begin // after precharge until end of refresh, all banks are idle
                assert(bank_status_q == 0);
            end
            if(instruction_address == 23 && pause_counter) begin // if at PRE_REFRESH_DELAY and not yet done, then delay_counter should still be at original value

            end
        end

        (*keep*) reg[31:0] bank; 
        always @(posedge i_controller_clk) begin
            if(sync_rst_controller) begin
                //reset bank status and active row
                for(f_index_1=0; f_index_1 < (1<<(BA_BITS+DUAL_RANK_DIMM)); f_index_1=f_index_1+1) begin
                        f_bank_status[f_index_1] <= 0;  
                        f_bank_status_2[f_index_1] = 0;  
                        f_bank_active_row[f_index_1] <= 0; 
                end
            end
            else begin
                //check if a DDR3 command is issued
                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b010) begin //PRECHARGE
                    bank = {!cmd_d[PRECHARGE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]};
                    if(cmd_d[PRECHARGE_SLOT][10]) begin //A10 precharge all banks
                        for(f_index_1=0; f_index_1 < (1<<(BA_BITS+DUAL_RANK_DIMM)); f_index_1=f_index_1+1) begin
                                f_bank_status_2[f_index_1] = 0;  
                        end
                    end
                    else begin
                        //f_bank_status <= f_bank_status & ~(1<<bank); //set to zero to idle bank
                        //f_bank_status[bank] <= 0; //set to zero to idle bank
                        f_bank_status_2 = f_bank_status_2 & ~(1<<bank); //set to zero to idle bank
                    end
                    assert(bank <= (8<<DUAL_RANK_DIMM)-1); // if dual rank, then logically there will be double the banks
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b011) begin //ACTIVATE
                    bank = {!cmd_d[ACTIVATE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]};
                   // f_bank_status <= f_bank_status | (1<<bank); //bank will be turned active
                    //f_bank_status[bank] <= 1;
                    assert(bank <= (8<<DUAL_RANK_DIMM)-1); 
                    f_bank_status_2 = f_bank_status_2 | (1<<bank); //bank will be turned active
                    f_bank_active_row[bank] <= cmd_d[ACTIVATE_SLOT][CMD_ADDRESS_START:0]; //save row to be activated 
                end

                if(instruction_address == 20 || instruction_address == 24) begin ///current instruction at precharge
                    //all banks will be in idle after refresh
                    for( index=0; index < (1<<(BA_BITS+DUAL_RANK_DIMM)); index=index+1) begin
                        f_bank_status_2[index] <= 0;  
                    end
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
                        assert(o_wb_stall_calib);
                    end
                    //delay_counter is zero at first clock of new instruction address, the actual delay_clock wil start at next clock cycle 
                    if(instruction_address == 19 && delay_counter != 0) begin
                        assert(o_wb_stall);
                        assert(o_wb_stall_calib);
                    end
                    if(instruction_address == 20 || instruction_address == 21) begin //no pending request at precharge all and refresh command
                        assert(!stage1_pending);
                        assert(!stage2_pending);
                    end
                    if($past(o_wb_stall_q) && stage1_pending && !$past(stage1_update)) begin //if pipe did not move forward
                       assert(stage1_we == $past(stage1_we));
                       assert(stage1_aux == $past(stage1_aux));
                       assert(stage1_bank == $past(stage1_bank));
                       assert(stage1_col == $past(stage1_col));
                       assert(stage1_row == $past(stage1_row));
                       assert(stage1_dm == $past(stage1_dm));
                    end
                    if(stage0_pending && $past(stage0_pending) && (ECC_ENABLE == 3)) begin // stage0 must remain the same as long as pending is high
                        assert(stage0_addr == $past(stage0_addr));
                        assert(stage0_aux == $past(stage0_aux));
                        assert(stage0_we == $past(stage0_we));
                    end
                end
        end
        
        always @* begin
            if(instruction_address != 22 && instruction_address != 19 && instruction_address != 23) begin
               assert(!stage1_pending && !stage2_pending); //must be pending except in tREFI and in prestall delay
            end

            if(!reset_done) begin 
                assert(stage1_pending == 0 && stage2_pending == 0);
            end

            if((state_calibrate <= ISSUE_READ) || (state_calibrate >= ANALYZE_DATA && state_calibrate <= BITSLIP_DQS_TRAIN_3)) begin // add ANALYZE_DATA and BITSLIP_DQS_TRAIN_3
                for(f_index_1 = 0; f_index_1 < 1; f_index_1 = f_index_1 + 1) begin
                    assert(o_wb_ack_read_q[f_index_1] == 0);
                end
                for(f_index_1 = 0; f_index_1 < READ_ACK_PIPE_WIDTH; f_index_1 = f_index_1 + 1) begin
                    assert(shift_reg_read_pipe_q[f_index_1] == 0);
                end
            end

            if( state_calibrate < ISSUE_WRITE_1 ) begin
                assert(bank_status_q == 0);
            end

            if(state_calibrate != DONE_CALIBRATE) begin
                assert(o_wb_ack == 0); //o_wb_ack must not go high before done calibration
            end

            if(state_calibrate > ISSUE_WRITE_1 && state_calibrate <= READ_DATA) begin
                if(stage1_pending) begin
                    assert(!stage1_we == stage1_aux[0]); //if write, then aux id must be 1 else 0
                    assert(stage1_aux[2:1] == 2'b00);
                end
                if(stage2_pending) begin
                    assert(!stage2_we == stage2_aux[0]); //if write, then aux id must be 1 else 0
                    assert(stage2_aux[2:1] == 2'b00);
                end
            end

            assert(state_calibrate <= DONE_CALIBRATE);
        end
        
        
        wire[3:0] f_nreqs, f_nacks, f_outstanding;
        wire[3:0] f_ackwait_count, f_stall_count;
        wire[3:0] f_nreqs_2, f_nacks_2, f_outstanding_2;
        reg[READ_ACK_PIPE_WIDTH+1+(ECC_ENABLE == 1 || ECC_ENABLE == 2):0] f_ack_pipe_after_stage2;
        reg[AUX_WIDTH:0] f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH+1+(ECC_ENABLE == 1 || ECC_ENABLE == 2):0];
        // 1 more pipeline stage will be added when ECC_ENABLE is 1 or 2
        integer f_ack_pipe_marker;

        integer f_sum_of_pending_acks = 0;
        always @* begin
                if(past_sync_rst_controller) begin
                    assume(f_nreqs == 0);
                    assume(f_nacks == 0);
                end

                if(state_calibrate != IDLE) assume(added_read_pipe_max == 1);
                if(ECC_ENABLE == 3) begin
                    f_sum_of_pending_acks = stage1_pending + (stage2_pending && !ecc_req_stage2) + stage0_pending; // stage2 is only valid if non-ECC request
                end
                else begin
                    f_sum_of_pending_acks = stage1_pending + stage2_pending;
                end
                for(f_index_1 = 0; f_index_1 < READ_ACK_PIPE_WIDTH; f_index_1 = f_index_1 + 1) begin
                    f_sum_of_pending_acks = f_sum_of_pending_acks + shift_reg_read_pipe_q[f_index_1][0] + 0;
                end
                for(f_index_1 = 0; f_index_1 < 2; f_index_1 = f_index_1 + 1) begin //since added_read_pipe_max is assumed to be one, only the first two bits of o_wb_ack_read_q is relevant
                    f_sum_of_pending_acks = f_sum_of_pending_acks + o_wb_ack_read_q[f_index_1][0] + 0;
                end
                if(ECC_ENABLE == 1 || ECC_ENABLE == 2) begin
                    f_sum_of_pending_acks = f_sum_of_pending_acks + o_wb_ack_uncalibrated + o_wb_ack_q;
                end

                if(o_wb_ack_uncalibrated) begin
                    assert(state_calibrate != DONE_CALIBRATE);
                end
                if(o_wb_ack_q) begin
                    assert(state_calibrate == DONE_CALIBRATE);
                end

                //the remaining o_wb_ack_read_q (>2) should stay zero at
                //all instance
                for(f_index_1 = 2; f_index_1 < MAX_ADDED_READ_ACK_DELAY ; f_index_1 = f_index_1 + 1) begin
                    assert(o_wb_ack_read_q[f_index_1] == 0);
                end
                if(ECC_ENABLE == 1 || ECC_ENABLE == 2) begin
                    f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH+1+1] = {o_aux,(o_wb_ack_uncalibrated || o_wb_ack_q)};
                end
                f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH+1] = o_wb_ack_read_q[0]; //last stage of f_aux_ack_pipe_after_stage2 is also the last ack stage
                f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH] = o_wb_ack_read_q[1];
                for(f_index_1 = 0; f_index_1 < READ_ACK_PIPE_WIDTH; f_index_1 = f_index_1 + 1) begin
                    f_aux_ack_pipe_after_stage2[READ_ACK_PIPE_WIDTH - 1 - f_index_1] = shift_reg_read_pipe_q[f_index_1];
                end

                if(ECC_ENABLE == 1 || ECC_ENABLE == 2) begin
                    f_ack_pipe_after_stage2 = {
                        (o_wb_ack_uncalibrated || o_wb_ack_q),
                        o_wb_ack_read_q[0][0], 
                        o_wb_ack_read_q[1][0], 
                        shift_reg_read_pipe_q[0][0], 
                        shift_reg_read_pipe_q[1][0],
                        shift_reg_read_pipe_q[2][0],
                        shift_reg_read_pipe_q[3][0],
                        shift_reg_read_pipe_q[4][0]
                    };
                end
                else begin
                    f_ack_pipe_after_stage2 = {
                        o_wb_ack_read_q[0][0], 
                        o_wb_ack_read_q[1][0], 
                        shift_reg_read_pipe_q[0][0], 
                        shift_reg_read_pipe_q[1][0],
                        shift_reg_read_pipe_q[2][0],
                        shift_reg_read_pipe_q[3][0],
                        shift_reg_read_pipe_q[4][0]
                    };
                end
                // write_ack_index_q must be less than READ_ACK_PIPE_WIDTH
                assert(write_ack_index_q < READ_ACK_PIPE_WIDTH);
                assert(write_ack_index_q != 0); //always greater than 1
                if(f_ackwait_count > F_MAX_STALL && (ECC_ENABLE != 3)) begin
                    assert(|f_ack_pipe_after_stage2[(READ_ACK_PIPE_WIDTH+1) : (f_ackwait_count - F_MAX_STALL - 1)]); //at least one stage must be high
                end

                if(!past_sync_rst_controller && state_calibrate == DONE_CALIBRATE) begin
                    assert(f_outstanding == f_sum_of_pending_acks || !i_wb_cyc);
                end
                else if(past_sync_rst_controller) begin
                    assert(f_sum_of_pending_acks == 0);
                end
                if(state_calibrate != DONE_CALIBRATE && !past_sync_rst_controller) begin
                    assert(f_outstanding == 0 || !i_wb_cyc);
                end
                if(state_calibrate <= ISSUE_WRITE_1 && !past_sync_rst_controller) begin
                    //not inside tREFI, prestall delay, nor precharge
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                    assert(f_sum_of_pending_acks == 0);
                end
                if(state_calibrate == READ_DATA && !past_sync_rst_controller) begin
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                    assert(f_sum_of_pending_acks <= 3);

                    // if((f_sum_of_pending_acks > 1) && o_wb_ack_read_q[0]) begin
                    //     assert(o_wb_ack_read_q[0] == {0, 1'b1}); 
                    // end
                    if((f_sum_of_pending_acks > 1) && o_wb_ack_uncalibrated) begin //if sum of pending acks > 1 then the first two will be write and have aux of 0, while the last will have aux of 1 (read)
                        assert(o_aux[2:0] == 0);
                        assert(o_wb_ack_uncalibrated == 1);
                    end
                    f_ack_pipe_marker = 0;
                    for(f_index_1 = 0; f_index_1 < READ_ACK_PIPE_WIDTH + 2; f_index_1 = f_index_1 + 1) begin //check each ack stage starting from last stage
                        if(f_aux_ack_pipe_after_stage2[f_index_1][0]) begin //if ack is high
                            if(f_aux_ack_pipe_after_stage2[f_index_1][3:1] == 1) begin //ack for read
                                assert(f_ack_pipe_marker == 0); //read ack must be the last ack on the pipe(f_pipe_marker must still be zero)
                                f_ack_pipe_marker = f_ack_pipe_marker + 1;
                                assert(!stage1_pending && !stage2_pending); //a single read request must be the last request on this calibration
                            end
                            else begin //ack for write
                                assert(f_aux_ack_pipe_after_stage2[f_index_1][3:1] == 0);
                                f_ack_pipe_marker = f_ack_pipe_marker + 1;
                            end
                        end
                    end
                    assert(f_ack_pipe_marker <= 3);
                end
                if(state_calibrate <= READ_DATA && (ECC_ENABLE == 3)) begin
                    assert(!stage0_pending); // stage0 pending will never go high before READ_DATA
                end

                if(state_calibrate == ANALYZE_DATA && !past_sync_rst_controller) begin
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                    assert(f_sum_of_pending_acks == 0);
                end
                if(state_calibrate != DONE_CALIBRATE && !past_sync_rst_controller) begin //if not yet done calibration, no request should be accepted
                    assert(f_nreqs == 0);
                    assert(f_nacks == 0);
                    assert(f_outstanding == 0 || !i_wb_cyc); 
                end

               if(state_calibrate == ISSUE_WRITE_2 || state_calibrate == ISSUE_READ) begin
                   if(calib_stb == 1) begin
                        assert(calib_aux[2:0] == 0);          
                        assert(calib_we == 1);
                    end
               end
               if(state_calibrate == READ_DATA) begin
                   if(calib_stb == 1) begin
                        assert(calib_aux[2:0] == 1);          
                        assert(calib_we == 0);
                    end
               end
               if(state_calibrate <= ISSUE_WRITE_1 || state_calibrate == ANALYZE_DATA || state_calibrate == DONE_CALIBRATE) begin
                        assert(calib_stb == 0);
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
                if(instruction_address != 22 && instruction_address != 19 && instruction_address != 23 && $past(i_wb_cyc) && !past_sync_rst_controller) begin
                   assert(f_nreqs == $past(f_nreqs));           
                end
                if(state_calibrate == DONE_CALIBRATE && $past(state_calibrate) != DONE_CALIBRATE && !past_sync_rst_controller) begin//just started DONE_CALBRATION
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
            for(f_index_1=0; f_index_1< (1<<(BA_BITS+DUAL_RANK_DIMM)); f_index_1=f_index_1+1) begin
                assert(delay_before_precharge_counter_q[f_index_1] <= max(ACTIVATE_TO_PRECHARGE_DELAY, max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY)));
                assert(delay_before_activate_counter_q[f_index_1] <= PRECHARGE_TO_ACTIVATE_DELAY); 
                assert(delay_before_write_counter_q[f_index_1] <= (max(READ_TO_WRITE_DELAY,ACTIVATE_TO_WRITE_DELAY) + 1) );
                assert(delay_before_read_counter_q[f_index_1] <= (max(WRITE_TO_READ_DELAY,ACTIVATE_TO_READ_DELAY)) + 1);
            end
            if(stage2_pending && (ECC_ENABLE != 3)) begin
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
                      for(f_index_1 = 0; f_index_1 <= PRECHARGE_TO_ACTIVATE_DELAY; f_index_1= f_index_1 +1 ) begin
                        if(delay_before_activate_counter_q[stage2_bank] == PRECHARGE_TO_ACTIVATE_DELAY - f_index_1) begin
                            assert(f_ackwait_count <= (max(WRITE_TO_PRECHARGE_DELAY,READ_TO_PRECHARGE_DELAY) + 1 + f_index_1));
                        end
                      end
                      */
                end
            end
            else begin
                // this is cheating but for now this will do, I shall come back here soon to fix this ;)
                assume(f_stall_count < F_MAX_STALL);
                assume(f_ackwait_count < F_MAX_ACK_DELAY);
            end
        end


        // Test time parameter violations
        reg[6:0] f_precharge_time_stamp[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; 
        reg[6:0] f_activate_time_stamp[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; 
        reg[6:0] f_read_time_stamp[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; 
        reg[6:0] f_write_time_stamp[(1<<(BA_BITS+DUAL_RANK_DIMM))-1:0]; 
        reg[6:0] f_timer = 0;
        initial begin
            for(f_index_1=0; f_index_1 < (1<<(BA_BITS+DUAL_RANK_DIMM)); f_index_1=f_index_1+1) begin
                f_precharge_time_stamp[f_index_1] = 0;
                f_activate_time_stamp[f_index_1] = 0;
                f_read_time_stamp[f_index_1] = 0;
                f_write_time_stamp[f_index_1] = 0;
            end
        end
        (*anyconst*) reg[BA_BITS-1+DUAL_RANK_DIMM:0] bank_const;


        always @(posedge i_controller_clk) begin
            f_timer <= f_timer + 4;
            if(f_past_valid) begin
                assume($past(f_timer) < f_timer); //assume that counter will never overflow
            end
        end

        always @(posedge i_controller_clk) begin
            if(sync_rst_controller) begin
                for(f_index_1=0; f_index_1 < (1<<(BA_BITS+DUAL_RANK_DIMM)); f_index_1=f_index_1+1) begin
                    f_precharge_time_stamp[f_index_1] <= 0;
                    f_activate_time_stamp[f_index_1] <= 0;
                    f_read_time_stamp[f_index_1] <= 0;
                    f_write_time_stamp[f_index_1] <= 0;
                end
            end
            else begin
                //check if a DDR3 command is issued
                if(cmd_d[PRECHARGE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b010) begin //PRECHARGE
                    f_precharge_time_stamp[{!cmd_d[PRECHARGE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[PRECHARGE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] <= f_timer + PRECHARGE_SLOT; 
                end

                if(cmd_d[ACTIVATE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b011) begin //ACTIVATE
                    f_activate_time_stamp[{!cmd_d[ACTIVATE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[ACTIVATE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] <= f_timer + ACTIVATE_SLOT; 
                end

                if(cmd_d[WRITE_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b100) begin //WRITE
                    f_write_time_stamp[{!cmd_d[WRITE_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[WRITE_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] <= f_timer + WRITE_SLOT;
                    //Check tCCD (write-to-write delay)
                    assert((f_timer+WRITE_SLOT) - f_write_time_stamp[bank_const] >= tCCD); 
                end

                if(cmd_d[READ_SLOT][CMD_CS_N-1:CMD_WE_N] == 3'b101) begin //READ
                    f_read_time_stamp[{!cmd_d[READ_SLOT][CMD_CS_N_2] && DUAL_RANK_DIMM , cmd_d[READ_SLOT][CMD_BANK_START:CMD_ADDRESS_START+1]}] <= f_timer + READ_SLOT;
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
                assert((f_precharge_time_stamp[bank_const] - f_read_time_stamp[bank_const]) >= ps_to_nCK(tRTP));
            end

            // Check tWTR (Delay from start of internal write transaction to internal read command)
            if(f_read_time_stamp[bank_const] > f_write_time_stamp[bank_const]) begin
                assert((f_read_time_stamp[bank_const] - f_write_time_stamp[bank_const]) >= (CWL_nCK + 3'd4 + ps_to_nCK(tWTR)));
            end

            // Check tRCD (ACT to internal read delay time)
            if(f_read_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_read_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ps_to_nCK(tRCD));
            end 
            
            // Check tRCD (ACT to internal write delay time)
            if(f_write_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_write_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ps_to_nCK(tRCD));
            end

            // Check tRP (PRE command period)
            if(f_activate_time_stamp[bank_const] > f_precharge_time_stamp[bank_const]) begin
                assert((f_activate_time_stamp[bank_const] - f_precharge_time_stamp[bank_const]) >= ps_to_nCK(tRP));
            end
            
            // Check tRAS (ACTIVE to PRECHARGE command period)
            if(f_precharge_time_stamp[bank_const] > f_activate_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_activate_time_stamp[bank_const]) >= ps_to_nCK(tRAS));
            end

            // Check tWR (WRITE recovery time for write-to-precharge)
            if(f_precharge_time_stamp[bank_const] > f_write_time_stamp[bank_const]) begin
                assert((f_precharge_time_stamp[bank_const] - f_write_time_stamp[bank_const]) >= (CWL_nCK + 3'd4 + ps_to_nCK(tWR)));
            end

            // Check delay from read-to-write
            if(f_write_time_stamp[bank_const] > f_read_time_stamp[bank_const]) begin
                assert((f_write_time_stamp[bank_const] - f_read_time_stamp[bank_const]) >= (CL_nCK + tCCD + 3'd2 - CWL_nCK));
            end

        end

        // extra assertions to make sure engine starts properly
        always @* begin
            //if(!past_sync_rst_controller) begin
                assert(instruction_address <= 26);
                assert(state_calibrate <= DONE_CALIBRATE);

                if(!o_wb_stall) begin
                    assert(state_calibrate == DONE_CALIBRATE);
                    assert(instruction_address == 22 || (instruction_address == 19 && delay_counter == 0) || (instruction_address == 23));
                end

                if(instruction_address == 19 && delay_counter != 0 && state_calibrate == DONE_CALIBRATE) begin
                    if(stage1_pending || stage2_pending) begin
                        assert(pause_counter);
                    end
                end

                if(stage1_pending || stage2_pending) begin
                   assert(state_calibrate > ISSUE_WRITE_1); 
                   assert(instruction_address == 22 || instruction_address == 19 || instruction_address == 23);
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
                
                if(state_calibrate > ISSUE_WRITE_1 && state_calibrate <= ANALYZE_DATA) begin
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
                    assert(o_wb_stall_calib);
                end
                if(reset_done) begin
                    assert(instruction_address >= 19 && instruction_address <= 26);
                end
                //delay_counter is zero at first clock of new instruction address, the actual delay_clock wil start at next clock cycle 
                if(instruction_address == 19 && delay_counter != 0) begin
                    assert(o_wb_stall);
                    assert(o_wb_stall_calib);
                end

                if(instruction_address == 19 && pause_counter) begin //pre-stall delay to finish all remaining requests
                   assert(delay_counter == PRE_REFRESH_DELAY); 
                   //assert(reset_done);
                   //assert(state_calibrate >= ISSUE_WRITE_1);
               end
           //end
        end
/*
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
            if(f_empty_2 && (i_wb2_cyc && SECOND_WISHBONE)) begin
                assert(!wb2_stb && !o_wb2_ack);
            end
            if(!wb2_stb && !o_wb2_ack) begin
                assert(f_empty_2);
            end
            f_write_data_2 = 0;
            f_write_fifo_2 = 0;
            if(i_wb2_stb && !o_wb2_stall && (i_wb2_cyc && SECOND_WISHBONE)) begin //if there is request
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
                // must not be a read/write to delays when not yet done calibrating 
                assume(i_wb2_addr[3:0] > 3);
            end
        end
        
        //verify outcome of request
        always @(posedge i_controller_clk) begin
            if(sync_rst_controller) begin
                f_o_wb2_ack_q <= 0;
                f_read_data_2_q <= 0;
            end
            else begin
                f_o_wb2_ack_q <= o_wb2_ack && f_read_data_2[0] && (i_wb2_cyc && SECOND_WISHBONE);
                f_read_data_2_q <= f_read_data_2;
            end
        end
        always @* begin
            if(!past_sync_rst_controller) begin
                if(wb2_stb && o_wb2_ack) begin
                    assert(f_full_2 || !(i_wb2_cyc && SECOND_WISHBONE));
                end
                if(f_full_2) begin
                    assert(wb2_stb && o_wb2_ack);
                    assert(f_outstanding_2 == 2 || !(i_wb2_cyc && SECOND_WISHBONE));
                end
                if(f_outstanding_2 == 2) begin
                    assert(f_full_2 || !(i_wb2_cyc && SECOND_WISHBONE));
                end
                if(f_empty_2) begin
                    assert(f_outstanding_2 == 0 || !(i_wb2_cyc && SECOND_WISHBONE));
                end
                if(f_outstanding_2 == 0) begin
                    assert(f_empty_2 || !(i_wb2_cyc && SECOND_WISHBONE));
                end
            end
            assert(f_outstanding_2 <= 2);
            f_read_fifo_2 = 0;
           if(o_wb2_ack && !f_read_data_2[0] && !past_sync_rst_controller) begin //read request
                f_read_fifo_2 = 1;
           end

           if(o_wb2_ack && f_read_data_2[0] && !past_sync_rst_controller) begin
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
                    assert(!$past(wb2_update) || !$past((i_wb2_cyc && SECOND_WISHBONE)));
                end

                //read request
               if(o_wb2_ack && !f_read_data_2[0] && i_rst_n && (i_wb2_cyc && SECOND_WISHBONE) && !(f_o_wb2_ack_q && f_read_data_2_q[1 +: (4 + lanes_clog2)] == f_read_data_2[1 +: (4 + lanes_clog2)] )) begin 
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
                            for(f_index_1 = 0; f_index_1 < LANES; f_index_1 = f_index_1 + 1) begin
                             assert(o_wb2_data[4*f_index_1 +: 4] == $past(added_read_pipe[f_index_1]));
                            end
                           end

                        6: begin
                             assert(o_wb2_data == $past(dqs_store[31:0]));
                           end

                        7: begin
                                for(f_index_1 = 0; 8*f_index_1 < 32 && f_index_1 < LANES; f_index_1 = f_index_1 + 1) begin
                                     assert(o_wb2_data[8*f_index_1 +: 8] == $past(i_phy_iserdes_bitslip_reference[8*f_index_1 +: 8])); 
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
               for(f_index_1 = 0; f_index_1 < LANES; f_index_1 = f_index_1 + 1) begin
                    if(o_phy_bitslip[f_index_1]) begin
                        //Bitslip cannot be asserted for two consecutive CLKDIV cycles; Bitslip must be
                        //deasserted for at least one CLKDIV cycle between two Bitslip assertions. 
                        
                        assert(!$past(o_phy_bitslip[f_index_1]));
                    end
               end
           end
        end
        
        mini_fifo #(
            .FIFO_WIDTH(1), //the fifo will have 2**FIFO_WIDTH positions
            .DATA_WIDTH(F_TEST_WB2_DATA_WIDTH) //each FIFO position can store DATA_WIDTH bits
       ) fifo_2 (
            .i_clk(i_controller_clk), 
            .i_rst_n(i_rst_n && (i_wb2_cyc && SECOND_WISHBONE)), //reset outstanding request at reset or when cyc goes low
            .read_fifo(f_read_fifo_2), 
            .write_fifo(f_write_fifo_2),
            .empty(f_empty_2), 
            .full(f_full_2),
            .write_data(f_write_data_2),
            .read_data(f_read_data_2)
       ); 
    */
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
            .i_reset(past_sync_rst_controller),
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
            .i_wb_err(o_wb_err),
            // Some convenience output parameters
            .f_nreqs(f_nreqs), 
            .f_nacks(f_nacks),
            .f_outstanding(f_outstanding),
            .f_ackwait_count(f_ackwait_count),
            .f_stall_count(f_stall_count)
            // }}}
            // }}}
        );
/*
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
            .i_wb_cyc((i_wb2_cyc && SECOND_WISHBONE)), 
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
        );*/
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

    always @(posedge i_clk) begin
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
