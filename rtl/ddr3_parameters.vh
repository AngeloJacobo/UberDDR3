// Some parameters are salvaged from Micron DDR3 Simulation Model Files ( https://www.micron.com/products/dram/ddr3-sdram/part-catalog/mt41k128m16jt-125 )


localparam CONTROLLER_CLK_PERIOD = 5.0; //200MHz controller clock (5ns)
localparam DDR3_CLK_PERIOD = 1.25; //800MHz DDR3 clock (1.25ns)
	
////////////////////////////////////////////////////////////// COMMAND PARAMETERS //////////////////////////////////////////////////////////////

//DDR3 commands {cs_n, ras_n, cas_n, we_n} (JEDEC DDR3 doc pg. 33 )
localparam[3:0] CMD_MRS = 4'b0000; // Mode Register Set
localparam[3:0] CMD_REF = 4'b0001; // Refresh
localparam[3:0] CMD_PRE = 4'b0010; // Precharge (A10-AP: 0 = Single Bank Precharge, 1 = Precharge All Banks)
localparam[3:0] CMD_ACT = 4'b0011; // Bank Activate
localparam[3:0] CMD_WR  = 4'b0100; // Write (A10-AP: 0 = no Auto-Precharge) (A12-BC#: 1 = Burst Length 8) 
localparam[3:0] CMD_RD  = 4'b0101; //Read  (A10-AP: 0 = no Auto-Precharge) (A12-BC#: 1 = Burst Length 8) 
localparam[3:0] CMD_NOP = 4'b0111; // No Operation
localparam[3:0] CMD_DES = 4'b1000; // Deselect command performs the same function as No Operation command (JEDEC DDR3 doc pg. 34 NOTE 11)
localparam[3:0] CMD_ZQC = 4'b0110; // ZQ Calibration (A10-AP: 0 = ZQ Calibration Short, 1 = ZQ Calibration Long)
	
localparam RST_USE_TIMER = 26; // Command bit that determines if timer will be used
localparam RST_STAY_COMMAND = 25; //Command bit that determines if command will last for entire timer duration (or if 
localparam RST_CKE = 24; //Control clock-enable input to DDR3
localparam RST_RESET_N = 23; //Control reset to DDR3


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////// SET MODE REGISTERS //////////////////////////////////////////////////////////////

localparam[2:0] PASR = 3'b000; //Partial Array Self-Refresh: Full Array
localparam[2:0] CWL = 3'b011; //CAS write Latency: 8 (1.5 ns > tCK(avg) >= 1.25 ns)
localparam ASR = 1'b1; //Auto Self-Refresh: on
localparam SRT = 1'b0; //Self-Refresh Temperature Range:0 (If ASR = 1, SRT bit must be set to 0)
localparam[1:0] RTT_WR = 2'b00; //Dynamic ODT: off
localparam[18:0] MR2 = {3'b010, 5'b00000, RTT_WR, 1'b0, SRT, ASR, CWL, PASR}; 

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

localparam INITIAL_RESET_HIGH 		= 		200_000; // 200us reset must be high at initialization
localparam INITIAL_CKE_LOW 		= 		500_000; // 500us cke must be low before activating

`ifdef DDR3_1600_11_11_11 //DDR3-1600 (11-11-11) speed bin
    localparam TRAS 	= 		35; // tRAS ns Minimum Active to Precharge command time
    localparam TRC 		= 		48.750; // tRC ns Active to Active/Auto Refresh command time
    localparam TRCD 	= 		13.750; // tRCD ns Active to Read/Write command time
    localparam TRP 		= 		13.750; // tRP ns Precharge command period
`endif

`ifdef RAM_1Gb
	localparam TRFC 		=			110;		// ns Refresh command  to ACT or REF 
`elsif RAM_2Gb
	localparam TRFC 		=			160;		// ns Refresh command  to ACT or REF 
`elsif RAM_4Gb
	localparam TRFC 		=			300;		// ns Refresh command  to ACT or REF 
`else
	localparam TRFC 			=		350;		// ns Refresh command  to ACT or REF 
`endif

localparam TXPR = max(5*DDR3_CLK_PERIOD,TRFC+10); // tXPR ns Exit Reset from CKE HIGH to a valid command
localparam TMRD = 4; // tMRD nCK Mode Register Set command cycle time

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////// I/O Interface Width //////////////////////////////////////////////////////////////

`ifdef RAM_1Gb
	`ifdef x4
		localparam DM_BITS      =           1;   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS    =          14 ;  // MAX Address Bits
		localparam ROW_BITS    =          14;   // Set this localparam to control how many Address bits are used
		localparam COL_BITS      =         11;   // Set this localparam to control how many Column bits are used
		localparam DQ_BITS       =          4 ;  // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS      =          1 ;  // Set this localparam to control how many Dqs bits are used
	`elsif x8
		localparam DM_BITS        =         1;   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS    =          14 ;  // MAX Address Bits
		localparam ROW_BITS    =           14;   // Set this localparam to control how many Address bits are used
		localparam COL_BITS    =           10;   // Set this localparam to control how many Column bits are used
		localparam DQ_BITS      =           8 ;  // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS    =           1;   // Set this localparam to control how many Dqs bits are used
	`else
		localparam DM_BITS       =          2;   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS     =         13 ;  // MAX Address Bits
		localparam ROW_BITS      =         13 ;  // Set this localparam to control how many Address bits are used
		localparam COL_BITS      =         10 ;  // Set this localparam to control how many Column bits are used
		localparam DQ_BITS        =        16;   // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS      =          2;   // Set this localparam to control how many Dqs bits are used
	`endif

`elsif RAM_2Gb
	`ifdef x4
		localparam DM_BITS        =         1 ;  // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS     =         15 ;  // MAX Address Bits
		localparam ROW_BITS     =          15;   // Set this localparam to control how many Address bits are used
		localparam COL_BITS     =          11;   // Set this localparam to control how many Column bits are used
		localparam DQ_BITS       =          4 ;  // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS    =            1 ;  // Set this localparam to control how many Dqs bits are used
	`elsif x8
		localparam DM_BITS      =           1   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS     =         15 ;  // MAX Address Bits
		localparam ROW_BITS    =           15;   // Set this localparam to control how many Address bits are used
		localparam COL_BITS     =          10 ;  // Set this localparam to control how many Column bits are used
		localparam DQ_BITS     =            8;   // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS    =            1 ;  // Set this localparam to control how many Dqs bits are used
	`else
		localparam x16
		localparam DM_BITS      =          2 ;  // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS      =        14 ;  // MAX Address Bits
		localparam ROW_BITS       =        14 ;  // Set this localparam to control how many Address bits are used
		localparam COL_BITS     =          10 ;  // Set this localparam to control how many Column bits are used
		localparam DQ_BITS       =         16  ; // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS     =           2 ;  // Set this localparam to control how many Dqs bits are used
	`endif

`elsif RAM_4Gb
	`ifdef x4
		localparam DM_BITS      =           1;   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS     =         16 ;  // MAX Address Bits
		localparam ROW_BITS      =         16;   // Set this localparam to control how many Address bits are used
		localparam COL_BITS      =         11;   // Set this localparam to control how many Column bits are used
		localparam DQ_BITS        =         4;   // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS      =          1 ;  // Set this localparam to control how many Dqs bits are used
	`elsif x8
		localparam DM_BITS        =         1;   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS    =         16 ;  // MAX Address Bits
		localparam ROW_BITS     =          16 ;  // Set this localparam to control how many Address bits are used
		localparam COL_BITS       =        10;   // Set this localparam to control how many Column bits are used
		localparam DQ_BITS        =         8 ;  // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS     =           1 ;  // Set this localparam to control how many Dqs bits are used
	`else
		localparam x16
		localparam DM_BITS       =          2;   // Set this localparam to control how many Data Mask bits are used
		localparam ADDR_BITS      =        15 ;  // MAX Address Bits
		localparam ROW_BITS      =         15;   // Set this localparam to control how many Address bits are used
		localparam COL_BITS      =         10 ;  // Set this localparam to control how many Column bits are used
		localparam DQ_BITS        =        16;   // Set this localparam to control how many Data bits are used       **Same as part bit width**
		localparam DQS_BITS       =         2 ;  // Set this localparam to control how many Dqs bits are used
	`endif

`else
		`ifdef x4
			localparam DM_BITS         =        1 ;  // Set this localparam to control how many Data Mask bits are used
			localparam ADDR_BITS     =         16 ;  // MAX Address Bits
			localparam ROW_BITS       =        16;  // Set this localparam to control how many Address bits are used
			localparam COL_BITS       =        14;   // Set this localparam to control how many Column bits are used
			localparam DQ_BITS        =         4 ;  // Set this localparam to control how many Data bits are used       **Same as part bit width**
			localparam DQS_BITS      =          1 ;  // Set this localparam to control how many Dqs bits are used
		`elsif x8
			localparam DM_BITS      =           1 ;  // Set this localparam to control how many Data Mask bits are used
			localparam ADDR_BITS      =        16 ;  // MAX Address Bits
			localparam ROW_BITS     =          16 ;  // Set this localparam to control how many Address bits are used
			localparam COL_BITS       =        11;   // Set this localparam to control how many Column bits are used
			localparam DQ_BITS        =         8 ;  // Set this localparam to control how many Data bits are used       **Same as part bit width**
			localparam DQS_BITS      =          1 ;  // Set this localparam to control how many Dqs bits are used
		`else
			localparam DM_BITS      =          2;   // Set this localparam to control how many Data Mask bits are used
			localparam ADDR_BITS     =         16 ;  // MAX Address Bits
			localparam ROW_BITS      =         16;   // Set this localparam to control how many Address bits are used
			localparam COL_BITS       =        10;   // Set this localparam to control how many Column bits are used
			localparam DQ_BITS       =         16;   // Set this localparam to control how many Data bits are used       **Same as part bit width**
			localparam DQS_BITS       =        2 ;  // Set this localparam to control how many Dqs bits are used
		`endif
`endif
	
localparam BA_BITS      =           3 ;  // Set this parmaeter to control how many Bank Address bits are used
localparam AP          =           10 ;  // the address bit that controls auto-precharge and precharge-all
localparam BC           =          12;   // the address bit that controls burst chop



function integer max(input integer a, input integer b);
	if(a >= b) max = a;
	else	max = b;
endfunction

