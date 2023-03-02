// Background:
// This DDR3 controller will be used with a DDR3-1600 with Kintex 7 FPGA Board (XC7K160T-3FFG676E). 
// The goal will be to:
//	- Run this at 1600Mbps (Maximum Physical Interface (PHY) Rate for a 4:1 
//			memory controller based on "DC and AC Switching Characteristics" for Kintex 7)
//	- Parameterize everything
//	- Interface should be (nearly) bus agnostic	  
//	- High (sustained) data throughput. Sequential writes should be able to continue without interruption 

`default_nettype none

`define DDR3_1600_11_11_11 // DDR3-1600 (11-11-11) speed bin

`define RAM_1Gb //DDR3 Capacity
//`define RAM_2Gb 
//`define RAM_4Gb 
//`define RAM_8Gb

`define x8 //DDR3 organization (DQ bus width) 
//`define x4
//`define x16


module ddr3_controller #( 
	parameter LANES = 8, //8 lanes of DQ
	parameter OPT_LOWPOWER = 1, //1 = low power, 0 = low logic
	parameter OPT_BUS_ABORT = 1  //1 = can abort bus, 0 = no abort (i_wb_cyc will be ignored, ideal for an AXI implementation which cannot abort transaction)(
	) 
	(
		i_clk, i_rst_n, 
	// Wishbone inputs
		i_wb_cyc, 
		i_wb_stb, 
		i_wb_we, 
		i_wb_addr, 
		i_wb_data, 
		i_wb_sel,
		i_aux,
	// Wishbone outputs
		o_wb_ack,
		o_wb_stall,
		o_wb_data, 
		o_aux
	// PHY Interface (to be added later)
	////////////////////////////////////
);

	`include "ddr3_parameters.vh"
	
	input wire i_clk, i_rst_n; //200MHz input clock
	// Wishbone inputs
	input wire i_wb_cyc; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
	input wire i_wb_stb; //request a transfer
	input wire i_wb_we; //write-enable (1 = write, 0 = read)
	input wire[ADDR_BITS - 3 - 1:0] i_wb_addr; //{row, bank, col>>3}, this is WORD-ADRESSABLE (burst of 8 sequential address in 1 transaction)
	input wire[DQ_BITS*LANES*8 - 1:0] i_wb_data; //write data, 8 times the number of pins on the device (4:1 memory controller means 8 DDR transactions per controller clock)
	input wire[(DQ_BITS*LANES*8)/8 - 1:0] i_wb_sel; //byte strobe for write (1 = write the byte)
	input wire i_aux; //for AXI-interface compatibility (given upon strobe)
	// Wishbone outputs
	output reg o_wb_ack; //1 = read/write request has completed
	output reg o_wb_stall; //1 = busy, cannot accept requests
	output reg[DQ_BITS*LANES*8 - 1:0] o_wb_data; //read data, 8 times the number of pins on the device (4:1 memory controller means 8 DDR transactions per controller clock)
	output reg o_aux;//for AXI-interface compatibility (returned upon ack)
	
	
	//////////////////////////////////////////////////////// RESET and Initialization Procedure (JEDEC DDR3 doc pg. 19) ////////////////////////////////////////////////////////
	
	//This reset and initialization process is designed for simplicity. This uses a Read-Only Memory (ROM)) 
	//to store the {ddr3ddr3_commands,time_delay(19:0)}. The output is registered to 
	reg[31:0] reset_initialization_rom[15:0];
	
	initial begin						//{ { use-timer , stay-command , cke , reset_n } , CMD , TIMER or MRS}
		reset_initialization_rom[0] = {4'b1100 , CMD_NOP , ns_to_cycles(INITIAL_RESET_HIGH)};  
		//1. RESET# needs to be maintained for minimum 200 us with stable power. CKE is pulled
			//“Low” anytime before RESET# being de-asserted (min. time 10 ns). .
		
		reset_initialization_rom[1] = {4'b1101 , CMD_NOP, ns_to_cycles(INITIAL_CKE_LOW)}; 
		//2. After RESET# is de-asserted, wait for another 500 us until CKE becomes active. During this time, the
			//DRAM will start internal state initialization; this will be done independently of external clocks. 
			// .... Also, a NOP or Deselect command must be registered (with tIS set up time to clock) before
			//CKE goes active.

		reset_initialization_rom[2] = {4'b1111 , CMD_NOP, ns_to_cycles(TXPR)}; 
		//3. After CKE is being registered high, wait minimum of Reset CKE Exit time, tXPR.
		
		reset_initialization_rom[3] = {4'b0011, CMD_MRS, MR2[18:0]}; 
		//4. Delay of TMRD between MRS commands is 4nCK (DDR3 clock cycle). In a 4:1 controller, this is just a 1 clock cycle delay thus no delay is actually needed.
		
		
	end
	
	//notes:
	//ODT must be statically held low at all times (except for write of course) when RTT_NOM is enabled via MR1.
	
	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	
	//convert nanoseconds time input to number of clock cycles (referenced to CONTROLLER_CLK_PERIOD)
	function [18:0] ns_to_cycles (input[19:0] ns); 
		ns_to_cycles = $ceil(ns/CONTROLLER_CLK_PERIOD);
	endfunction


`ifdef	FORMAL


`endif
endmodule

