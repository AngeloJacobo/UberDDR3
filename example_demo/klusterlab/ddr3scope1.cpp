////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	ddr3scope.cpp
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file decodes the debug bits produced by the SMI IP and
//		stored in a (compressed) WB scope.  It is useful for determining
//	if the SMI IP is working, or even if/how the RPi is toggling the
//	associated SMI bits.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023, Gisselquist Technology, LLC
// {{{
// This file is part of the ETH10G project.
//
// The ETH10G project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, files
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_DDR3SCOPE1
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_DDR3SCOPE1
#define	WBSCOPEDATA	R_DDR3SCOPE1D

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	DDR3SCOPE1 : public SCOPE {
public:
	DDR3SCOPE1(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~DDR3SCOPE1(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger;

		trigger  = (val>>31)&1;

		printf("%6s", (trigger) ? "TRIGGERED at state_calibrate == MPR_READ! ":"");
	}

	virtual	void	define_traces(void) {
        /*
       assign o_debug1 = {debug_trigger, 2'b00, delay_before_read_data[3:0] ,i_phy_idelayctrl_rdy, lane[2:0], dqs_start_index_stored[4:0], 
        dqs_target_index[4:0], instruction_address[4:0], state_calibrate[4:0], o_wb2_stall};    
        
        register_trace("delay_before_read_data",4,25);     
		register_trace("i_phy_idelayctrl_rdy",1,24);
		register_trace("lane",3,21);
		register_trace("dqs_start_index_stored",5,16);
		register_trace("dqs_target_index",5,11);
		register_trace("instruction_address",5,6);
		register_trace("state_calibrate",5,1);
		register_trace("o_wb2_stall",1,0);
		*/
		/*
		 assign o_debug1 = {debug_trigger,stage1_we,stage1_col[5:0],stage1_data[7:0],stage1_dm[15:0]};
		
		register_trace("stage1_we",1,30);
		register_trace("stage1_col",6,24);
		register_trace("stage1_data",8,16);
		register_trace("stage1_dm",16,0);
		*/
		/*
		    assign o_debug1 = {debug_trigger,i_phy_iserdes_dqs[7:0],state_calibrate[4:0], instruction_address[4:0],o_phy_idelay_dqs_ld,o_phy_idelay_data_ld,o_phy_odelay_data_ld,o_phy_odelay_dqs_ld,
             delay_before_read_data[2:0],delay_before_write_level_feedback[4:0],lane};
                 assign o_debug1 = {debug_trigger,i_phy_iserdes_dqs[7:0],state_calibrate[4:0], instruction_address[4:0],reset_from_wb2,
                        repeat_test, delay_before_read_data[2:0], delay_before_write_level_feedback[4:0],lane[2:0]};
         */ 
        register_trace("i_phy_iserdes_dqs",8,23);
        register_trace("state_calibrate",5,18);
        register_trace("instruction_address",5,13);
        register_trace("reset_from_wb2",1,12);
        register_trace("repeat_test",1,11);
        register_trace("delay_before_read_data",3,8);
        register_trace("delay_before_write_level_feedback",5,3);
        register_trace("lane",3,0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	DDR3SCOPE1 *scope = new DDR3SCOPE1(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("ddr3scope1.vcd");
	}
}

#endif
