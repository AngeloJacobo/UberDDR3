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

#ifndef	R_DDR3SCOPE3
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_DDR3SCOPE3
#define	WBSCOPEDATA	R_DDR3SCOPE3D

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	DDR3SCOPE3 : public SCOPE {
public:
	DDR3SCOPE3(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~DDR3SCOPE3(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger;

		trigger  = (val>>31)&1;

		printf("%6s", (trigger) ? "TRIGGERED at state_calibrate == MPR_READ! ":"");
	}

	virtual	void	define_traces(void) {
        /*
        assign o_debug3 = {debug_trigger, delay_before_write_level_feedback[4:0], odelay_data_cntvaluein[lane][4:0], odelay_dqs_cntvaluein[lane][4:0], 
            state_calibrate[4:0], prev_write_level_feedback, i_phy_iserdes_data[48], i_phy_iserdes_data[40], i_phy_iserdes_data[32], i_phy_iserdes_data[24]
            , i_phy_iserdes_data[16], i_phy_iserdes_data[8], i_phy_iserdes_data[0], lane[2:0] };
        
    
		register_trace("delay_before_write_level_feedback",5,26);
		register_trace("odelay_data_cntvaluein",5,21);
		register_trace("odelay_dqs_cntvaluein",5,16);
		register_trace("state_calibrate",5,11);
		register_trace("prev_write_level_feedback",1,10);
		
		register_trace("i_phy_iserdes_data_lane6",1,9);
		register_trace("i_phy_iserdes_data_lane5",1,8);
		register_trace("i_phy_iserdes_data_lane4",1,7);
		register_trace("i_phy_iserdes_data_lane3",1,6);
		register_trace("i_phy_iserdes_data_lane2",1,5);
		register_trace("i_phy_iserdes_data_lane1",1,4);
		register_trace("i_phy_iserdes_data_lane0",1,3);
		register_trace("lane",3,0);
		*/
		/*
		 assign o_debug3 = {debug_trigger, lane[2:0], delay_before_read_data[3:0], i_phy_iserdes_data[448 +: 3], i_phy_iserdes_data[384 +: 3], i_phy_iserdes_data[320 +: 3], 
                        i_phy_iserdes_data[256 +: 3], i_phy_iserdes_data[192 +: 3], i_phy_iserdes_data[128 +: 3], i_phy_iserdes_data[64 +: 3], i_phy_iserdes_data[0 +: 3]};
       
        register_trace("lane",3,28);
        register_trace("delay_before_read_data",4,24);
        register_trace("i_phy_iserdes_data_burst7",3,21);
		register_trace("i_phy_iserdes_data_burst6",3,18);
		register_trace("i_phy_iserdes_data_burst5",3,15);
		register_trace("i_phy_iserdes_data_burst4",3,12);
		register_trace("i_phy_iserdes_data_burst3",3,9);
		register_trace("i_phy_iserdes_data_burst2",3,6);
		register_trace("i_phy_iserdes_data_burst1",3,3);
		register_trace("i_phy_iserdes_data_burst0",3,0);
		*/
		/*
		assign o_debug3 = {debug_trigger, i_phy_iserdes_data[128 +: 7], i_phy_iserdes_data[128 +: 8], i_phy_iserdes_data[64 +: 8], i_phy_iserdes_data[0 +: 8]};
		

		register_trace("i_phy_iserdes_data_burst3",7,24);
		register_trace("i_phy_iserdes_data_burst2",8,16);
		register_trace("i_phy_iserdes_data_burst1",8,8);
		register_trace("i_phy_iserdes_data_burst0",8,0);
		*/
		/*
		assign o_debug3 = {debug_trigger,i_phy_iserdes_data[30:0]};
		*/
		register_trace("i_phy_iserdes_data_30_0",31,0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	DDR3SCOPE3 *scope = new DDR3SCOPE3(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("ddr3scope3.vcd");
	}
}

#endif
