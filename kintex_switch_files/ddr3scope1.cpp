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
      assign o_debug1 = {debug_trigger, o_wb2_stall, lane[2:0], dqs_start_index_stored[2:0], dqs_target_index[2:0], delay_before_read_data[2:0], 
                o_phy_idelay_dqs_ld[lane], state_calibrate[4:0], dqs_store[11:0]};
        */
        register_trace("o_wb2_stall",1,30);     
		register_trace("lane",3,27);
		register_trace("dqs_start_index_stored",3,24);
		register_trace("dqs_target_index",3,21);
		register_trace("delay_before_read_data",3,18);
		register_trace("o_phy_idelay_dqs_ld",1,17);
		register_trace("state_calibrate",5,12);
		register_trace("dqs_store",12,0);
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
