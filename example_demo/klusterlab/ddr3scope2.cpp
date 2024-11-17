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

#ifndef	R_DDR3SCOPE2
int main(int argc, char **argv) {
	printf("This design was not built with a NET scope within it.\n");
}
#else

#define	WBSCOPE		R_DDR3SCOPE2
#define	WBSCOPEDATA	R_DDR3SCOPE2D

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	DDR3SCOPE2 : public SCOPE {
public:
	DDR3SCOPE2(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~DDR3SCOPE2(void) {}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger;

		trigger  = (val>>31)&1;

		printf("%6s", (trigger) ? "TRIGGERED at state_calibrate == MPR_READ! ":"");
	}

	virtual	void	define_traces(void) {
        /*
        assign o_debug2 = {debug_trigger, idelay_dqs_cntvaluein[lane][4:0], idelay_data_cntvaluein[lane][4:0], i_phy_iserdes_dqs[15:0], 
                o_phy_dqs_tri_control, o_phy_dq_tri_control,
                (i_phy_iserdes_data == 0), (i_phy_iserdes_data == {(DQ_BITS*LANES*8){1'b1}}), (i_phy_iserdes_data < { {(DQ_BITS*LANES*4){1'b0}}, {(DQ_BITS*LANES*4){1'b1}} } )
                }; 
        

		register_trace("idelay_dqs_cntvaluein",5,26);
		register_trace("idelay_data_cntvaluein",5,21);
		register_trace("i_phy_iserdes_dqs_lane1",8,13);
		register_trace("i_phy_iserdes_dqs_lane0",8,5);
		register_trace("o_phy_dqs_tri_control",1,4);
		register_trace("o_phy_dq_tri_control",1,3);
		register_trace("i_phy_iserdes_data_is_zero",1,2);
		register_trace("i_phy_iserdes_data_all_1s",1,1);
		register_trace("i_phy_iserdes_data_less_than_half",1,0);
		*/
		/*
		assign o_debug2 = {debug_trigger,i_phy_iserdes_data[62:32]};
		*/
		register_trace("i_phy_iserdes_data_62_32",31,0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	DDR3SCOPE2 *scope = new DDR3SCOPE2(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("ddr3scope2.vcd");
	}
}

#endif
