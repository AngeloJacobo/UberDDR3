////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	builddate.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	This file records the date of the last build.  Running "make"
//		in the main directory will create this file.  The `define found
//	within it then creates a version stamp that can be used to tell which
//	configuration is within an FPGA and so forth.
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
// }}}
`ifndef	DATESTAMP
`define DATESTAMP 32'h20230723
`define BUILDTIME 32'h00082055
`endif
//
