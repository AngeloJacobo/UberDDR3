////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pktarbiter.v
// {{{
// Project:	10Gb Ethernet switch
//
// Purpose:	A simple arbiter.  Has nothing to do with packets really.  Takes
//		a series of requests for access, and provides that only one
//	has said access in a round robin fashion.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) (None)
// {{{
// The algorithm described in this file was copied from a stack overflow
// article:
//
//	https://stackoverflow.com/questions/55015328/understanding-a-simple-round-robin-arbiter-verilog-code
//
// The formal properties, if present, are Copyright (C) 2021, Gisselquist
// Technology, LLC, and proprietary to Gisselquist Technology.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module pktarbiter #(
		parameter	W = 4
	) (
		// {{{
		input	wire		i_clk, i_reset_n,
		input	wire	[W-1:0]	i_req,		// Incoming request
		input	wire		i_stall,	// Request is busy
		output	wire	[W-1:0]	o_grant		// Outgoing grant/access
		// }}}
	);

	// Declarations
	// {{{
	wire	[2*W-1:0]	w_req;
	wire	[2*W-1:0]	w_grant;
	wire	[W-1:0]		new_grant;
	wire	[2*W-1:0]	req_diff;
	reg	[W-1:0]		last, grant;
	// }}}

	assign	w_req   = { i_req, i_req };
	assign	req_diff = w_req - { {(W){1'b0}}, last };
	assign	w_grant = w_req & ~req_diff;
	assign	new_grant = w_grant[W-1:0] | w_grant[2*W-1:W];

	// o_grant, grant and last
	// {{{
	always @(posedge i_clk)
	if (!i_reset_n)
	begin
		grant <= 0;
		last  <= 1;
	end else if (grant == 0 || !i_stall)
	begin
		grant <= new_grant;
		if (last == 0)
			last <= 1;
		if (i_req != 0)
			last <= { new_grant[W-2:0], new_grant[W-1] };
	end

	assign	o_grant = grant;
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Declarations
	// {{{
	reg	f_past_valid;
	wire	[W-1:0]	not_granted;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!i_reset_n);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	not_granted = (i_stall) ? {(W){1'b1}} : (i_req & (~o_grant));

	always @(posedge i_clk)
	if (!i_reset_n || $past(!i_reset_n))
	begin
		assume(i_req == 0);
	end else
		assume((i_req & $past(not_granted)) == $past(not_granted));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (i_reset_n)
		assert($onehot(last));

	always @(*)
	if (i_reset_n)
		assert($onehot0(o_grant));

	always @(posedge i_clk)
	if (i_reset_n && $past(i_reset_n))
	begin
		if ($past(i_req) != 0)
			assert($onehot(o_grant));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[$clog2(W+2)-1:0]	cvr_count;

	always @(posedge i_clk or negedge i_reset_n)
	if (!i_reset_n)
		cvr_count <= 0;
	else if (&i_req)
		cvr_count <= cvr_count + 1;

	always @(*)
		cover(i_reset_n && (&cvr_count));

	// }}}
`endif
// }}}
endmodule
