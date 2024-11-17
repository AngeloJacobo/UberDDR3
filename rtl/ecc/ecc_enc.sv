/////////////////////////////////////////////////////////////////////
//   ,------.                    ,--.                ,--.          //
//   |  .--. ' ,---.  ,--,--.    |  |    ,---. ,---. `--' ,---.    //
//   |  '--'.'| .-. |' ,-.  |    |  |   | .-. | .-. |,--.| .--'    //
//   |  |\  \ ' '-' '\ '-'  |    |  '--.' '-' ' '-' ||  |\ `--.    //
//   `--' '--' `---'  `--`--'    `-----' `---' `-   /`--' `---'    //
//                                             `---'               //
//   Error Correction and Detection Encoder                        //
//   Parameterized Extended Hamming Code Encoder                   //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//             Copyright (C) 2017 ROA Logic BV                     //
//             www.roalogic.com                                    //
//                                                                 //
//   This source file may be used and distributed without          //
//   restriction provided that this copyright statement is not     //
//   removed from the file and that any derivative work contains   //
//   the original copyright notice and the associated disclaimer.  //
//                                                                 //
//      THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY        //
//   EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     //
//   TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS     //
//   FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR OR     //
//   CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,  //
//   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT  //
//   NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;  //
//   LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)      //
//   HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN     //
//   CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR  //
//   OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS          //
//   SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  //
//                                                                 //
/////////////////////////////////////////////////////////////////////

// +FHDR -  Semiconductor Reuse Standard File Header Section  -------
// FILE NAME      : ecc_enc.sv
// DEPARTMENT     :
// AUTHOR         : rherveille
// AUTHOR'S EMAIL :
// ------------------------------------------------------------------
// RELEASE HISTORY
// VERSION DATE        AUTHOR      DESCRIPTION
// 1.0     2017-04-07  rherveille  initial release
// ------------------------------------------------------------------
// KEYWORDS : HAMMING ERROR CORRECTION ENCODER                 
// ------------------------------------------------------------------
// PURPOSE  : Adds ECC bits to incoming data
// ------------------------------------------------------------------
// PARAMETERS
//  PARAM NAME        RANGE  DESCRIPTION              DEFAULT UNITS
//  K                 1+     Information vector size  8
//  P0_LSB            0,1    0: p0 located at MSB     1
//                           1: p0 located at LSB
// ------------------------------------------------------------------
// REUSE ISSUES 
//   Reset Strategy      : none
//   Clock Domains       : none
//   Critical Timing     :
//   Test Features       : na
//   Asynchronous I/F    : yes
//   Scan Methodology    : na
//   Instantiations      : none
//   Synthesizable (y/n) : Yes
//   Other               :                                         
// -FHDR-------------------------------------------------------------


//-----------------------------------------------------------------------------
// Hamming codes can detect and correct a single bit error.
// An extended Hamming code allows detection of double bit errors and
// correction of single bit errors.
// This is called SECDED; Single Error Correction, Double Error Detection
//
// Number of bits required by a Hamming code: n = m + k
// n = code length
// m = number of check bits
// k = number of information bits
//
// Information, parity, and syndrome expressed as vectors:
// u = Information bit vector
// p = Parity check bit vector
// s = Syndrome vector
//
// The parity vector is encoded in 'n'.
// The information bit vector is part of 'p'
// The syndrome vector needs to be calculated.
//
// Bits required:
// p ranges from 0 to m+k; or p_range=m+k+1
// As a result 2^m >= m+k+1
//-----------------------------------------------------------------------------


module ecc_enc #(
  parameter K       = 8, //Information bit vector size
  parameter P0_LSB  = 1, //0: p0 is located at MSB
                         //1: p0 is located at LSB

  //these should be localparams
  parameter m = calculate_m(K),
  parameter n = m + K
)
(
  input  [K-1:0] d_i,      //information bit vector input
  output [n  :0] q_o,      //encoded data word output

  output [m  :1] p_o,      //parity vector output
  output         p0_o      //extended parity bit
);


//---------------------------------------------------------
// Functions
//---------------------------------------------------------
function integer calculate_m;
  input integer k;

  integer m_local;
begin
  m_local=1;
  while (2**m_local < m_local+k+1) m_local++;

  calculate_m = m_local;
end
endfunction //calculate_m


function [n:1] store_dbits_in_codeword;
  input [K-1:0] d;

  integer bit_idx, cw_idx;
begin
    //This function puts the information bits vector in the correct location
    //Information bits are stored in non-power-of-2 locations

    //clear all bits
    store_dbits_in_codeword = 0;

    bit_idx=0; //information vector bit index
    for (cw_idx=1; cw_idx<=n; cw_idx++)
      if (2**$clog2(cw_idx) != cw_idx) 
        /* verilator lint_off UNUSEDSIGNAL */
        store_dbits_in_codeword[cw_idx] = d[bit_idx++];
        /* verilator lint_on UNUSEDSIGNAL */
end
endfunction //store_dbits_in_codeword


function [m:1] calculate_p;
  input [n:1] cw;

  integer p_idx, cw_idx;
begin
    //clear p
    calculate_p = 0;

    for (p_idx =1; p_idx <=m; p_idx++)  //parity-index
    for (cw_idx=1; cw_idx<=n; cw_idx++) //codeword-index
      if (|(2**(p_idx-1) & cw_idx)) calculate_p[p_idx] = calculate_p[p_idx] ^ cw[cw_idx];
end
endfunction //calculate_p


function [n:1] store_p_in_codeword;
  input [n:1] cw;
  input [m:1] p;

  integer i;
begin
    //databits don't change ... copy into codeword
    store_p_in_codeword = cw;

    //put parity vector at power-of-2 locations
    for (i=1; i<=m; i=i+1)
      store_p_in_codeword[2**(i-1)] = p[i];
end
endfunction //store_p_in_codeword


//---------------------------------------------------------
// Variables
//---------------------------------------------------------
logic [n:1] cw_w_dbits; //codeword with loaded data bits
logic [n:1] cw;         //codeword with information + parity bits
  

//---------------------------------------------------------
// Module Body
//---------------------------------------------------------

/*
  Below diagram indicates the locations of the parity and data bits
  in the final 'p' vector.
  It also shows what databits each parity bit operates on

    1  2  3  4  5  6  7  8  9 10 11 12 13  14  15
   p1 p2 d1 p4 d2 d3 d4 p8 d5 d6 d7 d8 d9 d10 d11
p1  x     x     x     x     x     x     x       x
p2     x  x        x  x        x  x         x   x
p4           x  x  x  x              x  x   x   x
p8                       x  x  x  x  x  x   x   x
*/

//Step 1: Load all databits in codeword
assign cw_w_dbits = store_dbits_in_codeword(d_i);

//Step 2: Calculate p-vector
assign p_o = calculate_p(cw_w_dbits);

//Step 3: Store p-vector in codeword
assign cw = store_p_in_codeword(cw_w_dbits, p_o);

//Step 4: Calculate p0 (extended parity bit)
//        and store it in the codeword
assign p0_o = ^cw;
assign q_o  = P0_LSB ? {cw,p0_o} : {p0_o,cw};

endmodule
