/////////////////////////////////////////////////////////////////////
//   ,------.                    ,--.                ,--.          //
//   |  .--. ' ,---.  ,--,--.    |  |    ,---. ,---. `--' ,---.    //
//   |  '--'.'| .-. |' ,-.  |    |  |   | .-. | .-. |,--.| .--'    //
//   |  |\  \ ' '-' '\ '-'  |    |  '--.' '-' ' '-' ||  |\ `--.    //
//   `--' '--' `---'  `--`--'    `-----' `---' `-   /`--' `---'    //
//                                             `---'               //
//   Error Correction and Detection Decoder                        //
//   Parameterized Extended Hamming Code Decoder                   //
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
// FILE NAME      : ecc_dec.sv
// DEPARTMENT     :
// AUTHOR         : rherveille
// AUTHOR'S EMAIL :
// ------------------------------------------------------------------
// RELEASE HISTORY
// VERSION DATE        AUTHOR      DESCRIPTION
// 1.0     2017-04-07  rherveille  initial release
// ------------------------------------------------------------------
// KEYWORDS : HAMMING ERROR CORRECTION DECODER                 
// ------------------------------------------------------------------
// PURPOSE  : Decodes Data and ECC bits from incoming data
//            Detects and corrects bit errors
// ------------------------------------------------------------------
// PARAMETERS
//  PARAM NAME        RANGE  DESCRIPTION              DEFAULT UNITS
//  K                 1+     Information vector size  8
//  LATENCY           0,1,2  0: No latency            0
//                           1: Registered outputs
//                           2: Registered inputs/outputs
//  P0_LSB            0,1    0: p0 located at MSB     1
//                           1: p0 located at LSB
// ------------------------------------------------------------------
// REUSE ISSUES 
//   Reset Strategy      : external asynchronous active low; rst_ni
//   Clock Domains       : 1, clk_i, rising edge
//   Critical Timing     :
//   Test Features       : na
//   Asynchronous I/F    : no
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

module ecc_dec #(
  parameter K       = 8, //Information bit vector size
  parameter LATENCY = 0, //0: no latency (combinatorial design)
                         //1: registered outputs
                         //2: registered inputs+outputs
  parameter P0_LSB  = 1, //0: p0 is located at MSB
                         //1: p0 is located at LSB

  //These should be localparams
  parameter m = calculate_m(K),
  parameter n = m + K
)
(
  /* verilator lint_off UNUSEDSIGNAL */
  //clock/reset ports (if LATENCY > 0)
  input              rst_ni,     //asynchronous reset
  input              clk_i,      //clock input
  input              clkena_i,   //clock enable input
  /* verilator lint_on UNUSEDSIGNAL */

  //data ports
  input      [n  :0] d_i,        //encoded code word input
  output reg [K-1:0] q_o,        //information bit vector output
  output reg [m  :0] syndrome_o, //syndrome vector output

  //flags
  output reg         sb_err_o,   //single bit error detected
  output reg         db_err_o,   //double bit error detected
  output reg         sb_fix_o    //repaired error in the information bits
);

//---------------------------------------------------------
// Functions
//---------------------------------------------------------
function integer calculate_m(input integer k);
  integer m_local;
begin
  m_local=1;
  while (2**m_local < m_local+k+1) m_local++;

  calculate_m = m_local;
end
endfunction //calculate_m


function [m:1] calculate_syndrome(input [n:0] cw);
  integer p_idx, cw_idx;
begin
    //clear syndrome
    calculate_syndrome = 0;

    for (p_idx =1; p_idx <=m; p_idx++)  //parity vector index
    for (cw_idx=1; cw_idx<=n; cw_idx++) //code-word index
      if (|(2**(p_idx-1) & cw_idx)) calculate_syndrome[p_idx] = calculate_syndrome[p_idx] ^ cw[cw_idx];
end
endfunction //calculate_syndrome


function [n:0] correct_codeword(input [n:0] cw, input [m:1] syndrome);
    /*
      Correct all bits, including parity bits and extended parity bit.
      This simplifies this section and keeps the logic simple.

      The parity-bits are not used when extracting the information bits vector.
      Dead-logic-removal gets rid of the generated logic for the parity bits.
    */

    //assign code word
    correct_codeword = cw;

    //then invert bit indicated by syndrome
    correct_codeword[syndrome] = ~correct_codeword[syndrome];
endfunction //correct_codeword


function [K-1:0] extract_q(input [n:0] cw);
  integer bit_idx, cw_idx;
begin
    //This function extracts the information bits vector from the codeword
    //information bits are stored in non-power-of-2 locations

    bit_idx=0; //information bit vector index
    for (cw_idx=1; cw_idx<=n; cw_idx++) //codeword index
      if (2**$clog2(cw_idx) != cw_idx)
        /* verilator lint_off UNUSEDSIGNAL */
        extract_q[bit_idx++] = cw[cw_idx];
        /* verilator lint_on UNUSEDSIGNAL */
end
endfunction //extract_q


function is_power_of_2(input [m:1] n_local);
    is_power_of_2 = (n_local & (n_local-1)) == 0;
endfunction


function information_error(input [m:1] syndrome);
begin
    //This function checks if an error was detected/corrected in the information bits
    information_error = |syndrome & !is_power_of_2(syndrome);
end
endfunction //information_error


//---------------------------------------------------------
// Variables 
//---------------------------------------------------------
wire          parity;      //full codeword parity check
logic         parity_reg;
wire  [m  :1] syndrome;    //bit error indication/location
logic [m  :1] syndrome_reg;
wire  [n  :0] cw_fixed;    //corrected code word
  
wire  [n  :0] d;
logic [n  :0] d_reg;
wire  [K-1:0] q;
wire          sb_err;
wire          db_err;
wire          sb_fix;

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

//Step 1: Locate Parity bit
assign d = P0_LSB ? d_i : {d_i[n-1:0],d_i[n]};

//Step 2: Calculate code word parity
assign parity = ^d;

//Step 3: Calculate syndrome
assign syndrome = calculate_syndrome(d);

//Step 4: Generate intermediate registers (if any)
generate
  if (LATENCY > 1)
  begin : gen_inter_reg_latency_g1
      always @(posedge clk_i or negedge rst_ni)
        if (!rst_ni)
        begin
            d_reg        <= {n+1{1'b0}};
            parity_reg   <= 1'b0;
            syndrome_reg <= {m{1'b0}};
        end
        else if (clkena_i)
        begin
            d_reg        <= d;
            parity_reg   <= parity;
            syndrome_reg <= syndrome;
        end
  end
  else
  begin : gen_inter_reg_latency_0
      assign d_reg        = d;
      assign parity_reg   = parity;
      assign syndrome_reg = syndrome;
  end
endgenerate

//Step 5: Correct erroneous bit (if any)
assign cw_fixed = correct_codeword(d_reg, syndrome_reg); 

//Step 6: Extract information bits vector
assign q = extract_q(cw_fixed);

//Step 7: Generate status flags
assign sb_err = (parity_reg & |syndrome_reg);
assign db_err = ~parity_reg & |syndrome_reg;
assign sb_fix =  parity_reg & |information_error(syndrome_reg);

//Step 8: Generate output registers (if required)
generate
  if (LATENCY > 0) 
  begin : gen_output_reg_latency_g0 //Generate output registers
      always @(posedge clk_i or negedge rst_ni)
        if (!rst_ni)
        begin
            q_o        <= {K{1'b0}};
            syndrome_o <= {m+1{1'b0}};
            sb_err_o   <= 1'b0;
            db_err_o   <= 1'b0;
            sb_fix_o   <= 1'b0;
        end
        else if (clkena_i)
        begin
            q_o        <= q;
            syndrome_o <= P0_LSB ? {syndrome_reg, parity_reg} : {parity_reg, syndrome_reg};
            sb_err_o   <= sb_err;
            db_err_o   <= db_err;
            sb_fix_o   <= sb_fix;
        end
  end

  else
  begin : gen_output_reg_latency_0//No output registers
      always_comb
      begin
          q_o        = q;
          syndrome_o = P0_LSB ? {syndrome_reg, parity_reg} : {parity_reg, syndrome_reg};
          sb_err_o   = sb_err;
          db_err_o   = db_err;
          sb_fix_o   = sb_fix;
      end
  end
endgenerate

endmodule
