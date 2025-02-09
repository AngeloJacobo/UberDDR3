// Define either TWO_LANES_x8 or EIGHT_LANES_x8
//`define TWO_LANES_x8
`define EIGHT_LANES_x8

`ifdef EIGHT_LANES_x8
  `ifdef TWO_LANES_x8
      ERROR: Display compilation error here
  `endif
  `define x8
`endif

`ifdef TWO_LANES_x8
  `define x16
`endif

// Check if neither is defined
`ifndef EIGHT_LANES_x8
  `ifndef TWO_LANES_x8
    ERROR: Display compilation error here
  `endif
`endif

`define den8192Mb
`define sg125
