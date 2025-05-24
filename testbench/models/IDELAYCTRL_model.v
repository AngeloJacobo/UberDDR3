`timescale 1 ns/1 ps

module IDELAYCTRL_model (
  output reg RDY,
  input REFCLK,
  input RST
);
  initial RDY = 0;
  always @(posedge RST) begin
    RDY <= 0;
  end
  always @(negedge RST) begin
    # 10; // 10ns delay before RDY assertion
    RDY <= 1;
  end

endmodule

