module top;
  reg clk;
  reg rst_n;

  initial
  begin
    clk = 0;
    rst_n = 0;
    #40 rst_n = 1;
  end

  always
    #5 clk = ~ clk;

  parameter width = 32;

  Test#(width) localName(clk, rst_n);
endmodule
