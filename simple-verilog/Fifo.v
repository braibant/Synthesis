

module Fifo
  ( clk
  , rst_n
  , enqRdy
  , enqEn
  , enqVal
  , deqRdy
  , deqEn
  , deqVal
  );
  parameter width = 1;

  input clk, rst_n;
  output enqRdy, deqRdy;
  input enqEn, deqEn;
  input [width-1:0] enqVal;
  output [width-1:0] deqVal;

  reg [width-1:0] data;
  reg valid;

  assign deqVal = data;
  assign enqRdy = !valid;
  assign deqRdy = valid;

  always@(posedge clk)
  begin
    if(!rst_n)
      valid <= 0;
    else
    begin
      if(enqEn)
      begin
        data <= enqVal;
        valid <= 1'b1;
      end
      else
        valid <= 1'b0;
    end
  end
endmodule
