module Test(clk, rst_n);
  parameter width = 1;
  input clk, rst_n;
  reg [width-1:0] enqValReg;

  always@(posedge clk)
  begin
    if(!rst_n)
      enqValReg <= 0;
    else if(enqEn)
      enqValReg <= enqValReg + 1;
  end
  wire enqEn, deqEn, enqRdy, deqRdy;
  wire [width-1:0] deqVal, enqVal;

  assign enqEn = enqRdy;
  assign deqEn = deqRdy;
  assign enqVal = enqValReg;

  always@(posedge clk)
  begin
    if(rst_n)
      if(enqEn)
        $display("enqVal: %d", enqVal);
  end

  always@(posedge clk)
    if(rst_n)
      if(deqEn)
        $display("                       deqVal: %d", deqVal);

  Fifo#(width) localName (clk, rst_n, enqRdy, enqEn, enqVal, deqRdy, deqEn, deqVal);
endmodule
