module top;
   reg clk;
   reg rst_n;
   
  initial
    begin
       clk = 0;
       rst_n = 0;
       // #30 rst_n = 1;
    end
   
   always
     #100 clk = ~ clk;

   
   Test localName(clk, rst_n);
endmodule
