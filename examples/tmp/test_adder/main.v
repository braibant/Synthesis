module top;
   reg clk;
   reg rst_n;
   
  initial
    begin
       $display ("%b %d", 4'b1000, 4'b1000);
       clk = 0;
       rst_n = 0;
       #60 rst_n = 1;
    end
   
   always
     #50 clk = ~ clk;

   
   Test localName(clk, rst_n);
endmodule
