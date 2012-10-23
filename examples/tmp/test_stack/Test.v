module Test(clk, rst_n);
   input clk, rst_n;
   
   wire res;
   wire guard;
   
   Stack foo (clk, rst_n, guard, res);
   
   // always@(posedge clk)
   //   begin
   // 	$display("res: %b\tguard: %b", res, guard);	
   //   end
   
    


endmodule
