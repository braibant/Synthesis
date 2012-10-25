module Test(clk, rst_n);
   input clk, rst_n;
   reg [3:0] a, b ;

   reg [3:0] s, t ;
   reg 		 p, g;
   
   wire [9:0] res;
   wire 	guard;
   
   always@(posedge clk)
     begin
	if(!rst_n)
	  begin 
	     a <= 0;
	     b <= 1;
	  end
	else
	  begin
	     {p,g,s,t} <= res;
	     #10
	     $display("begin");	     
             $display("a: %b;\tb: %b", a, b);
             $display("s: %b;\tt: %b;\tp: %b;\t g: %b", s,t,p,g);
	     $display("res: %b", res);
	     $display("guard: %b", guard);
	     $display("end");	     
	     a <= a + 1;
             if (a == 4'b1111)
		   b <= b << 1;	     
	     $stop;
	  end	    
     end
      
   always@(posedge clk)
     begin
	if(rst_n)
	  begin
	   
	  end
     end
   
    
   Adder foo (clk, rst_n, guard, res, a, b);


endmodule
