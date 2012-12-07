module Test(clk, rst_n);
   input clk, rst_n;
   
   parameter size = 16;
   
   wire [63:0] isrc;
   reg [3:0] src [15:0];
   assign isrc = {src[15], src[14], src[13], src[12], src[11], src[10], src[9], src[8],
		  src[7], src[6], src[5], src[4], src[3], src[2], src[1], src[0]};
   
   wire [63:0] itgt;
   wire [3:0] tgt [15:0];
   assign {tgt[15], tgt[14], tgt[13], tgt[12], tgt[11], tgt[10], tgt[9], tgt[8],
	   tgt[7], tgt[6], tgt[5], tgt[4], tgt[3], tgt[2], tgt[1], tgt[0]} = itgt;
   
   wire guard;
   
   integer index; // Used for initialisations
   
   Sorter foo (clk, rst_n, guard, itgt, isrc);
   
   integer seed = 255;
   
   initial
     begin
	for(index = 0; index < size; index = index + 1)
	  begin
	     src[index] <= $random(seed);
	  end
     end
	
   always@(posedge clk)
     begin
	if(!rst_n)
	  begin 
	  end
	else
	  begin
	     // display the current input
	     $display("guard:%b", guard);
	     
	     $display("input\t%b\n", isrc);
	     for(index = 0; index < size; index = index + 1)
	       begin
		  $display("%d:\t%d\t(%b)", index, src[index], src[index]);		  
	       end
	     
	     $display("output\t%b\n", itgt);
	     for(index = 0; index < size; index = index + 1)
	       begin
		  $display("%d:\t%d\t(%b)", index, tgt[index], tgt[index]);		  
	       end	     
	     $stop;
	  end	    
     end
          


endmodule
