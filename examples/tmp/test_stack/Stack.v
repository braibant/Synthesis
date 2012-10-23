module Stack (clk, rst_n, guard, value);
   integer 	index; // Used for initialisations
   input 	clk;
   input 	rst_n;
   output 	guard;
   output [0:0] value;
   // state declarations
   reg [7:0] 	reg_0 [255:0];
   reg [7:0] 	reg_1 [255:0];
   reg [7:0] 	reg_2;
   reg [11:0] 	reg_3 [255:0];
   reg [7:0] 	reg_4;
   // bindings 
   wire 	wire0 = 0'b0;
   wire [7:0] 	wire1 = reg_4;
   wire [11:0] 	wire2 = reg_3[wire1];
   wire [3:0] 	wire3 = wire2[3:0];
   wire [3:0] 	wire4 = 4'b0;
   wire 	wire5 = wire3 == wire4;
   wire [7:0] 	wire6 = reg_2;
   wire [7:0] 	wire7 = wire2[11:4];
   wire [7:0] 	wire8 = 8'b1;
   wire [7:0] 	wire9 = wire6 + wire8;
   wire [7:0] 	wire10 = wire1 + wire8;
   wire [7:0] 	wire11 = reg_4;
   wire [11:0] 	wire12 = reg_3[wire11];
   wire [3:0] 	wire13 = wire12[3:0];
   wire [3:0] 	wire14 = 4'b1;
   wire 	wire15 = wire13 == wire14;
   wire [7:0] 	wire16 = wire12[11:4];
   wire [7:0] 	wire17 = reg_0[wire16];
   wire [7:0] 	wire18 = reg_2;
   wire [7:0] 	wire19 = wire18 + wire8;
   wire [7:0] 	wire20 = wire11 + wire8;
   wire [7:0] 	wire21 = reg_4;
   wire [11:0] 	wire22 = reg_3[wire21];
   wire [3:0] 	wire23 = wire22[3:0];
   wire [3:0] 	wire24 = 4'b10;
   wire 	wire25 = wire23 == wire24;
   wire [7:0] 	wire26 = reg_2;
   wire [7:0] 	wire27 = wire26 - wire8;
   wire [7:0] 	wire28 = reg_1[wire27];
   wire [7:0] 	wire29 = wire22[11:4];
   wire [7:0] 	wire30 = wire21 + wire8;
   wire 	wire31 = wire5 | wire15;
   wire [7:0] 	wire32 = reg_4;
   wire [11:0] 	wire33 = reg_3[wire32];
   wire [3:0] 	wire34 = wire33[3:0];
   wire [3:0] 	wire35 = 4'b11;
   wire 	wire36 = wire34 == wire35;
   wire [7:0] 	wire37 = reg_2;
   wire [7:0] 	wire38 = wire37 - wire8;
   wire [7:0] 	wire39 = reg_1[wire38];
   wire [7:0] 	wire40 = 8'b10;
   wire [7:0] 	wire41 = wire37 - wire40;
   wire [7:0] 	wire42 = reg_1[wire41];
   wire [7:0] 	wire43 = wire42 + wire39;
   wire [7:0] 	wire44 = wire32 + wire8;
   wire 	wire45 = wire31 | wire25;
   wire [7:0] 	wire46 = reg_4;
   wire [11:0] 	wire47 = reg_3[wire46];
   wire [3:0] 	wire48 = wire47[3:0];
   wire [3:0] 	wire49 = 4'b100;
   wire 	wire50 = wire48 == wire49;
   wire [7:0] 	wire51 = reg_2;
   wire [7:0] 	wire52 = wire51 - wire8;
   wire [7:0] 	wire53 = reg_1[wire52];
   wire [7:0] 	wire54 = wire51 - wire40;
   wire [7:0] 	wire55 = reg_1[wire54];
   wire [7:0] 	wire56 = wire55 - wire53;
   wire [7:0] 	wire57 = wire46 + wire8;
   wire 	wire58 = wire45 | wire36;
   wire [7:0] 	wire59 = reg_4;
   wire [11:0] 	wire60 = reg_3[wire59];
   wire [3:0] 	wire61 = wire60[3:0];
   wire [3:0] 	wire62 = 4'b101;
   wire 	wire63 = wire61 == wire62;
   wire [7:0] 	wire64 = wire59 + wire8;
   wire [7:0] 	wire65 = wire60[11:4];
   wire [7:0] 	wire66 = wire64 + wire65;
   wire 	wire67 = wire58 | wire50;
   wire [7:0] 	wire68 = reg_4;
   wire [11:0] 	wire69 = reg_3[wire68];
   wire [3:0] 	wire70 = wire69[3:0];
   wire [3:0] 	wire71 = 4'b110;
   wire 	wire72 = wire70 == wire71;
   wire [7:0] 	wire73 = wire68 + wire8;
   wire [7:0] 	wire74 = wire69[11:4];
   wire [7:0] 	wire75 = wire73 - wire74;
   wire 	wire76 = wire67 | wire63;
   wire [7:0] 	wire77 = reg_4;
   wire [11:0] 	wire78 = reg_3[wire77];
   wire [3:0] 	wire79 = wire78[3:0];
   wire [3:0] 	wire80 = 4'b111;
   wire 	wire81 = wire79 == wire80;
   wire [7:0] 	wire82 = reg_2;
   wire [7:0] 	wire83 = wire82 - wire8;
   wire [7:0] 	wire84 = reg_1[wire83];
   wire [7:0] 	wire85 = wire82 - wire40;
   wire [7:0] 	wire86 = reg_1[wire85];
   wire 	wire87 = wire86 == wire84;
   wire [7:0] 	wire88 = wire77 + wire8;
   wire [7:0] 	wire89 = wire78[11:4];
   wire [7:0] 	wire90 = wire88 + wire89;
   wire 	wire91 = wire76 | wire72;
   wire [7:0] 	wire92 = reg_4;
   wire [11:0] 	wire93 = reg_3[wire92];
   wire [3:0] 	wire94 = wire93[3:0];
   wire [3:0] 	wire95 = 4'b1001;
   wire 	wire96 = wire94 == wire95;
   wire [7:0] 	wire97 = reg_2;
   wire [7:0] 	wire98 = wire97 - wire8;
   wire [7:0] 	wire99 = reg_1[wire98];
   wire [7:0] 	wire100 = wire97 - wire40;
   wire [7:0] 	wire101 = reg_1[wire100];
   wire 	wire102 = wire101 < wire99;
   wire 	wire103 = wire101 == wire99;
   wire 	wire104 = wire102 | wire103;
   wire [7:0] 	wire105 = wire92 + wire8;
   wire [7:0] 	wire106 = wire93[11:4];
   wire [7:0] 	wire107 = wire105 + wire106;
   wire 	wire108 = wire91 | wire81;
   wire [7:0] 	wire109 = reg_4;
   wire [11:0] 	wire110 = reg_3[wire109];
   wire [3:0] 	wire111 = wire110[3:0];
   wire [3:0] 	wire112 = 4'b1010;
   wire 	wire113 = wire111 == wire112;
   wire [7:0] 	wire114 = reg_2;
   wire [7:0] 	wire115 = wire114 - wire8;
   wire [7:0] 	wire116 = reg_1[wire115];
   wire [7:0] 	wire117 = wire114 - wire40;
   wire [7:0] 	wire118 = reg_1[wire117];
   wire 	wire119 = wire116 < wire118;
   wire [7:0] 	wire120 = wire109 + wire8;
   wire [7:0] 	wire121 = wire110[11:4];
   wire [7:0] 	wire122 = wire120 + wire121;
   wire 	wire123 = wire108 | wire96;
   wire 	wire124 = 1'b0;
   wire [7:0] 	wire125 = reg_4;
   wire [11:0] 	wire126 = reg_3[wire125];
   wire [3:0] 	wire127 = wire126[3:0];
   wire [3:0] 	wire128 = 4'b1011;
   wire 	wire129 = wire127 == wire128;
   wire 	wire130 = 1'b1;
   wire 	wire131 = wire123 | wire113;
   wire 	wire132 = wire131 ? wire124 : wire130;
   wire 	wire133 = wire131 | wire129;
   wire 	wire134 = wire31 & wire5;
   wire 	wire135 = ~ wire5;
   wire 	wire136 = wire135 & wire15;
   wire [7:0] 	wire137 = wire134 ? wire6 : wire18;
   wire [7:0] 	wire138 = wire134 ? wire7 : wire17;
   wire [7:0] 	wire139 = wire134 ? wire9 : wire19;
   wire [7:0] 	wire140 = wire134 ? wire10 : wire20;
   wire 	wire141 = ~ wire31;
   wire 	wire142 = wire141 & wire25;
   wire [7:0] 	wire143 = wire31 ? wire139 : wire27;
   wire [7:0] 	wire144 = wire31 ? wire140 : wire30;
   wire 	wire145 = ~ wire45;
   wire 	wire146 = wire145 & wire36;
   wire 	wire147 = wire31 | wire146;
   wire [7:0] 	wire148 = wire31 ? wire137 : wire41;
   wire [7:0] 	wire149 = wire31 ? wire138 : wire43;
   wire [7:0] 	wire150 = wire45 ? wire143 : wire38;
   wire [7:0] 	wire151 = wire45 ? wire144 : wire44;
   wire 	wire152 = ~ wire58;
   wire 	wire153 = wire152 & wire50;
   wire 	wire154 = wire147 | wire153;
   wire [7:0] 	wire155 = wire147 ? wire148 : wire54;
   wire [7:0] 	wire156 = wire147 ? wire149 : wire56;
   wire [7:0] 	wire157 = wire58 ? wire150 : wire52;
   wire [7:0] 	wire158 = wire58 ? wire151 : wire57;
   wire 	wire159 = ~ wire67;
   wire 	wire160 = wire159 & wire63;
   wire [7:0] 	wire161 = wire67 ? wire158 : wire66;
   wire 	wire162 = ~ wire76;
   wire 	wire163 = wire162 & wire72;
   wire [7:0] 	wire164 = wire76 ? wire161 : wire75;
   wire 	wire165 = ~ wire91;
   wire 	wire166 = wire165 & wire81;
   wire 	wire167 = wire67 | wire166;
   wire [7:0] 	wire168 = wire67 ? wire157 : wire85;
   wire 	wire169 = wire166 & wire87;
   wire 	wire170 = wire91 | wire169;
   wire [7:0] 	wire171 = wire91 ? wire164 : wire90;
   wire 	wire172 = ~ wire87;
   wire 	wire173 = wire166 & wire172;
   wire [7:0] 	wire174 = wire170 ? wire171 : wire88;
   wire 	wire175 = ~ wire108;
   wire 	wire176 = wire175 & wire96;
   wire 	wire177 = wire167 | wire176;
   wire [7:0] 	wire178 = wire167 ? wire168 : wire100;
   wire 	wire179 = wire176 & wire104;
   wire 	wire180 = wire108 | wire179;
   wire [7:0] 	wire181 = wire108 ? wire174 : wire107;
   wire 	wire182 = ~ wire104;
   wire 	wire183 = wire176 & wire182;
   wire [7:0] 	wire184 = wire180 ? wire181 : wire105;
   wire 	wire185 = ~ wire123;
   wire 	wire186 = wire185 & wire113;
   wire 	wire187 = wire177 | wire186;
   wire [7:0] 	wire188 = wire177 ? wire178 : wire117;
   wire 	wire189 = wire186 & wire119;
   wire 	wire190 = wire123 | wire189;
   wire [7:0] 	wire191 = wire123 ? wire184 : wire122;
   wire 	wire192 = ~ wire119;
   wire 	wire193 = wire186 & wire192;
   wire [7:0] 	wire194 = wire190 ? wire191 : wire120;
   // effects 
   assign guard = wire133;
   assign value = wire132;
   always@(posedge clk)
     begin
	if(rst_n)
	  begin
	     // reset 
		end
	else
	  begin
	     $display  ("pc:%d\tsp:%d",reg_4,reg_2);
	     $display  ("code at pc:%b",reg_3[reg_4]);
	     $display  ("opcode:%b", wire2[3:0]);
	     $display  ("guard: %b, value: %b", guard, value);
	     for (index = 0; index < 8; index = index + 1)
	       begin 
		  $display  ("stack[%d]: %d",index, reg_1[index]);
	       end
	     for (index = 0; index < 8; index = index + 1)
	       begin 
		  $display  ("regs [%d]: %d",index, reg_0[index]);
	       end
	     if (wire2[3:0] == 4'b1011)
	       begin
		  $stop;
	       end
	     // put  debug code here (display, stop, ...)
	     if(wire131) reg_4 <= wire194;
	     if(wire187) reg_2 <= wire188;
	     if(wire154) reg_1[wire155] <= wire156;
	     if(wire142) reg_0[wire29] <= wire28;
	  end
     end
   
   initial
     begin
	for(index = 0; index < 255; index = index + 1)
	  begin
	     reg_0 [index] <= 0;
	     reg_1 [index] <= 0;
	  end
	reg_2 <= 0;
	reg_4 <= 0;
        reg_3[0] = 12'b000010100000;
	reg_3[1] = 12'b000000100000;
	reg_3[2] = 12'b000001101010;
	reg_3[3] = 12'b000010100000;
	reg_3[4] = 12'b000000100000;
	reg_3[5] = 12'b000000110111;
	reg_3[6] = 12'b000010100000;
	reg_3[7] = 12'b000000000010;
	reg_3[8] = 12'b000000000101;
	reg_3[9] = 12'b000000000000;
	reg_3[10] = 12'b000000100010;
	reg_3[11] = 12'b000000010000;
	reg_3[12] = 12'b000000010010;
	reg_3[13] = 12'b000000010000;
	reg_3[14] = 12'b000001000010;
	reg_3[15] = 12'b000001000001;
	reg_3[16] = 12'b000010100000;
	reg_3[17] = 12'b000100001010;
	reg_3[18] = 12'b000001000001;
	reg_3[19] = 12'b000010100000;
	reg_3[20] = 12'b000011010111;
	reg_3[21] = 12'b000000010001;
	reg_3[22] = 12'b000000100001;
	reg_3[23] = 12'b000000000011;
	reg_3[24] = 12'b000000110010;
	reg_3[25] = 12'b000000010001;
	reg_3[26] = 12'b000000100010;
	reg_3[27] = 12'b000000110001;
	reg_3[28] = 12'b000000010010;
	reg_3[29] = 12'b000001000001;
	reg_3[30] = 12'b000000010000;
	reg_3[31] = 12'b000000000011;
	reg_3[32] = 12'b000001000010;
	reg_3[33] = 12'b000100110110;
	reg_3[34] = 12'b000000010001;
	reg_3[35] = 12'b000000000010;
	reg_3[36] = 12'b000000001011;
	for(index = 37; index < 255; index = index + 1)
	  begin
		      reg_3 [index] <= 0;
	  end	
     end

endmodule
