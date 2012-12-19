module Cpu (clk, rst_n, guard, value);
integer index; // Used for initialisations
input clk;
input rst_n;
output guard;
output [-1:0] value;
// state declarations
reg [3:0] reg_0;
reg [3:0] reg_1 [3:0];
reg [12:0] reg_2 [15:0];
reg [3:0] reg_3 [15:0];
// bindings 
wire  wire0 = 0'b0;
wire  wire1 = 1'b1;
wire  wire2 = 1'b0;
wire [3:0] wire3 = reg_0;
wire [12:0] wire4 = reg_2[wire3];
wire [2:0] wire5 = wire4[2:0];
wire [2:0] wire6 = 3'b0;
wire  wire7 = wire5 == wire6;
wire [3:0] wire8 = 4'b1;
wire [3:0] wire9 = wire3 + wire8;
wire [1:0] wire10 = wire4[4:3];
wire [3:0] wire11 = wire4[12:9];
wire [12:0] wire12 = reg_2[wire3];
wire [2:0] wire13 = wire12[2:0];
wire [2:0] wire14 = 3'b1;
wire  wire15 = wire13 == wire14;
wire [1:0] wire16 = wire12[4:3];
wire [12:0] wire17 = reg_2[wire3];
wire [2:0] wire18 = wire17[2:0];
wire [2:0] wire19 = 3'b10;
wire  wire20 = wire18 == wire19;
wire [1:0] wire21 = wire17[6:5];
wire [3:0] wire22 = reg_1[wire21];
wire [1:0] wire23 = wire17[8:7];
wire [3:0] wire24 = reg_1[wire23];
wire [1:0] wire25 = wire17[4:3];
wire [3:0] wire26 = wire22 + wire24;
wire  wire27 = wire7 | wire15;
wire [12:0] wire28 = reg_2[wire3];
wire [2:0] wire29 = wire28[2:0];
wire [2:0] wire30 = 3'b11;
wire  wire31 = wire29 == wire30;
wire [1:0] wire32 = wire28[6:5];
wire [3:0] wire33 = reg_1[wire32];
wire [1:0] wire34 = wire28[8:7];
wire [3:0] wire35 = reg_1[wire34];
wire [3:0] wire36 = 4'b0;
wire  wire37 = wire33 == wire36;
wire  wire38 = wire27 | wire20;
wire [12:0] wire39 = reg_2[wire3];
wire [2:0] wire40 = wire39[2:0];
wire  wire41 = wire40 == wire30;
wire [1:0] wire42 = wire39[6:5];
wire [3:0] wire43 = reg_1[wire42];
wire [1:0] wire44 = wire39[8:7];
wire [3:0] wire45 = reg_1[wire44];
wire  wire46 = wire43 == wire36;
wire  wire47 = ~ wire46;
wire  wire48 = wire31 & wire37;
wire  wire49 = wire38 | wire48;
wire [12:0] wire50 = reg_2[wire3];
wire [2:0] wire51 = wire50[2:0];
wire [2:0] wire52 = 3'b100;
wire  wire53 = wire51 == wire52;
wire [1:0] wire54 = wire50[8:7];
wire [3:0] wire55 = reg_1[wire54];
wire [3:0] wire56 = reg_3[wire55];
wire [1:0] wire57 = wire50[6:5];
wire  wire58 = wire41 & wire47;
wire  wire59 = wire49 | wire58;
wire [12:0] wire60 = reg_2[wire3];
wire [2:0] wire61 = wire60[2:0];
wire [2:0] wire62 = 3'b101;
wire  wire63 = wire61 == wire62;
wire [1:0] wire64 = wire60[6:5];
wire [3:0] wire65 = reg_1[wire64];
wire [1:0] wire66 = wire60[8:7];
wire [3:0] wire67 = reg_1[wire66];
wire  wire68 = wire59 | wire53;
wire  wire69 = wire68 | wire63;
wire  wire70 = wire27 & wire7;
wire  wire71 = ~ wire7;
wire  wire72 = wire71 & wire15;
wire [1:0] wire73 = wire70 ? wire10 : wire16;
wire [3:0] wire74 = wire70 ? wire11 : wire3;
wire  wire75 = ~ wire27;
wire  wire76 = wire75 & wire20;
wire [1:0] wire77 = wire27 ? wire73 : wire25;
wire [3:0] wire78 = wire27 ? wire74 : wire26;
wire  wire79 = ~ wire38;
wire  wire80 = wire79 & wire48;
wire [3:0] wire81 = wire38 ? wire9 : wire35;
wire  wire82 = ~ wire49;
wire  wire83 = wire82 & wire58;
wire [3:0] wire84 = wire49 ? wire81 : wire9;
wire  wire85 = ~ wire59;
wire  wire86 = wire85 & wire53;
wire  wire87 = wire38 | wire86;
wire [1:0] wire88 = wire38 ? wire77 : wire57;
wire [3:0] wire89 = wire38 ? wire78 : wire56;
wire [3:0] wire90 = wire59 ? wire84 : wire9;
wire  wire91 = ~ wire68;
wire  wire92 = wire91 & wire63;
wire  wire93 = wire69 & wire92;
wire  wire94 = wire68 | wire93;
wire [3:0] wire95 = wire68 ? wire90 : wire9;
// effects 
assign guard = wire69;
assign value = wire0;
always@(posedge clk)
begin
	if(rst_n)
		begin
// reset 
		end
	else
		begin
// put  debug code here (display, stop, ...)
if(wire93) reg_3[wire65] <= wire67;
if(wire87) reg_1[wire88] <= wire89;
if(wire94) reg_0 <= wire95;
		end
end
endmodule
