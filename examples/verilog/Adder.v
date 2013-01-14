module Adder (clk, rst_n, guard, value);
integer index; // Used for initialisations
input clk;
input rst_n;
output guard;
output [9:0] value;
// state declarations
reg [3:0] reg_0;
reg [3:0] reg_1;
// bindings 
wire  wire0 = 0'b0;
wire  wire1 = 1'b1;
wire  wire2 = 1'b0;
wire [3:0] wire3 = reg_0;
wire [3:0] wire4 = reg_1;
wire [1:0] wire5 = wire3[1:0];
wire [1:0] wire6 = wire3[3:2];
wire [1:0] wire7 = wire4[1:0];
wire [1:0] wire8 = wire4[3:2];
wire  wire9 = wire5[0:0];
wire  wire10 = wire5[1:1];
wire  wire11 = wire7[0:0];
wire  wire12 = wire7[1:1];
wire  wire13 = 1'b1;
wire  wire14 = wire9 == wire13;
wire  wire15 = wire11 == wire13;
wire  wire16 = wire14 | wire15;
wire  wire17 = wire14 & wire15;
wire  wire18 = wire9 + wire11;
wire  wire19 = wire18 + wire13;
wire [3:0] wire20 = {wire16, wire17, wire18, wire19};
wire  wire21 = wire10 == wire13;
wire  wire22 = wire12 == wire13;
wire  wire23 = wire21 | wire22;
wire  wire24 = wire21 & wire22;
wire  wire25 = wire10 + wire12;
wire  wire26 = wire25 + wire13;
wire [3:0] wire27 = {wire23, wire24, wire25, wire26};
wire [2:0] wire28 = wire20[3:1];
wire [1:0] wire29 = wire28[2:1];
wire  wire30 = wire29[1:1];
wire  wire31 = 0;
wire [2:0] wire32 = wire27[3:1];
wire [1:0] wire33 = wire32[2:1];
wire  wire34 = wire33[1:1];
wire  wire35 = wire17 ? wire26 : wire25;
wire  wire36 = wire16 ? wire26 : wire25;
wire  wire37 = wire23 & wire16;
wire  wire38 = wire24 | wire37;
wire  wire39 = wire23 & wire17;
wire  wire40 = wire24 | wire39;
wire [1:0] wire41 = {wire35, wire18};
wire [1:0] wire42 = {wire36, wire19};
wire [5:0] wire43 = {wire38, wire40, wire41, wire42};
wire  wire44 = wire6[0:0];
wire  wire45 = wire6[1:1];
wire  wire46 = wire8[0:0];
wire  wire47 = wire8[1:1];
wire  wire48 = wire44 == wire13;
wire  wire49 = wire46 == wire13;
wire  wire50 = wire48 | wire49;
wire  wire51 = wire48 & wire49;
wire  wire52 = wire44 + wire46;
wire  wire53 = wire52 + wire13;
wire [3:0] wire54 = {wire50, wire51, wire52, wire53};
wire  wire55 = wire45 == wire13;
wire  wire56 = wire47 == wire13;
wire  wire57 = wire55 | wire56;
wire  wire58 = wire55 & wire56;
wire  wire59 = wire45 + wire47;
wire  wire60 = wire59 + wire13;
wire [3:0] wire61 = {wire57, wire58, wire59, wire60};
wire [2:0] wire62 = wire54[3:1];
wire [1:0] wire63 = wire62[2:1];
wire  wire64 = wire63[1:1];
wire [2:0] wire65 = wire61[3:1];
wire [1:0] wire66 = wire65[2:1];
wire  wire67 = wire66[1:1];
wire  wire68 = wire51 ? wire60 : wire59;
wire  wire69 = wire50 ? wire60 : wire59;
wire  wire70 = wire57 & wire50;
wire  wire71 = wire58 | wire70;
wire  wire72 = wire57 & wire51;
wire  wire73 = wire58 | wire72;
wire [1:0] wire74 = {wire68, wire52};
wire [1:0] wire75 = {wire69, wire53};
wire [5:0] wire76 = {wire71, wire73, wire74, wire75};
wire [4:0] wire77 = wire43[5:1];
wire [3:0] wire78 = wire77[4:1];
wire [1:0] wire79 = wire78[3:2];
wire [4:0] wire80 = wire76[5:1];
wire [3:0] wire81 = wire80[4:1];
wire [1:0] wire82 = wire81[3:2];
wire [1:0] wire83 = wire40 ? wire75 : wire74;
wire [1:0] wire84 = wire38 ? wire75 : wire74;
wire  wire85 = wire71 & wire38;
wire  wire86 = wire73 | wire85;
wire  wire87 = wire71 & wire40;
wire  wire88 = wire73 | wire87;
wire [3:0] wire89 = {wire83, wire41};
wire [3:0] wire90 = {wire84, wire42};
wire [9:0] wire91 = {wire86, wire88, wire89, wire90};
// effects 
assign guard = wire1;
assign value = wire91;
always@(posedge clk)
begin
	if(rst_n)
		begin
// reset 
		end
	else
		begin
	if(wire1)
		begin
// put  debug code here (display, stop, ...)
		end
		end
end
endmodule
