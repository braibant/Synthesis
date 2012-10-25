module Adder (clk, rst_n, guard, value, reg_0, reg_1);
input clk;
input rst_n;
output guard;
output [9:0] value;
// state declarations
input [3:0] reg_0;
input [3:0] reg_1;
// bindings 
wire  wire0 = 0'b0;
wire [3:0] wire1 = reg_0;
wire [3:0] wire2 = reg_1;
wire [1:0] wire3 = wire1[1:0];
wire [1:0] wire4 = wire1[3:2];
wire [1:0] wire5 = wire2[1:0];
wire [1:0] wire6 = wire2[3:2];
wire  wire7 = wire3[0:0];
wire  wire8 = wire3[1:1];
wire  wire9 = wire5[0:0];
wire  wire10 = wire5[1:1];
wire  wire11 = 1'b1;
wire  wire12 = wire7 == wire11;
wire  wire13 = wire9 == wire11;
wire  wire14 = wire12 | wire13;
wire  wire15 = wire12 & wire13;
wire  wire16 = wire7 + wire9;
wire  wire17 = wire16 + wire11;
wire [3:0] wire18 = {wire14, wire15, wire16, wire17};
wire  wire19 = wire8 == wire11;
wire  wire20 = wire10 == wire11;
wire  wire21 = wire19 | wire20;
wire  wire22 = wire19 & wire20;
wire  wire23 = wire8 + wire10;
wire  wire24 = wire23 + wire11;
wire [3:0] wire25 = {wire21, wire22, wire23, wire24};
wire [2:0] wire26 = wire18[3:1];
wire [1:0] wire27 = wire26[2:1];
wire  wire28 = wire27[1:1];
wire  wire29 = 0;
wire [2:0] wire30 = wire25[3:1];
wire [1:0] wire31 = wire30[2:1];
wire  wire32 = wire31[1:1];
wire  wire33 = wire15 ? wire24 : wire23;
wire  wire34 = wire14 ? wire24 : wire23;
wire  wire35 = wire21 & wire14;
wire  wire36 = wire22 | wire35;
wire  wire37 = wire21 & wire15;
wire  wire38 = wire22 | wire37;
wire [1:0] wire39 = {wire33, wire16};
wire [1:0] wire40 = {wire34, wire17};
wire [5:0] wire41 = {wire36, wire38, wire39, wire40};
wire  wire42 = wire4[0:0];
wire  wire43 = wire4[1:1];
wire  wire44 = wire6[0:0];
wire  wire45 = wire6[1:1];
wire  wire46 = wire42 == wire11;
wire  wire47 = wire44 == wire11;
wire  wire48 = wire46 | wire47;
wire  wire49 = wire46 & wire47;
wire  wire50 = wire42 + wire44;
wire  wire51 = wire50 + wire11;
wire [3:0] wire52 = {wire48, wire49, wire50, wire51};
wire  wire53 = wire43 == wire11;
wire  wire54 = wire45 == wire11;
wire  wire55 = wire53 | wire54;
wire  wire56 = wire53 & wire54;
wire  wire57 = wire43 + wire45;
wire  wire58 = wire57 + wire11;
wire [3:0] wire59 = {wire55, wire56, wire57, wire58};
wire [2:0] wire60 = wire52[3:1];
wire [1:0] wire61 = wire60[2:1];
wire  wire62 = wire61[1:1];
wire [2:0] wire63 = wire59[3:1];
wire [1:0] wire64 = wire63[2:1];
wire  wire65 = wire64[1:1];
wire  wire66 = wire49 ? wire58 : wire57;
wire  wire67 = wire48 ? wire58 : wire57;
wire  wire68 = wire55 & wire48;
wire  wire69 = wire56 | wire68;
wire  wire70 = wire55 & wire49;
wire  wire71 = wire56 | wire70;
wire [1:0] wire72 = {wire66, wire50};
wire [1:0] wire73 = {wire67, wire51};
wire [5:0] wire74 = {wire69, wire71, wire72, wire73};
wire [4:0] wire75 = wire41[5:1];
wire [3:0] wire76 = wire75[4:1];
wire [1:0] wire77 = wire76[3:2];
wire [4:0] wire78 = wire74[5:1];
wire [3:0] wire79 = wire78[4:1];
wire [1:0] wire80 = wire79[3:2];
wire [1:0] wire81 = wire38 ? wire73 : wire72;
wire [1:0] wire82 = wire36 ? wire73 : wire72;
wire  wire83 = wire69 & wire36;
wire  wire84 = wire71 | wire83;
wire  wire85 = wire69 & wire38;
wire  wire86 = wire71 | wire85;
wire [3:0] wire87 = {wire81, wire39};
wire [3:0] wire88 = {wire82, wire40};
wire [9:0] wire89 = {wire84, wire86, wire87, wire88};
wire  wire90 = 1'b1;
// effects 
assign guard = wire90;
assign value = wire89;
always@(posedge clk)
begin
	if(rst_n)
		begin
//INIT 
		end
	else
		begin
		end
end
endmodule
