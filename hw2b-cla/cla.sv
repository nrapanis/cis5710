`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   assign pout = pin[3] & pin[2] & pin[1] & pin[0];
   assign gout = gin[3] | (pin[3] & gin[2]) | (pin[3] & pin[2] & gin[1]) |
                 (pin[3] & pin[2] & pin[1] & gin[0]);
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | (pin[1] & pin[0] & cin);
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | (pin[2] & pin[1] & gin[0]) | (pin[2] & pin[1] & pin[0] & cin);



endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   wire gout_temp;
   wire pout_temp;
   wire [2:0] cout1, cout2;
   wire c4;

   gp4 instance1(.gin(gin[3:0]),
                 .pin(pin[3:0]),
                 .cin(cin),
                 .gout(gout_temp),
                 .pout(pout_temp),
                 .cout(cout1));

   assign c4 = gout_temp | (pout_temp & cin);

   gp4 instance2(.gin(gin[7:4]),
                 .pin(pin[7:4]),
                 .cin(c4),
                 .gout(gout),
                 .pout(pout),
                 .cout(cout2));

   assign cout = {cout2, c4, cout1};

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   wire [31:0] g, p;

   wire [31:0] cout;

   wire [7:0] gout, pout;

   wire goutout, poutout;

   wire [6:0] cout_temp;

   genvar i;

   assign cout[0] = cin;

   for (i = 0; i < 32; i = i + 1) begin : g_gp1
      gp1 gp1_(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
   end

   genvar k;

   for (k = 0; k < 8; k = k + 1) begin : g_gp4
      gp4 gp4_(.gin(g[4*(k+1)-1 : 4*(k)]),
               .pin(p[4*(k+1)-1 : 4*(k)]),
               .cin(cout[4*k]),
               .gout(gout[k]),
               .pout(pout[k]),
               .cout(cout[4*(k+1)-1 : 4*(k) + 1]));
   end

   gp8 gp8_(.gin(gout),
            .pin(pout),
            .cin(cin),
            .gout(goutout),
            .pout(poutout),
            .cout(cout_temp));


   assign cout[28] = cout_temp[6];
   assign cout[24] = cout_temp[5];
   assign cout[20] = cout_temp[4];
   assign cout[16] = cout_temp[3];
   assign cout[12] = cout_temp[2];
   assign cout[8] = cout_temp[1];
   assign cout[4] = cout_temp[0];

   genvar j;

   assign sum[0] = a[0] ^ b[0] ^ cin;

   for (j = 1; j < 32; j = j + 1) begin : g_addition
      assign sum[j] = a[j] ^ b[j] ^ cout[j];
   end
endmodule
