/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

wire [31:0] dividents [33];
wire [31:0] remainders [33];
wire [31:0] quotients [33];

assign dividents[0] = i_dividend;
assign remainders[0] = 32'b0;
assign quotients[0] = 32'b0;

  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_iter
    divu_1iter div(
      .i_dividend(dividents[i]),
      .i_divisor(i_divisor),
      .i_remainder(remainders[i]),
      .i_quotient(quotients[i]),
      .o_dividend(dividents[i+1]),
      .o_remainder(remainders[i+1]),
      .o_quotient(quotients[i+1]));
  end

  assign o_remainder = remainders[32];
  assign o_quotient = quotients[32];
endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  wire [31:0] temp_sum;

  assign temp_sum = {i_remainder[30:0], i_dividend[31]};

  assign o_quotient = (temp_sum < i_divisor) ? {i_quotient[30:0], 1'b0} : {i_quotient[30:0], 1'b1};
  assign o_remainder = (temp_sum < i_divisor) ? temp_sum : temp_sum - i_divisor;
  assign o_dividend = {i_dividend[30:0], 1'b0};
endmodule
