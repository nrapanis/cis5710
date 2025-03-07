

`timescale 1ns / 1ns

// quotient = dividend / divisor

module DividerUnsignedPipelined (
    input wire clk,
    rst,
    stall,
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

  logic [31:0] dividents[9];
  logic [31:0] remainders[9];
  logic [31:0] quotients[9];
  logic [31:0] divisor[9];

  assign dividents[0] = i_dividend;
  assign remainders[0] = 32'b0;
  assign quotients[0] = 32'b0;
  assign divisor[0] = i_divisor;

  genvar i;
  for (i = 0; i < 7; i = i + 1) begin : gen_iter
    logic [31:0] dividend1, dividend2, dividend3, dividend4;
    logic [31:0] remainder1, remainder2, remainder3, remainder4;
    logic [31:0] quotient1, quotient2, quotient3, quotient4;

    divu_1iter div1 (
        .i_dividend (dividents[i]),
        .i_divisor  (divisor[i]),
        .i_remainder(remainders[i]),
        .i_quotient (quotients[i]),
        .o_dividend (dividend1),
        .o_remainder(remainder1),
        .o_quotient (quotient1)
    );

    divu_1iter div2 (
        .i_dividend (dividend1),
        .i_divisor  (divisor[i]),
        .i_remainder(remainder1),
        .i_quotient (quotient1),
        .o_dividend (dividend2),
        .o_remainder(remainder2),
        .o_quotient (quotient2)
    );

    divu_1iter div3 (
        .i_dividend (dividend2),
        .i_divisor  (divisor[i]),
        .i_remainder(remainder2),
        .i_quotient (quotient2),
        .o_dividend (dividend3),
        .o_remainder(remainder3),
        .o_quotient (quotient3)
    );

    divu_1iter div4 (
        .i_dividend (dividend3),
        .i_divisor  (divisor[i]),
        .i_remainder(remainder3),
        .i_quotient (quotient3),
        .o_dividend (dividend4),
        .o_remainder(remainder4),
        .o_quotient (quotient4)
    );

    always_ff @(posedge clk) begin
      if (rst) begin
        dividents[i+1] <= 32'd0;
        remainders[i+1] <= 32'd0;
        quotients[i+1] <= 32'd0;
        divisor[i+1] <= 32'b0;
      end else begin
        dividents[i+1] <= dividend4;
        remainders[i+1] <= remainder4;
        quotients[i+1] <= quotient4;
        divisor[i+1] <= divisor[i];
      end
    end
  end

  logic [31:0] dividend1L, dividend2L, dividend3L, dividend4L;
  logic [31:0] remainder1L, remainder2L, remainder3L, remainder4L;
  logic [31:0] quotient1L, quotient2L, quotient3L, quotient4L;

  divu_1iter div1 (
      .i_dividend (dividents[7]),
      .i_divisor  (divisor[7]),
      .i_remainder(remainders[7]),
      .i_quotient (quotients[7]),
      .o_dividend (dividend1L),
      .o_remainder(remainder1L),
      .o_quotient (quotient1L)
  );

  divu_1iter div2 (
      .i_dividend (dividend1L),
      .i_divisor  (divisor[7]),
      .i_remainder(remainder1L),
      .i_quotient (quotient1L),
      .o_dividend (dividend2L),
      .o_remainder(remainder2L),
      .o_quotient (quotient2L)
  );

  divu_1iter div3 (
      .i_dividend (dividend2L),
      .i_divisor  (divisor[7]),
      .i_remainder(remainder2L),
      .i_quotient (quotient2L),
      .o_dividend (dividend3L),
      .o_remainder(remainder3L),
      .o_quotient (quotient3L)
  );

  divu_1iter div4 (
      .i_dividend (dividend3L),
      .i_divisor  (divisor[7]),
      .i_remainder(remainder3L),
      .i_quotient (quotient3L),
      .o_dividend (dividend4L),
      .o_remainder(remainder4L),
      .o_quotient (quotient4L)
  );

  assign o_remainder = remainder4L;
  assign o_quotient  = quotient4L;
endmodule


module divu_1iter (
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    input  wire  [31:0] i_remainder,
    input  wire  [31:0] i_quotient,
    output logic [31:0] o_dividend,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

  wire [31:0] temp_sum;

  assign temp_sum = {i_remainder[30:0], i_dividend[31]};

  assign o_quotient = (temp_sum < i_divisor) ? {i_quotient[30:0], 1'b0} : {i_quotient[30:0], 1'b1};
  assign o_remainder = (temp_sum < i_divisor) ? temp_sum : temp_sum - i_divisor;
  assign o_dividend = {i_dividend[30:0], 1'b0};

endmodule
