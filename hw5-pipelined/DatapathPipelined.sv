`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef DIVIDER_STAGES
`define DIVIDER_STAGES 8
`endif

`ifndef SYNTHESIS
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif
`include "../hw2b-cla/cla.sv"
`include "../hw4-multicycle/DividerUnsignedPipelined.sv"
`include "cycle_status.sv"

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
`ifndef SYNTHESIS
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
`endif
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  ///// BELOW IS THE IMPLEMENTATION OF THE REGFILE

  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];
  int i;

  always_ff @(posedge clk) begin : blockName
    regs[0] <= 32'd0;
    if (rst) begin
      for (i = 1; i < 32; i = i + 1) begin : g_do
        regs[i] <= 32'd0;
      end
    end else begin
      if (we && rd != 0) begin
        regs[rd] <= rd_data;
      end
    end
  end

endmodule

typedef struct packed {

  // misc and jump insns
  logic insn_lui;
  logic insn_auipc;
  logic insn_jal;
  logic insn_jalr;

  // branch insns
  logic insn_beq;
  logic insn_bne;
  logic insn_blt;
  logic insn_bge;
  logic insn_bltu;
  logic insn_bgeu;

  // load insns
  logic insn_lb;
  logic insn_lh;
  logic insn_lw;
  logic insn_lbu;
  logic insn_lhu;

  // store insns
  logic insn_sb;
  logic insn_sh;
  logic insn_sw;

  // immediate insns
  logic insn_addi;
  logic insn_slti;
  logic insn_sltiu;
  logic insn_xori;
  logic insn_ori;
  logic insn_andi;
  logic insn_slli;
  logic insn_srli;
  logic insn_srai;

  // regreg insns
  logic insn_add;
  logic insn_sub;
  logic insn_sll;
  logic insn_slt;
  logic insn_sltu;
  logic insn_xor;
  logic insn_srl;
  logic insn_sra;
  logic insn_or;
  logic insn_and;
  logic insn_mul;
  logic insn_mulh;
  logic insn_mulhsu;
  logic insn_mulhu;
  logic insn_div;
  logic insn_divu;
  logic insn_rem;
  logic insn_remu;

  // more misc insns
  logic insn_ecall;
  logic insn_fence;
} insn_key;

///// BELOW ARE THE STRUCTS

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE]  pc;
  logic [`INSN_SIZE] insn;

  cycle_status_e cycle_status;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE]  pc;
  logic [`INSN_SIZE] insn;

  logic [4:0] insn_rd;
  logic [`OPCODE_SIZE] opcode;

  logic [11:0] imm_i;
  logic [11:0] imm_s;
  logic [12:0] imm_b;
  logic [20:0] imm_j;
  logic [19:0] imm_u;

  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_s_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_j_sext;

  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;

  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;

  insn_key insn_set;

  cycle_status_e cycle_status;

  logic halt;

} stage_execute_t;

/** state at the start of Memory stage */

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [`OPCODE_SIZE] opcode;

  logic [4:0] insn_rd;
  logic [`REG_SIZE] rd_data;
  logic we;

  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;

  logic [`REG_SIZE] addr_to_dmem;
  logic [`REG_SIZE] store_data_to_dmem;
  logic [3:0] store_we_to_dmem;

  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_s_sext;

  logic [`REG_SIZE] branched_pc; // represents the pc value that will be branched to IF there is a branch
  logic branch_taken;  // 1: branch, 0: no branch

  logic halt;

  insn_key insn_set;

  cycle_status_e cycle_status;
} stage_memory_t;

/** state at the start of Writeback stage */

typedef struct packed {
  logic [`INSN_SIZE] insn;
  logic [`OPCODE_SIZE] opcode;
  logic [`REG_SIZE] pc;

  // register signals
  logic [4:0] insn_rd;
  logic [`REG_SIZE] rd_data;
  logic we;

  logic halt;

  cycle_status_e cycle_status;
} stage_writeback_t;


module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See the cycle_status.sv file for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  ///// BELOW IS THE REGISTER FILE INSTANTIATION

  logic [4:0] rs1 = decode_state.insn[19:15];
  logic [4:0] rs2 = decode_state.insn[24:20];
  logic [4:0] rd = decode_state.insn[11:7];

  logic [`REG_SIZE] rs1_data, rs2_data;

  // Instantiate register file
  RegFile rf (
      .clk(clk),
      .rst(rst),
      .we(w_we),
      .rd(w_insn_rd),
      .rd_data(w_rd_data),
      .rs1(d_insn_rs1),
      .rs2(d_insn_rs2),
      .rs1_data(d_rs1_data_temp),
      .rs2_data(d_rs2_data_temp)
  );

  // CLA inputs
  logic [31:0] cla_a;
  logic [31:0] cla_b;
  logic cla_cin;
  logic [31:0] cla_sum;

  // assign cla_a = x_rs1_data;

  // // determine b and cin for the cla
  // always_comb begin
  //   cla_b   = x_rs2_data;
  //   cla_cin = 0;

  //   if (x_insn_key.insn_sub) begin
  //     cla_b   = ~x_rs2_data;
  //     cla_cin = 1;
  //   end else if (x_insn_key.insn_addi) begin
  //     cla_b = x_imm_i_sext;
  //   end
  // end

  cla adder (
      .a(x_rs1_data),
      .b((x_insn_key.insn_sub) ? ~x_rs2_data : (x_insn_key.insn_addi) ? x_imm_i_sext : x_rs2_data),
      .cin((x_insn_key.insn_sub) ? 1'b1 : 1'b0),
      .sum(cla_sum)
  );

  // intermediary for multiplier instructions
  logic [63:0] multiple;
  logic [31:0] product_temp;

  // division vars

  // wire [31:0] signed_quotient;
  // wire [31:0] signed_remainder;

  // wire [31:0] unsigned_divisor;
  // wire [31:0] unsigned_dividend;
  // wire [31:0] unsigned_quotient;
  // wire [31:0] unsigned_remainder;

  // // convert dividend and divisor to unsigned
  // assign unsigned_dividend = execute_state.rs1_data[31] ? (~execute_state.rs1_data + 1) : execute_state.rs1_data;
  // assign unsigned_divisor = execute_state.rs2_data[31] ? (~execute_state.rs2_data + 1) : execute_state.rs2_data;

  // // convert outputs from unsigned division to be signed
  // assign signed_quotient = (execute_state.rs1_data[31] ^ execute_state.rs2_data[31]) ? (~unsigned_quotient + 1) : unsigned_quotient;
  // assign signed_remainder = (execute_state.rs1_data[31]) ? (~unsigned_remainder + 1) : unsigned_remainder;

  // // need to wait 8 cycles to run
  // DividerUnsignedPipelined divider(.clk(clk), .rst(rst), .stall(0), 
  //         .i_dividend(unsigned_dividend), .i_divisor(unsigned_divisor), 
  //         .o_quotient(unsigned_quotient), .o_remainder(unsigned_remainder));





  ///// BELOW ARE THE PIPELINE STAGES

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;


  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (x_branch_taken) begin
      // BRANCH TO NEW PC
      f_pc_current <= x_branched_pc;
    end else if (load_to_use_stall) begin
      f_pc_current <= f_pc_current;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current   <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );


  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET};
    end else if (x_branch_taken) begin
      // FLUSH
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_TAKEN_BRANCH};
    end else if (load_to_use_stall) begin
      decode_state <= decode_state;
    end else begin
      decode_state <= '{pc: f_pc_current, insn: f_insn, cycle_status: f_cycle_status};
    end
  end

  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  logic [`REG_SIZE] d_pc_current;
  logic [`INSN_SIZE] d_insn;
  cycle_status_e d_cycle_status;

  assign d_pc_current = decode_state.pc;
  assign d_insn = decode_state.insn;
  assign d_cycle_status = decode_state.cycle_status;

  // DECODE INSN

  // components of the instruction
  logic [6:0] d_insn_funct7;
  logic [4:0] d_insn_rs2;
  logic [4:0] d_insn_rs1;
  logic [2:0] d_insn_funct3;
  logic [4:0] d_insn_rd;
  logic [4:0] d_insn_rd_temp;
  logic [`OPCODE_SIZE] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd_temp, d_insn_opcode} = d_insn;

  assign d_insn_rd = (d_insn_opcode == OpBranch) ? 0 : d_insn_rd_temp;
  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  logic [11:0] d_imm_i;
  assign d_imm_i = d_insn[31:20];

  // S - stores
  logic [11:0] d_imm_s;
  assign d_imm_s[11:5] = d_insn_funct7, d_imm_s[4:0] = d_insn_rd;

  // B - conditionals
  logic [12:0] d_imm_b;
  assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7,
      {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd_temp,
      d_imm_b[0] = 1'b0;

  // J - unconditional jumps
  logic [20:0] d_imm_j;
  assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {
    d_insn[31:12], 1'b0
  };

  logic [`REG_SIZE] d_imm_i_sext;
  logic [`REG_SIZE] d_imm_s_sext;
  logic [`REG_SIZE] d_imm_b_sext;
  logic [`REG_SIZE] d_imm_j_sext;

  assign d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  assign d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  assign d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  assign d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  logic [19:0] d_imm_u;
  assign d_imm_u = d_insn[31:12];

  // data taken from register file
  logic [`REG_SIZE] d_rs1_data_temp;
  logic [`REG_SIZE] d_rs2_data_temp;

  logic [`REG_SIZE] d_rs1_data;
  logic [`REG_SIZE] d_rs2_data;

  logic [4:0] w_insn_rd_bypass;
  assign w_insn_rd_bypass = (w_opcode == OpBranch) ? 0 : w_insn_rd;

  // WD Bypass
  always_comb begin
    d_rs1_data = d_rs1_data_temp;
    d_rs2_data = d_rs2_data_temp;


    if (w_insn_rd_bypass == d_insn_rs1 && d_insn_rs1 != 0) begin
      d_rs1_data = w_rd_data;
    end
    if (w_insn_rd_bypass == d_insn_rs2 && d_insn_rs2 != 0) begin
      d_rs2_data = w_rd_data;
    end
  end

  insn_key d_insn_key;
  assign d_insn_key.insn_lui = d_insn_opcode == OpLui;
  assign d_insn_key.insn_auipc = d_insn_opcode == OpAuipc;
  assign d_insn_key.insn_jal = d_insn_opcode == OpJal;
  assign d_insn_key.insn_jalr = d_insn_opcode == OpJalr;

  assign d_insn_key.insn_beq = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_bne = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_blt = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_bge = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b101;
  assign d_insn_key.insn_bltu = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b110;
  assign d_insn_key.insn_bgeu = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b111;

  assign d_insn_key.insn_lb = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_lh = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_lw = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b010;
  assign d_insn_key.insn_lbu = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_lhu = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b101;

  assign d_insn_key.insn_sb = d_insn_opcode == OpStore && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_sh = d_insn_opcode == OpStore && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_sw = d_insn_opcode == OpStore && d_insn_funct3 == 3'b010;

  assign d_insn_key.insn_addi = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_slti = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b010;
  assign d_insn_key.insn_sltiu = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b011;
  assign d_insn_key.insn_xori = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_ori = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b110;
  assign d_insn_key.insn_andi = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b111;

  assign d_insn_key.insn_slli = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b001 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_srli = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_srai = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'b0100000;

  assign d_insn_key.insn_add  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b000 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_sub  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b000 && d_insn_funct7 == 7'b0100000;
  assign d_insn_key.insn_sll  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b001 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_slt  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b010 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_sltu = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b011 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_xor  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b100 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_srl  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_sra  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'b0100000;
  assign d_insn_key.insn_or   = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b110 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_and  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b111 && d_insn_funct7 == 7'd0;

  assign d_insn_key.insn_mul    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_mulh   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_mulhsu = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b010;
  assign d_insn_key.insn_mulhu  = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b011;
  assign d_insn_key.insn_div    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_divu   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b101;
  assign d_insn_key.insn_rem    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b110;
  assign d_insn_key.insn_remu   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b111;

  assign d_insn_key.insn_ecall = d_insn_opcode == OpEnviron && d_insn[31:7] == 25'd0;
  assign d_insn_key.insn_fence = d_insn_opcode == OpMiscMem;


  // LOAD -> STORE WM BYPASSING
  logic load_to_use_stall;

  assign load_to_use_stall = 
    (x_opcode == OpLoad) &&
    (
      (d_insn_rs1 != 0 && d_insn_rs1 == x_insn_rd) ||
      (d_insn_rs2 != 0 && d_insn_rs2 == x_insn_rd && d_insn_opcode != OpStore)  // useful if store uses rs2
      );  // the current insn is sb, sh, sw



  /****************/
  /* EXECUTE STAGE*/
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,
          opcode: 0,

          insn_rd: 0,

          imm_i: 0,
          imm_s: 0,
          imm_b: 0,
          imm_j: 0,

          imm_i_sext: 0,
          imm_s_sext: 0,
          imm_b_sext: 0,
          imm_j_sext: 0,

          imm_u: 0,

          // data taken from register file
          rs1_data:
          0,
          rs2_data: 0,
          insn_rs1: 0,
          insn_rs2: 0,

          // insn_key containing the insn signal
          insn_set:
          0,

          halt: 0
      };
    end else if (x_branch_taken) begin
      // FLUSH
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_TAKEN_BRANCH,
          opcode: 0,

          insn_rd: 0,

          imm_i: 0,
          imm_s: 0,
          imm_b: 0,
          imm_j: 0,

          imm_i_sext: 0,
          imm_s_sext: 0,
          imm_b_sext: 0,
          imm_j_sext: 0,

          imm_u: 0,

          // data taken from register file
          rs1_data:
          0,
          rs2_data: 0,
          insn_rs1: 0,
          insn_rs2: 0,

          // insn_key containing the insn signal
          insn_set:
          0,

          halt: 0
      };
    end else if (load_to_use_stall) begin
      //bubble
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_LOAD2USE,
          opcode: 0,

          insn_rd: 0,

          imm_i: 0,
          imm_s: 0,
          imm_b: 0,
          imm_j: 0,

          imm_i_sext: 0,
          imm_s_sext: 0,
          imm_b_sext: 0,
          imm_j_sext: 0,

          imm_u: 0,

          // data taken from register file
          rs1_data:
          0,
          rs2_data: 0,
          insn_rs1: 0,
          insn_rs2: 0,

          // insn_key containing the insn signal
          insn_set:
          0,

          halt: 0
      };
    end else begin
      execute_state <= '{
          pc: d_pc_current,
          insn: d_insn,
          cycle_status: d_cycle_status,

          opcode: d_insn_opcode,

          insn_rd: d_insn_rd,

          imm_i: d_imm_i,
          imm_s: d_imm_s,
          imm_b: d_imm_b,
          imm_j: d_imm_j,

          imm_i_sext: d_imm_i_sext,
          imm_s_sext: d_imm_s_sext,
          imm_b_sext: d_imm_b_sext,
          imm_j_sext: d_imm_j_sext,

          imm_u: d_imm_u,

          // data taken from register file
          rs1_data:
          d_rs1_data,
          rs2_data: d_rs2_data,
          insn_rs1: d_insn_rs1,
          insn_rs2: d_insn_rs2,

          // insn_key containing the insn signal
          insn_set:
          d_insn_key,

          halt: 0
      };
    end
  end

  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );

  // Execute Signals
  logic x_we;
  logic [31:0] x_rd_data;

  logic [`REG_SIZE] x_pc;
  assign x_pc = execute_state.pc;
  logic [`INSN_SIZE] x_insn;
  assign x_insn = execute_state.insn;
  cycle_status_e x_cycle_status;
  assign x_cycle_status = execute_state.cycle_status;


  logic [`OPCODE_SIZE] x_opcode;
  assign x_opcode = execute_state.opcode;

  logic [4:0] x_insn_rd;
  assign x_insn_rd = execute_state.insn_rd;

  logic [11:0] x_imm_i;
  assign x_imm_i = execute_state.imm_i;
  logic [11:0] x_imm_s;
  assign x_imm_s = execute_state.imm_s;
  logic [12:0] x_imm_b;
  assign x_imm_b = execute_state.imm_b;
  logic [20:0] x_imm_j;
  assign x_imm_j = execute_state.imm_j;

  logic [`REG_SIZE] x_imm_i_sext;
  assign x_imm_i_sext = execute_state.imm_i_sext;
  logic [`REG_SIZE] x_imm_s_sext;
  assign x_imm_s_sext = execute_state.imm_s_sext;
  logic [`REG_SIZE] x_imm_b_sext;
  assign x_imm_b_sext = execute_state.imm_b_sext;
  logic [`REG_SIZE] x_imm_j_sext;
  assign x_imm_j_sext = execute_state.imm_j_sext;

  logic [19:0] x_imm_u;
  assign x_imm_u = execute_state.imm_u;

  // data taken from register file
  logic [`REG_SIZE] x_rs1_data_temp;
  assign x_rs1_data_temp = execute_state.rs1_data;
  logic [`REG_SIZE] x_rs2_data_temp;
  assign x_rs2_data_temp = execute_state.rs2_data;

  logic [4:0] x_insn_rs1;
  assign x_insn_rs1 = execute_state.insn_rs1;
  logic [4:0] x_insn_rs2;
  assign x_insn_rs2 = execute_state.insn_rs2;

  logic [`REG_SIZE] x_rs1_data;
  logic [`REG_SIZE] x_rs2_data;

  // insn_key containing the insn signal
  insn_key x_insn_key;
  assign x_insn_key = execute_state.insn_set;

  // memory signals
  logic [`REG_SIZE] x_addr_to_dmem;
  logic [`REG_SIZE] x_store_mem_to_dmem;
  logic [3:0] x_store_we_to_dmem;

  // branch signal
  logic [`REG_SIZE] x_branched_pc; // represents the pc value that will be branched to IF there is a branch
  logic x_branch_taken;  // 1: branch, 0: no branch

  // MX and WX Bypass

  // always_comb begin
  //   // default
  //   x_rs1_data = x_rs1_data_temp;
  //   x_rs2_data = x_rs2_data_temp;

  //   // rs1_data
  //   if (x_insn_rs1 != 0) begin
  //     if (m_insn_rd == x_insn_rs1) begin
  //       x_rs1_data = mem_rd_data;
  //     end else if (w_insn_rd_bypass == x_insn_rs1) begin
  //       x_rs1_data = w_rd_data;
  //     end
  //   end
  //   // rs2_data
  //   if (x_insn_rs2 != 0) begin
  //     if (m_insn_rd == x_insn_rs2) begin
  //       x_rs2_data = mem_rd_data;
  //     end else if (w_insn_rd_bypass == x_insn_rs2) begin
  //       x_rs2_data = w_rd_data;
  //     end
  //   end
  // end

  assign x_rs1_data = (x_insn_rs1 != 0 && m_insn_rd == x_insn_rs1) ? mem_rd_data :
                      (x_insn_rs1 != 0 && w_insn_rd_bypass == x_insn_rs1) ? w_rd_data : x_rs1_data_temp;
  assign x_rs2_data = (x_insn_rs2 != 0 && m_insn_rd == x_insn_rs2) ? mem_rd_data :
                      (x_insn_rs2 != 0 && w_insn_rd_bypass == x_insn_rs2) ? w_rd_data : x_rs2_data_temp;

  // halt signal
  logic x_halt;


  logic [1:0] sub_dest;
  logic [31:0] mem_chosen_dest;
  logic [31:0] mem_actual_dest;

  always_comb begin
    // register signals
    x_we = 0;
    x_rd_data = 0;

    // data memory signals
    x_addr_to_dmem = 0;
    x_store_mem_to_dmem = 0;
    x_store_we_to_dmem = 0;

    //
    multiple = 0;

    // branch signals
    x_branched_pc = x_pc;
    x_branch_taken = 0;

    // halt signal
    x_halt = 0;

    case (x_opcode)
      OpLui: begin
        x_we = 1;
        x_rd_data = x_imm_u << 12;
      end

      OpAuipc: begin
        x_we = 1;
        x_rd_data = x_pc + (x_imm_u << 12);
      end

      OpJal: begin
        x_we = 1;
        x_rd_data = x_pc + 4;
        x_branched_pc = x_pc + x_imm_j_sext;
        x_branch_taken = 1;
      end
      OpJalr: begin
        x_we = 1;
        x_rd_data = x_pc + 4;
        x_branched_pc = (x_rs1_data + x_imm_i_sext) & ~32'h1;
        x_branch_taken = 1;
      end

      // I-TYPE
      OpRegImm: begin
        x_we = 1;
        case (1)
          x_insn_key.insn_addi:  x_rd_data = cla_sum;
          x_insn_key.insn_slti:  x_rd_data = $signed(x_rs1_data) < $signed(x_imm_i_sext) ? 1 : 0;
          x_insn_key.insn_sltiu: x_rd_data = x_rs1_data < x_imm_i_sext ? 1 : 0;
          x_insn_key.insn_xori:  x_rd_data = x_rs1_data ^ x_imm_i_sext;
          x_insn_key.insn_ori:   x_rd_data = x_rs1_data | x_imm_i_sext;
          x_insn_key.insn_andi:  x_rd_data = x_rs1_data & x_imm_i_sext;
          x_insn_key.insn_slli:  x_rd_data = x_rs1_data << x_imm_i[4:0];
          x_insn_key.insn_srli:  x_rd_data = x_rs1_data >> x_imm_i[4:0];
          x_insn_key.insn_srai:  x_rd_data = $signed(x_rs1_data) >>> x_imm_i[4:0];
        endcase
      end

      // R-TYPE
      OpRegReg: begin
        x_we = 1;
        case (1)
          x_insn_key.insn_add:  x_rd_data = cla_sum;
          x_insn_key.insn_sub:  x_rd_data = cla_sum;
          x_insn_key.insn_sll:  x_rd_data = x_rs1_data << x_rs2_data[4:0];
          x_insn_key.insn_slt:  x_rd_data = $signed(x_rs1_data) < $signed(x_rs2_data) ? 1 : 0;
          x_insn_key.insn_sltu: x_rd_data = x_rs1_data < x_rs2_data ? 1 : 0;
          x_insn_key.insn_xor:  x_rd_data = x_rs1_data ^ x_rs2_data;
          x_insn_key.insn_srl:  x_rd_data = x_rs1_data >> x_rs2_data[4:0];
          x_insn_key.insn_sra:  x_rd_data = $signed(x_rs1_data) >>> x_rs2_data[4:0];
          x_insn_key.insn_or:   x_rd_data = x_rs1_data | x_rs2_data;
          x_insn_key.insn_and:  x_rd_data = x_rs1_data & x_rs2_data;
          x_insn_key.insn_mul: begin
            multiple  = x_rs1_data * x_rs2_data;
            x_rd_data = multiple[31:0];
          end
          x_insn_key.insn_mulh: begin
            multiple  = $signed(x_rs1_data) * $signed(x_rs2_data);
            x_rd_data = multiple[63:32];
          end
          x_insn_key.insn_mulhsu: begin
            multiple  = {{32{x_rs1_data[31]}}, x_rs1_data} * {{32{1'b0}}, x_rs2_data};
            x_rd_data = multiple[63:32];
          end
          x_insn_key.insn_mulhu: begin
            multiple  = $unsigned(x_rs1_data) * $unsigned(x_rs2_data);
            x_rd_data = multiple[63:32];
          end
        endcase
      end

      OpBranch: begin
        x_branched_pc = x_pc + x_imm_b_sext;
        case (1)
          x_insn_key.insn_beq:  x_branch_taken = x_rs1_data == x_rs2_data;
          x_insn_key.insn_bne:  x_branch_taken = x_rs1_data != x_rs2_data;
          x_insn_key.insn_blt:  x_branch_taken = $signed(x_rs1_data) < $signed(x_rs2_data);
          x_insn_key.insn_bge:  x_branch_taken = $signed(x_rs1_data) >= $signed(x_rs2_data);
          x_insn_key.insn_bltu: x_branch_taken = $signed(x_rs1_data) < $unsigned(x_rs2_data);
          x_insn_key.insn_bgeu: x_branch_taken = $signed(x_rs1_data) >= $unsigned(x_rs2_data);
        endcase
      end

      OpEnviron: begin
        x_halt = 1;
      end

      OpMiscMem: begin
        // fence — do nothing
      end

      default: begin
        // illegal insn
      end
    endcase
  end


  /****************/
  /* MEMORY STAGE*/
  /****************/

  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,
          opcode: 0,

          // register signals
          insn_rd:
          0,
          rd_data: 0,
          we: 0,

          rs1_data: 0,
          rs2_data: 0,

          imm_i_sext: 0,
          imm_s_sext: 0,

          insn_set: 0,

          // memory signals
          addr_to_dmem:
          0,
          store_data_to_dmem: 0,
          store_we_to_dmem: 0,

          // branch signals
          branched_pc:
          0,  // represents the pc value that will be branched to IF there is a branch
          branch_taken: 0,  // 1: branch, 0: no branch


          halt: 0
      };
    end else begin
      memory_state <= '{
          pc: x_pc,
          insn: x_insn,
          cycle_status: x_cycle_status,
          opcode: x_opcode,

          // register signals
          insn_rd:
          x_insn_rd,
          rd_data: x_rd_data,
          we: x_we,

          rs1_data: x_rs1_data,
          rs2_data: x_rs2_data,

          imm_i_sext: x_imm_i_sext,
          imm_s_sext: x_imm_s_sext,

          // memory signals
          addr_to_dmem:
          x_addr_to_dmem,
          store_data_to_dmem: x_store_mem_to_dmem,
          store_we_to_dmem: x_store_we_to_dmem,

          insn_set: x_insn_key,

          // branch signals
          branched_pc:
          x_branched_pc,  // represents the pc value that will be branched to IF there is a branch
          branch_taken: x_branch_taken,  // 1: branch, 0: no branch

          halt: x_halt

      };
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );


  // WM Bypass
  logic [`REG_SIZE] wm_bypass_store_data;
  assign wm_bypass_store_data = (w_insn_rd_bypass != 0 && m_insn_rs2 == w_insn_rd_bypass && w_opcode == OpLoad && m_opcode == OpStore)? w_rd_data : memory_state.rs2_data;

  logic [4:0] m_insn_rs2;
  assign m_insn_rs2 = memory_state.insn[24:20];

  // always_comb begin
  //   wm_bypass_store_data = x_rs2_data;

  //   if (m_insn_rs2 != 0 && m_insn_rs2 == w_insn_rd_bypass && w_we) begin
  //     wm_bypass_store_data = w_rd_data;
  //   end
  // end

  // MEMORY SIGNALS

  logic [`REG_SIZE] m_imm_i_sext;
  assign m_imm_i_sext = memory_state.imm_i_sext;
  logic [`REG_SIZE] m_imm_s_sext;
  assign m_imm_s_sext = memory_state.imm_s_sext;

  logic [`REG_SIZE] m_pc;
  assign m_pc = memory_state.pc;
  logic [`INSN_SIZE] m_insn;
  assign m_insn = memory_state.insn;
  cycle_status_e m_cycle_status;
  assign m_cycle_status = memory_state.cycle_status;

  logic [`OPCODE_SIZE] m_opcode;
  assign m_opcode = memory_state.opcode;

  insn_key m_insn_key;
  assign m_insn_key = memory_state.insn_set;

  // register signals
  logic [4:0] m_insn_rd;
  assign m_insn_rd = memory_state.insn_rd;
  logic [31:0] mem_rd_data;
  logic m_we;

  // memory signals
  logic [`REG_SIZE] m_addr_to_dmem;
  assign m_addr_to_dmem = memory_state.addr_to_dmem;
  logic [`REG_SIZE] m_store_data_to_dmem;
  assign m_store_data_to_dmem = memory_state.store_data_to_dmem;
  logic [3:0] m_store_we_to_dmem;
  assign m_store_we_to_dmem = memory_state.store_we_to_dmem;
  logic m_halt;
  assign m_halt = memory_state.halt;


  always_comb begin
    mem_rd_data = memory_state.rd_data;
    m_we = memory_state.we;
    // Handle memory operations
    case (m_opcode)
      OpLoad: begin
        m_we = 1;
        case (1)
          m_insn_key.insn_lb: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_i_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            sub_dest = mem_actual_dest[1:0];
            addr_to_dmem = mem_chosen_dest;
            case (sub_dest)
              2'd0: mem_rd_data = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
              2'd1: mem_rd_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
              2'd2: mem_rd_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
              2'd3: mem_rd_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
              default: ;
            endcase
          end
          m_insn_key.insn_lh: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_i_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            sub_dest = mem_actual_dest[1:0];
            addr_to_dmem = mem_chosen_dest;
            case (sub_dest)
              2'd0: mem_rd_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
              2'd2: mem_rd_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
              default: ;
            endcase
          end
          m_insn_key.insn_lw: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_i_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            addr_to_dmem = mem_chosen_dest;
            mem_rd_data = load_data_from_dmem;
          end
          m_insn_key.insn_lbu: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_i_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            sub_dest = mem_actual_dest[1:0];
            addr_to_dmem = mem_chosen_dest;
            case (sub_dest)
              2'd0: mem_rd_data = {24'b0, load_data_from_dmem[7:0]};
              2'd1: mem_rd_data = {24'b0, load_data_from_dmem[15:8]};
              2'd2: mem_rd_data = {24'b0, load_data_from_dmem[23:16]};
              2'd3: mem_rd_data = {24'b0, load_data_from_dmem[31:24]};
              default: ;
            endcase
          end
          m_insn_key.insn_lhu: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_i_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            sub_dest = mem_actual_dest[1:0];
            addr_to_dmem = mem_chosen_dest;
            case (sub_dest)
              2'd0: mem_rd_data = {16'b0, load_data_from_dmem[15:0]};
              2'd2: mem_rd_data = {16'b0, load_data_from_dmem[31:16]};
              default: ;
            endcase
          end
        endcase
      end

      OpStore: begin
        case (1)
          m_insn_key.insn_sb: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_s_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            sub_dest = mem_actual_dest[1:0];
            addr_to_dmem = mem_chosen_dest;
            case (sub_dest)
              2'd0: begin
                store_data_to_dmem = {24'b0, wm_bypass_store_data[7:0]};
                store_we_to_dmem   = 4'b0001;
              end
              2'd1: begin
                store_data_to_dmem = {16'b0, wm_bypass_store_data[7:0], 8'b0};
                store_we_to_dmem   = 4'b0010;
              end
              2'd2: begin
                store_data_to_dmem = {8'b0, wm_bypass_store_data[7:0], 16'b0};
                store_we_to_dmem   = 4'b0100;
              end
              2'd3: begin
                store_data_to_dmem = {wm_bypass_store_data[7:0], 24'b0};
                store_we_to_dmem   = 4'b1000;
              end
              default: ;
            endcase
          end
          m_insn_key.insn_sh: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_s_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            sub_dest = mem_actual_dest[1:0];
            addr_to_dmem = mem_chosen_dest;
            case (sub_dest)
              2'd0: begin
                store_data_to_dmem = {16'b0, wm_bypass_store_data[15:0]};
                store_we_to_dmem   = 4'b0011;
              end
              2'd2: begin
                store_data_to_dmem = {wm_bypass_store_data[15:0], 16'b0};
                store_we_to_dmem   = 4'b1100;
              end
              default: ;
            endcase
          end
          m_insn_key.insn_sw: begin
            mem_actual_dest = memory_state.rs1_data + m_imm_s_sext;
            mem_chosen_dest = {mem_actual_dest[31:2], 2'b00};
            addr_to_dmem = mem_chosen_dest;
            store_data_to_dmem = wm_bypass_store_data;
            store_we_to_dmem = 4'b1111;
          end
        endcase
      end

      default: begin
        // illegal insn or NOP
      end
    endcase
  end



  /****************/
  /* WRITEBACK STAGE*/
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,
          opcode: 0,

          // register signals
          insn_rd:
          0,
          rd_data: 0,
          we: 0,

          halt: 0
      };
    end else begin
      writeback_state <= '{
          pc: m_pc,
          insn: m_insn,
          cycle_status: m_cycle_status,
          opcode: m_opcode,

          // register signals
          insn_rd:
          m_insn_rd,
          rd_data: mem_rd_data,
          we: m_we,

          halt: m_halt

      };
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );

  // WRITE SIGNALS
  logic [`REG_SIZE] w_pc;
  assign w_pc = writeback_state.pc;
  logic [`INSN_SIZE] w_insn;
  assign w_insn = writeback_state.insn;
  cycle_status_e w_cycle_status;
  assign w_cycle_status = writeback_state.cycle_status;

  logic [`OPCODE_SIZE] w_opcode;
  assign w_opcode = writeback_state.opcode;

  // register signals
  logic [4:0] w_insn_rd;
  assign w_insn_rd = writeback_state.insn_rd;
  logic [31:0] w_rd_data;
  assign w_rd_data = writeback_state.rd_data;
  logic w_we;
  assign w_we = writeback_state.we;

  // halt
  logic w_halt;
  assign w_halt = writeback_state.halt;

  assign halt = w_halt;

  // set trace signals
  assign trace_writeback_pc = w_pc;
  assign trace_writeback_insn = w_insn;
  assign trace_writeback_cycle_status = w_cycle_status;

endmodule


module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem_array[NUM_WORDS];

`ifdef SYNTHESIS
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end
`endif

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end

endmodule

/* This design has just one clock for both processor and memory. */
module Processor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;




  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
