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

///// BELOW ARE THE STRUCTS

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  alu_op_t alu_ctl;
  logic alu_input_control;
  logic regFile_we;
  logic mem_re;
  logic mem_we;

  cycle_status_e cycle_status;
} stage_decode_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] a;
  logic [`REG_SIZE] b;
  alu_op_t alu_ctl;
  logic alu_input_control;
  logic regFile_we;
  logic mem_re;
  logic mem_we;

  cycle_status_e cycle_status;
} stage_execute_t;

typedef struct packed {
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] b;
  logic [`REG_SIZE] o;
  alu_op_t alu_ctl;
  logic alu_input_control;
  logic regFile_we;
  logic mem_re;
  logic mem_we;

  cycle_status_e cycle_status;
} stage_memory_t;

typedef struct packed {
  logic [`INSN_SIZE] insn;
  logic [`REG_SIZE] d;
  logic [`REG_SIZE] o;
  alu_op_t alu_ctl;
  logic alu_input_control;
  logic regFile_we;
  logic mem_re;
  logic mem_we;

  cycle_status_e cycle_status;
} stage_writeback_t;

typedef enum logic [3:0] {
  ALU_ADD  = 4'd0,
  ALU_SUB  = 4'd1,
  ALU_AND  = 4'd2,
  ALU_OR   = 4'd3,
  ALU_XOR  = 4'd4,
  ALU_SLT  = 4'd5,
  ALU_SLTU = 4'd6,
  ALU_SLL  = 4'd7,
  ALU_SRL  = 4'd8,
  ALU_SRA  = 4'd9
} alu_op_t;

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

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = decode_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = decode_state.insn[31:20];
  wire [ 4:0] imm_shamt = decode_state.insn[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {
    decode_state.insn[31:12], 1'b0
  };

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // // opcodes - see section 19 of RiscV spec
  // localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  // localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  // localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  // localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  // localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  // localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  // localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  alu_op_t alu_ctl;
  logic alu_input_control;
  logic regFile_we;
  logic mem_re;
  logic mem_we;

  always_comb begin
    alu_ctl           = ALU_ADD;
    alu_input_control = 1'b0;
    regFile_we        = 1'b0;
    mem_re            = 1'b0;
    mem_we            = 1'b0;

    case (insn_opcode)
      OpLui: begin  // LUI
        regFile_we = 1;
        alu_input_control = 1;
      end
      OpRegReg: begin  // R-type
        alu_input_control = 1'b0;
        regFile_we = 1'b1;
        case ({
          insn_funct7, insn_funct3
        })
          {7'b0000000, 3'b000} : alu_ctl = ALU_ADD;
          {7'b0100000, 3'b000} : alu_ctl = ALU_SUB;
          {7'b0000000, 3'b111} : alu_ctl = ALU_AND;
          {7'b0000000, 3'b110} : alu_ctl = ALU_OR;
          {7'b0000000, 3'b100} : alu_ctl = ALU_XOR;
          {7'b0000000, 3'b010} : alu_ctl = ALU_SLT;
          {7'b0000000, 3'b011} : alu_ctl = ALU_SLTU;
          {7'b0000000, 3'b001} : alu_ctl = ALU_SLL;
          {7'b0000000, 3'b101} : alu_ctl = ALU_SRL;
          {7'b0100000, 3'b101} : alu_ctl = ALU_SRA;
          default: alu_ctl = ALU_ADD;
        endcase
      end

      OpRegImm: begin  // I-type, but ALU
        alu_input_control = 1'b1;
        regFile_we = 1'b1;
        case (insn_funct3)
          3'b000:  alu_ctl = ALU_ADD;  // ADDI
          3'b111:  alu_ctl = ALU_AND;  // ANDI
          3'b110:  alu_ctl = ALU_OR;  // ORI
          3'b100:  alu_ctl = ALU_XOR;  // XORI
          3'b010:  alu_ctl = ALU_SLT;  // SLTI
          3'b011:  alu_ctl = ALU_SLTU;  // SLTIU
          3'b001:  alu_ctl = ALU_SLL;  // SLLI
          3'b101:  alu_ctl = (insn_funct7 == 7'b0000000) ? ALU_SRL : ALU_SRA;  // SRLI / SRAI
          default: alu_ctl = ALU_ADD;
        endcase
      end

      // OpLoad: begin  // Load
      //   alu_input_control = 1'b1;
      //   regFile_we = 1'b1;
      //   mem_re = 1'b1;
      //   alu_ctl = ALU_ADD;
      // end

      // OpStore: begin  // Store
      //   alu_input_control = 1'b1;
      //   mem_we = 1'b1;
      //   alu_ctl = ALU_ADD;
      // end

      OpBranch: begin  // Branch
        alu_input_control = 1'b0;
        alu_ctl = ALU_SUB;
      end

      default: begin

      end
    endcase
  end


  // wire insn_lui = insn_opcode == OpLui;
  // wire insn_auipc = insn_opcode == OpAuipc;
  // wire insn_jal = insn_opcode == OpJal;
  // wire insn_jalr = insn_opcode == OpJalr;

  // wire insn_beq = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b000;
  // wire insn_bne = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b001;
  // wire insn_blt = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b100;
  // wire insn_bge = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b101;
  // wire insn_bltu = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b110;
  // wire insn_bgeu = insn_opcode == OpBranch && decode_state.insn[14:12] == 3'b111;

  // wire insn_lb = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b000;
  // wire insn_lh = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b001;
  // wire insn_lw = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b010;
  // wire insn_lbu = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b100;
  // wire insn_lhu = insn_opcode == OpLoad && decode_state.insn[14:12] == 3'b101;

  // wire insn_sb = insn_opcode == OpStore && decode_state.insn[14:12] == 3'b000;
  // wire insn_sh = insn_opcode == OpStore && decode_state.insn[14:12] == 3'b001;
  // wire insn_sw = insn_opcode == OpStore && decode_state.insn[14:12] == 3'b010;

  // wire insn_addi = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b000;
  // wire insn_slti = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b010;
  // wire insn_sltiu = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b011;
  // wire insn_xori = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b100;
  // wire insn_ori = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b110;
  // wire insn_andi = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b111;

  // wire insn_slli = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  // wire insn_srli = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  // wire insn_srai = insn_opcode == OpRegImm && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;

  // wire insn_add  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'd0;
  // wire insn_sub  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b000 && decode_state.insn[31:25] == 7'b0100000;
  // wire insn_sll  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b001 && decode_state.insn[31:25] == 7'd0;
  // wire insn_slt  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b010 && decode_state.insn[31:25] == 7'd0;
  // wire insn_sltu = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b011 && decode_state.insn[31:25] == 7'd0;
  // wire insn_xor  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b100 && decode_state.insn[31:25] == 7'd0;
  // wire insn_srl  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'd0;
  // wire insn_sra  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b101 && decode_state.insn[31:25] == 7'b0100000;
  // wire insn_or   = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b110 && decode_state.insn[31:25] == 7'd0;
  // wire insn_and  = insn_opcode == OpRegReg && decode_state.insn[14:12] == 3'b111 && decode_state.insn[31:25] == 7'd0;

  // wire insn_mul    = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b000;
  // wire insn_mulh   = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b001;
  // wire insn_mulhsu = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b010;
  // wire insn_mulhu  = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b011;
  // wire insn_div    = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b100;
  // wire insn_divu   = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b101;
  // wire insn_rem    = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b110;
  // wire insn_remu   = insn_opcode == OpRegReg && decode_state.insn[31:25] == 7'd1 && decode_state.insn[14:12] == 3'b111;

  // wire insn_ecall = insn_opcode == OpEnviron && decode_state.insn[31:7] == 25'd0;
  // wire insn_fence = insn_opcode == OpMiscMem;

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
      .rd      (writeback_state.insn[11:7]),
      .rd_data (writeback_state.o),
      .rs1     (rs1),
      .rs1_data(rs1_data),
      .rs2     (rs2),
      .rs2_data(rs2_data),
      .clk     (clk),
      .we      (memory_state.regFile_we), /////// TODO FUCKING CHANGE IT AT ONCE IT IS WRONG
      .rst     (rst)
  );

  assign addr_to_dmem = 32'd0;


  ///// BELOW ARE THE PIPELINE STAGES

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  ///// HANDLE BRANCHES

  logic branch_taken;
  logic [`REG_SIZE] branch_target;

  wire [12:0] imm_b_execute;
  assign {imm_b_execute[12], imm_b_execute[10:5]} = execute_state.insn[31:25];
  assign {imm_b_execute[4:1], imm_b_execute[11]} = execute_state.insn[11:7];
  assign imm_b_execute[0] = 1'b0;

  wire [`REG_SIZE] imm_b_execute_sext = {{19{imm_b_execute[12]}}, imm_b_execute[12:0]};

  always_comb begin
    branch_taken  = 1'b0;

    branch_target = execute_state.pc + imm_b_execute_sext;

    // Check branch conditions based on the funct3 field (which is part of decode_state.insn)
    if (insn_opcode == 7'b1100011) begin
      case (insn_funct3)
        3'b000:  branch_taken = (alu_result == 32'd0);  // BEQ
        3'b001:  branch_taken = (alu_result != 32'd0);  // BNE
        3'b100:  branch_taken = ($signed(execute_state.a) < $signed(execute_state.b));  // BLT
        3'b101:  branch_taken = ($signed(execute_state.a) >= $signed(execute_state.b));  // BGE
        3'b110:  branch_taken = (execute_state.a < execute_state.b);  // BLTU
        3'b111:  branch_taken = (execute_state.a >= execute_state.b);  // BGEU
        default: branch_taken = 1'b0;
      endcase
    end
  end

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (branch_taken) begin
      f_pc_current <= branch_target;


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
      decode_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,
          alu_ctl: ALU_ADD,
          alu_input_control: 0,
          regFile_we: 0,
          mem_re: 0,
          mem_we: 0
      };
          end else if (branch_taken) begin
      f_pc_current <= branch_target;
      decode_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_RESET,
          alu_ctl: ALU_ADD,
          alu_input_control: 0,
          regFile_we: 0,
          mem_re: 0,
          mem_we: 0
      };
    end else begin
      begin
        decode_state <= '{
            pc: f_pc_current,
            insn: f_insn,
            cycle_status: f_cycle_status,
            alu_ctl: alu_ctl,
            alu_input_control: alu_input_control,
            regFile_we: regFile_we,
            mem_re: mem_re,
            mem_we: mem_we
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );


  ///// WD Bypassing

  logic [4:0] rs1_decode = decode_state.insn[19:15];
  logic [4:0] rs2_decode = decode_state.insn[24:20];
  logic [4:0] rd_writeback = writeback_state.insn[11:7];

  wire [31:0] wd_rs1_data = ((writeback_state.regFile_we) && 
                           (rd_writeback == rs1_decode) && 
                           (rs1_decode != 0)) ? writeback_state.d : rs1_data;
  wire [31:0] wd_rs2_data = ((writeback_state.regFile_we) && 
                           (rd_writeback == rs2_decode) && 
                           (rs2_decode != 0)) ? writeback_state.d : rs2_data;




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
          a: 0,
          b: 0,
          cycle_status: CYCLE_RESET,
          alu_ctl: ALU_ADD,
          alu_input_control: 0,
          regFile_we: 0,
          mem_re: 0,
          mem_we: 0
      };
    end else begin
      begin
        if (insn_opcode == OpLui) begin
          execute_state <= '{
              pc: decode_state.pc,
              insn: decode_state.insn,
              a: 0,
              b: 0,
              cycle_status: decode_state.cycle_status,
              alu_ctl: decode_state.alu_ctl,
              alu_input_control: decode_state.alu_input_control,
              regFile_we: decode_state.regFile_we,
              mem_re: decode_state.mem_re,
              mem_we: decode_state.mem_we
          };
        end else begin
          execute_state <= '{
              pc: decode_state.pc,
              insn: decode_state.insn,
              a: wd_rs1_data,
              b: wd_rs2_data,
              cycle_status: decode_state.cycle_status,
              alu_ctl: decode_state.alu_ctl,
              alu_input_control: decode_state.alu_input_control,
              regFile_we: decode_state.regFile_we,
              mem_re: decode_state.mem_re,
              mem_we: decode_state.mem_we
          };
        end
      end
    end
  end
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );

  /****************/
  /* MEMORY STAGE*/
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
          insn: 0,
          o: 0,
          b: 0,
          cycle_status: CYCLE_RESET,
          alu_ctl: ALU_ADD,
          alu_input_control: 0,
          regFile_we: 0,
          mem_re: 0,
          mem_we: 0
      };
    end else begin
      begin
        memory_state <= '{
            insn: execute_state.insn,
            o: alu_result,  // TODO, input to data mem when we do the latter
            b: execute_state.b,
            cycle_status: execute_state.cycle_status,
            alu_ctl: execute_state.alu_ctl,
            alu_input_control: execute_state.alu_input_control,
            regFile_we: execute_state.regFile_we,
            mem_re: execute_state.mem_re,
            mem_we: execute_state.mem_we
        };
      end
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );

  /****************/
  /* WRITEBACK STAGE*/
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
          insn: 0,
          o: 0,
          d: 0,
          cycle_status: CYCLE_RESET,
          alu_ctl: ALU_ADD,
          alu_input_control: 0,
          regFile_we: 0,
          mem_re: 0,
          mem_we: 0
      };
    end else begin
      begin
        writeback_state <= '{
            insn: memory_state.insn,
            o: memory_state.o,
            d: memory_state.o,  // TODO output of dataMem but we dont care about memory instructions now!
            cycle_status: memory_state.cycle_status,
            alu_ctl: memory_state.alu_ctl,
            alu_input_control: memory_state.alu_input_control,
            regFile_we: memory_state.regFile_we,
            mem_re: memory_state.mem_re,
            mem_we: memory_state.mem_we
        };
      end
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );


  ///// DO THE ALU

  logic [`REG_SIZE] alu_result;
  wire [11:0] imm_i_execute;
  assign imm_i_execute = execute_state.insn[31:20];
  wire [`REG_SIZE] imm_i_execute_sext = {{20{imm_i_execute[11]}}, imm_i_execute[11:0]};

  wire [19:0] imm_u_execute;
  assign imm_u_execute = execute_state.insn[31:12];
  wire  [`REG_SIZE] imm_u_execute_ext = {imm_u_execute, 12'b0};

  logic [`REG_SIZE] alu_second_operand;

assign alu_second_operand = (execute_state.insn[6:0] == OpLui)
                              ? imm_u_execute_ext
                              : ((execute_state.alu_input_control)
                                  ? imm_i_execute_sext
                                  : execute_state.b);


  always_comb begin
    unique case (execute_state.alu_ctl)
      ALU_ADD: alu_result = execute_state.a + alu_second_operand;
      ALU_SUB: alu_result = execute_state.a - alu_second_operand;
      ALU_AND: alu_result = execute_state.a & alu_second_operand;
      ALU_OR: alu_result = execute_state.a | alu_second_operand;
      ALU_XOR: alu_result = execute_state.a ^ alu_second_operand;
      ALU_SLT:
      alu_result = ($signed(execute_state.a) < $signed(alu_second_operand)) ? 32'd1 : 32'd0;
      ALU_SLTU: alu_result = (execute_state.a < alu_second_operand) ? 32'd1 : 32'd0;
      ALU_SLL: alu_result = execute_state.a << alu_second_operand[4:0];
      ALU_SRL: alu_result = execute_state.a >> alu_second_operand[4:0];
      ALU_SRA: alu_result = $signed(execute_state.a) >>> alu_second_operand[4:0];
      default: alu_result = 32'd0;
    endcase
  end
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
