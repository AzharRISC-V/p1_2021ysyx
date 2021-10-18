// ZhengpuShi

`include "defines.v"

// 简易的译码，可以快速计算出是否为跳转指令，以及跳转地址
module minidecode(
  input   wire                  clk,
  input   wire                  rst,
  input   wire  [`YSYX210544_BUS_64]       pc,
  input   wire  [`YSYX210544_BUS_32]       inst,

  // 从寄存器取出数据
  output  wire  [4 : 0]         rs1,
  input   wire  [`YSYX210544_BUS_64]       rs1_data,
  output  wire  [4 : 0]         rs2,
  input   wire  [`YSYX210544_BUS_64]       rs2_data,

  output  reg                   pc_jmp,
  output  reg   [`YSYX210544_BUS_64]       pc_jmpaddr
);

wire [4 : 0] opcode = inst[6  :  2];
wire [2 : 0] funct3 = inst[14 : 12];

wire inst_jalr  = opcode == 5'b11001;
wire inst_jal   = opcode == 5'b11011;
wire inst_b     = opcode == 5'b11000;
wire inst_beq   = inst_b && (funct3 == `FUNCT3_BEQ);
wire inst_bne   = inst_b && (funct3 == `FUNCT3_BNE);
wire inst_blt   = inst_b && (funct3 == `FUNCT3_BLT);
wire inst_bge   = inst_b && (funct3 == `FUNCT3_BGE);
wire inst_bltu  = inst_b && (funct3 == `FUNCT3_BLTU);
wire inst_bgeu  = inst_b && (funct3 == `FUNCT3_BGEU);

wire cond_beq   = rs1_data == rs2_data;
wire cond_bne   = rs1_data != rs2_data;
wire cond_blt   = ($signed(rs1_data) < $signed(rs2_data));
wire cond_bge   = ($signed(rs1_data) >= $signed(rs2_data));
wire cond_bltu  = rs1_data < rs2_data;
wire cond_bgeu  = rs1_data >= rs2_data;
wire cond_b     = cond_beq | cond_bne | cond_blt | cond_bge | cond_bltu | cond_bgeu;
wire jump_b     = inst_b & cond_b;

wire [`YSYX210544_BUS_64]I_imm   = { {52{inst[31]}}, inst[31 : 20] };
wire [`YSYX210544_BUS_64]J_imm   = { {44{inst[31]}}, inst[19 : 12], inst[20], inst[30 : 21], 1'b0 };
wire [`YSYX210544_BUS_64]B_imm   = { {52{inst[31]}}, inst[7], inst[30 : 25], inst[11 : 8], 1'b0 };

wire [`YSYX210544_BUS_64] jal_tgt    = pc + I_imm;
wire [`YSYX210544_BUS_64] jalr_tgt   = (rs1_data + J_imm) & (~1);
wire [`YSYX210544_BUS_64] b_tgt      = B_imm;

assign pc_jmp = rst ? 0 : inst_jal | inst_jalr | jump_b;

always @(*) begin
  if (rst) begin
    pc_jmpaddr = 0;
  end else begin
    if (inst_jal)         pc_jmpaddr = jal_tgt;
    else if (inst_jalr)   pc_jmpaddr = jalr_tgt;
    else if (jump_b)      pc_jmpaddr = b_tgt;
    else                  pc_jmpaddr = 0;
  end
end

endmodule