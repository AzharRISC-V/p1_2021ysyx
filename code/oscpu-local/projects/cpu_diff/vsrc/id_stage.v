
//--xuezhen--

`include "defines.v"

module id_stage(
  input wire rst,
  input wire [31 : 0]inst,
  input wire [`REG_BUS]rs1_data,
  input wire [`REG_BUS]rs2_data,
  
  
  output wire rs1_r_ena,
  output wire [4 : 0]rs1_r_addr,
  output wire rs2_r_ena,
  output wire [4 : 0]rs2_r_addr,
  output wire rd_w_ena,
  output wire [4 : 0]rd_w_addr,
  
  output wire [4 : 0]inst_type,
  output wire [7 : 0]inst_opcode,       // 用于区分不同指令的自定义编码
  output wire [`REG_BUS]op1,
  output wire [`REG_BUS]op2
);

// common fields
wire [6  : 0]opcode;
wire [4  : 0]rd;
wire [2  : 0]func3;
wire [4  : 0]rs1;
wire [4  : 0]rs2;
wire [6  : 0]func7;
wire [63 : 0]imm;           // 带符号扩展的imm

// I-type
wire [11 : 0]I_imm;
// S-type
wire [11 : 0]S_imm;
// B-type
wire [12 : 0]B_imm;
// U-type
wire [31 : 0]U_imm;
// J-type
wire [20 : 0]J_imm;

assign opcode = inst[6  :  0];
assign rd     = inst[11 :  7];
assign func3  = inst[14 : 12];
assign rs1    = inst[19 : 15];
assign func7  = inst[31 : 25];
assign I_imm  = { inst[31 : 20] };
assign S_imm  = { inst[31 : 25], inst[11 : 7] };
assign B_imm  = { inst[31], inst[7], inst[30 : 25], inst[11 : 8], 1'b0 };
assign U_imm  = { inst[31 : 12], 12'b0 };
assign J_imm  = { inst[31], inst[19 : 12], inst[20], inst[30 : 21], 1'b0 };
assign imm = {{52{I_imm[11]}}, I_imm};

// ===== 指令识别 =====

wire inst_addi =   ~opcode[2] & ~opcode[3] & opcode[4] & ~opcode[5] & ~opcode[6]
                & ~func3[0] & ~func3[1] & ~func3[2];

// 根据指令，可判断是6种指令类型种的哪一种？

// 确定指令类型、指令操作码

// 10000    arith inst      算术运算，第二个操作数是立即数
// 01000    logic           逻辑运算，两个操作数都是寄存器
// 00100    load-store      读写内存，
// 00010    j               是否跳转
// 00001    sys             系统指令
assign inst_type[4] = ( rst == 1'b1 ) ? 0 : inst_addi;

// 执行操作码（自定义的）
// 8b0001_0001      addi
// 8b....           其余指令
// 由于 RV32I 由 47条， 。。。， 2^8=256条，足够保存了。
assign inst_opcode[0] = (  rst == 1'b1 ) ? 0 : inst_addi;
assign inst_opcode[1] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[2] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[3] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[4] = (  rst == 1'b1 ) ? 0 : inst_addi;
assign inst_opcode[5] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[6] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[7] = (  rst == 1'b1 ) ? 0 : 0;




assign rs1_r_ena  = ( rst == 1'b1 ) ? 0 : inst_type[4];
assign rs1_r_addr = ( rst == 1'b1 ) ? 0 : ( inst_type[4] == 1'b1 ? rs1 : 0 );
assign rs2_r_ena  = 0;
assign rs2_r_addr = 0;

assign rd_w_ena   = ( rst == 1'b1 ) ? 0 : inst_type[4];
assign rd_w_addr  = ( rst == 1'b1 ) ? 0 : ( inst_type[4] == 1'b1 ? rd  : 0 );

assign op1 = ( rst == 1'b1 ) ? 0 : ( inst_type[4] == 1'b1 ? rs1_data : 0 );
assign op2 = ( rst == 1'b1 ) ? 0 : ( inst_type[4] == 1'b1 ? { {52{I_imm[11]}}, I_imm } : 0 );


endmodule
