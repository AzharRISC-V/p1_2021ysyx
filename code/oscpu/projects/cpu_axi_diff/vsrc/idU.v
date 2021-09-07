
// ZhengpuShi

// Instruction Decode Unit, 组合逻辑电路

`include "defines.v"

module idU(
  input   wire  [`BUS_32]     i_inst,
  input   wire  [`BUS_64]     i_rs1_data,
  input   wire  [`BUS_64]     i_rs2_data,
  input   wire  [`BUS_64]     i_pc_old,
  input   wire  [`BUS_64]     i_pc,
  input   wire  [`BUS_64]     i_pc_pred,
  output  reg                 o_rs1_ren,
  output  wire  [4 : 0]       o_rs1,
  output  wire                o_rs2_ren,
  output  wire  [4 : 0]       o_rs2,
  output  wire  [4 : 0]       o_rd,
  output  wire                o_memren,
  output  wire  [`BUS_64]     o_memaddr,
  output  wire                o_memwen,
  output  wire  [`BUS_64]     o_memwdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg   [1 : 0]       o_csr_op,
  output  reg   [`BUS_64]     o_csr_wdata,
  input   reg   [`BUS_64]     i_csr_rdata,
  output  wire  [2 : 0]       o_itype,
  output  wire  [6 : 0]       o_opcode,
  output  wire  [2 : 0]       o_funct3,
  output  wire  [6 : 0]       o_funct7,
  output  wire  [`BUS_64]     o_op1,            // 两个操作数
  output  wire  [`BUS_64]     o_op2,
  output  wire  [`BUS_64]     o_t1,
  output  wire  [`BUS_64]     o_pc_pred,
  output  wire                o_skip_difftest
);


assign o_pc_pred = i_pc_pred;

// decode
// 带符号扩展的imm
wire  [`BUS_64]               imm;
wire  [`BUS_32]               R_imm;
wire  [`BUS_32]               I_imm;
wire  [`BUS_32]               S_imm;
wire  [`BUS_32]               B_imm;
wire  [`BUS_32]               U_imm;
wire  [`BUS_32]               J_imm;

wire  [5 : 0]                 shamt;
wire  [`BUS_64]               shamt_64;   // 扩展为64位后的值

assign o_opcode   = i_inst[6  :  0];
assign o_rd       = i_inst[11 :  7];
assign o_funct3   = i_inst[14 : 12];
assign o_rs1      = i_inst[19 : 15];
assign o_rs2      = i_inst[24 : 20];
assign o_funct7   = i_inst[31 : 25];

assign R_imm    = 0;
assign I_imm    = { {20{i_inst[31]}}, i_inst[31 : 20] };
assign S_imm    = { {20{i_inst[31]}}, i_inst[31 : 25], i_inst[11 : 7] };
assign B_imm    = { {20{i_inst[31]}}, i_inst[7], i_inst[30 : 25], i_inst[11 : 8], 1'b0 };
assign U_imm    = { i_inst[31 : 12], 12'b0 };
assign J_imm    = { {12{i_inst[31]}}, i_inst[19 : 12], i_inst[20], i_inst[30 : 21], 1'b0 };
assign shamt    = i_inst[25 : 20];
assign shamt_64 = {58'd0, shamt};

// i_inst-type

// // 以后有机会再优化这部分组合逻辑
// // (区分6种类型)
// wire itype_R = rst ? 0 : (o_opcode == `OPCODE_ADD );
// wire itype_I = rst ? 0 : (o_opcode == `OPCODE_JALR) || (o_opcode == `OPCODE_LB   ) || (o_opcode == `OPCODE_ADDI ) || (o_opcode == `OPCODE_FENCE) || (o_opcode == `OPCODE_ENV);
// wire itype_U = rst ? 0 : (o_opcode == `OPCODE_LUI ) || (o_opcode == `OPCODE_AUIPC);
// wire itype_S = rst ? 0 : (o_opcode == `OPCODE_SB  );
// wire itype_B = rst ? 0 : (o_opcode == `OPCODE_BEQ );
// wire itype_J = rst ? 0 : (o_opcode == `OPCODE_JAL );
// // (转换为0~5的数字)
// wire [2:0] itype_R_val = 0;
// wire [2:0] itype_I_val = itype_I ? 1 : 0;
// wire [2:0] itype_U_val = itype_U ? 2 : 0;
// wire [2:0] itype_S_val = itype_S ? 3 : 0;
// wire [2:0] itype_B_val = itype_B ? 4 : 0;
// wire [2:0] itype_J_val = itype_J ? 5 : 0;
// // wire [5:0] itype_sum = itype_R_val + itype_I_val + itype_U_val + itype_S_val + itype_B_val + itype_J_val;
// // assign o_itype = itype_sum[2:0];

// instruction type : R,I,S,B,U,J
always@(*) begin
  case (o_opcode)
    `OPCODE_LUI   : o_itype = `INST_U_TYPE;
    `OPCODE_AUIPC : o_itype = `INST_U_TYPE;
    `OPCODE_JAL   : o_itype = `INST_J_TYPE;
    `OPCODE_JALR  : o_itype = `INST_I_TYPE;
    `OPCODE_BEQ   : o_itype = `INST_B_TYPE;
    `OPCODE_LB    : o_itype = `INST_I_TYPE;
    `OPCODE_SB    : o_itype = `INST_S_TYPE;
    `OPCODE_ADDI  : o_itype = `INST_I_TYPE;
    `OPCODE_ADD   : o_itype = `INST_R_TYPE;
    `OPCODE_FENCE : o_itype = `INST_I_TYPE;
    `OPCODE_ENV   : o_itype = `INST_I_TYPE;
    `OPCODE_ADDIW : o_itype = `INST_I_TYPE;
    `OPCODE_ADDW  : o_itype = `INST_R_TYPE;
    default       : o_itype = 0;
  endcase
end

// 立即数的值
reg [`BUS_32]imm0;
always@(*) begin
  case (o_itype)
    `INST_R_TYPE  : imm0 = R_imm;
    `INST_I_TYPE  : imm0 = I_imm;
    `INST_S_TYPE  : imm0 = S_imm;
    `INST_B_TYPE  : imm0 = B_imm;
    `INST_U_TYPE  : imm0 = U_imm;
    `INST_J_TYPE  : imm0 = J_imm;
    default       : imm0 = 0;
  endcase
end
assign imm = {{32{imm0[31]}}, imm0};

// rs1读使能
always @(*) begin
  case (o_itype)
    `INST_R_TYPE  : o_rs1_ren = 1;
    `INST_I_TYPE  : o_rs1_ren = 1;
    `INST_S_TYPE  : o_rs1_ren = 1;
    `INST_B_TYPE  : o_rs1_ren = 1;
    default       : o_rs1_ren = 0;
  endcase
end

// rs2读使能
always @(*) begin
  case (o_itype)
    `INST_R_TYPE  : o_rs2_ren = 1;
    `INST_S_TYPE  : o_rs2_ren = 1;
    `INST_B_TYPE  : o_rs2_ren = 1;
    default       : o_rs2_ren = 0;
  endcase
end

// mem_ren
assign o_memren = (o_opcode == `OPCODE_LB) ? 1 : 0;

// mem_addr
assign o_memaddr = (o_memren | o_memwen) ? $signed(i_rs1_data) + $signed(imm) : 0;

// mem_wen
assign o_memwen = (o_itype == `INST_S_TYPE) ? 1 : 0;

// mem_wdata
assign o_memwdata = i_rs2_data;

// o_op1
always @(*) begin
  case (o_itype)
    `INST_R_TYPE  : o_op1 = i_rs1_data;
    `INST_B_TYPE  : o_op1 = i_rs1_data;
    `INST_I_TYPE  : o_op1 = i_rs1_data;
    `INST_J_TYPE  : o_op1 = i_pc + 4;
    `INST_U_TYPE  : begin
      if (o_opcode == `OPCODE_LUI)            o_op1 = imm;
      else if (o_opcode == `OPCODE_AUIPC)     o_op1 = i_pc;
      else                                  o_op1 = 0;
    end
    default       : o_op1 = 0;
  endcase
end

// o_op2
always @(*) begin
  case (o_itype)
    `INST_R_TYPE  : o_op2 = i_rs2_data;
    `INST_B_TYPE  : o_op2 = i_rs2_data;
    `INST_I_TYPE  : begin
      case (o_funct3)
        `FUNCT3_SLLI  : o_op2 = shamt_64;
        `FUNCT3_SRLI  : o_op2 = shamt_64;
        default       : o_op2 = imm;
      endcase
    end
    `INST_J_TYPE  : o_op2 = i_pc + imm;
    `INST_U_TYPE  : begin
      if (o_opcode == `OPCODE_AUIPC)   o_op2 = imm;
      else                           o_op2 = 0;
    end
    default       : o_op2 = 0;
  endcase
end

// o_t1
always @(*) begin
  case (o_opcode)
    `OPCODE_JALR  : o_t1 = i_pc + 4;
    `OPCODE_BEQ   : o_t1 = i_pc + imm;
    default       : o_t1 = 0;
  endcase
end

// ------------- csr -----------------

// o_csr_op
always @(*) begin
  if (o_opcode == `OPCODE_CSR) begin
    case (o_funct3)
      `FUNCT3_CSRRW   : o_csr_op = 2'b01;
      `FUNCT3_CSRRS   : o_csr_op = 2'b10;
      `FUNCT3_CSRRC   : o_csr_op = 2'b11;
      `FUNCT3_CSRRWI  : o_csr_op = 2'b01;
      `FUNCT3_CSRRSI  : o_csr_op = 2'b11;
      `FUNCT3_CSRRCI  : o_csr_op = 2'b11;
      default         : o_csr_op = 0;
    endcase
  end
  else begin
    o_csr_op = 0;
  end
end

// csr_inactive
wire csr_inactive = o_csr_op == 2'b00;

// o_csr_addr
assign o_csr_addr = i_inst[31 : 20];

// csr_zimm
wire [`BUS_64] csr_zimm = {{60{i_inst[19]}}, i_inst[18:15]};

// o_csr_wdata
always@(*) begin
  if (o_opcode == `OPCODE_CSR) begin
    case (o_funct3)
      `FUNCT3_CSRRW   : o_csr_wdata = i_rs1_data;
      `FUNCT3_CSRRS   : o_csr_wdata = i_rs1_data;
      `FUNCT3_CSRRC   : o_csr_wdata = i_rs1_data;
      `FUNCT3_CSRRWI  : o_csr_wdata = csr_zimm;
      `FUNCT3_CSRRSI  : o_csr_wdata = csr_zimm;
      `FUNCT3_CSRRCI  : o_csr_wdata = csr_zimm;
      default         : o_csr_wdata = 0;
    endcase
  end
  else begin
    o_csr_wdata = 0;
  end
end

// 让REF跳过指令比对
wire mem_addr_is_device = (o_memaddr & ~(64'hFFF)) == 64'h2000_0000;

// o_skip_difftest
assign o_skip_difftest = 
  (i_inst == 32'h7b)                 // putch
  | (o_opcode == `OPCODE_CSR)   
  | mem_addr_is_device
  ;


endmodule
