
//--xuezhen--

`include "defines.v"

module id_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,
  input   wire  [`BUS_32]       inst,

  output  reg                   sig_memread,
  output  reg                   sig_memwrite,

  input   wire  [`BUS_64]       rs1_data,
  input   wire  [`BUS_64]       rs2_data,
  input   wire  [`BUS_64]       pc_cur,
  input   wire  [`BUS_64]       pc,

  output  wire                  rs1_ren,
  output  wire  [4 : 0]         rs1,
  output  wire                  rs2_ren,
  output  wire  [4 : 0]         rs2,
  output  wire  [4 : 0]         rd,

  output  reg                   mem_ren,
  output  wire  [`BUS_64]       mem_raddr,
  input   wire  [`BUS_64]       mem_rdata,
  output  wire                  mem_wen,
  output  wire  [`BUS_64]       mem_waddr,
  output  wire  [`BUS_64]       mem_wdata,
  output  wire  [`BUS_64]       mem_wmask,
  
  output  wire  [2 : 0]         inst_type,
  output  wire  [4 : 0]         inst_opcode,
  output  wire  [2 : 0]         inst_funct3,
  output  wire  [6 : 0]         inst_funct7,
  output  wire  [`BUS_64]       op1,            // 两个操作数
  output  wire  [`BUS_64]       op2,
  output  wire  [`BUS_64]       t1
);

// decode
wire [`BUS_64]imm;           // 带符号扩展的imm

wire [`BUS_32]R_imm;
wire [`BUS_32]I_imm;
wire [`BUS_32]S_imm;
wire [`BUS_32]B_imm;
wire [`BUS_32]U_imm;
wire [`BUS_32]J_imm;

assign inst_opcode  = inst[6  :  2];
assign rd           = inst[11 :  7];
assign inst_funct3  = inst[14 : 12];
assign rs1          = inst[19 : 15];
assign inst_funct7  = inst[31 : 25];

assign R_imm = 0;
assign I_imm  = { {20{inst[31]}}, inst[31 : 20] };
assign S_imm  = { {20{inst[31]}}, inst[31 : 25], inst[11 : 7] };
assign B_imm  = { {20{inst[31]}}, inst[7], inst[30 : 25], inst[11 : 8], 1'b0 };
assign U_imm  = { inst[31 : 12], 12'b0 };
assign J_imm  = { {12{inst[31]}}, inst[19 : 12], inst[20], inst[30 : 21], 1'b0 };

// sig_memread, sig_memwrite
assign sig_memread  = (!rst) ? 0 : (inst_opcode == `OPCODE_LB);
assign sig_memwrite = (!rst) ? 0 : (inst_opcode == `OPCODE_SB);

// inst-type
always@(*) begin
  if (rst)
    inst_type = 0;
  else begin
    case (inst_opcode)
      `OPCODE_LUI   : inst_type = `INST_U_TYPE;
      `OPCODE_AUIPC : inst_type = `INST_U_TYPE;
      `OPCODE_JAL   : inst_type = `INST_J_TYPE;
      `OPCODE_JALR  : inst_type = `INST_I_TYPE;
      `OPCODE_BEQ   : inst_type = `INST_B_TYPE;
      `OPCODE_LB    : inst_type = `INST_I_TYPE;
      `OPCODE_SB    : inst_type = `INST_S_TYPE;
      `OPCODE_ADDI  : inst_type = `INST_I_TYPE;
      `OPCODE_ADD   : inst_type = `INST_R_TYPE;
      `OPCODE_FENCE : inst_type = `INST_I_TYPE;
      `OPCODE_ENV   : inst_type = `INST_I_TYPE;
      default       : inst_type = 0;
    endcase
  end
end

// 立即数的值
reg [`BUS_32]imm0;
always@(*) begin
  if (rst)
    imm0 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : imm0 = R_imm;
      `INST_I_TYPE  : imm0 = I_imm;
      `INST_S_TYPE  : imm0 = S_imm;
      `INST_B_TYPE  : imm0 = B_imm;
      `INST_U_TYPE  : imm0 = U_imm;
      `INST_J_TYPE  : imm0 = J_imm;
      default       : imm0 = 0;
    endcase
  end
end
assign imm = {{32{imm0[31]}}, imm0};

// rs1读使能
reg rs1_ren0;
always@(*) begin
  if (rst) 
    rs1_ren0 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : rs1_ren0 = 1;
      `INST_I_TYPE  : rs1_ren0 = 1;
      `INST_S_TYPE  : rs1_ren0 = 1;
      `INST_B_TYPE  : rs1_ren0 = 1;
      default       : rs1_ren0 = 0;
    endcase
  end
end
assign rs1_ren = (instcycle_cnt_val == 3) ? rs1_ren0 : 0;

// rs2读使能
reg rs2_ren0;
always@(*) begin
  if (rst)
    rs2_ren0 = 0;
  case (inst_type)
    `INST_R_TYPE  : rs2_ren0 = 1;
    `INST_S_TYPE  : rs2_ren0 = 1;
    `INST_B_TYPE  : rs2_ren0 = 1;
    default       : rs2_ren0 = 0;
  endcase
end
assign rs2_ren = (instcycle_cnt_val == 3) ? rs2_ren0 : 0;

// mem_ren
always@(*) begin
  if (rst) 
    mem_ren = 0;
  else
    mem_ren = (inst_opcode == `OPCODE_LB) ? 1 : 0;
end

// mem_raddr
assign mem_raddr = (rs1_data + imm);

// mem_wen
always@(*) begin
  if (rst) 
    mem_wen = 0;
  else
    mem_wen = (inst_type == `INST_S_TYPE) ? 1 : 0;
end

// mem_waddr
assign mem_waddr = ($signed(rs1_data) + $signed(imm));

// mem_wdata
assign mem_wdata = (rs2_data);

// mem_wmask
always@(*) begin
  if (rst)
    mem_wmask = 0;
  else
    if (inst_type == `INST_S_TYPE)
      case (inst_funct3)
        `FUNCT3_SB    : mem_wmask = 'hFF;
        `FUNCT3_SH    : mem_wmask = 'hFFFF;
        `FUNCT3_SW    : mem_wmask = 64'h00000000_FFFFFFFF;
        `FUNCT3_SD    : mem_wmask = 64'hFFFFFFFF_FFFFFFFF;
        default       : mem_wmask = 0;
      endcase
    else
      mem_wmask = 0;
end

// op1
always@(*) begin
  if (rst) 
    op1 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : op1 = rs1_data;
      `INST_B_TYPE  : op1 = rs1_data;
      `INST_I_TYPE  : op1 = rs1_data;
      `INST_J_TYPE  : op1 = pc + 4;
      `INST_U_TYPE  : begin
        if (inst_opcode == `OPCODE_AUIPC)
          op1 = pc;
        else
          op1 = 0;
      end
      default       : op1 = 0;
    endcase
  end
end

// op2
always@(*) begin
  if (rst) 
    op2 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : op2 = rs2_data;
      `INST_B_TYPE  : op2 = rs2_data;
      `INST_I_TYPE  : op2 = imm;
      `INST_J_TYPE  : op2 = pc + imm;
      `INST_U_TYPE  : begin
        if (inst_opcode == `OPCODE_AUIPC)   op2 = imm;
        else                                op2 = 0;
      end
      default       : op2 = 0;
    endcase
  end
end

// t1
always@(*) begin
  if (!rst) 
    t1 = 0;
  else begin
    case (inst_opcode)
      `OPCODE_JALR  : t1 = pc + 4;
      `OPCODE_BEQ   : t1 = pc + imm;
      default       : t1 = 0;
    endcase
  end
end

endmodule
