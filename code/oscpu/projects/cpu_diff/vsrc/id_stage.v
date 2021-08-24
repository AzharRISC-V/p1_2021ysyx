
//--xuezhen--

`include "defines.v"

module id_stage(
  input   wire              rst,
  input   wire  [`BUS_32]   inst,
  input   wire  [`BUS_64]   rs1_data,
  input   wire  [`BUS_64]   rs2_data,
  input   wire  [`BUS_64]   pc_cur,
  input   wire  [`BUS_64]   pc,

  output  wire              rs1_r_ena,
  output  wire  [4 : 0]     rs1_r_addr,
  output  wire              rs2_r_ena,
  output  wire  [4 : 0]     rs2_r_addr,
  output  wire              rd_w_ena,
  output  wire  [4 : 0]     rd_w_addr,

  output  wire              mem_ren,
  output  wire  [`BUS_64]   mem_raddr,
  input   wire  [`BUS_64]   mem_rdata,
  output  wire              mem_wen,
  output  wire  [`BUS_64]   mem_waddr,
  output  wire  [`BUS_64]   mem_wdata,
  output  wire  [`BUS_64]   mem_wmask,
  
  output  wire  [2 : 0]     inst_type,
  output  wire  [4 : 0]     inst_opcode,
  output  wire  [2 : 0]     inst_funct3,
  output  wire  [6 : 0]     inst_funct7,
  output  wire  [`BUS_64]   op1,            // 两个操作数
  output  wire  [`BUS_64]   op2,
  output  wire  [`BUS_64]   t1
);

// decode
wire [4  : 0]rd;
wire [4  : 0]rs1;
wire [4  : 0]rs2;
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

// inst-type
reg [2 : 0]inst_type0;
always@(*) begin
  if (rst == 1'b1) inst_type0 = 0;
  else begin
    case (inst_opcode)
      `OPCODE_LUI   : inst_type0 = `INST_U_TYPE;
      `OPCODE_AUIPC : inst_type0 = `INST_U_TYPE;
      `OPCODE_JAL   : inst_type0 = `INST_J_TYPE;
      `OPCODE_JALR  : inst_type0 = `INST_I_TYPE;
      `OPCODE_BEQ   : inst_type0 = `INST_B_TYPE;
      `OPCODE_LB    : inst_type0 = `INST_I_TYPE;
      `OPCODE_SB    : inst_type0 = `INST_S_TYPE;
      `OPCODE_ADDI  : inst_type0 = `INST_I_TYPE;
      `OPCODE_ADD   : inst_type0 = `INST_R_TYPE;
      `OPCODE_FENCE : inst_type0 = `INST_I_TYPE;
      `OPCODE_ENV   : inst_type0 = `INST_I_TYPE;
      default       : inst_type0 = 0;
    endcase
  end
end
assign inst_type = inst_type0;

// 立即数的值
reg [`BUS_32]imm0;
always@(*) begin
  if (rst == 1'b1) imm0 = 0;
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
reg rs1_r_ena0;
always@(*) begin
  if (rst == 1'b1) rs1_r_ena0 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : rs1_r_ena0 = 1;
      `INST_I_TYPE  : rs1_r_ena0 = 1;
      `INST_S_TYPE  : rs1_r_ena0 = 1;
      `INST_B_TYPE  : rs1_r_ena0 = 1;
      default       : rs1_r_ena0 = 0;
    endcase
  end
end
assign rs1_r_ena = rs1_r_ena0;

// rs1读地址
assign rs1_r_addr = rs1;

// rs2读使能
reg rs2_r_ena0;
always@(*) begin
  if (rst == 1'b1) rs2_r_ena0 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : rs2_r_ena0 = 1;
      `INST_S_TYPE  : rs2_r_ena0 = 1;
      `INST_B_TYPE  : rs2_r_ena0 = 1;
      default       : rs2_r_ena0 = 0;
    endcase
  end
end
assign rs2_r_ena = rs2_r_ena0;

// rs2读地址
assign rs2_r_addr = rs2;

// rd写使能
reg rd_w_ena0;
always@(*) begin
  if (rst == 1'b1) rd_w_ena0 = 0;
  else
    case (inst_opcode)
      `OPCODE_AUIPC     : begin rd_w_ena0 = 1;  end
      `OPCODE_ADDI      : begin rd_w_ena0 = 1;  end
      `OPCODE_JAL       : begin rd_w_ena0 = 1;  end
      `OPCODE_JALR      : begin rd_w_ena0 = 1;  end
      `OPCODE_LB        : begin rd_w_ena0 = 1;  end
      default           : begin rd_w_ena0 = 0;  end
    endcase
end
assign rd_w_ena = rd_w_ena0;

// rd写地址
assign rd_w_addr = rd;

// mem_ren
reg mem_ren0;
always@(*) begin
  if (rst == 1'b1) mem_ren0 = 0;
  else
    mem_ren0 = (inst_opcode == `OPCODE_LB) ? 1 : 0;
end
assign mem_ren = mem_ren0;

// mem_raddr
assign mem_raddr = (rs1_data + imm);

// mem_wen
reg mem_wen0;
always@(*) begin
  if (rst == 1'b1) mem_wen0 = 0;
  else
    mem_wen0 = (inst_type == `INST_S_TYPE) ? 1 : 0;
end
assign mem_wen = mem_wen0;

// mem_waddr
assign mem_waddr = (rs1_data + S_imm) >> 3;

// mem_wdata
assign mem_wdata = (rs2_data);

// mem_wmask
reg [`BUS_64] mem_wmask0;
always@(*) begin
  if (rst == 1'b1) mem_wmask0 = 0;
  else
    if (inst_type == `INST_S_TYPE)
      case (inst_funct3)
        `FUNCT3_SB    : mem_wmask0 = 'hFF;
        `FUNCT3_SH    : mem_wmask0 = 'hFFFF;
        `FUNCT3_SW    : mem_wmask0 = 64'h00000000_FFFFFFFF;
        `FUNCT3_SD    : mem_wmask0 = 64'hFFFFFFFF_FFFFFFFF;
        default       : mem_wmask0 = 0;
      endcase
    else
      mem_wmask0 = 0;
end
assign mem_wmask = mem_wmask0;

// op1
reg [`BUS_64] op1_0;
always@(*) begin
  if (rst == 1'b1) op1_0 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : op1_0 = rs1_data;
      `INST_B_TYPE  : op1_0 = rs1_data;
      `INST_I_TYPE  : op1_0 = rs1_data;
      `INST_J_TYPE  : op1_0 = pc + 4;
      `INST_U_TYPE  : begin
        if (inst_opcode == `OPCODE_AUIPC)
          op1_0 = pc;
        else
          op1_0 = 0;
      end
      default       : op1_0 = 0;
    endcase
  end
end
assign op1 = op1_0;

// op2
reg [`BUS_64] op2_0;
always@(*) begin
  if (rst == 1'b1) op2_0 = 0;
  else begin
    case (inst_type)
      `INST_R_TYPE  : op2_0 = rs2_data;
      `INST_B_TYPE  : op2_0 = rs2_data;
      `INST_I_TYPE  : op2_0 = imm;
      `INST_J_TYPE  : op2_0 = pc + imm;
      `INST_U_TYPE  : begin
        if (inst_opcode == `OPCODE_AUIPC)   op2_0 = imm;
        else                                op2_0 = 0;
      end
      default       : op2_0 = 0;
    endcase
  end
end
assign op2 = op2_0;

// t1
reg [`BUS_64] t1_0;
always@(*) begin
  if (rst == 1'b1) t1_0 = 0;
  else begin
    case (inst_opcode)
      `OPCODE_JALR  : t1_0 = pc + 4;
      `OPCODE_BEQ   : t1_0 = pc + imm;
      default       : t1_0 = 0;
    endcase
  end
end
assign t1 = t1_0;

endmodule
