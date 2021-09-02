
//--xuezhen--

`include "defines.v"

module id_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   wire  [`BUS_32]       inst,

  input   wire  [`BUS_64]       rs1_data,
  input   wire  [`BUS_64]       rs2_data,
  input   wire  [`BUS_64]       pc_old,
  input   wire  [`BUS_64]       pc,

  output  reg                   rs1_ren,
  output  wire  [4 : 0]         rs1,
  output  wire                  rs2_ren,
  output  wire  [4 : 0]         rs2,
  output  wire  [4 : 0]         rd,

  output  wire                  mem_ren,
  output  wire  [`BUS_64]       mem_addr,
  output  wire                  mem_wen,
  output  wire  [`BUS_64]       mem_wdata,

  output  reg   [11 : 0]        csr_addr,
  output  reg   [1 : 0]         csr_op,
  output  reg   [`BUS_64]       csr_wdata,
  input   reg   [`BUS_64]       csr_rdata,
  
  output  wire  [2 : 0]         itype,
  output  wire  [4 : 0]         opcode,
  output  wire  [2 : 0]         funct3,
  output  wire  [6 : 0]         funct7,
  output  wire  [`BUS_64]       op1,            // 两个操作数
  output  wire  [`BUS_64]       op2,
  output  wire  [`BUS_64]       t1,

  output  wire                  skip_difftest
);

// decode
wire [`BUS_64]imm;           // 带符号扩展的imm

wire [`BUS_32]R_imm;
wire [`BUS_32]I_imm;
wire [`BUS_32]S_imm;
wire [`BUS_32]B_imm;
wire [`BUS_32]U_imm;
wire [`BUS_32]J_imm;

wire  [5 : 0]   shamt;
wire  [`BUS_64] shamt_64;   // 扩展为64位后的值

assign opcode = rst ? 0 : inst[6  :  2];
assign rd     = rst ? 0 : inst[11 :  7];
assign funct3 = rst ? 0 : inst[14 : 12];
assign rs1    = rst ? 0 : inst[19 : 15];
assign rs2    = rst ? 0 : inst[24 : 20];
assign funct7 = rst ? 0 : inst[31 : 25];

assign R_imm  = rst ? 0 : 0;
assign I_imm  = rst ? 0 : { {20{inst[31]}}, inst[31 : 20] };
assign S_imm  = rst ? 0 : { {20{inst[31]}}, inst[31 : 25], inst[11 : 7] };
assign B_imm  = rst ? 0 : { {20{inst[31]}}, inst[7], inst[30 : 25], inst[11 : 8], 1'b0 };
assign U_imm  = rst ? 0 : { inst[31 : 12], 12'b0 };
assign J_imm  = rst ? 0 : { {12{inst[31]}}, inst[19 : 12], inst[20], inst[30 : 21], 1'b0 };

assign shamt  = rst ? 0 : inst[25 : 20];
assign shamt_64 = {58'd0, shamt};

// inst-type

// // 以后有机会再优化这部分组合逻辑
// // (区分6种类型)
// wire itype_R = rst ? 0 : (opcode == `OPCODE_ADD );
// wire itype_I = rst ? 0 : (opcode == `OPCODE_JALR) || (opcode == `OPCODE_LB   ) || (opcode == `OPCODE_ADDI ) || (opcode == `OPCODE_FENCE) || (opcode == `OPCODE_ENV);
// wire itype_U = rst ? 0 : (opcode == `OPCODE_LUI ) || (opcode == `OPCODE_AUIPC);
// wire itype_S = rst ? 0 : (opcode == `OPCODE_SB  );
// wire itype_B = rst ? 0 : (opcode == `OPCODE_BEQ );
// wire itype_J = rst ? 0 : (opcode == `OPCODE_JAL );
// // (转换为0~5的数字)
// wire [2:0] itype_R_val = 0;
// wire [2:0] itype_I_val = itype_I ? 1 : 0;
// wire [2:0] itype_U_val = itype_U ? 2 : 0;
// wire [2:0] itype_S_val = itype_S ? 3 : 0;
// wire [2:0] itype_B_val = itype_B ? 4 : 0;
// wire [2:0] itype_J_val = itype_J ? 5 : 0;
// // wire [5:0] itype_sum = itype_R_val + itype_I_val + itype_U_val + itype_S_val + itype_B_val + itype_J_val;
// // assign itype = itype_sum[2:0];

always@(*) begin
  if (rst)
    itype = 0;
  else begin
    case (opcode)
      `OPCODE_LUI   : itype = `INST_U_TYPE;
      `OPCODE_AUIPC : itype = `INST_U_TYPE;
      `OPCODE_JAL   : itype = `INST_J_TYPE;
      `OPCODE_JALR  : itype = `INST_I_TYPE;
      `OPCODE_BEQ   : itype = `INST_B_TYPE;
      `OPCODE_LB    : itype = `INST_I_TYPE;
      `OPCODE_SB    : itype = `INST_S_TYPE;
      `OPCODE_ADDI  : itype = `INST_I_TYPE;
      `OPCODE_ADD   : itype = `INST_R_TYPE;
      `OPCODE_FENCE : itype = `INST_I_TYPE;
      `OPCODE_ENV   : itype = `INST_I_TYPE;
      `OPCODE_ADDIW : itype = `INST_I_TYPE;
      `OPCODE_ADDW  : itype = `INST_R_TYPE;
      default       : itype = 0;
    endcase
  end
end

// 立即数的值
reg [`BUS_32]imm0;
always@(*) begin
  if (rst)
    imm0 = 0;
  else begin
    case (itype)
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
always @(*) begin
  if (rst) 
    rs1_ren = 0;
  else begin
    case (itype)
      `INST_R_TYPE  : rs1_ren = 1;
      `INST_I_TYPE  : rs1_ren = 1;
      `INST_S_TYPE  : rs1_ren = 1;
      `INST_B_TYPE  : rs1_ren = 1;
      default       : rs1_ren = 0;
    endcase
  end
end

// rs2读使能
always @(*) begin
  if (rst)
    rs2_ren = 0;
  else begin
    case (itype)
      `INST_R_TYPE  : rs2_ren = 1;
      `INST_S_TYPE  : rs2_ren = 1;
      `INST_B_TYPE  : rs2_ren = 1;
      default       : rs2_ren = 0;
    endcase
  end
end

// mem_ren
always @(*) begin
  if (rst) begin
    mem_ren = 0;
  end
  else begin
    mem_ren = (opcode == `OPCODE_LB) ? 1 : 0;
  end
end

// mem_addr
assign mem_addr = (mem_ren | mem_wen) ? $signed(rs1_data) + $signed(imm) : 0;

// mem_wen
always @(*) begin
  if (rst) 
    mem_wen = 0;
  else
    mem_wen = (itype == `INST_S_TYPE) ? 1 : 0;
end

// mem_wdata
always @(*) begin
  if (rst)
    mem_wdata = 0;
  else begin
    mem_wdata = rs2_data;
  end
end

// op1
always @(*) begin
  if (rst) 
    op1 = 0;
  else begin
    case (itype)
      `INST_R_TYPE  : op1 = rs1_data;
      `INST_B_TYPE  : op1 = rs1_data;
      `INST_I_TYPE  : op1 = rs1_data;
      `INST_J_TYPE  : op1 = pc + 4;
      `INST_U_TYPE  : begin
        if (opcode == `OPCODE_LUI)            op1 = imm;
        else if (opcode == `OPCODE_AUIPC)     op1 = pc;
        else                                  op1 = 0;
      end
      default       : op1 = 0;
    endcase
  end
end

// op2
always @(*) begin
  if (rst) 
    op2 = 0;
  else begin
    case (itype)
      `INST_R_TYPE  : op2 = rs2_data;
      `INST_B_TYPE  : op2 = rs2_data;
      `INST_I_TYPE  : begin
        case (funct3)
          `FUNCT3_SLLI  : op2 = shamt_64;
          `FUNCT3_SRLI  : op2 = shamt_64;
          default       : op2 = imm;
        endcase
      end
      `INST_J_TYPE  : op2 = pc + imm;
      `INST_U_TYPE  : begin
        if (opcode == `OPCODE_AUIPC)   op2 = imm;
        else                           op2 = 0;
      end
      default       : op2 = 0;
    endcase
  end
end

// t1
always @(*) begin
  if (rst) 
    t1 = 0;
  else begin
    case (opcode)
      `OPCODE_JALR  : t1 = pc + 4;
      `OPCODE_BEQ   : t1 = pc + imm;
      default       : t1 = 0;
    endcase
  end
end

// ------------- csr -----------------

// csr_op
always @(*) begin
  if (rst)
    csr_op = 0;
  else begin
    if (opcode == `OPCODE_CSR) begin
      case (funct3)
        `FUNCT3_CSRRW   : csr_op = 2'b01;
        `FUNCT3_CSRRS   : csr_op = 2'b10;
        `FUNCT3_CSRRC   : csr_op = 2'b11;
        `FUNCT3_CSRRWI  : csr_op = 2'b01;
        `FUNCT3_CSRRSI  : csr_op = 2'b11;
        `FUNCT3_CSRRCI  : csr_op = 2'b11;
        default         : csr_op = 0;
      endcase
    end
    else begin
      csr_op = 0;
    end
  end
end

// csr_inactive
wire csr_inactive = csr_op == 2'b00;

// csr_addr
assign csr_addr = csr_inactive ?  0 : inst[31 : 20];

// csr_zimm
wire [`BUS_64] csr_zimm = csr_inactive ? 0 : {{60{inst[19]}}, inst[18:15]};

// csr_wdata
always@(*) begin
  if (csr_inactive)
    csr_wdata = 0;
  else begin
    if (opcode == `OPCODE_CSR) begin
      case (funct3)
        `FUNCT3_CSRRW   : csr_wdata = rs1_data;
        `FUNCT3_CSRRS   : csr_wdata = rs1_data;
        `FUNCT3_CSRRC   : csr_wdata = rs1_data;
        `FUNCT3_CSRRWI  : csr_wdata = csr_zimm;
        `FUNCT3_CSRRSI  : csr_wdata = csr_zimm;
        `FUNCT3_CSRRCI  : csr_wdata = csr_zimm;
        default         : csr_wdata = 0;
      endcase
    end
    else begin
      csr_wdata = 0;
    end
  end
end

// 让REF跳过指令比对
wire mem_addr_is_device = (mem_addr & ~(64'hFFF)) == 64'h2000_0000;

// skip_difftest
assign skip_difftest = 
  (inst == 7)                 // putch
  | (opcode == `OPCODE_CSR)   
  | mem_addr_is_device
  ;
  
endmodule
