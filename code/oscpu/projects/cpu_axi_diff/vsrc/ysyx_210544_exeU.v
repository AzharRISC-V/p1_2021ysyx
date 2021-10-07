
// ZhengpuShi

// Execute Unit, 组合逻辑电路

`include "defines.v"

module ysyx_210544_exeU(
  input   wire                ena,
  input   wire  [7 : 0]       i_inst_opcode,
  input   wire  [`BUS_64]     i_op1,
  input   wire  [`BUS_64]     i_op2,
  input   wire  [`BUS_64]     i_op3,
  input   wire  [`BUS_64]     i_csr_rdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg                 o_csr_ren,
  output  reg                 o_csr_wen,
  output  reg   [`BUS_64]     o_csr_wdata,
  output  reg                 o_pc_jmp,
  output  reg   [`BUS_64]     o_pc_jmpaddr,
  output  wire  [`BUS_64]     o_rd_wdata,
  output  reg                 o_exeU_skip_cmt    // 这里也会发现需要跳过提交的指令，比如 csr mcycle
);

wire i_disable;
wire [63:0] reg64_t1;
wire [63:0] reg64_t2;
wire [63:0] reg64_t3;
wire [63:0] reg64_t4;
wire [31:0] reg32_t1;
wire inst_csr;



assign i_disable = !ena;
assign reg64_t1 = i_op1 + i_op2;
assign reg64_t2 = i_op1 << i_op2[5:0];
assign reg64_t3 = i_op1 - $signed(i_op2);
assign reg64_t4 = i_op1 << i_op2[4:0];
assign reg32_t1 = i_op1[31:0] >> i_op2[4:0];

always @(*) begin
  if( i_disable ) begin
    o_rd_wdata = `ZERO_WORD;
  end
  else begin
    case( i_inst_opcode )
      `INST_ADDI    : begin o_rd_wdata = i_op1 + i_op2;  end
      `INST_ADD     : begin o_rd_wdata = i_op1 + i_op2;  end
      `INST_SUB     : begin o_rd_wdata = i_op1 - i_op2;  end
      `INST_SUBW    : begin o_rd_wdata = {{33{reg64_t3[31]}}, reg64_t3[30:0]}; end
      `INST_ADDIW   : begin o_rd_wdata = {{33{reg64_t1[31]}}, reg64_t1[30:0]}; end
      `INST_AND     : begin o_rd_wdata = i_op1 & i_op2;  end
      `INST_ANDI    : begin o_rd_wdata = i_op1 & i_op2;  end
      `INST_OR      : begin o_rd_wdata = i_op1 | i_op2;  end
      `INST_ORI     : begin o_rd_wdata = i_op1 | i_op2;  end
      `INST_XOR     : begin o_rd_wdata = i_op1 ^ i_op2;  end
      `INST_XORI    : begin o_rd_wdata = i_op1 ^ i_op2;  end
      `INST_SLL     : begin o_rd_wdata = i_op1 << i_op2[5:0]; end
      `INST_SLLI    : begin o_rd_wdata = i_op1 << i_op2[5:0]; end
      `INST_SLLIW   : begin o_rd_wdata = {{33{reg64_t2[31]}}, reg64_t2[30:0]}; end
      `INST_SLLW    : begin o_rd_wdata = {{33{reg64_t4[31]}}, reg64_t4[30:0]}; end
      `INST_SLT     : begin o_rd_wdata = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
      `INST_SLTI    : begin o_rd_wdata = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
      `INST_SLTIU   : begin o_rd_wdata = i_op1 < i_op2 ? 1 : 0; end
      `INST_SLTU    : begin o_rd_wdata = (i_op1 < i_op2) ? 1 : 0; end
      `INST_SRA     : begin o_rd_wdata = $signed(i_op1) >>> i_op2[5:0]; end
      `INST_SRAW    : begin o_rd_wdata = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
      `INST_SRAI    : begin o_rd_wdata = $signed(i_op1) >>> i_op2[5:0]; end
      `INST_SRAIW   : begin o_rd_wdata = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
      `INST_SRL     : begin o_rd_wdata = i_op1 >> i_op2[5:0]; end
      `INST_SRLI    : begin o_rd_wdata = i_op1 >> i_op2[5:0]; end
      `INST_SRLW    : begin o_rd_wdata = {{32{reg32_t1[31]}}, reg32_t1}; end
      `INST_SRLIW   : begin o_rd_wdata = {{32{reg32_t1[31]}}, reg32_t1}; end
      `INST_LUI     : begin o_rd_wdata = i_op1; end
      `INST_AUIPC   : begin o_rd_wdata = i_op1 + i_op2; end
      `INST_JAL     : begin o_rd_wdata = i_op1 + i_op2; end
      `INST_JALR    : begin o_rd_wdata = i_op3; end
      `INST_CSRRW   : begin o_rd_wdata = i_csr_rdata; end
      `INST_CSRRS   : begin o_rd_wdata = i_csr_rdata; end
      `INST_CSRRC   : begin o_rd_wdata = i_csr_rdata; end
      `INST_CSRRWI  : begin o_rd_wdata = i_csr_rdata; end
      `INST_CSRRSI  : begin o_rd_wdata = i_csr_rdata; end
      `INST_CSRRCI  : begin o_rd_wdata = i_csr_rdata; end
      default       : begin o_rd_wdata = `ZERO_WORD; end
    endcase
  end
end

// o_pc_jmp
always @(*) begin
  if ( i_disable ) begin
    o_pc_jmp = 0;
  end
  else begin
    case (i_inst_opcode)
      `INST_BEQ   : begin o_pc_jmp = (i_op1 == i_op2) ? 1 : 0; end
      `INST_BNE   : begin o_pc_jmp = (i_op1 != i_op2) ? 1 : 0; end
      `INST_BLT   : begin o_pc_jmp = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
      `INST_BGE   : begin o_pc_jmp = ($signed(i_op1) >= $signed(i_op2)) ? 1 : 0; end
      `INST_BLTU  : begin o_pc_jmp = (i_op1 < i_op2) ? 1 : 0; end
      `INST_BGEU  : begin o_pc_jmp = (i_op1 >= i_op2) ? 1 : 0; end
      `INST_JAL   : begin o_pc_jmp = 1; end
      `INST_JALR  : begin o_pc_jmp = 1; end
      default     : begin o_pc_jmp = 0; end
    endcase
  end
end

// o_pc_jmpaddr
always @(*) begin
  if ( i_disable ) begin
    o_pc_jmpaddr = 0;
  end
  else begin
    case (i_inst_opcode)
      `INST_JAL   : begin o_pc_jmpaddr = i_op3; end
      `INST_JALR  : begin o_pc_jmpaddr = (i_op1 + i_op2) & ~1; end
      `INST_BEQ   : begin o_pc_jmpaddr = i_op3; end
      `INST_BNE   : begin o_pc_jmpaddr = i_op3; end
      `INST_BLT   : begin o_pc_jmpaddr = i_op3; end
      `INST_BGE   : begin o_pc_jmpaddr = i_op3; end
      `INST_BLTU  : begin o_pc_jmpaddr = i_op3; end
      `INST_BGEU  : begin o_pc_jmpaddr = i_op3; end
      default     : begin o_pc_jmpaddr = 0; end
    endcase
  end
end

// ------------- csr -----------------

assign inst_csr = 
  (i_inst_opcode == `INST_CSRRW ) | (i_inst_opcode == `INST_CSRRS ) | 
  (i_inst_opcode == `INST_CSRRC ) | (i_inst_opcode == `INST_CSRRWI) | 
  (i_inst_opcode == `INST_CSRRSI) | (i_inst_opcode == `INST_CSRRCI) ;

assign o_csr_ren  = (i_disable) ? 0 : inst_csr;
assign o_csr_wen  = (i_disable) ? 0 : inst_csr;
assign o_csr_addr = (i_disable) ? 0 : (inst_csr ? i_op2[11:0] : 0);

always @(*) begin
  if (i_disable) begin
    o_csr_wdata = 0;
  end
  else begin
    case (i_inst_opcode)
      `INST_CSRRW   : o_csr_wdata = i_op1;
      `INST_CSRRS   : o_csr_wdata = i_csr_rdata | i_op1;
      `INST_CSRRC   : o_csr_wdata = i_csr_rdata & (~i_op1);
      `INST_CSRRWI  : o_csr_wdata = i_op1;
      `INST_CSRRSI  : o_csr_wdata = i_csr_rdata | i_op1;
      `INST_CSRRCI  : o_csr_wdata = i_csr_rdata & (~i_op1);
      default       : o_csr_wdata = 0;
    endcase
  end
end

assign o_exeU_skip_cmt = (inst_csr && (o_csr_addr == 12'hB00));

wire _unused_ok = &{1'b0,
  reg64_t1[63:32],
  reg64_t2[63:32],
  reg64_t3[63:32],
  reg64_t4[63:32],
  1'b0};

endmodule
