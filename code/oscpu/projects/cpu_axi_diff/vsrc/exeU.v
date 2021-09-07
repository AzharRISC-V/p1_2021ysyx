
// ZhengpuShi

// Execute Unit, 组合逻辑电路

`include "defines.v"

module exeU(
  input   wire  [6 : 0]       opcode,
  input   wire  [2 : 0]       funct3,
  input   wire  [6 : 0]       funct7,
  input   wire  [`REG_BUS]    op1,
  input   wire  [`REG_BUS]    op2,
  input   wire  [`REG_BUS]    t1,
  input   wire  [`BUS_64]     pc_pred,     // 顺序计算得出的pc值，用于对比
  input                       memren_i,
  input                       memwen_i,
  output  reg                 pc_jmp,
  output  reg   [`BUS_64]     pc_jmpaddr,
  output  wire                rd_wen,
  output  wire  [`BUS_64]     rd_data,
  output                      memren_o,
  output                      memwen_o

);


// Special Instruction: putch a0
// wire                          putch_wen;
// wire [7 : 0]                  putch_wdata;
// assign putch_wen              = if_inst_o == 32'h7b;
// assign putch_wdata            = (!putch_wen) ? 0 : (regs[10][7:0]); 
// putch Putch(
//   .clk                (clock            ),
//   .rst                (reset            ),
//   .wen                (putch_wen        ),
//   .wdata              (putch_wdata      ) 
// );
// always @(posedge clock) begin
//   if (inst == 7) begin
//     $write("%c", regs[10][7:0]);
//   end
// end
// assign io_uart_out_valid = putch_wen;
// assign io_uart_out_ch = putch_wdata;

// rd_wen
always @(*) begin
  case (opcode)
    `OPCODE_LUI       : begin rd_wen = 1; end
    `OPCODE_AUIPC     : begin rd_wen = 1; end
    `OPCODE_ADDI      : begin rd_wen = 1; end
    `OPCODE_JAL       : begin rd_wen = 1; end
    `OPCODE_JALR      : begin rd_wen = 1; end
    `OPCODE_LB        : begin rd_wen = 1; end
    `OPCODE_ADD       : begin rd_wen = 1; end
    `OPCODE_ADDIW     : begin rd_wen = 1; end
    `OPCODE_ADDW      : begin rd_wen = 1; end
    `OPCODE_CSR       : begin rd_wen = 1; end
    default           : begin rd_wen = 0; end
  endcase
end

// rd_wdata_o
reg [`BUS_64] reg64_1;
reg [`BUS_32] reg32_1;
always @(*) begin
  case( opcode )
    `OPCODE_LUI         : begin rd_data = op1; end
    `OPCODE_AUIPC       : begin rd_data = op1 + op2; end
    `OPCODE_ADDI        : begin
      case( funct3 )
        `FUNCT3_ADDI    : begin rd_data = op1 + op2; end
        `FUNCT3_SLTI    : begin rd_data = ($signed(op1) < $signed(op2)) ? 1 : 0; end
        `FUNCT3_SLTIU   : begin rd_data = op1 < op2 ? 1 : 0; end
        `FUNCT3_XORI    : begin rd_data = op1 ^ op2; end
        `FUNCT3_ORI     : begin rd_data = op1 | op2; end
        `FUNCT3_ANDI    : begin rd_data = op1 & op2; end
        `FUNCT3_SLLI    : begin rd_data = op1 << op2; end
        `FUNCT3_SRLI    : begin
          // if (funct7[5])  begin reg64_1 = op1 >>> op2; rd_data = { {33{t1[31]}}, reg64_1[30:0]}; end   // SRAI
          if (funct7[5])  begin rd_data = $signed(op1) >>> op2; end   // SRAI
          else            begin rd_data = op1 >> op2; end   // SRLI
        end
        default         :;
      endcase
    end
    `OPCODE_JAL         : begin rd_data = op1; end
    `OPCODE_JALR        : begin rd_data = t1; end
    `OPCODE_ADD         : begin
      case (funct3)
        `FUNCT3_ADD     : begin rd_data = (funct7[5]) ? op1 - op2 : op1 + op2; end    // SUB or ADD
        `FUNCT3_SLL     : begin rd_data = op1 << op2[5:0]; end
        `FUNCT3_SLT     : begin rd_data = ($signed(op1) < $signed(op2)) ? 1 : 0; end
        `FUNCT3_SLTU    : begin rd_data = (op1 < op2) ? 1 : 0; end
        `FUNCT3_XOR     : begin rd_data = op1 ^ op2; end
        `FUNCT3_SRL     : begin
          if (funct7[5])  begin rd_data = $signed(op1) >>> op2[5:0]; end   // SRA
          else            begin rd_data = op1 >> op2[5:0]; end             // SRL
        end
        `FUNCT3_OR      : begin rd_data = op1 | op2; end
        `FUNCT3_AND     : begin rd_data = op1 & op2; end
        default         : begin rd_data = 0; end
      endcase
    end
    `OPCODE_ADDIW       : begin
      case (funct3)
        `FUNCT3_ADDIW   : begin reg64_1 = op1 + $signed(op2); rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
        `FUNCT3_SLLIW   : begin reg64_1 = op1 << op2; rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
        `FUNCT3_SRLIW   : begin
          if (funct7[5])  begin rd_data = $signed({{33{op1[31]}}, op1[30:0]}) >>> op2[4:0]; end               // SRAIW
          else            begin reg32_1 = op1[31:0] >> op2[4:0]; rd_data = {{32{reg32_1[31]}}, reg32_1}; end  // SRLIW
        end
        default         : begin rd_data = 0; end
      endcase
    end
    `OPCODE_ADDW        : begin
      case (funct3)
        `FUNCT3_ADDW    : begin
          if (funct7[5])  begin reg64_1 = op1 - $signed(op2); rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end // SUBW
          else            begin reg64_1 = op1 + $signed(op2); rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end // ADDW
        end
        `FUNCT3_SLLW    : begin reg64_1 = op1 << op2[4:0]; rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
        `FUNCT3_SRAW    : begin
          if (funct7[5])  begin rd_data = $signed({{33{op1[31]}}, op1[30:0]}) >>> op2[4:0]; end                 // SRAW
          else            begin reg32_1 = op1[31:0] >> op2[4:0]; rd_data = {{32{reg32_1[31]}}, reg32_1}; end    // SRLW
        end
        default         : begin rd_data = 0; end
      endcase
    end
    default             : begin rd_data = `ZERO_WORD; end
  endcase
end

// pc_jmp, pc_jmpaddr
always @(*) begin
  case (opcode)
    `OPCODE_JAL         : begin pc_jmp = 1; pc_jmpaddr = op2; end
    `OPCODE_JALR        : begin pc_jmp = 1; pc_jmpaddr = (op1 + op2) & ~1; end
    `OPCODE_BEQ         : begin 
      case (funct3)
        `FUNCT3_BEQ     : begin pc_jmp = (op1 == op2) ? 1 : 0; end
        `FUNCT3_BNE     : begin pc_jmp = (op1 != op2) ? 1 : 0; end
        `FUNCT3_BLT     : begin pc_jmp = ($signed(op1) < $signed(op2)) ? 1 : 0; end
        `FUNCT3_BGE     : begin pc_jmp = ($signed(op1) >= $signed(op2)) ? 1 : 0; end
        `FUNCT3_BLTU    : begin pc_jmp = (op1 < op2) ? 1 : 0; end
        `FUNCT3_BGEU    : begin pc_jmp = (op1 >= op2) ? 1 : 0; end
        default         : begin pc_jmp = 0; end
      endcase
      pc_jmpaddr = t1; 
    end
    default             : begin pc_jmp = 0; pc_jmpaddr = 0; end
  endcase
end

// 跳转指令，并且跳转目标与预测目标不同时，冲刷流水线
// assign o_jump_flush_req = pc_jmp ? (pc_jmpaddr != pc_pred_i) : 0;
// assign o_jump_flush_pc = o_jump_flush_req ? pc_jmpaddr : pc_pred_i; 

// memren_o
assign memren_o = memren_i;
// memwen_o
assign memwen_o = memwen_i;

endmodule
