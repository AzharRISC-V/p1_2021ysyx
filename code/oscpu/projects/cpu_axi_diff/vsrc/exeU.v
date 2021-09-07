
// ZhengpuShi

// Execute Unit, 组合逻辑电路

`include "defines.v"

module exeU(
  input   wire  [6 : 0]       i_opcode,
  input   wire  [2 : 0]       i_funct3,
  input   wire  [6 : 0]       i_funct7,
  input   wire  [`BUS_64]     i_op1,
  input   wire  [`BUS_64]     i_op2,
  input   wire  [`BUS_64]     i_t1,
  input   wire  [`BUS_64]     i_pc_pred,
  input                       i_memren,
  input                       i_memwen,
  output  reg                 o_pc_jmp,
  output  reg   [`BUS_64]     o_pc_jmpaddr,
  output  wire                o_rd_wen,
  output  wire  [`BUS_64]     o_rd_data,
  output                      o_memren,
  output                      o_memwen

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

// o_rd_wen
always @(*) begin
  case (i_opcode)
    `OPCODE_LUI       : begin o_rd_wen = 1; end
    `OPCODE_AUIPC     : begin o_rd_wen = 1; end
    `OPCODE_ADDI      : begin o_rd_wen = 1; end
    `OPCODE_JAL       : begin o_rd_wen = 1; end
    `OPCODE_JALR      : begin o_rd_wen = 1; end
    `OPCODE_LB        : begin o_rd_wen = 1; end
    `OPCODE_ADD       : begin o_rd_wen = 1; end
    `OPCODE_ADDIW     : begin o_rd_wen = 1; end
    `OPCODE_ADDW      : begin o_rd_wen = 1; end
    `OPCODE_CSR       : begin o_rd_wen = 1; end
    default           : begin o_rd_wen = 0; end
  endcase
end

// rd_wdata_o
reg [`BUS_64] reg64_1;
reg [`BUS_32] reg32_1;
always @(*) begin
  case( i_opcode )
    `OPCODE_LUI         : begin o_rd_data = i_op1; end
    `OPCODE_AUIPC       : begin o_rd_data = i_op1 + i_op2; end
    `OPCODE_ADDI        : begin
      case( i_funct3 )
        `FUNCT3_ADDI    : begin o_rd_data = i_op1 + i_op2; end
        `FUNCT3_SLTI    : begin o_rd_data = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
        `FUNCT3_SLTIU   : begin o_rd_data = i_op1 < i_op2 ? 1 : 0; end
        `FUNCT3_XORI    : begin o_rd_data = i_op1 ^ i_op2; end
        `FUNCT3_ORI     : begin o_rd_data = i_op1 | i_op2; end
        `FUNCT3_ANDI    : begin o_rd_data = i_op1 & i_op2; end
        `FUNCT3_SLLI    : begin o_rd_data = i_op1 << i_op2; end
        `FUNCT3_SRLI    : begin
          // if (i_funct7[5])  begin reg64_1 = i_op1 >>> i_op2; o_rd_data = { {33{i_t1[31]}}, reg64_1[30:0]}; end   // SRAI
          if (i_funct7[5])  begin o_rd_data = $signed(i_op1) >>> i_op2; end   // SRAI
          else            begin o_rd_data = i_op1 >> i_op2; end   // SRLI
        end
        default         :;
      endcase
    end
    `OPCODE_JAL         : begin o_rd_data = i_op1; end
    `OPCODE_JALR        : begin o_rd_data = i_t1; end
    `OPCODE_ADD         : begin
      case (i_funct3)
        `FUNCT3_ADD     : begin o_rd_data = (i_funct7[5]) ? i_op1 - i_op2 : i_op1 + i_op2; end    // SUB or ADD
        `FUNCT3_SLL     : begin o_rd_data = i_op1 << i_op2[5:0]; end
        `FUNCT3_SLT     : begin o_rd_data = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
        `FUNCT3_SLTU    : begin o_rd_data = (i_op1 < i_op2) ? 1 : 0; end
        `FUNCT3_XOR     : begin o_rd_data = i_op1 ^ i_op2; end
        `FUNCT3_SRL     : begin
          if (i_funct7[5])  begin o_rd_data = $signed(i_op1) >>> i_op2[5:0]; end   // SRA
          else            begin o_rd_data = i_op1 >> i_op2[5:0]; end             // SRL
        end
        `FUNCT3_OR      : begin o_rd_data = i_op1 | i_op2; end
        `FUNCT3_AND     : begin o_rd_data = i_op1 & i_op2; end
        default         : begin o_rd_data = 0; end
      endcase
    end
    `OPCODE_ADDIW       : begin
      case (i_funct3)
        `FUNCT3_ADDIW   : begin reg64_1 = i_op1 + $signed(i_op2); o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
        `FUNCT3_SLLIW   : begin reg64_1 = i_op1 << i_op2; o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
        `FUNCT3_SRLIW   : begin
          if (i_funct7[5])  begin o_rd_data = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end               // SRAIW
          else            begin reg32_1 = i_op1[31:0] >> i_op2[4:0]; o_rd_data = {{32{reg32_1[31]}}, reg32_1}; end  // SRLIW
        end
        default         : begin o_rd_data = 0; end
      endcase
    end
    `OPCODE_ADDW        : begin
      case (i_funct3)
        `FUNCT3_ADDW    : begin
          if (i_funct7[5])  begin reg64_1 = i_op1 - $signed(i_op2); o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end // SUBW
          else            begin reg64_1 = i_op1 + $signed(i_op2); o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end // ADDW
        end
        `FUNCT3_SLLW    : begin reg64_1 = i_op1 << i_op2[4:0]; o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
        `FUNCT3_SRAW    : begin
          if (i_funct7[5])  begin o_rd_data = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end                 // SRAW
          else            begin reg32_1 = i_op1[31:0] >> i_op2[4:0]; o_rd_data = {{32{reg32_1[31]}}, reg32_1}; end    // SRLW
        end
        default         : begin o_rd_data = 0; end
      endcase
    end
    default             : begin o_rd_data = `ZERO_WORD; end
  endcase
end

// o_pc_jmp, o_pc_jmpaddr
always @(*) begin
  case (i_opcode)
    `OPCODE_JAL         : begin o_pc_jmp = 1; o_pc_jmpaddr = i_op2; end
    `OPCODE_JALR        : begin o_pc_jmp = 1; o_pc_jmpaddr = (i_op1 + i_op2) & ~1; end
    `OPCODE_BEQ         : begin 
      case (i_funct3)
        `FUNCT3_BEQ     : begin o_pc_jmp = (i_op1 == i_op2) ? 1 : 0; end
        `FUNCT3_BNE     : begin o_pc_jmp = (i_op1 != i_op2) ? 1 : 0; end
        `FUNCT3_BLT     : begin o_pc_jmp = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
        `FUNCT3_BGE     : begin o_pc_jmp = ($signed(i_op1) >= $signed(i_op2)) ? 1 : 0; end
        `FUNCT3_BLTU    : begin o_pc_jmp = (i_op1 < i_op2) ? 1 : 0; end
        `FUNCT3_BGEU    : begin o_pc_jmp = (i_op1 >= i_op2) ? 1 : 0; end
        default         : begin o_pc_jmp = 0; end
      endcase
      o_pc_jmpaddr = i_t1; 
    end
    default             : begin o_pc_jmp = 0; o_pc_jmpaddr = 0; end
  endcase
end

// 跳转指令，并且跳转目标与预测目标不同时，冲刷流水线
// assign o_jump_flush_req = o_pc_jmp ? (o_pc_jmpaddr != pc_pred_i) : 0;
// assign o_jump_flush_pc = o_jump_flush_req ? o_pc_jmpaddr : pc_pred_i; 

// o_memren
assign o_memren = i_memren;
// o_memwen
assign o_memwen = i_memwen;

endmodule
