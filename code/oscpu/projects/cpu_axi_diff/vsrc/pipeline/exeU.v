
// ZhengpuShi

// Execute Unit, 组合逻辑电路

`include "../defines.v"

module exeU(
  input   wire                rst,
  input   wire                i_ena,
  input   wire  [4 : 0]       i_inst_type,
  input   wire  [7 : 0]       i_inst_opcode,
  input   wire  [`BUS_OPCODE] i_opcode,
  input   wire  [`BUS_FUNCT3] i_funct3,
  input   wire  [`BUS_FUNCT7] i_funct7,
  input   wire  [`BUS_64]     i_op1,
  input   wire  [`BUS_64]     i_op2,
  input   wire  [`BUS_64]     i_op3,
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


wire i_disable = !i_ena;

reg [`BUS_64] reg64_1;
reg [`BUS_32] reg32_1;

wire [63:0] reg64_t1 = i_op1 + i_op2;
wire [63:0] reg64_t2 = i_op1 << i_op2[5:0];
wire [63:0] reg64_t3 = i_op1 - $signed(i_op2);
wire [63:0] reg64_t4 = i_op1 << i_op2[4:0];
wire [31:0] reg32_t1 = i_op1[31:0] >> i_op2[4:0];
always@( * )
begin
  if( i_disable )
  begin
    o_rd_data = `ZERO_WORD;
  end
  else
  begin
    case( i_inst_opcode )
	  `INST_ADDI    : begin o_rd_data = i_op1 + i_op2;  end
	  `INST_ADD     : begin o_rd_data = i_op1 + i_op2;  end
	  `INST_SUB     : begin o_rd_data = i_op1 - i_op2;  end
	  `INST_SUBW    : begin o_rd_data = {{33{reg64_t3[31]}}, reg64_t3[30:0]}; end
	  `INST_ADDIW   : begin o_rd_data = {{33{reg64_t1[31]}}, reg64_t1[30:0]}; end
	  `INST_AND     : begin o_rd_data = i_op1 & i_op2;  end
	  `INST_ANDI    : begin o_rd_data = i_op1 & i_op2;  end
	  `INST_OR      : begin o_rd_data = i_op1 | i_op2;  end
	  `INST_ORI     : begin o_rd_data = i_op1 | i_op2;  end
	  `INST_XOR     : begin o_rd_data = i_op1 ^ i_op2;  end
	  `INST_XORI    : begin o_rd_data = i_op1 ^ i_op2;  end
    `INST_SLL     : begin o_rd_data = i_op1 << i_op2[5:0]; end
    `INST_SLLI    : begin o_rd_data = i_op1 << i_op2[5:0]; end
    `INST_SLLIW   : begin o_rd_data = {{33{reg64_t2[31]}}, reg64_t2[30:0]}; end
    `INST_SLLW    : begin o_rd_data = {{33{reg64_t4[31]}}, reg64_t4[30:0]}; end
    `INST_SLT     : begin o_rd_data = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
    `INST_SLTI    : begin o_rd_data = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
    `INST_SLTIU   : begin o_rd_data = i_op1 < i_op2 ? 1 : 0; end
    `INST_SLTU    : begin o_rd_data = (i_op1 < i_op2) ? 1 : 0; end
    `INST_SRA     : begin o_rd_data = $signed(i_op1) >>> i_op2[5:0]; end
    `INST_SRAW    : begin o_rd_data = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
    `INST_SRAI    : begin o_rd_data = $signed(i_op1) >>> i_op2[5:0]; end
    `INST_SRAIW   : begin o_rd_data = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
    `INST_SRL     : begin o_rd_data = i_op1 >> i_op2[5:0]; end
    `INST_SRLI    : begin o_rd_data = i_op1 >> i_op2[5:0]; end
    `INST_SRLW    : begin o_rd_data = {{32{reg32_t1[31]}}, reg32_t1}; end
    `INST_SRLIW   : begin o_rd_data = {{32{reg32_t1[31]}}, reg32_t1}; end
    `INST_LUI     : begin o_rd_data = i_op1; end
    `INST_AUIPC   : begin o_rd_data = i_op1 + i_op2; end
    `INST_JAL     : begin o_rd_data = i_op1 + i_op2; end
    `INST_JALR    : begin o_rd_data = i_op3; end
	  default       : begin o_rd_data = `ZERO_WORD; end
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


// // o_rd_wen
// always @(*) begin
//   if (i_disable) begin
//     o_rd_wen = 0;
//   end
//   else begin
//     case (i_opcode)
//       `OPCODE_LUI       : begin o_rd_wen = 1; end
//       `OPCODE_AUIPC     : begin o_rd_wen = 1; end
//       `OPCODE_ADDI      : begin o_rd_wen = 1; end
//       `OPCODE_JAL       : begin o_rd_wen = 1; end
//       `OPCODE_JALR      : begin o_rd_wen = 1; end
//       `OPCODE_LB        : begin o_rd_wen = 1; end
//       `OPCODE_ADD       : begin o_rd_wen = 1; end
//       `OPCODE_ADDIW     : begin o_rd_wen = 1; end
//       `OPCODE_ADDW      : begin o_rd_wen = 1; end
//       `OPCODE_CSR       : begin o_rd_wen = 1; end
//       default           : begin o_rd_wen = 0; end
//     endcase
//   end
// end

// // rd_wdata_o
// reg [`BUS_64] reg64_1;
// reg [`BUS_32] reg32_1;
// always @(*) begin
//   if (i_disable) begin
//     o_rd_data = 0;
//   end
//   else begin
//     case( i_opcode )
//       `OPCODE_LUI         : begin o_rd_data = i_op1; end
//       `OPCODE_AUIPC       : begin o_rd_data = i_op1 + i_op2; end
//       `OPCODE_ADDI        : begin
//         case( i_funct3 )
//           `FUNCT3_ADDI    : begin o_rd_data = i_op1 + i_op2; end
//           `FUNCT3_SLTI    : begin o_rd_data = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
//           `FUNCT3_SLTIU   : begin o_rd_data = i_op1 < i_op2 ? 1 : 0; end
//           `FUNCT3_XORI    : begin o_rd_data = i_op1 ^ i_op2; end
//           `FUNCT3_ORI     : begin o_rd_data = i_op1 | i_op2; end
//           `FUNCT3_ANDI    : begin o_rd_data = i_op1 & i_op2; end
//           `FUNCT3_SLLI    : begin o_rd_data = i_op1 << i_op2; end
//           end
//           default         :;
//         endcase
//       end
//       `OPCODE_JAL         : begin o_rd_data = i_op1; end
//       `OPCODE_JALR        : begin o_rd_data = i_t1; end
//       `OPCODE_ADD         : begin
//         case (i_funct3)
//           `FUNCT3_ADD     : begin o_rd_data = (i_funct7[5]) ? i_op1 - i_op2 : i_op1 + i_op2; end    // SUB or ADD
//           `FUNCT3_SLL     : begin o_rd_data = i_op1 << i_op2[5:0]; end
//           `FUNCT3_SLT     : begin o_rd_data = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
//           `FUNCT3_SLTU    : begin o_rd_data = (i_op1 < i_op2) ? 1 : 0; end
//           `FUNCT3_XOR     : begin o_rd_data = i_op1 ^ i_op2; end
//           end
//           `FUNCT3_OR      : begin o_rd_data = i_op1 | i_op2; end
//           `FUNCT3_AND     : begin o_rd_data = i_op1 & i_op2; end
//           default         : begin o_rd_data = 0; end
//         endcase
//       end
//       `OPCODE_ADDIW       : begin
//         case (i_funct3)
//           `FUNCT3_ADDIW   : begin reg64_1 = i_op1 + $signed(i_op2); o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
//           `FUNCT3_SLLIW   : begin reg64_1 = i_op1 << i_op2; o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
//           `FUNCT3_SRLIW   : begin
//             if (i_funct7[5])  begin o_rd_data = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end               // SRAIW
//             else              // SRLIW
//           end
//           default         : begin o_rd_data = 0; end
//         endcase
//       end
//       `OPCODE_ADDW        : begin
//         case (i_funct3)
//           `FUNCT3_ADDW    : begin
//             if (i_funct7[5])   // SUBW
//             else            begin reg64_1 = i_op1 + $signed(i_op2); o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end // ADDW
//           end
//           `FUNCT3_SLLW    : begin reg64_1 = i_op1 << i_op2[4:0]; o_rd_data = {{33{reg64_1[31]}}, reg64_1[30:0]}; end
//           `FUNCT3_SRAW    : begin
//             if (i_funct7[5])  begin o_rd_data = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end                 // SRAW
//             else                // SRLW
//           end
//           default         : begin o_rd_data = 0; end
//         endcase
//       end
//       default             : begin o_rd_data = `ZERO_WORD; end
//     endcase
//   end
// end

// // o_pc_jmp, o_pc_jmpaddr
// always @(*) begin
//   if (i_disable) begin
//     o_pc_jmp = 0;
//     o_pc_jmpaddr = 0;
//   end
//   else begin
//     case (i_opcode)
//       `OPCODE_JAL         : begin o_pc_jmp = 1; o_pc_jmpaddr = i_op2; end
//       `OPCODE_JALR        : begin o_pc_jmp = 1; o_pc_jmpaddr = (i_op1 + i_op2) & ~1; end
//       `OPCODE_BEQ         : begin 
//         case (i_funct3)
//           `FUNCT3_BEQ     : begin o_pc_jmp = (i_op1 == i_op2) ? 1 : 0; end
//           `FUNCT3_BNE     : begin o_pc_jmp = (i_op1 != i_op2) ? 1 : 0; end
//           `FUNCT3_BLT     : begin o_pc_jmp = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
//           `FUNCT3_BGE     : begin o_pc_jmp = ($signed(i_op1) >= $signed(i_op2)) ? 1 : 0; end
//           `FUNCT3_BLTU    : begin o_pc_jmp = (i_op1 < i_op2) ? 1 : 0; end
//           `FUNCT3_BGEU    : begin o_pc_jmp = (i_op1 >= i_op2) ? 1 : 0; end
//           default         : begin o_pc_jmp = 0; end
//         endcase
//         o_pc_jmpaddr = i_t1; 
//       end
//       default             : begin o_pc_jmp = 0; o_pc_jmpaddr = 0; end
//     endcase
//   end
// end


// // o_memren
// assign o_memren = i_disable ? 0 : i_memren;
// // o_memwen
// assign o_memwen = i_disable ? 0 : i_memwen;

endmodule
