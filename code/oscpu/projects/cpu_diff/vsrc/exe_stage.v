
//--xuezhen--

`include "defines.v"

module exe_stage(
  input wire rst,
  input wire [4 : 0]inst_opcode_i,
  input wire [2 : 0]inst_funct3,
  input wire [6 : 0]inst_funct7,
  input wire [`REG_BUS]op1,
  input wire [`REG_BUS]op2,
  input wire [`REG_BUS]t1,
  
  output wire [4 : 0]inst_opcode_o,
  output reg  [`REG_BUS]rd_data,
  output wire pc_jmp,
  output wire [`BUS_64] pc_jmpaddr
);

assign inst_opcode_o = inst_opcode_i;

// rd_data
always@( * ) begin
  if( rst == 1'b1 )  rd_data = `ZERO_WORD; 
  else begin
    case( inst_opcode_i )
      `OPCODE_AUIPC       : begin rd_data = op1 + op2;  end
      `OPCODE_ADDI        : begin
        case( inst_funct3 )
          `FUNCT3_ADDI    : begin rd_data = op1 + op2;  end
          `FUNCT3_SLTI    : begin rd_data = ($signed(op1) < $signed(op2)) ? 1 : 0;  end
          `FUNCT3_SLTIU   : begin rd_data = op1 < op2 ? 1 : 0;  end
          default         :;
        endcase
      end
      `OPCODE_JAL         : begin rd_data = op1;        end
      `OPCODE_JALR        : begin rd_data = t1;         end
      default:            begin rd_data = `ZERO_WORD; end
    endcase
  end
end

// pc_jmp
always @(*) begin
  if (rst == 1'b1) pc_jmp = 0;
  else begin
    case (inst_opcode_i)
      `OPCODE_JAL         : pc_jmp = 1;
      `OPCODE_JALR        : pc_jmp = 1;
      `OPCODE_BEQ         : begin
        case (inst_funct3)
          `FUNCT3_BEQ     : pc_jmp = (op1 == op2) ? 1 : 0;
          `FUNCT3_BNE     : pc_jmp = (op1 != op2) ? 1 : 0;
          `FUNCT3_BLT     : pc_jmp = ($signed(op1) < $signed(op2)) ? 1 : 0;
          `FUNCT3_BGE     : pc_jmp = ($signed(op1) > $signed(op2)) ? 1 : 0;
          `FUNCT3_BLTU    : pc_jmp = (op1 < op2) ? 1 : 0;
          `FUNCT3_BGEU    : pc_jmp = ($signed(op1) >= $signed(op2)) ? 1 : 0;
          default         : pc_jmp = 0;
        endcase
      end
      default             : pc_jmp = 0;
    endcase
  end
end

// pc_jmpaddr
always @(*) begin
  if (rst == 1'b1) pc_jmpaddr = `ZERO_WORD;
  else begin
    case (inst_opcode_i)
      `OPCODE_JAL         : pc_jmpaddr = op2;
      `OPCODE_JALR        : pc_jmpaddr = (op1 + op2) & ~1;
      `OPCODE_BEQ         : pc_jmpaddr = t1;
      default             : pc_jmpaddr = 0;
    endcase
  end
end



endmodule
