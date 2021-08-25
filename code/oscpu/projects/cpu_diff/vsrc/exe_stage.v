
//--xuezhen--

`include "defines.v"

module exe_stage(
  input   wire              rst,
  input   wire  [4 : 0]     inst_opcode_i,
  input   wire  [2 : 0]     inst_funct3,
  input   wire  [6 : 0]     inst_funct7,
  input   wire  [`REG_BUS]  op1,
  input   wire  [`REG_BUS]  op2,
  input   wire  [`REG_BUS]  t1,
  input   wire  [4 : 0]     rd_waddr_i,
  output  wire  [4 : 0]     inst_opcode_o,
  output  wire              pc_jmp,
  output  wire  [`BUS_64]   pc_jmpaddr,
  output  wire              rd_wen_o,
  output  wire  [4 : 0]     rd_waddr_o,
  output  wire  [`BUS_64]   rd_wdata_o
);

assign rd_waddr_o = rd_waddr_i;

assign inst_opcode_o = inst_opcode_i;

// rd写使能
reg rd_wen;
always@(*) begin
  if (rst == 1'b1) rd_wen = 0;
  else
    case (inst_opcode_i)
      `OPCODE_AUIPC     : begin rd_wen = 1;  end
      `OPCODE_ADDI      : begin rd_wen = 1;  end
      `OPCODE_JAL       : begin rd_wen = 1;  end
      `OPCODE_JALR      : begin rd_wen = 1;  end
      `OPCODE_LB        : begin rd_wen = 1;  end
      default           : begin rd_wen = 0;  end
    endcase
end
assign rd_wen_o = rd_wen;

// rd_wdata_o
reg [`REG_BUS] rd_data;
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

assign rd_wdata_o = rd_data;

// pc_jmp
reg pc_jmp_0;
always @(*) begin
  if (rst == 1'b1) pc_jmp_0 = 0;
  else begin
    case (inst_opcode_i)
      `OPCODE_JAL         : pc_jmp_0 = 1;
      `OPCODE_JALR        : pc_jmp_0 = 1;
      `OPCODE_BEQ         : begin
        case (inst_funct3)
          `FUNCT3_BEQ     : pc_jmp_0 = (op1 == op2) ? 1 : 0;
          `FUNCT3_BNE     : pc_jmp_0 = (op1 != op2) ? 1 : 0;
          `FUNCT3_BLT     : pc_jmp_0 = ($signed(op1) < $signed(op2)) ? 1 : 0;
          `FUNCT3_BGE     : pc_jmp_0 = ($signed(op1) > $signed(op2)) ? 1 : 0;
          `FUNCT3_BLTU    : pc_jmp_0 = (op1 < op2) ? 1 : 0;
          `FUNCT3_BGEU    : pc_jmp_0 = ($signed(op1) >= $signed(op2)) ? 1 : 0;
          default         : pc_jmp_0 = 0;
        endcase
      end
      default             : pc_jmp_0 = 0;
    endcase
  end
end
assign pc_jmp = pc_jmp_0;

// pc_jmpaddr
reg [`BUS_64] pc_jmpaddr_0;
always @(*) begin
  if (rst == 1'b1) pc_jmpaddr_0 = `ZERO_WORD;
  else begin
    case (inst_opcode_i)
      `OPCODE_JAL         : pc_jmpaddr_0 = op2;
      `OPCODE_JALR        : pc_jmpaddr_0 = (op1 + op2) & ~1;
      `OPCODE_BEQ         : pc_jmpaddr_0 = t1;
      default             : pc_jmpaddr_0 = 0;
    endcase
  end
end
assign pc_jmpaddr = pc_jmpaddr_0;



endmodule
