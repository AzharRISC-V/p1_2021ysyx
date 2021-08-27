
//--xuezhen--

`include "defines.v"

module exe_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,
  // input   wire  [`BUS_STAGE]    stage_i,
  // output  reg   [`BUS_STAGE]    stage_o,
  // input   wire  [`BUS_STATE]    state,

  input   wire  [4 : 0]         inst_opcode,
  input   wire  [2 : 0]         inst_funct3,
  input   wire  [6 : 0]         inst_funct7,
  input   wire  [`REG_BUS]      op1,
  input   wire  [`REG_BUS]      op2,
  input   wire  [`REG_BUS]      t1,

  output  reg                   pc_jmp,
  output  reg   [`BUS_64]       pc_jmpaddr,
  output  wire                  rd_wen,
  output  reg   [`BUS_64]       rd_data
);

// rd写使能
reg rd_wen0;
always@(*) begin
  if (rst) rd_wen0 = 0;
  else
    case (inst_opcode)
      `OPCODE_AUIPC     : begin rd_wen0 = 1; end
      `OPCODE_ADDI      : begin rd_wen0 = 1; end
      `OPCODE_JAL       : begin rd_wen0 = 1; end
      `OPCODE_JALR      : begin rd_wen0 = 1; end
      `OPCODE_LB        : begin rd_wen0 = 1; end
      default           : begin rd_wen0 = 0; end
    endcase
end
//assign rd_wen = (rst | (state != `STATE_IDLE)) ? 0 : rd_wen;
assign rd_wen = ((instcycle_cnt_val == 4) | (instcycle_cnt_val == 6)) ? rd_wen0 : 0;

// rd_wdata_o
always@( * ) begin
  if(rst)  rd_data = `ZERO_WORD; 
  else begin
    case( inst_opcode )
      `OPCODE_AUIPC       : begin rd_data = op1 + op2; end
      `OPCODE_ADDI        : begin
        case( inst_funct3 )
          `FUNCT3_ADDI    : begin rd_data = op1 + op2; end
          `FUNCT3_SLTI    : begin rd_data = ($signed(op1) < $signed(op2)) ? 1 : 0; end
          `FUNCT3_SLTIU   : begin rd_data = op1 < op2 ? 1 : 0; end
          default         :;
        endcase
      end
      `OPCODE_JAL         : begin rd_data = op1; end
      `OPCODE_JALR        : begin rd_data = t1; end
      default             : begin rd_data = `ZERO_WORD; end
    endcase
  end
end

// pc_jmp, pc_jmpaddr
always @(posedge clk) begin
  if (rst) begin
    pc_jmp <= 0;
    pc_jmpaddr <= `ZERO_WORD;
  end
  else begin
    case (inst_opcode)
      `OPCODE_JAL         : begin pc_jmp <= 1; pc_jmpaddr <= op2; end
      `OPCODE_JALR        : begin pc_jmp <= 1; pc_jmpaddr <= (op1 + op2) & ~1; end
      `OPCODE_BEQ         : begin 
        case (inst_funct3)
          `FUNCT3_BEQ     : begin pc_jmp <= (op1 == op2) ? 1 : 0; end
          `FUNCT3_BNE     : begin pc_jmp <= (op1 != op2) ? 1 : 0; end
          `FUNCT3_BLT     : begin pc_jmp <= ($signed(op1) < $signed(op2)) ? 1 : 0; end
          `FUNCT3_BGE     : begin pc_jmp <= ($signed(op1) > $signed(op2)) ? 1 : 0; end
          `FUNCT3_BLTU    : begin pc_jmp <= (op1 < op2) ? 1 : 0; end
          `FUNCT3_BGEU    : begin pc_jmp <= ($signed(op1) >= $signed(op2)) ? 1 : 0; end
          default         : begin pc_jmp <= 0; end
        endcase
        pc_jmpaddr <= t1; 
      end
      default             : begin pc_jmp <= 0; end
    endcase
  end
end


endmodule
