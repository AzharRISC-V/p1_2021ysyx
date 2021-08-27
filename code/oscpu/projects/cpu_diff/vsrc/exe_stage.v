
//--xuezhen--

`include "defines.v"

module exe_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,

  input   wire  [4 : 0]         opcode_i,
  input   wire  [2 : 0]         funct3_i,
  input   wire  [6 : 0]         funct7_i,
  input   wire  [`REG_BUS]      op1_i,
  input   wire  [`REG_BUS]      op2_i,
  input   wire  [`REG_BUS]      t1_i,

  output  reg                   pc_jmp,
  output  reg   [`BUS_64]       pc_jmpaddr,
  output  wire                  rd_wen,
  output  reg   [`BUS_64]       rd_data
);

// 保存解码信息
reg   [4 : 0]     opcode;
reg   [2 : 0]     funct3;
reg   [6 : 0]     funct7;
reg   [`REG_BUS]  op1;
reg   [`REG_BUS]  op2;
reg   [`REG_BUS]  t1;
always @(posedge clk) begin
  if (rst) begin
    opcode = 0;
    funct3 = 0;
    funct7 = 0;
    op1 = 0;
    op2 = 0;
    t1 = 0;
  end
  else begin
    if (instcycle_cnt_val == 3) begin
      opcode = opcode_i; 
      funct3 = funct3_i;
      funct7 = funct7_i;
      op1 = op1_i;
      op2 = op2_i;
      t1 = t1_i;
    end
  end
end

reg rd_wen0;
always@(*) begin
  if (rst) rd_wen0 = 0;
  else
    case (opcode)
      `OPCODE_AUIPC     : begin rd_wen0 = 1; end
      `OPCODE_ADDI      : begin rd_wen0 = 1; end
      `OPCODE_JAL       : begin rd_wen0 = 1; end
      `OPCODE_JALR      : begin rd_wen0 = 1; end
      `OPCODE_LB        : begin rd_wen0 = 1; end
      default           : begin rd_wen0 = 0; end
    endcase
end

assign rd_wen = ((instcycle_cnt_val == 6) || (instcycle_cnt_val == 7)) ? rd_wen0 : 0;

// rd_wdata_o
always@( posedge clk ) begin
  if(rst)  rd_data = `ZERO_WORD; 
  else begin
    if (instcycle_cnt_val == 4) begin
      case( opcode )
        `OPCODE_AUIPC       : begin rd_data = op1 + op2; end
        `OPCODE_ADDI        : begin
          case( funct3 )
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
end

// pc_jmp, pc_jmpaddr
always @(posedge clk) begin
  if (rst) begin
    pc_jmp <= 0;
    pc_jmpaddr <= `ZERO_WORD;
  end
  else begin
    case (opcode)
      `OPCODE_JAL         : begin pc_jmp <= 1; pc_jmpaddr <= op2; end
      `OPCODE_JALR        : begin pc_jmp <= 1; pc_jmpaddr <= (op1 + op2) & ~1; end
      `OPCODE_BEQ         : begin 
        case (funct3)
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
