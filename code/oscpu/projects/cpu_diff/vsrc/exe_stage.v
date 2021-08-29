
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

// Indicate that if EX is working
wire ex_active = (instcycle_cnt_val == 4);
wire ex_inactive = !ex_active;

// 保存解码信息
reg   [4 : 0]     opcode;
reg   [2 : 0]     funct3;
reg   [6 : 0]     funct7;
reg   [`REG_BUS]  op1;
reg   [`REG_BUS]  op2;
reg   [`REG_BUS]  t1;
always @(*) begin
  if (ex_inactive) begin
    {opcode, funct3, funct7, op1, op2, t1} = 0;
  end
  else begin
    opcode = opcode_i; 
    funct3 = funct3_i;
    funct7 = funct7_i;
    op1 = op1_i;
    op2 = op2_i;
    t1 = t1_i;
  end
end

// rd_wen
reg rd_wen0;
always@(*) begin
  if (ex_inactive) begin
    rd_wen0 = 0;
  end
  else
    case (opcode)
      `OPCODE_LUI       : begin rd_wen0 = 1; end
      `OPCODE_AUIPC     : begin rd_wen0 = 1; end
      `OPCODE_ADDI      : begin rd_wen0 = 1; end
      `OPCODE_JAL       : begin rd_wen0 = 1; end
      `OPCODE_JALR      : begin rd_wen0 = 1; end
      `OPCODE_LB        : begin rd_wen0 = 1; end
      `OPCODE_ADD       : begin rd_wen0 = 1; end
      `OPCODE_ADDIW     : begin rd_wen0 = 1; end
      `OPCODE_ADDW      : begin rd_wen0 = 1; end
      default           : begin rd_wen0 = 0; end
    endcase
end
assign rd_wen = rd_wen0;

// rd_wdata_o
reg [`BUS_64] reg64_1;
reg [`BUS_32] reg32_1;
always_latch begin
  if(ex_inactive) begin
    rd_data = `ZERO_WORD;
  end
  else begin
    //if (instcycle_cnt_val == 4) begin
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
    //end
  end
end

// pc_jmp, pc_jmpaddr
always @(posedge clk) begin
  if (ex_inactive) begin
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
          `FUNCT3_BGE     : begin pc_jmp <= ($signed(op1) >= $signed(op2)) ? 1 : 0; end
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
