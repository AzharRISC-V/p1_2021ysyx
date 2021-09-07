
// ZhengpuShi

// Execute Interface

`include "defines.v"

module exe_stage(
  input   wire                rst,
  input   wire                clk,
  input   reg                 i_ex_decoded_req,
  output  reg                 o_ex_decoded_ack,
  output  reg                 o_ex_executed_req,
  input   reg                 i_ex_executed_ack,
  input   wire  [6 : 0]       i_ex_opcode,
  input   wire  [2 : 0]       i_ex_funct3,
  input   wire  [6 : 0]       i_ex_funct7,
  input   wire  [`REG_BUS]    i_ex_op1,
  input   wire  [`REG_BUS]    i_ex_op2,
  input   wire  [`REG_BUS]    i_ex_t1,
  input   wire                i_ex_memren,
  input   wire                i_ex_memwen,
  input   wire  [`BUS_64]     i_ex_pc_pred,
  output  reg                 o_ex_pc_jmp,
  output  reg   [`BUS_64]     o_ex_pc_jmpaddr,
  output  wire                o_ex_rd_wen,
  output  wire  [`BUS_64]     o_ex_rd_wdata,
  output  wire                o_ex_memren,
  output  wire                o_ex_memwen
);

assign o_ex_decoded_ack = 1'b1;

wire decoded_hs = i_ex_executed_ack & o_ex_decoded_ack;

// 保存输入信息
reg   [6 : 0]                 tmp_i_ex_opcode;
reg   [2 : 0]                 tmp_i_ex_funct3;
reg   [6 : 0]                 tmp_i_ex_funct7;
reg   [`REG_BUS]              tmp_i_ex_op1;
reg   [`REG_BUS]              tmp_i_ex_op2;
reg   [`REG_BUS]              tmp_i_ex_t1;
reg                           tmp_i_ex_memren;
reg                           tmp_i_ex_memwen;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_ex_opcode, 
      tmp_i_ex_funct3, 
      tmp_i_ex_funct7, 
      tmp_i_ex_op1, 
      tmp_i_ex_op2, 
      tmp_i_ex_t1,
      tmp_i_ex_memren,
      tmp_i_ex_memwen
    } <= 0;

    o_ex_decoded_ack <= 0;
  end
  else begin
    if (decoded_hs) begin
      tmp_i_ex_opcode   <= i_ex_opcode; 
      tmp_i_ex_funct3   <= i_ex_funct3;
      tmp_i_ex_funct7   <= i_ex_funct7;
      tmp_i_ex_op1      <= i_ex_op1;
      tmp_i_ex_op2      <= i_ex_op2;
      tmp_i_ex_t1       <= i_ex_t1;
      tmp_i_ex_memren   <= i_ex_memren;
      tmp_i_ex_memwen   <= i_ex_memwen;

      o_ex_decoded_ack <= 1;
    end
    else if (i_ex_executed_ack) begin
      o_ex_decoded_ack <= 0;
    end
  end
end

exeU ExeU(
  .i_opcode                   (tmp_i_ex_opcode            ),
  .i_funct3                   (tmp_i_ex_funct3            ),
  .i_funct7                   (tmp_i_ex_funct7            ),
  .i_op1                      (tmp_i_ex_op1               ),
  .i_op2                      (tmp_i_ex_op2               ),
  .i_t1                       (tmp_i_ex_t1                ),
  .i_memren                   (tmp_i_ex_memren            ),
  .i_memwen                   (tmp_i_ex_memwen            ),
  .i_pc_pred                  (i_ex_pc_pred               ),
  .o_pc_jmp                   (o_ex_pc_jmp                ),
  .o_pc_jmpaddr               (o_ex_pc_jmpaddr            ),
  .o_rd_wen                   (o_ex_rd_wen                ),
  .o_rd_data                  (o_ex_rd_wdata              ),
  .o_memren                   (o_ex_memren                ),
  .o_memwen                   (o_ex_memwen                )
);

endmodule
