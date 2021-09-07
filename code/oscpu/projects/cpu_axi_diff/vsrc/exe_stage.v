
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
  input   wire  [`BUS_64]     i_ex_pc,
  input   wire  [`BUS_32]     i_ex_inst,
  input   wire  [6 : 0]       i_ex_opcode,
  input   wire  [2 : 0]       i_ex_funct3,
  input   wire  [6 : 0]       i_ex_funct7,
  input   wire  [`BUS_64]     i_ex_op1,
  input   wire  [`BUS_64]     i_ex_op2,
  input   wire  [`BUS_64]     i_ex_t1,
  input   wire                i_ex_memren,
  input   wire                i_ex_memwen,
  input   wire  [`BUS_64]     i_ex_pc_pred,
  input   wire  [4 : 0]       i_ex_rd,
  output  reg   [`BUS_64]     o_ex_pc,
  output  reg   [`BUS_32]     o_ex_inst,
  output  reg                 o_ex_pc_jmp,
  output  reg   [`BUS_64]     o_ex_pc_jmpaddr,
  output  reg   [4 : 0]       o_ex_rd,
  output  reg                 o_ex_rd_wen,
  output  reg   [`BUS_64]     o_ex_rd_wdata,
  output  reg                 o_ex_memren,
  output  reg                 o_ex_memwen
);

assign o_ex_decoded_ack = 1'b1;

wire decoded_hs = i_ex_decoded_req & o_ex_decoded_ack;


// 是否使能组合逻辑单元部件
reg                           i_ena;
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [`BUS_64]               tmp_i_ex_pc;
reg   [`BUS_32]               tmp_i_ex_inst;
reg   [6 : 0]                 tmp_i_ex_opcode;
reg   [2 : 0]                 tmp_i_ex_funct3;
reg   [6 : 0]                 tmp_i_ex_funct7;
reg   [`BUS_64]               tmp_i_ex_op1;
reg   [`BUS_64]               tmp_i_ex_op2;
reg   [`BUS_64]               tmp_i_ex_t1;
reg                           tmp_i_ex_memren;
reg                           tmp_i_ex_memwen;
reg   [4 : 0]                 tmp_i_ex_rd;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_ex_pc,
      tmp_i_ex_inst,
      tmp_i_ex_opcode, 
      tmp_i_ex_funct3, 
      tmp_i_ex_funct7, 
      tmp_i_ex_op1, 
      tmp_i_ex_op2, 
      tmp_i_ex_t1,
      tmp_i_ex_memren,
      tmp_i_ex_memwen,
      tmp_i_ex_rd
    } <= 0;

    o_ex_executed_req   <= 0;
    i_ena               <= 0;
  end
  else begin
    if (decoded_hs) begin
      tmp_i_ex_pc       <= i_ex_pc;
      tmp_i_ex_inst     <= i_ex_inst;
      tmp_i_ex_opcode   <= i_ex_opcode; 
      tmp_i_ex_funct3   <= i_ex_funct3;
      tmp_i_ex_funct7   <= i_ex_funct7;
      tmp_i_ex_op1      <= i_ex_op1;
      tmp_i_ex_op2      <= i_ex_op2;
      tmp_i_ex_t1       <= i_ex_t1;
      tmp_i_ex_memren   <= i_ex_memren;
      tmp_i_ex_memwen   <= i_ex_memwen;
      tmp_i_ex_rd       <= i_ex_rd;

      o_ex_executed_req <= 1;
      i_ena             <= 1;
    end
    else if (i_ex_executed_ack) begin
      i_ena             <= 0;
      o_ex_executed_req <= 0;
      i_ena             <= 0;
    end
  end
end

assign o_ex_pc    = i_disable ? 0 : tmp_i_ex_pc;
assign o_ex_inst  = i_disable ? 0 : tmp_i_ex_inst;
assign o_ex_rd    = i_disable ? 0 : tmp_i_ex_rd;

exeU ExeU(
  .i_ena                      (i_ena                      ),
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
