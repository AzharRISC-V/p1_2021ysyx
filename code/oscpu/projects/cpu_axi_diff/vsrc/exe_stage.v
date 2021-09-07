
// ZhengpuShi

// Execute Interface

`include "defines.v"

module exe_stage(
  input   wire                  rst,
  input   wire                  clk,
  input   reg                   ex_decoded_req_i,
  output  reg                   ex_decoded_ack_o,
  output  reg                   ex_executed_req_o,
  input   reg                   ex_executed_ack_i,

  input   wire  [4 : 0]         ex_opcode_i,
  input   wire  [2 : 0]         ex_funct3_i,
  input   wire  [6 : 0]         ex_funct7_i,
  input   wire  [`REG_BUS]      ex_op1_i,
  input   wire  [`REG_BUS]      ex_op2_i,
  input   wire  [`REG_BUS]      ex_t1_i,
  input   wire                  ex_memren_i,
  input   wire                  ex_memwen_i,

  input   wire  [`BUS_64]       ex_pc_pred_i,     // 顺序计算得出的pc值，用于对比
  output  reg                   ex_pc_jmp_o,
  output  reg   [`BUS_64]       ex_pc_jmpaddr_o,
  output  wire                  ex_rd_wen_o,
  output  wire  [`BUS_64]       ex_rd_wdata_o,
  output  wire                  ex_memren_o,
  output  wire                  ex_memwen_o
  
  // output  wire                  pipe_flush_req,
  // output  wire  [`BUS_64]       pipe_flush_pc,
  // input   wire                  pipe_flush_ack
);

assign ex_decoded_ack_o = 1'b1;

wire decoded_hs = ex_decoded_req_i & ex_decoded_ack_o;

// 保存输入信息
reg   [4 : 0]     tmp_ex_opcode_i;
reg   [2 : 0]     tmp_ex_funct3_i;
reg   [6 : 0]     tmp_ex_funct7_i;
reg   [`REG_BUS]  tmp_ex_op1_i;
reg   [`REG_BUS]  tmp_ex_op2_i;
reg   [`REG_BUS]  tmp_ex_t1_i;
reg               tmp_ex_memren_i;
reg               tmp_ex_memwen_i;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_ex_opcode_i, 
      tmp_ex_funct3_i, 
      tmp_ex_funct7_i, 
      tmp_ex_op1_i, 
      tmp_ex_op2_i, 
      tmp_ex_t1_i,
      tmp_ex_memren_i,
      tmp_ex_memwen_i
    } <= 0;

    ex_executed_req_o <= 0;
  end
  else begin
    if (decoded_hs) begin
      tmp_ex_opcode_i   <= ex_opcode_i; 
      tmp_ex_funct3_i   <= ex_funct3_i;
      tmp_ex_funct7_i   <= ex_funct7_i;
      tmp_ex_op1_i      <= ex_op1_i;
      tmp_ex_op2_i      <= ex_op2_i;
      tmp_ex_t1_i       <= ex_t1_i;
      tmp_ex_memren_i   <= ex_memren_i;
      tmp_ex_memwen_i   <= ex_memwen_i;

      ex_executed_req_o <= 1;
    end
    else if (ex_executed_ack_i) begin
      ex_executed_req_o <= 0;
    end
  end
end

exeU ExeU(
  .opcode                     (tmp_ex_opcode_i            ),
  .funct3                     (tmp_ex_funct3_i            ),
  .funct7                     (tmp_ex_funct7_i            ),
  .op1                        (tmp_ex_op1_i               ),
  .op2                        (tmp_ex_op2_i               ),
  .t1                         (tmp_ex_t1_i                ),
  .memren_i                   (tmp_ex_memren_i            ),
  .memwen_i                   (tmp_ex_memwen_i            ),
  .pc_pred                    (ex_pc_pred_i               ),
  .pc_jmp                     (ex_pc_jmp_o                ),
  .pc_jmpaddr                 (ex_pc_jmpaddr_o            ),
  .rd_wen                     (ex_rd_wen_o                ),
  .rd_data                    (ex_rd_wdata_o              ),
  .memren_o                   (ex_memren_o                ),
  .memwen_o                   (ex_memwen_o                )
);

endmodule
