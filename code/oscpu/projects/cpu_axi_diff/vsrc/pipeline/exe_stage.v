
// ZhengpuShi

// Execute Interface

`include "../defines.v"

module exe_stage(
  input   wire                rst,
  input   wire                clk,
  input   reg                 i_ex_decoded_req,
  output  reg                 o_ex_decoded_ack,
  output  reg                 o_ex_executed_req,
  input   reg                 i_ex_executed_ack,
  input   wire  [4 : 0]       i_ex_inst_type,
  input   wire  [7 : 0]       i_ex_inst_opcode,
  input   wire  [`BUS_64]     i_ex_pc,
  input   wire  [`BUS_32]     i_ex_inst,
  input   wire  [`BUS_OPCODE] i_ex_opcode,
  input   wire  [`BUS_FUNCT3] i_ex_funct3,
  input   wire  [`BUS_FUNCT7] i_ex_funct7,
  input   wire  [`BUS_64]     i_ex_op1,
  input   wire  [`BUS_64]     i_ex_op2,
  input   wire  [`BUS_64]     i_ex_t1,
  input   wire  [`BUS_64]     i_ex_memaddr,
  input   wire                i_ex_memren,
  input   wire                i_ex_memwen,
  input   wire  [`BUS_64]     i_ex_pc_pred,
  input   wire  [`BUS_RIDX]   i_ex_rd,
  input   reg                 i_ex_rd_wen,
  input   wire                i_ex_nocmt,
  input   wire                i_ex_skipcmt,
  input   wire  [1:0]         i_ex_memaction,
  output  reg   [`BUS_64]     o_ex_pc,
  output  wire  [`BUS_FUNCT3] o_ex_funct3,
  output  reg   [`BUS_32]     o_ex_inst,
  output  reg                 o_ex_pc_jmp,
  output  reg   [`BUS_64]     o_ex_pc_jmpaddr,
  output  reg   [`BUS_RIDX]   o_ex_rd,
  output  reg                 o_ex_rd_wen,
  output  reg   [`BUS_64]     o_ex_rd_wdata,
  output  reg   [`BUS_64]     o_ex_memaddr,
  output  reg                 o_ex_memren,
  output  reg                 o_ex_memwen,
  output  wire  [`BUS_64]     o_ex_op1,
  output  wire  [`BUS_64]     o_ex_op2,
  output  wire                o_ex_nocmt,
  output  wire                o_ex_skipcmt,
  output  wire  [1:0]         o_ex_memaction
);

assign o_ex_decoded_ack = 1'b1;

wire decoded_hs = i_ex_decoded_req & o_ex_decoded_ack;


// 是否使能组合逻辑单元部件
reg                           i_ena;
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [4 : 0]                 tmp_i_ex_inst_type;
reg   [7 : 0]                 tmp_i_ex_inst_opcode;
reg   [`BUS_64]               tmp_i_ex_pc;
reg   [`BUS_32]               tmp_i_ex_inst;
reg   [6 : 0]                 tmp_i_ex_opcode;
reg   [2 : 0]                 tmp_i_ex_funct3;
reg   [6 : 0]                 tmp_i_ex_funct7;
reg   [`BUS_64]               tmp_i_ex_op1;
reg   [`BUS_64]               tmp_i_ex_op2;
reg   [`BUS_64]               tmp_i_ex_t1;
reg   [`BUS_64]               tmp_i_ex_memaddr;
reg                           tmp_i_ex_memren;
reg                           tmp_i_ex_memwen;
reg   [4 : 0]                 tmp_i_ex_rd;
reg                           tmp_i_ex_rd_wen;
reg                           tmp_i_ex_nocmt;
reg                           tmp_i_ex_skipcmt;
reg   [1:0]                   tmp_i_ex_memaction;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_ex_inst_type,
      tmp_i_ex_inst_opcode,
      tmp_i_ex_pc,
      tmp_i_ex_inst,
      tmp_i_ex_opcode, 
      tmp_i_ex_funct3, 
      tmp_i_ex_funct7, 
      tmp_i_ex_op1, 
      tmp_i_ex_op2, 
      tmp_i_ex_t1,
      tmp_i_ex_memaddr,
      tmp_i_ex_memren,
      tmp_i_ex_memwen,
      tmp_i_ex_rd,
      tmp_i_ex_rd_wen,
      tmp_i_ex_nocmt,
      tmp_i_ex_skipcmt,
      tmp_i_ex_memaction
    } <= 0;

    o_ex_executed_req   <= 0;
    i_ena               <= 0;
  end
  else begin
    if (decoded_hs) begin
      tmp_i_ex_inst_type   <= i_ex_inst_type;
      tmp_i_ex_inst_opcode <= i_ex_inst_opcode;
      tmp_i_ex_pc       <= i_ex_pc;
      tmp_i_ex_inst     <= i_ex_inst;
      tmp_i_ex_opcode   <= i_ex_opcode; 
      tmp_i_ex_funct3   <= i_ex_funct3;
      tmp_i_ex_funct7   <= i_ex_funct7;
      tmp_i_ex_op1      <= i_ex_op1;
      tmp_i_ex_op2      <= i_ex_op2;
      tmp_i_ex_t1       <= i_ex_t1;
      tmp_i_ex_memaddr  <= i_ex_memaddr;
      tmp_i_ex_memren   <= i_ex_memren;
      tmp_i_ex_memwen   <= i_ex_memwen;
      tmp_i_ex_rd       <= i_ex_rd;
      tmp_i_ex_rd_wen   <= i_ex_rd_wen;
      tmp_i_ex_nocmt    <= i_ex_nocmt;
      tmp_i_ex_skipcmt  <= i_ex_skipcmt;
      tmp_i_ex_memaction <= i_ex_memaction;

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

assign o_ex_pc      = i_disable ? 0 : tmp_i_ex_pc;
assign o_ex_funct3  = i_disable ? 0 : tmp_i_ex_funct3;
assign o_ex_inst    = i_disable ? 0 : tmp_i_ex_inst;
assign o_ex_rd      = i_disable ? 0 : tmp_i_ex_rd;
assign o_ex_op1     = i_disable ? 0 : tmp_i_ex_op1;
assign o_ex_op2     = i_disable ? 0 : tmp_i_ex_op2;
assign o_ex_rd      = i_disable ? 0 : tmp_i_ex_rd;
assign o_ex_rd_wen  = i_disable ? 0 : tmp_i_ex_rd_wen;
assign o_ex_nocmt   = i_disable ? 0 : tmp_i_ex_nocmt;
assign o_ex_skipcmt = i_disable ? 0 : tmp_i_ex_skipcmt;
assign o_ex_memaction = i_disable ? 0 : tmp_i_ex_memaction;


// o_memaddr
assign o_ex_memaddr = i_disable ? 0 : tmp_i_ex_memaddr;

exeU ExeU(
  .rst                        (rst                        ),
  .i_ena                      (i_ena                      ),
  .i_inst_type                (tmp_i_ex_inst_type         ),
  .i_inst_opcode              (tmp_i_ex_inst_opcode       ),
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
  .o_rd_wen                   (                 ),
  .o_rd_data                  (o_ex_rd_wdata              ),
  .o_memren                   (o_ex_memren                ),
  .o_memwen                   (o_ex_memwen                )
);

endmodule