
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
  input   wire  [`BUS_64]     i_ex_op1,
  input   wire  [`BUS_64]     i_ex_op2,
  input   wire  [`BUS_64]     i_ex_op3,
  input   wire  [`BUS_RIDX]   i_ex_rd,
  input   reg                 i_ex_rd_wen,
  input   wire                i_ex_nocmt,
  input   wire                i_ex_clint_mstatus_mie,
  input   wire                i_ex_clint_mie_mtie,
  input   wire                i_ex_clint_mtime_overflow,
  input   wire                i_ex_skipcmt,
  input   reg   [`BUS_64]     i_ex_csr_rdata,
  input   reg   [`BUS_64]     i_ex_clint_mip,
  output  reg   [`BUS_64]     o_ex_clint_mip,
  output  reg   [11 : 0]      o_ex_csr_addr,
  output  reg                 o_ex_csr_ren,
  output  reg                 o_ex_csr_wen,
  output  reg   [`BUS_64]     o_ex_csr_wdata,
  output  reg   [`BUS_64]     o_ex_pc,
  output  reg   [`BUS_32]     o_ex_inst,
  output  reg                 o_ex_pc_jmp,
  output  reg   [`BUS_64]     o_ex_pc_jmpaddr,
  output  reg   [`BUS_RIDX]   o_ex_rd,
  output  reg                 o_ex_rd_wen,
  output  reg   [`BUS_64]     o_ex_rd_wdata,
  output  wire  [4 : 0]       o_ex_inst_type,
  output  wire  [7 : 0]       o_ex_inst_opcode,
  output  wire  [`BUS_64]     o_ex_op1,
  output  wire  [`BUS_64]     o_ex_op2,
  output  wire  [`BUS_64]     o_ex_op3,
  output  wire                o_ex_nocmt,
  output  wire                o_ex_skipcmt,
  output  reg   [`BUS_64]     o_ex_intrNo
);

assign o_ex_decoded_ack = 1'b1;

wire decoded_hs = i_ex_decoded_req & o_ex_decoded_ack;
wire executed_hs = i_ex_executed_ack & o_ex_executed_req;

wire exeU_skip_cmt;

// 是否为异常指令：ecall, mret
wire is_inst_exceptionU = (i_ex_inst_opcode == `INST_ECALL) |
  (i_ex_inst_opcode == `INST_MRET);
// 是否产生了时钟中断？
wire is_time_int_req = i_ex_clint_mstatus_mie & i_ex_clint_mie_mtie & i_ex_clint_mtime_overflow;

// 通道选择
reg o_ena_exeU;
reg o_ena_exceptionU;

wire            exeU_req;
wire            exeU_pc_jmp;
wire [`BUS_64]  exeU_pc_jmpaddr;

wire            exceptionU_req;
wire            exceptionU_pc_jmp;
wire [`BUS_64]  exceptionU_pc_jmpaddr;


// 保存输入信息
reg   [4 : 0]                 tmp_i_ex_inst_type;
reg   [7 : 0]                 tmp_i_ex_inst_opcode;
reg   [`BUS_64]               tmp_i_ex_pc;
reg   [`BUS_32]               tmp_i_ex_inst;
reg   [`BUS_64]               tmp_i_ex_op1;
reg   [`BUS_64]               tmp_i_ex_op2;
reg   [`BUS_64]               tmp_i_ex_op3;
reg   [4 : 0]                 tmp_i_ex_rd;
reg                           tmp_i_ex_rd_wen;
reg                           tmp_i_ex_nocmt;
reg                           tmp_i_ex_skipcmt;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_ex_inst_type,
      tmp_i_ex_inst_opcode,
      tmp_i_ex_pc,
      tmp_i_ex_inst,
      tmp_i_ex_op1, 
      tmp_i_ex_op2, 
      tmp_i_ex_op3,
      tmp_i_ex_rd,
      tmp_i_ex_rd_wen,
      tmp_i_ex_nocmt,
      tmp_i_ex_skipcmt
    } <= 0;

    o_ex_executed_req   <= 0;
    o_ena_exceptionU    <= 0;
    o_ex_clint_mip      <= 0;
    o_ex_intrNo <= 0;
  end
  else begin
    // 启动
    if (decoded_hs) begin
      tmp_i_ex_inst_type   <= i_ex_inst_type;
      tmp_i_ex_inst_opcode <= i_ex_inst_opcode;
      tmp_i_ex_pc       <= i_ex_pc;
      tmp_i_ex_inst     <= i_ex_inst;
      tmp_i_ex_op1      <= i_ex_op1;
      tmp_i_ex_op2      <= i_ex_op2;
      tmp_i_ex_op3      <= i_ex_op3;
      tmp_i_ex_rd       <= i_ex_rd;
      tmp_i_ex_rd_wen   <= i_ex_rd_wen;
      tmp_i_ex_nocmt    <= i_ex_nocmt;
      tmp_i_ex_skipcmt  <= i_ex_skipcmt;
      
      // 只使用命令执行之前的 mip 值
      // o_ex_clint_mip    <= i_ex_clint_mip;
      o_ex_clint_mip    <= is_time_int_req ? 64'h80 : 0;//  i_ex_clint_mip;
      o_ex_intrNo <= is_time_int_req ? 7 : 0;

      // 通道选择
      if (!is_inst_exceptionU && !is_time_int_req) begin
        o_ena_exeU        <= 1;
        // exeU立即结束，请求信号置位
        o_ex_executed_req <= 1;
      end
      else begin
        o_ena_exceptionU  <= 1;
      end
    end
    // exeU或exceptionU收到应答，请求信号撤销
    else if (executed_hs) begin
      o_ex_executed_req <= 0;
      o_ena_exeU        <= 0;
      o_ena_exceptionU  <= 0;
      o_ex_intrNo <= 0;
    end
    // exceptionU结束，请求信号置位
    else if (exceptionU_req) begin
      o_ex_executed_req <= 1;
    end
  end
end

wire i_disable = rst | (!executed_hs);

assign o_ex_pc            = i_disable ? 0 : tmp_i_ex_pc;
assign o_ex_inst          = i_disable ? 0 : tmp_i_ex_inst;
assign o_ex_rd            = i_disable ? 0 : tmp_i_ex_rd;
assign o_ex_op1           = i_disable ? 0 : tmp_i_ex_op1;
assign o_ex_op2           = i_disable ? 0 : tmp_i_ex_op2;
assign o_ex_op3           = i_disable ? 0 : tmp_i_ex_op3;
assign o_ex_inst_type     = i_disable ? 0 : tmp_i_ex_inst_type;
assign o_ex_inst_opcode   = i_disable ? 0 : tmp_i_ex_inst_opcode;
assign o_ex_rd            = i_disable ? 0 : (!o_ena_exeU ? 0 : tmp_i_ex_rd);
assign o_ex_rd_wen        = i_disable ? 0 : (!o_ena_exeU ? 0 : tmp_i_ex_rd_wen);
assign o_ex_nocmt         = i_disable ? 0 : tmp_i_ex_nocmt;
assign o_ex_skipcmt       = i_disable ? 0 : (tmp_i_ex_skipcmt | exeU_skip_cmt);


wire   [11 : 0]      exeU_csr_addr;
wire                 exeU_csr_ren;
wire                 exeU_csr_wen;
wire   [`BUS_64]     exeU_csr_wdata;
wire   [`BUS_64]     exceptionU_csr_rdata;
wire   [11 : 0]      exceptionU_csr_addr;
wire                 exceptionU_csr_ren;
wire                 exceptionU_csr_wen;
wire   [`BUS_64]     exceptionU_csr_wdata;


assign o_ex_pc_jmp      = rst ? 0 : (o_ena_exeU ? exeU_pc_jmp     : exceptionU_pc_jmp);
assign o_ex_pc_jmpaddr  = rst ? 0 : (o_ena_exeU ? exeU_pc_jmpaddr : exceptionU_pc_jmpaddr);
assign o_ex_csr_addr    = rst ? 0 : (o_ena_exeU ? exeU_csr_addr   : exceptionU_csr_addr);
assign o_ex_csr_ren     = rst ? 0 : (o_ena_exeU ? exeU_csr_ren    : exceptionU_csr_ren);
assign o_ex_csr_wen     = rst ? 0 : (o_ena_exeU ? exeU_csr_wen    : exceptionU_csr_wen);
assign o_ex_csr_wdata   = rst ? 0 : (o_ena_exeU ? exeU_csr_wdata  : exceptionU_csr_wdata);

exeU ExeU(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .ena                        (o_ena_exeU                 ),
  .ack                        (i_ex_executed_ack          ),
  .req                        (exeU_req                   ),
  .i_inst_type                (tmp_i_ex_inst_type         ),
  .i_inst_opcode              (tmp_i_ex_inst_opcode       ),
  .i_op1                      (tmp_i_ex_op1               ),
  .i_op2                      (tmp_i_ex_op2               ),
  .i_op3                      (tmp_i_ex_op3               ),
  .i_csr_rdata                (i_ex_csr_rdata             ),
  .o_csr_addr                 (exeU_csr_addr              ),
  .o_csr_ren                  (exeU_csr_ren               ),
  .o_csr_wen                  (exeU_csr_wen               ),
  .o_csr_wdata                (exeU_csr_wdata             ),
  .o_pc_jmp                   (exeU_pc_jmp                ),
  .o_pc_jmpaddr               (exeU_pc_jmpaddr            ),
  .o_rd_wdata                 (o_ex_rd_wdata              ),
  .o_exeU_skip_cmt            (exeU_skip_cmt              )
);

exceptionU ExceptionU(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .ena                        (o_ena_exceptionU & (!o_ex_executed_req)),
  .ack                        (i_ex_executed_ack          ),
  .req                        (exceptionU_req             ),
  .i_inst_opcode              (i_ex_inst_opcode           ),
  .i_pc                       (tmp_i_ex_pc                ),
  .i_csr_rdata                (i_ex_csr_rdata             ),
  .o_pc_jmp                   (exceptionU_pc_jmp          ),
  .o_pc_jmpaddr               (exceptionU_pc_jmpaddr      ),
  .o_csr_addr                 (exceptionU_csr_addr        ),
  .o_csr_ren                  (exceptionU_csr_ren         ),
  .o_csr_wen                  (exceptionU_csr_wen         ),
  .o_csr_wdata                (exceptionU_csr_wdata       )
);

endmodule
