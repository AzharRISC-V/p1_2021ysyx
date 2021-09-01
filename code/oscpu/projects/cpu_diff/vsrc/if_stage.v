
//--xuezhen--

`include "defines.v"

module if_stage(
  input   wire  [`BUS_64]       clk_cnt,
  input   wire                  clk,
  input   wire                  rst,
  input   wire                  finished,     // 上一条指令是否已经完成？

  input   wire                  pc_jmp,
  input   wire  [`BUS_64]       pc_jmpaddr,

  output  reg   [`BUS_64]       pc_old,
  output  reg   [`BUS_64]       pc,
  output  reg   [`BUS_32]       inst

);


// fetch an instruction
always@(posedge clk) begin
  if(rst) begin
    pc_old    <= 0;
    pc        <= `PC_START_RESET;
  end
  else begin
    if (finished) begin
      pc_old  <= pc;
      pc      <= pc_jmp ? pc_jmpaddr : (pc + 4);
    end
  end
end

// Access memory
reg [`BUS_64] two_inst_data;

RAMHelper InstMemory(
  .show_dbg         (0),
  .clk              (clk),
  .en               (1),
  .rIdx             ((pc - `PC_START) >> 3),  // 按照64位(8字节)来访问
  .rdata            (two_inst_data),
  .wIdx             (0),
  .wdata            (0),
  .wmask            (0),
  .wen              (0)
);


// PC是4的倍数，形式为
// PC             低16位
// 0x8000_0000    0000_0000
// 0x8000_0004    0000_0100
// 0x8000_0008    0000_1000
// 所以，
// pc[2]是0，则是0/2/4/... 第偶数条指令
// pc[2]是1，则是1/3/5/... 第奇数条指令
// 而radata中是一次取出8字节，包含两条指令
assign inst = pc[2] ? two_inst_data[63 : 32] : two_inst_data[31 : 0];

// 是否打印调试信息？
wire show_dbg = (clk_cnt >= `CLK_CNT_VAL);

always@(*) begin
  //$display("--- ");
  if (0)//show_dbg)
    $displayh("  clk_cnt:", clk_cnt, " IF: pc=", pc, " two_inst_data=", two_inst_data, " pc[2]=", pc[2], " inst=", inst);
end

endmodule
