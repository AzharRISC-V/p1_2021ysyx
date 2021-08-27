
//--xuezhen--

`include "defines.v"

module if_stage(
  input   wire  [`BUS_64]       clk_cnt,
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,

  input   wire                  pc_jmp,
  input   wire  [`BUS_64]       pc_jmpaddr,

  output  reg   [`BUS_64]       pc_cur,
  output  reg   [`BUS_64]       pc,
  output  reg   [`BUS_32]       inst

);


// fetch an instruction
always@(posedge clk) begin
  if( rst == 1'b1 ) begin
    pc_cur = `PC_START_RESET;
    pc = `PC_START_RESET;
  end
  else begin
    if (instcycle_cnt_val == 3) begin
      pc_cur = pc;
      if (pc_jmp == 1'b1)
        pc = pc_jmpaddr;
      else
        pc = pc + 4;
    end
  end
end

// Access memory
reg [`BUS_64] two_inst_data;
RAMHelper RAMHelper(
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
  if (show_dbg)
    $displayh("  clk_cnt:", clk_cnt, " IF: pc=", pc, " two_inst_data=", two_inst_data, " pc[2]=", pc[2], " inst=", inst);
end

endmodule
