
//--xuezhen--

`include "defines.v"

module if_stage(
  input   wire              clk,
  input   wire              rst,

  // input wire inst_ok,
  input   wire              pc_jmp,
  input   wire  [`BUS_64]   pc_jmpaddr ,

  output  reg   [`BUS_64]   pc_cur,
  output  reg   [`BUS_64]   pc,
  output  reg   [`BUS_32]   inst
);

parameter PC_START_RESET = `PC_START - 4;

// fetch an instruction
always@( posedge clk ) begin
  if( rst == 1'b1 ) begin
    pc_cur <= PC_START_RESET;
    pc <= PC_START_RESET;
  end
  else begin
    // if (inst_ok == 1'b1) begin
      pc_cur <= pc;
      if (pc_jmp == 1'b1)
        pc <= pc_jmpaddr;
      else
        pc <= pc + 4;
    // end
    // else begin
    //   pc_cur <= pc_cur;
    //   pc <= pc;
    // end 
  end
end

// Access memory
reg [`BUS_64] rdata;
RAMHelper RAMHelper(
  .clk              (clk),
  .en               (1),
  .rIdx             ((pc - `PC_START) >> 3),  // 按照64位(8字节)来访问
  .rdata            (rdata),
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
assign inst = pc[2] ? rdata[63 : 32] : rdata[31 : 0];

endmodule