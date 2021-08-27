// Zhengpu Shi

`include "defines.v"

/*
  rd 有两处写入，这里做一个简单的处理
  目前还不是流水线，而一个指令不可能同时在EX/MEM后访问rd，所以没有冲突
*/

module wb_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,

  input   wire                  ex_wen_i      ,   // EX后的写回
  input   wire  [`BUS_64]       ex_wdata_i    ,   
  input   wire                  mem_wen_i     ,   // MEM后的写回
  input   wire  [`BUS_64]       mem_wdata_i   ,

  output  reg                   wen_o,
  output  wire  [`BUS_64]       wdata_o
);

// Indicate that if WB is working
wire wb_active = (instcycle_cnt_val == 4);
wire wb_inactive = !wb_active;

// // 保存ex的操作数
// reg               ex_wen;
// reg   [`REG_BUS]  ex_wdata;
// always @(posedge clk) begin
//   if (wb_inactive) begin
//     ex_wen <= 0;
//     ex_wdata <= 0;
//   end
//   else begin
//     if (instcycle_cnt_val == 6) begin
//       ex_wen <= ex_wen_i;
//       ex_wdata <= ex_wdata_i;
//     end
//     else if (instcycle_cnt_val == 0) begin
//       ex_wen <= 0;
//       ex_wdata <= 0;
//     end
//   end
// end

// // 保存mem的操作数
// reg               mem_wen;
// reg   [`REG_BUS]  mem_wdata;
// always @(posedge clk) begin
//   if (wb_inactive) begin
//     mem_wen <= 0;
//     mem_wdata <= 0;
//   end
//   else begin
//     if (instcycle_cnt_val == 6) begin
//       mem_wen <= mem_wen_i;
//       mem_wdata <= mem_wdata_i;
//     end
//     else if (instcycle_cnt_val == 2) begin
//       mem_wen <= 0;
//       mem_wdata <= 0;
//     end
//   end
// end

// 写使能
always @(*) begin
  if (wb_inactive) begin
    wen_o = 0;
  end
  else begin
    // if (instcycle_cnt_val == 6) begin
    //   wen_o = ex_wen_i | mem_wen_i;
    // end
    // else if (instcycle_cnt_val == 2) begin
    //   wen_o = 0;
    // end

    wen_o = ex_wen_i | mem_wen_i;
  end
end

// 写入数据的来源，0：EX, 1:MEM
wire ch = ex_wen_i ? 0 : 1;

// 写数据
assign wdata_o = wen_o ? (ch ? mem_wdata_i : ex_wdata_i) : 0;

endmodule
