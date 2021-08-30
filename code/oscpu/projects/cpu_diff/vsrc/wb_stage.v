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
  input   wire                  csr_wen_i     ,   // CSR后的写回
  input   wire  [`BUS_64]       csr_wdata_i   ,

  output  reg                   wen_o,
  output  wire  [`BUS_64]       wdata_o
);

// Indicate that if WB is working
wire wb_active = (instcycle_cnt_val == 4);
wire wb_inactive = !wb_active;

// 写使能
always @(*) begin
  if (wb_inactive) begin
    wen_o = 0;
  end
  else begin
    wen_o = ex_wen_i | mem_wen_i | csr_wen_i;
  end
end

// 写数据
always @(*) begin
  if (!wen_o) begin
    wdata_o = 0;
  end
  else begin
    if (csr_wen_i) begin
      wdata_o = csr_wdata_i;
    end
    else if (mem_wen_i) begin
      wdata_o = mem_wdata_i;
    end
    else if (ex_wen_i) begin
      wdata_o = ex_wdata_i;
    end
    else begin
      wdata_o = 0;
    end
  end
end

endmodule
