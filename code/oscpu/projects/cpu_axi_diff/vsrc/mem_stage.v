
// Zhengpu Shi

// Memory Interface

`include "defines.v";

module mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 mem_executed_req_i,
  output  reg                 mem_executed_ack_o,
  output  reg                 mem_memoryed_req_o,
  input   reg                 mem_memoryed_ack_i,
  input   wire  [`BUS_64]     mem_addr_i,
  input   wire                mem_ren_i,
  input   wire  [2 : 0]       mem_funct3_i,
  input   wire                mem_wen_i,
  input   wire  [`BUS_64]     mem_wdata_i,
  output  wire  [`BUS_64]     mem_rdata_o
);


assign mem_executed_ack_o = 1'b1;

wire executed_hs = mem_executed_req_i & mem_executed_ack_o;

// 保存输入信息
reg   [`BUS_64]               tmp_mem_addr_i;
reg                           tmp_mem_ren_i;
reg   [2 : 0]                 tmp_mem_funct3_i;
reg                           tmp_mem_wen_i;
reg   [`BUS_64]               tmp_mem_wdata_i;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_mem_addr_i, 
      tmp_mem_ren_i, 
      tmp_mem_funct3_i, 
      tmp_mem_wen_i, 
      tmp_mem_wdata_i 
    } <= 0;

    mem_memoryed_req_o <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_mem_addr_i      <= mem_addr_i; 
      tmp_mem_ren_i       <= mem_ren_i;
      tmp_mem_funct3_i    <= mem_funct3_i;
      tmp_mem_wen_i       <= mem_wen_i;
      tmp_mem_wdata_i     <= mem_wdata_i;

      mem_memoryed_req_o <= 1;
    end
    else if (mem_memoryed_ack_i) begin
      mem_memoryed_req_o <= 0;
    end
  end
end

memU MemU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .addr_i                     (tmp_mem_addr_i             ),
  .ren_i                      (tmp_mem_ren_i              ),
  .funct3_i                   (tmp_mem_funct3_i           ),
  .wen_i                      (tmp_mem_wen_i              ),
  .wdata_i                    (tmp_mem_wdata_i            ),
  .rdata_o                    (mem_rdata_o                )
);

endmodule
