
// Zhengpu Shi

// Memory Interface

`include "defines.v";

module mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_mem_executed_req,
  output  reg                 o_mem_executed_ack,
  output  reg                 o_mem_memoryed_req,
  input   reg                 i_mem_memoryed_ack,
  input   wire  [`BUS_64]     i_mem_pc,
  input   wire  [`BUS_32]     i_mem_inst,
  input   wire  [`BUS_64]     i_mem_addr,
  input   wire                i_mem_ren,
  input   wire  [2 : 0]       i_mem_funct3,
  input   wire                i_mem_wen,
  input   wire  [`BUS_64]     i_mem_wdata,
  output  wire  [`BUS_64]     o_mem_pc,
  output  wire  [`BUS_32]     o_mem_inst,
  output  wire  [`BUS_64]     o_mem_rdata
);


assign o_mem_executed_ack = 1'b1;

wire executed_hs = i_mem_executed_req & o_mem_executed_ack;

// 保存输入信息
reg   [`BUS_64]               tmp_i_mem_pc;
reg   [`BUS_32]               tmp_i_mem_inst;
reg   [`BUS_64]               tmp_i_mem_addr;
reg                           tmp_i_mem_ren;
reg   [2 : 0]                 tmp_i_mem_funct3;
reg                           tmp_i_mem_wen;
reg   [`BUS_64]               tmp_i_mem_wdata;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_mem_pc,
      tmp_i_mem_inst,
      tmp_i_mem_addr, 
      tmp_i_mem_ren, 
      tmp_i_mem_funct3, 
      tmp_i_mem_wen, 
      tmp_i_mem_wdata
    } <= 0;

    o_mem_memoryed_req <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_i_mem_pc        <= i_mem_pc;
      tmp_i_mem_inst      <= i_mem_inst;
      tmp_i_mem_addr      <= i_mem_addr; 
      tmp_i_mem_ren       <= i_mem_ren;
      tmp_i_mem_funct3    <= i_mem_funct3;
      tmp_i_mem_wen       <= i_mem_wen;
      tmp_i_mem_wdata     <= i_mem_wdata;

      o_mem_memoryed_req <= 1;
    end
    else if (i_mem_memoryed_ack) begin
      o_mem_memoryed_req <= 0;
    end
  end
end

assign o_mem_pc = tmp_i_mem_pc;
assign o_mem_inst = tmp_i_mem_inst;

memU MemU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_addr                     (tmp_i_mem_addr             ),
  .i_ren                      (tmp_i_mem_ren              ),
  .i_funct3                   (tmp_i_mem_funct3           ),
  .i_wen                      (tmp_i_mem_wen              ),
  .i_wdata                    (tmp_i_mem_wdata            ),
  .o_rdata                    (o_mem_rdata                )
);

endmodule
