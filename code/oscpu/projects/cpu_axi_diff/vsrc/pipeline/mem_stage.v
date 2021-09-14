
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
  input   wire  [`BUS_FUNCT3] i_mem_funct3,
  input   wire                i_mem_wen,
  input   wire  [`BUS_64]     i_mem_wdata,
  input   wire  [`BUS_RIDX]   i_mem_rd,
  input   wire                i_mem_rd_wen,
  input   wire  [`BUS_64]     i_mem_rd_wdata,
  input   wire                i_mem_nocmt,
  input   wire                i_mem_skipcmt,
  output  wire  [`BUS_RIDX]   o_mem_rd,
  output  wire                o_mem_rd_wen,
  output  wire  [`BUS_64]     o_mem_rd_wdata,
  output  wire  [`BUS_64]     o_mem_pc,
  output  wire  [`BUS_32]     o_mem_inst,
  output  wire  [`BUS_64]     o_mem_rdata,
  output  wire                o_mem_nocmt,
  output  wire                o_mem_skipcmt
);


assign o_mem_executed_ack = 1'b1;

wire executed_hs = i_mem_executed_req & o_mem_executed_ack;

// 是否使能组合逻辑单元部件
reg                           i_ena;
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [`BUS_64]               tmp_i_mem_pc;
reg   [`BUS_32]               tmp_i_mem_inst;
reg   [`BUS_64]               tmp_i_mem_addr;
reg                           tmp_i_mem_ren;
reg   [`BUS_FUNCT3]           tmp_i_mem_funct3;
reg                           tmp_i_mem_wen;
reg   [`BUS_64]               tmp_i_mem_wdata;
reg   [`BUS_RIDX]             tmp_i_mem_rd;
reg                           tmp_i_mem_rd_wen;
reg   [`BUS_64]               tmp_i_mem_rd_wdata;
reg                           tmp_i_mem_nocmt;
reg                           tmp_i_mem_skipcmt;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_mem_pc,
      tmp_i_mem_inst,
      tmp_i_mem_addr, 
      tmp_i_mem_ren, 
      tmp_i_mem_funct3, 
      tmp_i_mem_wen, 
      tmp_i_mem_wdata,
      tmp_i_mem_rd,
      tmp_i_mem_rd_wen,
      tmp_i_mem_rd_wdata,
      tmp_i_mem_nocmt,
      tmp_i_mem_skipcmt
    } <= 0;

    o_mem_memoryed_req    <= 0;
    i_ena                 <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_i_mem_pc              <= i_mem_pc;
      tmp_i_mem_inst            <= i_mem_inst;
      tmp_i_mem_addr            <= i_mem_addr; 
      tmp_i_mem_ren             <= i_mem_ren;
      tmp_i_mem_funct3          <= i_mem_funct3;
      tmp_i_mem_wen             <= i_mem_wen;
      tmp_i_mem_wdata           <= i_mem_wdata;
      tmp_i_mem_rd              <= i_mem_rd;
      tmp_i_mem_rd_wen          <= i_mem_rd_wen;
      tmp_i_mem_rd_wdata        <= i_mem_rd_wdata;
      tmp_i_mem_nocmt           <= i_mem_nocmt;
      tmp_i_mem_skipcmt         <= i_mem_skipcmt;

      o_mem_memoryed_req        <= 1;
      i_ena                     <= 1;
    end
    else if (i_mem_memoryed_ack) begin
      o_mem_memoryed_req        <= 0;
      i_ena                     <= 0;
    end
  end
end

assign o_mem_pc           = i_disable ? 0 : tmp_i_mem_pc;
assign o_mem_inst         = i_disable ? 0 : tmp_i_mem_inst;
assign o_mem_rd           = i_disable ? 0 : tmp_i_mem_rd;
assign o_mem_rd_wen       = i_disable ? 0 : tmp_i_mem_rd_wen;
assign o_mem_rd_wdata     = i_disable ? 0 : tmp_i_mem_rd_wdata;
assign o_mem_nocmt        = i_disable ? 0 : tmp_i_mem_nocmt;
assign o_mem_skipcmt      = i_disable ? 0 : tmp_i_mem_skipcmt;

memU MemU(
  .i_ena                      (i_ena                      ),
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_addr                     (i_mem_addr                 ),
  .i_ren                      (i_mem_ren                  ),
  .i_funct3                   (i_mem_funct3               ),
  .i_wen                      (i_mem_wen                  ),
  .i_wdata                    (i_mem_wdata                ),
  .o_rdata                    (o_mem_rdata                )
);

endmodule
