
// ZhengpuShi

// Memory Interface

`include "defines.v"

module ysyx_210544_mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   wire                i_mem_executed_req,
  output  wire                o_mem_executed_ack,
  output  reg                 o_mem_memoryed_req,
  input   wire                i_mem_memoryed_ack,
  input   wire  [`YSYX210544_BUS_64]     i_mem_pc,
  input   wire  [`YSYX210544_BUS_32]     i_mem_inst,
  input   wire  [`YSYX210544_BUS_RIDX]   i_mem_rd,
  input   wire                i_mem_rd_wen,
  input   wire  [`YSYX210544_BUS_64]     i_mem_rd_wdata,
  input   wire                i_mem_skipcmt,
  input   wire  [7 : 0]       i_mem_inst_opcode,
  input   wire  [`YSYX210544_BUS_64]     i_mem_op1,
  input   wire  [`YSYX210544_BUS_64]     i_mem_op2,
  input   wire  [`YSYX210544_BUS_64]     i_mem_op3,
  output  wire  [`YSYX210544_BUS_RIDX]   o_mem_rd,
  output  wire                o_mem_rd_wen,
  output  reg   [`YSYX210544_BUS_64]     o_mem_rd_wdata,
  output  wire  [`YSYX210544_BUS_64]     o_mem_pc,
  output  wire  [`YSYX210544_BUS_32]     o_mem_inst,
  output  wire                o_mem_skipcmt,
  output  wire                o_mem_clint_mtime_overflow,
  input   wire  [`YSYX210544_BUS_32]     i_mem_intrNo,
  output  reg   [`YSYX210544_BUS_32]     o_mem_intrNo,
  output  wire                o_mem_fencei_req,
  input   wire                i_mem_fencei_ack,

  ///////////////////////////////////////////////
  // DCache interface
  output  wire                o_dcache_req,
  output  wire  [63:0]        o_dcache_addr,
  output  wire                o_dcache_op,
  output  wire  [2 :0]        o_dcache_bytes,
  output  wire  [63:0]        o_dcache_wdata,
  input   wire                i_dcache_ack,
  input   wire  [63:0]        i_dcache_rdata
);

wire                          executed_hs;
wire                          memoryed_hs;
wire                          addr_is_mem;
wire                          addr_is_mmio;
wire                          ren_or_wen;
wire                          ch_cachesync; 
wire                          ch_mem;   
wire                          ch_mmio;  
wire                          ch_none;  

// memoryed request for different slaves
wire                          memoryed_req_cachesync;
wire                          memoryed_req_mem;
wire                          memoryed_req_mmio;
wire                          memoryed_req_none;
wire   [`YSYX210544_BUS_64]              rdata_mem;      // readed data from mmio
wire   [`YSYX210544_BUS_64]              rdata_mmio;     // readed data from main memory
reg    [`YSYX210544_BUS_64]              rdata;          // readed data from main memory or mmio

// 保存输入信息
reg   [`YSYX210544_BUS_64]               tmp_i_mem_pc;
reg   [`YSYX210544_BUS_32]               tmp_i_mem_inst;
reg   [`YSYX210544_BUS_RIDX]             tmp_i_mem_rd;
reg                           tmp_i_mem_rd_wen;
reg   [`YSYX210544_BUS_64]               tmp_i_mem_rd_wdata;
reg   [7 : 0]                 tmp_i_mem_inst_opcode;
reg                           tmp_i_mem_skipcmt;
reg                           tmp_ch_cachesync;
reg                           tmp_ch_mem;
reg                           tmp_ch_mmio;

wire [63:0]                   mem_addr;
reg  [2:0]                    mem_bytes;
reg                           mem_ren;
reg                           mem_wen;
reg  [63:0]                   mem_wdata;



assign o_mem_executed_ack = 1'b1;

assign executed_hs = i_mem_executed_req & o_mem_executed_ack;
assign memoryed_hs = i_mem_memoryed_ack & o_mem_memoryed_req;

assign addr_is_mem  = (mem_addr[31:28] != 4'b0);
assign addr_is_mmio = (mem_addr[31:24] == 8'h02);// & (64'hFF000000)) == 64'h02000000;

// channel select, only valid in one pulse
assign ren_or_wen = mem_ren | mem_wen;

assign ch_cachesync = i_mem_inst_opcode == `YSYX210544_INST_FENCEI;
assign ch_mem   = addr_is_mem & ren_or_wen;
assign ch_mmio  = addr_is_mmio & ren_or_wen;
assign ch_none  = (!ch_cachesync) & ((!(addr_is_mem | addr_is_mmio)) | (!ren_or_wen));

// o_mem_memoryed_req
always @(*) begin
  if (rst) begin
    o_mem_memoryed_req = 0;
  end
  else if (tmp_ch_cachesync) begin
    o_mem_memoryed_req = memoryed_req_cachesync;
  end
  else if (tmp_ch_mem) begin
    o_mem_memoryed_req = memoryed_req_mem;
  end
  else if (tmp_ch_mmio) begin
    o_mem_memoryed_req = memoryed_req_mmio;
  end
  else begin
    o_mem_memoryed_req = memoryed_req_none;
  end
end

// rdata
always @(*) begin
  if (rst) begin
    rdata = 0;
  end
  else if (tmp_ch_mem) begin
    rdata = rdata_mem;
  end
  else if (tmp_ch_mmio) begin
    rdata = rdata_mmio;
  end
  else begin
    rdata = 0;
  end
end

// o_mem_memoryed_req
always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_mem_pc,
      tmp_i_mem_inst,
      tmp_i_mem_rd,
      tmp_i_mem_rd_wen,
      tmp_i_mem_rd_wdata,
      tmp_i_mem_inst_opcode,
      tmp_i_mem_skipcmt,
      tmp_ch_cachesync,
      tmp_ch_mem,
      tmp_ch_mmio
    } <= 0;

    o_mem_intrNo <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_i_mem_pc              <= i_mem_pc;
      tmp_i_mem_inst            <= i_mem_inst;
      tmp_i_mem_inst_opcode     <= i_mem_inst_opcode;
      tmp_i_mem_rd              <= i_mem_rd;
      tmp_i_mem_rd_wen          <= i_mem_rd_wen;
      tmp_i_mem_rd_wdata        <= i_mem_rd_wdata;
      tmp_i_mem_skipcmt         <= i_mem_skipcmt;
      tmp_ch_cachesync          <= ch_cachesync;
      tmp_ch_mem                <= ch_mem;
      tmp_ch_mmio               <= ch_mmio;

      o_mem_intrNo <= i_mem_intrNo;
    end
    else if (memoryed_hs) begin
      // 该通道号需要消除，不能留到下一个指令
      tmp_ch_cachesync          <= 0;
      tmp_ch_mem                <= 0;
      tmp_ch_mmio               <= 0;

      o_mem_intrNo <= 0;

    end
  end
end

assign o_mem_pc           = tmp_i_mem_pc;
assign o_mem_inst         = tmp_i_mem_inst;
assign o_mem_rd           = tmp_i_mem_rd;
assign o_mem_rd_wen       = tmp_i_mem_rd_wen;
// assign o_mem_rd_wdata     = tmp_i_mem_rd_wdata;
assign o_mem_skipcmt      = tmp_i_mem_skipcmt | tmp_ch_mmio;

// ren, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_ren = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_LB  : begin mem_ren = 1; end
      `YSYX210544_INST_LBU : begin mem_ren = 1; end
      `YSYX210544_INST_LH  : begin mem_ren = 1; end
      `YSYX210544_INST_LHU : begin mem_ren = 1; end 
      `YSYX210544_INST_LW  : begin mem_ren = 1; end
      `YSYX210544_INST_LWU : begin mem_ren = 1; end
      `YSYX210544_INST_LD  : begin mem_ren = 1; end
      default   : begin mem_ren = 0; end
    endcase
  end
end

// wen, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_wen = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_SB  : begin mem_wen = 1; end
      `YSYX210544_INST_SH  : begin mem_wen = 1; end
      `YSYX210544_INST_SW  : begin mem_wen = 1; end
      `YSYX210544_INST_SD  : begin mem_wen = 1; end
      default   : begin mem_wen = 0; end
    endcase
  end
end

// addr, only valid at one pulse
assign mem_addr = i_mem_op1 + i_mem_op3;

// bytes, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_bytes = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_LB  : begin mem_bytes = 0; end
      `YSYX210544_INST_LBU : begin mem_bytes = 0; end
      `YSYX210544_INST_SB  : begin mem_bytes = 0; end
      `YSYX210544_INST_LH  : begin mem_bytes = 1; end
      `YSYX210544_INST_LHU : begin mem_bytes = 1; end 
      `YSYX210544_INST_SH  : begin mem_bytes = 1; end
      `YSYX210544_INST_LW  : begin mem_bytes = 3; end
      `YSYX210544_INST_SW  : begin mem_bytes = 3; end
      `YSYX210544_INST_LWU : begin mem_bytes = 3; end
      `YSYX210544_INST_LD  : begin mem_bytes = 7; end
      `YSYX210544_INST_SD  : begin mem_bytes = 7; end
      default   : begin mem_bytes = 0; end
    endcase
  end
end

// wdata, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_wdata = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_SB  : begin mem_wdata = {56'd0, i_mem_op2[7:0]}; end
      `YSYX210544_INST_SH  : begin mem_wdata = {48'd0, i_mem_op2[15:0]}; end
      `YSYX210544_INST_SW  : begin mem_wdata = {32'd0, i_mem_op2[31:0]}; end
      `YSYX210544_INST_SD  : begin mem_wdata = i_mem_op2[63:0]; end
      default   : begin mem_wdata = 0; end
    endcase
  end
end

// rdata, valid at several pulses
always @(*) begin
  if (rst) begin
    o_mem_rd_wdata = 0;
  end
  else begin
    case (tmp_i_mem_inst_opcode)
      `YSYX210544_INST_LB  : begin o_mem_rd_wdata = {{57{rdata[7]}}, rdata[6:0]} ; end
      `YSYX210544_INST_LBU : begin o_mem_rd_wdata = {56'd0, rdata[7:0]}; end
      `YSYX210544_INST_LH  : begin o_mem_rd_wdata = {{49{rdata[15]}}, rdata[14:0]}; end
      `YSYX210544_INST_LHU : begin o_mem_rd_wdata = {48'd0, rdata[15:0]}; end
      `YSYX210544_INST_LW  : begin o_mem_rd_wdata = {{33{rdata[31]}}, rdata[30:0]}; end
      `YSYX210544_INST_LWU : begin o_mem_rd_wdata = {32'd0, rdata[31:0]}; end
      `YSYX210544_INST_LD  : begin o_mem_rd_wdata = rdata[63:0]; end
      default   : begin o_mem_rd_wdata = tmp_i_mem_rd_wdata; end
    endcase
  end
end

// 访问主存和外设（过AXI总线）
ysyx_210544_memU MemU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_mem ),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_mem           ),
  .i_addr                     (mem_addr                   ),
  .i_bytes                    (mem_bytes                  ),
  .i_ren                      (mem_ren                    ),
  .i_wen                      (mem_wen                    ),
  .i_wdata                    (mem_wdata                  ),
  .o_rdata                    (rdata_mem                  ),

  .o_dcache_req               (o_dcache_req               ),
  .o_dcache_addr              (o_dcache_addr              ),
  .o_dcache_op                (o_dcache_op                ),
  .o_dcache_bytes             (o_dcache_bytes             ),
  .o_dcache_wdata             (o_dcache_wdata             ),
  .i_dcache_ack               (i_dcache_ack               ),
  .i_dcache_rdata             (i_dcache_rdata             )
);

// 访问外设（cpu内部的）
ysyx_210544_mem_mmio Mem_mmio(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_mmio),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_mmio          ), 
  .ren                        (mem_ren                    ),
  .wen                        (mem_wen                    ),
  .wdata                      (mem_wdata                  ),
  .addr                       (mem_addr                   ),
  .rdata                      (rdata_mmio                 ),
  .o_clint_mtime_overflow     (o_mem_clint_mtime_overflow )
);

// 访问Cache
ysyx_210544_mem_cachesync Mem_cachesync(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_cachesync),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_cachesync     ),
  .o_cachesync_req            (o_mem_fencei_req           ),
  .i_cachesync_ack            (i_mem_fencei_ack           )
);

// 仅握手
ysyx_210544_mem_nothing Mem_nothing(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_none),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_none          )
);

endmodule
