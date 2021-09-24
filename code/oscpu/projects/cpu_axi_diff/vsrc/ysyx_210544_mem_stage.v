
// ZhengpuShi

// Memory Interface

`include "defines.v"

module ysyx_210544_mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_mem_executed_req,
  output  reg                 o_mem_executed_ack,
  output  reg                 o_mem_memoryed_req,
  input   reg                 i_mem_memoryed_ack,
  input   wire  [`BUS_64]     i_mem_pc,
  input   wire  [`BUS_32]     i_mem_inst,
  input   wire  [`BUS_RIDX]   i_mem_rd,
  input   wire                i_mem_rd_wen,
  input   wire  [`BUS_64]     i_mem_rd_wdata,
  input   wire                i_mem_nocmt,
  input   wire                i_mem_skipcmt,
  input   wire  [4 : 0]       i_mem_inst_type,
  input   wire  [7 : 0]       i_mem_inst_opcode,
  input   wire  [`BUS_64]     i_mem_op1,
  input   wire  [`BUS_64]     i_mem_op2,
  input   wire  [`BUS_64]     i_mem_op3,
  input   reg   [`BUS_64]     i_mem_clint_mip,
  output  reg   [`BUS_64]     o_mem_clint_mip,
  output  wire  [`BUS_RIDX]   o_mem_rd,
  output  wire                o_mem_rd_wen,
  output  wire  [`BUS_64]     o_mem_rd_wdata,
  output  wire  [`BUS_64]     o_mem_pc,
  output  wire  [`BUS_32]     o_mem_inst,
  output  wire                o_mem_nocmt,
  output  wire                o_mem_skipcmt,
  output  wire                o_mem_clint_mtime_overflow,
  input   wire  [`BUS_32]     i_mem_intrNo,
  output  reg   [`BUS_32]     o_mem_intrNo,

  ///////////////////////////////////////////////
  // DCache interface
  output  wire                o_dcache_req,
  output  wire  [63:0]        o_dcache_addr,
  output  wire                o_dcache_op,
  output  wire  [3 :0]        o_dcache_bytes,
  output  wire  [63:0]        o_dcache_wdata,
  input   wire                i_dcache_ack,
  input   wire  [63:0]        i_dcache_rdata
);


assign o_mem_executed_ack = 1'b1;

wire executed_hs = i_mem_executed_req & o_mem_executed_ack;
wire memoryed_hs = i_mem_memoryed_ack & o_mem_memoryed_req;

wire addr_is_mem  = (mem_addr & (64'hFF000000)) == 64'h80000000;
wire addr_is_mmio = (mem_addr & (64'hFF000000)) == 64'h02000000;

// channel select, only valid in one pulse
wire ch_mem   = addr_is_mem & (mem_ren | mem_wen);
wire ch_mmio  = addr_is_mmio & (mem_ren | mem_wen);
wire ch_none  = (!(addr_is_mem | addr_is_mmio)) | (!(mem_ren | mem_wen));

// memoryed request for different slaves
wire                  memoryed_req_mem;
wire                  memoryed_req_mmio;
wire                  memoryed_req_none;
wire   [`BUS_64]      rdata_mem;      // readed data from mmio
wire   [`BUS_64]      rdata_mmio;     // readed data from main memory
reg    [`BUS_64]      rdata;          // readed data from main memory or mmio

// o_mem_memoryed_req
always @(*) begin
  if (rst) begin
    o_mem_memoryed_req = 0;
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

// 保存输入信息
reg                           tmp_i_mem_executed_req;
reg   [`BUS_64]               tmp_i_mem_pc;
reg   [`BUS_32]               tmp_i_mem_inst;
reg   [`BUS_RIDX]             tmp_i_mem_rd;
reg                           tmp_i_mem_rd_wen;
reg   [`BUS_64]               tmp_i_mem_rd_wdata;
reg   [4 : 0]                 tmp_i_mem_inst_type;
reg   [7 : 0]                 tmp_i_mem_inst_opcode;
reg   [`BUS_64]               tmp_i_mem_op1;
reg   [`BUS_64]               tmp_i_mem_op2;
reg   [`BUS_64]               tmp_i_mem_op3;
reg                           tmp_i_mem_nocmt;
reg                           tmp_i_mem_skipcmt;
reg                           tmp_ch_mem;
reg                           tmp_ch_mmio;
reg                           tmp_ch_none;

reg  [63:0] mem_addr;
reg  [2:0]  mem_bytes;
reg         mem_ren;
reg         mem_wen;
wire [63:0] rdata_mem;
reg  [63:0] mem_wdata;



// o_mem_memoryed_req
always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_mem_executed_req,
      tmp_i_mem_pc,
      tmp_i_mem_inst,
      tmp_i_mem_rd,
      tmp_i_mem_rd_wen,
      tmp_i_mem_rd_wdata,
      tmp_i_mem_inst_type,
      tmp_i_mem_inst_opcode,
      tmp_i_mem_op1,
      tmp_i_mem_op2,
      tmp_i_mem_op3,
      tmp_i_mem_nocmt,
      tmp_i_mem_skipcmt,
      tmp_ch_mem,
      tmp_ch_mmio,
      tmp_ch_none
    } <= 0;

    o_mem_clint_mip <= 0;
    o_mem_intrNo <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_i_mem_executed_req    <= i_mem_executed_req;
      tmp_i_mem_pc              <= i_mem_pc;
      tmp_i_mem_inst            <= i_mem_inst;
      tmp_i_mem_op1             <= i_mem_op1;
      tmp_i_mem_op2             <= i_mem_op2;
      tmp_i_mem_op3             <= i_mem_op3;
      tmp_i_mem_inst_type       <= i_mem_inst_type;
      tmp_i_mem_inst_opcode     <= i_mem_inst_opcode;
      tmp_i_mem_rd              <= i_mem_rd;
      tmp_i_mem_rd_wen          <= i_mem_rd_wen;
      tmp_i_mem_rd_wdata        <= i_mem_rd_wdata;
      tmp_i_mem_nocmt           <= i_mem_nocmt;
      tmp_i_mem_skipcmt         <= i_mem_skipcmt;
      tmp_ch_mem                <= ch_mem;
      tmp_ch_mmio               <= ch_mmio;
      tmp_ch_none               <= ch_none;

      o_mem_clint_mip           <= i_mem_clint_mip;
      o_mem_intrNo <= i_mem_intrNo;
    end
    else if (memoryed_hs) begin
      // 该通道号需要消除，不能留到下一个指令
      tmp_ch_mem                <= 0;
      tmp_ch_mmio               <= 0;
      tmp_ch_none               <= 0;

      o_mem_intrNo <= 0;

    end
  end
end

assign o_mem_pc           = tmp_i_mem_pc;
assign o_mem_inst         = tmp_i_mem_inst;
assign o_mem_rd           = tmp_i_mem_rd;
assign o_mem_rd_wen       = tmp_i_mem_rd_wen;
assign o_mem_rd_wdata     = tmp_i_mem_rd_wdata;
assign o_mem_nocmt        = tmp_i_mem_nocmt;
assign o_mem_skipcmt      = tmp_i_mem_skipcmt | tmp_ch_mmio;


// ren, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_ren = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_LB  : begin mem_ren = 1; end
      `INST_LBU : begin mem_ren = 1; end
      `INST_LH  : begin mem_ren = 1; end
      `INST_LHU : begin mem_ren = 1; end 
      `INST_LW  : begin mem_ren = 1; end
      `INST_LWU : begin mem_ren = 1; end
      `INST_LD  : begin mem_ren = 1; end
      default   : begin mem_ren = 0; end
    endcase
  end
end

// wen, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_wen = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_SB  : begin mem_wen = 1; end
      `INST_SH  : begin mem_wen = 1; end
      `INST_SW  : begin mem_wen = 1; end
      `INST_SD  : begin mem_wen = 1; end
      default   : begin mem_wen = 0; end
    endcase
  end
end

// addr, only valid at one pulse
assign mem_addr = i_mem_op1 + i_mem_op3;

// bytes, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_bytes = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_LB  : begin mem_bytes = 0; end
      `INST_LBU : begin mem_bytes = 0; end
      `INST_SB  : begin mem_bytes = 0; end
      `INST_LH  : begin mem_bytes = 1; end
      `INST_LHU : begin mem_bytes = 1; end 
      `INST_SH  : begin mem_bytes = 1; end
      `INST_LW  : begin mem_bytes = 3; end
      `INST_SW  : begin mem_bytes = 3; end
      `INST_LWU : begin mem_bytes = 3; end
      `INST_LD  : begin mem_bytes = 7; end
      `INST_SD  : begin mem_bytes = 7; end
      default   : begin mem_bytes = 0; end
    endcase
  end
end

// wdata, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_wdata = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_SB  : begin mem_wdata = {56'd0, i_mem_op2[7:0]}; end
      `INST_SH  : begin mem_wdata = {48'd0, i_mem_op2[15:0]}; end
      `INST_SW  : begin mem_wdata = {32'd0, i_mem_op2[31:0]}; end
      `INST_SD  : begin mem_wdata = i_mem_op2[63:0]; end
      default   : begin mem_wdata = 0; end
    endcase
  end
end

// rdata, valid at several pulses
always @(*) begin
  if ( rst == 1'b1) begin
    o_mem_rd_wdata = 0;
  end
  else begin
    case (tmp_i_mem_inst_opcode)
      `INST_LB  : begin o_mem_rd_wdata = {{57{rdata[7]}}, rdata[6:0]} ; end
      `INST_LBU : begin o_mem_rd_wdata = {56'd0, rdata[7:0]}; end
      `INST_LH  : begin o_mem_rd_wdata = {{49{rdata[15]}}, rdata[14:0]}; end
      `INST_LHU : begin o_mem_rd_wdata = {48'd0, rdata[15:0]}; end
      `INST_LW  : begin o_mem_rd_wdata = {{33{rdata[31]}}, rdata[30:0]}; end
      `INST_LWU : begin o_mem_rd_wdata = {32'd0, rdata[31:0]}; end
      `INST_LD  : begin o_mem_rd_wdata = rdata[63:0]; end
      default   : begin o_mem_rd_wdata = tmp_i_mem_rd_wdata; end
    endcase
  end
end

// 访问主存
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

// 访问外设
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

// 仅握手
ysyx_210544_mem_nothing Mem_nothing(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_none),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_none          )
);

endmodule
