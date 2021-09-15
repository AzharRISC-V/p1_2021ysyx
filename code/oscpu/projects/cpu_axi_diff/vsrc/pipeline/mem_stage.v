
// Zhengpu Shi

// Memory Interface

`include "../defines.v";

module mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_mem_executed_req,
  output  reg                 o_mem_executed_ack,
  output  reg                 o_mem_memoryed_req,
  input   reg                 i_mem_memoryed_ack,
  input   wire  [1:0]         i_mem_memaction,
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
  input   wire  [`BUS_64]     i_mem_op1,
  input   wire  [`BUS_64]     i_mem_op2,
  output  wire  [`BUS_RIDX]   o_mem_rd,
  output  wire                o_mem_rd_wen,
  output  wire  [`BUS_64]     o_mem_rd_wdata,
  output  wire  [`BUS_64]     o_mem_pc,
  output  wire  [`BUS_32]     o_mem_inst,
  output  wire  [`BUS_64]     o_mem_rdata,
  output  wire                o_mem_nocmt,
  output  wire                o_mem_skipcmt,

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

// 是否使能组合逻辑单元部件
reg                           i_ena;
wire                          i_disable = !i_ena;

// 保存输入信息
reg                           tmp_i_mem_executed_req;
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
reg   [`BUS_64]               tmp_i_mem_op1;
reg   [`BUS_64]               tmp_i_mem_op2;
reg                           tmp_i_mem_nocmt;
reg                           tmp_i_mem_skipcmt;
reg   [1:0]                   tmp_i_mem_memaction;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_mem_executed_req,
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
      tmp_i_mem_op1,
      tmp_i_mem_op2,
      tmp_i_mem_nocmt,
      tmp_i_mem_skipcmt,
      tmp_i_mem_memaction
    } <= 0;

    // o_mem_memoryed_req    <= 0;
    i_ena                 <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_i_mem_executed_req    <= i_mem_executed_req;
      tmp_i_mem_pc              <= i_mem_pc;
      tmp_i_mem_inst            <= i_mem_inst;
      tmp_i_mem_addr            <= i_mem_addr; 
      tmp_i_mem_ren             <= i_mem_ren;
      tmp_i_mem_funct3          <= i_mem_funct3;
      tmp_i_mem_wen             <= i_mem_wen;
      tmp_i_mem_wdata           <= i_mem_wdata;
      tmp_i_mem_op1             <= i_mem_op1;
      tmp_i_mem_op2             <= i_mem_op2;
      tmp_i_mem_rd              <= i_mem_rd;
      tmp_i_mem_rd_wen          <= i_mem_rd_wen;
      tmp_i_mem_rd_wdata        <= i_mem_rd_wdata;
      tmp_i_mem_nocmt           <= i_mem_nocmt;
      tmp_i_mem_skipcmt         <= i_mem_skipcmt;
      tmp_i_mem_memaction       <= i_mem_memaction;

      // o_mem_memoryed_req        <= 1;
      i_ena                     <= 1;
    end
    else if (i_mem_memoryed_ack & o_mem_memoryed_req) begin
      // o_mem_memoryed_req        <= 0;
      i_ena                     <= 0;
    end
  end
end

assign o_mem_pc           = i_disable ? 0 : tmp_i_mem_pc;
assign o_mem_inst         = i_disable ? 0 : tmp_i_mem_inst;
assign o_mem_rd           = i_disable ? 0 : tmp_i_mem_rd;
assign o_mem_rd_wen       = i_disable ? 0 : tmp_i_mem_rd_wen;
// rd_wdata
always @(*) begin
  if (i_disable) begin
    o_mem_rd_wdata = 0;
  end
  else begin
    case (tmp_i_mem_memaction)
      `MEM_ACTION_LOAD: begin
        case (tmp_i_mem_funct3)
          `FUNCT3_LB    : o_mem_rd_wdata = {{57{mem_rdata[7]}}, mem_rdata[6:0]} ;
          `FUNCT3_LH    : o_mem_rd_wdata = {{49{mem_rdata[15]}}, mem_rdata[14:0]};
          `FUNCT3_LW    : o_mem_rd_wdata = {{33{mem_rdata[31]}}, mem_rdata[30:0]};
          `FUNCT3_LD    : o_mem_rd_wdata = mem_rdata[63:0];
          `FUNCT3_LBU   : o_mem_rd_wdata = {56'd0, mem_rdata[7:0]};
          `FUNCT3_LHU   : o_mem_rd_wdata = {48'd0, mem_rdata[15:0]};
          `FUNCT3_LWU   : o_mem_rd_wdata = {32'd0, mem_rdata[31:0]};
          default       : o_mem_rd_wdata = 0;
        endcase
      end
      default: begin
        o_mem_rd_wdata = tmp_i_mem_rd_wdata;
      end
    endcase
  end
end

// rd_wdata
always @(*) begin
  if (i_mem_memaction == `MEM_ACTION_STORE) begin
    case (i_mem_funct3)
      `FUNCT3_SB    : mem_wdata = {56'd0, i_mem_op2[7:0]};
      `FUNCT3_SH    : mem_wdata = {48'd0, i_mem_op2[15:0]};
      `FUNCT3_SW    : mem_wdata = {32'd0, i_mem_op2[31:0]};
      `FUNCT3_SD    : mem_wdata = i_mem_op2[63:0];
      default       : mem_wdata = 0;
    endcase
  end
  else begin
    mem_wdata = 0;
  end
end

assign o_mem_nocmt        = i_disable ? 0 : tmp_i_mem_nocmt;
assign o_mem_skipcmt      = i_disable ? 0 : tmp_i_mem_skipcmt;

wire [63:0] mem_rdata;
reg  [63:0] mem_wdata;

memU MemU(
  .i_ena                      (i_ena                      ),
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_memaction                (i_mem_memaction        ),
  .i_addr                     (i_mem_addr             ),
  .i_ren                      (i_mem_ren              ),
  .i_funct3                   (i_mem_funct3           ),
  .i_wen                      (i_mem_wen              ),
  .i_wdata                    (mem_wdata              ),
  .o_rdata                    (mem_rdata                  ),
  .i_executed_req             (i_mem_executed_req         ),
  .o_memoryed_req             (o_mem_memoryed_req         ),
  .i_memoryed_ack             (i_mem_memoryed_ack         ),

  .o_dcache_req               (o_dcache_req               ),
  .o_dcache_addr              (o_dcache_addr              ),
  .o_dcache_op                (o_dcache_op                ),
  .o_dcache_bytes             (o_dcache_bytes             ),
  .o_dcache_wdata             (o_dcache_wdata             ),
  .i_dcache_ack               (i_dcache_ack               ),
  .i_dcache_rdata             (i_dcache_rdata             )
);

endmodule
