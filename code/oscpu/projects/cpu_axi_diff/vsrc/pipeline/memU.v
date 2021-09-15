
// ZhengpuShi

// Memory Unit, 组合逻辑电路

`include "../defines.v";
`include "mem_access.v"

module memU(
  input   wire                i_ena,
  input   wire                clk,
  input   wire  [1:0]         i_memaction,
  input   wire                rst,
  input   wire  [`BUS_64]     i_addr,
  input   wire                i_ren,
  input   wire  [`BUS_FUNCT3] i_funct3,
  input   wire                i_wen,
  input   wire  [`BUS_64]     i_wdata,
  output  wire  [`BUS_64]     o_rdata,
  input   reg                 i_executed_req,   // execute是否活动
  output  reg                 o_memoryed_req,   // 发出 已访存就绪 的请求
  input   reg                 i_memoryed_ack,

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


wire i_disable = !i_ena;

// If access memory?
wire  is_mem;
// If access device?
wire  is_device;

assign is_mem = i_disable ? 0 : (i_addr & ~(64'hFFFFFFF)) == 64'h80000000;
assign is_device = i_disable ? 0 : (i_addr & ~(64'hFFF)) == 64'h20000000;

wire            en;
wire  [`BUS_64] addr_0;
wire  [2 : 0]   funct3_0;

assign en        = i_disable ? 0 : i_ren | i_wen;
assign addr_0    = i_disable ? 0 : (!en) ? 0 : i_addr;
assign funct3_0  = i_disable ? 0 : (!en) ? 0 : i_funct3;

wire   [`BUS_64] mem_rdata;

wire mem_read_ok;

reg [2:0] dcache_bytes;
always @(*) begin
  case (i_funct3[1:0])
    2'b00   : dcache_bytes = 0; // byte
    2'b01   : dcache_bytes = 1; // half
    2'b10   : dcache_bytes = 3; // word
    2'b11   : dcache_bytes = 7; // dword
    default : dcache_bytes = 0;
  endcase
end


wire hs_dcache = o_dcache_req & i_dcache_ack;

reg wait_finish;  // 是否等待访存完毕？

always @(posedge clk) begin
  if (rst) begin
    wait_finish    <= 0;
    o_memoryed_req <= 0;
  end
  else begin
    if (i_executed_req) begin
      if (i_memaction == `MEM_ACTION_NONE) begin
        o_memoryed_req    <= 1;
      end
      else if (i_memaction == `MEM_ACTION_LOAD) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= i_ren ? `REQ_READ : `REQ_WRITE;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= dcache_bytes;
        o_dcache_wdata    <= i_ren ? 0 : i_wdata;
        wait_finish       <= 1;
      end
      else if (i_memaction == `MEM_ACTION_STORE) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= i_ren ? `REQ_READ : `REQ_WRITE;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= dcache_bytes;
        o_dcache_wdata    <= i_ren ? 0 : i_wdata;
        wait_finish       <= 1;
      end
    end
    else begin
      // 等待访存完毕
      if (wait_finish && hs_dcache) begin
        wait_finish       <= 0;
        o_dcache_req      <= 0;
        o_memoryed_req    <= 1;
      end
      // 清除req信号
      else if (i_memoryed_ack) begin
        o_memoryed_req    <= 0;
      end
    end
  end
end


// 访问外设
wire   [`BUS_64] dev_rdata;

wire  dev_read_ok;

devices Devices(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .ren                        (i_ren & is_device          ),
  .raddr                      (addr_0                     ),
  .rdata                      (dev_rdata                  ),
  .read_ok                    (dev_read_ok                )  
);


assign o_rdata = i_dcache_rdata;// is_mem ? i_dcache_rdata : dev_rdata;

endmodule
