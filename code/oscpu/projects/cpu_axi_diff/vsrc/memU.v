
// ZhengpuShi

// Memory Unit, 组合逻辑电路

`include "defines.v";
`include "mem_access.v"

module memU(
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     addr_i,
  input   wire                ren_i,
  input   wire  [2 : 0]       funct3_i,
  input   wire                wen_i,
  input   wire  [`BUS_64]     wdata_i,
  output  wire  [`BUS_64]     rdata_o
);


// If access memory?
wire  is_mem        = (addr_i & ~(64'hFFFFFFF)) == 64'h80000000;
// If access device?
wire  is_device     = (addr_i & ~(64'hFFF)) == 64'h20000000;

wire [`BUS_64] s1 = (addr_i & ~(64'hFFFFFFF));
wire [`BUS_64] s2 = (addr_i & ~(64'hFFF));

wire            en        = ren_i | wen_i;
wire  [`BUS_64] addr_0    = (!en) ? 0 : addr_i;
wire  [2 : 0]   funct3_0  = (!en) ? 0 : funct3_i;

wire   [`BUS_64] mem_rdata;

wire mem_read_ok;

// 访问内存，将1字节访问转换为8字节对齐的一次或两次访问
mem_access Mem_access(
  .clk                        (clk                        ),
  .ren_i                      (ren_i & is_mem             ),
  .addr_i                     (addr_0                     ),
  .funct3_i                   (funct3_0                   ),
  .rdata_o                    (mem_rdata                  ),
  .wdata_i                    (wdata_i                    ),
  .wen_i                      (wen_i & is_mem             )
);

wire   [`BUS_64] dev_rdata;

wire  dev_read_ok;

devices Devices(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .ren                        (ren_i & is_device          ),
  .raddr                      (addr_0                     ),
  .rdata                      (dev_rdata                  ),
  .read_ok                    (dev_read_ok                )  
);


assign rdata_o = (!en) ? 0 : (is_mem ? mem_rdata : dev_rdata);

endmodule
