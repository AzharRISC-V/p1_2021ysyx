// Zhengpu Shi

`include "defines.v";
`include "mem_access.v"

module mem_stage(
  input   wire  [`BUS_64]       clk_cnt,
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,

  output  wire                  sig_memread_ok,
  output  wire                  sig_memwrite_ok,

  input   wire  [`BUS_64]       addr,
  input   wire                  ren,
  input   wire  [2 : 0]         funct3,
  output  wire  [`BUS_64]       rdata,

  input   wire                  wen,
  input   wire  [`BUS_64]       wdata
);

// If access memory?
wire  is_mem        = (addr & ~(64'hFFFFFFF)) == 64'h80000000;
// If access device?
wire  is_device     = (addr & ~(64'hFFF)) == 64'h20000000;

wire [`BUS_64] s1 = (addr & ~(64'hFFFFFFF));
wire [`BUS_64] s2 = (addr & ~(64'hFFF));

wire            en        = ren | wen;
wire  [`BUS_64] addr_0    = (!en) ? 0 : addr;
wire  [2 : 0]   funct3_0  = (!en) ? 0 : funct3;

wire   [`BUS_64] mem_rdata;

wire mem_read_ok;

// 访问内存，将1字节访问转换为8字节对齐的一次或两次访问
mem_access Mem_access(
  .clk_cnt            (clk_cnt          ),
  .clk                (clk              ),
  .ren                (ren & is_mem     ),
  .sig_memread_ok     (mem_read_ok      ),
  .sig_memwrite_ok    (sig_memwrite_ok  ),
  .addr               (addr_0           ),
  .funct3             (funct3_0         ),
  .rdata              (mem_rdata        ),
  .wdata              (wdata            ),
  .wen                (wen & is_mem     )
);

assign sig_memread_ok = (!en) ? 0 : (is_mem ? mem_read_ok : dev_read_ok);

wire   [`BUS_64] dev_rdata;

wire  dev_read_ok;

devices Devices(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (ren & is_device  ),
  .raddr              (addr_0           ),
  .rdata              (dev_rdata        ),
  .read_ok            (dev_read_ok      )  
);


assign rdata = (!en) ? 0 : (is_mem ? mem_rdata : dev_rdata);

endmodule
