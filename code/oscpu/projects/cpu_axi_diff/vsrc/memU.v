
// ZhengpuShi

// Memory Unit, 组合逻辑电路

`include "defines.v";
`include "mem_access.v"

module memU(
  input   wire                i_ena,
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_addr,
  input   wire                i_ren,
  input   wire  [`BUS_FUNCT3] i_funct3,
  input   wire                i_wen,
  input   wire  [`BUS_64]     i_wdata,
  output  wire  [`BUS_64]     o_rdata
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

// 访问内存，将1字节访问转换为8字节对齐的一次或两次访问
// mem_access Mem_access(
//   .i_ena                      (i_ena                      ),
//   .clk                        (clk                        ),
//   .i_ren                      (i_ren & is_mem             ),
//   .i_addr                     (addr_0                     ),
//   .i_funct3                   (funct3_0                   ),
//   .o_rdata                    (mem_rdata                  ),
//   .i_wdata                    (i_wdata                    ),
//   .i_wen                      (i_wen & is_mem             )
// );

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


assign o_rdata = (!en) ? 0 : (is_mem ? mem_rdata : dev_rdata);

endmodule
