
// ZhengpuShi

// Fetch Interface

`include "defines.v"

module ysyx_210544_if_stage(
  input   wire                clk,
  input   wire                rst,
  input                       i_if_writebacked_req,
  output  wire                o_if_fetched_req,

  ///////////////////////////////////////////////
  // AXI interface for Fetch
  input                       i_if_bus_ack,
  input         [`YSYX210544_BUS_32]     i_if_bus_rdata,
  output                      o_if_bus_req,
  output        [`YSYX210544_BUS_64]     o_if_bus_addr,
  
  ///////////////////////////////////////////////
  input   wire                i_if_pc_jmp,
  input   wire  [`YSYX210544_BUS_64]     i_if_pc_jmpaddr,
  output  wire  [`YSYX210544_BUS_64]     o_if_pc,
  output  wire  [`YSYX210544_BUS_32]     o_if_inst
);

ysyx_210544_ifU IfU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_bus_ack                  (i_if_bus_ack               ),
  .i_bus_rdata                (i_if_bus_rdata             ),
  .o_bus_req                  (o_if_bus_req               ),
  .o_bus_addr                 (o_if_bus_addr              ),
  .i_writebacked_req          (i_if_writebacked_req       ),
  .i_pc_jmp                   (i_if_pc_jmp                ),
  .i_pc_jmpaddr               (i_if_pc_jmpaddr            ),
  .o_pc                       (o_if_pc                    ),
  .o_inst                     (o_if_inst                  ),
  .o_fetched                  (o_if_fetched_req           )
);

endmodule
