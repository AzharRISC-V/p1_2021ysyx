
// ZhengpuShi

// Fetch Interface

`include "defines.v"

module if_stage(
  input   wire                clk,
  input   wire                rst,
  output reg                  o_if_fetched_req,
  input  reg                  i_if_fetched_ack,

  ///////////////////////////////////////////////
  // AXI interface for Fetch
	input                       i_if_axi_ready,
  input         [`BUS_64]     i_if_axi_data_read,
  input         [1:0]         i_if_axi_resp,
	output reg                  o_if_axi_valid,
  output reg    [`BUS_64]     o_if_axi_addr,
  output        [1:0]         o_if_axi_size,
  
  ///////////////////////////////////////////////
  input   wire                i_if_pc_jmp,
  input   wire  [`BUS_64]     i_if_pc_jmpaddr,
  output  reg   [`BUS_64]     o_if_pc,
  output  wire  [`BUS_64]     o_if_pc_pred,
  output  reg   [`BUS_32]     o_if_inst,
  output                      o_if_nocmt
);

// ifU IfU(
//   .i_ena                      (1                          ),
//   .clk                        (clk                        ),
//   .rst                        (rst                        ),
// 	.i_axi_ready                (i_if_axi_ready             ),
//   .i_axi_data_read            (i_if_axi_data_read         ),
//   .i_axi_resp                 (i_if_axi_resp              ),
// 	.o_axi_valid                (o_if_axi_valid             ),
//   .o_axi_addr                 (o_if_axi_addr              ),
//   .o_axi_size                 (o_if_axi_size              ),
//   .i_pc_jmp                   (i_if_pc_jmp                ),
//   .i_pc_jmpaddr               (i_if_pc_jmpaddr            ),
//   .o_pc                       (o_if_pc                    ),
//   .o_pc_pred                  (o_if_pc_pred               ),
//   .o_inst                     (o_if_inst                  ),
//   .o_fetched                  (o_if_fetched_req           ),
//   .o_nocmt                    (o_if_nocmt                 )
// );

// always @( posedge clk ) begin
//   if (rst) begin
//     o_if_fetched_req          <= 0;
//   end
//   else begin
//     if (o_fetched) begin
//       o_if_fetched_req        <= 1;
//     end
//     else if (i_if_fetched_ack) begin
//       o_if_fetched_req        <= 0; 
//     end
//   end
// end

endmodule
