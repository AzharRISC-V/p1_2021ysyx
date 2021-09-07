
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
  input         [63:0]        i_if_axi_data_read,
  input         [1:0]         i_if_axi_resp,
	output reg                  o_if_axi_valid,
  output reg    [63:0]        o_if_axi_addr,
  output        [1:0]         o_if_axi_size,
  
  ///////////////////////////////////////////////
  input   wire                i_if_pc_jmp,
  input   wire  [`BUS_64]     i_if_pc_jmpaddr,
  output  reg   [`BUS_64]     o_if_pc_old,
  output  reg   [`BUS_64]     o_if_pc,
  output  wire  [`BUS_64]     o_if_pc_pred,    // 预测的下一个PC
  output  reg   [`BUS_32]     o_if_inst
);


wire fetched_pulse;

ifU IfU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_axi_ready                (i_if_axi_ready             ),
  .i_axi_data_read            (i_if_axi_data_read         ),
  .i_axi_resp                 (i_if_axi_resp              ),
	.o_axi_valid                (o_if_axi_valid             ),
  .o_axi_addr                 (o_if_axi_addr              ),
  .o_axi_size                 (o_if_axi_size              ),
  .i_pc_jmp                   (i_if_pc_jmp                ),
  .i_pc_jmpaddr               (i_if_pc_jmpaddr            ),
  .o_pc_old                   (o_if_pc_old                ),
  .o_pc                       (o_if_pc                    ),
  .o_pc_pred                  (o_if_pc_pred               ),
  .o_inst                     (o_if_inst                  ),
  .fetched_pulse              (fetched_pulse              )
);

always @( posedge clk ) begin
  if (rst) begin
    o_if_fetched_req          <= 0;
  end
  else begin
    if (fetched_pulse) begin
      o_if_fetched_req        <= 1;
    end
    else if (i_if_fetched_ack) begin
      o_if_fetched_req        <= 0; 
    end
  end
end

endmodule
