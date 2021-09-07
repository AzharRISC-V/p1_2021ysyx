
// ZhengpuShi

// Fetch Interface

`include "defines.v"

module if_stage(
  input   wire                clk,
  input   wire                rst,
  output reg                  if_fetched_req_o,
  input  reg                  if_fetched_ack_i,

  ///////////////////////////////////////////////
  // AXI interface for Fetch
	input                       if_axi_ready_i,
  input         [63:0]        if_axi_data_read_i,
  input         [1:0]         if_axi_resp_i,
	output reg                  if_axi_valid_o,
  output reg    [63:0]        if_axi_addr_o,
  output        [1:0]         if_axi_size_o,
  
  ///////////////////////////////////////////////
  input   wire                if_pc_jmp_i,
  input   wire  [`BUS_64]     if_pc_jmpaddr_i,
  output  reg   [`BUS_64]     if_pc_old_o,
  output  reg   [`BUS_64]     if_pc_o,
  output  wire  [`BUS_64]     if_pc_pred_o,    // 预测的下一个PC
  output  reg   [`BUS_32]     if_inst_o
);


wire fetched_pulse;

ifU IfU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.axi_ready_i                (if_axi_ready_i             ),
  .axi_data_read_i            (if_axi_data_read_i         ),
  .axi_resp_i                 (if_axi_resp_i              ),
	.axi_valid_o                (if_axi_valid_o             ),
  .axi_addr_o                 (if_axi_addr_o              ),
  .axi_size_o                 (if_axi_size_o              ),
  .pc_jmp_i                   (if_pc_jmp_i                ),
  .pc_jmpaddr_i               (if_pc_jmpaddr_i            ),
  .pc_old_o                   (if_pc_old_o                ),
  .pc_o                       (if_pc_o                    ),
  .pc_pred_o                  (if_pc_pred_o               ),
  .inst_o                     (if_inst_o                  ),
  .fetched_pulse              (fetched_pulse              )
);

always @( posedge clk ) begin
  if (rst) begin
    if_fetched_req_o          <= 0;
  end
  else begin
    if (fetched_pulse) begin
      if_fetched_req_o        <= 1;
    end
    else if (if_fetched_ack_i) begin
      if_fetched_req_o        <= 0; 
    end
  end
end

endmodule
