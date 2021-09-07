
// ZhengpuShi

// Fetch Unit

`include "defines.v"

module ifU(
  input   wire                clk,
  input   wire                rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
	input                       axi_ready_i,
  input         [63:0]        axi_data_read_i,
  input         [1:0]         axi_resp_i,
	output reg                  axi_valid_o,
  output reg    [63:0]        axi_addr_o,
  output        [1:0]         axi_size_o,
  
  /////////////////////////////////////////////////////////
  input   wire                pc_jmp_i,
  input   wire  [`BUS_64]     pc_jmpaddr_i,
  output  reg   [`BUS_64]     pc_old_o,
  output  reg   [`BUS_64]     pc_o,
  output  wire  [`BUS_64]     pc_pred_o,    // 预测的下一个PC
  output  reg   [`BUS_32]     inst_o,
  output                      fetched_pulse     // 取到指令的通知
);

assign axi_valid_o = 1'b1;

wire handshake_done = axi_valid_o & axi_ready_i;

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    // pc_old    <= 0;
    pc_o                      <= 0;
    axi_addr_o                <= `PC_START;
  end
  else begin
    if (handshake_done) begin
      inst_o                  <= axi_data_read_i[31:0];
      pc_o                    <= axi_addr_o;
      axi_addr_o              <= axi_addr_o + 4;
    end
  end
end

assign fetched_pulse = handshake_done;

assign pc_pred_o = pc_o + 4;
assign axi_size_o = `SIZE_W;

endmodule
