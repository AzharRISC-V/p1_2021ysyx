
// ZhengpuShi

// Fetch Unit

`include "../defines.v"

module ifU(
  input   wire                i_ena,
  input   wire                clk,
  input   wire                rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
	input                       i_bus_ack,
  input         [`BUS_64]     i_bus_rdata,
	output reg                  o_bus_req,
  output reg    [`BUS_64]     o_bus_addr,
  
  /////////////////////////////////////////////////////////
  input   wire                i_pc_jmp,
  input   wire  [`BUS_64]     i_pc_jmpaddr,
  output  reg   [`BUS_64]     o_pc,
  output  reg   [`BUS_64]     o_pc_pred,            // 预测的下一个PC
  output  reg   [`BUS_32]     o_inst,
  output                      o_fetched,            // 取到指令的通知
  output  reg                 o_nocmt               // 由于冲刷流水线而不提交这条指令
);


wire i_disable = !i_ena;

assign o_bus_req = 1'b1;

wire handshake_done = o_bus_req & i_bus_ack;

// 忽略下一条取指
reg           ignore_next_inst;
reg [`BUS_64] saved_pc_jmpaddr;

always @(posedge clk) begin
  if (rst) begin
    ignore_next_inst <= 0;
    saved_pc_jmpaddr <= 0;
  end
  else begin
    if (i_pc_jmp & (i_pc_jmpaddr != o_pc_pred)) begin
      ignore_next_inst <= 1;
      saved_pc_jmpaddr <= i_pc_jmpaddr;
    end
  end
end

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    o_bus_addr              <= `PC_START;
    o_pc                    <= 0;
    o_pc_pred               <= 0;
    o_fetched               <= 0;
  end
  else begin
    if (handshake_done) begin
      if (ignore_next_inst) begin
        ignore_next_inst        <= 0;
        o_bus_addr              <= saved_pc_jmpaddr;
        o_pc                    <= saved_pc_jmpaddr;
        o_pc_pred               <= saved_pc_jmpaddr + 4;
      end
      else begin
        o_bus_addr              <= o_bus_addr + 4;
        o_pc                    <= o_bus_addr;
        o_pc_pred               <= o_bus_addr + 4;
        o_inst                  <= i_bus_rdata[31:0];
        o_fetched               <= 1;
      end
    end
    else begin
      o_inst                  <= 0;
      o_fetched               <= 0;
    end
  end
end


endmodule
