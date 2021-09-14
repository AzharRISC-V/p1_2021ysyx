
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

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    o_bus_addr              <= `PC_START;
    o_pc                    <= 0;
    o_pc_pred               <= 0;
    o_nocmt                 <= 0;
    o_fetched               <= 0;
  end
  else begin
    if (handshake_done) begin
      // 如果是冲刷流水线，则放弃这条指令1次
      if (drop_inst_once) begin
        drop_inst_once          <= 0;
        flush_en                <= 0;
        o_fetched               <= 0;
      end
      else begin
        o_bus_addr              <= o_bus_addr + 4;
        o_pc                    <= o_bus_addr;
        o_pc_pred               <= o_bus_addr + 4;
        o_inst                  <= i_bus_rdata[31:0];
        o_nocmt                 <= 0;
        o_fetched               <= 1;
      end
    end
    // 冲刷流水线：将nop指令放入总线，并且不提交这条指令到difftest
    else if (flush_en) begin
      flush_en                <= 0;
      o_bus_addr              <= i_pc_jmpaddr;
      o_pc                    <= i_pc_jmpaddr;
      o_pc_pred               <= i_pc_jmpaddr + 4;
      o_inst                  <= `INST_NOP;
      o_nocmt                 <= 1;
      o_fetched               <= 1;
    end
    else begin
      //o_pc                    <= 0;
      //o_pc_pred               <= 0;
      o_inst                  <= 0;
      o_nocmt                 <= 0;
      o_fetched               <= 0;
    end
  end
end

// 顺序计算得出的pc值，用于同jump时的地址对比，若不同则需要冲刷流水线
// assign o_axi_size = `SIZE_D;// `SIZE_W;

// 是否冲刷流水线
reg      flush_en;

// 是否丢弃一条指令
reg drop_inst_once;

always @(posedge clk) begin
  if (rst) begin
    flush_en            <= 0;
    drop_inst_once      <= 0;
  end
  else begin
    if (i_pc_jmp & (o_pc_pred != i_pc_jmpaddr)) begin
      flush_en          <= 1;
      drop_inst_once    <= 1;
    end
  end
end

endmodule
