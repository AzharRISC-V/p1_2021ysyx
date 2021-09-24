
// ZhengpuShi

`include "defines.v"

module ysyx_210544_csrfile(
  input   wire              clk,
  input   wire              rst,

  // 读写CSR
  input                     i_csr_ren,
  input   wire  [11 : 0]    i_csr_addr,
  input                     i_csr_wen,
  input   wire  [`BUS_64]   i_csr_wdata,
  output  reg   [`BUS_64]   o_csr_rdata,

  // 中断信号，直接控制csr
  output                    o_csr_clint_mstatus_mie,
  output                    o_csr_clint_mie_mtie,

  // difftest
  output  wire  [`BUS_64]   o_csrs[0 : 15]
);


// CSR
reg [`BUS_64]   csrs[0 : 15];

assign o_csr_clint_mstatus_mie = csrs[`CSR_IDX_MSTATUS][3];
assign o_csr_clint_mie_mtie = csrs[`CSR_IDX_MIE][7];

// i_csr_addr translate to csr_idx
reg  [3 : 0]       csr_idx;
always @(*) begin
  if (rst) begin
    csr_idx = `CSR_IDX_NONE;
  end
  else begin
    case (i_csr_addr)
      `CSR_ADR_MCYCLE   : csr_idx = `CSR_IDX_MCYCLE;
      `CSR_ADR_MSTATUS  : csr_idx = `CSR_IDX_MSTATUS;
      `CSR_ADR_MIE      : csr_idx = `CSR_IDX_MIE;
      `CSR_ADR_MTVEC    : csr_idx = `CSR_IDX_MTVEC;
      `CSR_ADR_MSCRATCH : csr_idx = `CSR_IDX_MSCRATCH;
      `CSR_ADR_MEPC     : csr_idx = `CSR_IDX_MEPC;
      `CSR_ADR_MCAUSE   : csr_idx = `CSR_IDX_MCAUSE;
      `CSR_ADR_MIP      : csr_idx = `CSR_IDX_MIP;
      default           : csr_idx = `CSR_IDX_NONE;
    endcase
  end
end

// csr读取
always @(*) begin
  if (rst == 1'b1) begin
    o_csr_rdata   = 0;
  end
  else if (i_csr_ren == 1'b1) begin
    o_csr_rdata = csrs[csr_idx];
  end
  else begin
    o_csr_rdata = 0;
  end
end

wire mstatus_sd = (i_csr_wdata[14:13] == 2'b11) | (i_csr_wdata[16:15] == 2'b11);

// csr写入
always @(posedge clk) begin
  if (rst == 1'b1) begin
    csrs[`CSR_IDX_MCYCLE]   <= 0;
    csrs[`CSR_IDX_MSTATUS]  <= 64'h1800;// 64'h1808;
    csrs[`CSR_IDX_MIE]      <= 0;// 64'h80;
    csrs[`CSR_IDX_MTVEC]    <= 0;
    csrs[`CSR_IDX_MEPC]     <= 0;
    csrs[`CSR_IDX_MCAUSE]   <= 0;// 64'h80000000_00000007;
    csrs[`CSR_IDX_MIP]      <= 0;// 64'h80;
  end
  else begin

    if (i_csr_wen) begin
      if (csr_idx == `CSR_IDX_MSTATUS) begin
        csrs[csr_idx] <= {mstatus_sd, i_csr_wdata[62:0]};
      end
      else begin
        csrs[csr_idx] <= i_csr_wdata;
      end
    end
  end
end

// difftest csr_regs接口
genvar i;
generate
  for (i = 0; i < 8; i = i + 1) begin
    assign o_csrs[i] = csrs[i];
  end
endgenerate

// mcycle模拟
always @(posedge clk) begin
  if (rst) begin
    csrs[`CSR_IDX_MCYCLE] <= 0;
  end
  else begin
    csrs[`CSR_IDX_MCYCLE] <= csrs[`CSR_IDX_MCYCLE] + 1;
  end
end


endmodule
