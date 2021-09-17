
`include "defines.v"

module csrfile(
  input   wire              clk,
  input   wire              rst,

  // 读写CSR
  input                     i_csr_ren,
  input   wire  [11 : 0]    i_csr_addr,
  input                     i_csr_wen,
  input   wire  [`BUS_64]   i_csr_wdata,
  output  reg   [`BUS_64]   o_csr_rdata,
  // difftest
  output  wire  [`BUS_64]   o_csrs[0 : 7]
);


// CSR
reg [`BUS_64]   csrs[0 : 7];

// i_csr_addr translate to csr_idx
reg  [2 : 0]       csr_idx;
always @(*) begin
  if (rst) begin
    csr_idx = `CSR_IDX_NONE;
  end
  else begin
    case (i_csr_addr)
      12'h300   : csr_idx = `CSR_IDX_MSTATUS;
      12'hB00   : csr_idx = `CSR_IDX_MCYCLE;
      default   : csr_idx = `CSR_IDX_NONE;
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

// csr写入
always @(posedge clk) begin
  if (rst == 1'b1) begin
    csrs[ 0]      <= 0;
    csrs[ 1]      <= 64'h00000000_00001800;
    csrs[ 2]      <= 0;
    csrs[ 3]      <= 0;
    csrs[ 4]      <= 0;
    csrs[ 5]      <= 0;
    csrs[ 6]      <= 0;
    csrs[ 7]      <= 0;
  end
  else begin
    if (i_csr_wen) begin
      csrs[csr_idx] = i_csr_wdata;
    end
    // case (i_csr_op)
    //   `CSROP_READ_WRITE     : begin o_csr_rdata = csrs[csr_idx]; csrs[csr_idx] = i_csr_wdata; end
    //   `CSROP_READ_SET       : begin o_csr_rdata = csrs[csr_idx]; csrs[csr_idx] = csrs[csr_idx] | i_csr_wdata; end
    //   `CSROP_READ_CLEAR     : begin o_csr_rdata = csrs[csr_idx]; csrs[csr_idx] = csrs[csr_idx] & (~i_csr_wdata); end
    //   default               : begin o_csr_rdata = 0; end
    // endcase
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
    csrs[`CSR_IDX_MCYCLE] = 0;
  end
  else begin
    csrs[`CSR_IDX_MCYCLE] += 1;
  end
end


endmodule
