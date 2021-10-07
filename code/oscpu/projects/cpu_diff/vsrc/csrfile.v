
`include "defines.v"

module csrfile(
  input   wire              clk,
  input   wire              rst,

  // 读写CSR
  input   wire  [11 : 0]    csr_addr,
  // 操作码 [1:0]
  // 00    none
  // 01    read and write
  // 10    read and set
  // 11    read and clear
  input   wire  [1 : 0]     csr_op,
  input   wire  [`BUS_64]   csr_wdata,
  output  reg   [`BUS_64]   csr_rdata,
  // difftest
  output  wire  [`BUS_64]   csrs_o[0 : 7]
);


// CSR
reg [`BUS_64]   csrs[0 : 7];

// csr_addr translate to csr_idx
reg  [2 : 0]       csr_idx;
always @(*) begin
  if (rst) begin
    csr_idx = `CSR_IDX_NONE;
  end
  else begin
    case (csr_addr)
      12'h300   : csr_idx = `CSR_IDX_MSTATUS;
      12'hB00   : csr_idx = `CSR_IDX_MCYCLE;
      default   : csr_idx = `CSR_IDX_NONE;
    endcase
  end
end

// csr读写
always @(*) 
begin
  if (rst) begin
    csrs[ 0]    = 0;
    csrs[ 1]    = 64'h00000000_00001800;
    csrs[ 2]    = 0;
    csrs[ 3]    = 0;
    csrs[ 4]    = 0;
    csrs[ 5]    = 0;
    csrs[ 6]    = 0;
    csrs[ 7]    = 0;
    csr_rdata   = 0;
  end
  else begin
    case (csr_op)
      2'b01     : begin csr_rdata = csrs[csr_idx]; csrs[csr_idx] = csr_wdata; end
      2'b10     : begin csr_rdata = csrs[csr_idx]; csrs[csr_idx] = csrs[csr_idx] | csr_wdata; end
      2'b11     : begin csr_rdata = csrs[csr_idx]; csrs[csr_idx] = csrs[csr_idx] & (~csr_wdata); end
      default   : ;
    endcase
  end
end

// difftest csr_regs接口
genvar i;
generate
  for (i = 0; i < 8; i = i + 1) 
  begin: CSRS_O_GEN
    assign csrs_o[i] = csrs[i];
  end
endgenerate

// mcycle模拟
always @(posedge clk) begin
  if (rst) begin
    csrs[`CSR_IDX_MCYCLE] = 0;
  end
  else begin
    csrs[`CSR_IDX_MCYCLE] = csrs[`CSR_IDX_MCYCLE] + 1;
  end
end


endmodule
