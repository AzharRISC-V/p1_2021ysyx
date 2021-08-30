
`include "defines.v"

module regfile(
  input   wire              clk,
  input   wire              rst,
  
  // 读取普通寄存器
  input   wire  [4  : 0]    rs1,
  input   wire              rs1_ren,
  input   wire  [4  : 0]    rs2,
  input   wire              rs2_ren,
  output  reg   [`BUS_64]   rs1_data,
  output  reg   [`BUS_64]   rs2_data,
 
  // 写入普通寄存器
  input   wire  [4  : 0]    rd,
  input   wire              rd_wen,
  input   wire  [`BUS_64]   rd_data,
  output  wire              sig_wb_ok,

  // difftest
  output  wire  [`BUS_64]   regs_o[0 : 31],

  // 读写CSR
  input   wire  [11 : 0]    csr_addr,
  // 操作码 [1:0]
  // 00    none
  // 01    read and write
  // 10    read and set
  // 11    read and clear
  input   wire  [1 : 0]     csr_op,
  input   wire  [`BUS_64]   csr_wdata,
  output  reg   [`BUS_64]   csr_rdata
);

// 32 registers
reg [`BUS_64]   regs[0 : 31];

// CSR
reg [`BUS_64]   csrs[0 : 7];

// CSR index in local memory
parameter CSR_IDX_NONE      = 0;
parameter CSR_IDX_MCYCLE    = 1;

// rd 写入
always @(posedge clk) 
begin
  if ( rst == 1'b1 ) 
  begin
    regs[ 0] <= `ZERO_WORD;
    regs[ 1] <= `ZERO_WORD;
    regs[ 2] <= `ZERO_WORD;
    regs[ 3] <= `ZERO_WORD;
    regs[ 4] <= `ZERO_WORD;
    regs[ 5] <= `ZERO_WORD;
    regs[ 6] <= `ZERO_WORD;
    regs[ 7] <= `ZERO_WORD;
    regs[ 8] <= `ZERO_WORD;
    regs[ 9] <= `ZERO_WORD;
    regs[10] <= `ZERO_WORD;
    regs[11] <= `ZERO_WORD;
    regs[12] <= `ZERO_WORD;
    regs[13] <= `ZERO_WORD;
    regs[14] <= `ZERO_WORD;
    regs[15] <= `ZERO_WORD;
    regs[16] <= `ZERO_WORD;
    regs[17] <= `ZERO_WORD;
    regs[18] <= `ZERO_WORD;
    regs[19] <= `ZERO_WORD;
    regs[20] <= `ZERO_WORD;
    regs[21] <= `ZERO_WORD;
    regs[22] <= `ZERO_WORD;
    regs[23] <= `ZERO_WORD;
    regs[24] <= `ZERO_WORD;
    regs[25] <= `ZERO_WORD;
    regs[26] <= `ZERO_WORD;
    regs[27] <= `ZERO_WORD;
    regs[28] <= `ZERO_WORD;
    regs[29] <= `ZERO_WORD;
    regs[30] <= `ZERO_WORD;
    regs[31] <= `ZERO_WORD;
  end
  else 
  begin
    if (rd_wen && (rd != 5'h00))
      regs[rd] <= rd_data;
  end
end

assign sig_wb_ok = (!rst) & (rd_wen) & (rd != 5'h00);

// rs1 读取
always @(*) begin
  if (rst == 1'b1)
    rs1_data = `ZERO_WORD;
  else if (rs1_ren == 1'b1)
    rs1_data = regs[rs1];
  else
    rs1_data = `ZERO_WORD;
end

// rs2 读取
always @(*) begin
  if (rst == 1'b1)
    rs2_data = `ZERO_WORD;
  else if (rs2_ren == 1'b1)
    rs2_data = regs[rs2];
  else
    rs2_data = `ZERO_WORD;
end

// difftest regs接口
genvar i;
generate
  for (i = 0; i < 32; i = i + 1) begin
    assign regs_o[i] = (rd_wen & rd == i & i != 0) ? rd_data : regs[i];
  end
endgenerate

// csr_addr translate to csr_idx
reg  [2 : 0]       csr_idx;
always @(*) begin
  if (rst) begin
    csr_idx = CSR_IDX_NONE;
  end
  else begin
    case (csr_addr)
      12'hB00   : csr_idx = CSR_IDX_MCYCLE;
      default   : csr_idx = CSR_IDX_NONE;
    endcase
  end
end

// csr读写
always @(*) 
begin
  if (rst) begin
    csrs[ 0]    = 0;
    csrs[ 1]    = 0;
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


endmodule
