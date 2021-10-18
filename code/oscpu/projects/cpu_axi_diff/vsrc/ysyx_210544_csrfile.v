
// ZhengpuShi

`include "defines.v"

module ysyx_210544_csrfile(
  input   wire              clk,
  input   wire              rst,

  // 读写CSR
  input                     i_csr_ren,
  input   wire  [11 : 0]    i_csr_addr,
  input                     i_csr_wen,
  input   wire  [`YSYX210544_BUS_64]   i_csr_wdata,
  output  reg   [`YSYX210544_BUS_64]   o_csr_rdata,

  // 中断信号，直接控制csr
  output                    o_csr_clint_mstatus_mie,
  output                    o_csr_clint_mie_mtie,

  output  reg   [`YSYX210544_BUS_64]   o_csrs_mcycle,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mstatus,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mie,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mtvec,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mscratch,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mepc,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mcause,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mip
);

wire              mstatus_sd;


// CSR
assign o_csr_clint_mstatus_mie = o_csrs_mstatus[3];
assign o_csr_clint_mie_mtie = o_csrs_mie[7];

// csr读取
always @(*) begin
  if (rst) begin
    o_csr_rdata   = 0;
  end
  else if (i_csr_ren) begin
    case (i_csr_addr)
        `YSYX210544_CSR_ADR_MCYCLE:    o_csr_rdata = o_csrs_mcycle;
        `YSYX210544_CSR_ADR_MSTATUS:   o_csr_rdata = o_csrs_mstatus;
        `YSYX210544_CSR_ADR_MIE:       o_csr_rdata = o_csrs_mie;
        `YSYX210544_CSR_ADR_MTVEC:     o_csr_rdata = o_csrs_mtvec;
        `YSYX210544_CSR_ADR_MSCRATCH:  o_csr_rdata = o_csrs_mscratch;
        `YSYX210544_CSR_ADR_MEPC:      o_csr_rdata = o_csrs_mepc;
        `YSYX210544_CSR_ADR_MCAUSE:    o_csr_rdata = o_csrs_mcause;
        `YSYX210544_CSR_ADR_MIP:       o_csr_rdata = o_csrs_mip;
        default:            o_csr_rdata = 0;
    endcase
  end
  else begin
    o_csr_rdata = 0;
  end
end

assign mstatus_sd = (i_csr_wdata[14:13] == 2'b11) | (i_csr_wdata[16:15] == 2'b11);

// csr写入
always @(posedge clk) begin
    if (rst) begin
        o_csrs_mcycle    <= 0;
        o_csrs_mstatus   <= 64'h1800;// 64'h1808;
        o_csrs_mie       <= 0;// 64'h80;
        o_csrs_mtvec     <= 0;
        o_csrs_mscratch  <= 0;
        o_csrs_mepc      <= 0;
        o_csrs_mcause    <= 0;// 64'h80000000_00000007;
        o_csrs_mip       <= 0;// 64'h80;
    end
    else begin
        o_csrs_mcycle <= o_csrs_mcycle + 1;
        if (i_csr_wen) begin
            case (i_csr_addr)
                // `YSYX210544_CSR_ADR_MCYCLE:    o_csrs_mcycle <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MSTATUS:   o_csrs_mstatus <= {mstatus_sd, i_csr_wdata[62:0]};
                `YSYX210544_CSR_ADR_MIE:       o_csrs_mie <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MTVEC:     o_csrs_mtvec <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MSCRATCH:  o_csrs_mscratch <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MEPC:      o_csrs_mepc <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MCAUSE:    o_csrs_mcause <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MIP:       o_csrs_mip <= i_csr_wdata;
                default: ;
            endcase
        end
    end
end

endmodule
