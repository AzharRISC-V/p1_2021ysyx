
// ZhengpuShi

`include "defines.v"


module ysyx_210544_mem_mmio(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,
  input   wire                ren,
  input   wire                wen,
  input   wire [`YSYX210544_BUS_64]      addr,
  input   wire [`YSYX210544_BUS_64]      wdata,
  output  reg  [`YSYX210544_BUS_64]      rdata,
  output  wire                o_clint_mtime_overflow
);

// rtc设备
wire  [`YSYX210544_BUS_64]               rtc_rdata;
wire  [`YSYX210544_BUS_64]               i_clint_rdata;



ysyx_210544_rtc Rtc(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (ren & (addr == `YSYX210544_DEV_RTC)),
  .rdata              (rtc_rdata        )
);

// CLINT (Core Local Interrupt Controller)
ysyx_210544_clint Clint(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_clint_addr               (addr                       ),
  .i_clint_ren                (ren                        ),
  .o_clint_rdata              (i_clint_rdata              ),
  .i_clint_wen                (wen                        ),
  .i_clint_wdata              (wdata                      ),
  .o_clint_mtime_overflow     (o_clint_mtime_overflow     )
);

// Custom MMIO area
reg   [`YSYX210544_BUS_64]               custom_regs[0:15];

/*
---------original info-----------------
DESIGNED BY ZHENGPU SHI
LAST UPDATE TIME : 2021/10/23 15:12:50
AT NUAA/CS/ROOM 415
---------binary data-------------------
44 45 53 49 47 4E 45 44 
20 42 59 20 5A 48 45 4E 
47 50 55 20 53 48 49 0A 
4C 41 53 54 20 55 50 44 
41 54 45 20 54 49 4D 45 
20 3A 20 32 30 32 31 2F 
31 30 2F 32 33 20 31 35 
3A 31 32 3A 35 30 0A 41 
54 20 4E 55 41 41 2F 43 
53 2F 52 4F 4F 4D 20 34 
31 35 0A 00 00 00 00 00
---------verilog code-------------------
64'h44_45_4E_47_49_53_45_44; 
64'h4E_45_48_5A_20_59_42_20; 
64'h0A_49_48_53_20_55_50_47; 
64'h44_50_55_20_54_53_41_4C; 
64'h45_4D_49_54_20_45_54_41; 
64'h2F_31_32_30_32_20_3A_20; 
64'h35_31_20_33_32_2F_30_31; 
64'h41_0A_30_35_3A_32_31_3A; 
64'h43_2F_41_41_55_4E_20_54; 
64'h34_20_4D_4F_4F_52_2F_53; 
64'h00_00_00_00_00_0A_35_31;
--------usage --------------------------
1. get data from 0x02008000,+1,+2,..., get 64bit (8byte) every time.
2. show byte from lsb, if find \00, then stop
3. we should print the original info.
*/
always @(posedge clk) begin
  if (rst) begin
    custom_regs[0] <= 64'h44_45_4E_47_49_53_45_44;
    custom_regs[1] <= 64'h4E_45_48_5A_20_59_42_20;
    custom_regs[2] <= 64'h0A_49_48_53_20_55_50_47;
    custom_regs[3] <= 64'h44_50_55_20_54_53_41_4C;
    custom_regs[4] <= 64'h45_4D_49_54_20_45_54_41;
    custom_regs[5] <= 64'h2F_31_32_30_32_20_3A_20;
    custom_regs[6] <= 64'h35_31_20_33_32_2F_30_31;
    custom_regs[7] <= 64'h41_0A_30_35_3A_32_31_3A;
    custom_regs[8] <= 64'h43_2F_41_41_55_4E_20_54;
    custom_regs[9] <= 64'h34_20_4D_4F_4F_52_2F_53;
    custom_regs[10] <= 64'h00_00_00_00_00_0A_35_31;
    custom_regs[11] <= 0;
    custom_regs[12] <= 0;
    custom_regs[13] <= 0;
    custom_regs[14] <= 0;
    custom_regs[15] <= 0;
  end
end

always @(posedge clk) begin
    if (rst) begin
        req   <= 0;
        rdata <= 0;
    end
    else begin
        // set request
        if (start) begin
            if (ren) begin
                if (addr == `YSYX210544_DEV_RTC)             rdata <= rtc_rdata;
                else if (addr == `YSYX210544_DEV_MTIME)      rdata <= i_clint_rdata;
                else if (addr == `YSYX210544_DEV_MTIMECMP)   rdata <= i_clint_rdata;
                else if ((addr & `YSYX210544_DEV_CUSTOM_MASK) == `YSYX210544_DEV_CUSTOM) begin
                  rdata <= custom_regs[addr[3:0]];
                end
                req <= 1;
            end
            else begin
                req <= 1;
            end
        end
        // clear request
        else if (ack) begin
            req   <= 0;
            rdata <= 0;
        end
    end
end

endmodule
