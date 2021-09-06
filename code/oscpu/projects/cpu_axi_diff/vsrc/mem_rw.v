// ZhengpuShi

// IF与MEM对 axi 的仲裁
module mem_rw # (
    parameter RW_DATA_WIDTH     = 64,
    parameter RW_ADDR_WIDTH     = 64,
    parameter AXI_DATA_WIDTH    = 64,
    parameter AXI_ADDR_WIDTH    = 64,
    parameter AXI_ID_WIDTH      = 4,
    parameter AXI_USER_WIDTH    = 1
)(
    input                               clock,
    input                               reset,

    // IF read, addr:64bit, data:32bit
	input                               ifr_valid_i,    // 请求数据，保持1个时钟周期
	output                              ifr_ready_o,    // 收到数据，保持1个时钟周期
    input                               ifr_rw_i,       // 0:read, 1:write
    input  [63 : 0]                     ifr_addr_i,
    output [31 : 0]                     ifr_data_o,

    // MEM read, addr:64bit, data:64bit
    input                               memr_valid_i,    // 请求数据，保持1个时钟周期
	output                              memr_ready_o,    // 收到数据，保持1个时钟周期
    input                               memr_rw_i,       // 0:read, 1:write
    input  [63 : 0]                     memr_addr_i,
    output [63 : 0]                     memr_data_o,

    // MEM write, addr:64bit, data:64bit
    input                               memw_valid_i,    // 请求数据，保持1个时钟周期
	output                              memw_ready_o,    // 收到数据，保持1个时钟周期
    input                               memw_rw_i,       // 0:read, 1:write
    input  [63 : 0]                     memw_addr_i,
    input  [63 : 0]                     memw_data_i,
    input  [63 : 0]                     memw_mask_i

);


endmodule