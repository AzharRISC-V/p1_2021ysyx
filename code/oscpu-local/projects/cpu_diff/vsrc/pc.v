// /*
//     程序计数器模块

//     功能：
//     1. 根据当前PC、跳转请求等输入，得到新的PC
// */
// `include "defines.v"

// module pc(
//     input   wire                        rst,
//     input   wire                        clk,

//     input   wire    [`REG_BUS]          pc_i,       // 输入的pc
//     output  reg     [`REG_BUS]          pc_o,       // 输出的pc
// );
    
//     always @(posedge clk) begin
//         if (rst) begin
//             pc <= `REG_ZERO;
//         end
//         else begin
//             pc <= pc_i + 1;
//         end
//     end
    
// endmodule
