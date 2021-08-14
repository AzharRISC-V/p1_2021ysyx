
`include "tb_ram.v"

//tb_top
module tb_top;
  wire          clk;
  wire          rst;
  wire          wr_en;
  wire          rd_en;
  wire[7:0]     addr;
  wire[31:0]    data;

  ram inst_ram(
      .clk_i(clk),
      .rst_i(rst),
      .wr_en_i(wr_en),
      .rd_en_i(rd_en),
      .addr_i(addr),
      .data_io(data)
  );
  
  tb_ram inst_tb_ram(
      .clk_o(clk),
      .rst_o(rst),
      .wr_en_o(wr_en),
      .rd_en_o(rd_en),
      .addr_o(addr),
      .data_io(data)
  );

  

    // 生成vcd波形文件
    initial begin
        $dumpfile("./build/ram_wave.vcd");
        $dumpvars(0, tb_top);
        #10000 $finish;
    end

endmodule