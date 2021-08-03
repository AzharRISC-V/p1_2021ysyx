module v5 (clk);
    input clk;
    always @(posedge clk) begin
        $display("I am called by v4");
    end

endmodule //v5