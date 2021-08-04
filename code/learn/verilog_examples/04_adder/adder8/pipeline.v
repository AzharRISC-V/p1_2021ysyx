// 8 位全加器 - 4 级流水线方式
module pipeline(cout,sum,ina,inb,cin,clk);
    output [7:0] sum;
    output cout;
    input [7:0] ina,inb;
    input cin,clk;
    reg [7:0] tempa,tempb,sum;
    reg tempci,firstco,secondco,thirdco,cout;
    reg [1:0] firsts,thirda,thirdb;
    reg [3:0] seconda,secondb,seconds;
    reg [5:0] firsta,firstb,thirds;

    // 输入数据缓存
    always @(posedge clk) begin
        tempa = ina; tempb = inb; tempci = cin;
    end

    always @(posedge clk) begin
        // 第一级加，第0,1位
        {firstco,firsts} = tempa[1:0] + tempb[1:0] + tempci;
        // 未参加计算的数据缓存
        firsta = tempa[7:2];
        firstb = tempb[7:2];
    end

    always @(posedge clk) begin
        // 第二级加（第2,3位）
        {secondco,seconds} = {firsta[1:0] + firstb[1:0] + firstco, firsts};
        // 剩余数据缓存
        seconda = firsta[5:2];
        secondb = firstb[5:2];
    end

    always @(posedge clk) begin
        // 第三级加（第4,5位）
        {thirdco,thirds} = {seconda[1:0] + secondb[1:0] + secondco, seconds};
        // 剩余数据缓存
        thirda = seconda[3:2];
        thirdb = secondb[5:2];
    end

    always @(posedge clk) begin
        // 第四级加（高两位相加）
        {cout,sum} = {thirda[1:0] + thirdb[1:0] + thirdco, thirds};
    end

endmodule
