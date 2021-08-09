import os

dirname = os.path.dirname(os.path.abspath(__file__))

print(dirname)

with open(os.path.join(dirname, "test.bin"), "wb") as file:
    for var in range(256):
        var = str(var)              # eg: "255"
        var = int(var,base=16)      # 2*256 + 5*16 + 5 = 597 = 0x0255
        byte = var.to_bytes(2, byteorder="little")      # 0x02 0x55
        file.write(byte)

