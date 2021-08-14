import os

dirname = os.path.dirname(__file__)
filename = os.path.join(dirname, "532decoder.bin")

with open(filename, "wb") as file:
    for var in range(32):
        # 00000000_00000000_00000000_00000001
        # 00000000_00000000_00000000_00000010
        # ...
        # 10000000_00000000_00000000_00000000
        value = 1 << var
        result = value.to_bytes(4, byteorder = "little")
        file.write(result)

print("Finished!")
