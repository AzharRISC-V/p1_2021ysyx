# modify to your ID. DO NOT add any trailing space!!!
ID = 210544

TOP = ysyx_$(ID)
V_FILE = $(TOP).v
RAM_FILE = ../ram/S011HD1P_X32Y2D128.v
LINT_FLAGS = -Wall -Wno-DECLFILENAME

# lint without UNUSED
lint: $(V_FILE) install-file
	verilator -DYSYXSOC --lint-only --top-module $(TOP) $(LINT_FLAGS) -Wno-UNUSED $(V_FILE)

# lint with UNUSED
lint-unused: $(V_FILE) install-file
	verilator -DYSYXSOC --lint-only --top-module $(TOP) $(LINT_FLAGS) $(V_FILE)

# install-file
install-file:
	cp ../../../../projects/soc/vsrc/ysyx_210544.v ./

.PHONY: lint lint-unused install-file
