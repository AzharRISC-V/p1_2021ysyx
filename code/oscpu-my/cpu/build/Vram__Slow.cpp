// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vram.h for the primary calling header

#include "Vram.h"
#include "Vram__Syms.h"

//==========

Vram::Vram(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModule{_vcname__}
 {
    Vram__Syms* __restrict vlSymsp = __VlSymsp = new Vram__Syms(_vcontextp__, this, name());
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values

    // Reset structure values
    _ctor_var_reset(this);
}

void Vram::__Vconfigure(Vram__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    vlSymsp->_vm_contextp__->timeunit(-9);
    vlSymsp->_vm_contextp__->timeprecision(-12);
}

Vram::~Vram() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = nullptr);
}

void Vram::_eval_initial(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_eval_initial\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__rst = vlTOPp->rst;
}

void Vram::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::final\n"); );
    // Variables
    Vram__Syms* __restrict vlSymsp = this->__VlSymsp;
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vram::_eval_settle(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_eval_settle\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void Vram::_ctor_var_reset(Vram* self) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_ctor_var_reset\n"); );
    // Body
    if (false && self) {}  // Prevent unused
    self->rst = VL_RAND_RESET_I(1);
    self->clk = VL_RAND_RESET_I(1);
    self->raddr_i = VL_RAND_RESET_I(12);
    self->rdata_o = VL_RAND_RESET_I(32);
    self->waddr_i = VL_RAND_RESET_I(12);
    self->wdata_i = VL_RAND_RESET_I(32);
    self->we_i = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<4096; ++__Vi0) {
        self->ram__DOT__mem[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        self->__Vm_traceActivity[__Vi0] = VL_RAND_RESET_I(1);
    }
}
