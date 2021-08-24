// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vrom.h for the primary calling header

#include "Vrom.h"
#include "Vrom__Syms.h"

//==========

Vrom::Vrom(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModule{_vcname__}
 {
    Vrom__Syms* __restrict vlSymsp = __VlSymsp = new Vrom__Syms(_vcontextp__, this, name());
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values

    // Reset structure values
    _ctor_var_reset(this);
}

void Vrom::__Vconfigure(Vrom__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    vlSymsp->_vm_contextp__->timeunit(-9);
    vlSymsp->_vm_contextp__->timeprecision(-12);
}

Vrom::~Vrom() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = nullptr);
}

void Vrom::_eval_initial(Vrom__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrom::_eval_initial\n"); );
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__rst = vlTOPp->rst;
}

void Vrom::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrom::final\n"); );
    // Variables
    Vrom__Syms* __restrict vlSymsp = this->__VlSymsp;
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vrom::_eval_settle(Vrom__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrom::_eval_settle\n"); );
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void Vrom::_ctor_var_reset(Vrom* self) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrom::_ctor_var_reset\n"); );
    // Body
    if (false && self) {}  // Prevent unused
    self->rst = VL_RAND_RESET_I(1);
    self->clk = VL_RAND_RESET_I(1);
    self->raddr_i = VL_RAND_RESET_I(12);
    self->rdata_o = VL_RAND_RESET_I(32);
    self->we_i = VL_RAND_RESET_I(1);
    self->waddr_i = VL_RAND_RESET_I(12);
    self->wdata_i = VL_RAND_RESET_I(32);
    self->inited_i = VL_RAND_RESET_I(1);
    self->inited_o = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<4096; ++__Vi0) {
        self->rom__DOT__mem[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0=0; __Vi0<1; ++__Vi0) {
        self->__Vm_traceActivity[__Vi0] = VL_RAND_RESET_I(1);
    }
}
