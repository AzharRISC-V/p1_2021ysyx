// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vram.h for the primary calling header

#include "Vram.h"
#include "Vram__Syms.h"

//==========

VerilatedContext* Vram::contextp() {
    return __VlSymsp->_vm_contextp__;
}

void Vram::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vram::eval\n"); );
    Vram__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
#ifdef VL_DEBUG
    // Debug assertions
    _eval_debug_assertions();
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        vlSymsp->__Vm_activity = true;
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("ram.v", 10, "",
                "Verilated model didn't converge\n"
                "- See https://verilator.org/warn/DIDNOTCONVERGE");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void Vram::_eval_initial_loop(Vram__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    _eval_initial(vlSymsp);
    vlSymsp->__Vm_activity = true;
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        _eval_settle(vlSymsp);
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("ram.v", 10, "",
                "Verilated model didn't DC converge\n"
                "- See https://verilator.org/warn/DIDNOTCONVERGE");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void Vram::_sequent__TOP__1(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_sequent__TOP__1\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*0:0*/ __Vdlyvset__ram__DOT__mem__v0;
    SData/*11:0*/ __Vdlyvdim0__ram__DOT__mem__v0;
    IData/*31:0*/ __Vdlyvval__ram__DOT__mem__v0;
    // Body
    __Vdlyvset__ram__DOT__mem__v0 = 0U;
    if (((~ (IData)(vlTOPp->rst)) & (IData)(vlTOPp->we_i))) {
        __Vdlyvval__ram__DOT__mem__v0 = vlTOPp->wdata_i;
        __Vdlyvset__ram__DOT__mem__v0 = 1U;
        __Vdlyvdim0__ram__DOT__mem__v0 = vlTOPp->waddr_i;
    }
    if (__Vdlyvset__ram__DOT__mem__v0) {
        vlTOPp->ram__DOT__mem[__Vdlyvdim0__ram__DOT__mem__v0] 
            = __Vdlyvval__ram__DOT__mem__v0;
    }
}

VL_INLINE_OPT void Vram::_settle__TOP__2(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_settle__TOP__2\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->rdata_o = ((IData)(vlTOPp->rst) ? 0U : 
                       vlTOPp->ram__DOT__mem[vlTOPp->raddr_i]);
}

void Vram::_eval(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_eval\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->rst) & (~ (IData)(vlTOPp->__Vclklast__TOP__rst))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    vlTOPp->_settle__TOP__2(vlSymsp);
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__rst = vlTOPp->rst;
}

VL_INLINE_OPT QData Vram::_change_request(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_change_request\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData Vram::_change_request_1(Vram__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_change_request_1\n"); );
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void Vram::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vram::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((rst & 0xfeU))) {
        Verilated::overWidthError("rst");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((raddr_i & 0xf000U))) {
        Verilated::overWidthError("raddr_i");}
    if (VL_UNLIKELY((waddr_i & 0xf000U))) {
        Verilated::overWidthError("waddr_i");}
    if (VL_UNLIKELY((we_i & 0xfeU))) {
        Verilated::overWidthError("we_i");}
}
#endif  // VL_DEBUG
