// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vrvcpu.h for the primary calling header

#include "Vrvcpu.h"
#include "Vrvcpu__Syms.h"

//==========

VerilatedContext* Vrvcpu::contextp() {
    return __VlSymsp->_vm_contextp__;
}

void Vrvcpu::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vrvcpu::eval\n"); );
    Vrvcpu__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("rvcpu.v", 10, "",
                "Verilated model didn't converge\n"
                "- See https://verilator.org/warn/DIDNOTCONVERGE");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void Vrvcpu::_eval_initial_loop(Vrvcpu__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("rvcpu.v", 10, "",
                "Verilated model didn't DC converge\n"
                "- See https://verilator.org/warn/DIDNOTCONVERGE");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void Vrvcpu::_combo__TOP__2(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_combo__TOP__2\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->inst_ena = ((IData)(vlTOPp->rst) ? 0U : 1U);
    vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi = (IData)(
                                                           (0x10U 
                                                            == 
                                                            (0x703cU 
                                                             & vlTOPp->inst)));
    vlTOPp->rvcpu__DOT__inst_opcode = ((0xfeU & (IData)(vlTOPp->rvcpu__DOT__inst_opcode)) 
                                       | ((IData)(vlTOPp->rst)
                                           ? 0U : (1U 
                                                   & (IData)(vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi))));
    vlTOPp->rvcpu__DOT__inst_opcode = ((0xefU & (IData)(vlTOPp->rvcpu__DOT__inst_opcode)) 
                                       | (((IData)(vlTOPp->rst)
                                            ? 0U : 
                                           (1U & (IData)(vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi))) 
                                          << 4U));
}

VL_INLINE_OPT void Vrvcpu::_sequent__TOP__3(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_sequent__TOP__3\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*0:0*/ __Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v0;
    CData/*4:0*/ __Vdlyvdim0__rvcpu__DOT__Regfile__DOT__regs__v32;
    CData/*0:0*/ __Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v32;
    QData/*63:0*/ __Vdlyvval__rvcpu__DOT__Regfile__DOT__regs__v32;
    // Body
    __Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v0 = 0U;
    __Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v32 = 0U;
    vlTOPp->rvcpu__DOT__If_stage__DOT__pc = ((IData)(vlTOPp->rst)
                                              ? 0ULL
                                              : (4ULL 
                                                 + vlTOPp->rvcpu__DOT__If_stage__DOT__pc));
    if (vlTOPp->rst) {
        __Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v0 = 1U;
    } else if ((((IData)(vlTOPp->rst) ? 0U : (1U & 
                                              ((IData)(vlTOPp->rvcpu__DOT__inst_type) 
                                               >> 4U))) 
                & (0U != (IData)(vlTOPp->rvcpu__DOT__rd_w_addr)))) {
        __Vdlyvval__rvcpu__DOT__Regfile__DOT__regs__v32 
            = vlTOPp->rvcpu__DOT__rd_data;
        __Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v32 = 1U;
        __Vdlyvdim0__rvcpu__DOT__Regfile__DOT__regs__v32 
            = vlTOPp->rvcpu__DOT__rd_w_addr;
    }
    if (__Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v0) {
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[1U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[2U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[3U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[4U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[5U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[6U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[7U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[8U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[9U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0xaU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0xbU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0xcU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0xdU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0xeU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0xfU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x10U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x11U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x12U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x13U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x14U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x15U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x16U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x17U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x18U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x19U] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x1aU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x1bU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x1cU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x1dU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x1eU] = 0ULL;
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0x1fU] = 0ULL;
    }
    if (__Vdlyvset__rvcpu__DOT__Regfile__DOT__regs__v32) {
        vlTOPp->rvcpu__DOT__Regfile__DOT__regs[__Vdlyvdim0__rvcpu__DOT__Regfile__DOT__regs__v32] 
            = __Vdlyvval__rvcpu__DOT__Regfile__DOT__regs__v32;
    }
    vlTOPp->inst_addr = vlTOPp->rvcpu__DOT__If_stage__DOT__pc;
}

VL_INLINE_OPT void Vrvcpu::_combo__TOP__4(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_combo__TOP__4\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->rvcpu__DOT__inst_type = ((0xfU & (IData)(vlTOPp->rvcpu__DOT__inst_type)) 
                                     | (((IData)(vlTOPp->rst)
                                          ? 0U : (1U 
                                                  & (IData)(vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi))) 
                                        << 4U));
    if (vlTOPp->rst) {
        vlTOPp->rvcpu__DOT__rd_w_addr = 0U;
        vlTOPp->rvcpu__DOT__rd_data = 0ULL;
    } else {
        vlTOPp->rvcpu__DOT__rd_w_addr = ((0x10U & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                          ? (0x1fU 
                                             & (vlTOPp->inst 
                                                >> 7U))
                                          : 0U);
        vlTOPp->rvcpu__DOT__rd_data = ((0x11U == (IData)(vlTOPp->rvcpu__DOT__inst_opcode))
                                        ? (((IData)(vlTOPp->rst)
                                             ? 0ULL
                                             : ((0x10U 
                                                 & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                                 ? 
                                                ((IData)(vlTOPp->rst)
                                                  ? 0ULL
                                                  : 
                                                 (((IData)(vlTOPp->rst)
                                                    ? 0U
                                                    : 
                                                   (1U 
                                                    & ((IData)(vlTOPp->rvcpu__DOT__inst_type) 
                                                       >> 4U)))
                                                   ? 
                                                  vlTOPp->rvcpu__DOT__Regfile__DOT__regs
                                                  [
                                                  ((IData)(vlTOPp->rst)
                                                    ? 0U
                                                    : 
                                                   ((0x10U 
                                                     & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                                     ? 
                                                    (0x1fU 
                                                     & (vlTOPp->inst 
                                                        >> 0xfU))
                                                     : 0U))]
                                                   : 0ULL))
                                                 : 0ULL)) 
                                           + ((IData)(vlTOPp->rst)
                                               ? 0ULL
                                               : ((0x10U 
                                                   & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                                   ? 
                                                  ((0xfffffffffffff000ULL 
                                                    & ((- (QData)((IData)(
                                                                          (1U 
                                                                           & (vlTOPp->inst 
                                                                              >> 0x1fU))))) 
                                                       << 0xcU)) 
                                                   | (QData)((IData)(
                                                                     (0xfffU 
                                                                      & (vlTOPp->inst 
                                                                         >> 0x14U)))))
                                                   : 0ULL)))
                                        : 0ULL);
    }
}

void Vrvcpu::_eval(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_eval\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__2(vlSymsp);
    vlTOPp->__Vm_traceActivity[1U] = 1U;
    if (((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk)))) {
        vlTOPp->_sequent__TOP__3(vlSymsp);
        vlTOPp->__Vm_traceActivity[2U] = 1U;
    }
    vlTOPp->_combo__TOP__4(vlSymsp);
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
}

VL_INLINE_OPT QData Vrvcpu::_change_request(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_change_request\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData Vrvcpu::_change_request_1(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_change_request_1\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void Vrvcpu::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((rst & 0xfeU))) {
        Verilated::overWidthError("rst");}
}
#endif  // VL_DEBUG
