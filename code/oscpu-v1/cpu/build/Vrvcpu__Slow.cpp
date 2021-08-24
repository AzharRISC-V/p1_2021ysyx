// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vrvcpu.h for the primary calling header

#include "Vrvcpu.h"
#include "Vrvcpu__Syms.h"

//==========

Vrvcpu::Vrvcpu(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModule{_vcname__}
 {
    Vrvcpu__Syms* __restrict vlSymsp = __VlSymsp = new Vrvcpu__Syms(_vcontextp__, this, name());
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values

    // Reset structure values
    _ctor_var_reset(this);
}

void Vrvcpu::__Vconfigure(Vrvcpu__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    vlSymsp->_vm_contextp__->timeunit(-9);
    vlSymsp->_vm_contextp__->timeprecision(-12);
}

Vrvcpu::~Vrvcpu() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = nullptr);
}

void Vrvcpu::_settle__TOP__1(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_settle__TOP__1\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->rvcpu__DOT__inst_opcode = (0xf1U & (IData)(vlTOPp->rvcpu__DOT__inst_opcode));
    vlTOPp->rvcpu__DOT__inst_opcode = (0x1fU & (IData)(vlTOPp->rvcpu__DOT__inst_opcode));
    vlTOPp->inst_ena = ((IData)(vlTOPp->rst) ? 0U : 1U);
    vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi = (IData)(
                                                           (0x10U 
                                                            == 
                                                            (0x703cU 
                                                             & vlTOPp->inst)));
    vlTOPp->inst_addr = vlTOPp->rvcpu__DOT__If_stage__DOT__pc;
    vlTOPp->rvcpu__DOT__inst_opcode = ((0xfeU & (IData)(vlTOPp->rvcpu__DOT__inst_opcode)) 
                                       | ((IData)(vlTOPp->rst)
                                           ? 0U : (1U 
                                                   & (IData)(vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi))));
    vlTOPp->rvcpu__DOT__inst_opcode = ((0xefU & (IData)(vlTOPp->rvcpu__DOT__inst_opcode)) 
                                       | (((IData)(vlTOPp->rst)
                                            ? 0U : 
                                           (1U & (IData)(vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi))) 
                                          << 4U));
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

void Vrvcpu::_eval_initial(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_eval_initial\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
}

void Vrvcpu::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::final\n"); );
    // Variables
    Vrvcpu__Syms* __restrict vlSymsp = this->__VlSymsp;
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vrvcpu::_eval_settle(Vrvcpu__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_eval_settle\n"); );
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__1(vlSymsp);
    vlTOPp->__Vm_traceActivity[2U] = 1U;
    vlTOPp->__Vm_traceActivity[1U] = 1U;
    vlTOPp->__Vm_traceActivity[0U] = 1U;
}

void Vrvcpu::_ctor_var_reset(Vrvcpu* self) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vrvcpu::_ctor_var_reset\n"); );
    // Body
    if (false && self) {}  // Prevent unused
    self->clk = VL_RAND_RESET_I(1);
    self->rst = VL_RAND_RESET_I(1);
    self->inst = VL_RAND_RESET_I(32);
    self->inst_addr = VL_RAND_RESET_Q(64);
    self->inst_ena = VL_RAND_RESET_I(1);
    self->rvcpu__DOT__rd_w_addr = VL_RAND_RESET_I(5);
    self->rvcpu__DOT__inst_type = VL_RAND_RESET_I(5);
    self->rvcpu__DOT__inst_opcode = VL_RAND_RESET_I(8);
    self->rvcpu__DOT__rd_data = VL_RAND_RESET_Q(64);
    self->rvcpu__DOT__If_stage__DOT__pc = VL_RAND_RESET_Q(64);
    self->rvcpu__DOT__Id_stage__DOT__inst_addi = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<32; ++__Vi0) {
        self->rvcpu__DOT__Regfile__DOT__regs[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0=0; __Vi0<3; ++__Vi0) {
        self->__Vm_traceActivity[__Vi0] = VL_RAND_RESET_I(1);
    }
}
