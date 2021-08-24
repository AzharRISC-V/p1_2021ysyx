// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals
#include "verilated_vcd_c.h"
#include "Vrvcpu__Syms.h"


void Vrvcpu::traceChgTop0(void* userp, VerilatedVcd* tracep) {
    Vrvcpu__Syms* __restrict vlSymsp = static_cast<Vrvcpu__Syms*>(userp);
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    if (VL_UNLIKELY(!vlSymsp->__Vm_activity)) return;
    // Body
    {
        vlTOPp->traceChgSub0(userp, tracep);
    }
}

void Vrvcpu::traceChgSub0(void* userp, VerilatedVcd* tracep) {
    Vrvcpu__Syms* __restrict vlSymsp = static_cast<Vrvcpu__Syms*>(userp);
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode + 1);
    if (false && oldp) {}  // Prevent unused
    // Body
    {
        if (VL_UNLIKELY(vlTOPp->__Vm_traceActivity[1U])) {
            tracep->chgCData(oldp+0,(vlTOPp->rvcpu__DOT__rd_w_addr),5);
            tracep->chgCData(oldp+1,(vlTOPp->rvcpu__DOT__inst_type),5);
            tracep->chgCData(oldp+2,(vlTOPp->rvcpu__DOT__inst_opcode),8);
            tracep->chgBit(oldp+3,(vlTOPp->rvcpu__DOT__Id_stage__DOT__inst_addi));
        }
        if (VL_UNLIKELY(vlTOPp->__Vm_traceActivity[2U])) {
            tracep->chgQData(oldp+4,(vlTOPp->rvcpu__DOT__If_stage__DOT__pc),64);
            tracep->chgQData(oldp+6,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[0]),64);
            tracep->chgQData(oldp+8,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[1]),64);
            tracep->chgQData(oldp+10,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[2]),64);
            tracep->chgQData(oldp+12,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[3]),64);
            tracep->chgQData(oldp+14,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[4]),64);
            tracep->chgQData(oldp+16,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[5]),64);
            tracep->chgQData(oldp+18,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[6]),64);
            tracep->chgQData(oldp+20,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[7]),64);
            tracep->chgQData(oldp+22,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[8]),64);
            tracep->chgQData(oldp+24,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[9]),64);
            tracep->chgQData(oldp+26,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[10]),64);
            tracep->chgQData(oldp+28,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[11]),64);
            tracep->chgQData(oldp+30,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[12]),64);
            tracep->chgQData(oldp+32,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[13]),64);
            tracep->chgQData(oldp+34,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[14]),64);
            tracep->chgQData(oldp+36,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[15]),64);
            tracep->chgQData(oldp+38,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[16]),64);
            tracep->chgQData(oldp+40,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[17]),64);
            tracep->chgQData(oldp+42,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[18]),64);
            tracep->chgQData(oldp+44,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[19]),64);
            tracep->chgQData(oldp+46,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[20]),64);
            tracep->chgQData(oldp+48,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[21]),64);
            tracep->chgQData(oldp+50,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[22]),64);
            tracep->chgQData(oldp+52,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[23]),64);
            tracep->chgQData(oldp+54,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[24]),64);
            tracep->chgQData(oldp+56,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[25]),64);
            tracep->chgQData(oldp+58,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[26]),64);
            tracep->chgQData(oldp+60,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[27]),64);
            tracep->chgQData(oldp+62,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[28]),64);
            tracep->chgQData(oldp+64,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[29]),64);
            tracep->chgQData(oldp+66,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[30]),64);
            tracep->chgQData(oldp+68,(vlTOPp->rvcpu__DOT__Regfile__DOT__regs[31]),64);
        }
        tracep->chgBit(oldp+70,(vlTOPp->clk));
        tracep->chgBit(oldp+71,(vlTOPp->rst));
        tracep->chgIData(oldp+72,(vlTOPp->inst),32);
        tracep->chgQData(oldp+73,(vlTOPp->inst_addr),64);
        tracep->chgBit(oldp+75,(vlTOPp->inst_ena));
        tracep->chgBit(oldp+76,(((IData)(vlTOPp->rst)
                                  ? 0U : (1U & ((IData)(vlTOPp->rvcpu__DOT__inst_type) 
                                                >> 4U)))));
        tracep->chgCData(oldp+77,(((IData)(vlTOPp->rst)
                                    ? 0U : ((0x10U 
                                             & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                             ? (0x1fU 
                                                & (vlTOPp->inst 
                                                   >> 0xfU))
                                             : 0U))),5);
        tracep->chgQData(oldp+78,(((IData)(vlTOPp->rst)
                                    ? 0ULL : ((0x10U 
                                               & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                               ? ((IData)(vlTOPp->rst)
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
                                               : 0ULL))),64);
        tracep->chgQData(oldp+80,(((IData)(vlTOPp->rst)
                                    ? 0ULL : ((0x10U 
                                               & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                               ? ((0xfffffffffffff000ULL 
                                                   & ((- (QData)((IData)(
                                                                         (1U 
                                                                          & (vlTOPp->inst 
                                                                             >> 0x1fU))))) 
                                                      << 0xcU)) 
                                                  | (QData)((IData)(
                                                                    (0xfffU 
                                                                     & (vlTOPp->inst 
                                                                        >> 0x14U)))))
                                               : 0ULL))),64);
        tracep->chgQData(oldp+82,(((IData)(vlTOPp->rst)
                                    ? 0ULL : (((IData)(vlTOPp->rst)
                                                ? 0U
                                                : (1U 
                                                   & ((IData)(vlTOPp->rvcpu__DOT__inst_type) 
                                                      >> 4U)))
                                               ? vlTOPp->rvcpu__DOT__Regfile__DOT__regs
                                              [((IData)(vlTOPp->rst)
                                                 ? 0U
                                                 : 
                                                ((0x10U 
                                                  & (IData)(vlTOPp->rvcpu__DOT__inst_type))
                                                  ? 
                                                 (0x1fU 
                                                  & (vlTOPp->inst 
                                                     >> 0xfU))
                                                  : 0U))]
                                               : 0ULL))),64);
        tracep->chgQData(oldp+84,(((IData)(vlTOPp->rst)
                                    ? 0ULL : ((0x11U 
                                               == (IData)(vlTOPp->rvcpu__DOT__inst_opcode))
                                               ? (((IData)(vlTOPp->rst)
                                                    ? 0ULL
                                                    : 
                                                   ((0x10U 
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
                                                  + 
                                                  ((IData)(vlTOPp->rst)
                                                    ? 0ULL
                                                    : 
                                                   ((0x10U 
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
                                               : 0ULL))),64);
        tracep->chgCData(oldp+86,((0x7fU & vlTOPp->inst)),7);
        tracep->chgCData(oldp+87,((0x1fU & (vlTOPp->inst 
                                            >> 7U))),5);
        tracep->chgCData(oldp+88,((7U & (vlTOPp->inst 
                                         >> 0xcU))),3);
        tracep->chgCData(oldp+89,((0x1fU & (vlTOPp->inst 
                                            >> 0xfU))),5);
        tracep->chgSData(oldp+90,((0xfffU & (vlTOPp->inst 
                                             >> 0x14U))),12);
    }
}

void Vrvcpu::traceCleanup(void* userp, VerilatedVcd* /*unused*/) {
    Vrvcpu__Syms* __restrict vlSymsp = static_cast<Vrvcpu__Syms*>(userp);
    Vrvcpu* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlSymsp->__Vm_activity = false;
        vlTOPp->__Vm_traceActivity[0U] = 0U;
        vlTOPp->__Vm_traceActivity[1U] = 0U;
        vlTOPp->__Vm_traceActivity[2U] = 0U;
    }
}
