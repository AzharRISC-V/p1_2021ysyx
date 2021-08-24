// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals
#include "verilated_vcd_c.h"
#include "Vrom__Syms.h"


void Vrom::traceChgTop0(void* userp, VerilatedVcd* tracep) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    if (VL_UNLIKELY(!vlSymsp->__Vm_activity)) return;
    // Body
    {
        vlTOPp->traceChgSub0(userp, tracep);
    }
}

void Vrom::traceChgSub0(void* userp, VerilatedVcd* tracep) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode + 1);
    if (false && oldp) {}  // Prevent unused
    // Body
    {
        tracep->chgBit(oldp+0,(vlTOPp->rst));
        tracep->chgBit(oldp+1,(vlTOPp->clk));
        tracep->chgSData(oldp+2,(vlTOPp->raddr_i),12);
        tracep->chgIData(oldp+3,(vlTOPp->rdata_o),32);
        tracep->chgBit(oldp+4,(vlTOPp->we_i));
        tracep->chgSData(oldp+5,(vlTOPp->waddr_i),12);
        tracep->chgIData(oldp+6,(vlTOPp->wdata_i),32);
        tracep->chgBit(oldp+7,(vlTOPp->inited_i));
        tracep->chgBit(oldp+8,(vlTOPp->inited_o));
    }
}

void Vrom::traceCleanup(void* userp, VerilatedVcd* /*unused*/) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlSymsp->__Vm_activity = false;
        vlTOPp->__Vm_traceActivity[0U] = 0U;
    }
}
