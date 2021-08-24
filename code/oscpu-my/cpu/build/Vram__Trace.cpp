// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals
#include "verilated_vcd_c.h"
#include "Vram__Syms.h"


void Vram::traceChgTop0(void* userp, VerilatedVcd* tracep) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    if (VL_UNLIKELY(!vlSymsp->__Vm_activity)) return;
    // Body
    {
        vlTOPp->traceChgSub0(userp, tracep);
    }
}

void Vram::traceChgSub0(void* userp, VerilatedVcd* tracep) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode + 1);
    if (false && oldp) {}  // Prevent unused
    // Body
    {
        tracep->chgBit(oldp+0,(vlTOPp->rst));
        tracep->chgBit(oldp+1,(vlTOPp->clk));
        tracep->chgSData(oldp+2,(vlTOPp->raddr_i),12);
        tracep->chgIData(oldp+3,(vlTOPp->rdata_o),32);
        tracep->chgSData(oldp+4,(vlTOPp->waddr_i),12);
        tracep->chgIData(oldp+5,(vlTOPp->wdata_i),32);
        tracep->chgBit(oldp+6,(vlTOPp->we_i));
    }
}

void Vram::traceCleanup(void* userp, VerilatedVcd* /*unused*/) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlSymsp->__Vm_activity = false;
        vlTOPp->__Vm_traceActivity[0U] = 0U;
    }
}
