// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals
#include "verilated_vcd_c.h"
#include "Vram__Syms.h"


//======================

void Vram::trace(VerilatedVcdC* tfp, int, int) {
    tfp->spTrace()->addInitCb(&traceInit, __VlSymsp);
    traceRegister(tfp->spTrace());
}

void Vram::traceInit(void* userp, VerilatedVcd* tracep, uint32_t code) {
    // Callback from tracep->open()
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {
        VL_FATAL_MT(__FILE__, __LINE__, __FILE__,
                        "Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.");
    }
    vlSymsp->__Vm_baseCode = code;
    tracep->module(vlSymsp->name());
    tracep->scopeEscape(' ');
    Vram::traceInitTop(vlSymsp, tracep);
    tracep->scopeEscape('.');
}

//======================


void Vram::traceInitTop(void* userp, VerilatedVcd* tracep) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlTOPp->traceInitSub0(userp, tracep);
    }
}

void Vram::traceInitSub0(void* userp, VerilatedVcd* tracep) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    const int c = vlSymsp->__Vm_baseCode;
    if (false && tracep && c) {}  // Prevent unused
    // Body
    {
        tracep->declBit(c+1,"rst", false,-1);
        tracep->declBit(c+2,"clk", false,-1);
        tracep->declBus(c+3,"raddr_i", false,-1, 11,0);
        tracep->declBus(c+4,"rdata_o", false,-1, 31,0);
        tracep->declBus(c+5,"waddr_i", false,-1, 11,0);
        tracep->declBus(c+6,"wdata_i", false,-1, 31,0);
        tracep->declBit(c+7,"we_i", false,-1);
        tracep->declBit(c+1,"ram rst", false,-1);
        tracep->declBit(c+2,"ram clk", false,-1);
        tracep->declBus(c+3,"ram raddr_i", false,-1, 11,0);
        tracep->declBus(c+4,"ram rdata_o", false,-1, 31,0);
        tracep->declBus(c+5,"ram waddr_i", false,-1, 11,0);
        tracep->declBus(c+6,"ram wdata_i", false,-1, 31,0);
        tracep->declBit(c+7,"ram we_i", false,-1);
    }
}

void Vram::traceRegister(VerilatedVcd* tracep) {
    // Body
    {
        tracep->addFullCb(&traceFullTop0, __VlSymsp);
        tracep->addChgCb(&traceChgTop0, __VlSymsp);
        tracep->addCleanupCb(&traceCleanup, __VlSymsp);
    }
}

void Vram::traceFullTop0(void* userp, VerilatedVcd* tracep) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlTOPp->traceFullSub0(userp, tracep);
    }
}

void Vram::traceFullSub0(void* userp, VerilatedVcd* tracep) {
    Vram__Syms* __restrict vlSymsp = static_cast<Vram__Syms*>(userp);
    Vram* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode);
    if (false && oldp) {}  // Prevent unused
    // Body
    {
        tracep->fullBit(oldp+1,(vlTOPp->rst));
        tracep->fullBit(oldp+2,(vlTOPp->clk));
        tracep->fullSData(oldp+3,(vlTOPp->raddr_i),12);
        tracep->fullIData(oldp+4,(vlTOPp->rdata_o),32);
        tracep->fullSData(oldp+5,(vlTOPp->waddr_i),12);
        tracep->fullIData(oldp+6,(vlTOPp->wdata_i),32);
        tracep->fullBit(oldp+7,(vlTOPp->we_i));
    }
}
