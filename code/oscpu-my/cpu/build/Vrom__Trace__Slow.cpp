// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals
#include "verilated_vcd_c.h"
#include "Vrom__Syms.h"


//======================

void Vrom::trace(VerilatedVcdC* tfp, int, int) {
    tfp->spTrace()->addInitCb(&traceInit, __VlSymsp);
    traceRegister(tfp->spTrace());
}

void Vrom::traceInit(void* userp, VerilatedVcd* tracep, uint32_t code) {
    // Callback from tracep->open()
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {
        VL_FATAL_MT(__FILE__, __LINE__, __FILE__,
                        "Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.");
    }
    vlSymsp->__Vm_baseCode = code;
    tracep->module(vlSymsp->name());
    tracep->scopeEscape(' ');
    Vrom::traceInitTop(vlSymsp, tracep);
    tracep->scopeEscape('.');
}

//======================


void Vrom::traceInitTop(void* userp, VerilatedVcd* tracep) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlTOPp->traceInitSub0(userp, tracep);
    }
}

void Vrom::traceInitSub0(void* userp, VerilatedVcd* tracep) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    const int c = vlSymsp->__Vm_baseCode;
    if (false && tracep && c) {}  // Prevent unused
    // Body
    {
        tracep->declBit(c+1,"rst", false,-1);
        tracep->declBit(c+2,"clk", false,-1);
        tracep->declBus(c+3,"raddr_i", false,-1, 11,0);
        tracep->declBus(c+4,"rdata_o", false,-1, 31,0);
        tracep->declBit(c+5,"we_i", false,-1);
        tracep->declBus(c+6,"waddr_i", false,-1, 11,0);
        tracep->declBus(c+7,"wdata_i", false,-1, 31,0);
        tracep->declBit(c+8,"inited_i", false,-1);
        tracep->declBit(c+9,"inited_o", false,-1);
        tracep->declBit(c+1,"rom rst", false,-1);
        tracep->declBit(c+2,"rom clk", false,-1);
        tracep->declBus(c+3,"rom raddr_i", false,-1, 11,0);
        tracep->declBus(c+4,"rom rdata_o", false,-1, 31,0);
        tracep->declBit(c+5,"rom we_i", false,-1);
        tracep->declBus(c+6,"rom waddr_i", false,-1, 11,0);
        tracep->declBus(c+7,"rom wdata_i", false,-1, 31,0);
        tracep->declBit(c+8,"rom inited_i", false,-1);
        tracep->declBit(c+9,"rom inited_o", false,-1);
    }
}

void Vrom::traceRegister(VerilatedVcd* tracep) {
    // Body
    {
        tracep->addFullCb(&traceFullTop0, __VlSymsp);
        tracep->addChgCb(&traceChgTop0, __VlSymsp);
        tracep->addCleanupCb(&traceCleanup, __VlSymsp);
    }
}

void Vrom::traceFullTop0(void* userp, VerilatedVcd* tracep) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    {
        vlTOPp->traceFullSub0(userp, tracep);
    }
}

void Vrom::traceFullSub0(void* userp, VerilatedVcd* tracep) {
    Vrom__Syms* __restrict vlSymsp = static_cast<Vrom__Syms*>(userp);
    Vrom* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    vluint32_t* const oldp = tracep->oldp(vlSymsp->__Vm_baseCode);
    if (false && oldp) {}  // Prevent unused
    // Body
    {
        tracep->fullBit(oldp+1,(vlTOPp->rst));
        tracep->fullBit(oldp+2,(vlTOPp->clk));
        tracep->fullSData(oldp+3,(vlTOPp->raddr_i),12);
        tracep->fullIData(oldp+4,(vlTOPp->rdata_o),32);
        tracep->fullBit(oldp+5,(vlTOPp->we_i));
        tracep->fullSData(oldp+6,(vlTOPp->waddr_i),12);
        tracep->fullIData(oldp+7,(vlTOPp->wdata_i),32);
        tracep->fullBit(oldp+8,(vlTOPp->inited_i));
        tracep->fullBit(oldp+9,(vlTOPp->inited_o));
    }
}
