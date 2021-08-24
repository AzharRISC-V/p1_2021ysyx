// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef VERILATED_VROM_H_
#define VERILATED_VROM_H_  // guard

#include "verilated_heavy.h"

//==========

class Vrom__Syms;
class Vrom_VerilatedVcd;


//----------

VL_MODULE(Vrom) {
  public:

    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(rst,0,0);
    VL_IN8(clk,0,0);
    VL_IN8(we_i,0,0);
    VL_IN8(inited_i,0,0);
    VL_OUT8(inited_o,0,0);
    VL_IN16(raddr_i,11,0);
    VL_IN16(waddr_i,11,0);
    VL_OUT(rdata_o,31,0);
    VL_IN(wdata_i,31,0);

    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    VlUnpacked<IData/*31:0*/, 4096> rom__DOT__mem;

    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk;
    CData/*0:0*/ __Vclklast__TOP__rst;
    VlUnpacked<CData/*0:0*/, 1> __Vm_traceActivity;

    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    Vrom__Syms* __VlSymsp;  // Symbol table

    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vrom);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// If contextp is null, then the model will use the default global context
    /// If name is "", then makes a wrapper with a
    /// single model invisible with respect to DPI scope names.
    Vrom(VerilatedContext* contextp, const char* name = "TOP");
    Vrom(const char* name = "TOP")
      : Vrom(nullptr, name) {}
    /// Destroy the model; called (often implicitly) by application code
    ~Vrom();
    /// Trace signals in the model; called by application code
    void trace(VerilatedVcdC* tfp, int levels, int options = 0);

    // API METHODS
    /// Return current simulation context for this model.
    /// Used to get to e.g. simulation time via contextp()->time()
    VerilatedContext* contextp();
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();

    // INTERNAL METHODS
    static void _eval_initial_loop(Vrom__Syms* __restrict vlSymsp);
    void __Vconfigure(Vrom__Syms* symsp, bool first);
  private:
    static QData _change_request(Vrom__Syms* __restrict vlSymsp);
    static QData _change_request_1(Vrom__Syms* __restrict vlSymsp);
    static void _ctor_var_reset(Vrom* self) VL_ATTR_COLD;
  public:
    static void _eval(Vrom__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(Vrom__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(Vrom__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__1(Vrom__Syms* __restrict vlSymsp);
    static void _settle__TOP__2(Vrom__Syms* __restrict vlSymsp);
  private:
    static void traceChgSub0(void* userp, VerilatedVcd* tracep);
    static void traceChgTop0(void* userp, VerilatedVcd* tracep);
    static void traceCleanup(void* userp, VerilatedVcd* /*unused*/);
    static void traceFullSub0(void* userp, VerilatedVcd* tracep) VL_ATTR_COLD;
    static void traceFullTop0(void* userp, VerilatedVcd* tracep) VL_ATTR_COLD;
    static void traceInitSub0(void* userp, VerilatedVcd* tracep) VL_ATTR_COLD;
    static void traceInitTop(void* userp, VerilatedVcd* tracep) VL_ATTR_COLD;
    void traceRegister(VerilatedVcd* tracep) VL_ATTR_COLD;
    static void traceInit(void* userp, VerilatedVcd* tracep, uint32_t code) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
