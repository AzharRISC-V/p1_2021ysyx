// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef VERILATED_VRVCPU_H_
#define VERILATED_VRVCPU_H_  // guard

#include "verilated_heavy.h"

//==========

class Vrvcpu__Syms;
class Vrvcpu_VerilatedVcd;


//----------

VL_MODULE(Vrvcpu) {
  public:

    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clk,0,0);
    VL_IN8(rst,0,0);
    VL_OUT8(inst_ena,0,0);
    VL_IN(inst,31,0);
    VL_OUT64(inst_addr,63,0);

    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    CData/*4:0*/ rvcpu__DOT__rd_w_addr;
    CData/*4:0*/ rvcpu__DOT__inst_type;
    CData/*7:0*/ rvcpu__DOT__inst_opcode;
    CData/*0:0*/ rvcpu__DOT__Id_stage__DOT__inst_addi;
    QData/*63:0*/ rvcpu__DOT__rd_data;
    QData/*63:0*/ rvcpu__DOT__If_stage__DOT__pc;
    VlUnpacked<QData/*63:0*/, 32> rvcpu__DOT__Regfile__DOT__regs;

    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk;
    VlUnpacked<CData/*0:0*/, 3> __Vm_traceActivity;

    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    Vrvcpu__Syms* __VlSymsp;  // Symbol table

    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vrvcpu);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// If contextp is null, then the model will use the default global context
    /// If name is "", then makes a wrapper with a
    /// single model invisible with respect to DPI scope names.
    Vrvcpu(VerilatedContext* contextp, const char* name = "TOP");
    Vrvcpu(const char* name = "TOP")
      : Vrvcpu(nullptr, name) {}
    /// Destroy the model; called (often implicitly) by application code
    ~Vrvcpu();
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
    static void _eval_initial_loop(Vrvcpu__Syms* __restrict vlSymsp);
    void __Vconfigure(Vrvcpu__Syms* symsp, bool first);
  private:
    static QData _change_request(Vrvcpu__Syms* __restrict vlSymsp);
    static QData _change_request_1(Vrvcpu__Syms* __restrict vlSymsp);
  public:
    static void _combo__TOP__2(Vrvcpu__Syms* __restrict vlSymsp);
    static void _combo__TOP__4(Vrvcpu__Syms* __restrict vlSymsp);
  private:
    static void _ctor_var_reset(Vrvcpu* self) VL_ATTR_COLD;
  public:
    static void _eval(Vrvcpu__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(Vrvcpu__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(Vrvcpu__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__3(Vrvcpu__Syms* __restrict vlSymsp);
    static void _settle__TOP__1(Vrvcpu__Syms* __restrict vlSymsp) VL_ATTR_COLD;
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
