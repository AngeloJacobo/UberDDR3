// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VMAIN__SYMS_H_
#define VERILATED_VMAIN__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "Vmain.h"

// INCLUDE MODULE CLASSES
#include "Vmain___024root.h"

// DPI TYPES for DPI Export callbacks (Internal use)

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES)Vmain__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    Vmain* const __Vm_modelp;
    bool __Vm_activity = false;  ///< Used by trace routines to determine change occurred
    uint32_t __Vm_baseCode = 0;  ///< Used by trace routines when tracing multiple models
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    Vmain___024root                TOP;

    // SCOPE NAMES
    VerilatedScope __Vscope_main__swic__thecpu__core;
    VerilatedScope __Vscope_main__swic__thecpu__core__instruction_decoder;

    // CONSTRUCTORS
    Vmain__Syms(VerilatedContext* contextp, const char* namep, Vmain* modelp);
    ~Vmain__Syms();

    // METHODS
    const char* name() { return TOP.name(); }
};

#endif  // guard
