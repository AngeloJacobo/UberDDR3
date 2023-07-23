// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table implementation internals

#include "Vmain__Syms.h"
#include "Vmain.h"
#include "Vmain___024root.h"

// FUNCTIONS
Vmain__Syms::~Vmain__Syms()
{
}

Vmain__Syms::Vmain__Syms(VerilatedContext* contextp, const char* namep, Vmain* modelp)
    : VerilatedSyms{contextp}
    // Setup internal state of the Syms class
    , __Vm_modelp{modelp}
    // Setup module instances
    , TOP{this, namep}
{
    // Configure time unit / time precision
    _vm_contextp__->timeunit(-12);
    _vm_contextp__->timeprecision(-12);
    // Setup each module's pointers to their submodules
    // Setup each module's pointer back to symbol table (for public functions)
    TOP.__Vconfigure(true);
    // Setup scopes
    __Vscope_main__swic__thecpu__core.configure(this, name(), "main.swic.thecpu.core", "core", 0, VerilatedScope::SCOPE_OTHER);
    __Vscope_main__swic__thecpu__core__instruction_decoder.configure(this, name(), "main.swic.thecpu.core.instruction_decoder", "instruction_decoder", 0, VerilatedScope::SCOPE_OTHER);
    // Setup export functions
    for (int __Vfinal = 0; __Vfinal < 2; ++__Vfinal) {
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"alu_ce", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"alu_sim", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"alu_sim_immv", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim_immv), false, VLVT_UINT32,VLVD_NODIR|VLVF_PUB_RW,1 ,22,0);
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"dcd_pc", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc), false, VLVT_UINT32,VLVD_NODIR|VLVF_PUB_RW,1 ,27,0);
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"op_sim", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"op_sim_immv", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim_immv), false, VLVT_UINT32,VLVD_NODIR|VLVF_PUB_RW,1 ,22,0);
        __Vscope_main__swic__thecpu__core.varInsert(__Vfinal,"op_valid", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_main__swic__thecpu__core__instruction_decoder.varInsert(__Vfinal,"o_sim", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_main__swic__thecpu__core__instruction_decoder.varInsert(__Vfinal,"o_sim_immv", &(TOP.main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim_immv), false, VLVT_UINT32,VLVD_NODIR|VLVF_PUB_RW,1 ,22,0);
    }
}
