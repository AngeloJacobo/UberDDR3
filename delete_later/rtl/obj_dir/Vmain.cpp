// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vmain.h"
#include "Vmain__Syms.h"
#include "verilated_vcd_c.h"
#include "verilated_dpi.h"

//============================================================
// Constructors

Vmain::Vmain(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vmain__Syms(contextp(), _vcname__, this)}
    , i_clk{vlSymsp->TOP.i_clk}
    , i_reset{vlSymsp->TOP.i_reset}
    , i_ddr3_controller_idelayctrl_rdy{vlSymsp->TOP.i_ddr3_controller_idelayctrl_rdy}
    , o_ddr3_controller_dqs_tri_control{vlSymsp->TOP.o_ddr3_controller_dqs_tri_control}
    , o_ddr3_controller_dq_tri_control{vlSymsp->TOP.o_ddr3_controller_dq_tri_control}
    , o_ddr3_controller_toggle_dqs{vlSymsp->TOP.o_ddr3_controller_toggle_dqs}
    , o_ddr3_controller_odelay_data_cntvaluein{vlSymsp->TOP.o_ddr3_controller_odelay_data_cntvaluein}
    , o_ddr3_controller_odelay_dqs_cntvaluein{vlSymsp->TOP.o_ddr3_controller_odelay_dqs_cntvaluein}
    , o_ddr3_controller_idelay_data_cntvaluein{vlSymsp->TOP.o_ddr3_controller_idelay_data_cntvaluein}
    , o_ddr3_controller_idelay_dqs_cntvaluein{vlSymsp->TOP.o_ddr3_controller_idelay_dqs_cntvaluein}
    , o_ddr3_controller_odelay_data_ld{vlSymsp->TOP.o_ddr3_controller_odelay_data_ld}
    , o_ddr3_controller_odelay_dqs_ld{vlSymsp->TOP.o_ddr3_controller_odelay_dqs_ld}
    , o_ddr3_controller_idelay_data_ld{vlSymsp->TOP.o_ddr3_controller_idelay_data_ld}
    , o_ddr3_controller_idelay_dqs_ld{vlSymsp->TOP.o_ddr3_controller_idelay_dqs_ld}
    , o_ddr3_controller_bitslip{vlSymsp->TOP.o_ddr3_controller_bitslip}
    , o_sirefclk_word{vlSymsp->TOP.o_sirefclk_word}
    , o_sirefclk_ce{vlSymsp->TOP.o_sirefclk_ce}
    , i_fan_sda{vlSymsp->TOP.i_fan_sda}
    , i_fan_scl{vlSymsp->TOP.i_fan_scl}
    , o_fan_sda{vlSymsp->TOP.o_fan_sda}
    , o_fan_scl{vlSymsp->TOP.o_fan_scl}
    , o_fpga_pwm{vlSymsp->TOP.o_fpga_pwm}
    , o_sys_pwm{vlSymsp->TOP.o_sys_pwm}
    , i_fan_tach{vlSymsp->TOP.i_fan_tach}
    , o_emmc_clk{vlSymsp->TOP.o_emmc_clk}
    , i_emmc_ds{vlSymsp->TOP.i_emmc_ds}
    , io_emmc_cmd_tristate{vlSymsp->TOP.io_emmc_cmd_tristate}
    , o_emmc_cmd{vlSymsp->TOP.o_emmc_cmd}
    , i_emmc_cmd{vlSymsp->TOP.i_emmc_cmd}
    , io_emmc_dat_tristate{vlSymsp->TOP.io_emmc_dat_tristate}
    , o_emmc_dat{vlSymsp->TOP.o_emmc_dat}
    , i_emmc_dat{vlSymsp->TOP.i_emmc_dat}
    , i_emmc_detect{vlSymsp->TOP.i_emmc_detect}
    , i_i2c_sda{vlSymsp->TOP.i_i2c_sda}
    , i_i2c_scl{vlSymsp->TOP.i_i2c_scl}
    , o_i2c_sda{vlSymsp->TOP.o_i2c_sda}
    , o_i2c_scl{vlSymsp->TOP.o_i2c_scl}
    , o_sdcard_clk{vlSymsp->TOP.o_sdcard_clk}
    , i_sdcard_ds{vlSymsp->TOP.i_sdcard_ds}
    , io_sdcard_cmd_tristate{vlSymsp->TOP.io_sdcard_cmd_tristate}
    , o_sdcard_cmd{vlSymsp->TOP.o_sdcard_cmd}
    , i_sdcard_cmd{vlSymsp->TOP.i_sdcard_cmd}
    , io_sdcard_dat_tristate{vlSymsp->TOP.io_sdcard_dat_tristate}
    , o_sdcard_dat{vlSymsp->TOP.o_sdcard_dat}
    , i_sdcard_dat{vlSymsp->TOP.i_sdcard_dat}
    , i_sdcard_detect{vlSymsp->TOP.i_sdcard_detect}
    , cpu_sim_cyc{vlSymsp->TOP.cpu_sim_cyc}
    , cpu_sim_stb{vlSymsp->TOP.cpu_sim_stb}
    , cpu_sim_we{vlSymsp->TOP.cpu_sim_we}
    , cpu_sim_addr{vlSymsp->TOP.cpu_sim_addr}
    , cpu_sim_stall{vlSymsp->TOP.cpu_sim_stall}
    , cpu_sim_ack{vlSymsp->TOP.cpu_sim_ack}
    , cpu_prof_stb{vlSymsp->TOP.cpu_prof_stb}
    , i_cpu_reset{vlSymsp->TOP.i_cpu_reset}
    , i_clk200{vlSymsp->TOP.i_clk200}
    , i_wbu_uart_rx{vlSymsp->TOP.i_wbu_uart_rx}
    , o_wbu_uart_tx{vlSymsp->TOP.o_wbu_uart_tx}
    , o_wbu_uart_cts_n{vlSymsp->TOP.o_wbu_uart_cts_n}
    , o_gpio{vlSymsp->TOP.o_gpio}
    , i_sw{vlSymsp->TOP.i_sw}
    , i_btn{vlSymsp->TOP.i_btn}
    , o_led{vlSymsp->TOP.o_led}
    , i_gpio{vlSymsp->TOP.i_gpio}
    , i_ddr3_controller_iserdes_data{vlSymsp->TOP.i_ddr3_controller_iserdes_data}
    , o_ddr3_controller_cmd{vlSymsp->TOP.o_ddr3_controller_cmd}
    , o_ddr3_controller_data{vlSymsp->TOP.o_ddr3_controller_data}
    , cpu_sim_data{vlSymsp->TOP.cpu_sim_data}
    , cpu_sim_idata{vlSymsp->TOP.cpu_sim_idata}
    , cpu_prof_addr{vlSymsp->TOP.cpu_prof_addr}
    , cpu_prof_ticks{vlSymsp->TOP.cpu_prof_ticks}
    , i_ddr3_controller_iserdes_dqs{vlSymsp->TOP.i_ddr3_controller_iserdes_dqs}
    , i_ddr3_controller_iserdes_bitslip_reference{vlSymsp->TOP.i_ddr3_controller_iserdes_bitslip_reference}
    , o_ddr3_controller_dm{vlSymsp->TOP.o_ddr3_controller_dm}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

Vmain::Vmain(const char* _vcname__)
    : Vmain(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

Vmain::~Vmain() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void Vmain___024root___eval_debug_assertions(Vmain___024root* vlSelf);
#endif  // VL_DEBUG
void Vmain___024root___eval_static(Vmain___024root* vlSelf);
void Vmain___024root___eval_initial(Vmain___024root* vlSelf);
void Vmain___024root___eval_settle(Vmain___024root* vlSelf);
void Vmain___024root___eval(Vmain___024root* vlSelf);

void Vmain::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vmain::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    Vmain___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_activity = true;
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        Vmain___024root___eval_static(&(vlSymsp->TOP));
        Vmain___024root___eval_initial(&(vlSymsp->TOP));
        Vmain___024root___eval_settle(&(vlSymsp->TOP));
    }
    // MTask 0 start
    VL_DEBUG_IF(VL_DBG_MSGF("MTask0 starting\n"););
    Verilated::mtaskId(0);
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    Vmain___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool Vmain::eventsPending() { return false; }

uint64_t Vmain::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* Vmain::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void Vmain___024root___eval_final(Vmain___024root* vlSelf);

VL_ATTR_COLD void Vmain::final() {
    Vmain___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* Vmain::hierName() const { return vlSymsp->name(); }
const char* Vmain::modelName() const { return "Vmain"; }
unsigned Vmain::threads() const { return 1; }
std::unique_ptr<VerilatedTraceConfig> Vmain::traceConfig() const {
    return std::unique_ptr<VerilatedTraceConfig>{new VerilatedTraceConfig{false, false, false}};
};

//============================================================
// Trace configuration

void Vmain___024root__trace_init_top(Vmain___024root* vlSelf, VerilatedVcd* tracep);

VL_ATTR_COLD static void trace_init(void* voidSelf, VerilatedVcd* tracep, uint32_t code) {
    // Callback from tracep->open()
    Vmain___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<Vmain___024root*>(voidSelf);
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {
        VL_FATAL_MT(__FILE__, __LINE__, __FILE__,
            "Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.");
    }
    vlSymsp->__Vm_baseCode = code;
    tracep->scopeEscape(' ');
    tracep->pushNamePrefix(std::string{vlSymsp->name()} + ' ');
    Vmain___024root__trace_init_top(vlSelf, tracep);
    tracep->popNamePrefix();
    tracep->scopeEscape('.');
}

VL_ATTR_COLD void Vmain___024root__trace_register(Vmain___024root* vlSelf, VerilatedVcd* tracep);

VL_ATTR_COLD void Vmain::trace(VerilatedVcdC* tfp, int levels, int options) {
    if (tfp->isOpen()) {
        vl_fatal(__FILE__, __LINE__, __FILE__,"'Vmain::trace()' shall not be called after 'VerilatedVcdC::open()'.");
    }
    if (false && levels && options) {}  // Prevent unused
    tfp->spTrace()->addModel(this);
    tfp->spTrace()->addInitCb(&trace_init, &(vlSymsp->TOP));
    Vmain___024root__trace_register(&(vlSymsp->TOP), tfp->spTrace());
}
