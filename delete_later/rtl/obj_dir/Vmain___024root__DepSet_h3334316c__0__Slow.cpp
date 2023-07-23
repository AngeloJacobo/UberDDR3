// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vmain.h for the primary calling header

#include "verilated.h"
#include "verilated_dpi.h"

#include "Vmain__Syms.h"
#include "Vmain___024root.h"

VL_ATTR_COLD void Vmain___024root___eval_static__TOP(Vmain___024root* vlSelf);

VL_ATTR_COLD void Vmain___024root___eval_static(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_static\n"); );
    // Body
    Vmain___024root___eval_static__TOP(vlSelf);
    vlSelf->__Vm_traceActivity[6U] = 1U;
    vlSelf->__Vm_traceActivity[5U] = 1U;
    vlSelf->__Vm_traceActivity[4U] = 1U;
    vlSelf->__Vm_traceActivity[3U] = 1U;
    vlSelf->__Vm_traceActivity[2U] = 1U;
    vlSelf->__Vm_traceActivity[1U] = 1U;
    vlSelf->__Vm_traceActivity[0U] = 1U;
}

VL_ATTR_COLD void Vmain___024root___eval_static__TOP(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_static__TOP\n"); );
    // Body
    vlSelf->main__DOT__ddr3_controller_inst__DOT__instruction_address = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__instruction = 0x4380005U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_counter = 5U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_counter_is_zero = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__reset_done = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__pause_counter = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update = 1U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_stall = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_stall = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_pending = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_aux = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_we = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[8U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[9U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0xaU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0xbU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0xcU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0xdU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0xeU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data[0xfU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_dm = 0ULL;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_col = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_bank = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_row = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_next_bank = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_next_row = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_pending = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_aux = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_we = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm_unaligned = 0ULL;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[8U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[9U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0xaU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0xbU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0xcU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0xdU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0xeU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned[0xfU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_col = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_row = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_odt_q = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_stall_q = 1U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_store = 0ULL;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_count_repeat = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_stored = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index_orig = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dq_target_index = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_repeat = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_data = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_level_feedback = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__initial_dqs = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__lane = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__lane_times_8 = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_bitslip_arrangement = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe_max = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_stb = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_aux = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_we = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_col = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[8U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[9U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0xaU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0xbU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0xcU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0xdU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0xeU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data[0xfU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_odt = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dqs = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dq = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__prev_write_level_feedback = 1U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[8U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[9U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0xaU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0xbU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0xcU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0xdU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0xeU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store[0xfU] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_pattern[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_pattern[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_pattern[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_pattern[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_stb = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_update = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_we = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_addr = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_data = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_sel = 0U;
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_zero = 1U;
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_zero = 1U;
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_zero = 1U;
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_zero = 1U;
}

VL_ATTR_COLD void Vmain___024root___eval_initial__TOP(Vmain___024root* vlSelf);

VL_ATTR_COLD void Vmain___024root___eval_initial(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_initial\n"); );
    // Body
    Vmain___024root___eval_initial__TOP(vlSelf);
    vlSelf->__Vm_traceActivity[6U] = 1U;
    vlSelf->__Vm_traceActivity[5U] = 1U;
    vlSelf->__Vm_traceActivity[4U] = 1U;
    vlSelf->__Vm_traceActivity[3U] = 1U;
    vlSelf->__Vm_traceActivity[2U] = 1U;
    vlSelf->__Vm_traceActivity[1U] = 1U;
    vlSelf->__Vm_traceActivity[0U] = 1U;
    vlSelf->__Vtrigprevexpr___TOP__i_clk__0 = vlSelf->i_clk;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 
        = vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 
        = vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 
        = vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 
        = vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 
        = vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 
        = vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant;
    vlSelf->__Vtrigprevexpr___TOP__main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n__0 
        = vlSelf->main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n;
}

extern const VlWide<16>/*511:0*/ Vmain__ConstPool__CONST_h93e1b771_0;

VL_ATTR_COLD void Vmain___024root___eval_initial__TOP(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_initial__TOP\n"); );
    // Body
    vlSelf->main__DOT__wbwide_xbar__DOT__iM = 3U;
    vlSelf->main__DOT__wbwide_xbar__DOT__iN = 4U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM = 3U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__iM = 3U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__iM = 3U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__iM = 3U;
    vlSelf->main__DOT__wb32_xbar__DOT__iN = 1U;
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xffeU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xffdU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xffbU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xff7U & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xfefU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xfdfU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xfbfU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xf7fU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xeffU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xdffU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0xbffU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__requested[0U] 
        = (0x7ffU & vlSelf->main__DOT__wb32_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wb32_xbar__DOT__iM = 0xcU;
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM = 0xcU;
    vlSelf->main__DOT__wbu_xbar__DOT__iN = 1U;
    vlSelf->main__DOT__wbu_xbar__DOT__requested[0U] 
        = (2U & vlSelf->main__DOT__wbu_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wbu_xbar__DOT__requested[0U] 
        = (1U & vlSelf->main__DOT__wbu_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wbu_xbar__DOT__iM = 2U;
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM = 2U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__ik = 0x40U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k = 0U;
    while (VL_GTS_III(32, 0x80U, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k)) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv = 0x40U;
        if ((VL_LTES_III(32, 0x30U, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k) 
             & VL_GTES_III(32, 0x39U, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k))) {
            vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv 
                = (0x7fU & vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k);
            vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv 
                = (0x40U | (0xfU & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv)));
        } else {
            vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv 
                = ((VL_LTES_III(32, 0x41U, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k) 
                    & VL_GTES_III(32, 0x5aU, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k))
                    ? (0x40U | (0x3fU & ((IData)(9U) 
                                         + vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k)))
                    : ((VL_LTES_III(32, 0x61U, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k) 
                        & VL_GTES_III(32, 0x7aU, vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k))
                        ? ((0x40U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv)) 
                           | (0x3fU & ((IData)(3U) 
                                       + vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k)))
                        : ((0x40U == vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k)
                            ? (0x3eU | (0x40U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv)))
                            : ((0x25U == vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k)
                                ? (0x3fU | (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv))
                                : 0U))));
        }
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__remap[(0x7fU 
                                                                           & vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k)] 
            = vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv;
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k 
            = ((IData)(1U) + vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k);
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k = 0U;
    while (VL_GTS_III(32, 0x80U, vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k)) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__newv 
            = (VL_LTES_III(32, 0x40U, vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k)
                ? 0xaU : (0x7fU & ((9U >= vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k)
                                    ? ((IData)(0x30U) 
                                       + (0xfU & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k))
                                    : ((0x23U >= (0x3fU 
                                                  & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k))
                                        ? ((IData)(0x37U) 
                                           + (0x3fU 
                                              & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k))
                                        : ((0x3dU >= 
                                            (0x3fU 
                                             & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k))
                                            ? ((IData)(0x3dU) 
                                               + (0x3fU 
                                                  & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k))
                                            : ((0x3eU 
                                                == 
                                                (0x3fU 
                                                 & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k))
                                                ? 0x40U
                                                : 0x25U))))));
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__remap[(0x7fU 
                                                                            & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k)] 
            = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__newv;
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k 
            = ((IData)(1U) + vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k);
    }
    vlSelf->main__DOT__wbu_xbar__DOT__s_data[2U] = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__s_data[3U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0xaU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0xcU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0xdU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0xeU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][1U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[1U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][2U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][3U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][4U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][5U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][6U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][7U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][8U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][9U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0xaU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0xbU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0xcU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0xdU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0xeU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3U][0xfU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__sindex[3U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[1U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[2U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[3U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[4U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[5U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[6U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[7U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[8U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[9U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0xaU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0xbU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0xcU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0xdU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0xeU] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sindex[0xfU] = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__sindex[0U] = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__sindex[1U] = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__sindex[2U] = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__sindex[3U] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[0xcU] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[4U] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[0xdU] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[5U] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[0xeU] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[6U] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[0xfU] = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[7U] = 0U;
    vlSelf->main__DOT__r_wb32_sio_ack = 0U;
    vlSelf->main__DOT__r_sirefclk_en = 0U;
    vlSelf->main__DOT__r_sirefclk_data = 0x4e20U;
    vlSelf->main__DOT__r_cfg_ack = 0U;
    vlSelf->o_wbu_uart_cts_n = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__sgrant = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__grant[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mgrant = (0xeU 
                                                   & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant));
    vlSelf->main__DOT__wbwide_xbar__DOT__grant[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mgrant = (0xdU 
                                                   & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant));
    vlSelf->main__DOT__wbwide_xbar__DOT__grant[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mgrant = (0xbU 
                                                   & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant));
    vlSelf->main__DOT__wbwide_xbar__DOT__grant[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mgrant = (7U 
                                                   & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant));
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc 
        = (6U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb 
        = (6U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc 
        = (5U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb 
        = (5U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc 
        = (3U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb 
        = (3U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mempty = (1U 
                                                   | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty));
    vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull 
        = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__mfull = (0xeU 
                                                  & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mempty = (2U 
                                                   | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty));
    vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull 
        = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__mfull = (0xdU 
                                                  & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mempty = (4U 
                                                   | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty));
    vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull 
        = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__mfull = (0xbU 
                                                  & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__mempty = (8U 
                                                   | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty));
    vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull 
        = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__mfull = (7U 
                                                  & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_addr = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__decoded = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_addr = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__decoded = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_valid = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_addr = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[1U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[2U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[3U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[4U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[5U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[6U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[7U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[8U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[9U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xaU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xbU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xcU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xdU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xeU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xfU] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0x10U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0x11U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0x12U] = 0U;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__decoded = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__sgrant = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__grant[0U] = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__mgrant = 0U;
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xffeU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xffeU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xffdU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xffdU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xffbU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xffbU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xff7U & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xff7U & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xfefU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xfefU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xfdfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xfdfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xfbfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xfbfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xf7fU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xf7fU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xeffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xeffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xdffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xdffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0xbffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0xbffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc 
        = (0x7ffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb 
        = (0x7ffU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb));
    vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__mempty = 1U;
    vlSelf->main__DOT__wb32_xbar__DOT__mnearfull = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__mfull = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data = 0ULL;
    vlSelf->main__DOT__wb32_xbar__DOT__dcd_stb = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr = 0U;
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data = 0ULL;
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__sgrant = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__grant[0U] = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__mgrant = 0U;
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc 
        = (2U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb 
        = (2U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb));
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc 
        = (1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc));
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb 
        = (1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb));
    vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__mempty = 1U;
    vlSelf->main__DOT__wbu_xbar__DOT__mnearfull = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__mfull = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data = 0ULL;
    vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr = 0U;
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data = 0ULL;
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__br_config = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__br_holdoff = 0x7fcU;
    vlSelf->main__DOT__emmcscopei__DOT__dr_triggered = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__holdoff_counter = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__dr_stopped = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__ck_addr = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__dr_force_write = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__lst_adr = 1U;
    vlSelf->main__DOT__emmcscopei__DOT__imm_adr = 1U;
    vlSelf->main__DOT__emmcscopei__DOT__record_ce = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__waddr = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__dr_primed = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__br_pre_wb_ack = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack = 0U;
    vlSelf->main__DOT__emmcscopei__DOT__br_level_interrupt = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__br_config = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__br_holdoff = 0x7fcU;
    vlSelf->main__DOT__sdioscopei__DOT__dr_triggered = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__holdoff_counter = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__dr_stopped = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__ck_addr = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__dr_force_write = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__lst_adr = 1U;
    vlSelf->main__DOT__sdioscopei__DOT__imm_adr = 1U;
    vlSelf->main__DOT__sdioscopei__DOT__record_ce = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__waddr = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__dr_primed = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__br_pre_wb_ack = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__br_wb_ack = 0U;
    vlSelf->main__DOT__sdioscopei__DOT__br_level_interrupt = 0U;
    vlSelf->o_ddr3_controller_bitslip = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xfeU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xfeU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xfdU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xfdU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xfbU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xfbU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xf7U & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xf7U & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xefU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xefU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xdfU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xdfU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0xbfU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0xbfU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q 
        = (0x7fU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d 
        = (0x7fU & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][1U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[1U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][2U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[2U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][3U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[3U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][4U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[4U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][5U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[5U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][6U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[6U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][7U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[7U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][8U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[8U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][9U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[9U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0xaU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0xbU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0xcU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0xdU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0xeU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0U][0xfU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm[0U] = 0ULL;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][1U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[1U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][2U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[2U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][3U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[3U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][4U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[4U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][5U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[5U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][6U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[6U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][7U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[7U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][8U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[8U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][9U] 
        = Vmain__ConstPool__CONST_h93e1b771_0[9U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0xaU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0xbU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0xcU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0xdU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0xeU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1U][0xfU] 
        = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm[1U] = 0ULL;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[0U] = 0xffffffU;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[1U] = 0xffffffU;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[2U] = 0xffffffU;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[3U] = 0xffffffU;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[0U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[0U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[0U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[1U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[1U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[1U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[2U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[2U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[2U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[3U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[3U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[3U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[4U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[4U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[4U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[5U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[5U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[5U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[6U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[6U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[6U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[7U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[7U] = 0U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[7U] = 8U;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__index = 8U;
    VL_WRITEF("TEST FUNCTIONS\n-----------------------------\n\nTest ns_to_cycles() function:\n");
    VL_WRITEF("\tns_to_cycles(15) = 2 [exact]\n");
    VL_WRITEF("\tns_to_cycles(14.5) = 2 [round-off]\n");
    vlSelf->main__DOT__ddr3_controller_inst__DOT__ns_to_cycles__Vstatic__result = 2U;
    VL_WRITEF("\tns_to_cycles(11) = 2 [round-up]\n\nTest nCK_to_cycles() function:\n");
    VL_WRITEF("\tns_to_cycles(16) = 4 [exact]\n");
    VL_WRITEF("\tns_to_cycles(15) = 4 [round-off]\n");
    vlSelf->main__DOT__ddr3_controller_inst__DOT__nCK_to_cycles__Vstatic__result = 4U;
    VL_WRITEF("\tns_to_cycles(13) = 4 [round-up]\n\nTest ns_to_nCK() function:\n");
    VL_WRITEF("\tns_to_cycles(15) = 6 [exact]\n");
    VL_WRITEF("\tns_to_cycles(14.875) = 6 [round-off]\n");
    VL_WRITEF("\tns_to_cycles(13.875) = 6 [round-up] \n\nTest nCK_to_ns() function:\n");
    VL_WRITEF("\tns_to_cycles(4) =  10.000000 [exact]\n");
    VL_WRITEF("\tns_to_cycles(14.875) = 8.000000 [round-off]\n");
    VL_WRITEF("\tns_to_cycles(13.875) = 13.000000 [round-up]\n\nTest nCK_to_ns() function:\n");
    VL_WRITEF("\tns_to_cycles(4) = 10.000000 [exact]\n");
    VL_WRITEF("\tns_to_cycles(14.875) = 8.000000 [round-off]\n");
    VL_WRITEF("\tns_to_cycles(13.875) = 13.000000 [round-up]\n\n");
    VL_WRITEF("Test $floor() function:\n\t$floor(5/2) = 2.000000\n\t$floor(9/4) = 2.000000\n\t$floor(9/4) = 2.000000\n\t$floor(9/5) = 1.000000\n\n\nDISPLAY CONTROLLER PARAMETERS\n-----------------------------\n\nCONTROLLER_CLK_PERIOD = 10.00\nDDR3_CLK_PERIOD = 2.50\nROW_BITS = 14\nCOL_BITS = 10\nBA_BITS = 3\nDQ_BITS = 8\nLANES = 8\nAUX_WIDTH = 1\nWB2_ADDR_BITS = 32\nWB2_DATA_BITS = 32\nserdes_ratio = 4\nwb_addr_bits = 21\nwb_data_bits = 512\nwb_sel_bits  = 64\nwb2_sel_bits = 4\ncmd_len = 24\nDELAY_COUNTER_WIDTH = 16\nDELAY_SLOT_WIDTH = 19\n");
    VL_WRITEF("serdes_ratio = 4\nwb_addr_bits = 21\nwb_data_bits = 512\nwb_sel_bits = 64\n\n\nREAD_SLOT = 2\nWRITE_SLOT = 3\nACTIVATE_SLOT = 0\nPRECHARGE_SLOT = 1\n\n\nDELAYS:\n");
    VL_WRITEF("\tns_to_nCK(tRCD): 6\n");
    VL_WRITEF("\tns_to_nCK(tRP): 6\n");
    VL_WRITEF("\tns_to_nCK(tRTP): 4\n\ttCCD: 4\n\t(CL_nCK + tCCD + 2 - CWL_nCK): 7\n");
    VL_WRITEF("\t(CWL_nCK + 4 + ns_to_nCK(tWR)): 15\n");
    VL_WRITEF("\t(CWL_nCK + 4 + ns_to_nCK(tWTR)): 13\n\n\nPRECHARGE_TO_ACTIVATE_DELAY = 1\nACTIVATE_TO_WRITE_DELAY = 0\nACTIVATE_TO_READ_DELAY =  0\nREAD_TO_WRITE_DELAY = 1\nREAD_TO_READ_DELAY = 0\nREAD_TO_PRECHARGE_DELAY = 1\nWRITE_TO_WRITE_DELAY = 0\nWRITE_TO_READ_DELAY = 3\nWRITE_TO_PRECHARGE_DELAY = 4\nSTAGE2_DATA_DEPTH = 2\nREAD_ACK_PIPE_WIDTH = 5\n");
    vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_wstb = 0U;
    vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_stb = 0U;
    vlSelf->main__DOT__wbwide_bkram_ack = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__r_memlen = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__r_reset = 1U;
    vlSelf->main__DOT__wb32_i2cdma_ack = 0U;
    vlSelf->main__DOT__wb32_i2cdma_idata = 0U;
    vlSelf->main__DOT__wbwide_i2cdma_cyc = 0U;
    vlSelf->main__DOT__wbwide_i2cdma_stb = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_data = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data = 0U;
    vlSelf->main__DOT__u_fan__DOT__ctl_fpga = 0x1387U;
    vlSelf->main__DOT__u_fan__DOT__ctl_sys = 0x1387U;
    vlSelf->main__DOT__u_fan__DOT__pre_ack = 0U;
    vlSelf->main__DOT__wb32_fan_ack = 0U;
    vlSelf->main__DOT__u_fan__DOT__i2c_wb_ack = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda = 1U;
    vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc = 0U;
    vlSelf->main__DOT__u_fan__DOT__mem_stb = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__invalid_bus_cycle = 0U;
    vlSelf->main__DOT__u_fan__DOT__mem_addr = 0x1fU;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_illegal = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__lst_scl = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__q_scl = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__lst_sda = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__q_sda = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__stop_bit = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__channel_busy = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 0U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg = 0xffU;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset = 1U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request = 0U;
    vlSelf->main__DOT__u_emmc__DOT__rx_en = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk = 9U;
    vlSelf->main__DOT__u_emmc__DOT__cfg_sample_shift = 0x18U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90 = 0U;
    vlSelf->main__DOT__u_emmc__DOT__pp_cmd = 0U;
    vlSelf->main__DOT__u_emmc__DOT__pp_data = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds = 0U;
    vlSelf->main__DOT__u_emmc__DOT__cfg_ddr = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed = 0xfcU;
    vlSelf->main__DOT__emmc_int = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_a = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_b = 0U;
    vlSelf->main__DOT__wb32_emmc_ack = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_ack = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb = 1U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_half = 1U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__w_sdclk = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_id = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_arg = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_valid = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = 0x3ffffffU;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_err = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_data = 0xffffffffU;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_stop_bit = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg = 0xffffffffU;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data = 0xffffffffU;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__ck_sreg = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__sample_ck = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__dat0_busy = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__wait_for_busy = 1U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__last_ck = 0U;
    vlSelf->main__DOT__wb32_i2cs_ack = 0U;
    vlSelf->main__DOT__i2ci__DOT__half_valid = 0U;
    vlSelf->main__DOT__i2ci__DOT__imm_cycle = 0U;
    vlSelf->main__DOT__i2ci__DOT__insn_valid = 0U;
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual = 0U;
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__scl = 1U;
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__sda = 1U;
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_scl = 1U;
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_sda = 1U;
    vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid = 0U;
    vlSelf->main__DOT__wbwide_i2cm_cyc = 0U;
    vlSelf->main__DOT__wbwide_i2cm_stb = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__invalid_bus_cycle = 0U;
    vlSelf->main__DOT__wbwide_i2cm_addr = 0x3fffffU;
    vlSelf->main__DOT__i2ci__DOT__pf_valid = 0U;
    vlSelf->main__DOT__i2ci__DOT__pf_illegal = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_illegal = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__lst_scl = 1U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl = 1U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__q_scl = 1U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__lst_sda = 1U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda = 1U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__q_sda = 1U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__stop_bit = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 0U;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg = 0xffU;
    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
    vlSelf->main__DOT__i2ci__DOT__w_sda = 1U;
    vlSelf->main__DOT__i2ci__DOT__i2c_abort = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_we = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_null = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[1U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[2U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[3U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[4U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[5U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[6U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[7U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[8U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[9U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xaU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xbU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xcU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xdU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xeU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xfU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel = 0ULL;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[1U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[2U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[3U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[4U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[5U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[6U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[7U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[8U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[9U] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xaU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xbU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xcU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xdU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xeU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xfU] = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_ack = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_full = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_empty = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__rx_en = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk = 9U;
    vlSelf->main__DOT__u_sdcard__DOT__cfg_sample_shift = 0x18U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90 = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__pp_cmd = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__pp_data = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed = 0xfcU;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_removed = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_present = 0U;
    vlSelf->main__DOT__sdcard_int = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_a = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_b = 0U;
    vlSelf->main__DOT__wb32_sdcard_ack = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_ack = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_half = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__w_sdclk = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_id = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_arg = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_valid = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = 0x3ffffffU;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_err = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data = 0xffffffffU;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_stop_bit = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg = 0xffffffffU;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data = 0xffffffffU;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__ck_sreg = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__sample_ck = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__dat0_busy = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__wait_for_busy = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__last_ck = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__high_z = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__high_z = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__high_z = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__high_z = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__high_z = 1U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__high_z = 1U;
    vlSelf->main__DOT__console__DOT__rxf_wb_read = 0U;
    vlSelf->main__DOT__console__DOT__rx_uart_reset = 1U;
    vlSelf->main__DOT__console__DOT__txf_wb_write = 0U;
    vlSelf->main__DOT__console__DOT__tx_uart_reset = 1U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow = 0U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr = 0U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow = 1U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr = 0U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_next = 1U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__osrc = 0U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill = 0U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow = 0U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr = 0U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow = 1U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr = 0U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__r_next = 1U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__osrc = 0U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill = 0x3fU;
    vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter = 0x14U;
    vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__r_reset_hold = 1U;
    vlSelf->main__DOT__swic__DOT__cmd_reset = 1U;
    vlSelf->main__DOT__swic__DOT__cmd_halt = 1U;
    vlSelf->main__DOT__swic__DOT__cmd_clear_cache = 0U;
    vlSelf->main__DOT__swic__DOT__cmd_step = 0U;
    vlSelf->main__DOT__swic__DOT__GEN_DBG_CATCH__DOT__r_dbg_catch = 1U;
    vlSelf->main__DOT__swic__DOT__cmd_write = 0U;
    vlSelf->main__DOT__swic__DOT__cmd_read = 0U;
    vlSelf->main__DOT__swic__DOT__cmd_read_ack = 0U;
    vlSelf->main__DOT__swic__DOT__r_wdbus_data = 0U;
    vlSelf->main__DOT__swic__DOT__wdbus_ack = 0U;
    vlSelf->main__DOT__swic__DOT__r_mmus_ack = 0U;
    vlSelf->main__DOT__swic__DOT__last_sys_stb = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_pre_ack = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_ack = 0U;
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_running = 0U;
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value = 0U;
    vlSelf->main__DOT__swic__DOT__wdt_reset = 0U;
    vlSelf->main__DOT__swic__DOT__wdt_ack = 0U;
    vlSelf->main__DOT__swic__DOT__u_watchbus__DOT__r_value = 0x3fffU;
    vlSelf->main__DOT__swic__DOT__wdbus_int = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_running = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value = 0U;
    vlSelf->main__DOT__swic__DOT__tma_int = 0U;
    vlSelf->main__DOT__swic__DOT__tma_ack = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_running = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value = 0U;
    vlSelf->main__DOT__swic__DOT__tmb_int = 0U;
    vlSelf->main__DOT__swic__DOT__tmb_ack = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_running = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload = 0U;
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value = 0U;
    vlSelf->main__DOT__swic__DOT__tmc_int = 0U;
    vlSelf->main__DOT__swic__DOT__tmc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter = 0U;
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_now = 0U;
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set = 0U;
    vlSelf->main__DOT__swic__DOT__jif_int = 0U;
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set = 0U;
    vlSelf->main__DOT__swic__DOT__jif_ack = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_pending_sreg_write = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_PIPE__DOT__r_op_pipe = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Aid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Bid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rA = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rB = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_Rcc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_Av = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_Bv = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_F = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_div = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_fpu = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_break = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OPLOCK__DOT__r_op_lock = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_OP_PC__DOT__r_op_pc 
        = (0xffffffeU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_OP_PC__DOT__r_op_pc);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OPT_CIS_OP_PHASE__DOT__r_op_phase = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_wF = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_wR = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_index = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PC__DOT__r_alu_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_ALU_ILLEGAL__DOT__r_alu_illegal = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_alu_pc_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_pc_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_prelock_stall = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__break_en = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__user_step = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_user_stepped = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_pending_interrupt = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_ubreak = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_ILLEGAL_INSN__DOT__r_ill_err_u = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_BUSERR__DOT__r_ubus_err_flag = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_IHALT_PHASE__DOT__r_ihalt_phase = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ipc = 0x4000000U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pf_pc = 0x4000000U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__last_write_to_cc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache = 1U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__CLEAR_DCACHE__DOT__r_clear_dcache = 1U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc = 1U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted = 1U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_dbg_stall = 1U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_stb = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_addr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_DIV = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_FP = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_lock = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim_immv = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch_stb = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_pipe = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_error = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_c = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay = 3U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v_from_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v_from_last = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__needload = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_addr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__valid_mask = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__svmask = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cachable = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_svalid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel = 0xffffffffffffffffULL;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU] = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_cstb = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_result = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_valid = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_gbl = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_lcl = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner = 1U;
    vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner = 1U;
    vlSelf->main__DOT__swic__DOT__dbg_cyc = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_stb = 0U;
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb = 0U;
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_we = 0U;
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_addr = 0U;
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_data = 0U;
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_sel = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_we = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_addr = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_idata = 0U;
    vlSelf->main__DOT__swic__DOT__dbg_sel = 0U;
    vlSelf->main__DOT__raw_cpu_dbg_ack = 0U;
    vlSelf->main__DOT__wbu_zip_idata = 0U;
    vlSelf->main__DOT__swic__DOT__no_dbg_err = 0U;
    vlSelf->main__DOT__swic__DOT__mtc_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__moc_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__mpc_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__mic_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_ack = 0U;
    vlSelf->main__DOT__swic__DOT__utc_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__uoc_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__upc_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_ack = 0U;
    vlSelf->main__DOT__swic__DOT__uic_int = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data = 0U;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_ack = 0U;
    vlSelf->main__DOT__swic__DOT__dmac_ack = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_err = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[1U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[2U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[3U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[4U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[5U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[6U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[7U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[8U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[9U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xaU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xbU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xcU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xdU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xeU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xfU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_last = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_bytes = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_empty = 1U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_valid = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_next = 1U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_last = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_last = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_pipeline_full = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_outstanding = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner = 1U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__ALT__DOT__last_owner = 0U;
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state = 0U;
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable = 0U;
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie = 0U;
    vlSelf->main__DOT__swic__DOT__ctri_int = 0U;
    vlSelf->main__DOT__swic__DOT__ctri_data = 0U;
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state = 0U;
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable = 0U;
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_mie = 0U;
    vlSelf->main__DOT__swic__DOT__pic_interrupt = 0U;
    vlSelf->main__DOT__swic__DOT__pic_data = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__br_config = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__br_holdoff = 0x1fcU;
    vlSelf->main__DOT__i2cscopei__DOT__dr_triggered = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__holdoff_counter = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__dr_stopped = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__ck_addr = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__dr_force_write = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__lst_adr = 1U;
    vlSelf->main__DOT__i2cscopei__DOT__imm_adr = 1U;
    vlSelf->main__DOT__i2cscopei__DOT__record_ce = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__waddr = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__dr_primed = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__br_pre_wb_ack = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__br_wb_ack = 0U;
    vlSelf->main__DOT__i2cscopei__DOT__br_level_interrupt = 0U;
    vlSelf->main__DOT__rcv__DOT__q_uart = 1U;
    vlSelf->main__DOT__rcv__DOT__qq_uart = 1U;
    vlSelf->main__DOT__rcv__DOT__ck_uart = 1U;
    vlSelf->main__DOT__rcv__DOT__chg_counter = 0x7fU;
    vlSelf->main__DOT__rcv__DOT__half_baud_time = 0U;
    vlSelf->main__DOT__rcv__DOT__state = 0xfU;
    vlSelf->main__DOT__wbu_rx_stb = 0U;
    vlSelf->main__DOT__wbu_rx_data = 0U;
    vlSelf->main__DOT__rcv__DOT__baud_counter = 0U;
    vlSelf->main__DOT__rcv__DOT__zero_baud_counter = 1U;
    vlSelf->main__DOT__txv__DOT__r_busy = 1U;
    vlSelf->main__DOT__txv__DOT__state = 0xfU;
    vlSelf->main__DOT__txv__DOT__lcl_data = 0xffU;
    vlSelf->o_wbu_uart_tx = 1U;
    vlSelf->main__DOT__txv__DOT__zero_baud_counter = 1U;
    vlSelf->main__DOT__txv__DOT__baud_counter = 0U;
    vlSelf->main__DOT__w_console_rx_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__ps_full = 0U;
    vlSelf->main__DOT__genbus__DOT__r_wdt_reset = 1U;
    vlSelf->main__DOT__genbus__DOT__r_wdt_timer = 0U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__soft_reset = 1U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len = 0U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg = 0ULL;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw = 0U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len = 0U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr = 0U;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__in_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state = 0U;
    vlSelf->main__DOT__wbu_cyc = 0U;
    vlSelf->main__DOT__wbu_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_new_addr = 1U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed = 0U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__zero_acks = 1U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len = 0U;
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_read_request = 1U;
    vlSelf->main__DOT__genbus__DOT__exec_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits = 0x40U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_out_nl = 1U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_in_nl = 1U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__full_line = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__r_busy = 0U;
    vlSelf->main__DOT__genbus__DOT__wbu_tx_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__wbu_tx_data = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__aword_valid = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_filled = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k = 0U;
    while (VL_GTS_III(32, 0x400U, vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k)) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl[(0x3ffU 
                                                                                & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k)] = 0U;
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k 
            = ((IData)(1U) + vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k);
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dmatch = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__vaddr = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table = 1U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__pmatch = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__zmatch = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__hmatch = 0U;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb = 0U;
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow = 0U;
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr = 0U;
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow = 1U;
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr = 0U;
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n = 0U;
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow = 0U;
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr = 0U;
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow = 1U;
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr = 0U;
    vlSelf->main__DOT__genbus__DOT__ofifo_empty_n = 0U;
    vlSelf->o_gpio = 0x20U;
    vlSelf->main__DOT__spioi__DOT__r_led = 0U;
    vlSelf->main__DOT__spioi__DOT__led_demo = 1U;
    vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw = 0U;
    vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe = 0U;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner = 1U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_stb = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_we = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_addr = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_sel = 0ULL;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[1U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[2U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[3U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[4U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[5U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[6U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[7U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[8U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[9U] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xaU] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xbU] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xcU] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xdU] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xeU] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xfU] = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_ack = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_full = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr = 0U;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_empty = 1U;
}

VL_ATTR_COLD void Vmain___024root___eval_final(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_final\n"); );
}

VL_ATTR_COLD void Vmain___024root___eval_triggers__stl(Vmain___024root* vlSelf);
#ifdef VL_DEBUG
VL_ATTR_COLD void Vmain___024root___dump_triggers__stl(Vmain___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD void Vmain___024root___eval_stl(Vmain___024root* vlSelf);

VL_ATTR_COLD void Vmain___024root___eval_settle(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_settle\n"); );
    // Init
    CData/*0:0*/ __VstlContinue;
    // Body
    vlSelf->__VstlIterCount = 0U;
    __VstlContinue = 1U;
    while (__VstlContinue) {
        __VstlContinue = 0U;
        Vmain___024root___eval_triggers__stl(vlSelf);
        if (vlSelf->__VstlTriggered.any()) {
            __VstlContinue = 1U;
            if (VL_UNLIKELY((0x64U < vlSelf->__VstlIterCount))) {
#ifdef VL_DEBUG
                Vmain___024root___dump_triggers__stl(vlSelf);
#endif
                VL_FATAL_MT("main.v", 97, "", "Settle region did not converge.");
            }
            vlSelf->__VstlIterCount = ((IData)(1U) 
                                       + vlSelf->__VstlIterCount);
            Vmain___024root___eval_stl(vlSelf);
        }
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vmain___024root___dump_triggers__stl(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

extern const VlUnpacked<CData/*3:0*/, 8> Vmain__ConstPool__TABLE_h611c22d1_0;

VL_ATTR_COLD void Vmain___024root___stl_sequent__TOP__0(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___stl_sequent__TOP__0\n"); );
    // Init
    CData/*1:0*/ main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0;
    main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0 = 0;
    IData/*31:0*/ __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old;
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb;
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb = 0;
    IData/*31:0*/ __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt;
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt = 0;
    IData/*31:0*/ __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old;
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb;
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb = 0;
    IData/*31:0*/ __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt;
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__prior = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior = 0;
    CData/*7:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior = 0;
    CData/*1:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout;
    __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout = 0;
    QData/*63:0*/ __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel;
    __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__prior = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit = 0;
    CData/*2:0*/ __Vtableidx10;
    __Vtableidx10 = 0;
    VlWide<16>/*511:0*/ __Vtemp_h3711b190__0;
    VlWide<16>/*511:0*/ __Vtemp_h18146fff__0;
    // Body
    vlSelf->io_sdcard_cmd_tristate = vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__high_z;
    vlSelf->o_fan_sda = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda;
    vlSelf->o_fan_scl = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl;
    vlSelf->o_i2c_sda = vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_sda;
    vlSelf->o_i2c_scl = vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_scl;
    vlSelf->main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n 
        = (1U & (~ (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__raw_cpu_dbg_stall = vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb;
    vlSelf->main__DOT__wbwide_wbu_arbiter_cyc = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc;
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_merr 
        = vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wb32_wbdown_cyc = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc;
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__emmcscopei__DOT__bw_reset_request 
        = (1U & (~ ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                    >> 2U)));
    vlSelf->main__DOT__sdioscopei__DOT__bw_reset_request 
        = (1U & (~ ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                    >> 2U)));
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__r_valid 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_phase 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim_immv 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim_immv;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ubreak 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_ubreak;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_u 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_ILLEGAL_INSN__DOT__r_ill_err_u;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ubus_err_flag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_BUSERR__DOT__r_ubus_err_flag;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_valid 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_valid;
    vlSelf->main__DOT__i2cscopei__DOT__bw_reset_request 
        = (1U & (~ ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                    >> 2U)));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_busy 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb;
    vlSelf->o_ddr3_controller_dqs_tri_control = (1U 
                                                 & (~ 
                                                    ((IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs) 
                                                     >> 2U)));
    vlSelf->o_ddr3_controller_dq_tri_control = (1U 
                                                & (~ 
                                                   ((IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq) 
                                                    >> 3U)));
    vlSelf->o_ddr3_controller_toggle_dqs = (1U & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_val));
    vlSelf->o_ddr3_controller_data[0U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0U];
    vlSelf->o_ddr3_controller_data[1U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][1U];
    vlSelf->o_ddr3_controller_data[2U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][2U];
    vlSelf->o_ddr3_controller_data[3U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][3U];
    vlSelf->o_ddr3_controller_data[4U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][4U];
    vlSelf->o_ddr3_controller_data[5U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][5U];
    vlSelf->o_ddr3_controller_data[6U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][6U];
    vlSelf->o_ddr3_controller_data[7U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][7U];
    vlSelf->o_ddr3_controller_data[8U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][8U];
    vlSelf->o_ddr3_controller_data[9U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][9U];
    vlSelf->o_ddr3_controller_data[0xaU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0xaU];
    vlSelf->o_ddr3_controller_data[0xbU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0xbU];
    vlSelf->o_ddr3_controller_data[0xcU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0xcU];
    vlSelf->o_ddr3_controller_data[0xdU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0xdU];
    vlSelf->o_ddr3_controller_data[0xeU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0xeU];
    vlSelf->o_ddr3_controller_data[0xfU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data
        [1U][0xfU];
    vlSelf->o_ddr3_controller_dm = vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm
        [1U];
    vlSelf->o_sirefclk_ce = vlSelf->main__DOT__r_sirefclk_en;
    vlSelf->cpu_sim_idata = vlSelf->main__DOT__wbu_zip_idata;
    vlSelf->cpu_prof_stb = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_stb;
    vlSelf->cpu_prof_addr = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_addr;
    vlSelf->cpu_prof_ticks = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks;
    vlSelf->o_led = vlSelf->main__DOT__w_led;
    vlSelf->main__DOT__i2cdma_ready = (1U & (~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wb32_wbdown_err = vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr;
    vlSelf->main__DOT__wb32_xbar__DOT__m_data[0U] = (IData)(
                                                            (vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data 
                                                             >> 4U));
    vlSelf->main__DOT__wb32_xbar__DOT__m_sel[0U] = 
        (0xfU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data));
    vlSelf->main__DOT__wb32_xbar__DOT__m_addr[0U] = vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wb32_xbar__DOT__w_mpending[0U] 
        = vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__wbu_err = vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr;
    vlSelf->main__DOT__wbu_xbar__DOT__m_data[0U] = (IData)(
                                                           (vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data 
                                                            >> 4U));
    vlSelf->main__DOT__wbu_xbar__DOT__m_sel[0U] = (0xfU 
                                                   & (IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data));
    vlSelf->main__DOT__wbu_xbar__DOT__m_addr[0U] = vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wbu_xbar__DOT__w_mpending[0U] 
        = vlSelf->main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index_value 
        = (0x3fU & ((1U & (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_stored))
                     ? ((IData)(2U) + (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_stored))
                     : ((IData)(1U) + (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_stored))));
    vlSelf->main__DOT__u_i2cdma__DOT__skd_valid = vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_waddr_plus_one 
        = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr)));
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_waddr_plus_one 
        = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_I 
        = (((- (IData)((1U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_I 
                              >> 0x16U)))) << 0x16U) 
           | (0x3fffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_I));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim_immv 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim_immv;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cline 
        = (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                 >> 3U));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_ctag 
        = (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                       >> 3U));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__rx_valid 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid;
    vlSelf->main__DOT__genbus__DOT__w_bus_busy = vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cod_busy 
        = (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb));
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__w_addr 
        = (((- (IData)((1U & (vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_addr 
                              >> 0x18U)))) << 0x19U) 
           | vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_addr);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck 
        = (((0U == (0xffU & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                                     >> 0x18U)))) << 3U) 
           | (((0U == (0x3fU & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                                        >> 0x12U)))) 
               << 2U) | (((0U == (0x3fU & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                                                   >> 0xcU)))) 
                          << 1U) | (0U == (0x3fU & (IData)(
                                                           (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                                                            >> 6U)))))));
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__nxt_wrptr 
        = (0x7fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr)));
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__nxt_wrptr 
        = (0x7ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr)));
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__br_ctr 
        = ((0x10U & (vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr 
                     << 4U)) | ((8U & (vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr 
                                       << 2U)) | ((4U 
                                                   & vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr) 
                                                  | ((2U 
                                                      & (vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr 
                                                         >> 2U)) 
                                                     | (1U 
                                                        & (vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr 
                                                           >> 4U))))));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU] = 0U;
    if ((0U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xfU]));
    }
    if ((1U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xfU]));
    }
    if ((2U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xfU]));
    }
    if ((3U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xfU]));
    }
    if ((4U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xeU]));
    }
    if ((5U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xeU]));
    }
    if ((6U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xeU]));
    }
    if ((7U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xeU]));
    }
    if ((8U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xdU]));
    }
    if ((9U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xdU]));
    }
    if ((0xaU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xdU]));
    }
    if ((0xbU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xdU]));
    }
    if ((0xcU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xcU]));
    }
    if ((0xdU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xcU]));
    }
    if ((0xeU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xcU]));
    }
    if ((0xfU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xcU]));
    }
    if ((0x10U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xbU]));
    }
    if ((0x11U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xbU]));
    }
    if ((0x12U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xbU]));
    }
    if ((0x13U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xbU]));
    }
    if ((0x14U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xaU]));
    }
    if ((0x15U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xaU]));
    }
    if ((0x16U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xaU]));
    }
    if ((0x17U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0xaU]));
    }
    if ((0x18U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[9U]));
    }
    if ((0x19U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[9U]));
    }
    if ((0x1aU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[9U]));
    }
    if ((0x1bU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[9U]));
    }
    if ((0x1cU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[8U]));
    }
    if ((0x1dU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[8U]));
    }
    if ((0x1eU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[8U]));
    }
    if ((0x1fU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[8U]));
    }
    if ((0x20U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[7U]));
    }
    if ((0x21U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[7U]));
    }
    if ((0x22U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[7U]));
    }
    if ((0x23U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[7U]));
    }
    if ((0x24U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[6U]));
    }
    if ((0x25U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[6U]));
    }
    if ((0x26U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[6U]));
    }
    if ((0x27U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[6U]));
    }
    if ((0x28U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[5U]));
    }
    if ((0x29U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[5U]));
    }
    if ((0x2aU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[5U]));
    }
    if ((0x2bU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[5U]));
    }
    if ((0x2cU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[4U]));
    }
    if ((0x2dU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[4U]));
    }
    if ((0x2eU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[4U]));
    }
    if ((0x2fU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[4U]));
    }
    if ((0x30U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[3U]));
    }
    if ((0x31U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[3U]));
    }
    if ((0x32U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[3U]));
    }
    if ((0x33U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[3U]));
    }
    if ((0x34U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[2U]));
    }
    if ((0x35U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[2U]));
    }
    if ((0x36U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[2U]));
    }
    if ((0x37U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[2U]));
    }
    if ((0x38U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[1U]));
    }
    if ((0x39U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[1U]));
    }
    if ((0x3aU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[1U]));
    }
    if ((0x3bU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[1U]));
    }
    if ((0x3cU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U] 
            = ((0xffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U]) 
               | (0xff000000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0U]));
    }
    if ((0x3dU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U] 
            = ((0xff00ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U]) 
               | (0xff0000U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0U]));
    }
    if ((0x3eU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U] 
            = ((0xffff00ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U]) 
               | (0xff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0U]));
    }
    if ((0x3fU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U] 
            = ((0xffffff00U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U]) 
               | (0xffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg[0U]));
    }
    if (vlSelf->i_clk) {
        vlSelf->o_sdcard_clk = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__r_out) 
                                      >> 1U));
        vlSelf->o_sdcard_cmd = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__r_out) 
                                      >> 1U));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__o_pin 
            = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__r_out) 
                     >> 1U));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__o_pin 
            = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__r_out) 
                     >> 1U));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__o_pin 
            = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__r_out) 
                     >> 1U));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__o_pin 
            = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__r_out) 
                     >> 1U));
    } else {
        vlSelf->o_sdcard_clk = (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__r_out));
        vlSelf->o_sdcard_cmd = (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__r_out));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__o_pin 
            = (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__r_out));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__o_pin 
            = (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__r_out));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__o_pin 
            = (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__r_out));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__o_pin 
            = (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__r_out));
    }
    vlSelf->cpu_sim_stall = (1U & ((~ (IData)(vlSelf->cpu_sim_cyc)) 
                                   | (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb)));
    vlSelf->cpu_sim_ack = ((IData)(vlSelf->cpu_sim_cyc) 
                           & (IData)(vlSelf->main__DOT__raw_cpu_dbg_ack));
    vlSelf->main__DOT__wb32_sirefclk_stb = (IData)(
                                                   (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                                     >> 9U) 
                                                    & (0x200U 
                                                       == 
                                                       (0x700U 
                                                        & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))));
    vlSelf->main__DOT____Vcellinp__swic__i_reset = 
        ((IData)(vlSelf->i_cpu_reset) | (IData)(vlSelf->i_reset));
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc 
        = (IData)((((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                    >> 1U) | (IData)(vlSelf->cpu_sim_cyc)));
    vlSelf->main__DOT__wbwide_xbar__DOT__s_err = (8U 
                                                  | ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc) 
                                                     & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err)));
    vlSelf->main__DOT__wbu_xbar__DOT__s_err = (0xcU 
                                               | ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                                                  & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err)));
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted));
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN 
        = (1U & (~ ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy 
        = (1U & ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb)) 
                 | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy)));
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__r_halted));
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN 
        = (1U & (~ ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual))));
    __Vtemp_h3711b190__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x10U];
    __Vtemp_h3711b190__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x11U];
    __Vtemp_h3711b190__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x12U];
    __Vtemp_h3711b190__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x13U];
    __Vtemp_h3711b190__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x14U];
    __Vtemp_h3711b190__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x15U];
    __Vtemp_h3711b190__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x16U];
    __Vtemp_h3711b190__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x17U];
    __Vtemp_h3711b190__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x18U];
    __Vtemp_h3711b190__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x19U];
    __Vtemp_h3711b190__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1aU];
    __Vtemp_h3711b190__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1bU];
    __Vtemp_h3711b190__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1cU];
    __Vtemp_h3711b190__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1dU];
    __Vtemp_h3711b190__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1eU];
    __Vtemp_h3711b190__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1fU];
    VL_SHIFTL_WWI(512,512,32, __Vtemp_h18146fff__0, __Vtemp_h3711b190__0, 
                  ((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_shift) 
                   << 3U));
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0U] 
        = __Vtemp_h18146fff__0[0U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[1U] 
        = __Vtemp_h18146fff__0[1U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[2U] 
        = __Vtemp_h18146fff__0[2U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[3U] 
        = __Vtemp_h18146fff__0[3U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[4U] 
        = __Vtemp_h18146fff__0[4U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[5U] 
        = __Vtemp_h18146fff__0[5U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[6U] 
        = __Vtemp_h18146fff__0[6U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[7U] 
        = __Vtemp_h18146fff__0[7U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[8U] 
        = __Vtemp_h18146fff__0[8U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[9U] 
        = __Vtemp_h18146fff__0[9U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xaU] 
        = __Vtemp_h18146fff__0[0xaU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xbU] 
        = __Vtemp_h18146fff__0[0xbU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xcU] 
        = __Vtemp_h18146fff__0[0xcU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xdU] 
        = __Vtemp_h18146fff__0[0xdU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xeU] 
        = __Vtemp_h18146fff__0[0xeU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xfU] 
        = __Vtemp_h18146fff__0[0xfU];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_sel 
        = ((0x3fU >= (0x1ffffffcU & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift) 
                                     << 2U))) ? (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel 
                                                 << 
                                                 (0x1ffffffcU 
                                                  & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift) 
                                                     << 2U)))
            : 0ULL);
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_cfg_dbl 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds) 
           & (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy 
        = (1U & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb)) 
                 | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy)));
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read 
        = ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)) 
           & (IData)(vlSelf->main__DOT__console__DOT__rxf_wb_read));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Av 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset
        [(0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))];
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Bv 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset
        [(0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))];
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__regid 
        = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
            << 4U) | (0xfU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim_immv));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_invalidate_result 
        = ((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
           | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellinp__u_sfifo__i_reset 
        = ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort) 
           | (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset));
    vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__exec_stb) 
           | (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_empty_n));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
           & (IData)(vlSelf->main__DOT__genbus__DOT__wbu_tx_stb));
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT____Vcellinp__UPSIZE__DOT__u_fifo__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_rd 
        = ((~ (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_empty)) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
              >> 3U));
    vlSelf->o_ddr3_controller_odelay_data_cntvaluein 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__lane];
    vlSelf->o_ddr3_controller_odelay_dqs_cntvaluein 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__lane];
    vlSelf->o_ddr3_controller_idelay_data_cntvaluein 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__lane];
    vlSelf->o_ddr3_controller_idelay_dqs_cntvaluein 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__lane];
    vlSelf->main__DOT__wbu_xbar__DOT__s_data[0U] = 
        vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__rtn_data[0xfU];
    vlSelf->main__DOT__wbu_xbar__DOT__s_data[1U] = vlSelf->main__DOT__wbu_zip_idata;
    vlSelf->main__DOT____Vcellinp__u_i2cdma__S_VALID 
        = ((IData)(vlSelf->main__DOT__i2c_valid) & 
           (2U == (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid)));
    vlSelf->main__DOT__u_i2cdma__DOT____Vcellinp__sskd__i_data 
        = (((IData)(vlSelf->main__DOT__i2c_last) << 8U) 
           | (IData)(vlSelf->main__DOT__i2c_data));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_cfg_dbl 
        = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds) 
           & (0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__diff 
        = (0x1ffffffffULL & ((QData)((IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
                                              >> 0x1fU))) 
                             - (QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor))));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)) 
           & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[1U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][1U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[2U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][2U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[3U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][3U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[4U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][4U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[5U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][5U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[6U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][6U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[7U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][7U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[8U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][8U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[9U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][9U];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xaU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0xaU];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xbU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0xbU];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xcU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0xcU];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xdU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0xdU];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xeU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0xeU];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xfU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0xfU];
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0x10U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr))][0x10U];
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__w_any 
        = (0U != ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable)));
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__w_any 
        = (0U != ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable)));
    vlSelf->main__DOT__genbus__DOT__rx_valid = ((IData)(vlSelf->main__DOT__wbu_rx_stb) 
                                                & ((IData)(vlSelf->main__DOT__wbu_rx_data) 
                                                   >> 7U));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__r_busy) 
           | (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__first_size 
        = (0x7fU & ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                     ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                         ? 1U : ((1U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)
                                  ? 1U : 2U)) : ((1U 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                                  ? 
                                                 ((IData)(4U) 
                                                  - 
                                                  (3U 
                                                   & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))
                                                  : 
                                                 ((IData)(0x40U) 
                                                  - 
                                                  (0x3fU 
                                                   & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)))));
    if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__first_size) 
         > (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__first_size 
            = (0x7fU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen));
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size;
    if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
        if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size = 1U;
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel 
                = (((QData)((IData)((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel)))) 
                    << 0x3fU) | (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel 
                                 >> 1U));
        } else {
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size 
                = ((3U == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len))
                    ? 1U : 2U);
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel 
                = (((QData)((IData)((3U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel)))) 
                    << 0x3eU) | (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel 
                                 >> 2U));
        }
    } else if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size 
            = (((4U <= (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len)) 
                & (8U > (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len)))
                ? (0x7fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len) 
                            - (IData)(4U))) : 4U);
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel 
            = (((QData)((IData)((0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel)))) 
                << 0x3cU) | (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel 
                             >> 4U));
    } else {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size = 0x40U;
        if ((0x40U > ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len) 
                      - (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size)))) {
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size 
                = (0x7fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len) 
                            - (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size)));
        }
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel = 0xffffffffffffffffULL;
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc)))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel;
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__last_request_addr 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr;
    if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__last_request_addr 
            = (0xfffffffU & ((vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr 
                              + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen)) 
                             - (IData)(1U)));
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift 
        = (0x3fU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill));
    if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid) 
         & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift 
            = (0x3fU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill));
    }
    vlSelf->io_emmc_dat_tristate = ((0x80U & ((~ ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                  & ((~ 
                                                      (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                       >> 0x1fU)) 
                                                     | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data)))) 
                                              << 7U)) 
                                    | ((0x40U & ((~ 
                                                  ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                   & ((~ 
                                                       (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                        >> 0x1eU)) 
                                                      | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data)))) 
                                                 << 6U)) 
                                       | ((0x20U & 
                                           ((~ ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                & ((~ 
                                                    (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                     >> 0x1dU)) 
                                                   | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data)))) 
                                            << 5U)) 
                                          | ((0x10U 
                                              & ((~ 
                                                  ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                   & ((~ 
                                                       (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                        >> 0x1cU)) 
                                                      | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data)))) 
                                                 << 4U)) 
                                             | ((8U 
                                                 & ((~ 
                                                     ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                      & ((~ 
                                                          (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                           >> 0x1bU)) 
                                                         | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data)))) 
                                                    << 3U)) 
                                                | (7U 
                                                   & (~ 
                                                      ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                         & ((~ 
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                              >> 0x1aU)) 
                                                            | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data))) 
                                                        << 2U) 
                                                       | ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                            & ((~ 
                                                                (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                                 >> 0x19U)) 
                                                               | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data))) 
                                                           << 1U) 
                                                          | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                             & ((~ 
                                                                 (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                                  >> 0x18U)) 
                                                                | (IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data))))))))))));
    if (vlSelf->cpu_sim_cyc) {
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_stb 
            = (1U & (IData)(vlSelf->cpu_sim_stb));
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_we 
            = (1U & (IData)(vlSelf->cpu_sim_we));
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr 
            = (0x7fU & (IData)(vlSelf->cpu_sim_addr));
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_data 
            = vlSelf->cpu_sim_data;
    } else {
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_stb 
            = (1U & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb) 
                     >> 1U));
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_we 
            = (1U & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_swe) 
                     >> 1U));
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr 
            = (0x7fU & (IData)((vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
                                >> 0x1bU)));
        vlSelf->main__DOT____Vcellinp__swic__i_dbg_data 
            = (IData)((vlSelf->main__DOT____Vcellout__wbu_xbar__o_sdata 
                       >> 0x20U));
    }
    vlSelf->main__DOT__u_i2cdma__DOT__skd_ready = (1U 
                                                   & ((IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_reset) 
                                                      | ((~ (IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc)) 
                                                         | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__bus_err))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb 
        = (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
            >> 6U) & (IData)(((0x40000U == (0x70000U 
                                            & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                              & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                 >> 6U))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb 
        = (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
            >> 8U) & ((4U == (7U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U])) 
                      & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                         >> 8U)));
    vlSelf->main__DOT__console__DOT__rxf_wb_data = 
        ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__osrc)
          ? (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__last_write)
          : (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_data));
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write 
        = ((IData)(vlSelf->main__DOT__w_console_rx_stb) 
           & ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow)) 
              | (IData)(vlSelf->main__DOT__console__DOT__rxf_wb_read)));
    vlSelf->main__DOT__i2cscopei__DOT__dw_trigger = 
        ((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_primed) 
         & (((~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config)) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__r_aborted)) 
            | ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
               >> 1U)));
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][1U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[1U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][2U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][3U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][4U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][5U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][6U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][7U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][8U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][9U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0xaU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0xbU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0xcU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0xdU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0xeU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0U][0xfU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][1U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[1U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][2U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][3U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][4U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][5U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][6U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][7U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][8U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][9U] 
        = vlSelf->main__DOT__wbwide_bkram_idata[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0xaU] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0xbU] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0xcU] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0xdU] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0xeU] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1U][0xfU] 
        = vlSelf->main__DOT__wbwide_bkram_idata[0xfU];
    vlSelf->main__DOT__i2c_ready = (1U & ((~ (IData)(vlSelf->main__DOT__i2c_valid)) 
                                          | ((0U == (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid)) 
                                             | ((1U 
                                                 == (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid)) 
                                                | (((~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid)) 
                                                    & (2U 
                                                       == (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid))) 
                                                   | (2U 
                                                      < (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid)))))));
    vlSelf->main__DOT__w_console_tx_data = ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__osrc)
                                             ? (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__last_write)
                                             : (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_data));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__mpy_result 
        = ((2U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_sgn))
            ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_smpy_result
            : vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_umpy_result);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__w_match 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table) 
           & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dmatch) 
              & (0xe00000000ULL == (0xe00000000ULL 
                                    & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word))));
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn 
        = (0xffU & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted)
                     ? vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]
                     : (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn)));
    if (((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle)) 
         & (0U == (0xf0U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn))))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn 
            = (0xf0U & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                        << 4U));
    }
    vlSelf->main__DOT__i2ci__DOT__next_insn = (0xffU 
                                               & ((IData)(vlSelf->main__DOT__i2ci__DOT__r_halted)
                                                   ? 
                                                  vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[3U]
                                                   : (IData)(vlSelf->main__DOT__i2ci__DOT__pf_insn)));
    if (((~ (IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle)) 
         & (0U == (0xf0U & (IData)(vlSelf->main__DOT__i2ci__DOT__next_insn))))) {
        vlSelf->main__DOT__i2ci__DOT__next_insn = (0xf0U 
                                                   & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                                      << 4U));
    }
    __Vtableidx10 = (7U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel 
        = Vmain__ConstPool__TABLE_h611c22d1_0[__Vtableidx10];
    vlSelf->io_sdcard_dat_tristate = (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__high_z) 
                                       << 3U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__high_z) 
                                                  << 2U) 
                                                 | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__high_z) 
                                                     << 1U) 
                                                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__high_z))));
    vlSelf->main__DOT__emmcscopei__DOT__write_to_control 
        = (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
            & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
           & ((~ vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U]) 
              & (0xfU == (0xfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel)))));
    vlSelf->main__DOT__emmcscopei__DOT__read_from_data 
        = ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
           & ((~ (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
              & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                 & (0xfU == (0xfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))))));
    vlSelf->main__DOT__sdioscopei__DOT__write_to_control 
        = ((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
             & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
            >> 2U) & ((~ (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                          >> 0x10U)) & (0xf00ULL == 
                                        (0xf00ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))));
    vlSelf->main__DOT__sdioscopei__DOT__read_from_data 
        = (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
            >> 2U) & ((~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                          >> 2U)) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                      >> 0x10U) & (0xf00ULL 
                                                   == 
                                                   (0xf00ULL 
                                                    & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel)))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_valid 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)) 
           & ((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch) 
                  | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp))) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid)));
    vlSelf->main__DOT__i2cscopei__DOT__write_to_control 
        = ((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
             & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
            >> 1U) & ((~ (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                          >> 8U)) & (0xf0ULL == (0xf0ULL 
                                                 & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))));
    vlSelf->main__DOT__i2cscopei__DOT__read_from_data 
        = (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
            >> 1U) & ((~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                          >> 1U)) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                      >> 8U) & (0xf0ULL 
                                                == 
                                                (0xf0ULL 
                                                 & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel)))));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__clear_table 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
           | ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
              & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)) 
                 & (0x200000000ULL == (0xe00000000ULL 
                                       & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword)))));
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][1U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][1U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][2U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][3U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][4U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][5U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][6U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][7U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][8U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][9U] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0xaU] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0xbU] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0xcU] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0xdU] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0xeU] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2U][0xfU] 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_we = ((8U 
                                                  & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0x12U] 
                                                     << 3U)) 
                                                 | ((4U 
                                                     & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0x12U] 
                                                        << 2U)) 
                                                    | ((2U 
                                                        & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0x12U] 
                                                           << 1U)) 
                                                       | (1U 
                                                          & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][4U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][5U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][6U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][7U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][8U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][9U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0xaU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0xbU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0xcU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0xdU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0xeU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0x10U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0U][0xfU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0x11U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][4U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][5U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][6U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][7U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][8U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][9U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0xaU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0xbU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0xcU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0xdU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0xeU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0x10U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1U][0xfU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0x11U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][4U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][5U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][6U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][7U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][8U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][9U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0xaU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0xbU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0xcU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0xdU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0xeU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0x10U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2U][0xfU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0x11U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][4U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][5U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][6U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][7U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][8U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][9U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0xaU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0xbU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0xcU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0xdU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0xeU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0x10U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3U][0xfU] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0x11U];
    vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[0U] 
        = (((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data[0U])));
    vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[1U] 
        = (((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data[0U])));
    vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[2U] 
        = (((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data[0U])));
    vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[3U] 
        = (((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data[0U])));
    vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_fill = 0U;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_fill 
        = ((0x3c0U & (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_fill)) 
           | (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcA_v = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcA_v 
        = ((0xf0000000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcA_v) 
           | (((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                      >> 4U)) == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie))
               ? (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc)
               : ((0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc) 
                  | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase) 
                     << 1U))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcB_v = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcB_v 
        = ((0xf0000000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcB_v) 
           | (((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                      >> 4U)) == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie))
               ? (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc)
               : ((0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc) 
                  | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase) 
                     << 1U))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc 
        = ((0xf0000000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc) 
           | ((0x10U & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))
               ? ((0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc) 
                  | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase) 
                     << 1U)) : ((0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ipc) 
                                | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_IHALT_PHASE__DOT__r_ihalt_phase) 
                                   << 1U))));
    vlSelf->main__DOT__wbwide_xbar__DOT__s_ack = ((0xfffffffcU 
                                                   & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc) 
                                                      & ((vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q
                                                          [0U] 
                                                          & (0xeU 
                                                             == (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__state_calibrate))) 
                                                         << 2U))) 
                                                  | ((0xfffffffeU 
                                                      & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc) 
                                                         & ((IData)(vlSelf->main__DOT__wbwide_bkram_ack) 
                                                            << 1U))) 
                                                     | ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc) 
                                                        & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_ack))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response 
        = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
           & ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
              & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb) 
                 & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount) 
                    == ((IData)(1U) + (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done 
        = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response) 
           & (((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
               & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_valid) 
                  & (3U <= (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr)))) 
              | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type) 
                 & (0x30U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
           & ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
              & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb) 
                 & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount) 
                    == ((IData)(1U) + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response) 
           & (((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
               & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_valid) 
                  & (3U <= (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr)))) 
              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type) 
                 & (0x30U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))));
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_fill = 0U;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_fill 
        = ((0x3c0U & (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_fill)) 
           | (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset 
        = ((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
           | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc));
    vlSelf->__VdfgTmp_ha46ae6a3__0 = ((2U & ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                                             >> 4U)) 
                                      | (1U & (~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow))));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__index = 5U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done 
        = (1U & (~ (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase) 
                       | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__pending_crc)) 
                      | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid)) 
                     | (0U != (0x18U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)))) 
                    | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid))));
    if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done = 1U;
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done = 0U;
    }
    __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
        = (((QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[1U])) 
            << 0x20U) | (QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[0U])));
    __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout = 0U;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0xfU;
    if ((0U != (0xfU & (IData)(__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel)))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0xeU;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 4U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0xdU;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 8U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0xcU;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0xcU))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0xbU;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x10U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0xaU;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x14U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 9U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x18U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 8U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x1cU))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 7U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x20U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 6U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x24U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 5U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x28U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 4U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x2cU))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 3U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x30U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 2U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x34U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 1U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x38U))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = 0U;
    if ((0U != (0xfU & (IData)((__Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__sel 
                                >> 0x3cU))))) {
        __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout 
            = (0xfU & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__i_subaddr 
        = __Vfunc_main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__71__Vfuncout;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done 
        = (1U & (~ (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase) 
                       | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__pending_crc)) 
                      | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid)) 
                     | (0U != (0x18U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)))) 
                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid))));
    if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done = 1U;
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done = 0U;
    }
    vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber3 
        = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
           | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid));
    vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber3 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
           | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_pc_valid 
        = ((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy))) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_alu_pc_valid));
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq_d 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dq;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_d 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dqs;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update = 1U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID 
        = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
           & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
           & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__tag_lookup 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__isrc)
            ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__pc_tag_lookup
            : vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_tag_lookup);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__s_tvalid 
        = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
           & ((~ ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn) 
                  >> 0xbU)) & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl 
        = (0xc0000000U | ((0x3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl) 
                          | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                             << 0x18U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl 
        = ((0xffc01fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl) 
           | (((IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_sample_shift) 
               << 0x10U) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown) 
                             << 0xfU) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90) 
                                          << 0xeU) 
                                         | ((IData)(vlSelf->main__DOT__u_emmc__DOT__pp_cmd) 
                                            << 0xdU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl 
        = ((0xffffe000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl) 
           | ((((IData)(vlSelf->main__DOT__u_emmc__DOT__pp_data) 
                << 0xcU) | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width) 
                            << 0xaU)) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds) 
                                          << 9U) | 
                                         (((IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr) 
                                           << 8U) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_ckspd)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl 
        = (0xc0000000U | ((0x3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl) 
                          | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                             << 0x18U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl 
        = ((0xffc01fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl) 
           | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_sample_shift) 
               << 0x10U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown) 
                             << 0xfU) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90) 
                                          << 0xeU) 
                                         | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_cmd) 
                                            << 0xdU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl 
        = ((0xffffe000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl) 
           | ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_data) 
                << 0xcU) | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width) 
                            << 0xaU)) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds) 
                                          << 9U) | 
                                         (((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr) 
                                           << 8U) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_ckspd)))));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg 
        = ((0x1fffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg) 
           | (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy) 
               << 0x1fU) | ((((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_err) 
                              | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err)) 
                             << 0x1eU) | ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_trigger) 
                                          << 0x1dU))));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg 
        = ((0xe0ffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_sel) 
              << 0x18U));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg 
        = ((0xfffff800U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg) 
           | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_transferlen));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg 
        = ((0xff8fffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg) 
           | ((0x400000U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_inc)) 
                            << 0x16U)) | ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_size) 
                                          << 0x14U)));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg 
        = ((0xfff8ffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg) 
           | ((0x40000U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_inc)) 
                           << 0x12U)) | ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size) 
                                         << 0x10U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready 
        = ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts)) 
           & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready 
        = ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts)) 
           & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
           & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb));
    vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr 
        = ((0xf0000000U & vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr) 
           | vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr);
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt 
        = vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[4U];
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb 
        = (0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x10U)));
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old 
        = vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr;
    vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__Vfuncout 
        = ((0xffffU & vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__Vfuncout) 
           | ((((8U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb))
                 ? (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt 
                    >> 0x18U) : (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old 
                                 >> 0x18U)) << 0x18U) 
              | (0xff0000U & (((4U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb))
                                ? (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt 
                                   >> 0x10U) : (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old 
                                                >> 0x10U)) 
                              << 0x10U))));
    vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__Vfuncout 
        = ((0xffff0000U & vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__Vfuncout) 
           | ((0xff00U & (((2U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb))
                            ? (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt 
                               >> 8U) : (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old 
                                         >> 8U)) << 8U)) 
              | (0xffU & ((1U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__strb))
                           ? __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__nxt
                           : __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__old))));
    vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr 
        = vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__Vfuncout;
    vlSelf->main__DOT__u_i2cdma__DOT__next_memlen = 0U;
    vlSelf->main__DOT__u_i2cdma__DOT__next_memlen = 
        ((0xf0000000U & vlSelf->main__DOT__u_i2cdma__DOT__next_memlen) 
         | vlSelf->main__DOT__u_i2cdma__DOT__r_memlen);
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt 
        = vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[4U];
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb 
        = (0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x10U)));
    __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old 
        = vlSelf->main__DOT__u_i2cdma__DOT__next_memlen;
    vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__Vfuncout 
        = ((0xffffU & vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__Vfuncout) 
           | ((((8U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb))
                 ? (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt 
                    >> 0x18U) : (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old 
                                 >> 0x18U)) << 0x18U) 
              | (0xff0000U & (((4U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb))
                                ? (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt 
                                   >> 0x10U) : (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old 
                                                >> 0x10U)) 
                              << 0x10U))));
    vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__Vfuncout 
        = ((0xffff0000U & vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__Vfuncout) 
           | ((0xff00U & (((2U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb))
                            ? (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt 
                               >> 8U) : (__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old 
                                         >> 8U)) << 8U)) 
              | (0xffU & ((1U & (IData)(__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__strb))
                           ? __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__nxt
                           : __Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__old))));
    vlSelf->main__DOT__u_i2cdma__DOT__next_memlen = vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__Vfuncout;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0U] = vlSelf->main__DOT__emmcscopei__DOT__o_bus_data;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[1U] = vlSelf->main__DOT__i2cscopei__DOT__o_bus_data;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[2U] = vlSelf->main__DOT__sdioscopei__DOT__o_bus_data;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[3U] = vlSelf->main__DOT__i2ci__DOT__bus_read_data;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[4U] = vlSelf->main__DOT__wb32_i2cdma_idata;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[5U] = vlSelf->main__DOT__wb32_uart_idata;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[6U] = vlSelf->main__DOT__wb32_emmc_idata;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[7U] = vlSelf->main__DOT__wb32_fan_idata;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[8U] = vlSelf->main__DOT__wb32_sdcard_idata;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[9U] = vlSelf->main__DOT__r_wb32_sio_data;
    vlSelf->main__DOT__wb32_xbar__DOT__s_data[0xbU] 
        = vlSelf->main__DOT__wb32_ddr3_phy_idata;
    main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q
        [1U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[0U] 
        = main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0;
    main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q
        [2U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[1U] 
        = main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0;
    main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q
        [3U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[2U] 
        = main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0;
    main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0 
        = vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q
        [4U];
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[3U] 
        = main__DOT__ddr3_controller_inst__DOT____Vlvbound_h60cbe704__0;
    vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[4U] = 0U;
    if (vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_pending) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update = 0U;
        if ((((IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q) 
              >> (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank)) 
             & (vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q
                [vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank] 
                == (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_row)))) {
            if (((IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_we) 
                 & (0U == vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q
                    [vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank]))) {
                vlSelf->main__DOT__ddr3_controller_inst__DOT__index = 8U;
                vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq_d = 1U;
                vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_d = 1U;
                vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update = 1U;
                vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[4U] 
                    = (1U | ((IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_aux) 
                             << 1U));
            } else if (((~ (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_we)) 
                        & (0U == vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q
                           [vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank]))) {
                vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update = 1U;
                vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[4U] 
                    = (1U | ((IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_aux) 
                             << 1U));
            }
        }
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word = 0U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xf0ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
               << 0x1bU) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request) 
                             << 0x1aU) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en) 
                                           << 0x19U) 
                                          | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request) 
                                             << 0x18U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr)) 
               << 0x15U) | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__dat0_busy) 
                            << 0x14U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xfff83fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode) 
               << 0x10U) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err) 
                             << 0xfU) | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
                                         << 0xeU))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xffffcfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo) 
              << 0xcU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | ((((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
                  | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
                 | (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en)) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request)) 
               | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
                  & (2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type)))) 
              << 0xbU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
               << 0xaU) | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type) 
                           << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xffffff80U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd));
    vlSelf->main__DOT__wb32_spio_stb = (IData)((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                                 >> 9U) 
                                                & (0x300U 
                                                   == 
                                                   (0x700U 
                                                    & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))));
    vlSelf->main__DOT__genbus__DOT__ofifo_rd = ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb)) 
                                                & (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_empty_n));
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd 
        = ((~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy)) 
           & (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n));
    vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0 
        = (((IData)(vlSelf->main__DOT__spio_int) << 3U) 
           | ((4U & ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                     >> 3U)) | ((2U & ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill) 
                                       >> 4U)) | (IData)(vlSelf->main__DOT__sdcard_int))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word = 0U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xf0ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
               << 0x1bU) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request) 
                             << 0x1aU) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en) 
                                           << 0x19U) 
                                          | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request) 
                                             << 0x18U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr)) 
               << 0x15U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__dat0_busy) 
                             << 0x14U) | (0x80000U 
                                          & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_present)) 
                                             << 0x13U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xfff83fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_removed) 
               << 0x12U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode) 
                             << 0x10U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err) 
                                           << 0xfU) 
                                          | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
                                             << 0xeU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xffffcfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo) 
              << 0xcU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | ((((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
                  | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
                 | (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en)) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request)) 
               | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
                  & (2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type)))) 
              << 0xbU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
               << 0xaU) | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type) 
                           << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word 
        = ((0xffffff80U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word) 
           | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd));
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy 
        = (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
            & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))) 
           & (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len) 
               == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)) 
              & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len))));
    if (((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
           & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))) 
          & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid))) 
         & (1U == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw)))) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy = 1U;
    }
    if (((((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid)) 
           & (1U == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw))) 
          & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len))) 
         & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len) 
            == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)))) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy = 1U;
    }
    vlSelf->o_emmc_dat = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                          >> 0x18U);
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_data 
        = (((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last) 
            << 4U) | (0xfU & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT____VdfgTmp_h05977c6b__0 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data
        [(0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr))];
    vlSelf->main__DOT__i2ci__DOT__s_tvalid = ((IData)(vlSelf->main__DOT__i2ci__DOT__insn_valid) 
                                              & ((~ 
                                                  ((IData)(vlSelf->main__DOT__i2ci__DOT__insn) 
                                                   >> 0xbU)) 
                                                 & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__r_wait))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_haf314c36__0 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch_stb));
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbu_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data 
        = (0xfULL | (((QData)((IData)(vlSelf->main__DOT__wbu_we)) 
                      << 0x3fU) | (((QData)((IData)(
                                                    (0x7ffffffU 
                                                     & vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr))) 
                                    << 0x24U) | ((QData)((IData)(vlSelf->main__DOT__wbu_data)) 
                                                 << 4U))));
    vlSelf->main__DOT__swic__DOT__dc_ack = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)) 
                                                  & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                                     >> 2U)));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last)) 
                 & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last)) 
                    & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid)) 
                       | ((0x40U > (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill)) 
                          | (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)))))));
    vlSelf->main__DOT__i2cscope_int = (IData)(((((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe) 
                                                 >> 4U) 
                                                & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config))) 
                                               & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_level_interrupt))));
    vlSelf->main__DOT__sdioscope_int = (IData)(((((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe) 
                                                  >> 4U) 
                                                 & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config))) 
                                                & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_level_interrupt))));
    vlSelf->main__DOT__emmcscope_int = (IData)(((((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe) 
                                                  >> 4U) 
                                                 & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config))) 
                                                & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_level_interrupt))));
    vlSelf->main__DOT__w_console_busy = ((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
                                         | (IData)(vlSelf->main__DOT__genbus__DOT__wbu_tx_stb));
    vlSelf->main__DOT__wb32_xbar__DOT__mindex[0U] = vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex;
    vlSelf->main__DOT__wbu_xbar__DOT__mindex[0U] = vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                             << 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                             << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                             << 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x80000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data 
        = ((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                       >> 0xfU)) | ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0xeU)) 
                                    | ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xdU)) 
                                       | ((0x1000U 
                                           & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                              >> 0xcU)) 
                                          | ((0x800U 
                                              & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                 >> 0xbU)) 
                                             | ((0x400U 
                                                 & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                    >> 0xaU)) 
                                                | ((0x200U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                       >> 9U)) 
                                                   | ((0x100U 
                                                       & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                          >> 8U)) 
                                                      | ((0x80U 
                                                          & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                             >> 7U)) 
                                                         | ((0x40U 
                                                             & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                >> 6U)) 
                                                            | ((0x20U 
                                                                & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                   >> 5U)) 
                                                               | ((0x10U 
                                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                      >> 4U)) 
                                                                  | ((8U 
                                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                         >> 3U)) 
                                                                     | ((4U 
                                                                         & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                            >> 2U)) 
                                                                        | ((2U 
                                                                            & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                               >> 1U)) 
                                                                           | (1U 
                                                                              & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data))))))))))))))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xfU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xeU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xdU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xcU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xbU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xaU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 9U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 8U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data 
        = ((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                       >> 0x10U)) | ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                 >> 0xfU)) 
                                     | ((0x2000U & 
                                         (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                          >> 0xeU)) 
                                        | ((0x1000U 
                                            & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                               >> 0xdU)) 
                                           | ((0x800U 
                                               & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                  >> 0xcU)) 
                                              | ((0x400U 
                                                  & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                     >> 0xbU)) 
                                                 | ((0x200U 
                                                     & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 0xaU)) 
                                                    | ((0x100U 
                                                        & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                           >> 9U)) 
                                                       | ((0x80U 
                                                           & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                              >> 8U)) 
                                                          | ((0x40U 
                                                              & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                 >> 7U)) 
                                                             | ((0x20U 
                                                                 & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                    >> 6U)) 
                                                                | ((0x10U 
                                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                       >> 5U)) 
                                                                   | ((8U 
                                                                       & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                          >> 4U)) 
                                                                      | ((4U 
                                                                          & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                             >> 3U)) 
                                                                         | ((2U 
                                                                             & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                                >> 2U)) 
                                                                            | (1U 
                                                                               & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                                                >> 1U)))))))))))))))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xfU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xeU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xdU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xcU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xbU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 0xaU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 9U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 8U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__36__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__35__Vfuncout) 
              << 0x10U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfffffff0U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                      >> 0xeU)) | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                         << 1U))) | 
              ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                      >> 0xfU)) | (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xffffff0fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                         >> 0xcU)) | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                               << 3U))) 
              | ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                           >> 0xdU)) | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                 << 2U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfffff0ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                          >> 0xaU)) | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                 << 5U))) 
              | ((0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                            >> 0xbU)) | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   << 4U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xffff0fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                           >> 8U)) | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                 << 7U))) 
              | ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                             >> 9U)) | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   << 6U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfff0ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                            >> 6U)) | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   << 9U))) 
              | ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                              >> 7U)) | (0x10000U & 
                                         (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                          << 8U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xff0fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                             >> 4U)) | (0x400000U & 
                                        (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                         << 0xbU))) 
              | ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                               >> 5U)) | (0x100000U 
                                          & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                             << 0xaU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xf0ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                              >> 2U)) | (0x4000000U 
                                         & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                            << 0xdU))) 
              | ((0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                >> 3U)) | (0x1000000U 
                                           & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                              << 0xcU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x80000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w) 
               | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                 << 0xfU))) | ((0x20000000U 
                                                & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   >> 1U)) 
                                               | (0x10000000U 
                                                  & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                     << 0xeU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffffeULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | (IData)((IData)((1U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffeffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 1U))))) 
              << 0x10U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffeffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 2U))))) 
              << 0x20U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffeffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 3U))))) 
              << 0x30U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffffdULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 4U))))) 
              << 1U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffdffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 5U))))) 
              << 0x11U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffdffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 6U))))) 
              << 0x21U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffdffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 7U))))) 
              << 0x31U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffffbULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 8U))))) 
              << 2U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffbffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 9U))))) 
              << 0x12U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffbffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xaU))))) 
              << 0x22U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffbffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xbU))))) 
              << 0x32U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffff7ULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xcU))))) 
              << 3U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffff7ffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xdU))))) 
              << 0x13U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffff7ffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xeU))))) 
              << 0x23U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfff7ffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xfU))))) 
              << 0x33U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffffefULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x10U))))) 
              << 4U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffefffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x11U))))) 
              << 0x14U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffefffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x12U))))) 
              << 0x24U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffefffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x13U))))) 
              << 0x34U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffffdfULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x14U))))) 
              << 5U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffdfffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x15U))))) 
              << 0x15U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffdfffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x16U))))) 
              << 0x25U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffdfffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x17U))))) 
              << 0x35U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffffbfULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x18U))))) 
              << 6U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffbfffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x19U))))) 
              << 0x16U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffbfffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1aU))))) 
              << 0x26U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffbfffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1bU))))) 
              << 0x36U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffff7fULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1cU))))) 
              << 7U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffff7fffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1dU))))) 
              << 0x17U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffff7fffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1eU))))) 
              << 0x27U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xff7fffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1fU))))) 
              << 0x37U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffeffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x20U))))) 
              << 8U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffeffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x21U))))) 
              << 0x18U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffeffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x22U))))) 
              << 0x28U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfeffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x23U))))) 
              << 0x38U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffdffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x24U))))) 
              << 9U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffdffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x25U))))) 
              << 0x19U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffdffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x26U))))) 
              << 0x29U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfdffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x27U))))) 
              << 0x39U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffbffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x28U))))) 
              << 0xaU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffbffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x29U))))) 
              << 0x1aU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffbffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2aU))))) 
              << 0x2aU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfbffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2bU))))) 
              << 0x3aU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffff7ffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2cU))))) 
              << 0xbU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffff7ffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2dU))))) 
              << 0x1bU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffff7ffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2eU))))) 
              << 0x2bU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xf7ffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2fU))))) 
              << 0x3bU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffefffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x30U))))) 
              << 0xcU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffefffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x31U))))) 
              << 0x1cU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffefffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x32U))))) 
              << 0x2cU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xefffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x33U))))) 
              << 0x3cU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffdfffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x34U))))) 
              << 0xdU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffdfffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x35U))))) 
              << 0x1dU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffdfffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x36U))))) 
              << 0x2dU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xdfffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x37U))))) 
              << 0x3dU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffbfffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x38U))))) 
              << 0xeU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffbfffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x39U))))) 
              << 0x1eU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffbfffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3aU))))) 
              << 0x2eU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xbfffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3bU))))) 
              << 0x3eU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffff7fffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3cU))))) 
              << 0xfU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffff7fffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3dU))))) 
              << 0x1fU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffff7fffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3eU))))) 
              << 0x2fU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0x7fffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3fU))))) 
              << 0x3fU));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x15U)) | ((0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x12U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0xfU)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xcU)) 
                                         | ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 9U)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 6U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 3U)) 
                                                  | (1U 
                                                     & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data))))))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior 
        = (0xffffU & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
        = ((0xffffffffffff0000ULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | (IData)((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x16U)) | ((0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x13U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0x10U)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xdU)) 
                                         | ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xaU)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 7U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 4U)) 
                                                  | (1U 
                                                     & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 1U)))))))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior 
        = (0xffffU & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
                              >> 0x10U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
        = ((0xffffffff0000ffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | ((QData)((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout)) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x17U)) | ((0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x14U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0x11U)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xeU)) 
                                         | ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xbU)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 8U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 5U)) 
                                                  | (1U 
                                                     & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 2U)))))))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior 
        = (0xffffU & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
                              >> 0x20U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
        = ((0xffff0000ffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | ((QData)((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout)) 
              << 0x20U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x18U)) | ((0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x15U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0x12U)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xfU)) 
                                         | ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xcU)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 9U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 6U)) 
                                                  | (1U 
                                                     & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 3U)))))))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior 
        = (0xffffU & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
                              >> 0x30U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__38__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
        = ((0xffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | ((QData)((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__37__Vfuncout)) 
              << 0x30U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffffff8ULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | (IData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                              >> 0x20U)) 
                                     << 2U)) | ((2U 
                                                 & ((IData)(
                                                            (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                             >> 0x10U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w)))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffffff7ULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x30U))))) 
              << 3U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffffff8fULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x21U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x11U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 1U))))))) 
              << 4U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffffff7fULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x31U))))) 
              << 7U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffff8ffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x22U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x12U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 2U))))))) 
              << 8U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffff7ffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x32U))))) 
              << 0xbU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffff8fffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x23U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x13U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 3U))))))) 
              << 0xcU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffff7fffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x33U))))) 
              << 0xfU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffff8ffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x24U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x14U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 4U))))))) 
              << 0x10U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffff7ffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x34U))))) 
              << 0x13U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffff8fffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x25U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x15U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 5U))))))) 
              << 0x14U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffff7fffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x35U))))) 
              << 0x17U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffff8ffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x26U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x16U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 6U))))))) 
              << 0x18U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffff7ffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x36U))))) 
              << 0x1bU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffff8fffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x27U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x17U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 7U))))))) 
              << 0x1cU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffff7fffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x37U))))) 
              << 0x1fU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffff8ffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x28U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x18U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 8U))))))) 
              << 0x20U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffff7ffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x38U))))) 
              << 0x23U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffff8fffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x29U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x19U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 9U))))))) 
              << 0x24U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffff7fffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x39U))))) 
              << 0x27U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffff8ffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2aU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1aU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xaU))))))) 
              << 0x28U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffff7ffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3aU))))) 
              << 0x2bU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffff8fffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2bU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1bU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xbU))))))) 
              << 0x2cU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffff7fffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3bU))))) 
              << 0x2fU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfff8ffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2cU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1cU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xcU))))))) 
              << 0x30U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfff7ffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3cU))))) 
              << 0x33U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xff8fffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2dU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1dU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xdU))))))) 
              << 0x34U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xff7fffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3dU))))) 
              << 0x37U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xf8ffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2eU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1eU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xeU))))))) 
              << 0x38U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xf7ffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3eU))))) 
              << 0x3bU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0x8fffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2fU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1fU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xfU))))))) 
              << 0x3cU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0x7fffffffffffffffULL & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3fU))))) 
              << 0x3fU));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x10U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x12U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x14U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x1bU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x10U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x10U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x10U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x8000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x1bU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x14U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x12U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x10U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x80000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U]));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x15U)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0xeU)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 7U)) | (1U 
                                                   & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x16U)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0xfU)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 8U)) | (1U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 1U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x17U)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x10U)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 9U)) | (1U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 2U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x18U)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x11U)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xaU)) | 
                                 (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 3U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x19U)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x12U)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xbU)) | 
                                 (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 4U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1aU)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x13U)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xcU)) | 
                                 (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 5U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1bU)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x14U)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xdU)) | 
                                 (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 6U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1cU)) | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x15U)) | 
                                ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xeU)) | 
                                 (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 7U)))));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__40__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__39__Vfuncout) 
              << 0x10U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     << 2U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 0xfU)) | 
                                (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U]))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0xbU)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                        << 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                      >> 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 9U)) | (0x40U 
                                                  & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                                     << 6U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        << 9U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 8U)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         << 7U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 4U)) | 
                             ((0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                          << 0xbU)) 
                              | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                           >> 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 2U)) | 
                             (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         << 0xdU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 0x10U)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             >> 1U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 0xeU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           << 3U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 0x12U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               << 1U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 5U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0x14U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0x17U)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 6U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 0x15U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             << 0xaU)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0x19U)) 
                                | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                 << 8U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xc0000000U & ((0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0xcU)) 
                             | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0x1bU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     >> 2U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 0x13U)) | 
                                (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 4U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0xfU)) | 
                             ((0x10U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U]) 
                              | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                       >> 0x11U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 0xdU)) | 
                             (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       << 2U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        << 5U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 0xcU)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         << 3U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 8U)) | 
                             ((0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                          << 7U)) | 
                              (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                         >> 0xaU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 6U)) | 
                             (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         << 9U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 0xcU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             >> 5U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 0xaU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           >> 1U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 0xeU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               >> 3U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 1U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0x10U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0x13U)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 2U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 0x11U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             << 6U)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0x15U)) 
                                | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                 << 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xc0000000U & ((0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 8U)) 
                             | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0x17U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     >> 6U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 0x17U)) | 
                                (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 8U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0x13U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                        >> 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                      >> 0x15U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 0x11U)) | 
                             (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 2U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        << 1U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 0x10U)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         >> 1U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 0xcU)) 
                             | ((0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                            << 3U)) 
                                | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                             >> 0xeU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 0xaU)) 
                             | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 5U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 8U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                           >> 9U)) 
                              | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             << 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           >> 5U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 0xaU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               >> 7U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           >> 3U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0xcU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0xfU)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               >> 2U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             << 2U)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0x11U)) 
                                | (0x8000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U])))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xc0000000U & ((0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 4U)) 
                             | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0x13U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     >> 0xaU)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                         >> 0x1bU)) 
                                  | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                           >> 0xcU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0x17U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                        >> 8U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                      >> 0x19U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 0x15U)) | 
                             (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 6U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        >> 3U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 0x14U)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         >> 5U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 0x10U)) 
                             | ((0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                            >> 1U)) 
                                | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                             >> 0x12U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 0xeU)) 
                             | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 1U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 4U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                           >> 0xdU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             << 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           >> 9U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 6U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               >> 0xbU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           >> 7U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 8U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0xbU)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               >> 6U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 9U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             >> 2U)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0xdU)) 
                                | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                 >> 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xc0000000U & ((0x80000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U]) 
                             | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0xfU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x20000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x1bU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x1dU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (4U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x80000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x1bU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x10U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x200000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x40U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x800000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x100U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x2000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            >> 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x400U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x8000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            >> 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x1bU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x1000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x20000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             >> 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x1dU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x1bU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x19U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x17U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x15U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x13U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x11U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x4000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U]));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x80000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U]));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0xfU)) | (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x10U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x11U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 2U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x12U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 3U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x13U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 4U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x14U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 5U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x15U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 6U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x16U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 7U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x17U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 8U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x18U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 9U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x19U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xaU)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1aU)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xbU)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1bU)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xcU)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1cU)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xdU)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1dU)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xeU)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]) 
           | (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1eU)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xfU)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior 
        = (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__i_crc_data));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__42__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout 
        = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
        = ((0xffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]) 
           | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__41__Vfuncout) 
              << 0x10U));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     << 2U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0xfU)) | 
                                (1U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0xbU)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        << 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 8U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 9U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         << 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 5U)) | (
                                                   (0x400U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                                       << 0xaU)) 
                                                   | (0x200U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                         >> 7U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 0xeU)) 
                             | ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 3U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              << 0xcU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 1U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0x11U)) 
                             | ((0x20000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]) 
                                | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 0xfU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           << 4U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0x13U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               << 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x17U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              << 6U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0x15U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 0xaU)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x19U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 8U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x1dU)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 0xcU)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x1bU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 0xeU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | ((4U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U]) 
              | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                        >> 0x11U)) | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                            >> 2U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0xdU)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        << 2U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0xfU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 6U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0xbU)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         << 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 7U)) | (
                                                   (0x400U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                                       << 8U)) 
                                                   | (0x200U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                         >> 9U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 0xcU)) 
                             | ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 5U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              << 0xaU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 3U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0xfU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             >> 2U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           << 2U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0x11U)) 
                                | (0x80000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U])))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x15U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              << 4U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0x13U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 8U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x17U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x1bU)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 0xaU)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x19U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 0xcU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 2U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x13U)) | 
                                (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 4U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0xfU)) | 
                             ((0x10U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
                              | (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                       >> 0x11U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 4U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0xdU)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         << 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 9U)) | (
                                                   (0x400U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                                       << 6U)) 
                                                   | (0x200U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                         >> 0xbU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 0xaU)) 
                             | ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 7U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              << 8U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 5U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0xdU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             >> 4U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 0xbU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfff80000U & ((0x200000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0xfU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x13U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              << 2U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0x11U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 6U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x15U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x19U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 8U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x17U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 0xaU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 4U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x15U)) | 
                                (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 6U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x11U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 2U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x13U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 2U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0xfU)) 
                                                   | (0x40U 
                                                      & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U])))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0xbU)) | 
                             ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                         << 4U)) | 
                              (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                         >> 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 8U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 9U)) | 
                              (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          << 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 7U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0xbU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             >> 6U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 9U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 2U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0xdU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x11U)) 
                             | ((0x800000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U]) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0xfU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 4U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x13U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x17U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 6U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x15U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 8U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 6U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x17U)) | 
                                (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 8U)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x13U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x15U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xffffffc0U & ((0x100U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U]) 
                             | ((0x80U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                          >> 0x11U)) 
                                | (0x40U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                            >> 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0xdU)) | 
                             ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                         << 2U)) | 
                              (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                         >> 0xfU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 6U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 0xbU)) 
                              | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            << 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 9U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 9U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 8U)) 
                              | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 7U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 4U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0xbU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0xfU)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 2U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 2U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x11U)) 
                                | (0x2000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U])))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x15U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 4U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x13U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 6U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 8U)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x19U)) | 
                                (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0xaU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x15U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 6U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x17U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        >> 2U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0x13U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         >> 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0xfU)) | 
                             ((0x400U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
                              | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                           >> 0x11U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 4U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 0xdU)) 
                              | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            << 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 7U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xaU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 5U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 6U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 9U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 8U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0xdU)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 4U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0xbU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfe000000U & ((0x8000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0xfU)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 >> 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x13U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 2U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x11U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 4U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 0xaU)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                         >> 0x1bU)) 
                                  | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xcU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x17U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 8U)) | (8U 
                                                   & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x19U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        >> 4U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0x15U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         >> 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0x11U)) 
                             | ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                           >> 2U)) 
                                | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                             >> 0x13U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 2U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 0xfU)) 
                              | (0x1000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U])))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 5U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xcU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 3U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 8U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 7U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 0xaU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0xbU)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 6U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 9U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            >> 2U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0xdU)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 >> 4U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x11U)) 
                             | ((0x20000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U]) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0xfU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 2U)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | ((4U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 0xcU)) | ((2U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                         >> 0x1dU)) 
                                  | (1U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xeU)))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x19U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 0xaU)) | 
                              (8U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                     >> 0x1bU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        >> 6U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0x17U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         >> 8U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0x13U)) 
                             | ((0x400U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                           >> 4U)) 
                                | (0x200U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                             >> 0x15U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfffff000U & ((0x4000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]) 
                             | ((0x2000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 0x11U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              >> 2U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0x8000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 3U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xeU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 1U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 0xaU)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 5U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 0xcU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 9U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 8U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 7U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            >> 4U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0xbU)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 >> 6U))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0xfU)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                >> 2U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0xdU))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0x80000000U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    >> 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                          << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                       >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                           << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                        >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                            << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                             << 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                             << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                             << 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                         >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w) 
           | (0x80000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data 
        = ((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                       >> 0xfU)) | ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0xeU)) 
                                    | ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xdU)) 
                                       | ((0x1000U 
                                           & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                              >> 0xcU)) 
                                          | ((0x800U 
                                              & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                 >> 0xbU)) 
                                             | ((0x400U 
                                                 & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                    >> 0xaU)) 
                                                | ((0x200U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                       >> 9U)) 
                                                   | ((0x100U 
                                                       & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                          >> 8U)) 
                                                      | ((0x80U 
                                                          & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                             >> 7U)) 
                                                         | ((0x40U 
                                                             & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                >> 6U)) 
                                                            | ((0x20U 
                                                                & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                   >> 5U)) 
                                                               | ((0x10U 
                                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                      >> 4U)) 
                                                                  | ((8U 
                                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                         >> 3U)) 
                                                                     | ((4U 
                                                                         & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                            >> 2U)) 
                                                                        | ((2U 
                                                                            & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                               >> 1U)) 
                                                                           | (1U 
                                                                              & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data))))))))))))))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xfU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xeU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xdU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xcU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xbU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xaU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 9U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 8U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data 
        = ((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                       >> 0x10U)) | ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                 >> 0xfU)) 
                                     | ((0x2000U & 
                                         (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                          >> 0xeU)) 
                                        | ((0x1000U 
                                            & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                               >> 0xdU)) 
                                           | ((0x800U 
                                               & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                  >> 0xcU)) 
                                              | ((0x400U 
                                                  & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                     >> 0xbU)) 
                                                 | ((0x200U 
                                                     & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 0xaU)) 
                                                    | ((0x100U 
                                                        & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                           >> 9U)) 
                                                       | ((0x80U 
                                                           & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                              >> 8U)) 
                                                          | ((0x40U 
                                                              & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                 >> 7U)) 
                                                             | ((0x20U 
                                                                 & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                    >> 6U)) 
                                                                | ((0x10U 
                                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                       >> 5U)) 
                                                                   | ((8U 
                                                                       & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                          >> 4U)) 
                                                                      | ((4U 
                                                                          & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                             >> 3U)) 
                                                                         | ((2U 
                                                                             & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                                >> 2U)) 
                                                                            | (1U 
                                                                               & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                                                >> 1U)))))))))))))))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xfU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xeU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xdU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xcU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xbU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 0xaU));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 9U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 8U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__78__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC16__77__Vfuncout) 
              << 0x10U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfffffff0U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                      >> 0xeU)) | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                         << 1U))) | 
              ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                      >> 0xfU)) | (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xffffff0fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                         >> 0xcU)) | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                               << 3U))) 
              | ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                           >> 0xdU)) | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                 << 2U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfffff0ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                          >> 0xaU)) | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                 << 5U))) 
              | ((0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                            >> 0xbU)) | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   << 4U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xffff0fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                           >> 8U)) | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                 << 7U))) 
              | ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                             >> 9U)) | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   << 6U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfff0ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                            >> 6U)) | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   << 9U))) 
              | ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                              >> 7U)) | (0x10000U & 
                                         (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                          << 8U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xff0fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                             >> 4U)) | (0x400000U & 
                                        (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                         << 0xbU))) 
              | ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                               >> 5U)) | (0x100000U 
                                          & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                             << 0xaU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xf0ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                              >> 2U)) | (0x4000000U 
                                         & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                            << 0xdU))) 
              | ((0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                >> 3U)) | (0x1000000U 
                                           & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                              << 0xcU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w 
        = ((0xfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w) 
           | (((0x80000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w) 
               | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                 << 0xfU))) | ((0x20000000U 
                                                & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                   >> 1U)) 
                                               | (0x10000000U 
                                                  & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w 
                                                     << 0xeU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffffeULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | (IData)((IData)((1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffeffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 1U))))) 
              << 0x10U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffeffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 2U))))) 
              << 0x20U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffeffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 3U))))) 
              << 0x30U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffffdULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 4U))))) 
              << 1U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffdffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 5U))))) 
              << 0x11U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffdffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 6U))))) 
              << 0x21U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffdffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 7U))))) 
              << 0x31U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffffbULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 8U))))) 
              << 2U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffbffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 9U))))) 
              << 0x12U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffbffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xaU))))) 
              << 0x22U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffbffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xbU))))) 
              << 0x32U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffff7ULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xcU))))) 
              << 3U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffff7ffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xdU))))) 
              << 0x13U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffff7ffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xeU))))) 
              << 0x23U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfff7ffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0xfU))))) 
              << 0x33U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffffefULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x10U))))) 
              << 4U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffefffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x11U))))) 
              << 0x14U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffefffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x12U))))) 
              << 0x24U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffefffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x13U))))) 
              << 0x34U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffffdfULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x14U))))) 
              << 5U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffdfffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x15U))))) 
              << 0x15U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffdfffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x16U))))) 
              << 0x25U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffdfffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x17U))))) 
              << 0x35U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffffbfULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x18U))))) 
              << 6U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffbfffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x19U))))) 
              << 0x16U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffbfffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1aU))))) 
              << 0x26U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffbfffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1bU))))) 
              << 0x36U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffff7fULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1cU))))) 
              << 7U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffff7fffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1dU))))) 
              << 0x17U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffff7fffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1eU))))) 
              << 0x27U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xff7fffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x1fU))))) 
              << 0x37U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffeffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x20U))))) 
              << 8U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffeffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x21U))))) 
              << 0x18U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffeffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x22U))))) 
              << 0x28U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfeffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x23U))))) 
              << 0x38U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffdffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x24U))))) 
              << 9U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffdffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x25U))))) 
              << 0x19U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffdffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x26U))))) 
              << 0x29U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfdffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x27U))))) 
              << 0x39U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffffbffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x28U))))) 
              << 0xaU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffbffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x29U))))) 
              << 0x1aU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffbffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2aU))))) 
              << 0x2aU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfbffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2bU))))) 
              << 0x3aU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffffffff7ffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2cU))))) 
              << 0xbU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffffffff7ffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2dU))))) 
              << 0x1bU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xfffff7ffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2eU))))) 
              << 0x2bU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xf7ffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x2fU))))) 
              << 0x3bU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffefffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x30U))))) 
              << 0xcU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffefffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x31U))))) 
              << 0x1cU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffefffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x32U))))) 
              << 0x2cU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xefffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x33U))))) 
              << 0x3cU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffdfffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x34U))))) 
              << 0xdU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffdfffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x35U))))) 
              << 0x1dU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffdfffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x36U))))) 
              << 0x2dU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xdfffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x37U))))) 
              << 0x3dU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffffbfffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x38U))))) 
              << 0xeU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffbfffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x39U))))) 
              << 0x1eU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffbfffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3aU))))) 
              << 0x2eU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xbfffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3bU))))) 
              << 0x3eU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffffffff7fffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3cU))))) 
              << 0xfU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffffffff7fffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3dU))))) 
              << 0x1fU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0xffff7fffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3eU))))) 
              << 0x2fU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
        = ((0x7fffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                             >> 0x3fU))))) 
              << 0x3fU));
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x15U)) | ((0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x12U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0xfU)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xcU)) 
                                         | ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 9U)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 6U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 3U)) 
                                                  | (1U 
                                                     & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data))))))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior 
        = (0xffffU & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 4U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & (IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
        = ((0xffffffffffff0000ULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | (IData)((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout)));
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x16U)) | ((0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x13U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0x10U)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xdU)) 
                                         | ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xaU)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 7U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 4U)) 
                                                  | (1U 
                                                     & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 1U)))))))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior 
        = (0xffffU & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
                              >> 0x10U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 7U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 6U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill 
        = vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit 
        = (1U & ((IData)(vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data) 
                 >> 5U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__fill;
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__prior) 
                                                    << 1U)));
}
