// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vmain.h for the primary calling header

#include "verilated.h"
#include "verilated_dpi.h"

#include "Vmain__Syms.h"
#include "Vmain___024root.h"

extern const VlWide<15>/*479:0*/ Vmain__ConstPool__CONST_hbd99daea_0;

VL_INLINE_OPT void Vmain___024root___nba_sequent__TOP__3(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___nba_sequent__TOP__3\n"); );
    // Init
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
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
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior = 0;
    CData/*1:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit = 0;
    VlWide<16>/*511:0*/ __Vtemp_hb780e8f4__0;
    VlWide<16>/*511:0*/ __Vtemp_hdb251f8c__0;
    VlWide<16>/*511:0*/ __Vtemp_h12b8adbe__0;
    // Body
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
    if ((1U & (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid)) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b
            [(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
               & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo))
               ? (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
               : (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))];
    }
    if ((1U & (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid)) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a
            [(((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo)) 
               & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en))
               ? (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
               : (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))];
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed = 0xfcU;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb) 
                & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x20U)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed 
            = (0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]);
        if ((0U == (0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed = 1U;
        }
    }
    if (vlSelf->i_reset) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__counter = 0U;
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb = 0U;
        vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual = 0U;
        vlSelf->main__DOT__i2ci__DOT__insn = 0U;
        vlSelf->main__DOT__u_i2cdma__DOT__r_reset = 1U;
    } else {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__counter 
            = (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk) 
                & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown))
                ? 0x300U : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter));
        if (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_busy)))) {
            vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb = 1U;
        } else if (((0U == (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len)) 
                    & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy)))) {
            vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__i2ci__DOT__bus_write) 
              & (0x1000000U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U]))) 
             & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                        >> 0xdU)))) {
            vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual 
                = (1U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[3U] 
                         >> 0xbU));
        } else if (vlSelf->main__DOT__i2ci__DOT__bus_jump) {
            vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual = 0U;
        }
        if (vlSelf->main__DOT__i2ci__DOT__next_valid) {
            vlSelf->main__DOT__i2ci__DOT__insn = ((IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle)
                                                   ? 
                                                  ((0xf00U 
                                                    & (IData)(vlSelf->main__DOT__i2ci__DOT__insn)) 
                                                   | (IData)(vlSelf->main__DOT__i2ci__DOT__next_insn))
                                                   : 
                                                  ((0xffU 
                                                    & (IData)(vlSelf->main__DOT__i2ci__DOT__insn)) 
                                                   | (0xf00U 
                                                      & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                                         << 4U))));
        } else if (((~ (IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle)) 
                    & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready))) {
            vlSelf->main__DOT__i2ci__DOT__insn = ((0xffU 
                                                   & (IData)(vlSelf->main__DOT__i2ci__DOT__insn)) 
                                                  | ((IData)(vlSelf->main__DOT__i2ci__DOT__half_insn) 
                                                     << 8U));
        }
        if ((0x10U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                      & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)))) {
            if ((2U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) {
                vlSelf->main__DOT__u_i2cdma__DOT__r_reset = 1U;
            }
        } else if ((1U & (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                             >> 4U)))) {
            vlSelf->main__DOT__u_i2cdma__DOT__r_reset 
                = (((0U == vlSelf->main__DOT__u_i2cdma__DOT__r_memlen) 
                    | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__bus_err)) 
                   | (0x10000000U <= (vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr 
                                      + vlSelf->main__DOT__u_i2cdma__DOT__r_memlen)));
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en)) 
                  & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID) 
                & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_ready))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = 0xffffffffU;
        if ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
            if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) {
                vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w;
            }
        }
    } else if (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb) 
                  & (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                 & (1U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                & (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = 0xffffffffU;
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid)) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_last 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_last;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
            = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo)
                ? vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b
                : vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a);
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_last 
            = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
               & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr) 
                  >= (0xffffU & (((0xfU >= ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                            - (IData)(2U)))
                                   ? ((IData)(1U) << 
                                      ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                       - (IData)(2U)))
                                   : 0U) - (IData)(1U)))));
    }
    if ((((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
            | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active)) 
           | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request) 
              & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy)))) 
          | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response)) 
         | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))) {
        if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = 1U;
            if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err) 
                 | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response) 
                    & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type) 
                         >> 1U) & ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                                   & (0x30U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))) 
                       | ((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
                          & ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                             & (0x88U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))))))) {
                vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = 3U;
            }
            if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) 
                 & (9U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill)))) {
                vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = 2U;
            }
        } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = 0U;
        }
    }
    if ((1U & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase)) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err = 0U;
    } else {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc)));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc)));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc)));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc)));
    }
    if ((((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
            | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active)) 
           | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request) 
              & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy)))) 
          | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response)) 
         | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))) {
        if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = 1U;
            if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err) 
                 | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response) 
                    & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type) 
                         >> 1U) & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                                   & (0x30U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))) 
                       | ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
                          & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                             & (0x88U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))))))) {
                vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = 3U;
            }
            if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) 
                 & (9U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill)))) {
                vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = 2U;
            }
        } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = 0U;
        }
    }
    if ((1U & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase)) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err = 0U;
    } else {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc)));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc)));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc)));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err 
            = ((((0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc)) 
                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)) 
                << 1U) | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc)));
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__dw_bits;
    vlSelf->main__DOT__i2cscopei__DOT__ck_addr = vlSelf->__Vdly__main__DOT__i2cscopei__DOT__ck_addr;
    vlSelf->main__DOT__i2cscopei__DOT__dr_force_write 
        = vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_write;
    vlSelf->main__DOT__i2cscopei__DOT__dr_stopped = vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stopped;
    vlSelf->main__DOT__emmcscopei__DOT__ck_addr = vlSelf->__Vdly__main__DOT__emmcscopei__DOT__ck_addr;
    vlSelf->main__DOT__emmcscopei__DOT__dr_force_write 
        = vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_write;
    vlSelf->main__DOT__emmcscopei__DOT__dr_stopped 
        = vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stopped;
    vlSelf->main__DOT__sdioscopei__DOT__ck_addr = vlSelf->__Vdly__main__DOT__sdioscopei__DOT__ck_addr;
    vlSelf->main__DOT__sdioscopei__DOT__dr_force_write 
        = vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_write;
    vlSelf->main__DOT__sdioscopei__DOT__dr_stopped 
        = vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stopped;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
              | (IData)(vlSelf->main__DOT__wbwide_wbu_arbiter_stb)));
    vlSelf->main__DOT__wbu_xbar__DOT__sgrant = vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest) 
              >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest) 
              >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid) 
           & (0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS 
        = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU];
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid;
    vlSelf->main__DOT__i2ci__DOT__pf_valid = vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_valid;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr;
    if (vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v0) {
        vlSelf->main__DOT__wb32_xbar__DOT__grant[0U] = 0U;
    }
    if (vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v1) {
        vlSelf->main__DOT__wb32_xbar__DOT__grant[0U] 
            = vlSelf->__Vdlyvval__main__DOT__wb32_xbar__DOT__grant__v1;
    }
    if (vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v2) {
        vlSelf->main__DOT__wb32_xbar__DOT__grant[0U] = 0U;
    }
    if (vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0] 
            = vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr;
    vlSelf->main__DOT__swic__DOT__cpu_lcl_cyc = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner) 
                                                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_lcl));
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc;
    vlSelf->main__DOT__u_fan__DOT__trigger_counter 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__trigger_counter;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_i2cdma_stb) 
              | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem
        [(0x1fU & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr))];
    if (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_empty) {
        vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data 
            = vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_data;
    }
    vlSelf->main__DOT__swic__DOT__wdbus_int = vlSelf->__Vdly__main__DOT__swic__DOT__wdbus_int;
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable 
        = vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable;
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state 
        = vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state;
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable 
        = vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable;
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state 
        = vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length 
        = vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length;
    vlSelf->main__DOT__console__DOT__txf_status = (0x6000U 
                                                   | (((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_fill) 
                                                       << 2U) 
                                                      | (IData)(vlSelf->__VdfgTmp_ha46ae6a3__0)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate;
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3))) 
                & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3))));
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc;
    vlSelf->main__DOT__i2cscopei__DOT__new_data = (1U 
                                                   & ((~ 
                                                       ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                                                        >> 2U)) 
                                                      | (vlSelf->main__DOT____Vcellinp__i2cscopei____pinNumber4 
                                                         != vlSelf->main__DOT__i2cscopei__DOT__qd_data)));
    vlSelf->main__DOT__emmcscopei__DOT__new_data = 
        (1U & ((~ ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                   >> 2U)) | (vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber4 
                              != vlSelf->main__DOT__emmcscopei__DOT__qd_data)));
    vlSelf->main__DOT__sdioscopei__DOT__new_data = 
        (1U & ((~ ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                   >> 2U)) | (vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber4 
                              != vlSelf->main__DOT__sdioscopei__DOT__qd_data)));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb)) 
               | (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))))))) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
            = vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg;
        if (((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
               & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy))) 
              & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid))) 
             & (1U == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw)))) {
            vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                = (0xb80000000ULL | (0x3fffffffULL 
                                     & vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word));
        }
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb)) 
               | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT____Vcellinp__GEN_IDLES__DOT__buildcw__i_tx_busy))))) {
        if (vlSelf->main__DOT__genbus__DOT__ofifo_rd) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cw_stb = 1U;
            vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                = vlSelf->main__DOT__genbus__DOT__ofifo_codword;
        } else {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cw_stb 
                = (1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb)) 
                         & (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request) 
                             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent))) 
                            | ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state)) 
                               & (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
                                  >> 0x15U)))));
            if (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request) 
                 & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent)))) {
                vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                    = (0x100000000ULL | (0x3fffffffULL 
                                         & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword));
            } else {
                vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                    = (0x3fffffffULL & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword);
                if (vlSelf->main__DOT__wbu_cyc) {
                    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                        = (0x40000000ULL | (0x3fffffffULL 
                                            & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword));
                }
            }
        }
    }
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc));
    vlSelf->main__DOT__wbu_xbar__DOT__s_err = (0xcU 
                                               | ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                                                  & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err)));
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT____Vcellinp__UPSIZE__DOT__u_fifo__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift 
        = (0x3fU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill));
    if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid) 
         & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift 
            = (0x3fU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill));
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last)) 
                 & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last)) 
                    & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid)) 
                       | ((0x40U > (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill)) 
                          | (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)))))));
    if (vlSelf->main__DOT__u_fan__DOT__mem_ack) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_word 
            = vlSelf->main__DOT__u_fan__DOT__mem_data;
    }
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set 
        = ((IData)(vlSelf->main__DOT__swic__DOT____Vcellinp__u_jiffies__i_wb_stb) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    if (vlSelf->main__DOT__swic__DOT__cmd_reset) {
        vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set = 0U;
        vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie = 0U;
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length = 0U;
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src = 0U;
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst = 0U;
    } else {
        if (((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__enable_ints) 
             & (vlSelf->main__DOT__swic__DOT__sys_data 
                >> 0x1fU))) {
            vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie = 1U;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__disable_ints) 
                    & (vlSelf->main__DOT__swic__DOT__sys_data 
                       >> 0x1fU))) {
            vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie = 0U;
        }
        if (((((IData)(vlSelf->main__DOT__swic__DOT__dmac_stb) 
               & (IData)(vlSelf->main__DOT__swic__DOT__sys_we)) 
              & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request))) 
             & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy)))) {
            if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))) {
                if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))) {
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length 
                        = (0xfffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_len);
                }
                if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__sys_addr)))) {
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst 
                        = (0xfffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_dst);
                }
            }
            if ((1U & (~ ((IData)(vlSelf->main__DOT__swic__DOT__sys_addr) 
                          >> 1U)))) {
                if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))) {
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src 
                        = (0xfffffffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_src);
                }
            }
        } else if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy) {
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_addr 
                   << 6U);
            vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_addr 
                   << 6U);
        }
    }
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_wb 
        = ((vlSelf->main__DOT__swic__DOT__sys_data 
            - vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter) 
           - ((IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)
               ? 0U : 1U));
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_now 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset)) 
           & ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
              & (((IData)(1U) + vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter) 
                 == vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_when)));
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__r_valid 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid;
    if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack))) {
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x10U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[1U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x11U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[2U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x12U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[3U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x13U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[4U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x14U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[5U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x15U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[6U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x16U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[7U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x17U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[8U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x18U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[9U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x19U];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xaU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1aU];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xbU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1bU];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xcU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1cU];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xdU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1dU];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xeU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1eU];
        vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xfU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1fU];
    }
    if ((0x10U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data 
            = (0xffffU & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                          >> (7U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))));
    } else if ((8U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data 
            = (0xffffU & ((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                           << 8U) >> (7U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full = 0U;
    } else {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill 
            = (3U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill) 
                     >> 3U));
        if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) 
              & (0x3ffU == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr))) 
             & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb))) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full = 1U;
        }
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb 
        = (1U & ((~ ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
                     | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__cmd_sample_ck)))) 
                 & ((~ (IData)(vlSelf->i_emmc_cmd)) 
                    | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__resp_started))));
    if ((0x10U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data 
            = (0xffffU & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                          >> (7U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))));
    } else if ((8U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data 
            = (0xffffU & ((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                           << 8U) >> (7U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill))));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full = 0U;
    } else {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill 
            = (3U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill) 
                     >> 3U));
        if ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) 
              & (0x3ffU == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr))) 
             & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full = 1U;
        }
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb 
        = (1U & ((~ ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
                     | (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__cmd_sample_ck)))) 
                 & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__resp_started) 
                    | ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__cmd_sample_ck) 
                         >> 1U) & (~ ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in) 
                                      >> 1U))) | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__cmd_sample_ck) 
                                                  & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in)))))));
    vlSelf->main__DOT__r_cfg_ack = (1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                          >> 0xaU));
    vlSelf->main__DOT__r_wb32_sio_ack = (1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                               >> 9U));
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_full 
        = ((~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)) 
           & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_full));
    vlSelf->main__DOT__wb32_i2cdma_ack = (1U & ((~ (IData)(vlSelf->i_reset)) 
                                                & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                                   >> 4U)));
    vlSelf->main__DOT__wb32_i2cs_ack = (1U & ((~ (IData)(vlSelf->i_reset)) 
                                              & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                                 >> 3U)));
    if ((1U & ((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc))))) {
        vlSelf->main__DOT__wb32_xbar__DOT__mgrant = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available) {
            vlSelf->main__DOT__wb32_xbar__DOT__mgrant = 1U;
        } else if (vlSelf->main__DOT__wb32_xbar__DOT__m_stb) {
            vlSelf->main__DOT__wb32_xbar__DOT__mgrant = 0U;
        }
    }
    vlSelf->main__DOT__sdioscopei__DOT__br_wb_ack = 
        ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_pre_wb_ack) 
         & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
            >> 2U));
    vlSelf->main__DOT__i2cscopei__DOT__br_wb_ack = 
        ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_pre_wb_ack) 
         & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
            >> 1U));
    vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack = 
        ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_pre_wb_ack) 
         & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc));
    vlSelf->main__DOT__wb32_uart_ack = (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                         >> 5U) & (IData)(vlSelf->main__DOT__console__DOT__r_wb_ack));
    vlSelf->main__DOT__wb32_sdcard_ack = ((~ ((IData)(vlSelf->i_reset) 
                                              | (~ 
                                                 ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                  >> 8U)))) 
                                          & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_ack));
    vlSelf->main__DOT__wb32_fan_ack = ((~ ((IData)(vlSelf->i_reset) 
                                           | (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                 >> 7U)))) 
                                       & (IData)(vlSelf->main__DOT__u_fan__DOT__pre_ack));
    vlSelf->main__DOT__wb32_emmc_ack = ((~ ((IData)(vlSelf->i_reset) 
                                            | (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                  >> 6U)))) 
                                        & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_ack));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack 
            = (IData)(((6U == (6U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr))) 
                       & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr) 
                          | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack))));
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache) 
             | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_new_pc))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort = 1U;
        }
    } else {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort = 0U;
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache 
            = (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr 
                           >> 3U));
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cline 
        = (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                 >> 3U));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_ctag 
        = (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                       >> 3U));
    vlSelf->main__DOT__swic__DOT__sys_cyc = ((IData)(vlSelf->main__DOT__swic__DOT__cpu_lcl_cyc) 
                                             | (IData)(vlSelf->main__DOT__swic__DOT__dbg_cyc));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn 
            = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch) 
                | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal))
                ? 0xdU : (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_opn));
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy 
        = ((~ ((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
               | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err)))) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
              | ((~ ((2U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state)) 
                     & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack))) 
                 & (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending) 
                     & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid))) 
                    | ((~ ((((1U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state)) 
                             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)) 
                            & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack)) 
                           & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce)))) 
                       & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc))))));
    if (vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN) {
        if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckedge)) 
                   | ((IData)(vlSelf->main__DOT__i2ci__DOT__i2c_stretch) 
                      & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__insn_ready)))))) {
            vlSelf->main__DOT__i2ci__DOT__i2c_abort = 0U;
        } else {
            vlSelf->main__DOT__i2ci__DOT__i2c_abort = 0U;
            if (((((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) 
                   & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir)) 
                  & (8U == (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) 
                 & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))) {
                vlSelf->main__DOT__i2ci__DOT__i2c_abort = 1U;
            }
            if (((((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) 
                   & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir)) 
                  & (5U == (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) 
                 & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda) 
                    != (1U & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg) 
                              >> 7U))))) {
                vlSelf->main__DOT__i2ci__DOT__i2c_abort = 1U;
            }
            if (((0xbU == (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state)) 
                 & ((IData)(vlSelf->main__DOT__i2ci__DOT__w_sda) 
                    != (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda)))) {
                vlSelf->main__DOT__i2ci__DOT__i2c_abort = 1U;
            }
            if (((0xcU == (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state)) 
                 & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl)) 
                    | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))))) {
                vlSelf->main__DOT__i2ci__DOT__i2c_abort = 1U;
            }
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl)) 
                   | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))))) {
            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy = 1U;
        } else if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__stop_bit) {
            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy = 0U;
        }
    } else {
        vlSelf->main__DOT__i2ci__DOT__i2c_abort = 0U;
        vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy = 0U;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) {
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc 
                = (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword);
        } else {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc 
                = ((3U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc) 
                   | (0xffffffcU & (((IData)(1U) + 
                                     ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc 
                                       >> 2U) + ((0x3ff8000U 
                                                  & ((- (IData)(
                                                                (1U 
                                                                 & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__SHIFT_INSN__DOT__shifted[0xfU] 
                                                                    >> 0x11U)))) 
                                                     << 0xfU)) 
                                                 | (0x7fffU 
                                                    & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__SHIFT_INSN__DOT__shifted[0xfU] 
                                                       >> 2U))))) 
                                    << 2U)));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc 
                = (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc);
        }
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_M 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_mem;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R 
            = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_cc) 
                << 6U) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_pc) 
                           << 5U) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA)));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wR 
            = (1U & (~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_sto) 
                        | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
                           | (8U == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                             >> 1U)))))));
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__instruction_decoder__i_reset) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid 
            = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__pf_valid) 
                | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase)) 
               & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp)));
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_stalled)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid = 0U;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy) 
              | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc 
        = ((((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
             | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache)) 
            | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe)) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_switch_to_interrupt) 
              | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_release_from_interrupt) 
                 | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                     & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                        == (1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id) 
                                  >> 4U)))) & (0xfU 
                                               == (0xfU 
                                                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))))));
    vlSelf->main__DOT__u_fan__DOT__ck_tach = (1U & 
                                              ((IData)(vlSelf->main__DOT__u_fan__DOT__pipe_tach) 
                                               >> 1U));
    vlSelf->main__DOT__u_fan__DOT__pipe_tach = ((2U 
                                                 & ((IData)(vlSelf->main__DOT__u_fan__DOT__pipe_tach) 
                                                    << 1U)) 
                                                | (IData)(vlSelf->i_fan_tach));
    if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge) {
        if ((8U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
            if ((4U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                if ((2U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                    if ((1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__channel_busy)))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0U;
                    }
                } else if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                    if ((1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__channel_busy)))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0U;
                    }
                } else if ((1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch)))) {
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                    if ((1U & ((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda)) 
                               | (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl))))) {
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0xaU;
                    }
                }
            } else if ((2U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                    if ((1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch)))) {
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0xcU;
                        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda) 
                             != (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda))) {
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0xaU;
                        }
                    }
                } else {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    if ((((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__channel_busy)) 
                          & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl)) 
                         & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0U;
                    }
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                if ((1U & ((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl)) 
                           & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda))))) {
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 3U;
                }
            } else {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state 
                        = (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir) 
                            & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda))
                            ? 9U : 2U);
                }
            }
        } else if ((4U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
            if ((2U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda 
                        = (1U & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir) 
                                 | (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack))));
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 8U;
                } else {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda 
                        = (1U & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir) 
                                 | (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack))));
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                    if ((1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl)))) {
                        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir) {
                            if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir) {
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 7U;
                            }
                        } else if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda) 
                                    != (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack))) {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 7U;
                        }
                    }
                    if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 6U;
                    }
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg 
                        = ((0xfeU & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg) 
                                     << 1U)) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda));
                    if ((0U < (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits 
                            = (7U & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits) 
                                     - (IData)(1U)));
                    }
                    if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir) 
                         & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda) 
                            != (1U & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg) 
                                      >> 7U))))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0xaU;
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    } else {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state 
                            = ((0U == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits))
                                ? 6U : 4U);
                    }
                } else {
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                }
            } else {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda 
                    = (1U & (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg) 
                              >> 7U) | (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir))));
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda) 
                     == (1U & (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg) 
                                >> 7U) | (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir)))))) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 5U;
                }
                if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 4U;
                }
            }
        } else if ((2U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
            if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0U;
                }
            } else {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 0U;
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = 1U;
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = 0U;
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg 
                    = (0xffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn));
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir = 0U;
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__s_tvalid) 
                     & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_ready))) {
                    if ((0x400U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                        if ((0x200U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                            if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = 1U;
                                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = 0U;
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 4U;
                            } else {
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = 1U;
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 4U;
                            }
                        } else if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 4U;
                        } else {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 4U;
                        }
                    } else if ((0x200U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                        if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 4U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg 
                                = (0xffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn));
                        } else {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 3U;
                        }
                    } else if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0xbU;
                    }
                }
            }
        } else if ((1U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state 
                = ((4U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits))
                    ? 4U : 2U);
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 0U;
        } else {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 0U;
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = 1U;
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg 
                = (0xffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn));
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir = 0U;
            if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__s_tvalid) 
                 & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_ready))) {
                if ((0x400U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                    if ((0x200U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                        if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = 1U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = 0U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                        } else {
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = 1U;
                            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                        }
                    } else if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = 0U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                    } else {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                    }
                } else if ((0x200U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                    if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir = 1U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = 7U;
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg 
                            = (0xffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn));
                    }
                } else if ((0x100U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 0U;
                    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 1U;
                }
            }
        }
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN)))) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = 1U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = 1U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = 0U;
    }
    if (((((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort)) 
          | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual)) 
         | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_manual))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid = 0U;
    } else if (((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle)) 
                & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid = 0U;
        if (((((3U != (0xfU & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                               >> 4U))) & (0xdU != 
                                           (0xfU & 
                                            ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                                             >> 4U)))) 
              & (0U != (0xfU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn)))) 
             & (9U != (0xfU & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                               >> 4U))))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid = 1U;
        }
    } else if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid = 0U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid)) 
               | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready)))) {
        vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data 
            = ((IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid)
                ? (IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_data)
                : (IData)(vlSelf->main__DOT__u_i2cdma__DOT____Vcellinp__sskd__i_data));
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[1U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[1U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[2U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[2U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[3U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[3U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[4U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[4U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[5U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[5U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[6U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[6U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[7U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[7U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[8U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[8U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[9U] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[9U];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xaU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xaU];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xbU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xbU];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xcU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xcU];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xdU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xdU];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xeU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xeU];
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xfU] 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xfU];
    if (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_ack) {
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[1U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[2U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[3U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[4U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[5U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[6U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[7U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[8U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[9U] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xaU] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xbU] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xcU] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xdU] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xeU] = 0U;
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xfU] = 0U;
    }
    if (vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) {
        __Vtemp_hdb251f8c__0[0U] = Vmain__ConstPool__CONST_hbd99daea_0[0U];
        __Vtemp_hdb251f8c__0[1U] = Vmain__ConstPool__CONST_hbd99daea_0[1U];
        __Vtemp_hdb251f8c__0[2U] = Vmain__ConstPool__CONST_hbd99daea_0[2U];
        __Vtemp_hdb251f8c__0[3U] = Vmain__ConstPool__CONST_hbd99daea_0[3U];
        __Vtemp_hdb251f8c__0[4U] = Vmain__ConstPool__CONST_hbd99daea_0[4U];
        __Vtemp_hdb251f8c__0[5U] = Vmain__ConstPool__CONST_hbd99daea_0[5U];
        __Vtemp_hdb251f8c__0[6U] = Vmain__ConstPool__CONST_hbd99daea_0[6U];
        __Vtemp_hdb251f8c__0[7U] = Vmain__ConstPool__CONST_hbd99daea_0[7U];
        __Vtemp_hdb251f8c__0[8U] = Vmain__ConstPool__CONST_hbd99daea_0[8U];
        __Vtemp_hdb251f8c__0[9U] = Vmain__ConstPool__CONST_hbd99daea_0[9U];
        __Vtemp_hdb251f8c__0[0xaU] = Vmain__ConstPool__CONST_hbd99daea_0[0xaU];
        __Vtemp_hdb251f8c__0[0xbU] = Vmain__ConstPool__CONST_hbd99daea_0[0xbU];
        __Vtemp_hdb251f8c__0[0xcU] = Vmain__ConstPool__CONST_hbd99daea_0[0xcU];
        __Vtemp_hdb251f8c__0[0xdU] = Vmain__ConstPool__CONST_hbd99daea_0[0xdU];
        __Vtemp_hdb251f8c__0[0xeU] = Vmain__ConstPool__CONST_hbd99daea_0[0xeU];
        __Vtemp_hdb251f8c__0[0xfU] = vlSelf->main__DOT__wb32_wbdown_idata;
        VL_SHIFTR_WWI(512,512,32, __Vtemp_h12b8adbe__0, __Vtemp_hdb251f8c__0, 
                      (0x1e0U & ((IData)(vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data) 
                                 << 5U)));
        __Vtemp_hb780e8f4__0[1U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[1U] 
                                    | __Vtemp_h12b8adbe__0[1U]);
        __Vtemp_hb780e8f4__0[2U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[2U] 
                                    | __Vtemp_h12b8adbe__0[2U]);
        __Vtemp_hb780e8f4__0[3U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[3U] 
                                    | __Vtemp_h12b8adbe__0[3U]);
        __Vtemp_hb780e8f4__0[4U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[4U] 
                                    | __Vtemp_h12b8adbe__0[4U]);
        __Vtemp_hb780e8f4__0[5U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[5U] 
                                    | __Vtemp_h12b8adbe__0[5U]);
        __Vtemp_hb780e8f4__0[6U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[6U] 
                                    | __Vtemp_h12b8adbe__0[6U]);
        __Vtemp_hb780e8f4__0[7U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[7U] 
                                    | __Vtemp_h12b8adbe__0[7U]);
        __Vtemp_hb780e8f4__0[8U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[8U] 
                                    | __Vtemp_h12b8adbe__0[8U]);
        __Vtemp_hb780e8f4__0[9U] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[9U] 
                                    | __Vtemp_h12b8adbe__0[9U]);
        __Vtemp_hb780e8f4__0[0xaU] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xaU] 
                                      | __Vtemp_h12b8adbe__0[0xaU]);
        __Vtemp_hb780e8f4__0[0xbU] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xbU] 
                                      | __Vtemp_h12b8adbe__0[0xbU]);
        __Vtemp_hb780e8f4__0[0xcU] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xcU] 
                                      | __Vtemp_h12b8adbe__0[0xcU]);
        __Vtemp_hb780e8f4__0[0xdU] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xdU] 
                                      | __Vtemp_h12b8adbe__0[0xdU]);
        __Vtemp_hb780e8f4__0[0xeU] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xeU] 
                                      | __Vtemp_h12b8adbe__0[0xeU]);
        __Vtemp_hb780e8f4__0[0xfU] = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xfU] 
                                      | __Vtemp_h12b8adbe__0[0xfU]);
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0U] 
            = (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0U] 
               | __Vtemp_h12b8adbe__0[0U]);
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[1U] 
            = __Vtemp_hb780e8f4__0[1U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[2U] 
            = __Vtemp_hb780e8f4__0[2U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[3U] 
            = __Vtemp_hb780e8f4__0[3U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[4U] 
            = __Vtemp_hb780e8f4__0[4U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[5U] 
            = __Vtemp_hb780e8f4__0[5U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[6U] 
            = __Vtemp_hb780e8f4__0[6U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[7U] 
            = __Vtemp_hb780e8f4__0[7U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[8U] 
            = __Vtemp_hb780e8f4__0[8U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[9U] 
            = __Vtemp_hb780e8f4__0[9U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xaU] 
            = __Vtemp_hb780e8f4__0[0xaU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xbU] 
            = __Vtemp_hb780e8f4__0[0xbU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xcU] 
            = __Vtemp_hb780e8f4__0[0xcU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xdU] 
            = __Vtemp_hb780e8f4__0[0xdU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xeU] 
            = __Vtemp_hb780e8f4__0[0xeU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data[0xfU] 
            = __Vtemp_hb780e8f4__0[0xfU];
    }
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc 
        = ((0xf0000000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc) 
           | ((0x10U & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))
               ? ((0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc) 
                  | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase) 
                     << 1U)) : ((0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ipc) 
                                | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_IHALT_PHASE__DOT__r_ihalt_phase) 
                                   << 1U))));
    if (((IData)(vlSelf->main__DOT____Vcellinp__swic__i_dbg_stb) 
         & (~ (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb)))) {
        vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_addr 
            = vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr;
    }
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__w_any 
        = (0U != ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable)));
    vlSelf->main__DOT__gpioi__DOT__q_gpio = vlSelf->main__DOT__gpioi__DOT__x_gpio;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset)) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err)));
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_switch_to_interrupt))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                & (0xeU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id))))) {
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) {
            if ((0x20U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl)) {
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep 
                    = (1U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                             >> 4U));
            }
        } else {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep 
                = (1U & ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                          >> 4U) & ((~ (IData)(vlSelf->main__DOT__swic__DOT__pic_interrupt)) 
                                    | (~ (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                                          >> 5U)))));
        }
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset)) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent = 0U;
    } else if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_last))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent = 1U;
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo = 0U;
    } else if ((((((((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                     & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en))) 
                    & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
                   & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request))) 
                  & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request))) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb)) 
                & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x19U)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo 
            = (1U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                     >> 0xcU));
    }
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
        = ((0xffffffff0000ffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | ((QData)((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout)) 
              << 0x10U));
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x17U)) | ((0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x14U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0x11U)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xeU)) 
                                         | ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xbU)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 8U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 5U)) 
                                                  | (1U 
                                                     & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 2U)))))))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior 
        = (0xffffU & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
                              >> 0x20U)));
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
        = ((0xffff0000ffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | ((QData)((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout)) 
              << 0x20U));
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data 
        = ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                     >> 0x18U)) | ((0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                             >> 0x15U)) 
                                   | ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                >> 0x12U)) 
                                      | ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xfU)) 
                                         | ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 0xcU)) 
                                            | ((4U 
                                                & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                   >> 9U)) 
                                               | ((2U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 6U)) 
                                                  | (1U 
                                                     & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                        >> 3U)))))))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__prior 
        = (0xffffU & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w 
                              >> 0x30U)));
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
        = ((0xffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w) 
           | ((QData)((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__Vfuncout)) 
              << 0x30U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffffff8ULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | (IData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                              >> 0x20U)) 
                                     << 2U)) | ((2U 
                                                 & ((IData)(
                                                            (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                             >> 0x10U)) 
                                                    << 1U)) 
                                                | (1U 
                                                   & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w)))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffffff7ULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x30U))))) 
              << 3U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffffff8fULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x21U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x11U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 1U))))))) 
              << 4U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffffff7fULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x31U))))) 
              << 7U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffff8ffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x22U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x12U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 2U))))))) 
              << 8U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffffff7ffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x32U))))) 
              << 0xbU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffff8fffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x23U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x13U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 3U))))))) 
              << 0xcU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffffff7fffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x33U))))) 
              << 0xfU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffff8ffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x24U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x14U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 4U))))))) 
              << 0x10U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffffff7ffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x34U))))) 
              << 0x13U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffff8fffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x25U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x15U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 5U))))))) 
              << 0x14U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffffff7fffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x35U))))) 
              << 0x17U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffff8ffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x26U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x16U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 6U))))))) 
              << 0x18U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffffff7ffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x36U))))) 
              << 0x1bU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffff8fffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x27U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x17U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 7U))))))) 
              << 0x1cU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffffff7fffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x37U))))) 
              << 0x1fU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffff8ffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x28U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x18U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 8U))))))) 
              << 0x20U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffffff7ffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x38U))))) 
              << 0x23U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffff8fffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x29U)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x19U)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 9U))))))) 
              << 0x24U));
    if (vlSelf->main__DOT__genbus__DOT__r_wdt_reset) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cw_stb = 0U;
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffffff7fffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x39U))))) 
              << 0x27U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffff8ffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2aU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1aU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xaU))))))) 
              << 0x28U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfffff7ffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3aU))))) 
              << 0x2bU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffff8fffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2bU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1bU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xbU))))))) 
              << 0x2cU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xffff7fffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3bU))))) 
              << 0x2fU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfff8ffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2cU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1cU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xcU))))))) 
              << 0x30U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xfff7ffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3cU))))) 
              << 0x33U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xff8fffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2dU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1dU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xdU))))))) 
              << 0x34U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xff7fffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3dU))))) 
              << 0x37U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xf8ffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2eU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1eU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xeU))))))) 
              << 0x38U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0xf7ffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3eU))))) 
              << 0x3bU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0x8fffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)(((4U & ((IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                               >> 0x2fU)) 
                                      << 2U)) | ((2U 
                                                  & ((IData)(
                                                             (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                              >> 0x1fU)) 
                                                     << 1U)) 
                                                 | (1U 
                                                    & (IData)(
                                                              (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                                               >> 0xfU))))))) 
              << 0x3cU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w 
        = ((0x7fffffffffffffffULL & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w) 
           | ((QData)((IData)((1U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w 
                                             >> 0x3fU))))) 
              << 0x3fU));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          << 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x10U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x12U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x14U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                    >> 0x1bU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                          >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x10U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           << 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x10U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                       >> 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                           >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        << 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0x10U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 3U)));
    if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr = 0U;
    } else if ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr 
            = vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr;
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x8000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                            >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x1bU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x14U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x12U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         << 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0x10U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                             << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]) 
           | (0x80000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U]));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x15U)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0xeU)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 7U)) | (1U 
                                                   & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x16U)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0xfU)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 8U)) | (1U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 1U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[0U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x17U)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x10U)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 9U)) | (1U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                                      >> 2U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x18U)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x11U)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xaU)) | 
                                 (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 3U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[1U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x19U)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x12U)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xbU)) | 
                                 (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 4U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1aU)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x13U)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xcU)) | 
                                 (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 5U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[2U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1bU)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x14U)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xdU)) | 
                                 (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 6U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data 
        = ((8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1cU)) | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                       >> 0x15U)) | 
                                ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 0xeU)) | 
                                 (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                        >> 7U)))));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w[3U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 3U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 2U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__82__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC4__81__Vfuncout) 
              << 0x10U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     << 2U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 0xfU)) | 
                                (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U]))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0xbU)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                        << 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                      >> 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 9U)) | (0x40U 
                                                  & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                                     << 6U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        << 9U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 8U)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         << 7U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 4U)) | 
                             ((0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                          << 0xbU)) 
                              | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                           >> 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 2U)) | 
                             (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         << 0xdU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 0x10U)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             >> 1U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 0xeU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           << 3U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 0x12U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               << 1U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 5U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0x14U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0x17U)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 6U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 0x15U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             << 0xaU)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0x19U)) 
                                | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                 << 8U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U]) 
           | (0xc0000000U & ((0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0xcU)) 
                             | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0x1bU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     >> 2U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 0x13U)) | 
                                (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 4U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0xfU)) | 
                             ((0x10U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U]) 
                              | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                       >> 0x11U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 0xdU)) | 
                             (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       << 2U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        << 5U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 0xcU)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         << 3U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 8U)) | 
                             ((0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                          << 7U)) | 
                              (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                         >> 0xaU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 6U)) | 
                             (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         << 9U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 0xcU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             >> 5U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 0xaU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           >> 1U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 0xeU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               >> 3U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 1U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0x10U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0x13U)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               << 2U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 0x11U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             << 6U)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0x15U)) 
                                | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                 << 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U]) 
           | (0xc0000000U & ((0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 8U)) 
                             | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0x17U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     >> 6U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 0x17U)) | 
                                (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                       >> 8U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0x13U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                        >> 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                      >> 0x15U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 0x11U)) | 
                             (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 2U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        << 1U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 0x10U)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         >> 1U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 0xcU)) 
                             | ((0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                            << 3U)) 
                                | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                             >> 0xeU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 0xaU)) 
                             | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 5U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 8U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                           >> 9U)) 
                              | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             << 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           >> 5U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 0xaU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               >> 7U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           >> 3U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 0xcU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0xfU)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               >> 2U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             << 2U)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0x11U)) 
                                | (0x8000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U])))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U]) 
           | (0xc0000000U & ((0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 4U)) 
                             | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0x13U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                     >> 0xaU)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                         >> 0x1bU)) 
                                  | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                           >> 0xcU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                       >> 0x17U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                        >> 8U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                      >> 0x19U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffffff3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffffffc0U & ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 0x15U)) | 
                             (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                       >> 6U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xfffff8ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffffff00U & ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                        >> 3U)) | (
                                                   (0x200U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                       >> 0x14U)) 
                                                   | (0x100U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                         >> 5U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffffc7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xfffff800U & ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                         >> 0x10U)) 
                             | ((0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                            >> 1U)) 
                                | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                             >> 0x12U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffff3fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffffc000U & ((0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                         >> 0xeU)) 
                             | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           << 1U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                          << 4U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                           >> 0xdU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                             << 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                           >> 9U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                              << 6U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                               >> 0xbU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xff3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xffc00000U & ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                           >> 7U)) 
                             | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                             << 8U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xf8ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xff000000U & ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                            << 0xbU)) 
                             | ((0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                               >> 6U)) 
                                | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[0U] 
                                                 << 9U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0xc7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xf8000000U & ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                             >> 2U)) 
                             | ((0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[2U] 
                                                << 0xdU)) 
                                | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[1U] 
                                                 >> 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U] 
        = ((0x3fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U]) 
           | (0xc0000000U & ((0x80000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U]) 
                             | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w[3U] 
                                               << 0xfU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffffeU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffeffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          << 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x20000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x1bU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffffdU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                    >> 0x1dU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffdffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                          >> 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (4U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffffbU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffbffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x80000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffff7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                    >> 0x1bU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfff7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                          >> 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       << 2U)));
    if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request) 
                & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type;
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x10U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffffefU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffefffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x200000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffffdfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                       >> 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffdfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                           >> 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x40U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffffbfU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffbfffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x800000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffff7fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                       >> 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xff7fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                           >> 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x100U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffeffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfeffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x2000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffdffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                        >> 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfdffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            >> 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x13U)));
    if (vlSelf->main__DOT__genbus__DOT__r_wdt_reset) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 0U;
        vlSelf->main__DOT__wbu_cyc = 0U;
        vlSelf->__Vdly__main__DOT__wbu_stb = 0U;
        vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
    } else {
        if ((((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request) 
              & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb))) 
             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_rd)))) {
            vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent = 1U;
        } else if ((1U & (~ (IData)(vlSelf->main__DOT__zip_cpu_int)))) {
            vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent = 0U;
        }
        if ((2U & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state))) {
            if ((1U & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state))) {
                vlSelf->main__DOT__wbu_cyc = 0U;
                vlSelf->__Vdly__main__DOT__wbu_stb = 0U;
                vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 1U;
                if (((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
                     & (1U != (3U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                             >> 0x22U)))))) {
                    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 0U;
                    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
                }
            } else {
                vlSelf->main__DOT__wbu_cyc = 1U;
                vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 1U;
                if ((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))) {
                    vlSelf->__Vdly__main__DOT__wbu_stb = 0U;
                }
                if ((1U & ((~ (IData)(vlSelf->main__DOT__wbu_stb)) 
                           | (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))))) {
                    if (((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
                         & (0x400000000ULL == (0xc00000000ULL 
                                               & vlSelf->main__DOT__genbus__DOT__ififo_codword)))) {
                        if (vlSelf->main__DOT__genbus__DOT__w_bus_busy) {
                            vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
                        } else {
                            vlSelf->__Vdly__main__DOT__wbu_stb = 1U;
                            vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 1U;
                        }
                    } else if ((((~ (IData)(vlSelf->main__DOT__wbu_stb)) 
                                 & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__zero_acks)) 
                                | ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                   & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_ack)))) {
                        vlSelf->main__DOT__wbu_cyc = 0U;
                        vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
                        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 0U;
                    }
                }
                if (vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) {
                    vlSelf->main__DOT__wbu_cyc = 0U;
                    vlSelf->__Vdly__main__DOT__wbu_stb = 0U;
                    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 3U;
                    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 1U;
                }
            }
        } else if ((1U & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state))) {
            vlSelf->main__DOT__wbu_cyc = 1U;
            if ((1U & ((~ (IData)(vlSelf->main__DOT__wbu_stb)) 
                       | (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))))) {
                vlSelf->__Vdly__main__DOT__wbu_stb 
                    = (1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_read_request)));
            }
            if (((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                 & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_ack))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 0U;
                vlSelf->main__DOT__wbu_cyc = 0U;
                vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
            }
            if (vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) {
                vlSelf->__Vdly__main__DOT__wbu_stb = 0U;
                vlSelf->main__DOT__wbu_cyc = 0U;
                vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 0U;
                vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
            }
        } else {
            vlSelf->main__DOT__wbu_cyc = 0U;
            vlSelf->__Vdly__main__DOT__wbu_stb = 0U;
            vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 0U;
            if (((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
                 & (~ (IData)(vlSelf->main__DOT__genbus__DOT__w_bus_busy)))) {
                if ((1U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                   >> 0x23U)))) {
                    if ((1U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                       >> 0x22U)))) {
                        vlSelf->__Vdly__main__DOT__wbu_stb = 1U;
                        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 1U;
                        vlSelf->main__DOT__wbu_cyc = 1U;
                        vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 1U;
                    }
                } else if ((1U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                          >> 0x22U)))) {
                    vlSelf->__Vdly__main__DOT__wbu_stb = 1U;
                    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = 2U;
                    vlSelf->main__DOT__wbu_cyc = 1U;
                    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = 1U;
                }
            }
        }
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x400U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffffbffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfbffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x8000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xfffff7ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                        >> 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xf7ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            >> 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x1bU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x1000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffefffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xefffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x20000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffdfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                         >> 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xdfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                             >> 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x1dU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x1bU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x19U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x17U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x15U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x13U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0x11U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffffbfffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x4000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U]));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xbfffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                             << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]) 
           | (0x80000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U]));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0xfU)) | (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x10U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[0U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x11U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 2U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x12U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 3U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[1U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x13U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 4U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x14U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 5U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[2U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x15U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 6U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x16U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 7U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[3U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x17U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 8U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x18U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 9U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[4U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x19U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xaU)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1aU)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xbU)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[5U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1bU)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xcU)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1cU)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xdU)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[6U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1dU)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xeU)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U]);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
        = ((0xffff0000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]) 
           | (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data 
        = ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                  >> 0x1eU)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data 
                                      >> 0xfU)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior 
        = (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d[7U] 
           >> 0x10U);
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data) 
                 >> 1U));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit 
        = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__i_crc_data));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout 
        = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                     >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__i_bit)))
            ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                     << 1U))) : (0xfffeU 
                                                 & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__prior) 
                                                    << 1U)));
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__84__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout 
        = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
        = ((0xffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]) 
           | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC2__83__Vfuncout) 
              << 0x10U));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     << 2U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0xfU)) | 
                                (1U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0xbU)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        << 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 8U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 9U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         << 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 5U)) | (
                                                   (0x400U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                                       << 0xaU)) 
                                                   | (0x200U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                         >> 7U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 0xeU)) 
                             | ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 3U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              << 0xcU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 1U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0x11U)) 
                             | ((0x20000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U]) 
                                | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 0xfU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           << 4U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0x13U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               << 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x17U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              << 6U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0x15U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 0xaU)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x19U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 8U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x1dU)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 0xcU)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x1bU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 0xeU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | ((4U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U]) 
              | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                        >> 0x11U)) | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                            >> 2U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0xdU)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        << 2U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0xfU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 6U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0xbU)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         << 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 7U)) | (
                                                   (0x400U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                                       << 8U)) 
                                                   | (0x200U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                         >> 9U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 0xcU)) 
                             | ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 5U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              << 0xaU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 3U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0xfU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             >> 2U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           << 2U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0x11U)) 
                                | (0x80000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U])))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x15U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              << 4U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0x13U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 8U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x17U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x1bU)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 0xaU)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x19U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 0xcU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 2U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x13U)) | 
                                (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 4U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0xfU)) | 
                             ((0x10U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
                              | (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                       >> 0x11U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 4U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0xdU)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         << 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 9U)) | (
                                                   (0x400U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                                       << 6U)) 
                                                   | (0x200U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                         >> 0xbU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 0xaU)) 
                             | ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 7U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              << 8U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 5U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0xdU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             >> 4U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 0xbU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfff80000U & ((0x200000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U]) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0xfU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x13U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              << 2U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0x11U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 6U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x15U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x19U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 8U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x17U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 0xaU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 4U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x15U)) | 
                                (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 6U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x11U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 2U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x13U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        << 2U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0xfU)) 
                                                   | (0x40U 
                                                      & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U])))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0xbU)) | 
                             ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                         << 4U)) | 
                              (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                         >> 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 8U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 9U)) | 
                              (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          << 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 7U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 0xbU)) 
                             | ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             >> 6U)) 
                                | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                               << 9U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 2U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0xdU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0x11U)) 
                             | ((0x800000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U]) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0xfU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 4U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x13U)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 << 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x17U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 6U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x15U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 8U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 6U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x17U)) | 
                                (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 8U)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x13U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 4U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x15U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xffffffc0U & ((0x100U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U]) 
                             | ((0x80U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                          >> 0x11U)) 
                                | (0x40U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                            >> 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0xdU)) | 
                             ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                         << 2U)) | 
                              (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                         >> 0xfU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 6U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 0xbU)) 
                              | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            << 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 9U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 9U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 8U)) 
                              | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 7U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 4U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 0xbU)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0xfU)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 2U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            << 2U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0x11U)) 
                                | (0x2000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U])))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x15U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 4U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x13U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 6U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 8U)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0x19U)) | 
                                (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                       >> 0xaU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x15U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 6U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x17U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        >> 2U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0x13U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         >> 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0xfU)) | 
                             ((0x400U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
                              | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                           >> 0x11U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 4U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 0xdU)) 
                              | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            << 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 0xbU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 7U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xaU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 5U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 6U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 9U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 8U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0xdU)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 4U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 0xbU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xfe000000U & ((0x8000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U]) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0xfU)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 >> 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x13U)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                << 2U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0x11U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 4U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 0xaU)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                         >> 0x1bU)) 
                                  | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xcU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x17U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 8U)) | (8U 
                                                   & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                                      >> 0x19U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        >> 4U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0x15U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         >> 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0x11U)) 
                             | ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                           >> 2U)) 
                                | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                             >> 0x13U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfffff000U & ((0x4000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                         << 2U)) | 
                             ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                          >> 0xfU)) 
                              | (0x1000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U])))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 0xdU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 5U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xcU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 3U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 8U)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 7U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 0xaU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 0xbU)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 6U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 9U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            >> 2U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0xdU)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 >> 4U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0x11U)) 
                             | ((0x20000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U]) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0xfU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U]) 
           | (0x80000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                             << 2U)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfffffff8U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | ((4U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                     >> 0xcU)) | ((2U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                         >> 0x1dU)) 
                                  | (1U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xeU)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffffffc7U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfffffff8U & ((0x20U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                       >> 0x19U)) | 
                             ((0x10U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                        >> 0xaU)) | 
                              (8U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                     >> 0x1bU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfffffe3fU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xffffffc0U & ((0x100U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                        >> 6U)) | (
                                                   (0x80U 
                                                    & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                       >> 0x17U)) 
                                                   | (0x40U 
                                                      & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                         >> 8U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfffff1ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfffffe00U & ((0x800U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                        >> 0x13U)) 
                             | ((0x400U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                           >> 4U)) 
                                | (0x200U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                             >> 0x15U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffff8fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfffff000U & ((0x4000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]) 
                             | ((0x2000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                            >> 0x11U)) 
                                | (0x1000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                              >> 2U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffff7fffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0x8000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                         >> 0xfU)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfff8ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xffff0000U & ((0x40000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                          << 3U)) | 
                             ((0x20000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                           >> 0xeU)) 
                              | (0x10000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[0U] 
                                             << 1U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xffc7ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfff80000U & ((0x200000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                           >> 0xaU)) 
                             | ((0x100000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[2U] 
                                              << 5U)) 
                                | (0x80000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[1U] 
                                               >> 0xcU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xfe3fffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xffc00000U & ((0x1000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                            << 9U)) 
                             | ((0x800000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                              >> 8U)) 
                                | (0x400000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[3U] 
                                                << 7U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0xf1ffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xfe000000U & ((0x8000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                            >> 4U)) 
                             | ((0x4000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[5U] 
                                               << 0xbU)) 
                                | (0x2000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[4U] 
                                                 >> 6U))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0x8fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0xf0000000U & ((0x40000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U] 
                                             << 0xfU)) 
                             | ((0x20000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                >> 2U)) 
                                | (0x10000000U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[6U] 
                                                  << 0xdU))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U] 
        = ((0x7fffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U]) 
           | (0x80000000U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d[7U]));
    if ((1U & (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid)) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b
            [(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
               & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo))
               ? (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
               : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))];
    }
    if ((1U & (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid)) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a
            [(((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo)) 
               & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en))
               ? (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
               : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))];
    }
    if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
          | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response)) 
         | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = 1U;
    }
    if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request) 
                & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type;
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request) 
                & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 0U;
    } else if (((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)) 
                & (0U != (3U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 1U;
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done)) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb = 0U;
    } else if (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy)) 
                & (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
            = (0xffffU & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds)
                           ? ((IData)(0x10U) + ((0x1fffU 
                                                 & ((IData)(1U) 
                                                    << (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk))) 
                                                + ((IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)
                                                    ? 0x10U
                                                    : 0U)))
                           : ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width))
                               ? ((IData)(0x10U) + 
                                  ((0xfff8U & (((IData)(1U) 
                                                << (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk)) 
                                               << 3U)) 
                                   + ((IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)
                                       ? 0x10U : 0U)))
                               : ((1U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width))
                                   ? ((IData)(0x10U) 
                                      + ((0x3ffeU & 
                                          (((IData)(1U) 
                                            << (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk)) 
                                           << 1U)) 
                                         + ((IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)
                                             ? 0x10U
                                             : 0U)))
                                   : ((IData)(0x10U) 
                                      + ((0x1fffU & 
                                          ((IData)(1U) 
                                           << (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk))) 
                                         + ((IData)(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr)
                                             ? 0x10U
                                             : 0U)))))));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase = 1U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc = 0U;
    } else if ((3U == ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                       << 1U))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
            = (0xffffU & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count) 
                          - (IData)(2U)));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb 
            = (3U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
        if (vlSelf->main__DOT__u_emmc__DOT__cfg_ddr) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x22U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x22U >= (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (2U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        } else {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x12U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x12U >= (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (2U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        }
        if ((2U > (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = 0U;
        }
    } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
            = (0xffffU & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count) 
                          - (IData)(1U)));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb 
            = (2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
        if (vlSelf->main__DOT__u_emmc__DOT__cfg_ddr) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x21U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x21U >= (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (1U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        } else {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x11U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x11U >= (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (1U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        }
        if ((1U > (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = 0U;
        }
    }
    if ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
          | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response)) 
         | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = 1U;
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request) 
                & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 0U;
    } else if (((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)) 
                & (0U != (3U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = 1U;
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done)) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb = 0U;
    } else if (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy)) 
                & (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
            = (0xffffU & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds)
                           ? ((IData)(0x10U) + ((0x1fffU 
                                                 & ((IData)(1U) 
                                                    << (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk))) 
                                                + ((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)
                                                    ? 0x10U
                                                    : 0U)))
                           : ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width))
                               ? ((IData)(0x10U) + 
                                  ((0xfff8U & (((IData)(1U) 
                                                << (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk)) 
                                               << 3U)) 
                                   + ((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)
                                       ? 0x10U : 0U)))
                               : ((1U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width))
                                   ? ((IData)(0x10U) 
                                      + ((0x3ffeU & 
                                          (((IData)(1U) 
                                            << (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk)) 
                                           << 1U)) 
                                         + ((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)
                                             ? 0x10U
                                             : 0U)))
                                   : ((IData)(0x10U) 
                                      + ((0x1fffU & 
                                          ((IData)(1U) 
                                           << (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk))) 
                                         + ((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)
                                             ? 0x10U
                                             : 0U)))))));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase = 1U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc = 0U;
    } else if ((3U == ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                       << 1U))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
            = (0xffffU & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count) 
                          - (IData)(2U)));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb 
            = (3U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
        if (vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x22U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x22U >= (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (2U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        } else {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x12U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x12U >= (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (2U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        }
        if ((2U > (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = 0U;
        }
    } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
            = (0xffffU & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count) 
                          - (IData)(1U)));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb 
            = (2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
        if (vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x21U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x21U >= (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (1U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        } else {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase 
                = (0x11U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count));
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc 
                = ((0x11U >= (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)) 
                   & (1U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count)));
        }
        if ((1U > (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = 0U;
        }
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__r_busy) 
           | (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cp_stb;
    vlSelf->main__DOT__i2cscopei__DOT__br_config = vlSelf->__Vdly__main__DOT__i2cscopei__DOT__br_config;
    vlSelf->main__DOT__emmcscopei__DOT__br_config = vlSelf->__Vdly__main__DOT__emmcscopei__DOT__br_config;
    vlSelf->main__DOT__sdioscopei__DOT__br_config = vlSelf->__Vdly__main__DOT__sdioscopei__DOT__br_config;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__cw_stb;
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest) 
              >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest) 
              >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid) 
           & (0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS 
        = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel;
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_when 
        = vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__int_when;
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter 
        = vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__r_counter;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid;
    vlSelf->main__DOT__wb32_wbdown_stb = ((~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_full)) 
                                          & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_addr;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_cyc;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg;
    vlSelf->main__DOT__i2ci__DOT__w_sda = vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda;
    vlSelf->main__DOT__i2ci__DOT__i2c_ckedge = vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckedge;
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state 
        = vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & (0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS 
        = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel;
    vlSelf->main__DOT__u_i2cdma__DOT__bus_err = vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__bus_err;
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr 
        = (0x7fU & ((IData)(vlSelf->cpu_sim_cyc) ? (IData)(vlSelf->cpu_sim_addr)
                     : (IData)((vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
                                >> 0x1bU))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate;
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3))));
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr;
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2))));
    }
    if (vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a[vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3] 
            = (((~ ((IData)(0xffU) << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3))) 
                & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a
                [vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3]) 
               | (0xffffffffULL & ((IData)(vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3) 
                                   << (IData)(vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3))));
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_busy 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
           & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb));
    vlSelf->main__DOT__i2cscopei__DOT__qd_data = vlSelf->main__DOT____Vcellinp__i2cscopei____pinNumber4;
    vlSelf->main__DOT__i2cscopei__DOT__bw_reset_request 
        = (1U & (~ ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                    >> 2U)));
    vlSelf->main__DOT__i2cscopei__DOT__dw_trigger = 
        ((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_primed) 
         & (((~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config)) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__r_aborted)) 
            | ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
               >> 1U)));
    vlSelf->main__DOT__i2cscope_int = (IData)(((((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe) 
                                                 >> 4U) 
                                                & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config))) 
                                               & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_level_interrupt))));
    vlSelf->main__DOT__emmcscopei__DOT__qd_data = vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber4;
    vlSelf->main__DOT__emmcscopei__DOT__bw_reset_request 
        = (1U & (~ ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                    >> 2U)));
    vlSelf->main__DOT__emmcscope_int = (IData)(((((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe) 
                                                  >> 4U) 
                                                 & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config))) 
                                                & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_level_interrupt))));
    vlSelf->main__DOT__sdioscopei__DOT__qd_data = vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber4;
    vlSelf->main__DOT__sdioscopei__DOT__bw_reset_request 
        = (1U & (~ ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                    >> 2U)));
    vlSelf->main__DOT__sdioscope_int = (IData)(((((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe) 
                                                  >> 4U) 
                                                 & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config))) 
                                                & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_level_interrupt))));
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cod_busy 
        = (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb)) 
               | (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy))))) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid 
            = (1U & (vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__remap
                     [(0x7fU & (IData)(vlSelf->main__DOT__wbu_rx_data))] 
                     >> 6U));
    }
    if (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
         & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy)))) {
        if ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len) 
              == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)) 
             & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)))) {
            vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg 
                = ((0x3fffffffULL & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                   | ((QData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)) 
                      << 0x1eU));
        } else if ((4U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len))) {
            if ((1U & (~ ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len) 
                          >> 1U)))) {
                vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg 
                    = ((1U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len))
                        ? ((0xfffffffc0ULL & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                           | (IData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)))
                        : ((0xffffff03fULL & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                           | ((QData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)) 
                              << 6U)));
            }
        } else {
            vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg 
                = ((2U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len))
                    ? ((1U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len))
                        ? ((0xffffc0fffULL & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                           | ((QData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)) 
                              << 0xcU)) : ((0xfff03ffffULL 
                                            & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                                           | ((QData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)) 
                                              << 0x12U)))
                    : ((1U & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len))
                        ? ((0xfc0ffffffULL & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                           | ((QData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)) 
                              << 0x18U)) : ((0x3fffffffULL 
                                             & vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg) 
                                            | ((QData)((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits)) 
                                               << 0x1eU))));
        }
    }
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
    if (((IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_read) 
         & (~ (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow)))) {
        vlSelf->main__DOT__genbus__DOT__ofifo_codword 
            = vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo
            [(0x3ffU & (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr))];
    }
}
