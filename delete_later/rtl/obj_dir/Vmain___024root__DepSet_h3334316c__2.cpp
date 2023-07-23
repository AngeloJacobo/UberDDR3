// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vmain.h for the primary calling header

#include "verilated.h"
#include "verilated_dpi.h"

#include "Vmain__Syms.h"
#include "Vmain___024root.h"

extern const VlWide<18>/*575:0*/ Vmain__ConstPool__CONST_hb679b2e5_0;
extern const VlUnpacked<CData/*0:0*/, 512> Vmain__ConstPool__TABLE_h40cc9f5d_0;

VL_INLINE_OPT void Vmain___024root___nba_sequent__TOP__2(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___nba_sequent__TOP__2\n"); );
    // Init
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 = 0;
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
    SData/*8:0*/ __Vtableidx2;
    __Vtableidx2 = 0;
    // Body
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb 
        = vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__req_data 
        = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__gie) 
            << 0xcU) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT____VdfgTmp_h05977c6b__0));
    vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc = vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc;
    vlSelf->main__DOT__i2ci__DOT__pf_jump_addr = vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr;
    vlSelf->main__DOT__i2ci__DOT__pf_insn_addr = vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_insn_addr;
    vlSelf->main__DOT__wbwide_i2cm_cyc = vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr;
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending 
        = vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending 
        = vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending 
        = vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending 
        = vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending;
    vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending 
        = vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_i2cm_stb = vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb;
    vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe;
    vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl[vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl__v0] 
        = vlSelf->__Vdlyvval__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl__v0;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_flags 
        = ((2U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_index))
            ? ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__set_ovfl) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0)) 
                << 3U) | ((4U & ((4U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result 
                                        >> 0x1dU)) 
                                 ^ (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__keep_sgn_on_ovfl) 
                                     & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0)) 
                                    << 2U))) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__c) 
                                                 << 1U) 
                                                | (0U 
                                                   == vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result))))
            : ((3U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_index))
                ? ((4U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                          >> 0x1dU)) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_c) 
                                         << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_z)))
                : 0U));
    if (vlSelf->__Vdlyvset__main__DOT__i2cscopei__DOT__mem__v0) {
        vlSelf->main__DOT__i2cscopei__DOT__mem[vlSelf->__Vdlyvdim0__main__DOT__i2cscopei__DOT__mem__v0] 
            = vlSelf->__Vdlyvval__main__DOT__i2cscopei__DOT__mem__v0;
    }
    if (vlSelf->__Vdlyvset__main__DOT__emmcscopei__DOT__mem__v0) {
        vlSelf->main__DOT__emmcscopei__DOT__mem[vlSelf->__Vdlyvdim0__main__DOT__emmcscopei__DOT__mem__v0] 
            = vlSelf->__Vdlyvval__main__DOT__emmcscopei__DOT__mem__v0;
    }
    if (vlSelf->__Vdlyvset__main__DOT__sdioscopei__DOT__mem__v0) {
        vlSelf->main__DOT__sdioscopei__DOT__mem[vlSelf->__Vdlyvdim0__main__DOT__sdioscopei__DOT__mem__v0] 
            = vlSelf->__Vdlyvval__main__DOT__sdioscopei__DOT__mem__v0;
    }
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness;
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness 
        = vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness;
    vlSelf->main__DOT__wbwide_wbu_arbiter_stb = ((~ (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_full)) 
                                                 & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_stb));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr 
        = vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__rd_addr;
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr 
        = vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__rd_addr;
    vlSelf->main__DOT__i2ci__DOT__r_halted = vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted;
    vlSelf->main__DOT__u_fan__DOT__ctl_sys = vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys;
    vlSelf->main__DOT__u_fan__DOT__ctl_fpga = vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr;
    vlSelf->main__DOT__u_i2cdma__DOT__subaddr = vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__subaddr;
    vlSelf->main__DOT__wbwide_i2cdma_addr = vlSelf->__Vdly__main__DOT__wbwide_i2cdma_addr;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first 
        = vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U];
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__w_in 
        = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__high_z)
                  ? ((IData)(vlSelf->i_sdcard_dat) 
                     >> 3U) : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__o_pin)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__w_in 
        = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__high_z)
                  ? ((IData)(vlSelf->i_sdcard_dat) 
                     >> 2U) : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__o_pin)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__w_in 
        = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__high_z)
                  ? ((IData)(vlSelf->i_sdcard_dat) 
                     >> 1U) : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__o_pin)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__w_in 
        = (1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__high_z)
                  ? (IData)(vlSelf->i_sdcard_dat) : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__o_pin)));
    vlSelf->o_sdcard_dat = (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__o_pin) 
                             << 3U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__o_pin) 
                                        << 2U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__o_pin) 
                                                   << 1U) 
                                                  | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__o_pin))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg;
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
    vlSelf->main__DOT__w_console_busy = ((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
                                         | (IData)(vlSelf->main__DOT__genbus__DOT__wbu_tx_stb));
    if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy)))) {
        vlSelf->main__DOT__genbus__DOT__wbu_tx_data 
            = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__remap
            [vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_bits];
    }
    vlSelf->main__DOT__i2cscopei__DOT__lst_adr = (1U 
                                                  & ((~ 
                                                      ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                                                       >> 2U)) 
                                                     | (IData)(vlSelf->main__DOT__i2cscopei__DOT__imm_adr)));
    if ((4U & (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config))) {
        vlSelf->main__DOT__i2cscopei__DOT__lst_val 
            = vlSelf->main__DOT__i2cscopei__DOT__imm_val;
        vlSelf->main__DOT__i2cscopei__DOT__imm_val 
            = ((((IData)(vlSelf->main__DOT__i2cscopei__DOT__new_data) 
                 | (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_force_write)) 
                | (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped))
                ? vlSelf->main__DOT__i2cscopei__DOT__qd_data
                : vlSelf->main__DOT__i2cscopei__DOT__ck_addr);
    } else {
        vlSelf->main__DOT__i2cscopei__DOT__lst_val = 0U;
        vlSelf->main__DOT__i2cscopei__DOT__imm_val = 0U;
    }
    vlSelf->main__DOT__emmcscopei__DOT__lst_adr = (1U 
                                                   & ((~ 
                                                       ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                                                        >> 2U)) 
                                                      | (IData)(vlSelf->main__DOT__emmcscopei__DOT__imm_adr)));
    if ((4U & (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config))) {
        vlSelf->main__DOT__emmcscopei__DOT__lst_val 
            = vlSelf->main__DOT__emmcscopei__DOT__imm_val;
        vlSelf->main__DOT__emmcscopei__DOT__imm_val 
            = ((((IData)(vlSelf->main__DOT__emmcscopei__DOT__new_data) 
                 | (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_force_write)) 
                | (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped))
                ? vlSelf->main__DOT__emmcscopei__DOT__qd_data
                : vlSelf->main__DOT__emmcscopei__DOT__ck_addr);
    } else {
        vlSelf->main__DOT__emmcscopei__DOT__lst_val = 0U;
        vlSelf->main__DOT__emmcscopei__DOT__imm_val = 0U;
    }
    vlSelf->main__DOT__sdioscopei__DOT__lst_adr = (1U 
                                                   & ((~ 
                                                       ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                                                        >> 2U)) 
                                                      | (IData)(vlSelf->main__DOT__sdioscopei__DOT__imm_adr)));
    if ((4U & (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config))) {
        vlSelf->main__DOT__sdioscopei__DOT__lst_val 
            = vlSelf->main__DOT__sdioscopei__DOT__imm_val;
        vlSelf->main__DOT__sdioscopei__DOT__imm_val 
            = ((((IData)(vlSelf->main__DOT__sdioscopei__DOT__new_data) 
                 | (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_force_write)) 
                | (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped))
                ? vlSelf->main__DOT__sdioscopei__DOT__qd_data
                : vlSelf->main__DOT__sdioscopei__DOT__ck_addr);
    } else {
        vlSelf->main__DOT__sdioscopei__DOT__lst_val = 0U;
        vlSelf->main__DOT__sdioscopei__DOT__imm_val = 0U;
    }
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__nxt_wrptr 
        = (0x7fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr)));
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cword 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl
        [vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cmd_addr];
    if (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
         & (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb)))))) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_word 
            = vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word;
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__rd_len 
            = (0x3ffU & ((1U & (IData)((vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                        >> 0x22U)))
                          ? ((IData)(9U) + ((0x1c0U 
                                             & ((IData)(
                                                        (vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                                         >> 0x1fU)) 
                                                << 6U)) 
                                            | (0x3fU 
                                               & (IData)(
                                                         (vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                                          >> 0x18U)))))
                          : ((IData)(1U) + (7U & (IData)(
                                                         (vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                                          >> 0x1fU))))));
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cmd_addr 
            = (0xffU & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr) 
                        - ((0xc0U & ((IData)((vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                              >> 0x1fU)) 
                                     << 6U)) | (0x3fU 
                                                & (IData)(
                                                          (vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                                           >> 0x18U))))));
    }
    if ((0U == (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state))) {
        vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_inc 
            = (1U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                             >> 0x1eU)));
        vlSelf->main__DOT__wbu_we = (1U & (~ (IData)(
                                                     (vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                                      >> 0x23U))));
    }
    vlSelf->main__DOT__wbu_idata = ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mgrant)
                                     ? vlSelf->main__DOT__wbu_xbar__DOT__s_data
                                    [vlSelf->main__DOT__wbu_xbar__DOT__mindex
                                    [0U]] : 0U);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__nxt_wrptr 
        = (0x7ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr)));
    vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__exec_stb) 
           | (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_empty_n));
    if (vlSelf->main__DOT__genbus__DOT__r_wdt_reset) {
        vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_new_addr = 1U;
    } else if (((((~ (IData)(vlSelf->main__DOT__wbu_cyc)) 
                  & (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n)) 
                 & (~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy))) 
                & (2U != (3U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                        >> 0x22U)))))) {
        vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_new_addr 
            = ((0U == (0xfU & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                       >> 0x20U)))) 
               | (1U == (7U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                       >> 0x21U)))));
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched)) 
               & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__w_match))))) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_hlfd 
            = (7U & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__maddr) 
                     - (IData)(2U)));
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_dbld 
            = (0x3ffU & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__maddr) 
                         - (IData)(0xaU)));
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__zmatch 
        = ((~ (((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
                | ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)))) 
               | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__pmatch)))) 
           & (2U == (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr)));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__hmatch 
        = ((~ (((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
                | ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)))) 
               | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__pmatch)))) 
           & (0xbU > (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr)));
    if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy)))) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word 
            = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__a_addrword;
    }
    vlSelf->main__DOT__wbu_xbar__DOT__w_mpending[0U] 
        = vlSelf->main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__wbu_cyc))) 
               | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->main__DOT__wbu_xbar__DOT__mfull = 0U;
    } else if ((1U == ((((IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stall))) 
                        << 1U) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->main__DOT__wbu_xbar__DOT__mfull = 0U;
    } else if ((2U == ((((IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stall))) 
                        << 1U) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->main__DOT__wbu_xbar__DOT__mfull = vlSelf->main__DOT__wbu_xbar__DOT__mnearfull;
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel 
        = ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))
            ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))
                ? (((QData)((IData)((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel)))) 
                    << 0x3fU) | (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel 
                                 >> 1U)) : (((QData)((IData)(
                                                             (3U 
                                                              & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel)))) 
                                             << 0x3eU) 
                                            | (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel 
                                               >> 2U)))
            : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))
                ? (((QData)((IData)((0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel)))) 
                    << 0x3cU) | (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel 
                                 >> 4U)) : 0xffffffffffffffffULL));
    if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc)))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel;
    }
    if (vlSelf->main__DOT__wbwide_wbdown_stall) {
        if ((1U & ((~ (IData)(vlSelf->main__DOT__wb32_wbdown_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))))) {
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel 
                = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_sel;
        }
    } else {
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel 
            = ((1U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb))
                ? (((QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[1U])) 
                    << 0x20U) | (QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[0U])))
                : 0ULL);
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__tag_lookup 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__isrc)
            ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__pc_tag_lookup
            : vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_tag_lookup);
    if ((1U & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant))) {
        if ((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_stall)))) {
            vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
                = ((0x3ffffff8000000ULL & vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr) 
                   | (IData)((IData)(((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                       [0U]) ? vlSelf->main__DOT__wbu_xbar__DOT__m_addr
                                      [vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                      [0U]] : 0U))));
        }
    } else {
        vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
            = (0x3ffffff8000000ULL & vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr);
    }
    if ((2U & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant))) {
        if ((1U & (~ ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_stall) 
                      >> 1U)))) {
            vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
                = ((0x7ffffffULL & vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr) 
                   | ((QData)((IData)(((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                        [1U]) ? vlSelf->main__DOT__wbu_xbar__DOT__m_addr
                                       [vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                       [1U]] : 0U))) 
                      << 0x1bU));
        }
    } else {
        vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
            = (0x7ffffffULL & vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr);
    }
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err 
        = ((((~ (IData)(vlSelf->i_reset)) & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc)) 
            & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc)) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
              >> 3U));
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid = 0U;
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__rx_valid)) 
                      | (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full))))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid 
            = (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last) 
                | (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready)) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_last))) 
               | (0U != (3U & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__next_fill) 
                               >> 6U))));
    }
    vlSelf->cpu_sim_ack = ((IData)(vlSelf->cpu_sim_cyc) 
                           & (IData)(vlSelf->main__DOT__raw_cpu_dbg_ack));
    vlSelf->main__DOT__swic__DOT__dbg_ack = ((~ ((IData)(vlSelf->main__DOT____Vcellinp__swic__i_reset) 
                                                 | (~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_cyc)))) 
                                             & ((IData)(vlSelf->main__DOT__swic__DOT__dbg_pre_ack) 
                                                | (IData)(vlSelf->main__DOT__swic__DOT__cmd_read_ack)));
    vlSelf->main__DOT__swic__DOT__ctri_int = ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset)) 
                                              & ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie) 
                                                 & (IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__w_any)));
    vlSelf->main__DOT__swic__DOT__tma_int = ((~ (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                                                  | (IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__wb_write)) 
                                                 | (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt))) 
                                             & (1U 
                                                == vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value));
    vlSelf->main__DOT__swic__DOT__tmb_int = ((~ (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                                                  | (IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__wb_write)) 
                                                 | (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt))) 
                                             & (1U 
                                                == vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value));
    vlSelf->main__DOT__swic__DOT__tmc_int = ((~ (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                                                  | (IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__wb_write)) 
                                                 | (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt))) 
                                             & (1U 
                                                == vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    if (((8U == (0x1fU & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) 
         & (0U != (7U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count) 
                         >> 5U))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_data 
            = (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg);
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data = 0U;
    } else if ((2U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data 
            = (IData)((0xffffffffULL & ((0xffffffff000000ULL 
                                         & ((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data)) 
                                            << 0x18U)) 
                                        | (((0x27U 
                                             >= ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             ? (((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data)) 
                                                 << 0x18U) 
                                                >> 
                                                ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             : 0ULL) 
                                           >> 8U))));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data 
            = (0xffU & (IData)(((0x27U >= ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                           << 3U)) ? 
                                (0xffffffffffULL & 
                                 (((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data)) 
                                   << 0x18U) >> ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U)))
                                 : 0ULL)));
    } else if ((1U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data 
            = (IData)((0xffffffffULL & ((0xffffffff000000ULL 
                                         & ((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data)) 
                                            << 0x18U)) 
                                        | (((0x27U 
                                             >= ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             ? (((QData)((IData)(
                                                                 (0xffU 
                                                                  & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data) 
                                                                     >> 8U)))) 
                                                 << 0x20U) 
                                                >> 
                                                ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             : 0ULL) 
                                           >> 8U))));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data 
            = (0xffU & (IData)(((0x27U >= ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                           << 3U)) ? 
                                (0xffffffffffULL & 
                                 (((QData)((IData)(
                                                   (0xffU 
                                                    & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data) 
                                                       >> 8U)))) 
                                   << 0x20U) >> ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U)))
                                 : 0ULL)));
    } else {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data 
            = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data) 
               << 0x18U);
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data 
            = (0xffU & 0U);
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_valid 
        = ((~ (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                  | (2U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))) 
                 | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout)) 
               | (4U <= (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr)))) 
           & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data) 
              & ((8U == (0x1fU & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) 
                 & (0U != (7U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count) 
                                 >> 5U))))));
    if (((8U == (0x1fU & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) 
         & (0U != (7U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count) 
                         >> 5U))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_data 
            = (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg);
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data = 0U;
    } else if ((2U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data 
            = (IData)((0xffffffffULL & ((0xffffffff000000ULL 
                                         & ((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data)) 
                                            << 0x18U)) 
                                        | (((0x27U 
                                             >= ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             ? (((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data)) 
                                                 << 0x18U) 
                                                >> 
                                                ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             : 0ULL) 
                                           >> 8U))));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data 
            = (0xffU & (IData)(((0x27U >= ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                           << 3U)) ? 
                                (0xffffffffffULL & 
                                 (((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data)) 
                                   << 0x18U) >> ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U)))
                                 : 0ULL)));
    } else if ((1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data 
            = (IData)((0xffffffffULL & ((0xffffffff000000ULL 
                                         & ((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data)) 
                                            << 0x18U)) 
                                        | (((0x27U 
                                             >= ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             ? (((QData)((IData)(
                                                                 (0xffU 
                                                                  & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data) 
                                                                     >> 8U)))) 
                                                 << 0x20U) 
                                                >> 
                                                ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U))
                                             : 0ULL) 
                                           >> 8U))));
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data 
            = (0xffU & (IData)(((0x27U >= ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                           << 3U)) ? 
                                (0xffffffffffULL & 
                                 (((QData)((IData)(
                                                   (0xffU 
                                                    & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data) 
                                                       >> 8U)))) 
                                   << 0x20U) >> ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                                                 << 3U)))
                                 : 0ULL)));
    } else {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data 
            = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data) 
               << 0x18U);
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data 
            = (0xffU & 0U);
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_valid 
        = ((~ (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                  | (2U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))) 
                 | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout)) 
               | (4U <= (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr)))) 
           & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data) 
              & ((8U == (0x1fU & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) 
                 & (0U != (7U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count) 
                                 >> 5U))))));
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[0U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[1U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[2U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[3U] 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending;
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc))) 
               | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((1U == ((2U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                               & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall))) 
                              << 1U)) | (1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((2U == ((2U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                               & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall))) 
                              << 1U)) | (1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = ((0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull)) 
               | (1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull)));
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                                               >> 1U))) 
               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                  >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((1U == ((2U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                              & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
                                     >> 1U)) << 1U))) 
                       | (1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((2U == ((2U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                              & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
                                     >> 1U)) << 1U))) 
                       | (1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = ((0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull)) 
               | (2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull)));
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                                               >> 2U))) 
               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                  >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((1U == ((2U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                               >> 1U) & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
                                             >> 2U)) 
                                         << 1U))) | 
                       (1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                              >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((2U == ((2U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                               >> 1U) & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
                                             >> 2U)) 
                                         << 1U))) | 
                       (1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                              >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = ((0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull)) 
               | (4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull)));
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                                               >> 3U))) 
               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                  >> 3U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((1U == (((IData)((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                                  >> 3U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
                                               >> 3U)))) 
                        << 1U) | (1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                        >> 3U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull));
    } else if ((2U == (((IData)((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                                  >> 3U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
                                               >> 3U)))) 
                        << 1U) | (1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                        >> 3U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mfull 
            = ((7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull)) 
               | (8U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull)));
    }
    vlSelf->main__DOT__wb32_xbar__DOT__w_mpending[0U] 
        = vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    if (vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) {
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[1U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[2U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[3U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[4U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[5U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[6U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[7U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[8U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[9U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xaU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xbU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xcU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xdU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xeU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xfU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x10U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x11U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U];
    } else {
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[1U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[1U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[2U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[2U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[3U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[3U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[4U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[4U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[5U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[5U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[6U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[6U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[7U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[7U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[8U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[8U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[9U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[9U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xaU] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0xaU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xbU] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0xbU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xcU] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0xcU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xdU] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0xdU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xeU] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0xeU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xfU] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0xfU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x10U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0x10U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x11U] 
            = Vmain__ConstPool__CONST_hb679b2e5_0[0x11U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U] 
            = vlSelf->main__DOT__wbwide_i2cm_addr;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    if (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__clear_table) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_filled = 0U;
    } else if ((0x3ffU == (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr))) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_filled = 1U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__request[1U] 
        = (((IData)(vlSelf->main__DOT__wbwide_i2cm_cyc) 
            & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_valid))
            ? (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__decoded)
            : 0U);
    vlSelf->main__DOT__i2cscopei__DOT__this_addr = 
        (0x3ffU & ((IData)(vlSelf->main__DOT__i2cscopei__DOT__read_from_data)
                    ? ((IData)(1U) + ((IData)(vlSelf->main__DOT__i2cscopei__DOT__raddr) 
                                      + (IData)(vlSelf->main__DOT__i2cscopei__DOT__waddr)))
                    : ((IData)(vlSelf->main__DOT__i2cscopei__DOT__raddr) 
                       + (IData)(vlSelf->main__DOT__i2cscopei__DOT__waddr))));
    vlSelf->main__DOT__emmcscopei__DOT__this_addr = 
        (0xfffU & ((IData)(vlSelf->main__DOT__emmcscopei__DOT__read_from_data)
                    ? ((IData)(1U) + ((IData)(vlSelf->main__DOT__emmcscopei__DOT__raddr) 
                                      + (IData)(vlSelf->main__DOT__emmcscopei__DOT__waddr)))
                    : ((IData)(vlSelf->main__DOT__emmcscopei__DOT__raddr) 
                       + (IData)(vlSelf->main__DOT__emmcscopei__DOT__waddr))));
    vlSelf->main__DOT__sdioscopei__DOT__this_addr = 
        (0xfffU & ((IData)(vlSelf->main__DOT__sdioscopei__DOT__read_from_data)
                    ? ((IData)(1U) + ((IData)(vlSelf->main__DOT__sdioscopei__DOT__raddr) 
                                      + (IData)(vlSelf->main__DOT__sdioscopei__DOT__waddr)))
                    : ((IData)(vlSelf->main__DOT__sdioscopei__DOT__raddr) 
                       + (IData)(vlSelf->main__DOT__sdioscopei__DOT__waddr))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_he857573c__0 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd) 
           | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_wF));
    if (((IData)(vlSelf->main__DOT__wb32_sirefclk_stb) 
         & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
            >> 9U))) {
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x24U)))) {
            vlSelf->main__DOT__r_sirefclk_data = ((0x3fffff00U 
                                                   & vlSelf->main__DOT__r_sirefclk_data) 
                                                  | (0xffU 
                                                     & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x25U)))) {
            vlSelf->main__DOT__r_sirefclk_data = ((0x3fff00ffU 
                                                   & vlSelf->main__DOT__r_sirefclk_data) 
                                                  | (0xff00U 
                                                     & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x26U)))) {
            vlSelf->main__DOT__r_sirefclk_data = ((0x3f00ffffU 
                                                   & vlSelf->main__DOT__r_sirefclk_data) 
                                                  | (0xff0000U 
                                                     & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x27U)))) {
            vlSelf->main__DOT__r_sirefclk_data = ((0xffffffU 
                                                   & vlSelf->main__DOT__r_sirefclk_data) 
                                                  | (0x3f000000U 
                                                     & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U]));
        }
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr 
        = ((~ (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_full)) 
           & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)) 
              & (IData)(vlSelf->main__DOT__wbwide_wbu_arbiter_stb)));
    if (vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) {
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[1U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[2U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[3U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[4U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[5U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[6U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[7U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[8U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[9U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xaU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xbU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xcU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xdU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xeU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xfU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x10U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x11U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U];
    } else {
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[1U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[1U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[2U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[2U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[3U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[3U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[4U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[4U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[5U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[5U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[6U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[6U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[7U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[7U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[8U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[8U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[9U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[9U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xaU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0xaU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xbU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0xbU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xcU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0xcU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xdU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0xdU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xeU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0xeU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xfU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0xfU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x10U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0x10U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x11U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0x11U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data[0x12U];
    }
    vlSelf->main__DOT__wbu_wbu_arbiter_stall = ((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_stb) 
                                                & ((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_full) 
                                                   | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_we = 
        (1U & ((IData)(vlSelf->cpu_sim_cyc) ? (IData)(vlSelf->cpu_sim_we)
                : ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_swe) 
                   >> 1U)));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb)) 
               | (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall))))) {
        vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data 
            = (((QData)((IData)((1U & (IData)((vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                               >> 0x3fU))))) 
                << 0x24U) | (0xfffffffffULL & vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data));
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__instruction_decoder__i_reset) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable = 0U;
    } else if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) 
                 & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__pf_valid)) 
                    | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal))) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable 
            = (((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_mem) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB)) 
                 & (7U != (7U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preB) 
                                 >> 1U)))) & (7U != 
                                              (7U & 
                                               ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA) 
                                                >> 1U)))) 
               & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                  | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preB) 
                     != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA))));
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
         & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__saddr 
            = (7U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr) 
                     >> 3U));
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__svmask 
        = ((~ ((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache))) 
           & ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack)) 
               & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack)) 
              & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__needload 
        = ((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc))) 
           & ((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_advance) 
                  & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal)))) 
              & (((0U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay)) 
                  & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_v_from_last))) 
                 & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid)) 
                    | ((0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                                    >> 9U)) != vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache)))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_pedge 
        = ((((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__last_ck)) 
             & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__sdclk) 
                >> 7U)) << 1U) | (IData)((8U == (0x88U 
                                                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__sdclk)))));
    vlSelf->o_sirefclk_ce = vlSelf->main__DOT__r_sirefclk_en;
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_abort))) {
        vlSelf->main__DOT__i2ci__DOT__insn_valid = 0U;
    } else if (((IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual) 
                | (IData)(vlSelf->main__DOT__i2ci__DOT__bus_manual))) {
        vlSelf->main__DOT__i2ci__DOT__insn_valid = 0U;
    } else if (vlSelf->main__DOT__i2ci__DOT__next_valid) {
        vlSelf->main__DOT__i2ci__DOT__insn_valid = 
            ((IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle) 
             | ((3U != (0xfU & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                >> 4U))) & (0xdU != 
                                            (0xfU & 
                                             ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                              >> 4U)))));
    } else if (((((~ (IData)(vlSelf->main__DOT__i2ci__DOT__half_valid)) 
                  | (3U == (IData)(vlSelf->main__DOT__i2ci__DOT__half_insn))) 
                 | (0xdU == (IData)(vlSelf->main__DOT__i2ci__DOT__half_insn))) 
                & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready))) {
        vlSelf->main__DOT__i2ci__DOT__insn_valid = 0U;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy = 1U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit) 
                | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__zero_divisor))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy = 0U;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_pc_valid 
        = ((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy))) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_alu_pc_valid));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OPLOCK__DOT__r_op_lock = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OPLOCK__DOT__r_op_lock 
            = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_lock)) 
               & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal)));
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_break 
            = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
               & (0x7000000U == (0x7c00000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword)));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wF 
            = ((8U == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                               >> 1U))) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h9ed30f6d__0) 
                                            | (0U == 
                                               (7U 
                                                & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                   >> 0x13U)))) 
                                           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_he52a0fcf__0) 
                                              | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_ALU) 
                                                 & ((0xdU 
                                                     != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                                    & ((9U 
                                                        != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                                       & ((8U 
                                                           != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                                          & (7U 
                                                             != 
                                                             (7U 
                                                              & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                                 >> 0x1cU))))))))));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B 
            = ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB) 
                 & (0xeU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h20660d0e__0))) 
                << 6U) | ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB) 
                            & (0xfU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h20660d0e__0))) 
                           << 5U) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preB)));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_DIV 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_div;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim 
            = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
                & (0x7800000U == (0x7c00000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword))) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_noop));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ALU 
            = ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_ALU) 
                 | (0xcU == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                     >> 1U)))) | (8U 
                                                  == 
                                                  (0xfU 
                                                   & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                                      >> 1U)))) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_noop));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_lock 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_lock;
    }
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_waddr_plus_one 
        = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr)));
    vlSelf->main__DOT__console__DOT__tx_uart_reset 
        = (((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
              >> 5U) & (IData)(((0U == (0x300U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                                & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                   >> 0x14U)))) & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                                   >> 5U)) 
           | (((IData)((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                         >> 5U) & (0x300U == (0x300U 
                                              & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])))) 
               & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                  >> 5U)) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[5U] 
                              >> 0xcU) & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                  >> 0x15U)))));
    vlSelf->main__DOT__wbu_rx_stb = (((IData)(vlSelf->main__DOT__rcv__DOT__zero_baud_counter) 
                                      & (8U == (IData)(vlSelf->main__DOT__rcv__DOT__state))) 
                                     & (IData)(vlSelf->main__DOT__rcv__DOT__ck_uart));
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write 
        = ((IData)(vlSelf->main__DOT__w_console_rx_stb) 
           & ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow)) 
              | (IData)(vlSelf->main__DOT__console__DOT__rxf_wb_read)));
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_waddr_plus_one 
        = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr)));
    vlSelf->main__DOT__console__DOT__rx_uart_reset = 0U;
    if ((0x20U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                  & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)))) {
        if ((IData)(((0U == (0x300U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                     & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                        >> 0x14U)))) {
            vlSelf->main__DOT__console__DOT__rx_uart_reset = 1U;
        }
        if (((IData)(((0x200U == (0x300U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                      & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                         >> 0x15U))) & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[5U] 
                                        >> 0xcU))) {
            vlSelf->main__DOT__console__DOT__rx_uart_reset = 1U;
        }
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__i2c_valid)) 
               | (IData)(vlSelf->main__DOT__i2c_ready)))) {
        vlSelf->main__DOT__i2c_data = vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg;
        vlSelf->main__DOT__i2c_last = vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte;
    }
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__r_halted));
    vlSelf->o_emmc_clk = (1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__sdclk) 
                                >> 7U));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_pc_valid 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset)) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce));
    if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
         | ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem)) 
             & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc))) 
            & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_stalled))))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PC__DOT__r_alu_pc 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_OP_PC__DOT__r_op_pc;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_ALU_ILLEGAL__DOT__r_alu_illegal 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal)));
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OPT_CIS_OP_PHASE__DOT__r_op_phase = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid = 0U;
    } else {
        if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
              | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce)) 
             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OPT_CIS_OP_PHASE__DOT__r_op_phase;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
                    | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase = 0U;
        }
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem 
                = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_M) 
                    & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal))) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_valid));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal 
                = ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid) 
                     & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp))) 
                    & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch))) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OPT_CIS_OP_PHASE__DOT__r_op_phase 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase) 
                   & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wR)) 
                      | (~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R) 
                            >> 5U))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_valid) 
                   | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch));
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
                    | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem = 0U;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid = 0U;
        }
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready 
        = (1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    if (((IData)(vlSelf->main__DOT__u_fan__DOT__i2cd_valid) 
         & (IData)(vlSelf->main__DOT__u_fan__DOT__i2cd_last))) {
        vlSelf->main__DOT__u_fan__DOT__temp_data = 
            ((vlSelf->main__DOT__u_fan__DOT__temp_tmp 
              << 8U) | (IData)(vlSelf->main__DOT__u_fan__DOT__i2cd_data));
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request = 0U;
    } else if (((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write) 
                  & (0U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U]))) 
                 & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U] 
                    >> 0x16U)) & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                          >> 0x1eU)))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request = 1U;
    }
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda 
        = ((IData)(vlSelf->i_reset) | ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual)
                                        ? (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda)
                                        : (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda)));
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl 
        = ((IData)(vlSelf->i_reset) | ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual)
                                        ? (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl)
                                        : (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl)));
    if (vlSelf->i_reset) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc = 1U;
        vlSelf->main__DOT__i2ci__DOT__cpu_new_pc = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__w_sdclk = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__w_sdclk = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_reset = 1U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_counter = 0U;
        vlSelf->main__DOT__u_fan__DOT__tach_count = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_timer = 0U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data = 0U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ckcount = 0xc8U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err = 0U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted = 0U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__counter = 0U;
        vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb = 0U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda = 1U;
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl = 1U;
        vlSelf->main__DOT__u_fan__DOT__pp_ms = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__trigger_counter = 0x1869fU;
    } else {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc = 0U;
        if ((((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
                & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
               & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle))) 
              & (0xc0U == (0xf0U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn)))) 
             | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid) 
                 & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready)) 
                & (0xcU == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn))))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc = 1U;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc = 1U;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc = 1U;
        }
        vlSelf->main__DOT__i2ci__DOT__cpu_new_pc = 0U;
        if ((((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
                & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
               & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle))) 
              & (0xc0U == (0xf0U & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_insn)))) 
             | (((IData)(vlSelf->main__DOT__i2ci__DOT__half_valid) 
                 & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready)) 
                & (0xcU == (IData)(vlSelf->main__DOT__i2ci__DOT__half_insn))))) {
            vlSelf->main__DOT__i2ci__DOT__cpu_new_pc = 1U;
        }
        if (vlSelf->main__DOT__i2ci__DOT__i2c_abort) {
            vlSelf->main__DOT__i2ci__DOT__cpu_new_pc = 1U;
        }
        if (vlSelf->main__DOT__i2ci__DOT__bus_jump) {
            vlSelf->main__DOT__i2ci__DOT__cpu_new_pc = 1U;
        }
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__w_sdclk 
            = (0xffU & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk) 
                          & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown)) 
                         | (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd)))
                         ? ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown)
                             ? 0U : ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90)
                                      ? 0x66U : 0x33U))
                         : ((1U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd))
                             ? ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90)
                                 ? 0x3cU : 0xfU) : 
                            ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd))
                              ? ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90)
                                  ? ((0x200U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))
                                      ? 0xf0U : 0xfU)
                                  : ((0x200U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))
                                      ? 0xffU : 0U))
                              : ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90)
                                  ? (- (IData)((1U 
                                                & VL_REDXOR_16(
                                                               (0x300U 
                                                                & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))))))
                                  : (- (IData)((1U 
                                                & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter) 
                                                   >> 9U)))))))));
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__w_sdclk 
            = (0xffU & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk) 
                          & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown)) 
                         | (0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd)))
                         ? ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown)
                             ? 0U : ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90)
                                      ? 0x66U : 0x33U))
                         : ((1U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd))
                             ? ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90)
                                 ? 0x3cU : 0xfU) : 
                            ((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd))
                              ? ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90)
                                  ? ((0x200U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))
                                      ? 0xf0U : 0xfU)
                                  : ((0x200U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))
                                      ? 0xffU : 0U))
                              : ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90)
                                  ? (- (IData)((1U 
                                                & VL_REDXOR_16(
                                                               (0x300U 
                                                                & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))))))
                                  : (- (IData)((1U 
                                                & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter) 
                                                   >> 9U)))))))));
        if (vlSelf->main__DOT__u_fan__DOT__tach_reset) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_reset = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_timer = 0x5f5e0ffU;
            vlSelf->main__DOT__u_fan__DOT__tach_count 
                = vlSelf->main__DOT__u_fan__DOT__tach_counter;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_counter 
                = (((IData)(vlSelf->main__DOT__u_fan__DOT__ck_tach) 
                    & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__last_tach)))
                    ? 1U : 0U);
        } else {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_counter 
                = (0x7ffffffU & (vlSelf->main__DOT__u_fan__DOT__tach_counter 
                                 + (((IData)(vlSelf->main__DOT__u_fan__DOT__ck_tach) 
                                     & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__last_tach)))
                                     ? 1U : 0U)));
            vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_timer 
                = (0x7ffffffU & (vlSelf->main__DOT__u_fan__DOT__tach_timer 
                                 - (IData)(1U)));
            vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_reset 
                = (1U >= vlSelf->main__DOT__u_fan__DOT__tach_timer);
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted) {
            if (vlSelf->main__DOT__u_fan__DOT__i2cd_valid) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data 
                    = (0x200U | (((IData)(vlSelf->main__DOT__u_fan__DOT__i2cd_last) 
                                  << 8U) | (IData)(vlSelf->main__DOT__u_fan__DOT__i2cd_data)));
            }
            if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data 
                    = (0x1ffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data));
            }
        } else {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data 
                = (0x1ffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data));
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write) 
              & (0x3000000U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U]))) 
             & (0xf0000000ULL == (0xf0000000ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel)))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ckcount 
                = (0xfffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]);
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err = 1U;
        }
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort) 
             & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted)))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted = 1U;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write) {
            if (((IData)(((0U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                          & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U] 
                             >> 0x14U))) & (IData)(
                                                   (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                    >> 0x1eU)))) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err = 0U;
            }
            if (((IData)(((0U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                          & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U] 
                             >> 0x15U))) & (IData)(
                                                   (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                    >> 0x1eU)))) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted = 0U;
            }
            if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) 
                 & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted))) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err = 0U;
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted = 0U;
            }
        }
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted) 
             | (IData)(vlSelf->main__DOT__u_fan__DOT__pp_ms))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait = 0U;
        } else {
            if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
                 & (0x800U == (0xf00U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))))) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait = 1U;
            }
            if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
                vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait = 0U;
            }
        }
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__counter 
            = (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk) 
                & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown))
                ? 0x300U : (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter));
        if ((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall)))) {
            vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb 
                = vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid;
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write) 
              & (0x1000000U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U]))) 
             & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                        >> 0x1dU)))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda 
                = (IData)((0x800U != (0x4800U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U])));
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl 
                = (IData)((0x800U != (0x8800U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U])));
        } else if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda = 1U;
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl = 1U;
        }
        if ((0U == vlSelf->main__DOT__u_fan__DOT__trigger_counter)) {
            vlSelf->main__DOT__u_fan__DOT__pp_ms = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__trigger_counter = 0x1869fU;
        } else {
            vlSelf->main__DOT__u_fan__DOT__pp_ms = 
                (1U >= vlSelf->main__DOT__u_fan__DOT__trigger_counter);
            vlSelf->__Vdly__main__DOT__u_fan__DOT__trigger_counter 
                = (0x1ffffU & (vlSelf->main__DOT__u_fan__DOT__trigger_counter 
                               - (IData)(1U)));
        }
    }
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0U] 
        = (IData)(vlSelf->main__DOT__wbwide_i2cdma_sel);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[1U] 
        = (IData)((vlSelf->main__DOT__wbwide_i2cdma_sel 
                   >> 0x20U));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[2U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[3U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[1U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[4U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[2U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[5U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[3U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[6U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[4U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[7U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[5U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[8U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[6U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[9U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[7U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xaU] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[8U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xbU] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[9U];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xcU] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0xaU];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xdU] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0xbU];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xeU] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0xcU];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xfU] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0xdU];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0x10U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0xeU];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0x11U] 
        = vlSelf->main__DOT__wbwide_i2cdma_data[0xfU];
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0x12U] 
        = (0x400000U | vlSelf->main__DOT__wbwide_i2cdma_addr);
    if (((((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_reset)) 
          | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__bus_err)) 
         | ((IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc) 
            & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc = 0U;
        vlSelf->main__DOT__wbwide_i2cdma_stb = 0U;
    } else if (vlSelf->main__DOT__wbwide_i2cdma_cyc) {
        if ((1U & (~ (IData)(vlSelf->__VdfgTmp_h503d14d1__0)))) {
            vlSelf->main__DOT__wbwide_i2cdma_stb = 0U;
        }
        if ((1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc = 0U;
        }
    } else if (vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid) {
        if (((IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_overflow) 
             & (~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__wb_last)))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc = 0U;
            vlSelf->main__DOT__wbwide_i2cdma_stb = 0U;
        } else {
            vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc = 1U;
            vlSelf->main__DOT__wbwide_i2cdma_stb = 1U;
        }
    }
    if ((1U & ((((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc))) 
                | (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err)) 
               | ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                  & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))))) {
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last = 1U;
    } else if (vlSelf->main__DOT__wbwide_wbdown_stall) {
        if ((1U & ((~ (IData)(vlSelf->main__DOT__wb32_wbdown_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))))) {
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last 
                = (0ULL == (0xfffffffffffffffULL & vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_sel));
        }
    } else {
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last 
            = (0ULL == (0xfffffffffffffffULL & (((QData)((IData)(
                                                                 vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[1U])) 
                                                 << 0x20U) 
                                                | (QData)((IData)(
                                                                  vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[0U])))));
        if ((1U & (~ (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb)))) {
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last = 1U;
        }
    }
    vlSelf->main__DOT__swic__DOT__dbg_pre_addr = (3U 
                                                  & ((IData)(vlSelf->main__DOT__swic__DOT__dbg_addr) 
                                                     >> 5U));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset
        [(0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))];
    if ((0xfU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc;
    } else if ((0xeU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg 
            = ((0xffff0000U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg) 
               | ((0x10U & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))
                   ? (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_uflags)
                   : (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_iflags)));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg 
            = (0xeb800000U | (0x7fffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg));
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg 
            = ((0xffffffdfU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg) 
               | (0x20U & ((IData)(vlSelf->main__DOT__swic__DOT__dbg_addr) 
                           << 1U)));
    }
    vlSelf->main__DOT__swic__DOT__sys_idata = ((4U 
                                                & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                ? (
                                                   (2U 
                                                    & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                    ? 
                                                   ((1U 
                                                     & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                     ? vlSelf->main__DOT__swic__DOT__pic_data
                                                     : vlSelf->main__DOT__swic__DOT__dmac_data)
                                                    : 
                                                   ((1U 
                                                     & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                     ? 
                                                    ((4U 
                                                      & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                      ? 
                                                     ((2U 
                                                       & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                       ? 
                                                      ((1U 
                                                        & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data
                                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data)
                                                       : 
                                                      ((1U 
                                                        & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data
                                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data))
                                                      : 
                                                     ((2U 
                                                       & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                       ? 
                                                      ((1U 
                                                        & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data
                                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data)
                                                       : 
                                                      ((1U 
                                                        & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data
                                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data)))
                                                     : 
                                                    ((2U 
                                                      & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                      ? 
                                                     ((1U 
                                                       & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                       ? vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter
                                                       : 
                                                      (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                                        << 0x1fU) 
                                                       | vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value))
                                                      : 
                                                     ((1U 
                                                       & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                       ? 
                                                      (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                                        << 0x1fU) 
                                                       | vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value)
                                                       : 
                                                      (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                                        << 0x1fU) 
                                                       | vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value)))))
                                                : (
                                                   (2U 
                                                    & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                    ? 
                                                   ((1U 
                                                     & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                     ? vlSelf->main__DOT__swic__DOT__ctri_data
                                                     : vlSelf->main__DOT__swic__DOT__r_wdbus_data)
                                                    : 
                                                   ((1U 
                                                     & (IData)(vlSelf->main__DOT__swic__DOT__ack_idx))
                                                     ? vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value
                                                     : 0U)));
    if (vlSelf->main__DOT__swic__DOT__cmd_reset) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_inc = 0U;
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_trigger = 0U;
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_sel = 0U;
        vlSelf->main__DOT__swic__DOT__jif_int = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel = 0xffffffffffffffffULL;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_cstb = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__user_step = 0U;
        vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel = 0xffffffffffffffffULL;
        vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload = 0U;
        vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload = 0U;
        vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload = 0U;
    } else {
        if (((((IData)(vlSelf->main__DOT__swic__DOT__dmac_stb) 
               & (IData)(vlSelf->main__DOT__swic__DOT__sys_we)) 
              & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request))) 
             & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy)))) {
            if ((1U & (~ ((IData)(vlSelf->main__DOT__swic__DOT__sys_addr) 
                          >> 1U)))) {
                if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__sys_addr)))) {
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_inc 
                        = (1U & (~ (vlSelf->main__DOT__swic__DOT__sys_data 
                                    >> 0x12U)));
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_trigger 
                        = (1U & (vlSelf->main__DOT__swic__DOT__sys_data 
                                 >> 0x1dU));
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_sel 
                        = (0x1fU & (vlSelf->main__DOT__swic__DOT__sys_data 
                                    >> 0x18U));
                }
            }
        }
        vlSelf->main__DOT__swic__DOT__jif_int = 0U;
        if ((((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
              & (IData)(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set)) 
             & (vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter 
                == vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_when))) {
            vlSelf->main__DOT__swic__DOT__jif_int = 1U;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set) 
                    & VL_GTES_III(32, 0U, vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_wb))) {
            vlSelf->main__DOT__swic__DOT__jif_int = 1U;
        }
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag = 0U;
        if (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc)) 
             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v 
                = ((IData)(vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v) 
                   | (0xffU & ((IData)(1U) << (7U & 
                                               ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr) 
                                                >> 3U)))));
        }
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_cstb = 0U;
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) {
            if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line 
                    = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)
                        ? (5U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr)))
                        : (6U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr))));
            }
        } else {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line = 0U;
        }
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb 
            = ((~ ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc)) 
                   | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb)))) 
               & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)
                   ? (7U == (7U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr))
                   : (3U == (3U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                                   >> 1U)))));
        if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))) {
            if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))) {
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr 
                    = (0x3fU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr) 
                                + ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)
                                    ? 1U : 0U)));
                if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb) 
                     & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                        = ((0x3ffff8U & vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr) 
                           | (7U & ((IData)(1U) + vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr)));
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb 
                        = (1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb)));
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl 
                        = (1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb)));
                }
                if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v 
                        = ((~ ((IData)(1U) << (7U & 
                                               (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                                                >> 3U)))) 
                           & (IData)(vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v));
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = 1U;
                } else {
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = 0U;
                }
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[1U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[1U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[2U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[2U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[3U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[3U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[4U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[4U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[5U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[5U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[6U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[6U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[7U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[7U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[8U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[8U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[9U] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[9U];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xaU] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0xaU];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xbU] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0xbU];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xcU] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0xcU];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xdU] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0xdU];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xeU] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0xeU];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xfU] 
                    = vlSelf->main__DOT__swic__DOT__cpu_idata[0xfU];
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel = 0xffffffffffffffffULL;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag 
                    = (1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err)));
                if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack) 
                      & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line)) 
                     | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
                }
            } else {
                if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)) 
                           & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce))))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
                }
                if (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)) 
                     & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                        = (0x3fffffU & ((0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                                   >> 0x18U))
                                         ? (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                            >> 2U) : 
                                        (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                         >> 6U)));
                }
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = 0U;
                if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack) 
                      & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack)) 
                     | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
                    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
                }
            }
        } else if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr 
                = (0x3fU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr);
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr 
                = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl) 
                    & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v) 
                       >> (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                                 >> 3U)))) & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_itag 
                                              == (0x7ffffU 
                                                  & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                                                     >> 3U))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[1U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[2U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[3U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[4U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[5U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[6U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[7U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[8U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[9U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xaU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xbU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xcU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xdU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xeU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xfU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU];
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_cstb 
                = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb) 
                    & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall))) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__in_cache));
            if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)) 
                       & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce))))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
            }
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                    = (0x3fffffU & ((0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                               >> 0x18U))
                                     ? (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                        >> 2U) : (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                                  >> 6U)));
            }
            if (((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack)) 
                  & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce))) 
                 | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 0U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 0U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 0U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = 0U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
            }
        } else {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_we = 0U;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__in_cache 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__w_cachable));
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 0U;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 0U;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 0U;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = 0U;
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                    = (0x3fffffU & ((0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                               >> 0x18U))
                                     ? (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                        >> 2U) : (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                                  >> 6U)));
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_we = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 1U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl 
                    = (0xffU != (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl 
                    = (0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl 
                    = (0xffU != (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl 
                    = (0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
            } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss) {
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr 
                    = (0x3fU & ((0x38U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr) 
                                - (IData)(1U)));
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 3U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                    = (0x3ffff8U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr);
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 1U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = 1U;
            } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                        & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__w_cachable)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = 2U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
                    = (0x3fffffU & ((0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                               >> 0x18U))
                                     ? (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                        >> 2U) : (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                                  >> 6U)));
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = 1U;
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl 
                    = (0xffU != (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl 
                    = (0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl 
                    = (0xffU != (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
                vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl 
                    = (0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                 >> 0x18U));
            }
        }
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__CLEAR_DCACHE__DOT__r_clear_dcache) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
              & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie))) 
             & (0x1eU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__user_step 
                = (1U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                         >> 6U));
        }
        if (((IData)(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set) 
             & VL_LTS_III(32, 0U, vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_wb))) {
            vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set = 1U;
        } else if (vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_now) {
            vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set = 0U;
        }
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
             & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__w_cachable))))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel 
                = ((0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                              >> 0x18U)) ? ((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel)) 
                                            >> (3U 
                                                & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr))
                    : (((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel)) 
                        << 0x3cU) >> (0x3fU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr)));
        } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel = 0xffffffffffffffffULL;
        }
        if (vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__wb_write) {
            vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload 
                = ((vlSelf->main__DOT__swic__DOT__sys_data 
                    >> 0x1fU) & (0U != (0x7fffffffU 
                                        & vlSelf->main__DOT__swic__DOT__sys_data)));
        }
        if (vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__wb_write) {
            vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload 
                = ((vlSelf->main__DOT__swic__DOT__sys_data 
                    >> 0x1fU) & (0U != (0x7fffffffU 
                                        & vlSelf->main__DOT__swic__DOT__sys_data)));
        }
        if (vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__wb_write) {
            vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload 
                = ((vlSelf->main__DOT__swic__DOT__sys_data 
                    >> 0x1fU) & (0U != (0x7fffffffU 
                                        & vlSelf->main__DOT__swic__DOT__sys_data)));
        }
    }
    vlSelf->main__DOT__swic__DOT__dbg_cpu_status = 
        ((((IData)(vlSelf->main__DOT__gpio_int) << 0x1bU) 
          | (((IData)(vlSelf->main__DOT__i2cscope_int) 
              << 0x1aU) | ((0x2000000U & ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)) 
                                          << 0x19U)) 
                           | ((0x1000000U & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow)) 
                                             << 0x18U)) 
                              | (((IData)(vlSelf->main__DOT__emmc_int) 
                                  << 0x17U) | (((IData)(vlSelf->main__DOT__sdioscope_int) 
                                                << 0x16U) 
                                               | (((IData)(vlSelf->main__DOT__emmcscope_int) 
                                                   << 0x15U) 
                                                  | ((IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0) 
                                                     << 0xcU)))))))) 
         | (((IData)(vlSelf->main__DOT__swic__DOT__cpu_break) 
             << 0xbU) | (((IData)(vlSelf->main__DOT__swic__DOT__pic_interrupt) 
                          << 0xaU) | ((0x300U & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                                                 << 8U)) 
                                      | (((IData)(vlSelf->main__DOT__swic__DOT__GEN_DBG_CATCH__DOT__r_dbg_catch) 
                                          << 5U) | 
                                         (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                                           << 3U) | 
                                          ((2U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall)) 
                                                  << 1U)) 
                                           | (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt))))))));
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg = 0U;
    } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_arg;
    } else if (((((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                  & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                     >> 6U)) & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                >> 6U)) & (0x10000U 
                                           == (0x70000U 
                                               & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])))) {
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x18U)))) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xffffff00U & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x19U)))) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xffff00ffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xff00U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x1aU)))) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xff00ffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xff0000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x1bU)))) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xffffffU & vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xff000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U]));
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_id = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_arg = 0U;
    } else {
        if ((8U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_id 
                = (0x3fU & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg));
        }
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_arg 
            = ((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))
                ? 0U : (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
                                >> 8U)));
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90 = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb) 
                & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x19U)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90 
            = (1U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                     >> 0xeU));
        if ((0x100U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U])) {
            vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90 = 1U;
        }
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg = 0U;
    } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_arg;
    } else if (((((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                  & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                     >> 8U)) & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                >> 8U)) & (1U == (7U 
                                                  & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U])))) {
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x20U)))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xffffff00U & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x21U)))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xffff00ffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xff00U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x22U)))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xff00ffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xff0000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]));
        }
        if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x23U)))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg 
                = ((0xffffffU & vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg) 
                   | (0xff000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]));
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_id = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_arg = 0U;
    } else {
        if ((8U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_id 
                = (0x3fU & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg));
        }
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_arg 
            = ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))
                ? 0U : (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
                                >> 8U)));
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90 = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb) 
                & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x21U)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90 
            = (1U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                     >> 0xeU));
        if ((0x100U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U])) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90 = 1U;
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en)) 
                  & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID) 
                & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_ready))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = 0xffffffffU;
        if ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
            if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) {
                vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg 
                    = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w;
            }
        }
    } else if (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb) 
                  & (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                 & (1U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                & (0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = 0xffffffffU;
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid)) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data 
            = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo)
                ? vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b
                : vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a);
    }
    if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data = 0xffffffffU;
    } else {
        if ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) {
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period 
                = (((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr) 
                    & (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed)))
                    ? 2U : ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr) 
                              & (1U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed))) 
                             | ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr)) 
                                & (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed))))
                             ? 1U : 0U));
        }
        if ((2U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) {
            if ((1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) {
                if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 0U;
                    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data = 0xffffffffU;
                }
                if ((1U & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 0U;
                }
            } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready) {
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 1U;
                if ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count))) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 3U;
                }
                vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data 
                    = ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))
                        ? ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)
                            ? vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg
                            : (0xffffU | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg) 
                                          << 0x10U)))
                        : ((1U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))
                            ? ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)
                                ? vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U]
                                : (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                                           >> 0x20U)))
                            : ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))
                                ? ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)
                                    ? vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U]
                                    : vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U])
                                : vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U])));
            }
        } else if ((1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) {
            if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID) 
                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_ready))) {
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 1U;
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 1U;
                vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data 
                    = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data;
                if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_last) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 2U;
                }
            }
        } else {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = 0U;
            vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data 
                = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID)
                    ? vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data
                    : 0xffffffffU);
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 0U;
            if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__start_packet) {
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate 
                    = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_last)
                        ? 2U : 1U);
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = 1U;
            }
        }
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_half 
        = (1U & ((IData)(vlSelf->i_reset) | ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk) 
                                               & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown)) 
                                              | (0U 
                                                 == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd))) 
                                             | ((1U 
                                                 == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd)) 
                                                | ((2U 
                                                    == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd))
                                                    ? 
                                                   ((0x200U 
                                                     & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter))
                                                     ? 1U
                                                     : 2U)
                                                    : 
                                                   (0x100U 
                                                    == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__counter)))))));
    if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
          | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done)) 
         | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_err = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout) 
                & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_err = 1U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done) 
                & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_err 
            = (1U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode));
    }
    if ((1U & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done)) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_err = 0U;
    } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done = 1U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_err 
            = (1U & (IData)(((((0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err)) 
                               | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err))) 
                              | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err))) 
                             | (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err)))));
    }
    if ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
          | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done)) 
         | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_err = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout) 
                & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_err = 1U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done) 
                & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_err 
            = (1U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode));
    }
    if ((1U & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done)) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_err = 0U;
    } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done = 1U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_err 
            = (1U & (IData)(((((0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err)) 
                               | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err))) 
                              | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err))) 
                             | (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err)))));
    }
    vlSelf->main__DOT__console__DOT____VdfgTmp_h60af6732__0 
        = (1U & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow)) 
                 | (IData)(vlSelf->main__DOT__w_console_busy)));
    vlSelf->main__DOT__console__DOT____Vcellinp__txfifo____pinNumber6 
        = (1U & ((~ (IData)(vlSelf->main__DOT__w_console_busy)) 
                 & (~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow))));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
           & (IData)(vlSelf->main__DOT__genbus__DOT__wbu_tx_stb));
    if (vlSelf->__Vdlyvset__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl[vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0] 
            = vlSelf->__Vdlyvval__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0;
    }
    vlSelf->main__DOT__wbu_xbar__DOT__s_data[0U] = 
        vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__rtn_data[0xfU];
    vlSelf->main__DOT__wbu_xbar__DOT__s_data[1U] = vlSelf->main__DOT__wbu_zip_idata;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched;
    vlSelf->main__DOT__wbu_xbar__DOT__mnearfull = vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__mnearfull;
    vlSelf->main__DOT__wbu_xbar__DOT__m_addr[0U] = vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr;
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc 
        = vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last 
        = vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last;
    vlSelf->main__DOT__swic__DOT__cmd_read_ack = vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read_ack;
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_i2cm_stb) 
              | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr;
    vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull 
        = vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__mnearfull;
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc))) 
               | (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__mfull = 0U;
    } else if ((1U == ((((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stall))) 
                        << 1U) | (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__mfull = 0U;
    } else if ((2U == ((((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stall))) 
                        << 1U) | (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__mfull = vlSelf->main__DOT__wb32_xbar__DOT__mnearfull;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__mnearfull = vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__mnearfull;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x80000U ^ (0x3fffffU 
                                           & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x100000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x200000U & (0x200000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 2U));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr 
        = vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr;
    vlSelf->main__DOT__i2cscopei__DOT__raddr = vlSelf->__Vdly__main__DOT__i2cscopei__DOT__raddr;
    vlSelf->main__DOT__i2cscopei__DOT__waddr = vlSelf->__Vdly__main__DOT__i2cscopei__DOT__waddr;
    vlSelf->main__DOT__emmcscopei__DOT__raddr = vlSelf->__Vdly__main__DOT__emmcscopei__DOT__raddr;
    vlSelf->main__DOT__emmcscopei__DOT__waddr = vlSelf->__Vdly__main__DOT__emmcscopei__DOT__waddr;
    vlSelf->main__DOT__sdioscopei__DOT__raddr = vlSelf->__Vdly__main__DOT__sdioscopei__DOT__raddr;
    vlSelf->main__DOT__sdioscopei__DOT__waddr = vlSelf->__Vdly__main__DOT__sdioscopei__DOT__waddr;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x80000U ^ (0x3fffffU 
                                           & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x100000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x200000U & (0x200000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 2U));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit 
        = vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit;
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_pedge 
        = ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__last_ck)) 
           & (IData)(vlSelf->o_emmc_clk));
    vlSelf->main__DOT__u_fan__DOT__tach_reset = vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_reset;
    vlSelf->main__DOT__u_fan__DOT__tach_counter = vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_counter;
    vlSelf->main__DOT__u_fan__DOT__tach_timer = vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_timer;
    vlSelf->main__DOT__u_fan__DOT__temp_tmp = vlSelf->__Vdly__main__DOT__u_fan__DOT__temp_tmp;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted 
        = vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted;
    if (vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) {
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[1U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[1U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[2U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[2U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[3U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[3U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[4U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[4U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[5U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[5U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[6U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[6U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[7U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[7U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[8U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[8U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[9U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[9U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xaU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xaU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xbU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xbU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xcU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xcU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xdU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xdU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xeU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xeU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xfU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0xfU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x10U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x10U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x11U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x11U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data[0x12U];
    } else {
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[1U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[1U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[2U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[2U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[3U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[3U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[4U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[4U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[5U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[5U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[6U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[6U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[7U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[7U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[8U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[8U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[9U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[9U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xaU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xaU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xbU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xbU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xcU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xcU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xdU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xdU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xeU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xeU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xfU] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0xfU];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x10U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0x10U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x11U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0x11U];
        vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U] 
            = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data[0x12U];
    }
    vlSelf->main__DOT__u_i2cdma__DOT__r_overflow = vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow;
    vlSelf->__VdfgTmp_h503d14d1__0 = (7U & (~ ((4U 
                                                & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)) 
                                                   << 2U)) 
                                               | ((2U 
                                                   & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)) 
                                                      << 1U)) 
                                                  | (1U 
                                                     & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))))));
    vlSelf->main__DOT__wbwide_i2cdma_cyc = vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc;
    if (vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0] 
            = vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0;
    }
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data;
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data 
        = vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data;
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value 
        = vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value;
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value 
        = vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value;
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value 
        = vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value;
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value 
        = vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_value;
    vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0 
        = (((IData)(vlSelf->main__DOT__spio_int) << 3U) 
           | ((4U & ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                     >> 3U)) | ((2U & ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill) 
                                       >> 4U)) | (IData)(vlSelf->main__DOT__sdcard_int))));
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow 
        = vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_underflow;
    vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow 
        = vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb 
        = vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U];
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
        = vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U];
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_read 
        = ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow)) 
           & (IData)(vlSelf->main__DOT__console__DOT____Vcellinp__txfifo____pinNumber6));
    if (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb) 
         & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy)))) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_bits 
            = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy)))) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_bits = 0x40U;
    }
    vlSelf->main__DOT__i2cscopei__DOT__imm_adr = (1U 
                                                  & ((~ 
                                                      ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                                                       >> 2U)) 
                                                     | (~ 
                                                        (((IData)(vlSelf->main__DOT__i2cscopei__DOT__new_data) 
                                                          | (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_force_write)) 
                                                         | (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped)))));
    vlSelf->main__DOT__emmcscopei__DOT__imm_adr = (1U 
                                                   & ((~ 
                                                       ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                                                        >> 2U)) 
                                                      | (~ 
                                                         (((IData)(vlSelf->main__DOT__emmcscopei__DOT__new_data) 
                                                           | (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_force_write)) 
                                                          | (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped)))));
    vlSelf->main__DOT__sdioscopei__DOT__imm_adr = (1U 
                                                   & ((~ 
                                                       ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                                                        >> 2U)) 
                                                      | (~ 
                                                         (((IData)(vlSelf->main__DOT__sdioscopei__DOT__new_data) 
                                                           | (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_force_write)) 
                                                          | (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped)))));
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data 
        = (0xfULL | (((QData)((IData)(vlSelf->main__DOT__wbu_we)) 
                      << 0x3fU) | (((QData)((IData)(
                                                    (0x7ffffffU 
                                                     & vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr))) 
                                    << 0x24U) | ((QData)((IData)(vlSelf->main__DOT__wbu_data)) 
                                                 << 4U))));
    if ((1U & ((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__wbu_cyc))))) {
        vlSelf->main__DOT__wbu_xbar__DOT__mgrant = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available) {
            vlSelf->main__DOT__wbu_xbar__DOT__mgrant = 1U;
        } else if (vlSelf->main__DOT__wbu_xbar__DOT__m_stb) {
            vlSelf->main__DOT__wbu_xbar__DOT__mgrant = 0U;
        }
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__maddr 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr;
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__pmatch 
        = ((~ (IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset)) 
           & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy));
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__w_match 
        = ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table) 
           & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dmatch) 
              & (0xe00000000ULL == (0xe00000000ULL 
                                    & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word))));
    if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_busy)))) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__a_addrword 
            = ((2U != (0xfU & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword 
                                       >> 0x20U))))
                ? vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword
                : ((8U & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck))
                    ? ((4U & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck))
                        ? ((2U & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck))
                            ? ((1U & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck))
                                ? (0x300000000ULL | (QData)((IData)(
                                                                    (0x3f000000U 
                                                                     & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword) 
                                                                        << 0x18U)))))
                                : (0x340000000ULL | (QData)((IData)(
                                                                    (0x3ffc0000U 
                                                                     & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword) 
                                                                        << 0x12U))))))
                            : (0x380000000ULL | (QData)((IData)(
                                                                (0x3ffff000U 
                                                                 & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword) 
                                                                    << 0xcU))))))
                        : (0x3c0000000ULL | (QData)((IData)(
                                                            (0x3fffffc0U 
                                                             & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword) 
                                                                << 6U))))))
                    : vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword));
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_sel 
        = ((0x3fU >= (0x1ffffffcU & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift) 
                                     << 2U))) ? (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel 
                                                 << 
                                                 (0x1ffffffcU 
                                                  & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift) 
                                                     << 2U)))
            : 0ULL);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data 
        = (((QData)((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_we)) 
            << 0x2cU) | (((QData)((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr)) 
                          << 0x24U) | (((QData)((IData)(
                                                        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xfU])) 
                                        << 4U) | (QData)((IData)(
                                                                 (0xfU 
                                                                  & (IData)(
                                                                            (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel 
                                                                             >> 0x3cU))))))));
    vlSelf->main__DOT__wbwide_wbu_arbiter_cyc = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc;
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbwide_xbar__DOT__request[3U] 
        = (((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc) 
            & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_valid))
            ? (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__decoded)
            : 0U);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc 
        = ((2U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc)) 
           | ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant) 
              & ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                  [0U]) & ((IData)(vlSelf->main__DOT__wbu_cyc) 
                           >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                           [0U]))));
    if ((1U & ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_err)))) {
        vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc 
            = (2U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc));
    }
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc 
        = ((1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc)) 
           | (0xfffffffeU & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant) 
                             & (((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                  [1U]) & ((IData)(vlSelf->main__DOT__wbu_cyc) 
                                           >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                           [1U])) << 1U))));
    if ((1U & ((IData)(vlSelf->i_reset) | ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_err) 
                                           >> 1U)))) {
        vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc 
            = (1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc));
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__rx_valid 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellinp__u_sfifo__i_reset)) 
           & ((1U != (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr) 
                       << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd))) 
              & ((2U == (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr) 
                          << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd)))
                  ? (0xfU == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill))
                  : (0x10U == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill)))));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid)) 
               | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn 
            = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid)
                ? (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_word)
                : (IData)(vlSelf->main__DOT__u_fan__DOT__mem_data));
    }
    vlSelf->main__DOT__swic__DOT__dbg_cyc = (1U & (
                                                   (~ 
                                                    ((IData)(vlSelf->main__DOT____Vcellinp__swic__i_reset) 
                                                     | (~ (IData)(vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc)))) 
                                                   & (~ (IData)(vlSelf->main__DOT__swic__DOT__no_dbg_err))));
    vlSelf->main__DOT__swic__DOT__dbg_pre_ack = ((~ 
                                                  ((IData)(vlSelf->main__DOT____Vcellinp__swic__i_reset) 
                                                   | (~ (IData)(vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc)))) 
                                                 & (((IData)(vlSelf->main__DOT__swic__DOT__dbg_stb) 
                                                     & (~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_stall))) 
                                                    & (~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_cpu_read))));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid)) 
               | (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)))) {
        vlSelf->main__DOT__i2ci__DOT__pf_insn = (0xffU 
                                                 & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)
                                                     ? 
                                                    ((vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
                                                      << 8U) 
                                                     | (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
                                                        >> 0x18U))
                                                     : 
                                                    ((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid)
                                                      ? 
                                                     ((vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xfU] 
                                                       << 8U) 
                                                      | (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word[0xfU] 
                                                         >> 0x18U))
                                                      : 
                                                     ((vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xfU] 
                                                       << 8U) 
                                                      | (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted[0xfU] 
                                                         >> 0x18U)))));
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data 
        = ((~ (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active))) 
           & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data 
        = ((~ (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active))) 
           & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb));
    vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mgrant) 
           & (((0xfffff800U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                               & ((IData)(vlSelf->main__DOT__wb32_ddr3_phy_ack) 
                                  << 0xbU))) | ((0xfffffc00U 
                                                 & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                    & ((IData)(vlSelf->main__DOT__r_cfg_ack) 
                                                       << 0xaU))) 
                                                | ((0xfffffe00U 
                                                    & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                       & ((IData)(vlSelf->main__DOT__r_wb32_sio_ack) 
                                                          << 9U))) 
                                                   | ((0xffffff00U 
                                                       & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                          & ((IData)(vlSelf->main__DOT__wb32_sdcard_ack) 
                                                             << 8U))) 
                                                      | ((0xffffff80U 
                                                          & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                             & ((IData)(vlSelf->main__DOT__wb32_fan_ack) 
                                                                << 7U))) 
                                                         | ((0xffffffc0U 
                                                             & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                & ((IData)(vlSelf->main__DOT__wb32_emmc_ack) 
                                                                   << 6U))) 
                                                            | ((0xffffffe0U 
                                                                & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                   & ((IData)(vlSelf->main__DOT__wb32_uart_ack) 
                                                                      << 5U))) 
                                                               | ((0xfffffff0U 
                                                                   & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                      & ((IData)(vlSelf->main__DOT__wb32_i2cdma_ack) 
                                                                         << 4U))) 
                                                                  | ((0xfffffff8U 
                                                                      & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                         & ((IData)(vlSelf->main__DOT__wb32_i2cs_ack) 
                                                                            << 3U))) 
                                                                     | ((0xfffffffcU 
                                                                         & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                            & ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_wb_ack) 
                                                                               << 2U))) 
                                                                        | ((0xfffffffeU 
                                                                            & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                               & ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_wb_ack) 
                                                                                << 1U))) 
                                                                           | ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                                              & (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack))))))))))))) 
              >> vlSelf->main__DOT__wb32_xbar__DOT__mindex
              [0U]));
    if ((0x1000U & vlSelf->main__DOT__wb32_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = 0U;
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc))) 
               | (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = 0U;
    }
    vlSelf->main__DOT__wbu_xbar__DOT__m_data[0U] = (IData)(
                                                           (vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data 
                                                            >> 4U));
    vlSelf->main__DOT__wbu_xbar__DOT__m_sel[0U] = (0xfU 
                                                   & (IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data));
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid = 1U;
    } else if ((((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack)) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack)) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort))) 
                & ((7U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr) 
                          >> 3U)) == (7U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid = 0U;
    }
    vlSelf->main__DOT__swic__DOT__cpu_we = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner) 
                                            & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_we));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_itag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags
        [(7U & ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_pipe_stalled)) 
                       & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending))))
                 ? (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                    >> 9U) : (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                              >> 3U)))];
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_lcl 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_lcl) 
           | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_gbl 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_gbl) 
           | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__CLEAR_DCACHE__DOT__r_clear_dcache 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset)) 
           & (((IData)(vlSelf->main__DOT__swic__DOT__cmd_clear_cache) 
               & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall))) 
              | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                  & (0xeU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id))) 
                 & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                    >> 0xfU))));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy)) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall))))) {
        if ((0U == (2U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                          >> 1U)))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU] 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata;
        } else if ((2U == (3U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                                 >> 1U)))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x10U) | (0xffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
        } else if ((3U == (3U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                                 >> 1U)))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU] 
                = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                    << 0x18U) | ((0xff0000U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                               << 0x10U)) 
                                 | ((0xff00U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata 
                                                << 8U)) 
                                    | (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata))));
        }
    }
    if (((((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_abort)) 
          | (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual)) 
         | (IData)(vlSelf->main__DOT__i2ci__DOT__bus_manual))) {
        vlSelf->main__DOT__i2ci__DOT__half_valid = 0U;
    } else if (((~ (IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle)) 
                & (IData)(vlSelf->main__DOT__i2ci__DOT__next_valid))) {
        vlSelf->main__DOT__i2ci__DOT__half_valid = 0U;
        if (((((3U != (0xfU & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                               >> 4U))) & (0xdU != 
                                           (0xfU & 
                                            ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                             >> 4U)))) 
              & (0U != (0xfU & (IData)(vlSelf->main__DOT__i2ci__DOT__next_insn)))) 
             & (9U != (0xfU & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                               >> 4U))))) {
            vlSelf->main__DOT__i2ci__DOT__half_valid = 1U;
        }
    } else if (vlSelf->main__DOT__i2ci__DOT__half_ready) {
        vlSelf->main__DOT__i2ci__DOT__half_valid = 0U;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__zero_divisor 
            = (0U == vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr);
    }
    if (vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN) {
        if (((((IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckedge) 
               & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_stretch))) 
              & (8U == (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) 
             & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir)))) {
            vlSelf->main__DOT__i2c_valid = 1U;
        } else if (vlSelf->main__DOT__i2c_ready) {
            vlSelf->main__DOT__i2c_valid = 0U;
        }
    } else {
        vlSelf->main__DOT__i2c_valid = 0U;
    }
    if (vlSelf->main__DOT__i2ci__DOT__i2c_ckedge) {
        if ((8U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
            if ((4U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                if ((2U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                    if ((1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy)))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0U;
                    }
                } else if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                    if ((1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy)))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0U;
                    }
                } else if ((1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_stretch)))) {
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                    if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda)) 
                               | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl))))) {
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0xaU;
                    }
                }
            } else if ((2U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                    if ((1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_stretch)))) {
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0xcU;
                        if (((IData)(vlSelf->main__DOT__i2ci__DOT__w_sda) 
                             != (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))) {
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0xaU;
                        }
                    }
                } else {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    if ((((~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy)) 
                          & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl)) 
                         & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0U;
                    }
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl)) 
                           & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))))) {
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 3U;
                }
            } else {
                vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state 
                        = (((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir) 
                            & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda))
                            ? 9U : 2U);
                }
            }
        } else if ((4U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
            if ((2U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda 
                        = (1U & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir) 
                                 | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack))));
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 8U;
                } else {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda 
                        = (1U & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir) 
                                 | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack))));
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                    if ((1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl)))) {
                        if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir) {
                            if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir) {
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 7U;
                            }
                        } else if (((IData)(vlSelf->main__DOT__i2ci__DOT__w_sda) 
                                    != (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack))) {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 7U;
                        }
                    }
                    if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 6U;
                    }
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
                        = ((0xfeU & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg) 
                                     << 1U)) | (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda));
                    if ((0U < (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits 
                            = (7U & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits) 
                                     - (IData)(1U)));
                    }
                    if (((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir) 
                         & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda) 
                            != (1U & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg) 
                                      >> 7U))))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0xaU;
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    } else {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state 
                            = ((0U == (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits))
                                ? 6U : 4U);
                    }
                } else {
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                }
            } else {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda 
                    = (1U & (((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg) 
                              >> 7U) | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir))));
                vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                if (((IData)(vlSelf->main__DOT__i2ci__DOT__w_sda) 
                     == (1U & (((IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg) 
                                >> 7U) | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir)))))) {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 5U;
                }
                if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 4U;
                }
            }
        } else if ((2U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
            if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
                vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                if (vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl) {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0U;
                }
            } else {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 0U;
                vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = 1U;
                vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = 0U;
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
                    = (0xffU & (IData)(vlSelf->main__DOT__i2ci__DOT__insn));
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir = 0U;
                vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                if (((IData)(vlSelf->main__DOT__i2ci__DOT__s_tvalid) 
                     & (IData)(vlSelf->main__DOT__i2ci__DOT__insn_ready))) {
                    if ((0x400U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                        if ((0x200U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                            if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                                vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = 1U;
                                vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = 0U;
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                                vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 4U;
                            } else {
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                                vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = 1U;
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                                vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 4U;
                            }
                        } else if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 4U;
                        } else {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 4U;
                        }
                    } else if ((0x200U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                        if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 4U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
                                = (0xffU & (IData)(vlSelf->main__DOT__i2ci__DOT__insn));
                        } else {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 3U;
                        }
                    } else if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0xbU;
                    }
                }
            }
        } else if ((1U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state 
                = ((4U & (IData)(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits))
                    ? 4U : 2U);
            vlSelf->main__DOT__i2ci__DOT__w_scl = 0U;
        } else {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 0U;
            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = 1U;
            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = 0U;
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
                = (0xffU & (IData)(vlSelf->main__DOT__i2ci__DOT__insn));
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir = 0U;
            if (((IData)(vlSelf->main__DOT__i2ci__DOT__s_tvalid) 
                 & (IData)(vlSelf->main__DOT__i2ci__DOT__insn_ready))) {
                if ((0x400U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                    if ((0x200U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                        if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = 1U;
                            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = 0U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                        } else {
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                            vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                            vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = 1U;
                            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                        }
                    } else if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                        vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = 0U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                    } else {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                    }
                } else if ((0x200U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                    if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir = 1U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = 7U;
                        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
                            = (0xffU & (IData)(vlSelf->main__DOT__i2ci__DOT__insn));
                    }
                } else if ((0x100U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))) {
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 0U;
                    vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
                    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 1U;
                }
            }
        }
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN)))) {
        vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = 1U;
        vlSelf->main__DOT__i2ci__DOT__w_scl = 1U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = 0U;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_OP_PC__DOT__r_op_pc 
            = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch)
                ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc
                : vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc);
    }
    vlSelf->main__DOT__u_fan__DOT__last_tach = vlSelf->main__DOT__u_fan__DOT__ck_tach;
    vlSelf->main__DOT__u_fan__DOT__i2cd_data = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg;
    vlSelf->main__DOT__u_fan__DOT__i2cd_valid = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN) 
                                                 & ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge) 
                                                      & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch))) 
                                                     & (8U 
                                                        == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state))) 
                                                    & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir))));
    vlSelf->main__DOT__u_fan__DOT__i2cd_last = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte;
    vlSelf->o_fan_sda = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda;
    vlSelf->o_fan_scl = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl;
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted));
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual) 
                | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_manual))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid = 0U;
    } else if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid 
            = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle) 
               | ((3U != (0xfU & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                                  >> 4U))) & (0xdU 
                                              != (0xfU 
                                                  & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                                                     >> 4U)))));
    } else if (((((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid)) 
                  | (3U == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn))) 
                 | (0xdU == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn))) 
                & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready))) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid = 0U;
    }
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x80000U ^ (0x3fffffU 
                                           & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x100000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x200000U & (0x200000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 2U));
    vlSelf->main__DOT__swic__DOT__dc_stall = (IData)(
                                                     (((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                                                       >> 2U) 
                                                      | (IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbwide_xbar__DOT__request[0U] 
        = (((IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc) 
            & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_valid))
            ? (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded)
            : 0U);
    if (vlSelf->main__DOT__u_i2cdma__DOT__r_reset) {
        vlSelf->main__DOT__u_i2cdma__DOT__wb_last = 1U;
    } else if (((IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid) 
                & (IData)(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready))) {
        vlSelf->main__DOT__u_i2cdma__DOT__wb_last = 
            (1U & ((IData)(vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data) 
                   >> 8U));
    }
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_data 
        = (((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last) 
            << 4U) | (0xfU & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr)));
    if (vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset) {
        vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    } else if ((((IData)(vlSelf->main__DOT__wb32_wbdown_stb) 
                 & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready)) 
                & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb) 
                   & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = 0U;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Av 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset
        [(0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))];
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Bv 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset
        [(0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))];
    if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_stb)) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_stall))))) {
        vlSelf->main__DOT__swic__DOT__dbg_addr = ((IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb)
                                                   ? (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_addr)
                                                   : (IData)(vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr));
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__wdbus_int) 
         | (IData)(vlSelf->main__DOT__swic__DOT__cpu_err))) {
        vlSelf->main__DOT__swic__DOT__r_wdbus_data 
            = vlSelf->main__DOT__wbwide_zip_addr;
    }
    if (vlSelf->main__DOT__swic__DOT__sys_stb) {
        vlSelf->main__DOT__swic__DOT__ack_idx = vlSelf->main__DOT__swic__DOT__w_ack_idx;
    }
    vlSelf->main__DOT__swic__DOT__pic_data = 0U;
    vlSelf->main__DOT__swic__DOT__pic_data = (((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_mie) 
                                               << 0x1fU) 
                                              | (((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable) 
                                                  << 0x10U) 
                                                 | (((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__w_any) 
                                                     << 0xfU) 
                                                    | (IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state))));
    vlSelf->main__DOT__swic__DOT__ctri_data = 0U;
    vlSelf->main__DOT__swic__DOT__ctri_data = (((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie) 
                                                << 0x1fU) 
                                               | (((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable) 
                                                   << 0x10U) 
                                                  | (((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__w_any) 
                                                      << 0xfU) 
                                                     | (IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state))));
    vlSelf->main__DOT__swic__DOT__dmac_data = 0U;
    if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))) {
        vlSelf->main__DOT__swic__DOT__dmac_data = (
                                                   (0xf0000000U 
                                                    & vlSelf->main__DOT__swic__DOT__dmac_data) 
                                                   | ((1U 
                                                       & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                                       ? 
                                                      ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy)
                                                        ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length
                                                        : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length)
                                                       : 
                                                      ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy)
                                                        ? 
                                                       (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_addr 
                                                        << 6U)
                                                        : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst)));
    } else if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))) {
        vlSelf->main__DOT__swic__DOT__dmac_data = (
                                                   (0xf0000000U 
                                                    & vlSelf->main__DOT__swic__DOT__dmac_data) 
                                                   | ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy)
                                                       ? 
                                                      (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_addr 
                                                       << 6U)
                                                       : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src));
    } else {
        vlSelf->main__DOT__swic__DOT__dmac_data = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg;
    }
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read 
        = ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)) 
           & (IData)(vlSelf->main__DOT__console__DOT__rxf_wb_read));
    vlSelf->main__DOT__console__DOT__rxf_status = (0x6000U 
                                                   | (((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_fill) 
                                                       << 2U) 
                                                      | ((2U 
                                                          & ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill) 
                                                             >> 4U)) 
                                                         | (1U 
                                                            & (~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow))))));
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write 
        = ((IData)(vlSelf->main__DOT__console__DOT__txf_wb_write) 
           & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow)) 
              | (IData)(vlSelf->main__DOT__console__DOT____Vcellinp__txfifo____pinNumber6)));
    vlSelf->__VdfgTmp_ha46ae6a3__0 = ((2U & ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                                             >> 4U)) 
                                      | (1U & (~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow))));
    vlSelf->main__DOT__gpio_int = ((IData)(vlSelf->main__DOT__gpioi__DOT__q_gpio) 
                                   != (IData)(vlSelf->main__DOT__gpioi__DOT__r_gpio));
    vlSelf->main__DOT__gpioi__DOT__r_gpio = vlSelf->main__DOT__gpioi__DOT__q_gpio;
    vlSelf->main__DOT__swic__DOT__cpu_dbg_cc = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err) 
                                                 << 2U) 
                                                | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                                    << 1U) 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep)));
    __Vtableidx2 = (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done) 
                     << 8U) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en) 
                                << 7U) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                           << 6U) | 
                                          (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent) 
                                            << 5U) 
                                           | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
                                               << 4U) 
                                              | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
                                                  << 3U) 
                                                 | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done) 
                                                     << 2U) 
                                                    | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset) 
                                                        << 1U) 
                                                       | (IData)(vlSelf->i_reset)))))))));
    vlSelf->main__DOT__emmc_int = Vmain__ConstPool__TABLE_h40cc9f5d_0
        [__Vtableidx2];
    if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr = 0U;
    } else if ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr 
            = vlSelf->main__DOT__u_emmc__DOT__cfg_ddr;
    }
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
}
