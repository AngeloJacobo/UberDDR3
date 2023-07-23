// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vmain.h for the primary calling header

#include "verilated.h"
#include "verilated_dpi.h"

#include "Vmain__Syms.h"
#include "Vmain___024root.h"

VL_ATTR_COLD void Vmain___024root___stl_sequent__TOP__2(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___stl_sequent__TOP__2\n"); );
    // Init
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0;
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0;
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 = 0;
    CData/*0:0*/ main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0;
    main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0 = 0;
    CData/*0:0*/ main__DOT__swic__DOT____VdfgTmp_hcb574c13__0;
    main__DOT__swic__DOT____VdfgTmp_hcb574c13__0 = 0;
    VlWide<4>/*127:0*/ __Vtemp_hd96f9696__0;
    VlWide<4>/*127:0*/ __Vtemp_h6aa6ab78__0;
    // Body
    if ((0x38U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (0x80U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x39U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (0x40U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x3aU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (0x20U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x3bU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (0x10U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x3cU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (8U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x3dU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (4U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x3eU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (2U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    if ((0x3fU < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes))) {
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U] 
            = (1U | vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel[2U]);
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[0U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[1U] = 0U;
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[2U] 
        = (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_sel);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[3U] 
        = (IData)((vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_sel 
                   >> 0x20U));
    if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_valid) 
         & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_last)))) {
        VL_SHIFTR_WWI(128,128,6, __Vtemp_h6aa6ab78__0, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel, 
                      (0x3fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_addr));
        __Vtemp_hd96f9696__0[1U] = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[1U] 
                                    | __Vtemp_h6aa6ab78__0[1U]);
        __Vtemp_hd96f9696__0[2U] = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[2U] 
                                    | __Vtemp_h6aa6ab78__0[2U]);
        __Vtemp_hd96f9696__0[3U] = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[3U] 
                                    | __Vtemp_h6aa6ab78__0[3U]);
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[0U] 
            = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[0U] 
               | __Vtemp_h6aa6ab78__0[0U]);
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[1U] 
            = __Vtemp_hd96f9696__0[1U];
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[2U] 
            = __Vtemp_hd96f9696__0[2U];
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel[3U] 
            = __Vtemp_hd96f9696__0[3U];
    }
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall) 
           & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__dcd_stb));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x80000U ^ (0x3fffffU 
                                           & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x380000U & (0x100000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0 
        = (0U == (0x200000U & (0x200000U ^ (0x3fffffU 
                                            & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x12U]))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_hc7d9c82c__0) 
              << 2U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xffeU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | (IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 1U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xffdU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 1U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 2U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xffbU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 2U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 3U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xff7U & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 3U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 4U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xfefU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 4U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 5U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xfdfU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 5U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 6U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xfbfU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 6U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 7U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xf7fU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 7U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 8U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xeffU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 8U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 9U));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xdffU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 9U));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 0xaU));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0xbffU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 0xaU));
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest) 
              >> 0xbU));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((0x7ffU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0) 
              << 0xbU));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & (0U == (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS 
        = vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel;
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_rd 
        = ((~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_empty)) 
           & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    vlSelf->main__DOT__wbwide_wbdown_stall = (1U & 
                                              ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first) 
                                               | (((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb) 
                                                   & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
                                                      | (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_full))) 
                                                  | ((~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last)) 
                                                     | ((~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_empty)) 
                                                        & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_null))))));
    vlSelf->main__DOT__swic__DOT__dbg_cpu_read = ((IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h9a48e2a3__0) 
                                                  & ((~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_we)) 
                                                     & (0x20U 
                                                        == 
                                                        (0x60U 
                                                         & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr)))));
    vlSelf->main__DOT__swic__DOT__dbg_cpu_write = ((IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h9a48e2a3__0) 
                                                   & ((IData)(vlSelf->main__DOT__swic__DOT__dbg_we) 
                                                      & (IData)(
                                                                ((0x20U 
                                                                  == 
                                                                  (0x60U 
                                                                   & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))) 
                                                                 & (0xfU 
                                                                    == (IData)(vlSelf->main__DOT__swic__DOT__dbg_sel))))));
    vlSelf->main__DOT__swic__DOT__dmac_stb = ((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
                                              & (IData)(vlSelf->main__DOT__swic__DOT__sel_dmac));
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchdog__i_wb_stb 
        = ((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sel_watchdog));
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__wb_write 
        = (((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
            & (IData)(vlSelf->main__DOT__swic__DOT__sel_apic)) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__wb_write 
        = (((IData)(vlSelf->main__DOT__swic__DOT__sys_cyc) 
            & ((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
               & (IData)(vlSelf->main__DOT__swic__DOT__sel_pic))) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0 = 
        ((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
         & (IData)(vlSelf->main__DOT__swic__DOT__sel_timer));
    vlSelf->main__DOT__swic__DOT__w_ack_idx = 0U;
    if (vlSelf->main__DOT__swic__DOT__sel_watchdog) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = (1U 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__w_ack_idx));
    }
    if (vlSelf->main__DOT__swic__DOT__sel_bus_watchdog) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = (2U 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__w_ack_idx));
    }
    if (vlSelf->main__DOT__swic__DOT__sel_apic) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = (3U 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__w_ack_idx));
    }
    if (vlSelf->main__DOT__swic__DOT__sel_timer) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = (4U 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__w_ack_idx));
    }
    if (vlSelf->main__DOT__swic__DOT__actr_ack) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = (5U 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__w_ack_idx));
    }
    if (vlSelf->main__DOT__swic__DOT__sel_dmac) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = (6U 
                                                   | (IData)(vlSelf->main__DOT__swic__DOT__w_ack_idx));
    }
    if (vlSelf->main__DOT__swic__DOT__sel_pic) {
        vlSelf->main__DOT__swic__DOT__w_ack_idx = 7U;
    }
    main__DOT__swic__DOT____VdfgTmp_hcb574c13__0 = 
        ((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
         & (IData)(vlSelf->main__DOT__swic__DOT__actr_ack));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall)) 
                 & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem)) 
                    & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy)) 
                       & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy)) 
                          | (~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR) 
                                & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                                   == (0xeU | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                               << 4U))))))))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_pipe_stalled 
        = (1U & (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
                  & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_we)) 
                     | ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb)) 
                        | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall)))) 
                 | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending) 
                    | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending) 
                       >> 4U))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
              | (IData)(vlSelf->main__DOT__wbwide_zip_stb)));
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel 
        = (0U != (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [0U] & vlSelf->main__DOT__wbwide_xbar__DOT__grant
                  [0U]));
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__stay_on_channel 
        = (0U != (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [1U] & vlSelf->main__DOT__wbwide_xbar__DOT__grant
                  [1U]));
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__stay_on_channel 
        = (0U != (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [2U] & vlSelf->main__DOT__wbwide_xbar__DOT__grant
                  [2U]));
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__stay_on_channel 
        = (0U != (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [3U] & vlSelf->main__DOT__wbwide_xbar__DOT__grant
                  [3U]));
    vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant 
        = (1U & (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                    >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                    [0U])));
    if ((1U & (((~ vlSelf->main__DOT__wbwide_xbar__DOT__request
                 [vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                 [0U]]) & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                           >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                           [0U])) & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                     >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                     [0U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant 
        = (1U & (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                    >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                    [1U])));
    if ((1U & (((~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                    [vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                    [1U]] >> 1U)) & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                                     >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                     [1U])) & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                               >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                               [1U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                  >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant 
        = (1U & (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                    >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                    [2U])));
    if ((1U & (((~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                    [vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                    [2U]] >> 2U)) & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                                     >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                     [2U])) & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                               >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                               [2U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                  >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 0U;
    }
    if (vlSelf->i_reset) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 1U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[0U] 
        = (6U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
           [0U]);
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
           [0U]);
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[1U] 
        = ((6U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [1U]) | (IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0));
    if ((1U & (vlSelf->main__DOT__wbwide_xbar__DOT__request
               [0U] & (vlSelf->main__DOT__wbwide_xbar__DOT__grant
                       [0U] | ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant)) 
                               | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[1U] 
            = (1U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [1U]);
    }
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
           [1U]);
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[2U] 
        = ((6U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [2U]) | (IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0));
    if ((1U & (vlSelf->main__DOT__wbwide_xbar__DOT__request
               [1U] & (vlSelf->main__DOT__wbwide_xbar__DOT__grant
                       [1U] | ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                   >> 1U)) | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                              >> 1U)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[2U] 
            = (1U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [2U]);
    }
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
           [2U]);
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[3U] 
        = ((6U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [3U]) | (IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0));
    if ((1U & (vlSelf->main__DOT__wbwide_xbar__DOT__request
               [2U] & (vlSelf->main__DOT__wbwide_xbar__DOT__grant
                       [2U] | ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                   >> 2U)) | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                              >> 2U)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[3U] 
            = (1U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [3U]);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[0U] 
        = (5U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
           [0U]);
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                 [0U] >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[1U] 
        = ((5U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [1U]) | ((IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0) 
                     << 1U));
    if ((1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                [0U] >> 1U) & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                [0U] >> 1U) | ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant)) 
                                               | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[1U] 
            = (2U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [1U]);
    }
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                 [1U] >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[2U] 
        = ((5U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [2U]) | ((IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0) 
                     << 1U));
    if ((1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                [1U] >> 1U) & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                [1U] >> 1U) | ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                                   >> 1U)) 
                                               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                                  >> 1U)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[2U] 
            = (2U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [2U]);
    }
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                 [2U] >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[3U] 
        = ((5U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [3U]) | ((IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0) 
                     << 1U));
    if ((1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                [2U] >> 1U) & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                [2U] >> 1U) | ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                                   >> 2U)) 
                                               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                                  >> 2U)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[3U] 
            = (2U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [3U]);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[0U] 
        = (3U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
           [0U]);
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                 [0U] >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[1U] 
        = ((3U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [1U]) | ((IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0) 
                     << 2U));
    if ((1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                [0U] >> 2U) & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                [0U] >> 2U) | ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant)) 
                                               | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[1U] 
            = (4U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [1U]);
    }
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                 [1U] >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[2U] 
        = ((3U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [2U]) | ((IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0) 
                     << 2U));
    if ((1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                [1U] >> 2U) & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                [1U] >> 2U) | ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                                   >> 1U)) 
                                               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                                  >> 1U)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[2U] 
            = (4U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [2U]);
    }
    main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0 
        = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                 [2U] >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__requested[3U] 
        = ((3U & vlSelf->main__DOT__wbwide_xbar__DOT__requested
            [3U]) | ((IData)(main__DOT__wbwide_xbar__DOT____Vlvbound_he62f6d27__0) 
                     << 2U));
    if ((1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                [2U] >> 2U) & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                [2U] >> 2U) | ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                                   >> 2U)) 
                                               | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                                                  >> 2U)))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[3U] 
            = (4U | vlSelf->main__DOT__wbwide_xbar__DOT__requested
               [3U]);
    }
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__last_stb 
        = (2U <= ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight) 
                  + (((IData)(vlSelf->main__DOT__u_fan__DOT__mem_stb)
                       ? 1U : 0U) + ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
                                     & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready))))));
    if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid 
            = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_override) 
               & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_ready));
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_manual) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid = 0U;
        }
    } else {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid 
            = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
               & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready));
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
             & (0x900U == (0xf00U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))))) {
            vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid = 0U;
        }
    }
    if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
        vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid = 0U;
    }
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__last_stb 
        = ((~ (((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                >> 1U) & (IData)(vlSelf->main__DOT__wbwide_i2cm_stb))) 
           & (2U <= ((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight) 
                     + (((IData)(vlSelf->main__DOT__wbwide_i2cm_stb)
                          ? 1U : 0U) + ((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
                                        & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
                                           | (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)))))));
    if (vlSelf->main__DOT__i2ci__DOT__r_halted) {
        vlSelf->main__DOT__i2ci__DOT__next_valid = 
            ((IData)(vlSelf->main__DOT__i2ci__DOT__bus_override) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__ovw_ready));
        if (vlSelf->main__DOT__i2ci__DOT__bus_manual) {
            vlSelf->main__DOT__i2ci__DOT__next_valid = 0U;
        }
    } else {
        vlSelf->main__DOT__i2ci__DOT__next_valid = 
            ((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready));
        if (((IData)(vlSelf->main__DOT__i2ci__DOT__insn_valid) 
             & (0x900U == (0xf00U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))))) {
            vlSelf->main__DOT__i2ci__DOT__next_valid = 0U;
        }
    }
    if (vlSelf->main__DOT__i2ci__DOT__bus_jump) {
        vlSelf->main__DOT__i2ci__DOT__next_valid = 0U;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_cc 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA) 
           == (0xeU | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                       << 4U)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_pc 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA) 
           == (0xfU | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                       << 4U)));
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_empty)) 
           & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__tx_ready));
    vlSelf->main__DOT__wbwide_xbar__DOT__s_stall = 
        (8U | ((0xfffffffcU & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb) 
                               & ((IData)(vlSelf->main__DOT__wbwide_ddr3_controller_stall) 
                                  << 2U))) | ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb) 
                                              & (IData)(vlSelf->main__DOT__wbwide_wbdown_stall))));
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__wb_write 
        = ((IData)(vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchdog__i_wb_stb) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__enable_ints 
        = ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__wb_write) 
           & (vlSelf->main__DOT__swic__DOT__sys_data 
              >> 0xfU));
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__disable_ints 
        = ((~ (vlSelf->main__DOT__swic__DOT__sys_data 
               >> 0xfU)) & (IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__wb_write));
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__enable_ints 
        = ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__wb_write) 
           & (vlSelf->main__DOT__swic__DOT__sys_data 
              >> 0xfU));
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__disable_ints 
        = ((~ (vlSelf->main__DOT__swic__DOT__sys_data 
               >> 0xfU)) & (IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__wb_write));
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_jiffies__i_wb_stb 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0) 
           & (3U == (3U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_a__i_wb_stb 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0) 
           & (0U == (3U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_b__i_wb_stb 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0) 
           & (1U == (3U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_c__i_wb_stb 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb06aa5b__0) 
           & (2U == (3U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mtask_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (0U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mmstall_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (1U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mpstall_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (2U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mins_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (3U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__utask_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (4U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__umstall_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (5U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__upstall_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (6U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__uins_ctr____pinNumber5 
        = ((IData)(main__DOT__swic__DOT____VdfgTmp_hcb574c13__0) 
           & (7U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_div) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_stalled 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem) 
              & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_pipe_stalled) 
                 | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err) 
                    | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_error) 
                       | (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_PIPE__DOT__r_op_pipe)) 
                           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy)) 
                          | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                             & ((0xfU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id))) 
                                | (0xeU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))))))))));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbwide_zip_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available 
        = (0U != (7U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                         [0U] & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) 
                        & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                           [0U]))));
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__request
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available = 1U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__requested_channel_is_available 
        = (0U != (7U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                         [1U] & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) 
                        & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                           [1U]))));
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__request
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__requested_channel_is_available = 1U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__requested_channel_is_available 
        = (0U != (7U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                         [2U] & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) 
                        & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                           [2U]))));
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__request
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__requested_channel_is_available = 1U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__requested_channel_is_available 
        = (0U != (7U & ((vlSelf->main__DOT__wbwide_xbar__DOT__request
                         [3U] & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) 
                        & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                           [3U]))));
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__request
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__requested_channel_is_available = 1U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [0U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [0U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [0U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [0U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [0U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [0U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [0U] >> 3U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [1U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [1U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [1U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [1U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [1U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [1U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [1U] >> 3U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [2U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [2U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [2U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [2U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [2U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [2U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [2U] >> 3U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [3U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [3U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [3U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [3U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [3U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [3U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((8U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [3U] >> 3U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant = 0U;
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [0U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [0U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
               & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [1U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [1U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                >> 1U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                             >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__stay_on_channel = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [2U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [2U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                >> 2U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                             >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__stay_on_channel = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant)) 
                      & (~ vlSelf->main__DOT__wbwide_xbar__DOT__requested
                         [3U])))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ vlSelf->main__DOT__wbwide_xbar__DOT__request
               [3U]))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant = 0U;
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [0U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [0U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
               & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [1U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [1U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                >> 1U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                             >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [2U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [2U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                >> 2U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                             >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((2U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 1U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [3U] >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [3U] >> 1U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant = 0U;
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [0U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [0U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [0U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
               & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [1U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [1U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [1U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                >> 1U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                             >> 1U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [2U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [2U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (4U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [2U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                >> 2U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                             >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((4U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
         [3U])) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    } else if ((1U & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant) 
                          >> 2U)) & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__requested
                                        [3U] >> 2U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (8U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((1U & (~ (vlSelf->main__DOT__wbwide_xbar__DOT__request
                  [3U] >> 2U)))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    if ((IData)((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                  >> 3U) & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mempty) 
                               >> 3U))))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__stay_on_channel = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = 0U;
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__m_stall = 
        ((0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall)) 
         | (1U & ((vlSelf->main__DOT__wbwide_xbar__DOT__grant
                   [0U] >> 3U) | ((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                         & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                            [0U] >> 
                                            vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                            [0U])))
                                   ? ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                      | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall) 
                                         >> vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                         [0U])) : (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb)))));
    if ((1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__m_stall 
            = (0xeU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__m_stall = 
        ((0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall)) 
         | (2U & ((0x3ffffffeU & (vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                  [1U] >> 2U)) | ((
                                                   (1U 
                                                    & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                                        >> 1U) 
                                                       & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                                          [1U] 
                                                          >> 
                                                          vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                                          [1U])))
                                                    ? 
                                                   (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                                     >> 1U) 
                                                    | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall) 
                                                       >> 
                                                       vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                                       [1U]))
                                                    : 
                                                   ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                                                    >> 1U)) 
                                                  << 1U))));
    if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__m_stall 
            = (0xdU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__m_stall = 
        ((0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall)) 
         | (4U & ((0x7ffffffcU & (vlSelf->main__DOT__wbwide_xbar__DOT__grant
                                  [2U] >> 1U)) | ((
                                                   (1U 
                                                    & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                                        >> 2U) 
                                                       & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                                          [2U] 
                                                          >> 
                                                          vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                                          [2U])))
                                                    ? 
                                                   (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                                     >> 2U) 
                                                    | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall) 
                                                       >> 
                                                       vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                                       [2U]))
                                                    : 
                                                   ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                                                    >> 2U)) 
                                                  << 2U))));
    if ((4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__m_stall 
            = (0xbU & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall));
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__m_stall = 
        ((7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall)) 
         | (8U & ((0xfffffff8U & vlSelf->main__DOT__wbwide_xbar__DOT__grant
                   [3U]) | (((IData)((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant) 
                                       >> 3U) & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                                 [3U] 
                                                 >> 
                                                 vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                                 [3U])))
                              ? (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                  >> 3U) | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall) 
                                            >> vlSelf->main__DOT__wbwide_xbar__DOT__mindex
                                            [3U])) : 
                             ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb) 
                              >> 3U)) << 3U))));
    if ((8U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__m_stall 
            = (7U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall));
    }
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__wb_write 
        = ((IData)(vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_a__i_wb_stb) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__wb_write 
        = ((IData)(vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_b__i_wb_stb) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__wb_write 
        = ((IData)(vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_c__i_wb_stb) 
           & (IData)(vlSelf->main__DOT__swic__DOT__sys_we));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__this_is_a_multiply_op 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce) 
           & ((5U == (7U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                            >> 1U))) | (0xcU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem) 
              & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_stalled)) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)))));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((6U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | (IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest) 
              >> 1U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((5U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 1U));
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest) 
              >> 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request 
        = ((3U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request)) 
           | ((IData)(main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0) 
              << 2U));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid) 
           & (0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS 
        = vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel;
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = 0U;
    if ((0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
            = vlSelf->main__DOT__wbwide_xbar__DOT__sindex
            [0U];
    } else {
        if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
                = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex));
        }
        if ((4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
                = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex));
        }
        if ((8U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = 3U;
        }
    }
    if ((0U != (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__iN = 4U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = 0U;
    if ((0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
            = vlSelf->main__DOT__wbwide_xbar__DOT__sindex
            [1U];
    } else {
        if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
                = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex));
        }
        if ((4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
                = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex));
        }
        if ((8U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = 3U;
        }
    }
    if ((0U != (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__iN = 4U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = 0U;
    if ((0U == (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
            = vlSelf->main__DOT__wbwide_xbar__DOT__sindex
            [2U];
    } else {
        if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
                = (1U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex));
        }
        if ((4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex 
                = (2U | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex));
        }
        if ((8U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
            vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = 3U;
        }
    }
    if ((0U != (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant))) {
        vlSelf->main__DOT__wbwide_xbar__DOT__iN = 4U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
           & (IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_stall 
        = (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
            >> 1U) & (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_stall 
        = (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
            >> 2U) & (IData)(vlSelf->main__DOT__wbwide_zip_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_stall 
        = (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall) 
            >> 3U) & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_stall 
        = (((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
                | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce))) 
            & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid)) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid) 
              & ((IData)(vlSelf->main__DOT__swic__DOT__cmd_halt) 
                 | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rA) 
                     & (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0) 
                         & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_he857573c__0) 
                            & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                               >> 6U))) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                                            >> 6U) 
                                           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd)))) 
                    | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB) 
                        & ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0) 
                             | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy)) 
                            & (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_zI)) 
                                & ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                                     == (0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))) 
                                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR)) 
                                   | (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_pipe)) 
                                       & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy)) 
                                      | ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy) 
                                           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy) 
                                              | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy))) 
                                          & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_reg) 
                                             == (0x1fU 
                                                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B)))) 
                                         | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                                            & (0xeU 
                                               == (0xeU 
                                                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))))))) 
                               | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_he857573c__0) 
                                  & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                                     >> 6U)))) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                                                   >> 6U) 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd)))) 
                       | (((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_F) 
                               >> 3U)) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rA) 
                                           & (IData)(
                                                     ((0xeU 
                                                       == 
                                                       (0xeU 
                                                        & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))) 
                                                      & ((0x1fU 
                                                          & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A)) 
                                                         != 
                                                         (0xfU 
                                                          | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                                             << 4U)))))) 
                                          | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB) 
                                             & (IData)(
                                                       ((0xeU 
                                                         == 
                                                         (0xeU 
                                                          & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))) 
                                                        & ((0x1fU 
                                                            & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B)) 
                                                           != 
                                                           (0xfU 
                                                            | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                                               << 4U)))))))) 
                          & (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid) 
                              & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR) 
                                 & (IData)(((0xeU == 
                                             (0xeU 
                                              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R))) 
                                            & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                                               != (0xfU 
                                                   | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                                      << 4U))))))) 
                             | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_pending_sreg_write))))))));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_valid));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stall 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_stall) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_valid));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stall 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_stall) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_valid));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stall 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_stall) 
           & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_valid));
    vlSelf->main__DOT__swic__DOT__cpu_op_stall = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce) 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_stall));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_stall)) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid) 
              | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal) 
                 | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_stalled 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_stall));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__avsrc = 0U;
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__avsrc 
            = ((0x20U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))
                ? 5U : ((0x40U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))
                         ? 6U : 7U));
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) {
        if (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce)) 
             & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h740acd49__0) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rA)))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__avsrc = 4U;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) 
                    & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id) 
                       == (0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))))) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__avsrc = 4U;
        }
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bvsrc = 0U;
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bvsrc 
            = ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                 >> 5U) & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB))
                ? 4U : 5U);
    } else if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rB) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce)) 
                & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Bid) 
                   == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bvsrc = 6U;
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid)) 
                 | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_stalled))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ready 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_stalled)) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_advance 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_new_pc) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ready)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 0U;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 0U;
    if (vlSelf->main__DOT__swic__DOT__cmd_reset) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 0U;
    } else if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce)) 
                & (((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id) 
                           >> 4U)) == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)) 
                   & (0xfU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 1U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_switch_to_interrupt) 
                | ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)) 
                   & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache) 
                      | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe))))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 2U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_release_from_interrupt) 
                | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                   & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache) 
                      | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe))))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 3U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                & (((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id) 
                           >> 4U)) == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)) 
                   & (0xfU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 1U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch_stb) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 4U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc) 
                | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ready) 
                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_valid)))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = 1U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = 5U;
    }
}

VL_ATTR_COLD void Vmain___024root___stl_sequent__TOP__0(Vmain___024root* vlSelf);
VL_ATTR_COLD void Vmain___024root___stl_sequent__TOP__1(Vmain___024root* vlSelf);

VL_ATTR_COLD void Vmain___024root___eval_stl(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        Vmain___024root___stl_sequent__TOP__0(vlSelf);
        vlSelf->__Vm_traceActivity[6U] = 1U;
        vlSelf->__Vm_traceActivity[5U] = 1U;
        vlSelf->__Vm_traceActivity[4U] = 1U;
        vlSelf->__Vm_traceActivity[3U] = 1U;
        vlSelf->__Vm_traceActivity[2U] = 1U;
        vlSelf->__Vm_traceActivity[1U] = 1U;
        vlSelf->__Vm_traceActivity[0U] = 1U;
        Vmain___024root___stl_sequent__TOP__1(vlSelf);
        Vmain___024root___stl_sequent__TOP__2(vlSelf);
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vmain___024root___dump_triggers__ico(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___dump_triggers__ico\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VicoTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VicoTriggered.word(0U))) {
        VL_DBG_MSGF("         'ico' region trigger index 0 is active: Internal 'ico' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void Vmain___024root___dump_triggers__act(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VactTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 0 is active: @(posedge i_clk)\n");
    }
    if ((2ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 1 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[0].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((4ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 2 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[1].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((8ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 3 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[2].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x10ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 4 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[3].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x20ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 5 is active: @([changed] main.wb32_xbar.ARBITRATE_REQUESTS[0].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x40ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 6 is active: @([changed] main.wbu_xbar.ARBITRATE_REQUESTS[0].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x80ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 7 is active: @(posedge i_clk or negedge main.__Vcellinp__ddr3_controller_inst__i_rst_n)\n");
    }
    if ((0x100ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 8 is active: @(negedge i_clk)\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void Vmain___024root___dump_triggers__nba(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge i_clk)\n");
    }
    if ((2ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 1 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[0].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((4ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 2 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[1].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((8ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 3 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[2].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x10ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 4 is active: @([changed] main.wbwide_xbar.ARBITRATE_REQUESTS[3].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x20ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 5 is active: @([changed] main.wb32_xbar.ARBITRATE_REQUESTS[0].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x40ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 6 is active: @([changed] main.wbu_xbar.ARBITRATE_REQUESTS[0].MINDEX_MULTIPLE_SLAVES.r_regrant)\n");
    }
    if ((0x80ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 7 is active: @(posedge i_clk or negedge main.__Vcellinp__ddr3_controller_inst__i_rst_n)\n");
    }
    if ((0x100ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 8 is active: @(negedge i_clk)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void Vmain___024root___ctor_var_reset(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->i_clk = VL_RAND_RESET_I(1);
    vlSelf->i_reset = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->i_ddr3_controller_iserdes_data);
    vlSelf->i_ddr3_controller_iserdes_dqs = VL_RAND_RESET_Q(64);
    vlSelf->i_ddr3_controller_iserdes_bitslip_reference = VL_RAND_RESET_Q(64);
    vlSelf->i_ddr3_controller_idelayctrl_rdy = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(96, vlSelf->o_ddr3_controller_cmd);
    vlSelf->o_ddr3_controller_dqs_tri_control = VL_RAND_RESET_I(1);
    vlSelf->o_ddr3_controller_dq_tri_control = VL_RAND_RESET_I(1);
    vlSelf->o_ddr3_controller_toggle_dqs = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->o_ddr3_controller_data);
    vlSelf->o_ddr3_controller_dm = VL_RAND_RESET_Q(64);
    vlSelf->o_ddr3_controller_odelay_data_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->o_ddr3_controller_odelay_dqs_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->o_ddr3_controller_idelay_data_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->o_ddr3_controller_idelay_dqs_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->o_ddr3_controller_odelay_data_ld = VL_RAND_RESET_I(8);
    vlSelf->o_ddr3_controller_odelay_dqs_ld = VL_RAND_RESET_I(8);
    vlSelf->o_ddr3_controller_idelay_data_ld = VL_RAND_RESET_I(8);
    vlSelf->o_ddr3_controller_idelay_dqs_ld = VL_RAND_RESET_I(8);
    vlSelf->o_ddr3_controller_bitslip = VL_RAND_RESET_I(8);
    vlSelf->o_sirefclk_word = VL_RAND_RESET_I(8);
    vlSelf->o_sirefclk_ce = VL_RAND_RESET_I(1);
    vlSelf->i_fan_sda = VL_RAND_RESET_I(1);
    vlSelf->i_fan_scl = VL_RAND_RESET_I(1);
    vlSelf->o_fan_sda = VL_RAND_RESET_I(1);
    vlSelf->o_fan_scl = VL_RAND_RESET_I(1);
    vlSelf->o_fpga_pwm = VL_RAND_RESET_I(1);
    vlSelf->o_sys_pwm = VL_RAND_RESET_I(1);
    vlSelf->i_fan_tach = VL_RAND_RESET_I(1);
    vlSelf->o_emmc_clk = VL_RAND_RESET_I(1);
    vlSelf->i_emmc_ds = VL_RAND_RESET_I(1);
    vlSelf->io_emmc_cmd_tristate = VL_RAND_RESET_I(1);
    vlSelf->o_emmc_cmd = VL_RAND_RESET_I(1);
    vlSelf->i_emmc_cmd = VL_RAND_RESET_I(1);
    vlSelf->io_emmc_dat_tristate = VL_RAND_RESET_I(8);
    vlSelf->o_emmc_dat = VL_RAND_RESET_I(8);
    vlSelf->i_emmc_dat = VL_RAND_RESET_I(8);
    vlSelf->i_emmc_detect = VL_RAND_RESET_I(1);
    vlSelf->i_i2c_sda = VL_RAND_RESET_I(1);
    vlSelf->i_i2c_scl = VL_RAND_RESET_I(1);
    vlSelf->o_i2c_sda = VL_RAND_RESET_I(1);
    vlSelf->o_i2c_scl = VL_RAND_RESET_I(1);
    vlSelf->o_sdcard_clk = VL_RAND_RESET_I(1);
    vlSelf->i_sdcard_ds = VL_RAND_RESET_I(1);
    vlSelf->io_sdcard_cmd_tristate = VL_RAND_RESET_I(1);
    vlSelf->o_sdcard_cmd = VL_RAND_RESET_I(1);
    vlSelf->i_sdcard_cmd = VL_RAND_RESET_I(1);
    vlSelf->io_sdcard_dat_tristate = VL_RAND_RESET_I(4);
    vlSelf->o_sdcard_dat = VL_RAND_RESET_I(4);
    vlSelf->i_sdcard_dat = VL_RAND_RESET_I(4);
    vlSelf->i_sdcard_detect = VL_RAND_RESET_I(1);
    vlSelf->cpu_sim_cyc = VL_RAND_RESET_I(1);
    vlSelf->cpu_sim_stb = VL_RAND_RESET_I(1);
    vlSelf->cpu_sim_we = VL_RAND_RESET_I(1);
    vlSelf->cpu_sim_addr = VL_RAND_RESET_I(7);
    vlSelf->cpu_sim_data = VL_RAND_RESET_I(32);
    vlSelf->cpu_sim_stall = VL_RAND_RESET_I(1);
    vlSelf->cpu_sim_ack = VL_RAND_RESET_I(1);
    vlSelf->cpu_sim_idata = VL_RAND_RESET_I(32);
    vlSelf->cpu_prof_stb = VL_RAND_RESET_I(1);
    vlSelf->cpu_prof_addr = VL_RAND_RESET_I(28);
    vlSelf->cpu_prof_ticks = VL_RAND_RESET_I(32);
    vlSelf->i_cpu_reset = VL_RAND_RESET_I(1);
    vlSelf->i_clk200 = VL_RAND_RESET_I(1);
    vlSelf->i_wbu_uart_rx = VL_RAND_RESET_I(1);
    vlSelf->o_wbu_uart_tx = VL_RAND_RESET_I(1);
    vlSelf->o_wbu_uart_cts_n = VL_RAND_RESET_I(1);
    vlSelf->i_gpio = VL_RAND_RESET_I(16);
    vlSelf->o_gpio = VL_RAND_RESET_I(8);
    vlSelf->i_sw = VL_RAND_RESET_I(8);
    vlSelf->i_btn = VL_RAND_RESET_I(5);
    vlSelf->o_led = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__emmcscope_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscope_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdcard_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscope_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__gpio_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spio_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__r_sirefclk_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__r_sirefclk_data = VL_RAND_RESET_I(30);
    vlSelf->main__DOT__w_sirefclk_unused_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__r_sirefclk_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cdma_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2c_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2c_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2c_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2c_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__w_console_rx_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__w_console_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__w_console_rx_data = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__w_console_tx_data = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__uart_debug = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__raw_cpu_dbg_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__raw_cpu_dbg_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__zip_cpu_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_rx_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wbu_rx_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__w_led = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wbwide_i2cdma_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_i2cdma_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_i2cdma_addr = VL_RAND_RESET_I(22);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__wbwide_i2cdma_data);
    vlSelf->main__DOT__wbwide_i2cdma_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__wbwide_i2cm_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_i2cm_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_i2cm_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__wbwide_zip_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_zip_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_zip_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__wbwide_wbu_arbiter_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_wbu_arbiter_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_wbdown_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_bkram_ack = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__wbwide_bkram_idata);
    vlSelf->main__DOT__wbwide_ddr3_controller_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_wbdown_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_wbdown_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_wbdown_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_wbdown_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_buildtime_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wb32_buildtime_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_gpio_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wb32_gpio_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_sirefclk_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_sirefclk_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wb32_sirefclk_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_spio_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_spio_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wb32_spio_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_spio_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_version_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wb32_version_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_i2cs_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_i2cdma_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_i2cdma_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_uart_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_uart_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_emmc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_emmc_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_fan_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_fan_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_sdcard_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_sdcard_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_ddr3_phy_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_ddr3_phy_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_ddr3_phy_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbu_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbu_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbu_wbu_arbiter_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_zip_idata = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(192, vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel);
    VL_RAND_RESET_W(1536, vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata);
    VL_RAND_RESET_W(66, vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr);
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_swe = VL_RAND_RESET_I(3);
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb = VL_RAND_RESET_I(3);
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc = VL_RAND_RESET_I(3);
    vlSelf->main__DOT____Vcellout__wbwide_xbar__o_merr = VL_RAND_RESET_I(4);
    VL_RAND_RESET_W(2048, vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata);
    vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__r_wb32_sio_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__r_wb32_sio_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel = VL_RAND_RESET_Q(48);
    VL_RAND_RESET_W(384, vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata);
    VL_RAND_RESET_W(96, vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr);
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe = VL_RAND_RESET_I(12);
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb = VL_RAND_RESET_I(12);
    vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc = VL_RAND_RESET_I(12);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_ssel = VL_RAND_RESET_I(8);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_sdata = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr = VL_RAND_RESET_Q(54);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_swe = VL_RAND_RESET_I(2);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb = VL_RAND_RESET_I(2);
    vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc = VL_RAND_RESET_I(2);
    vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber4 = VL_RAND_RESET_I(31);
    vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber3 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber4 = VL_RAND_RESET_I(31);
    vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber3 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__u_i2cdma__S_VALID = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr = VL_RAND_RESET_I(7);
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__swic__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT____Vcellinp__i2cscopei____pinNumber4 = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__r_cfg_ack = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__request[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__requested[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__grant[__Vi0] = VL_RAND_RESET_I(4);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__mgrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__sgrant = VL_RAND_RESET_I(3);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__mfull = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__mempty = VL_RAND_RESET_I(4);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__mindex[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__sindex[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__m_stb = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__m_we = VL_RAND_RESET_I(4);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[__Vi0] = VL_RAND_RESET_I(22);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__wbwide_xbar__DOT__m_data[__Vi0]);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[__Vi0] = VL_RAND_RESET_Q(64);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__m_stall = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__s_stall = VL_RAND_RESET_I(4);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__wbwide_xbar__DOT__s_data[__Vi0]);
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__s_ack = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__s_err = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__iN = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbwide_xbar__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(577, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__decoded = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskd_ready = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__iskid__i_reset = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(577, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__decoded = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskd_ready = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_reset = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(577, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__decoded = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskd_ready = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_reset = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(577, vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__stay_on_channel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__requested_channel_is_available = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__stay_on_channel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__requested_channel_is_available = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__stay_on_channel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__requested_channel_is_available = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__r_sindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__r_sindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__r_sindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(599, vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__request[__Vi0] = VL_RAND_RESET_I(13);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__requested[__Vi0] = VL_RAND_RESET_I(12);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__grant[__Vi0] = VL_RAND_RESET_I(13);
    }
    vlSelf->main__DOT__wb32_xbar__DOT__mgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__sgrant = VL_RAND_RESET_I(12);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__w_mpending[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->main__DOT__wb32_xbar__DOT__mfull = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__mnearfull = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__mempty = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__mindex[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 16; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__sindex[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->main__DOT__wb32_xbar__DOT__m_stb = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__m_addr[__Vi0] = VL_RAND_RESET_I(8);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__m_data[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__m_sel[__Vi0] = VL_RAND_RESET_I(4);
    }
    vlSelf->main__DOT__wb32_xbar__DOT__m_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__s_stall = VL_RAND_RESET_I(16);
    for (int __Vi0 = 0; __Vi0 < 16; ++__Vi0) {
        vlSelf->main__DOT__wb32_xbar__DOT__s_data[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__wb32_xbar__DOT__dcd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__iN = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_xbar__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded = VL_RAND_RESET_I(13);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data = VL_RAND_RESET_Q(45);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data = VL_RAND_RESET_Q(45);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data = VL_RAND_RESET_Q(37);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__3__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__4__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__5__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__6__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__7__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__8__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__9__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__10__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__11__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = VL_RAND_RESET_I(13);
    vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data = VL_RAND_RESET_Q(45);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__request[__Vi0] = VL_RAND_RESET_I(3);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__requested[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__grant[__Vi0] = VL_RAND_RESET_I(3);
    }
    vlSelf->main__DOT__wbu_xbar__DOT__mgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__sgrant = VL_RAND_RESET_I(2);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__w_mpending[__Vi0] = VL_RAND_RESET_I(6);
    }
    vlSelf->main__DOT__wbu_xbar__DOT__mfull = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__mnearfull = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__mempty = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__mindex[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__sindex[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->main__DOT__wbu_xbar__DOT__m_stb = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__m_addr[__Vi0] = VL_RAND_RESET_I(27);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__m_data[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__m_sel[__Vi0] = VL_RAND_RESET_I(4);
    }
    vlSelf->main__DOT__wbu_xbar__DOT__m_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__s_stall = VL_RAND_RESET_I(4);
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__wbu_xbar__DOT__s_data[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__wbu_xbar__DOT__s_err = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__iN = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbu_xbar__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskd_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data = VL_RAND_RESET_Q(37);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr = VL_RAND_RESET_I(27);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__read_from_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__write_to_control = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__o_bus_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__emmcscopei__DOT__read_address = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__raddr = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__emmcscopei__DOT__waddr = VL_RAND_RESET_I(12);
    for (int __Vi0 = 0; __Vi0 < 4096; ++__Vi0) {
        vlSelf->main__DOT__emmcscopei__DOT__mem[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__emmcscopei__DOT__bw_reset_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__br_config = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__emmcscopei__DOT__br_holdoff = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__emmcscopei__DOT__holdoff_counter = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__emmcscopei__DOT__dr_triggered = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__dr_primed = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__dw_trigger = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__dr_stopped = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__emmcscopei__DOT__ck_addr = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__emmcscopei__DOT__qd_data = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__emmcscopei__DOT__dr_force_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__dr_run_timeout = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__new_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__dr_force_inhibit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__imm_adr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__lst_adr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__lst_val = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__emmcscopei__DOT__imm_val = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__emmcscopei__DOT__record_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__r_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__br_pre_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__emmcscopei__DOT__this_addr = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__emmcscopei__DOT__nxt_mem = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__emmcscopei__DOT__br_level_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__read_from_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__write_to_control = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__o_bus_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__sdioscopei__DOT__read_address = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__raddr = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__sdioscopei__DOT__waddr = VL_RAND_RESET_I(12);
    for (int __Vi0 = 0; __Vi0 < 4096; ++__Vi0) {
        vlSelf->main__DOT__sdioscopei__DOT__mem[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__sdioscopei__DOT__bw_reset_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__br_config = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__sdioscopei__DOT__br_holdoff = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__sdioscopei__DOT__holdoff_counter = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__sdioscopei__DOT__dr_triggered = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__dr_primed = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__dw_trigger = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__dr_stopped = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__sdioscopei__DOT__ck_addr = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__sdioscopei__DOT__qd_data = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__sdioscopei__DOT__dr_force_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__dr_run_timeout = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__new_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__dr_force_inhibit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__imm_adr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__lst_adr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__lst_val = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__sdioscopei__DOT__imm_val = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__sdioscopei__DOT__record_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__r_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__sdioscopei__DOT__br_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__br_pre_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__sdioscopei__DOT__this_addr = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__sdioscopei__DOT__nxt_mem = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__sdioscopei__DOT__br_level_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__index = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__instruction_address = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__instruction = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_counter = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_counter_is_zero = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__reset_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__pause_counter = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d = VL_RAND_RESET_I(8);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[__Vi0] = VL_RAND_RESET_I(14);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[__Vi0] = VL_RAND_RESET_I(14);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_pending = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_aux = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_we = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_dm = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_col = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_bank = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_row = VL_RAND_RESET_I(14);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_next_bank = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_next_row = VL_RAND_RESET_I(14);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_pending = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_aux = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm_unaligned = VL_RAND_RESET_Q(64);
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm[__Vi0] = VL_RAND_RESET_Q(64);
    }
    VL_RAND_RESET_W(512, vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned);
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[__Vi0]);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[__Vi0] = VL_RAND_RESET_Q(64);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[__Vi0] = VL_RAND_RESET_I(8);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_col = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_row = VL_RAND_RESET_I(14);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 4; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[__Vi0] = VL_RAND_RESET_I(24);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_odt_q = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_odt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_ck_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_reset_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_stall_q = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_stall_d = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__precharge_slot_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__activate_slot_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_q = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_d = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_val = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq_q = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq_d = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__aligned_cmd = VL_RAND_RESET_I(24);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__serial_index = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__serial_index_q = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__test_OFB = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__state_calibrate = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_store = VL_RAND_RESET_Q(40);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_count_repeat = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_stored = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index_orig = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dq_target_index = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index_value = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_repeat = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__train_delay = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_data = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_level_feedback = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__initial_dqs = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__lane = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__lane_times_8 = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_bitslip_arrangement = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe_max = VL_RAND_RESET_I(4);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[__Vi0] = VL_RAND_RESET_I(4);
    }
    for (int __Vi0 = 0; __Vi0 < 5; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0 = 0; __Vi0 < 5; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__index_read_pipe = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_read_pipe[__Vi0] = VL_RAND_RESET_I(16);
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q[__Vi0]);
    }
    for (int __Vi0 = 0; __Vi0 < 16; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_aux = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_col = VL_RAND_RESET_I(10);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_odt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dqs = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dq = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__prev_write_level_feedback = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__ddr3_controller_inst__DOT__write_pattern);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[__Vi0] = VL_RAND_RESET_I(7);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[__Vi0] = VL_RAND_RESET_I(5);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[__Vi0] = VL_RAND_RESET_I(5);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein_prev = VL_RAND_RESET_I(5);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_update = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_addr = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_sel = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_read_lane = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_data_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_dqs_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_data_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_dqs_cntvaluein = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_data_ld = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_dqs_ld = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_data_ld = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_dqs_ld = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_write_lane = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__ns_to_cycles__Vstatic__result = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__nCK_to_cycles__Vstatic__result = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__delay = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__slot_number = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__read_slot = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__write_slot = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__anticipate_activate_slot = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__anticipate_precharge_slot = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__ddr3_controller_inst__DOT__find_delay__Vstatic__k = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__ddr3_controller_inst__DOT____Vlvbound_h133f9401__0 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT____Vlvbound_hddcbe2f8__0 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__ddr3_controller_inst__DOT____Vlvbound_ha8bc7f27__1 = VL_RAND_RESET_I(2);
    for (int __Vi0 = 0; __Vi0 < 16384; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__bkrami__DOT__mem[__Vi0]);
    }
    vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_wstb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr = VL_RAND_RESET_I(14);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data);
    vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__bkrami__DOT__WRITE_TO_MEMORY__DOT__ik = VL_RAND_RESET_I(32);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__clock_generator__DOT__counter[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__clock_generator__DOT__r_delay = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__clock_generator__DOT__times_three = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__clock_generator__DOT__times_five = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__clock_generator__DOT__times_seven = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__u_i2cdma__DOT__r_memlen = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__u_i2cdma__DOT__subaddr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_i2cdma__DOT__current_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_i2cdma__DOT__next_memlen = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_i2cdma__DOT__wb_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT__bus_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT__r_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT__r_overflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT__skd_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT__skd_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data = VL_RAND_RESET_I(9);
    vlSelf->main__DOT__u_i2cdma__DOT____Vcellinp__sskd__i_data = VL_RAND_RESET_I(9);
    vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_data = VL_RAND_RESET_I(9);
    vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__pwm_counter = VL_RAND_RESET_I(13);
    vlSelf->main__DOT__u_fan__DOT__ctl_fpga = VL_RAND_RESET_I(13);
    vlSelf->main__DOT__u_fan__DOT__ctl_sys = VL_RAND_RESET_I(13);
    vlSelf->main__DOT__u_fan__DOT__ck_tach = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__last_tach = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__pipe_tach = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_fan__DOT__tach_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__tach_count = VL_RAND_RESET_I(27);
    vlSelf->main__DOT__u_fan__DOT__tach_counter = VL_RAND_RESET_I(27);
    vlSelf->main__DOT__u_fan__DOT__tach_timer = VL_RAND_RESET_I(27);
    vlSelf->main__DOT__u_fan__DOT__i2c_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__mem_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__mem_addr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_fan__DOT__mem_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_fan__DOT__mem_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__i2cd_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__i2cd_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__i2cd_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_fan__DOT__pp_ms = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__trigger_counter = VL_RAND_RESET_I(17);
    vlSelf->main__DOT__u_fan__DOT__temp_tmp = VL_RAND_RESET_I(24);
    vlSelf->main__DOT__u_fan__DOT__temp_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_fan__DOT__pre_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__pre_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_fan__DOT____Vcellinp__u_i2ccpu__i_wb_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ckcount = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__abort_address = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__jump_target = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_override = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_manual = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_read_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__s_tvalid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__last_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__invalid_bus_cycle = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_word = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__q_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__q_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__lst_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__lst_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__stop_bit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__channel_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__cfg_ddr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__cfg_sample_shift = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_emmc__DOT__sdclk = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__pp_cmd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__pp_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__rx_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_half = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__w_sdclk = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_ckspd = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_id = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_arg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_cfg_dbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__ika = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__ikb = VL_RAND_RESET_I(32);
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_sel = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_a = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_b = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_a = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_b = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_a = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_b = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_tx_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__counter = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__clk90 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__ckspd = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT____Vconcswap_1_h50d55398__0 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT____Vconcswap_1_h561f6367__0 = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg = VL_RAND_RESET_Q(48);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_ds = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg = VL_RAND_RESET_Q(40);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = VL_RAND_RESET_I(26);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__start_packet = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_stop_bit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__pending_crc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__dat0_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__wait_for_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_pedge = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_dedge = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__resp_started = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__io_started = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__last_ck = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__ck_sreg = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__pck_sreg = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__sample_ck = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__cmd_sample_ck = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT____VdfgTmp_h87c0e738__0 = 0;
    vlSelf->main__DOT__i2ci__DOT__cpu_new_pc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__pf_jump_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__i2ci__DOT__pf_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__pf_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__pf_insn = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__i2ci__DOT__pf_insn_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__i2ci__DOT__pf_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__half_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__imm_cycle = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__next_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__next_insn = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__i2ci__DOT__insn_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__half_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__i2c_abort = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__insn_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__insn = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__i2ci__DOT__half_insn = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__i2ci__DOT__i2c_ckedge = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__i2c_stretch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__i2c_ckcount = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__i2ci__DOT__ckcount = VL_RAND_RESET_I(12);
    vlSelf->main__DOT__i2ci__DOT__abort_address = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__i2ci__DOT__jump_target = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__i2ci__DOT__r_wait = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__soft_halt_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__r_halted = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__r_aborted = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__w_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__w_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__bus_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__bus_override = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__bus_manual = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__ovw_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__bus_jump = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__bus_read_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__i2ci__DOT__s_tvalid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__ovw_data = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__mid_axis_pkt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__r_channel = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__i2ci__DOT____VdfgTmp_h373818eb__0 = 0;
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__last_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__invalid_bus_cycle = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__r_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_shift = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__q_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__q_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__lst_scl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__lst_sda = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__stop_bit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_null = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__i_subaddr = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_empty = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_data = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_wr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_empty = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 32; ++__Vi0) {
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[__Vi0] = VL_RAND_RESET_I(5);
    }
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_wr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_rd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__cfg_sample_shift = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_sdcard__DOT__sdclk = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__pp_cmd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__pp_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__rx_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_half = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__w_sdclk = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_ckspd = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_id = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_arg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_cfg_dbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__ika = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__ikb = VL_RAND_RESET_I(32);
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_sel = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_a = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_b = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_a = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_b = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_a = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_b = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_tx_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_removed = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_present = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__counter = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__clk90 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__ckspd = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT____Vconcswap_1_h50d55398__0 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT____Vconcswap_1_h561f6367__0 = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg = VL_RAND_RESET_Q(48);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_ds = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg = VL_RAND_RESET_Q(40);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = VL_RAND_RESET_I(26);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__start_packet = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d);
    VL_RAND_RESET_W(256, vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_stop_bit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__pending_crc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__dat0_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__wait_for_busy = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 16; ++__Vi0) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[__Vi0] = VL_RAND_RESET_I(1);
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__w_dat = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_pedge = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_dedge = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__ck_sreg = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pck_sreg = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__sample_ck = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__cmd_sample_ck = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__resp_started = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__io_started = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__last_ck = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__o_pin = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__o_pin = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__o_pin = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__o_pin = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__w_out = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__high_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__r_out = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__w_in = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__high_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__r_out = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__w_in = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__high_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__r_out = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__w_in = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__high_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__r_out = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__w_in = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__high_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__r_out = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__w_in = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__high_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__r_out = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__console__DOT__rx_uart_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__rxf_wb_data = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__console__DOT__rxf_status = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__console__DOT__rxf_wb_read = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txf_status = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__console__DOT__txf_wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__tx_uart_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txf_wb_data = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__console__DOT__r_wb_addr = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__console__DOT__r_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT____Vcellinp__txfifo____pinNumber6 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT____VdfgTmp_h60af6732__0 = 0;
    for (int __Vi0 = 0; __Vi0 < 64; ++__Vi0) {
        vlSelf->main__DOT__console__DOT__rxfifo__DOT__fifo[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_data = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__last_write = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_next = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__osrc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_waddr_plus_one = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_fill = VL_RAND_RESET_I(10);
    for (int __Vi0 = 0; __Vi0 < 64; ++__Vi0) {
        vlSelf->main__DOT__console__DOT__txfifo__DOT__fifo[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->main__DOT__console__DOT__txfifo__DOT__r_data = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__last_write = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__r_next = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__osrc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_waddr_plus_one = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_read = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__console__DOT__txfifo__DOT__w_fill = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__swic__DOT__main_int_vector = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__alt_int_vector = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__ctri_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__tma_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__tmb_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__tmc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__jif_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dmac_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__mtc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__moc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__mpc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__mic_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__utc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__uoc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__upc_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__uic_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__actr_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sys_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sys_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sys_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sys_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__sys_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__cpu_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__swic__DOT__sys_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__sys_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sel_timer = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sel_pic = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sel_apic = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sel_watchdog = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sel_bus_watchdog = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__sel_dmac = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_addr = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__dbg_idata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__dbg_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_odata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__dbg_sel = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__no_dbg_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_break = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_cmd_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_cpu_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_cpu_read = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__reset_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__halt_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__step_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__clear_cache_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_halt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_step = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_clear_cache = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_read = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_waddr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__cmd_wdata = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__cpu_dbg_cc = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__wdt_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__wdt_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__wdbus_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__r_wdbus_data = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__swic__DOT__pic_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__wdbus_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_op_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_pf_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_i_count = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dmac_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dc_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dmac_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__dmac_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dc_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dc_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dc_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_gbl_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ctri_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__tma_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__tmb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__tmc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__jif_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_lcl_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_we = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__cpu_idata);
    vlSelf->main__DOT__swic__DOT__cpu_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__pic_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cpu_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ext_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__w_ack_idx = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__ack_idx = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__last_sys_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__cmd_read_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchdog__i_wb_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchbus____pinNumber2 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_a__i_wb_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_b__i_wb_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_c__i_wb_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__u_jiffies__i_wb_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__r_mmus_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_pre_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dbg_pre_addr = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__dbg_cpu_status = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__r_reset_hold = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__GEN_DBG_CATCH__DOT__r_dbg_catch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mtask_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mmstall_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mpstall_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mins_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__utask_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__umstall_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__upstall_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__uins_ctr____pinNumber5 = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0 = 0;
    vlSelf->main__DOT__swic__DOT____VdfgTmp_h9a48e2a3__0 = 0;
    vlSelf->main__DOT__swic__DOT____VdfgTmp_h145b7951__0 = 0;
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_running = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_watchbus__DOT__r_value = VL_RAND_RESET_I(14);
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_running = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_interval_count = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_running = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_interval_count = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_running = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_interval_count = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_now = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_when = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_when = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_wb = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_when = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_new_pc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_pipe_stalled = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wreg = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_result = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_lcl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_gbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 32; ++__Vi0) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__flags = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__iflags = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_uflags = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_iflags = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__break_en = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__user_step = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ubreak = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pending_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__step = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_u = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ubus_err_flag = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pf_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_stalled = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_opn = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preB = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_F = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wR = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rA = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ALU = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_M = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_DIV = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_FP = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wF = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_break = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_lock = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_I = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_zI = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_div = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_fpu = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_Rcc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_Av = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_Bv = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Av = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Bv = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcB_v = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcA_v = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_wF = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_F = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_break = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim_immv = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim_immv = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_reg = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_alu_pc_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_pc_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_pc_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_wR = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_wF = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_stalled = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_error = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_val = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_dbg_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_flags_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_flags = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_index = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_gpreg_vl = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_switch_to_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_release_from_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ipc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__last_write_to_cc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__instruction_decoder__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__avsrc = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bvsrc = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bisrc = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_pending_sreg_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_PIPE__DOT__r_op_pipe = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Aid = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Bid = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rA = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rB = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OPLOCK__DOT__r_op_lock = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim_immv = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_OP_PC__DOT__r_op_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OPT_CIS_OP_PHASE__DOT__r_op_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PC__DOT__r_alu_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_ALU_ILLEGAL__DOT__r_alu_illegal = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_prelock_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_lock_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim_immv = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__regid = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_pending_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_user_stepped = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_ubreak = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_ILLEGAL_INSN__DOT__r_ill_err_u = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_BUSERR__DOT__r_ubus_err_flag = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_IHALT_PHASE__DOT__r_ihalt_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__CLEAR_DCACHE__DOT__r_clear_dcache = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_haf314c36__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h740acd49__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_ha62fb8d9__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_he857573c__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_hefd95ffe__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_hb0e009d2__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim_immv = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_ALU = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_noop = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_lock = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_pc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_cc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_mem = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_sto = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_div = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_fpu = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_ljmp = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__pf_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_nxt_half = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_I = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_I = VL_RAND_RESET_I(23);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_immsrc = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_IMMEDIATE__DOT__w_halfI = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_pipe = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h20660d0e__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h9ed30f6d__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_he52a0fcf__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_brev_result = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__c = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__pre_sign = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__set_ovfl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__keep_sgn_on_ovfl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_lsr_result = VL_RAND_RESET_Q(33);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_asr_result = VL_RAND_RESET_Q(33);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_lsl_result = VL_RAND_RESET_Q(33);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__mpy_result = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__this_is_a_multiply_op = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_smpy_result = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_umpy_result = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_a_input = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_b_input = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_sgn = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_hi = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend = VL_RAND_RESET_Q(63);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__diff = VL_RAND_RESET_Q(33);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_z = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_c = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__zero_divisor = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 64; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache[__Vi0]);
    }
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[__Vi0] = VL_RAND_RESET_I(16);
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__valid_mask = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v_from_pc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v_from_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__rvsrc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_v_from_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__pc_tag_lookup = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_tag_lookup = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__tag_lookup = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache = VL_RAND_RESET_I(19);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__isrc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__svmask = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__needload = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_addr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__saddr = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_advance = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_invalidate_result = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__SHIFT_INSN__DOT__shifted);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__ik = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v = VL_RAND_RESET_I(8);
    for (int __Vi0 = 0; __Vi0 < 8; ++__Vi0) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[__Vi0] = VL_RAND_RESET_I(19);
    }
    for (int __Vi0 = 0; __Vi0 < 64; ++__Vi0) {
        VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem[__Vi0]);
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr = VL_RAND_RESET_I(6);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_gbl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_lcl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cache_miss_inow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__w_cachable = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__raw_cachable_address = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cachable = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_svalid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cline = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_ctag = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_cstb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_iv = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__in_cache = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_itag = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__req_data = VL_RAND_RESET_I(13);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__gie = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__pre_shifted);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_WIDE_BUS__DOT__pre_shift = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_WIDE_BUS__DOT__wide_preshift);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_WIDE_BUS__DOT__shifted_data);
    for (int __Vi0 = 0; __Vi0 < 16; ++__Vi0) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[__Vi0] = VL_RAND_RESET_I(12);
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__UNUSED_BITS__DOT__unused_aw = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT____VdfgTmp_h05977c6b__0 = 0;
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_addr = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_sel = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_transferlen = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_trigger = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_inc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_inc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_size = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_addr = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__rx_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__tx_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_ready = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stall = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_addr = VL_RAND_RESET_I(22);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_sel = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(520, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellinp__u_sfifo__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_trigger = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_zero_len = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_sel = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_src = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_dst = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_len = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_tlen = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__first_size = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__next_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__last_request_addr = VL_RAND_RESET_I(28);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__subaddr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__fill = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__next_fill = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_last = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size = VL_RAND_RESET_I(2);
    VL_RAND_RESET_W(1024, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__next_fill = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__next_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_bytes = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift = VL_RAND_RESET_I(6);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_empty = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 16; ++__Vi0) {
        VL_RAND_RESET_W(520, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[__Vi0]);
    }
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_next = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__ik = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_inc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_size = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_addr = VL_RAND_RESET_I(29);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__subaddr = VL_RAND_RESET_I(6);
    VL_RAND_RESET_W(1024, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_data);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_data);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel);
    VL_RAND_RESET_W(128, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_last = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_outstanding = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_pipeline_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__ALT__DOT__last_owner = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__w_any = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__enable_ints = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__disable_ints = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable = VL_RAND_RESET_I(15);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_mie = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__w_any = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__wb_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__enable_ints = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__disable_ints = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__read_from_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__write_to_control = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__o_bus_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__i2cscopei__DOT__read_address = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__raddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__i2cscopei__DOT__waddr = VL_RAND_RESET_I(10);
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__i2cscopei__DOT__mem[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__i2cscopei__DOT__bw_reset_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__br_config = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__i2cscopei__DOT__br_holdoff = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__i2cscopei__DOT__holdoff_counter = VL_RAND_RESET_I(20);
    vlSelf->main__DOT__i2cscopei__DOT__dr_triggered = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__dr_primed = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__dw_trigger = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__dr_stopped = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__i2cscopei__DOT__ck_addr = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__i2cscopei__DOT__qd_data = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__i2cscopei__DOT__dr_force_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__dr_run_timeout = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__new_data = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__dr_force_inhibit = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__imm_adr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__lst_adr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__lst_val = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__i2cscopei__DOT__imm_val = VL_RAND_RESET_I(31);
    vlSelf->main__DOT__i2cscopei__DOT__record_ce = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__r_data = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__i2cscopei__DOT__br_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__br_pre_wb_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__i2cscopei__DOT__this_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__i2cscopei__DOT__nxt_mem = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__i2cscopei__DOT__br_level_interrupt = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__rcv__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__rcv__DOT__baud_counter = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__rcv__DOT__zero_baud_counter = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__rcv__DOT__q_uart = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__rcv__DOT__qq_uart = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__rcv__DOT__ck_uart = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__rcv__DOT__chg_counter = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__rcv__DOT__half_baud_time = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__rcv__DOT__data_reg = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__txv__DOT__baud_counter = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__txv__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__txv__DOT__lcl_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__txv__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__txv__DOT__zero_baud_counter = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__soft_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__r_wdt_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__rx_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__in_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__in_word = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__ps_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__ps_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__genbus__DOT__wbu_tx_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wbu_tx_data = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__genbus__DOT__ififo_codword = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__exec_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__exec_word = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__ofifo_rd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__ofifo_codword = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__ofifo_empty_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__w_bus_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__r_wdt_timer = VL_RAND_RESET_I(19);
    vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__cod_busy = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 128; ++__Vi0) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__remap[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__w_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr = VL_RAND_RESET_I(8);
    for (int __Vi0 = 0; __Vi0 < 256; ++__Vi0) {
        vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_word = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cmd_addr = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_addr = VL_RAND_RESET_I(25);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__w_addr = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__rd_len = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cword = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state = VL_RAND_RESET_I(2);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_inc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_new_addr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_read_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__zero_acks = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_bits = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__r_active = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT____Vcellinp__GEN_IDLES__DOT__buildcw__i_tx_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word = VL_RAND_RESET_I(30);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_out_nl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_in_nl = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__full_line = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen = VL_RAND_RESET_I(7);
    for (int __Vi0 = 0; __Vi0 < 128; ++__Vi0) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__remap[__Vi0] = VL_RAND_RESET_I(7);
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__newv = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter = VL_RAND_RESET_I(22);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__aword_valid = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__a_addrword = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_filled = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__pmatch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dmatch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__vaddr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__cword = VL_RAND_RESET_I(32);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__maddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__zmatch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__hmatch = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_dbld = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_hlfd = VL_RAND_RESET_I(3);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword = VL_RAND_RESET_Q(36);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__clear_table = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__w_match = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k = VL_RAND_RESET_I(32);
    for (int __Vi0 = 0; __Vi0 < 64; ++__Vi0) {
        vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo[__Vi0] = VL_RAND_RESET_Q(36);
    }
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__nxt_wrptr = VL_RAND_RESET_I(7);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_read = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 1024; ++__Vi0) {
        vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo[__Vi0] = VL_RAND_RESET_Q(36);
    }
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__nxt_wrptr = VL_RAND_RESET_I(11);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_write = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_read = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__gpioi__DOT__r_gpio = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__gpioi__DOT__x_gpio = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__gpioi__DOT__q_gpio = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__spioi__DOT__led_demo = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spioi__DOT__r_led = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__spioi__DOT__bounced = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__spioi__DOT__sw_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__next_btn = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__s_btn = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__r_btn = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__btn_pipe = VL_RAND_RESET_I(10);
    vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__r_btn_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__next_int = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe = VL_RAND_RESET_I(16);
    vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner = VL_RAND_RESET_I(8);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_dir = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr = VL_RAND_RESET_I(25);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_clk = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__br_ctr = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_stb = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_we = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_ack = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_addr = VL_RAND_RESET_I(22);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data);
    VL_RAND_RESET_W(512, vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__rtn_data);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_sel = VL_RAND_RESET_Q(64);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_shift = VL_RAND_RESET_I(4);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT____Vcellinp__UPSIZE__DOT__u_fifo__i_reset = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_full = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_empty = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 32; ++__Vi0) {
        vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[__Vi0] = VL_RAND_RESET_I(4);
    }
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr = VL_RAND_RESET_I(1);
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_rd = VL_RAND_RESET_I(1);
    vlSelf->__VdfgTmp_h503d14d1__0 = 0;
    vlSelf->__VdfgTmp_ha46ae6a3__0 = 0;
    vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__28__Vfuncout = VL_RAND_RESET_I(32);
    vlSelf->__Vfunc_main__DOT__u_i2cdma__DOT__apply_strb__29__Vfuncout = VL_RAND_RESET_I(32);
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC8__79__i_crc_data = VL_RAND_RESET_I(8);
    vlSelf->__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__80__Vfuncout = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__sgrant = VL_RAND_RESET_I(3);
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v1 = VL_RAND_RESET_I(4);
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v1 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v2 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v4 = VL_RAND_RESET_I(4);
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v4 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v5 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v6 = 0;
    vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v7 = VL_RAND_RESET_I(4);
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v7 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v8 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v9 = 0;
    vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v10 = VL_RAND_RESET_I(4);
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v10 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v11 = 0;
    vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__mnearfull = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__sgrant = VL_RAND_RESET_I(12);
    vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__wb32_xbar__DOT__grant__v1 = VL_RAND_RESET_I(13);
    vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v1 = 0;
    vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v2 = 0;
    vlSelf->__Vdly__main__DOT____Vcellout__wb32_xbar__o_sstb = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__mnearfull = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant = VL_RAND_RESET_I(2);
    vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__wbu_xbar__DOT__grant__v1 = VL_RAND_RESET_I(3);
    vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v1 = 0;
    vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v2 = 0;
    vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__mnearfull = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__holdoff_counter = VL_RAND_RESET_I(20);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stopped = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stop_pipe = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_inhibit = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_write = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__ck_addr = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__waddr = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_primed = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__emmcscopei__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__emmcscopei__DOT__mem__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvset__main__DOT__emmcscopei__DOT__mem__v0 = 0;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__holdoff_counter = VL_RAND_RESET_I(20);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stopped = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stop_pipe = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_inhibit = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_write = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__ck_addr = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__waddr = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_primed = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__sdioscopei__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__sdioscopei__DOT__mem__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvset__main__DOT__sdioscopei__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v0 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v1 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v1 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v1 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v1 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v2 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v2 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v2 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v2 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v3 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v3 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v3 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v4 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v4 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v4 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v4 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v5 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v5 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v5 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v5 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v6 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v6 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v6 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v6 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v7 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v7 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v7 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v7 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v8 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v8 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v8 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v8 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v9 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v9 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v9 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v9 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v10 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v10 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v10 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v10 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v11 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v11 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v11 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v11 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v12 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v12 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v12 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v12 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v13 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v13 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v13 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v13 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v14 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v14 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v14 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v14 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v15 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v15 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v15 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v15 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v16 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v16 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v16 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v16 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v17 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v17 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v17 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v17 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v18 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v18 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v18 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v18 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v19 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v19 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v19 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v19 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v20 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v20 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v20 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v20 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v21 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v21 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v21 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v21 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v22 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v22 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v22 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v22 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v23 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v23 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v23 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v23 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v24 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v24 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v24 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v24 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v25 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v25 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v25 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v25 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v26 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v26 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v26 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v26 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v27 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v27 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v27 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v27 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v28 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v28 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v28 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v28 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v29 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v29 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v29 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v29 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v30 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v30 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v30 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v30 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v31 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v31 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v31 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v31 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v32 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v32 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v32 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v32 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v33 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v33 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v33 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v33 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v34 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v34 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v34 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v34 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v35 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v35 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v35 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v35 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v36 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v36 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v36 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v36 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v37 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v37 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v37 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v37 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v38 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v38 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v38 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v38 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v39 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v39 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v39 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v39 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v40 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v40 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v40 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v40 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v41 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v41 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v41 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v41 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v42 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v42 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v42 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v42 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v43 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v43 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v43 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v43 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v44 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v44 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v44 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v44 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v45 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v45 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v45 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v45 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v46 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v46 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v46 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v46 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v47 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v47 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v47 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v47 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v48 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v48 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v48 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v48 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v49 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v49 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v49 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v49 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v50 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v50 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v50 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v50 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v51 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v51 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v51 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v51 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v52 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v52 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v52 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v52 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v53 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v53 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v53 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v53 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v54 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v54 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v54 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v54 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v55 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v55 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v55 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v55 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v56 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v56 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v56 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v56 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v57 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v57 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v57 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v57 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v58 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v58 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v58 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v58 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v59 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v59 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v59 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v59 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v60 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v60 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v60 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v60 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v61 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v61 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v61 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v61 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v62 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v62 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v62 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v62 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v63 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v63 = 0;
    vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v63 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v63 = 0;
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v1 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v2 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v3 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v4 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v5 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v6 = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__bus_err = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbwide_i2cdma_addr = VL_RAND_RESET_I(22);
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__subaddr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbwide_i2cdma_sel = VL_RAND_RESET_Q(64);
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys = VL_RAND_RESET_I(13);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga = VL_RAND_RESET_I(13);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__pwm_counter = VL_RAND_RESET_I(13);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_reset = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_counter = VL_RAND_RESET_I(27);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_timer = VL_RAND_RESET_I(27);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__trigger_counter = VL_RAND_RESET_I(17);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__temp_tmp = VL_RAND_RESET_I(24);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_addr = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__rx_en = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg = VL_RAND_RESET_Q(48);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg = VL_RAND_RESET_Q(40);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = VL_RAND_RESET_I(26);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg);
    VL_RAND_RESET_W(256, vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg = VL_RAND_RESET_I(20);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout = VL_RAND_RESET_I(23);
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdfrontend__DOT__wait_for_busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__imm_cycle = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr = VL_RAND_RESET_I(28);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckedge = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckcount = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__inflight = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__wbwide_i2cm_addr = VL_RAND_RESET_I(22);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(512, vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_insn_addr = VL_RAND_RESET_I(28);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_illegal = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdlyvdim0__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvset__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 = 0;
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__rx_en = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg = VL_RAND_RESET_Q(48);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg = VL_RAND_RESET_Q(40);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = VL_RAND_RESET_I(26);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg);
    VL_RAND_RESET_W(256, vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg = VL_RAND_RESET_I(20);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout = VL_RAND_RESET_I(23);
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__wait_for_busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 = VL_RAND_RESET_I(7);
    vlSelf->__Vdlyvset__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 = 0;
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__r_fill = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__console__DOT__txfifo__DOT__fifo__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__console__DOT__txfifo__DOT__fifo__v0 = VL_RAND_RESET_I(7);
    vlSelf->__Vdlyvset__main__DOT__console__DOT__txfifo__DOT__fifo__v0 = 0;
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__r_fill = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_clear_cache = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_write = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read_ack = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__wdt_reset = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchbus__DOT__r_value = VL_RAND_RESET_I(14);
    vlSelf->__Vdly__main__DOT__swic__DOT__wdbus_int = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_zero = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__r_counter = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__int_when = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 = VL_RAND_RESET_I(16);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 = 0;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_addr = VL_RAND_RESET_I(22);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0 = 0;
    VL_RAND_RESET_W(512, vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0 = 0;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_illegal = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__dbg_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_err = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length = VL_RAND_RESET_I(28);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen = VL_RAND_RESET_I(11);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr = VL_RAND_RESET_I(28);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr = VL_RAND_RESET_I(28);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len = VL_RAND_RESET_I(11);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding = VL_RAND_RESET_I(11);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len = VL_RAND_RESET_I(11);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(1024, vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr = VL_RAND_RESET_I(5);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0 = 0;
    VL_RAND_RESET_W(520, vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0 = 0;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill = VL_RAND_RESET_I(7);
    VL_RAND_RESET_W(512, vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_last = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_outstanding = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_last = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state = VL_RAND_RESET_I(15);
    vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable = VL_RAND_RESET_I(15);
    vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state = VL_RAND_RESET_I(15);
    vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable = VL_RAND_RESET_I(15);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__holdoff_counter = VL_RAND_RESET_I(20);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stopped = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stop_pipe = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_inhibit = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_write = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__ck_addr = VL_RAND_RESET_I(31);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__waddr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_primed = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__i2cscopei__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__i2cscopei__DOT__mem__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvset__main__DOT__i2cscopei__DOT__mem__v0 = 0;
    vlSelf->__Vdly__main__DOT__rcv__DOT__chg_counter = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__rcv__DOT__state = VL_RAND_RESET_I(4);
    vlSelf->__Vdly__main__DOT__rcv__DOT__data_reg = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__rcv__DOT__baud_counter = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__rcv__DOT__zero_baud_counter = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__txv__DOT__r_busy = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__txv__DOT__lcl_data = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__txv__DOT__zero_baud_counter = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_timer = VL_RAND_RESET_I(19);
    vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_reset = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__hx_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__cw_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvset__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 = 0;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__wbu_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wide_addr = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_acks_needed = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_ack = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__zero_acks = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_read_request = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word = VL_RAND_RESET_I(30);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__dw_bits = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wbu_tx_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter = VL_RAND_RESET_I(22);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cw_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cp_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 = VL_RAND_RESET_Q(36);
    vlSelf->__Vdlyvset__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 = 0;
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr = VL_RAND_RESET_I(7);
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 = VL_RAND_RESET_Q(36);
    vlSelf->__Vdlyvset__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 = 0;
    vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr = VL_RAND_RESET_I(11);
    vlSelf->__Vdly__main__DOT__genbus__DOT__ofifo_empty_n = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__o_gpio = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__spioi__DOT__r_led = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_BUTTON__DOT__btn_pipe = VL_RAND_RESET_I(10);
    vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe = VL_RAND_RESET_I(16);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_owner = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_dir = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdlyvdim0__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 = VL_RAND_RESET_I(4);
    vlSelf->__Vdlyvset__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 = 0;
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__br_config = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__raddr = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__br_config = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__raddr = VL_RAND_RESET_I(12);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock = VL_RAND_RESET_I(2);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 = VL_RAND_RESET_I(32);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 = 0;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc = VL_RAND_RESET_I(28);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend = VL_RAND_RESET_Q(63);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result = VL_RAND_RESET_I(32);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr = VL_RAND_RESET_I(22);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_iv = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cachable = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag = VL_RAND_RESET_I(19);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 = VL_RAND_RESET_I(12);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 = 0;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v = VL_RAND_RESET_I(8);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr = VL_RAND_RESET_I(22);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state = VL_RAND_RESET_I(2);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb = VL_RAND_RESET_I(1);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 = VL_RAND_RESET_I(19);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 = 0;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr = VL_RAND_RESET_I(6);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending = VL_RAND_RESET_I(5);
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = VL_RAND_RESET_I(1);
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = 0;
    vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = 0;
    vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = 0;
    vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = VL_RAND_RESET_I(8);
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = 0;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__br_config = VL_RAND_RESET_I(3);
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__raddr = VL_RAND_RESET_I(10);
    vlSelf->__Vtrigprevexpr___TOP__i_clk__0 = VL_RAND_RESET_I(1);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 = VL_RAND_RESET_I(4);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 = VL_RAND_RESET_I(4);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 = VL_RAND_RESET_I(4);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 = VL_RAND_RESET_I(4);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 = VL_RAND_RESET_I(13);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant__0 = VL_RAND_RESET_I(3);
    vlSelf->__Vtrigprevexpr___TOP__main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n__0 = VL_RAND_RESET_I(1);
    vlSelf->__VactDidInit = 0;
    for (int __Vi0 = 0; __Vi0 < 7; ++__Vi0) {
        vlSelf->__Vm_traceActivity[__Vi0] = 0;
    }
}
