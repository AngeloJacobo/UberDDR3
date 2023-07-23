// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vmain.h for the primary calling header

#include "verilated.h"
#include "verilated_dpi.h"

#include "Vmain__Syms.h"
#include "Vmain___024root.h"

VL_INLINE_OPT void Vmain___024root___ico_sequent__TOP__0(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___ico_sequent__TOP__0\n"); );
    // Init
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0;
    main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT____Vlvbound_he5148a9b__0 = 0;
    CData/*0:0*/ main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0;
    main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT____Vlvbound_h97024913__0 = 0;
    // Body
    vlSelf->main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n 
        = (1U & (~ (IData)(vlSelf->i_reset)));
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
    vlSelf->main__DOT____Vcellinp__swic__i_reset = 
        ((IData)(vlSelf->i_cpu_reset) | (IData)(vlSelf->i_reset));
    vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc 
        = (IData)((((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                    >> 1U) | (IData)(vlSelf->cpu_sim_cyc)));
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted));
    vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN 
        = (1U & (~ ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset));
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__r_halted));
    vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN 
        = (1U & (~ ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual))));
    vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset 
        = ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset));
    vlSelf->main__DOT__wbu_arbiter_upsz__DOT____Vcellinp__UPSIZE__DOT__u_fifo__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc)) 
                 | (IData)(vlSelf->i_reset)));
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
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [0U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [0U]))));
    if ((((~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [0U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
              [vlSelf->main__DOT__wb32_xbar__DOT__sindex
              [0U]] : 0U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                               [0U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                        >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                        [0U]))) & (
                                                   (0U 
                                                    >= 
                                                    vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                    [0U]) 
                                                   & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                                                      >> 
                                                      vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                      [0U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [1U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [1U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [1U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [1U]] : 0U) >> 1U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [1U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [1U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [1U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [1U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 1U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [2U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [2U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [2U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [2U]] : 0U) >> 2U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [2U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [2U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [2U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [2U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 2U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__3__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [3U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [3U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [3U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [3U]] : 0U) >> 3U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [3U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [3U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [3U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [3U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__3__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 3U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__3__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__4__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [4U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [4U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [4U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [4U]] : 0U) >> 4U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [4U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [4U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [4U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [4U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__4__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 4U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__4__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__5__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [5U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [5U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [5U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [5U]] : 0U) >> 5U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [5U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [5U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [5U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [5U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__5__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 5U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__5__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__6__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [6U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [6U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [6U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [6U]] : 0U) >> 6U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [6U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [6U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [6U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [6U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__6__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 6U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__6__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__7__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [7U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [7U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [7U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [7U]] : 0U) >> 7U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [7U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [7U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [7U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [7U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__7__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 7U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__7__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__8__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [8U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [8U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [8U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [8U]] : 0U) >> 8U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [8U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [8U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [8U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [8U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__8__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 8U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__8__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__9__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [9U]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                              >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                              [9U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [9U]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [9U]] : 0U) >> 9U)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                       [9U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                                [9U]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [9U]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                      [9U])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__9__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 9U)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__9__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__10__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [0xaU]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                                >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                [0xaU]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [0xaU]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [0xaU]] : 0U) >> 0xaU)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                           [0xaU]) 
                                          & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                             >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                             [0xaU]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [0xaU]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                        >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                        [0xaU])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__10__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 0xaU)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__10__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__11__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                     [0xbU]) & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc) 
                                >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                [0xbU]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                [0xbU]) ? vlSelf->main__DOT__wb32_xbar__DOT__request
               [vlSelf->main__DOT__wb32_xbar__DOT__sindex
               [0xbU]] : 0U) >> 0xbU)) & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                           [0xbU]) 
                                          & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__m_stb) 
                                             >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                                             [0xbU]))) 
         & ((0U >= vlSelf->main__DOT__wb32_xbar__DOT__sindex
             [0xbU]) & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mempty) 
                        >> vlSelf->main__DOT__wb32_xbar__DOT__sindex
                        [0xbU])))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__11__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__sgrant) 
                  >> 0xbU)))) {
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__11__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                     [0U]) & ((IData)(vlSelf->main__DOT__wbu_cyc) 
                              >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                              [0U]))));
    if ((((~ ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
               [0U]) ? vlSelf->main__DOT__wbu_xbar__DOT__request
              [vlSelf->main__DOT__wbu_xbar__DOT__sindex
              [0U]] : 0U)) & ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                               [0U]) & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stb) 
                                        >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                        [0U]))) & (
                                                   (0U 
                                                    >= 
                                                    vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                                    [0U]) 
                                                   & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mempty) 
                                                      >> 
                                                      vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                                      [0U])))) {
        vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant)))) {
        vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 0U;
    }
    vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant 
        = (1U & (~ ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                     [1U]) & ((IData)(vlSelf->main__DOT__wbu_cyc) 
                              >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                              [1U]))));
    if ((((~ (((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                [1U]) ? vlSelf->main__DOT__wbu_xbar__DOT__request
               [vlSelf->main__DOT__wbu_xbar__DOT__sindex
               [1U]] : 0U) >> 1U)) & ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                       [1U]) & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stb) 
                                                >> 
                                                vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                                [1U]))) 
         & ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
             [1U]) & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mempty) 
                      >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                      [1U])))) {
        vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
    }
    if ((1U & (~ ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant) 
                  >> 1U)))) {
        vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 0U;
    }
    if (vlSelf->i_reset) {
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__3__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__4__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__5__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__6__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__7__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__8__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__9__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__10__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__11__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant = 1U;
        vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant = 1U;
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request 
        = ((((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
             & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb)) 
            & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                       >> 0x18U))) & ((1U == (3U & 
                                              (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                               >> 6U))) 
                                      | (IData)(((0U 
                                                  == 
                                                  (0x2bc0U 
                                                   & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U])) 
                                                 & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                    >> 0x19U)))));
    if ((((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
            | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
           | (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en)) 
          | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request)) 
         & ((IData)(((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                      >> 0x19U) & (0x200U == (0x300U 
                                              & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U])))) 
            | ((~ (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x19U))) & (2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type)))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = 0U;
    }
    if ((((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
            | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
           | (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en)) 
          | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request)) 
         & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
            >> 0xbU))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = 0U;
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request 
        = ((((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
             & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb)) 
            & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                       >> 0x20U))) & ((1U == (3U & 
                                              (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                               >> 6U))) 
                                      | (IData)(((0U 
                                                  == 
                                                  (0x2bc0U 
                                                   & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U])) 
                                                 & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                    >> 0x21U)))));
    if ((((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
            | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
           | (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en)) 
          | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request)) 
         & ((IData)(((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                      >> 0x21U) & (0x200U == (0x300U 
                                              & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U])))) 
            | ((~ (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                           >> 0x21U))) & (2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type)))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = 0U;
    }
    if ((((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
            | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
           | (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en)) 
          | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request)) 
         & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
            >> 0xbU))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = 0U;
    }
    vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber4 
        = (((IData)(vlSelf->o_emmc_clk) << 0x19U) | 
           (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
             << 0x17U) | (((IData)(vlSelf->o_emmc_cmd) 
                           << 0x16U) | ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT____VdfgTmp_h87c0e738__0)
                                           ? (IData)(vlSelf->o_emmc_cmd)
                                           : (IData)(vlSelf->i_emmc_cmd)) 
                                         << 0x14U) 
                                        | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb) 
                                            << 0x13U) 
                                           | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data) 
                                               << 0x12U) 
                                              | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                                  << 0x11U) 
                                                 | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                                                     << 0x10U) 
                                                    | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data) 
                                                        << 8U) 
                                                       | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)
                                                           ? (IData)(vlSelf->o_emmc_dat)
                                                           : (IData)(vlSelf->i_emmc_dat)))))))))));
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request 
        = ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb) 
             & (0x3000000ULL == (0x3000000ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))) 
            & (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                & (0x40U == (0xc0U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U]))) 
               | (0U == (3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                               >> 6U))))) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                              >> 0xbU) 
                                             | ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                                                & (0x240U 
                                                   == 
                                                   (0x3c0U 
                                                    & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U])))));
    if (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
           | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
          | (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en)) 
         | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request = 0U;
    }
    if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
         & (2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type)))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request = 0U;
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request 
        = ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb) 
             & (0x300000000ULL == (0x300000000ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))) 
            & (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                & (0x40U == (0xc0U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]))) 
               | (0U == (3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                               >> 6U))))) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                              >> 0xbU) 
                                             | ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                                                & (0x240U 
                                                   == 
                                                   (0x3c0U 
                                                    & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U])))));
    if (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
           | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request)) 
          | (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en)) 
         | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request = 0U;
    }
    if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy) 
         & (2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type)))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request = 0U;
    }
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbu_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__i2ci__DOT____VdfgTmp_h373818eb__0 
        = (((IData)(vlSelf->main__DOT__i2ci__DOT__r_wait) 
            << 0x17U) | (((IData)(vlSelf->main__DOT__i2ci__DOT__soft_halt_request) 
                          << 0x16U) | (((IData)(vlSelf->main__DOT__i2ci__DOT__r_aborted) 
                                        << 0x15U) | 
                                       (((IData)(vlSelf->main__DOT__i2ci__DOT__r_err) 
                                         << 0x14U) 
                                        | (((IData)(vlSelf->main__DOT__i2ci__DOT__r_halted) 
                                            << 0x13U) 
                                           | (((IData)(vlSelf->main__DOT__i2ci__DOT__insn_valid) 
                                               << 0x12U) 
                                              | (((IData)(vlSelf->main__DOT__i2ci__DOT__half_valid) 
                                                  << 0x11U) 
                                                 | (((IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle) 
                                                     << 0x10U) 
                                                    | (((IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_scl) 
                                                        << 0xfU) 
                                                       | (((IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_sda) 
                                                           << 0xeU) 
                                                          | (((IData)(vlSelf->i_i2c_scl) 
                                                              << 0xdU) 
                                                             | (((IData)(vlSelf->i_i2c_sda) 
                                                                 << 0xcU) 
                                                                | (IData)(vlSelf->main__DOT__i2ci__DOT__insn)))))))))))));
    vlSelf->main__DOT__wbu_xbar__DOT__s_stall = (0xcU 
                                                 | ((0xfffffffeU 
                                                     & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb) 
                                                        & (((IData)(vlSelf->cpu_sim_cyc) 
                                                            | (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb)) 
                                                           << 1U))) 
                                                    | ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb) 
                                                       & (IData)(vlSelf->main__DOT__wbu_wbu_arbiter_stall))));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbwide_zip_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset 
        = (1U & ((~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc)) 
                 | (IData)(vlSelf->i_reset)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy) 
              | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce)) 
                 | ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid)) 
                    | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i) 
                       | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__step) 
                           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_user_stepped)) 
                          | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag) 
                             | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag) 
                                | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pending_interrupt) 
                                    & ((~ (IData)((0U 
                                                   != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock)))) 
                                       & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase)))) 
                                   | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy) 
                                      | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy) 
                                         | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_break) 
                                            | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_prelock_stall) 
                                               | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal) 
                                                   & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy)) 
                                                  | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_div) 
                                                      & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy)) 
                                                     | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_ALU_ILLEGAL__DOT__r_alu_illegal) 
                                                        | (IData)(vlSelf->main__DOT__swic__DOT__cpu_break))))))))))))))));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__w_in 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__high_z)
            ? (IData)(vlSelf->i_sdcard_cmd) : (IData)(vlSelf->o_sdcard_cmd));
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
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = 0U;
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request = 0U;
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_tx_request 
        = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request) 
           & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
              >> 0xaU));
    if ((IData)((0x240U == (0x3c0U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U])))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_tx_request = 0U;
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_tx_request = 0U;
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request = 0U;
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request = 0U;
    }
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_tx_request 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request) 
           & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
              >> 0xaU));
    if ((IData)((0x240U == (0x3c0U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U])))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_tx_request = 0U;
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_tx_request = 0U;
    }
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbu_stb) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT____Vcellinp__i2cscopei____pinNumber4 
        = ((0x40000000U & ((IData)(vlSelf->main__DOT__i2ci__DOT__ovw_data) 
                           << 0x15U)) | (((IData)(vlSelf->main__DOT__i2ci__DOT__i2c_abort) 
                                          << 0x1dU) 
                                         | (((IData)(vlSelf->main__DOT__i2ci__DOT__i2c_stretch) 
                                             << 0x1cU) 
                                            | (((IData)(vlSelf->main__DOT__i2ci__DOT__half_insn) 
                                                << 0x18U) 
                                               | vlSelf->main__DOT__i2ci__DOT____VdfgTmp_h373818eb__0))));
    vlSelf->main__DOT__wbu_xbar__DOT__m_stall = (1U 
                                                 & ((vlSelf->main__DOT__wbu_xbar__DOT__grant
                                                     [0U] 
                                                     >> 2U) 
                                                    | (((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mgrant) 
                                                        & ((2U 
                                                            >= 
                                                            vlSelf->main__DOT__wbu_xbar__DOT__mindex
                                                            [0U]) 
                                                           & (vlSelf->main__DOT__wbu_xbar__DOT__request
                                                              [0U] 
                                                              >> 
                                                              vlSelf->main__DOT__wbu_xbar__DOT__mindex
                                                              [0U])))
                                                        ? 
                                                       ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mfull) 
                                                        | ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_stall) 
                                                           >> 
                                                           vlSelf->main__DOT__wbu_xbar__DOT__mindex
                                                           [0U]))
                                                        : (IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stb))));
    if (vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) {
        vlSelf->main__DOT__wbu_xbar__DOT__m_stall = 0U;
    }
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_i2cdma_stb) 
              | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_i2cm_stb) 
              | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
              | (IData)(vlSelf->main__DOT__wbwide_zip_stb)));
    vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
              | (IData)(vlSelf->main__DOT__wbwide_wbu_arbiter_stb)));
    vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb 
        = ((~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset)) 
           & ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
              | (IData)(vlSelf->main__DOT__wb32_wbdown_stb)));
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
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall)) 
                 & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem)) 
                    & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy)) 
                       & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy)) 
                          | (~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR) 
                                & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                                   == (0xeU | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                               << 4U))))))))));
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbu_cyc));
    vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall 
        = ((IData)(vlSelf->main__DOT__wbu_cyc) & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__m_stall));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbwide_zip_cyc));
    vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc));
    vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb) 
           & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem) 
              & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_stalled)) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)))));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_div) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond)));
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu));
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel 
        = ((IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid) 
           & (0U == (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)));
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS 
        = vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel;
    vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall 
        = ((IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall) 
           & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb));
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
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__this_is_a_multiply_op 
        = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce) 
           & ((5U == (7U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                            >> 1U))) | (0xcU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))));
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

void Vmain___024root___eval_ico(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_ico\n"); );
    // Body
    if ((1ULL & vlSelf->__VicoTriggered.word(0U))) {
        Vmain___024root___ico_sequent__TOP__0(vlSelf);
        vlSelf->__Vm_traceActivity[1U] = 1U;
    }
}

void Vmain___024root___eval_act(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___eval_act\n"); );
}

extern const VlUnpacked<CData/*1:0*/, 128> Vmain__ConstPool__TABLE_h7c414883_0;
extern const VlUnpacked<CData/*3:0*/, 128> Vmain__ConstPool__TABLE_h9e411d43_0;
extern const VlUnpacked<CData/*0:0*/, 128> Vmain__ConstPool__TABLE_h5b51c6c5_0;
extern const VlUnpacked<CData/*0:0*/, 128> Vmain__ConstPool__TABLE_h02e0efbb_0;
extern const VlUnpacked<CData/*3:0*/, 128> Vmain__ConstPool__TABLE_h809a37d6_0;
extern const VlUnpacked<CData/*0:0*/, 64> Vmain__ConstPool__TABLE_heed7669e_0;
extern const VlUnpacked<CData/*0:0*/, 64> Vmain__ConstPool__TABLE_hdf55cab5_0;
extern const VlWide<16>/*511:0*/ Vmain__ConstPool__CONST_h93e1b771_0;
extern const VlUnpacked<CData/*0:0*/, 2048> Vmain__ConstPool__TABLE_h88ad91a4_0;
extern const VlUnpacked<CData/*3:0*/, 2048> Vmain__ConstPool__TABLE_h5f0541c3_0;
extern const VlUnpacked<CData/*0:0*/, 64> Vmain__ConstPool__TABLE_hd397e023_0;
extern const VlUnpacked<CData/*1:0*/, 64> Vmain__ConstPool__TABLE_h9becc847_0;

VL_INLINE_OPT void Vmain___024root___nba_sequent__TOP__0(Vmain___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root___nba_sequent__TOP__0\n"); );
    // Init
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__Vfuncout = 0;
    QData/*39:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__fill = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__fill = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__i_bit = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__fill = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__prior = 0;
    IData/*31:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit = 0;
    CData/*2:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set = 0;
    CData/*2:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set;
    __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__Vfuncout = 0;
    QData/*39:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__fill = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__fill = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__i_bit = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__Vfuncout = 0;
    CData/*6:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__fill = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__i_bit = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__prior = 0;
    IData/*31:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout = 0;
    SData/*15:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior = 0;
    CData/*0:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit = 0;
    CData/*2:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set = 0;
    CData/*2:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout = 0;
    CData/*3:0*/ __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set;
    __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set = 0;
    SData/*10:0*/ __Vtableidx3;
    __Vtableidx3 = 0;
    CData/*5:0*/ __Vtableidx4;
    __Vtableidx4 = 0;
    SData/*10:0*/ __Vtableidx6;
    __Vtableidx6 = 0;
    CData/*5:0*/ __Vtableidx11;
    __Vtableidx11 = 0;
    CData/*6:0*/ __Vtableidx12;
    __Vtableidx12 = 0;
    CData/*6:0*/ __Vtableidx13;
    __Vtableidx13 = 0;
    VlWide<16>/*511:0*/ __Vtemp_h211bbf5b__0;
    VlWide<32>/*1023:0*/ __Vtemp_hc94fac31__0;
    VlWide<32>/*1023:0*/ __Vtemp_hfa8722fc__0;
    VlWide<32>/*1023:0*/ __Vtemp_hc94fac31__1;
    VlWide<32>/*1023:0*/ __Vtemp_hb4dafc67__0;
    VlWide<16>/*511:0*/ __Vtemp_h04488e48__0;
    VlWide<16>/*511:0*/ __Vtemp_h0448bebe__0;
    VlWide<16>/*511:0*/ __Vtemp_h0448985a__0;
    VlWide<16>/*511:0*/ __Vtemp_h434d0da1__0;
    VlWide<16>/*511:0*/ __Vtemp_hfc2bf96b__0;
    VlWide<16>/*511:0*/ __Vtemp_h02cc08c7__0;
    // Body
    vlSelf->__Vdly__main__DOT__u_fan__DOT__pwm_counter 
        = vlSelf->main__DOT__u_fan__DOT__pwm_counter;
    vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe 
        = vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe;
    vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw 
        = vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw;
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr 
        = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr;
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr;
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr 
        = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter 
        = vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchbus__DOT__r_value 
        = vlSelf->main__DOT__swic__DOT__u_watchbus__DOT__r_value;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe;
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill 
        = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill;
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr;
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness;
    vlSelf->__Vdly__main__DOT__rcv__DOT__data_reg = vlSelf->main__DOT__rcv__DOT__data_reg;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_dir 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_dir;
    vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_owner 
        = vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner;
    vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter 
        = vlSelf->main__DOT__txv__DOT__baud_counter;
    vlSelf->__Vdly__main__DOT__txv__DOT__zero_baud_counter 
        = vlSelf->main__DOT__txv__DOT__zero_baud_counter;
    vlSelf->__Vdly__main__DOT__txv__DOT__r_busy = vlSelf->main__DOT__txv__DOT__r_busy;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 = 0U;
    vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr 
        = vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr 
        = vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr;
    vlSelf->__Vdlyvset__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__wdbus_int 
        = vlSelf->main__DOT__swic__DOT__wdbus_int;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len;
    vlSelf->__Vdly__main__DOT__rcv__DOT__chg_counter 
        = vlSelf->main__DOT__rcv__DOT__chg_counter;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__raddr 
        = vlSelf->main__DOT__i2cscopei__DOT__raddr;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__raddr 
        = vlSelf->main__DOT__sdioscopei__DOT__raddr;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__raddr 
        = vlSelf->main__DOT__emmcscopei__DOT__raddr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stop_pipe 
        = vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stop_pipe 
        = vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stop_pipe 
        = vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe;
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n 
        = vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n;
    vlSelf->__Vdly__main__DOT__genbus__DOT__ofifo_empty_n 
        = vlSelf->main__DOT__genbus__DOT__ofifo_empty_n;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__holdoff_counter 
        = vlSelf->main__DOT__i2cscopei__DOT__holdoff_counter;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__holdoff_counter 
        = vlSelf->main__DOT__sdioscopei__DOT__holdoff_counter;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__holdoff_counter 
        = vlSelf->main__DOT__emmcscopei__DOT__holdoff_counter;
    vlSelf->__Vdly__main__DOT__rcv__DOT__zero_baud_counter 
        = vlSelf->main__DOT__rcv__DOT__zero_baud_counter;
    vlSelf->__Vdly__main__DOT__rcv__DOT__baud_counter 
        = vlSelf->main__DOT__rcv__DOT__baud_counter;
    vlSelf->__Vdly__main__DOT__rcv__DOT__state = vlSelf->main__DOT__rcv__DOT__state;
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read_ack 
        = vlSelf->main__DOT__swic__DOT__cmd_read_ack;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__ck_addr 
        = vlSelf->main__DOT__i2cscopei__DOT__ck_addr;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__temp_tmp 
        = vlSelf->main__DOT__u_fan__DOT__temp_tmp;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__ck_addr 
        = vlSelf->main__DOT__emmcscopei__DOT__ck_addr;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__ck_addr 
        = vlSelf->main__DOT__sdioscopei__DOT__ck_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit;
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read 
        = vlSelf->main__DOT__swic__DOT__cmd_read;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_write 
        = vlSelf->main__DOT__i2cscopei__DOT__dr_force_write;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_inhibit 
        = vlSelf->main__DOT__i2cscopei__DOT__dr_force_inhibit;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_write 
        = vlSelf->main__DOT__sdioscopei__DOT__dr_force_write;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_inhibit 
        = vlSelf->main__DOT__sdioscopei__DOT__dr_force_inhibit;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_write 
        = vlSelf->main__DOT__emmcscopei__DOT__dr_force_write;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_inhibit 
        = vlSelf->main__DOT__emmcscopei__DOT__dr_force_inhibit;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__trigger_counter 
        = vlSelf->main__DOT__u_fan__DOT__trigger_counter;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter;
    vlSelf->__Vdly__main__DOT__spioi__DOT__GEN_BUTTON__DOT__btn_pipe 
        = vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__btn_pipe;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__hx_stb 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_timer 
        = vlSelf->main__DOT__u_fan__DOT__tach_timer;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_counter 
        = vlSelf->main__DOT__u_fan__DOT__tach_counter;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__tach_reset 
        = vlSelf->main__DOT__u_fan__DOT__tach_reset;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__cw_stb 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wbu_tx_stb 
        = vlSelf->main__DOT__genbus__DOT__wbu_tx_stb;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__waddr 
        = vlSelf->main__DOT__i2cscopei__DOT__waddr;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_primed 
        = vlSelf->main__DOT__i2cscopei__DOT__dr_primed;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wb_state 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state;
    vlSelf->__Vdly__main__DOT__wbu_stb = vlSelf->main__DOT__wbu_stb;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__waddr 
        = vlSelf->main__DOT__emmcscopei__DOT__waddr;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__waddr 
        = vlSelf->main__DOT__sdioscopei__DOT__waddr;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_primed 
        = vlSelf->main__DOT__emmcscopei__DOT__dr_primed;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_primed 
        = vlSelf->main__DOT__sdioscopei__DOT__dr_primed;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table;
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow 
        = vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched;
    vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow 
        = vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding;
    vlSelf->__Vdlyvset__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_outstanding 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_outstanding;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0 = 0U;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cp_stb 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr;
    vlSelf->__Vdly__main__DOT__txv__DOT__lcl_data = vlSelf->main__DOT__txv__DOT__lcl_data;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len;
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid 
        = vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wide_addr 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 = 0U;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__zero_acks 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__zero_acks;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_acks_needed 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cw_stb 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal;
    vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw 
        = vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw;
    vlSelf->__Vdlyvset__main__DOT__i2cscopei__DOT__mem__v0 = 0U;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state;
    vlSelf->__Vdlyvset__main__DOT__emmcscopei__DOT__mem__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__sdioscopei__DOT__mem__v0 = 0U;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
    vlSelf->__Vdly__main__DOT__swic__DOT__dbg_stb = vlSelf->main__DOT__swic__DOT__dbg_stb;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 = 0U;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
    vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v2 = 0U;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_ack 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_ack;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_read_request 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_read_request;
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len 
        = vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len;
    vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_timer 
        = vlSelf->main__DOT__genbus__DOT__r_wdt_timer;
    vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_reset 
        = vlSelf->main__DOT__genbus__DOT__r_wdt_reset;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda;
    vlSelf->__Vdlyvset__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 = 0U;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__dir 
        = vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits 
        = vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg 
        = vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__w_sda = vlSelf->main__DOT__i2ci__DOT__w_sda;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_addr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_axisi2c__DOT__state 
        = vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state;
    vlSelf->__Vdlyvset__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 = 0U;
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr;
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__mnearfull 
        = vlSelf->main__DOT__wbu_xbar__DOT__mnearfull;
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending 
        = vlSelf->main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow 
        = vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow;
    vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow 
        = vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v3 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v4 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v5 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v6 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v7 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v8 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v9 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v10 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v11 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable 
        = vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable;
    vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable 
        = vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable;
    vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state 
        = vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state;
    vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state 
        = vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state;
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_write 
        = vlSelf->main__DOT__swic__DOT__cmd_write;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__dw_bits 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb;
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid;
    vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v2 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb;
    vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
        = vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc;
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err;
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
        = vlSelf->main__DOT__wbu_xbar__DOT__sgrant;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift;
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_err 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_err;
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first 
        = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__r_counter 
        = vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks;
    vlSelf->__Vdly__main__DOT__swic__DOT__wdt_reset 
        = vlSelf->main__DOT__swic__DOT__wdt_reset;
    vlSelf->__Vdly__main__DOT__swic__DOT__cmd_clear_cache 
        = vlSelf->main__DOT__swic__DOT__cmd_clear_cache;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__br_config 
        = vlSelf->main__DOT__i2cscopei__DOT__br_config;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__br_config 
        = vlSelf->main__DOT__sdioscopei__DOT__br_config;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__br_config 
        = vlSelf->main__DOT__emmcscopei__DOT__br_config;
    vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stopped 
        = vlSelf->main__DOT__i2cscopei__DOT__dr_stopped;
    vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stopped 
        = vlSelf->main__DOT__sdioscopei__DOT__dr_stopped;
    vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stopped 
        = vlSelf->main__DOT__emmcscopei__DOT__dr_stopped;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_zero 
        = vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_zero;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_value 
        = vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_zero 
        = vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_zero;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_zero 
        = vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_zero;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_zero 
        = vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_zero;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value 
        = vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value 
        = vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value 
        = vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckcount 
        = vlSelf->main__DOT__i2ci__DOT__i2c_ckcount;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckedge 
        = vlSelf->main__DOT__i2ci__DOT__i2c_ckedge;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_last 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_last;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_addr 
        = vlSelf->main__DOT__u_fan__DOT__mem_addr;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_illegal 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal;
    vlSelf->__Vdly__main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data 
        = vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data;
    vlSelf->__Vdly__main__DOT__spioi__DOT__r_led = vlSelf->main__DOT__spioi__DOT__r_led;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v3 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v4 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v5 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v6 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v7 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v8 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v9 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v10 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v11 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v12 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v13 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v14 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v15 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v16 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v17 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v18 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v19 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v20 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v21 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v22 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v23 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v24 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v25 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v26 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v27 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v28 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v29 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v30 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v31 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v32 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v33 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v34 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v35 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v36 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v37 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v38 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v39 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v40 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v41 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v42 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v43 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v44 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v45 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v46 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v47 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v48 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v49 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v50 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v51 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v52 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v53 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v54 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v55 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v56 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v57 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v58 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v59 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v60 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v61 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v62 = 0U;
    vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v63 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_stb 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_cyc 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc;
    vlSelf->__Vdlyvset__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 = 0U;
    vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc 
        = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc;
    vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__int_when 
        = vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_when;
    vlSelf->__Vdly__o_gpio = vlSelf->o_gpio;
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__rd_addr 
        = vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr;
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__rd_addr 
        = vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr;
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__r_fill 
        = vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill;
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__r_fill 
        = vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill;
    vlSelf->__Vdlyvset__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 = 0U;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga 
        = vlSelf->main__DOT__u_fan__DOT__ctl_fpga;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys 
        = vlSelf->main__DOT__u_fan__DOT__ctl_sys;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending;
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__bus_err 
        = vlSelf->main__DOT__u_i2cdma__DOT__bus_err;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU];
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0 = 0U;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU];
    vlSelf->__Vdlyvset__main__DOT__console__DOT__txfifo__DOT__fifo__v0 = 0U;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_last 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_last;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__inflight 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc 
        = vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb 
        = vlSelf->main__DOT__u_fan__DOT__mem_stb;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = 0U;
    vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = 0U;
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cachable 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cachable;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_iv 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_iv;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr;
    vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted 
        = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted 
        = vlSelf->main__DOT__i2ci__DOT__r_halted;
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow 
        = vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow;
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_overflow 
        = vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow;
    vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_underflow 
        = vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb;
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending 
        = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_insn_addr 
        = vlSelf->main__DOT__i2ci__DOT__pf_insn_addr;
    vlSelf->__Vdly__main__DOT__wbwide_i2cm_addr = vlSelf->main__DOT__wbwide_i2cm_addr;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__rx_en = vlSelf->main__DOT__u_emmc__DOT__rx_en;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__rx_en 
        = vlSelf->main__DOT__u_sdcard__DOT__rx_en;
    vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_underflow 
        = vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__imm_cycle 
        = vlSelf->main__DOT__i2ci__DOT__imm_cycle;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdfrontend__DOT__wait_for_busy 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__wait_for_busy;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__wait_for_busy 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__wait_for_busy;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU];
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU];
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen;
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy 
        = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U];
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U];
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_valid 
        = vlSelf->main__DOT__i2ci__DOT__pf_valid;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_illegal 
        = vlSelf->main__DOT__i2ci__DOT__pf_illegal;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout;
    vlSelf->__Vdly__main__DOT__wbwide_i2cdma_cyc = vlSelf->main__DOT__wbwide_i2cdma_cyc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count 
        = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg;
    vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr 
        = vlSelf->main__DOT__i2ci__DOT__pf_jump_addr;
    vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb = vlSelf->main__DOT__wbwide_i2cm_stb;
    vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc = vlSelf->main__DOT__wbwide_i2cm_cyc;
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending;
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending;
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending;
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending 
        = vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__subaddr 
        = vlSelf->main__DOT__u_i2cdma__DOT__subaddr;
    vlSelf->__Vdly__main__DOT__wbwide_i2cdma_sel = vlSelf->main__DOT__wbwide_i2cdma_sel;
    vlSelf->__Vdly__main__DOT__wbwide_i2cdma_addr = vlSelf->main__DOT__wbwide_i2cdma_addr;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr;
    vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow 
        = vlSelf->main__DOT__u_i2cdma__DOT__r_overflow;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en;
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__mnearfull 
        = vlSelf->main__DOT__wb32_xbar__DOT__mnearfull;
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending 
        = vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending;
    vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
        = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc;
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__mnearfull 
        = vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_b__v3 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v0 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v1 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v2 = 0U;
    vlSelf->__Vdlyvset__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fifo_a__v3 = 0U;
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done 
        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done;
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done 
        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done;
    vlSelf->__Vdly__main__DOT__wbwide_xbar__DOT__sgrant 
        = vlSelf->main__DOT__wbwide_xbar__DOT__sgrant;
    vlSelf->__Vdly__main__DOT____Vcellout__wb32_xbar__o_sstb 
        = vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb;
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__sgrant 
        = vlSelf->main__DOT__wb32_xbar__DOT__sgrant;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__ika = 4U;
    vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__ikb = 4U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__ika = 4U;
    vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__ikb = 4U;
    vlSelf->main__DOT__wbu_xbar__DOT__iN = 1U;
    vlSelf->main__DOT__wbwide_xbar__DOT__iN = 4U;
    vlSelf->main__DOT__wb32_xbar__DOT__iN = 1U;
    vlSelf->main__DOT__wb32_xbar__DOT__iM = vlSelf->main__DOT__wb32_xbar__DOT__mindex
        [0U];
    vlSelf->main__DOT__wbu_xbar__DOT__iM = vlSelf->main__DOT__wbu_xbar__DOT__mindex
        [0U];
    vlSelf->main__DOT__wbwide_xbar__DOT__iM = vlSelf->main__DOT__wbwide_xbar__DOT__mindex
        [3U];
    if (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_wstb) {
        vlSelf->main__DOT__bkrami__DOT__WRITE_TO_MEMORY__DOT__ik = 0x40U;
        if ((1U & (IData)(vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v0 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v0 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v0 = 0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v0 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 1U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v1 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v1 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v1 = 8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v1 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 2U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v2 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v2 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v2 = 0x10U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v2 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 3U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v3 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v3 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v3 = 0x18U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v3 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 4U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v4 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[1U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v4 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v4 = 0x20U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v4 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 5U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v5 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[1U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v5 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v5 = 0x28U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v5 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 6U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v6 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[1U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v6 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v6 = 0x30U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v6 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 7U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v7 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[1U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v7 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v7 = 0x38U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v7 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 8U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v8 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[2U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v8 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v8 = 0x40U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v8 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 9U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v9 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[2U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v9 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v9 = 0x48U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v9 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0xaU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v10 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[2U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v10 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v10 = 0x50U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v10 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0xbU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v11 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[2U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v11 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v11 = 0x58U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v11 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0xcU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v12 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[3U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v12 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v12 = 0x60U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v12 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0xdU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v13 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[3U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v13 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v13 = 0x68U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v13 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0xeU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v14 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[3U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v14 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v14 = 0x70U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v14 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0xfU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v15 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[3U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v15 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v15 = 0x78U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v15 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x10U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v16 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[4U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v16 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v16 = 0x80U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v16 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x11U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v17 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[4U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v17 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v17 = 0x88U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v17 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x12U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v18 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[4U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v18 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v18 = 0x90U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v18 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x13U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v19 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[4U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v19 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v19 = 0x98U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v19 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x14U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v20 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[5U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v20 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v20 = 0xa0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v20 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x15U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v21 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[5U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v21 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v21 = 0xa8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v21 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x16U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v22 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[5U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v22 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v22 = 0xb0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v22 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x17U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v23 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[5U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v23 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v23 = 0xb8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v23 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x18U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v24 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[6U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v24 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v24 = 0xc0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v24 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x19U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v25 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[6U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v25 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v25 = 0xc8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v25 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x1aU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v26 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[6U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v26 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v26 = 0xd0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v26 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x1bU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v27 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[6U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v27 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v27 = 0xd8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v27 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x1cU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v28 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[7U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v28 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v28 = 0xe0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v28 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x1dU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v29 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[7U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v29 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v29 = 0xe8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v29 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x1eU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v30 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[7U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v30 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v30 = 0xf0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v30 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x1fU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v31 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[7U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v31 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v31 = 0xf8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v31 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x20U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v32 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[8U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v32 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v32 = 0x100U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v32 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x21U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v33 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[8U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v33 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v33 = 0x108U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v33 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x22U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v34 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[8U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v34 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v34 = 0x110U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v34 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x23U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v35 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[8U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v35 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v35 = 0x118U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v35 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x24U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v36 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[9U]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v36 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v36 = 0x120U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v36 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x25U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v37 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[9U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v37 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v37 = 0x128U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v37 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x26U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v38 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[9U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v38 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v38 = 0x130U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v38 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x27U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v39 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[9U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v39 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v39 = 0x138U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v39 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x28U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v40 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xaU]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v40 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v40 = 0x140U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v40 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x29U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v41 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xaU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v41 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v41 = 0x148U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v41 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x2aU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v42 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xaU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v42 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v42 = 0x150U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v42 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x2bU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v43 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xaU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v43 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v43 = 0x158U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v43 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x2cU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v44 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xbU]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v44 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v44 = 0x160U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v44 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x2dU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v45 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xbU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v45 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v45 = 0x168U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v45 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x2eU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v46 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xbU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v46 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v46 = 0x170U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v46 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x2fU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v47 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xbU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v47 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v47 = 0x178U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v47 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x30U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v48 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xcU]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v48 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v48 = 0x180U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v48 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x31U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v49 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xcU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v49 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v49 = 0x188U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v49 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x32U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v50 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xcU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v50 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v50 = 0x190U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v50 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x33U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v51 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xcU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v51 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v51 = 0x198U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v51 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x34U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v52 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xdU]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v52 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v52 = 0x1a0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v52 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x35U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v53 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xdU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v53 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v53 = 0x1a8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v53 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x36U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v54 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xdU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v54 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v54 = 0x1b0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v54 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x37U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v55 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xdU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v55 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v55 = 0x1b8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v55 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x38U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v56 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xeU]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v56 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v56 = 0x1c0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v56 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x39U)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v57 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xeU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v57 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v57 = 0x1c8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v57 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x3aU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v58 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xeU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v58 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v58 = 0x1d0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v58 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x3bU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v59 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xeU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v59 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v59 = 0x1d8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v59 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x3cU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v60 
                = (0xffU & vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xfU]);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v60 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v60 = 0x1e0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v60 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x3dU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v61 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xfU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v61 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v61 = 0x1e8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v61 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x3eU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v62 
                = (0xffU & (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xfU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v62 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v62 = 0x1f0U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v62 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel 
                           >> 0x3fU)))) {
            vlSelf->__Vdlyvval__main__DOT__bkrami__DOT__mem__v63 
                = (vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data[0xfU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__bkrami__DOT__mem__v63 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__bkrami__DOT__mem__v63 = 0x1f8U;
            vlSelf->__Vdlyvdim0__main__DOT__bkrami__DOT__mem__v63 
                = vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr;
        }
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__ik = 0x40U;
        if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 = 0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v0 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 1U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 = 8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v1 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 2U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 = 0x10U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v2 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 3U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 = 0x18U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v3 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 4U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[1U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 = 0x20U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v4 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 5U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[1U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 = 0x28U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v5 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 6U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[1U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 = 0x30U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v6 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 7U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[1U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 = 0x38U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v7 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 8U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[2U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 = 0x40U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v8 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 9U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[2U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 = 0x48U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v9 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0xaU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[2U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 = 0x50U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v10 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0xbU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[2U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 = 0x58U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v11 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0xcU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[3U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 = 0x60U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v12 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0xdU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[3U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 = 0x68U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v13 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0xeU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[3U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 = 0x70U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v14 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0xfU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[3U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 = 0x78U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v15 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x10U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[4U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 = 0x80U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v16 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x11U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[4U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 = 0x88U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v17 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x12U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[4U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 = 0x90U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v18 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x13U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[4U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 = 0x98U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v19 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x14U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[5U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 = 0xa0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v20 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x15U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[5U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 = 0xa8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v21 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x16U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[5U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 = 0xb0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v22 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x17U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[5U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 = 0xb8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v23 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x18U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[6U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 = 0xc0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v24 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x19U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[6U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 = 0xc8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v25 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x1aU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[6U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 = 0xd0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v26 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x1bU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[6U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 = 0xd8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v27 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x1cU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[7U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 = 0xe0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v28 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x1dU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[7U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 = 0xe8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v29 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x1eU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[7U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 = 0xf0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v30 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x1fU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[7U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 = 0xf8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v31 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x20U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[8U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 = 0x100U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v32 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x21U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[8U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 = 0x108U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v33 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x22U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[8U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 = 0x110U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v34 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x23U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[8U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 = 0x118U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v35 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x24U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[9U]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 = 0x120U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v36 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x25U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[9U] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 = 0x128U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v37 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x26U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[9U] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 = 0x130U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v38 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x27U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[9U] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 = 0x138U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v39 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x28U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xaU]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 = 0x140U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v40 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x29U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xaU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 = 0x148U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v41 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x2aU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xaU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 = 0x150U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v42 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x2bU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xaU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 = 0x158U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v43 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x2cU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xbU]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 = 0x160U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v44 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x2dU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xbU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 = 0x168U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v45 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x2eU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xbU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 = 0x170U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v46 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x2fU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xbU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 = 0x178U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v47 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x30U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xcU]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 = 0x180U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v48 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x31U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xcU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 = 0x188U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v49 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x32U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xcU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 = 0x190U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v50 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x33U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xcU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 = 0x198U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v51 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x34U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xdU]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 = 0x1a0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v52 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x35U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xdU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 = 0x1a8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v53 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x36U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xdU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 = 0x1b0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v54 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x37U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xdU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 = 0x1b8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v55 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x38U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xeU]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 = 0x1c0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v56 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x39U)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xeU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 = 0x1c8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v57 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x3aU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xeU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 = 0x1d0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v58 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x3bU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xeU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 = 0x1d8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v59 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x3cU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 
                = (0xffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xfU]);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 = 0x1e0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v60 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x3dU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xfU] 
                            >> 8U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 = 0x1e8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v61 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x3eU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 
                = (0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xfU] 
                            >> 0x10U));
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 = 0x1f0U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v62 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel 
                           >> 0x3fU)))) {
            vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata[0xfU] 
                   >> 0x18U);
            vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = 1U;
            vlSelf->__Vdlyvlsb__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 = 0x1f8U;
            vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_mem__v63 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr;
        }
    }
    vlSelf->__Vdly__main__DOT__u_fan__DOT__pwm_counter 
        = ((0x1387U <= (IData)(vlSelf->main__DOT__u_fan__DOT__pwm_counter))
            ? 0U : (0x1fffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_fan__DOT__pwm_counter))));
    if (vlSelf->main__DOT__wbu_arbiter_upsz__DOT____Vcellinp__UPSIZE__DOT__u_fifo__i_reset) {
        vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr = 0U;
        vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr = 0U;
        vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill = 0U;
    } else {
        if (vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_rd) {
            vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr)));
        }
        if (vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr) {
            vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr)));
        }
        vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill 
            = (0x3fU & ((1U == (((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr) 
                                 << 1U) | (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_rd)))
                         ? ((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill) 
                            - (IData)(1U)) : ((2U == 
                                               (((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr) 
                                                 << 1U) 
                                                | (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_rd)))
                                               ? ((IData)(1U) 
                                                  + (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill))
                                               : ((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr) 
                                                  - (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr)))));
    }
    if (vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_reset) {
        vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr = 0U;
        vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr = 0U;
        vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill = 0U;
    } else {
        if (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_wr) {
            vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr)));
        }
        if (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_rd) {
            vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr)));
        }
        vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill 
            = (0x3fU & ((1U == (((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_wr) 
                                 << 1U) | (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_rd)))
                         ? ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill) 
                            - (IData)(1U)) : ((2U == 
                                               (((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_wr) 
                                                 << 1U) 
                                                | (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_rd)))
                                               ? ((IData)(1U) 
                                                  + (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill))
                                               : ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr) 
                                                  - (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr)))));
    }
    if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellinp__u_sfifo__i_reset) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill = 0U;
    } else {
        if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr)));
        }
        if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr)));
        }
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill 
            = (0x1fU & ((1U == (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr) 
                                 << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd)))
                         ? ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill) 
                            - (IData)(1U)) : ((2U == 
                                               (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr) 
                                                 << 1U) 
                                                | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd)))
                                               ? ((IData)(1U) 
                                                  + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill))
                                               : ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr) 
                                                  - (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr)))));
    }
    if (vlSelf->main__DOT____Vcellinp__swic__i_reset) {
        vlSelf->__Vdly__main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter = 0x14U;
    } else if ((0U < (IData)(vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter 
            = (0x1fU & ((IData)(vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter) 
                        - (IData)(1U)));
    }
    if (vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchbus____pinNumber2) {
        vlSelf->__Vdly__main__DOT__swic__DOT__u_watchbus__DOT__r_value = 0x2000U;
        vlSelf->__Vdly__main__DOT__swic__DOT__wdbus_int = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__wdbus_int)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__u_watchbus__DOT__r_value 
            = (0x3fffU & ((IData)(0x3fffU) + (IData)(vlSelf->main__DOT__swic__DOT__u_watchbus__DOT__r_value)));
        vlSelf->__Vdly__main__DOT__swic__DOT__wdbus_int 
            = (1U == (IData)(vlSelf->main__DOT__swic__DOT__u_watchbus__DOT__r_value));
    }
    if (vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_clk) {
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness 
            = ((0x80U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness 
            = ((0x40U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness 
            = ((0x20U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness 
            = ((0x10U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness 
            = ((8U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness 
            = ((4U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness 
            = ((2U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness 
            = ((1U & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))
                ? 0x1fU : ((0x1cU < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                            ? 0x1cU : ((0x17U < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                        ? 0x17U : (
                                                   (0xfU 
                                                    < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                                    ? 0xfU
                                                    : 
                                                   ((0xbU 
                                                     < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                                     ? 0xbU
                                                     : 
                                                    ((7U 
                                                      < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                                      ? 7U
                                                      : 
                                                     ((5U 
                                                       < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                                       ? 5U
                                                       : 
                                                      ((3U 
                                                        < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                                        ? 3U
                                                        : 
                                                       ((1U 
                                                         < (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness))
                                                         ? 1U
                                                         : 0U)))))))));
    }
    if (((IData)(vlSelf->main__DOT__rcv__DOT__zero_baud_counter) 
         & (8U != (IData)(vlSelf->main__DOT__rcv__DOT__state)))) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__data_reg 
            = (((IData)(vlSelf->main__DOT__rcv__DOT__qq_uart) 
                << 7U) | (0x7fU & ((IData)(vlSelf->main__DOT__rcv__DOT__data_reg) 
                                   >> 1U)));
    }
    if ((0U == (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))) {
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_owner = 1U;
        vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_dir = 1U;
    } else if (((IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_clk) 
                & (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_dir))) {
        if ((0x80U == (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))) {
            vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_dir 
                = (1U & (~ (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_dir)));
        } else {
            vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_owner 
                = (0xfeU & ((IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner) 
                            << 1U));
        }
    } else if (vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_clk) {
        if ((1U == (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner))) {
            vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_dir 
                = (1U & (~ (IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_dir)));
        } else {
            vlSelf->__Vdly__main__DOT__spioi__DOT__knightrider__DOT__led_owner 
                = (0x7fU & ((IData)(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner) 
                            >> 1U));
        }
    }
    vlSelf->__Vdly__main__DOT__txv__DOT__zero_baud_counter 
        = (1U == (IData)(vlSelf->main__DOT__txv__DOT__baud_counter));
    if ((0xfU == (IData)(vlSelf->main__DOT__txv__DOT__state))) {
        vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter = 0U;
        vlSelf->__Vdly__main__DOT__txv__DOT__zero_baud_counter = 1U;
        if (((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
             & (~ (IData)(vlSelf->main__DOT__txv__DOT__r_busy)))) {
            vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter = 0x63U;
            vlSelf->__Vdly__main__DOT__txv__DOT__zero_baud_counter = 0U;
        }
    } else if (vlSelf->main__DOT__txv__DOT__zero_baud_counter) {
        if ((8U < (IData)(vlSelf->main__DOT__txv__DOT__state))) {
            vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter = 0U;
            vlSelf->__Vdly__main__DOT__txv__DOT__zero_baud_counter = 1U;
        } else {
            vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter 
                = ((8U == (IData)(vlSelf->main__DOT__txv__DOT__state))
                    ? 0x62U : 0x63U);
        }
    } else {
        vlSelf->__Vdly__main__DOT__txv__DOT__baud_counter 
            = (0x7fU & ((IData)(vlSelf->main__DOT__txv__DOT__baud_counter) 
                        - (IData)(1U)));
    }
    __Vtableidx13 = (((IData)(vlSelf->main__DOT__txv__DOT__r_busy) 
                      << 6U) | (((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
                                 << 5U) | (((IData)(vlSelf->main__DOT__txv__DOT__state) 
                                            << 1U) 
                                           | (IData)(vlSelf->main__DOT__txv__DOT__zero_baud_counter))));
    if ((1U & Vmain__ConstPool__TABLE_h7c414883_0[__Vtableidx13])) {
        vlSelf->main__DOT__txv__DOT__state = Vmain__ConstPool__TABLE_h9e411d43_0
            [__Vtableidx13];
    }
    vlSelf->__Vdly__main__DOT__txv__DOT__r_busy = Vmain__ConstPool__TABLE_h5b51c6c5_0
        [__Vtableidx13];
    if (((3U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state)) 
         & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack))) {
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 
            = (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                           >> 3U));
        vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags__v0 
            = (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                     >> 3U));
    }
    if (vlSelf->main__DOT__genbus__DOT__r_wdt_reset) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__ofifo_empty_n = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow = 1U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cp_stb = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state = 1U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow = 1U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow = 0U;
    } else {
        if (((IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_read) 
             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr 
                = (0x7ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr)));
        }
        if (((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_read) 
             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr 
                = (0x7fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr)));
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n)) 
                   | (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n 
                = (1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow)));
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_empty_n)) 
                   | (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_rd)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__ofifo_empty_n 
                = (1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow)));
        }
        if (vlSelf->main__DOT__genbus__DOT__in_stb) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow = 0U;
        } else if (vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_read) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow 
                = ((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow) 
                   | ((0x7fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr))) 
                      == (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr)));
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb))))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched = 0U;
        } else if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched 
                = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__w_match;
        }
        if (vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow 
                = ((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow) 
                   & (IData)(vlSelf->main__DOT__genbus__DOT__in_stb));
        } else if (vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_write) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow 
                = (((0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr))) 
                    == (0x3fU & (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr))) 
                   & ((1U & (((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr)) 
                             >> 6U)) != (1U & ((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr) 
                                               >> 6U))));
        }
        if (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__aword_valid) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cp_stb = 1U;
        } else if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__cp_stb = 0U;
        }
        if (vlSelf->main__DOT__zip_cpu_int) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request = 1U;
        } else if ((((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb) 
                     & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT____Vcellinp__GEN_IDLES__DOT__buildcw__i_tx_busy))) 
                    & (0x100000000ULL == (0xfc0000000ULL 
                                          & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb) 
              & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT____Vcellinp__GEN_IDLES__DOT__buildcw__i_tx_busy))) 
             & (0ULL == (0xfc0000000ULL & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state = 1U;
        } else if ((1U & (~ (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
                             >> 0x15U)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state = 0U;
        }
        if (vlSelf->main__DOT__wbu_cyc) {
            if (((IData)(vlSelf->main__DOT__wbu_cyc) 
                 & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len = 0U;
            } else if ((((IData)(vlSelf->main__DOT__wbu_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))) 
                        & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len)))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len 
                    = (0x3ffU & ((IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len) 
                                 - (IData)(1U)));
            }
        } else {
            vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len = 0U;
            if ((((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
                  & (~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy))) 
                 & (0xc00000000ULL == (0xc00000000ULL 
                                       & vlSelf->main__DOT__genbus__DOT__ififo_codword)))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_len 
                    = (0x3ffU & (IData)(vlSelf->main__DOT__genbus__DOT__ififo_codword));
            }
        }
        if (vlSelf->main__DOT__genbus__DOT__exec_stb) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow = 0U;
        } else if (vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_read) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow 
                = ((IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow) 
                   | ((0x7ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr))) 
                      == (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr)));
        }
        if (vlSelf->main__DOT__genbus__DOT__ofifo_rd) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow 
                = ((IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow) 
                   & (IData)(vlSelf->main__DOT__genbus__DOT__exec_stb));
        } else if (vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_write) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow 
                = (((0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr))) 
                    == (0x3ffU & (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr))) 
                   & ((1U & (((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr)) 
                             >> 0xaU)) != (1U & ((IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr) 
                                                 >> 0xaU))));
        }
    }
    if (vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_wr) {
        vlSelf->__Vdlyvval__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 
            = vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_data;
        vlSelf->__Vdlyvset__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem__v0 
            = (0x1fU & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr));
    }
    if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy) {
        if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len 
                = (0x7ffU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len) 
                             - (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size)));
            if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len) 
                 <= (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len = 0U;
            }
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size 
                = (0x7fU & ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))
                             ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))
                                 ? 1U : 2U) : ((1U 
                                                & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))
                                                ? 4U
                                                : (
                                                   ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len) 
                                                    > 
                                                    ((IData)(0x40U) 
                                                     + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size)))
                                                    ? 0x40U
                                                    : 
                                                   ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len) 
                                                    - (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size))))));
            if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc) {
                vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr 
                    = (0x3fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr) 
                                + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size)));
            } else if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
                if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size)))) {
                    vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr 
                        = (0x3eU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr));
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
                vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr 
                    = (0x3cU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr));
            } else {
                vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr = 0U;
            }
        }
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = 0U;
        if (((((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid)) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_last))) 
              & (0U == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len))) 
             & (0U < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__fill)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = 1U;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = 1U;
        }
        if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc) 
             & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack))) {
            if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
                if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
                        = (0x3fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift) 
                                    + ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc)
                                        ? 1U : 0U)));
                } else {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
                        = (0x3fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift) 
                                    + ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc)
                                        ? 2U : 0U)));
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
                        = (0x3eU & (IData)(vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift));
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
                    = (0x3fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift) 
                                + ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc)
                                    ? 4U : 0U)));
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
                    = (0x3cU & (IData)(vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift));
            } else {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift = 0U;
            }
        }
    } else {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__first_size;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid = 0U;
        vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr 
            = (0x3fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr);
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift 
            = (0x3fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr);
    }
    if (((IData)(vlSelf->main__DOT__rcv__DOT__qq_uart) 
         != (IData)(vlSelf->main__DOT__rcv__DOT__ck_uart))) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__chg_counter = 0U;
    } else if ((0x7fU != (IData)(vlSelf->main__DOT__rcv__DOT__chg_counter))) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__chg_counter 
            = (0x7fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__rcv__DOT__chg_counter)));
    }
    if ((1U & ((~ ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                   >> 2U)) | (IData)(vlSelf->main__DOT__i2cscopei__DOT__write_to_control)))) {
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__raddr = 0U;
    } else if (((IData)(vlSelf->main__DOT__i2cscopei__DOT__read_from_data) 
                & ((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe) 
                   >> 4U))) {
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__raddr 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__i2cscopei__DOT__raddr)));
    }
    if ((1U & ((~ ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                   >> 2U)) | (IData)(vlSelf->main__DOT__sdioscopei__DOT__write_to_control)))) {
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__raddr = 0U;
    } else if (((IData)(vlSelf->main__DOT__sdioscopei__DOT__read_from_data) 
                & ((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe) 
                   >> 4U))) {
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__raddr 
            = (0xfffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__sdioscopei__DOT__raddr)));
    }
    if ((1U & ((~ ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                   >> 2U)) | (IData)(vlSelf->main__DOT__emmcscopei__DOT__write_to_control)))) {
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__raddr = 0U;
    } else if (((IData)(vlSelf->main__DOT__emmcscopei__DOT__read_from_data) 
                & ((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe) 
                   >> 4U))) {
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__raddr 
            = (0xfffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__emmcscopei__DOT__raddr)));
    }
    if (((((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
           | (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_rd)) 
          | (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb)) 
         | (IData)(vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter = 0U;
    } else if ((1U & (~ (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
                         >> 0x15U)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
            = (0x3fffffU & ((IData)(1U) + vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter));
    }
    if ((4U & (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config))) {
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stop_pipe 
            = ((0x1eU & ((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe) 
                         << 1U)) | (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped));
        if (((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_triggered) 
             & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped)))) {
            vlSelf->__Vdly__main__DOT__i2cscopei__DOT__holdoff_counter 
                = (0xfffffU & ((IData)(1U) + vlSelf->main__DOT__i2cscopei__DOT__holdoff_counter));
        }
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__ck_addr 
            = ((((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_force_write) 
                 | (IData)(vlSelf->main__DOT__i2cscopei__DOT__new_data)) 
                | (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped))
                ? 0U : (0x7fffffffU & ((IData)(1U) 
                                       + vlSelf->main__DOT__i2cscopei__DOT__ck_addr)));
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_inhibit 
            = vlSelf->main__DOT__i2cscopei__DOT__dr_force_write;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_write 
            = (1U & ((((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_run_timeout) 
                       & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_force_write))) 
                      & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_force_inhibit))) 
                     | (((IData)(vlSelf->main__DOT__i2cscopei__DOT__dw_trigger) 
                         & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_triggered))) 
                        | (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_primed)))));
        if (vlSelf->main__DOT__i2cscopei__DOT__record_ce) {
            vlSelf->__Vdly__main__DOT__i2cscopei__DOT__waddr 
                = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__i2cscopei__DOT__waddr)));
            vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_primed 
                = ((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_primed) 
                   | (0x3ffU == (IData)(vlSelf->main__DOT__i2cscopei__DOT__waddr)));
        }
    } else {
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stop_pipe = 0U;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__holdoff_counter = 0U;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__ck_addr = 0U;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_write = 1U;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_force_inhibit = 0U;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__waddr = 0U;
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_primed = 0U;
    }
    if ((4U & (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config))) {
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stop_pipe 
            = ((0x1eU & ((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe) 
                         << 1U)) | (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped));
        if (((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_triggered) 
             & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped)))) {
            vlSelf->__Vdly__main__DOT__sdioscopei__DOT__holdoff_counter 
                = (0xfffffU & ((IData)(1U) + vlSelf->main__DOT__sdioscopei__DOT__holdoff_counter));
        }
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__ck_addr 
            = ((((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_force_write) 
                 | (IData)(vlSelf->main__DOT__sdioscopei__DOT__new_data)) 
                | (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped))
                ? 0U : (0x7fffffffU & ((IData)(1U) 
                                       + vlSelf->main__DOT__sdioscopei__DOT__ck_addr)));
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_inhibit 
            = vlSelf->main__DOT__sdioscopei__DOT__dr_force_write;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_write 
            = (1U & ((((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_run_timeout) 
                       & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_force_write))) 
                      & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_force_inhibit))) 
                     | (((IData)(vlSelf->main__DOT__sdioscopei__DOT__dw_trigger) 
                         & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_triggered))) 
                        | (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_primed)))));
        if (vlSelf->main__DOT__sdioscopei__DOT__record_ce) {
            vlSelf->__Vdly__main__DOT__sdioscopei__DOT__waddr 
                = (0xfffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__sdioscopei__DOT__waddr)));
            vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_primed 
                = ((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_primed) 
                   | (0xfffU == (IData)(vlSelf->main__DOT__sdioscopei__DOT__waddr)));
        }
    } else {
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stop_pipe = 0U;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__holdoff_counter = 0U;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__ck_addr = 0U;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_write = 1U;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_force_inhibit = 0U;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__waddr = 0U;
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_primed = 0U;
    }
    if ((4U & (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config))) {
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stop_pipe 
            = ((0x1eU & ((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe) 
                         << 1U)) | (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped));
        if (((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_triggered) 
             & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped)))) {
            vlSelf->__Vdly__main__DOT__emmcscopei__DOT__holdoff_counter 
                = (0xfffffU & ((IData)(1U) + vlSelf->main__DOT__emmcscopei__DOT__holdoff_counter));
        }
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__ck_addr 
            = ((((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_force_write) 
                 | (IData)(vlSelf->main__DOT__emmcscopei__DOT__new_data)) 
                | (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped))
                ? 0U : (0x7fffffffU & ((IData)(1U) 
                                       + vlSelf->main__DOT__emmcscopei__DOT__ck_addr)));
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_inhibit 
            = vlSelf->main__DOT__emmcscopei__DOT__dr_force_write;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_write 
            = (1U & ((((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_run_timeout) 
                       & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_force_write))) 
                      & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_force_inhibit))) 
                     | (((IData)(vlSelf->main__DOT__emmcscopei__DOT__dw_trigger) 
                         & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_triggered))) 
                        | (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_primed)))));
        if (vlSelf->main__DOT__emmcscopei__DOT__record_ce) {
            vlSelf->__Vdly__main__DOT__emmcscopei__DOT__waddr 
                = (0xfffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__emmcscopei__DOT__waddr)));
            vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_primed 
                = ((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_primed) 
                   | (0xfffU == (IData)(vlSelf->main__DOT__emmcscopei__DOT__waddr)));
        }
    } else {
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stop_pipe = 0U;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__holdoff_counter = 0U;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__ck_addr = 0U;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_write = 1U;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_force_inhibit = 0U;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__waddr = 0U;
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_primed = 0U;
    }
    if ((((0xfU == (IData)(vlSelf->main__DOT__rcv__DOT__state)) 
          & (~ (IData)(vlSelf->main__DOT__rcv__DOT__ck_uart))) 
         & (IData)(vlSelf->main__DOT__rcv__DOT__half_baud_time))) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__zero_baud_counter = 0U;
        vlSelf->__Vdly__main__DOT__rcv__DOT__baud_counter = 0x63U;
    } else if ((9U == (IData)(vlSelf->main__DOT__rcv__DOT__state))) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__zero_baud_counter = 1U;
        vlSelf->__Vdly__main__DOT__rcv__DOT__baud_counter = 0U;
    } else if (((IData)(vlSelf->main__DOT__rcv__DOT__zero_baud_counter) 
                & (8U > (IData)(vlSelf->main__DOT__rcv__DOT__state)))) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__zero_baud_counter = 0U;
        vlSelf->__Vdly__main__DOT__rcv__DOT__baud_counter = 0x63U;
    } else {
        if ((1U == (IData)(vlSelf->main__DOT__rcv__DOT__baud_counter))) {
            vlSelf->__Vdly__main__DOT__rcv__DOT__zero_baud_counter = 1U;
        }
        if ((1U & (~ (IData)(vlSelf->main__DOT__rcv__DOT__zero_baud_counter)))) {
            vlSelf->__Vdly__main__DOT__rcv__DOT__baud_counter 
                = (0x7fU & ((IData)(vlSelf->main__DOT__rcv__DOT__baud_counter) 
                            - (IData)(1U)));
        }
    }
    __Vtableidx12 = (((IData)(vlSelf->main__DOT__rcv__DOT__zero_baud_counter) 
                      << 6U) | (((IData)(vlSelf->main__DOT__rcv__DOT__half_baud_time) 
                                 << 5U) | (((IData)(vlSelf->main__DOT__rcv__DOT__ck_uart) 
                                            << 4U) 
                                           | (IData)(vlSelf->main__DOT__rcv__DOT__state))));
    if (Vmain__ConstPool__TABLE_h02e0efbb_0[__Vtableidx12]) {
        vlSelf->__Vdly__main__DOT__rcv__DOT__state 
            = Vmain__ConstPool__TABLE_h809a37d6_0[__Vtableidx12];
    }
    if ((1U & ((IData)(vlSelf->main__DOT____Vcellinp__swic__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_cyc))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read_ack = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__dbg_cpu_read) {
        vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read_ack = 1U;
        vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read = 1U;
    } else {
        if (vlSelf->main__DOT__swic__DOT__cmd_read_ack) {
            vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read_ack = 0U;
        }
        if (vlSelf->main__DOT__swic__DOT__cmd_read) {
            vlSelf->__Vdly__main__DOT__swic__DOT__cmd_read = 0U;
        }
    }
    if (vlSelf->main__DOT__u_fan__DOT__i2cd_valid) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__temp_tmp 
            = ((0xffff00U & (vlSelf->main__DOT__u_fan__DOT__temp_tmp 
                             << 8U)) | (IData)(vlSelf->main__DOT__u_fan__DOT__i2cd_data));
    }
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset)) 
           & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) 
              & (0x1eU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit))));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result = 0U;
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor = 0U;
    } else {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe 
            = ((2U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe) 
                      << 1U)) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__this_is_a_multiply_op));
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                = (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                   << 1U);
            if ((1U & (~ (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__diff 
                                  >> 0x20U))))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                    = (1U | vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result);
            }
        } else {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign)
                    ? (- vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result)
                    : 0U);
        }
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit 
            = (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign)))
                ? (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit)))
                : 0U);
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign) 
             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy))) {
            if ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor 
                 >> 0x1fU)) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor 
                    = (- vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor);
            }
        } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr;
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr = 0U;
    } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) {
        __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
        __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout = 0U;
        if ((1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout)));
        }
        if ((2U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout)));
        }
        if ((4U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout)));
        }
        if ((8U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout)));
        }
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr 
            = (0x3ffU & (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr) 
                            << 2U) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr)) 
                          + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__45__Vfuncout)) 
                         >> 2U));
        __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
        __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout = 0U;
        if ((1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout)));
        }
        if ((2U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout)));
        }
        if ((4U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout)));
        }
        if ((8U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__set))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout)));
        }
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr 
            = (3U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr) 
                     + (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__46__Vfuncout)));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr = 0U;
    } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) {
        __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
        __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout = 0U;
        if ((1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout)));
        }
        if ((2U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout)));
        }
        if ((4U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout)));
        }
        if ((8U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout)));
        }
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr 
            = (0x3ffU & (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr) 
                            << 2U) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr)) 
                          + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__87__Vfuncout)) 
                         >> 2U));
        __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb;
        __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout = 0U;
        if ((1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout)));
        }
        if ((2U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout)));
        }
        if ((4U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout)));
        }
        if ((8U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__set))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout 
                = (7U & ((IData)(1U) + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout)));
        }
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr 
            = (3U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr) 
                     + (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__COUNTONES__88__Vfuncout)));
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present) 
                                              >> 2U))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter = 0U;
    } else if ((1U & (~ (IData)((0x3ffU == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter)))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter)));
    }
    if (vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc) {
        if ((1U == (((IData)(vlSelf->main__DOT__u_fan__DOT__mem_stb) 
                     << 1U) | (IData)(vlSelf->main__DOT__u_fan__DOT__mem_ack)))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight 
                = (3U & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight) 
                         - (IData)(1U)));
        } else if ((2U == (((IData)(vlSelf->main__DOT__u_fan__DOT__mem_stb) 
                            << 1U) | (IData)(vlSelf->main__DOT__u_fan__DOT__mem_ack)))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight 
                = (3U & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight)));
        }
    } else {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight = 0U;
    }
    vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr 
        = ((1U & (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__clear_table) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb))) 
                  | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb))))
            ? 1U : (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr))));
    if ((1U & ((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
               | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb))))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table = 1U;
    } else if (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table 
            = (0x209U >= (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr));
    }
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr 
        = ((1U & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                    | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
                   | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)) 
                  | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) 
                      & (0x3ffU == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr))) 
                     & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb))))
            ? 0U : (3U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                          + (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))));
    if ((1U & (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellinp__u_sfifo__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc))) 
               | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_err)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding = 0U;
    } else if ((2U == ((((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb) 
                         & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stall))) 
                        << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding 
            = (0x7ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding)));
    } else if ((1U == ((((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb) 
                         & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stall))) 
                        << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding 
            = (0x7ffU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding) 
                         - (IData)(1U)));
    }
    if (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
         & (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb)))))) {
        vlSelf->__Vdlyvval__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 
            = (((IData)((vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                         >> 0x1fU)) << 0x1eU) | (0x3fffffffU 
                                                 & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word)));
        vlSelf->__Vdlyvset__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__compression_tbl__v0 
            = vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) {
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[1U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[1U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[2U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[2U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[3U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[3U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[4U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[4U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[5U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[5U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[6U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[6U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[7U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[7U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[8U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[8U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[9U] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[9U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0xaU] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0xaU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0xbU] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0xbU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0xcU] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0xcU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0xdU] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0xdU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0xeU] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0xeU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0[0xfU] 
            = vlSelf->main__DOT__swic__DOT__cpu_idata[0xfU];
        vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache__v0 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr;
    }
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr 
        = ((1U & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                    | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
                   | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)) 
                  | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) 
                      & (0x3ffU == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr))) 
                     & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb))))
            ? 0U : (3U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr) 
                          + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))));
    if (((IData)(vlSelf->main__DOT__genbus__DOT__ps_full) 
         & (~ (IData)(vlSelf->main__DOT__txv__DOT__r_busy)))) {
        vlSelf->__Vdly__main__DOT__txv__DOT__lcl_data 
            = vlSelf->main__DOT__genbus__DOT__ps_data;
    } else if (vlSelf->main__DOT__txv__DOT__zero_baud_counter) {
        vlSelf->__Vdly__main__DOT__txv__DOT__lcl_data 
            = (0x80U | (0x7fU & ((IData)(vlSelf->main__DOT__txv__DOT__lcl_data) 
                                 >> 1U)));
    }
    if ((((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
          & (~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy))) 
         & (0ULL == (0xf00000000ULL & vlSelf->main__DOT__genbus__DOT__ififo_codword)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wide_addr 
            = (IData)(vlSelf->main__DOT__genbus__DOT__ififo_codword);
    } else if ((((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
                 & (~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy))) 
                & (0x200000000ULL == (0xe00000000ULL 
                                      & vlSelf->main__DOT__genbus__DOT__ififo_codword)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wide_addr 
            = (vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr 
               + (((IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                            >> 0x1fU)) << 0x1eU) | 
                  (0x3fffffffU & (IData)(vlSelf->main__DOT__genbus__DOT__ififo_codword))));
    } else if ((((IData)(vlSelf->main__DOT__wbu_stb) 
                 & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))) 
                & (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_inc))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__wide_addr 
            = ((IData)(1U) + vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr);
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
         & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack))) {
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 
            = (0xffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr 
                          >> 6U));
        vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags__v0 
            = (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr 
                     >> 3U));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
                | (~ (IData)(vlSelf->main__DOT__wbu_cyc))) 
               | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__zero_acks = 1U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_acks_needed = 0U;
    } else if ((2U == ((((IData)(vlSelf->main__DOT__wbu_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))) 
                        << 1U) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__zero_acks = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_acks_needed 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed)));
    } else if ((1U == ((((IData)(vlSelf->main__DOT__wbu_stb) 
                         & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))) 
                        << 1U) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__zero_acks 
            = (1U == (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed));
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__r_acks_needed 
            = (0x3ffU & ((IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed) 
                         - (IData)(1U)));
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__instruction_decoder__i_reset) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp = 0U;
    } else {
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) 
             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal 
                = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_valid))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 0U;
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_div) 
                 & (0xeU == (0xeU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA))))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 1U;
            }
            if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_fpu) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 1U;
            }
            if ((IData)(((0xeU == (0xeU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA))) 
                         & (0x1aU == (0x1eU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)))))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 1U;
            }
            if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal = 1U;
            }
        }
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) {
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__pf_valid))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp = 0U;
            } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch_stb) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp = 0U;
            } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__pf_valid) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp 
                    = ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                        >> 0x1fU) ? (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_ljmp)
                        : (0x7c87c000U == vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword));
            } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase) 
                        & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                           >> 0x1fU))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp 
                    = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_ljmp;
            }
        }
    }
    if (vlSelf->main__DOT__i2cscopei__DOT__record_ce) {
        vlSelf->__Vdlyvval__main__DOT__i2cscopei__DOT__mem__v0 
            = vlSelf->main__DOT__i2cscopei__DOT__r_data;
        vlSelf->__Vdlyvset__main__DOT__i2cscopei__DOT__mem__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__i2cscopei__DOT__mem__v0 
            = vlSelf->main__DOT__i2cscopei__DOT__waddr;
    }
    vlSelf->__Vdlyvval__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl__v0 
        = (((IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word 
                     >> 0x1fU)) << 0x1eU) | (0x3fffffffU 
                                             & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word)));
    vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__compression_tbl__v0 
        = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr;
    if (vlSelf->main__DOT__emmcscopei__DOT__record_ce) {
        vlSelf->__Vdlyvval__main__DOT__emmcscopei__DOT__mem__v0 
            = vlSelf->main__DOT__emmcscopei__DOT__r_data;
        vlSelf->__Vdlyvset__main__DOT__emmcscopei__DOT__mem__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__emmcscopei__DOT__mem__v0 
            = vlSelf->main__DOT__emmcscopei__DOT__waddr;
    }
    if (vlSelf->main__DOT__sdioscopei__DOT__record_ce) {
        vlSelf->__Vdlyvval__main__DOT__sdioscopei__DOT__mem__v0 
            = vlSelf->main__DOT__sdioscopei__DOT__r_data;
        vlSelf->__Vdlyvset__main__DOT__sdioscopei__DOT__mem__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__sdioscopei__DOT__mem__v0 
            = vlSelf->main__DOT__sdioscopei__DOT__waddr;
    }
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb 
        = ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                   | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
                  | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)))
            ? 0U : (0xfU & ((2U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))
                             ? (0xfU & ((0x7ffffff8U 
                                         & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb) 
                                            << 3U)) 
                                        | ((0x18U >> (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr)) 
                                           >> 1U)))
                             : ((1U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))
                                 ? (0xfU & ((0x7ffffff8U 
                                             & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb) 
                                                << 3U)) 
                                            | (((0x10U 
                                                 & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill) 
                                                    << 4U)) 
                                                >> (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr)) 
                                               >> 1U)))
                                 : ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb) 
                                    << 3U)))));
    if ((1U & (((IData)(vlSelf->main__DOT____Vcellinp__swic__i_reset) 
                | (~ (IData)(vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc))) 
               | (IData)(vlSelf->main__DOT__swic__DOT__no_dbg_err)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__dbg_stb = 0U;
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_stb)) 
                      | (~ (IData)(vlSelf->main__DOT__swic__DOT__dbg_stall))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__dbg_stb 
            = ((IData)(vlSelf->main__DOT____Vcellinp__swic__i_dbg_stb) 
               | (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb));
    }
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid 
        = ((~ (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                  | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
                 | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog)) 
               | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) 
                   & (0x3ffU == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr))) 
                  & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb)))) 
           & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid) 
              | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb)));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) {
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_gpreg_vl;
        vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset__v0 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id;
    }
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb 
        = ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                   | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
                  | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)))
            ? 0U : (0xfU & ((2U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))
                             ? (0xfU & ((0x7ffffff8U 
                                         & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb) 
                                            << 3U)) 
                                        | ((0x18U >> (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr)) 
                                           >> 1U)))
                             : ((1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill))
                                 ? (0xfU & ((0x7ffffff8U 
                                             & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb) 
                                                << 3U)) 
                                            | (((0x10U 
                                                 & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill) 
                                                    << 4U)) 
                                                >> (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr)) 
                                               >> 1U)))
                                 : ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb) 
                                    << 3U)))));
    if ((1U & ((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__wbu_cyc))))) {
        vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v0 = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available) {
            vlSelf->__Vdlyvval__main__DOT__wbu_xbar__DOT__grant__v1 
                = vlSelf->main__DOT__wbu_xbar__DOT__request
                [0U];
            vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v1 = 1U;
        } else if (vlSelf->main__DOT__wbu_xbar__DOT__m_stb) {
            vlSelf->__Vdlyvset__main__DOT__wbu_xbar__DOT__grant__v2 = 1U;
        }
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_sgn 
        = ((2U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_sgn) 
                  << 1U)) | (1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn)));
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid 
        = ((~ (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                  | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
                 | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full)) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog)) 
               | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid) 
                   & (0x3ffU == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr))) 
                  & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb)))) 
           & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid) 
              | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb)));
    if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) 
          & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack)) 
         & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr 
            = ((0x38U & (IData)(vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr)) 
               | (7U & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr))));
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr 
            = (0x38U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                        >> 6U));
    }
    if (vlSelf->main__DOT__wbu_cyc) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_ack 
            = ((IData)(vlSelf->main__DOT__wbu_we) ? 
               (((((IData)(vlSelf->main__DOT__wbu_stb)
                    ? 1U : 0U) + (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed)) 
                 + ((((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
                      & (~ (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy))) 
                     & (0x400000000ULL == (0xc00000000ULL 
                                           & vlSelf->main__DOT__genbus__DOT__ififo_codword)))
                     ? 1U : 0U)) <= ((IData)(1U) + 
                                     ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)
                                       ? 1U : 0U)))
                : (((IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len) 
                    + (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed)) 
                   <= ((IData)(1U) + ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)
                                       ? 1U : 0U))));
    } else {
        vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_ack = 1U;
        if (((IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n) 
             & (0xc00000000ULL == (0xc00000000ULL & vlSelf->main__DOT__genbus__DOT__ififo_codword)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_ack 
                = (1U >= (0x3ffU & (IData)(vlSelf->main__DOT__genbus__DOT__ififo_codword)));
        }
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce) 
         & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase) 
            | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_valid)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
            = (0xffffffeU & vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc);
        if ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
             >> 0x1fU)) {
            if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
                    = ((1U & vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc) 
                       | (0xffffffeU & (((IData)(1U) 
                                         + (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
                                            >> 1U)) 
                                        << 1U)));
            } else {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
                    = (2U | (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc));
            }
        } else {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc 
                = (0xffffffcU & (((IData)(1U) + (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc 
                                                 >> 2U)) 
                                 << 2U));
        }
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr 
            = (0x3fU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)
                         ? ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr))
                         : (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr)));
    } else {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr 
            = (0x3fU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr);
        if ((((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce)) 
              | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))) 
             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr 
                = (0x38U & (IData)(vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr));
        }
    }
    vlSelf->__Vdly__main__DOT__genbus__DOT__runwb__DOT__last_read_request 
        = (1U & ((IData)(vlSelf->main__DOT__genbus__DOT__r_wdt_reset) 
                 | ((IData)(vlSelf->main__DOT__wbu_cyc)
                     ? ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                        | (((IData)(vlSelf->main__DOT__wbu_stb) 
                            & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))
                            ? (2U >= (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len))
                            : (((IData)(vlSelf->main__DOT__wbu_stb) 
                                & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))
                                ? (1U >= (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len))
                                : (1U >= (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len)))))
                     : ((((~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n)) 
                          | (IData)(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy)) 
                         | (3U != (3U & (IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                                 >> 0x22U))))) 
                        | (1U >= (0x3ffU & (IData)(vlSelf->main__DOT__genbus__DOT__ififo_codword)))))));
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__genbus__DOT__soft_reset))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_timer = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_reset = 1U;
    } else if ((1U & ((~ (IData)(vlSelf->main__DOT__wbu_cyc)) 
                      | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_timer = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_reset = 0U;
    } else if ((0x7ffffU == vlSelf->main__DOT__genbus__DOT__r_wdt_timer)) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_reset = 1U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_timer = 0U;
    } else {
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_timer 
            = (0x7ffffU & ((IData)(1U) + vlSelf->main__DOT__genbus__DOT__r_wdt_timer));
        vlSelf->__Vdly__main__DOT__genbus__DOT__r_wdt_reset = 0U;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign) {
        if ((1U & (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
                           >> 0x1fU)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend = 0ULL;
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
                = ((0x7ffffffe00000000ULL & vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend) 
                   | (0x1ffffffffULL & (- (0x100000000ULL 
                                           | (QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend))))));
        }
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
            = (0x7ffffffffffffffeULL & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
                                        << 1U));
        if ((1U & (~ (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__diff 
                              >> 0x20U))))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
                = ((0xffffffffULL & vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend) 
                   | ((QData)((IData)((0x7fffffffU 
                                       & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__diff)))) 
                      << 0x20U));
        }
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
            = (QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata));
    }
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign 
        = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset)) 
                 & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign)
                     ? ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor 
                         >> 0x1fU) ^ (IData)((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend 
                                              >> 0x1fU)))
                     : ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) 
                        & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign) 
                           & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__zero_divisor)))))));
    if (vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_write) {
        vlSelf->__Vdlyvval__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 
            = vlSelf->main__DOT__genbus__DOT__in_word;
        vlSelf->__Vdlyvset__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__fifo__v0 
            = (0x3fU & (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr));
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__zero_divisor))) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid = 1U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy) {
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit) {
            vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid 
                = (1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign)));
        }
    } else {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid 
            = vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign;
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) {
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 
            = ((0xf00U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                          << 8U)) | ((0xc0U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn) 
                                               << 5U)) 
                                     | (0x3fU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr)));
        vlSelf->__Vdlyvset__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data__v0 
            = (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr));
    }
    if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb) 
          & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stall))) 
         & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_addr)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_addr 
            = ((0x3ffff8U & vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_addr) 
               | (7U & ((IData)(1U) + vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr)));
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_addr 
            = (0x3ffff8U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                            >> 6U));
    }
    if (vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_write) {
        vlSelf->__Vdlyvval__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 
            = vlSelf->main__DOT__genbus__DOT__exec_word;
        vlSelf->__Vdlyvset__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__fifo__v0 
            = (0x3ffU & (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr));
    }
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mgrant) 
           & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_err) 
              >> vlSelf->main__DOT__wbu_xbar__DOT__mindex
              [0U]));
    if ((4U & vlSelf->main__DOT__wbu_xbar__DOT__grant
         [0U])) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
            = (1U & (~ (IData)(vlSelf->main__DOT__wbu_err)));
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__wbu_cyc))) 
               | (IData)(vlSelf->main__DOT__wbu_err)))) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = 0U;
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc))))) {
        vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v0 = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available) {
            vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v1 
                = vlSelf->main__DOT__wbwide_xbar__DOT__request
                [0U];
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v1 = 1U;
        } else if ((1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb))) {
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v2 = 1U;
        }
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                                              >> 1U))))) {
        vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v3 = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__requested_channel_is_available) {
            vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v4 
                = vlSelf->main__DOT__wbwide_xbar__DOT__request
                [1U];
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v4 = 1U;
        } else if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb))) {
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v5 = 1U;
        }
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                                              >> 2U))))) {
        vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v6 = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__requested_channel_is_available) {
            vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v7 
                = vlSelf->main__DOT__wbwide_xbar__DOT__request
                [2U];
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v7 = 1U;
        } else if ((4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb))) {
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v8 = 1U;
        }
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (~ ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                                              >> 3U))))) {
        vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v9 = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__requested_channel_is_available) {
            vlSelf->__Vdlyvval__main__DOT__wbwide_xbar__DOT__grant__v10 
                = vlSelf->main__DOT__wbwide_xbar__DOT__request
                [3U];
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v10 = 1U;
        } else if ((8U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb))) {
            vlSelf->__Vdlyvset__main__DOT__wbwide_xbar__DOT__grant__v11 = 1U;
        }
    }
    if (vlSelf->main__DOT__swic__DOT__cmd_reset) {
        vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__r_counter = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_zero = 1U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_value = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_zero = 1U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_zero = 1U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_zero = 1U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i = 0U;
    } else {
        if (vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__enable_ints) {
            vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable 
                = (0x7fffU & ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable) 
                              | (vlSelf->main__DOT__swic__DOT__sys_data 
                                 >> 0x10U)));
        } else if (vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__disable_ints) {
            vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable 
                = ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable) 
                   & (~ (vlSelf->main__DOT__swic__DOT__sys_data 
                         >> 0x10U)));
        }
        if (vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__enable_ints) {
            vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable 
                = (0x7fffU & ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable) 
                              | (vlSelf->main__DOT__swic__DOT__sys_data 
                                 >> 0x10U)));
        } else if (vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__disable_ints) {
            vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable 
                = ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable) 
                   & (~ (vlSelf->main__DOT__swic__DOT__sys_data 
                         >> 0x10U)));
        }
        vlSelf->__Vdly__main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state 
            = ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__wb_write)
                ? ((IData)(vlSelf->main__DOT__swic__DOT__main_int_vector) 
                   | ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state) 
                      & (~ vlSelf->main__DOT__swic__DOT__sys_data)))
                : ((IData)(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state) 
                   | (IData)(vlSelf->main__DOT__swic__DOT__main_int_vector)));
        vlSelf->__Vdly__main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state 
            = ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__wb_write)
                ? ((IData)(vlSelf->main__DOT__swic__DOT__alt_int_vector) 
                   | ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state) 
                      & (~ vlSelf->main__DOT__swic__DOT__sys_data)))
                : ((IData)(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state) 
                   | (IData)(vlSelf->main__DOT__swic__DOT__alt_int_vector)));
        if ((0U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = 0U;
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = 1U;
            } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = 0U;
            } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                        & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__w_cachable)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack = 1U;
            }
        } else if ((3U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)
                    ? ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack) 
                       | (3U == (3U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr) 
                                       >> 1U)))) : 
                   ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack) 
                    | (7U == (7U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr)))));
        } else if ((1U == (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                            << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack 
                = (2U >= (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending));
        } else if ((2U == (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                            << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack 
                = (1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc)) 
                         | (0U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending))));
        }
        if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__r_counter 
                = ((IData)(1U) + vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter);
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks 
                = ((IData)(1U) + vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks);
        }
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv) 
             & (0xeU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag) 
                   & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                      >> 0xbU));
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag) 
                   & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                      >> 0xaU));
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i) 
                   & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                      >> 8U));
        } else {
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_error) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag = 1U;
            }
            if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag = 1U;
            }
            if ((((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)) 
                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_ALU_ILLEGAL__DOT__r_alu_illegal)) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i = 1U;
            }
        }
        if (vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__wb_write) {
            vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_zero 
                = (0U == (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data));
            vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_value 
                = (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data);
        } else {
            if (((IData)(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_running) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)))) {
                if ((1U == vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value)) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_zero = 1U;
                }
            }
            if (((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_running))) {
                if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_zero)))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_watchdog__DOT__r_value 
                        = (0x7fffffffU & (vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value 
                                          - (IData)(1U)));
                }
            }
        }
        if (vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__wb_write) {
            vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_zero 
                = (0U == (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data));
            vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value 
                = (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data);
        } else {
            if (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_running) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)))) {
                if ((1U == vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value)) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_zero = 1U;
                } else if (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_zero) 
                            & (IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_zero = 0U;
                }
            }
            if (((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_running))) {
                if (vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_zero) {
                    if (vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload) {
                        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value 
                            = vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_interval_count;
                    }
                } else {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_c__DOT__r_value 
                        = (0x7fffffffU & (vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value 
                                          - (IData)(1U)));
                }
            }
        }
        if (vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__wb_write) {
            vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_zero 
                = (0U == (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data));
            vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value 
                = (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data);
        } else {
            if (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_running) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)))) {
                if ((1U == vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value)) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_zero = 1U;
                } else if (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_zero) 
                            & (IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_zero = 0U;
                }
            }
            if (((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_running))) {
                if (vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_zero) {
                    if (vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload) {
                        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value 
                            = vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_interval_count;
                    }
                } else {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_b__DOT__r_value 
                        = (0x7fffffffU & (vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value 
                                          - (IData)(1U)));
                }
            }
        }
        if (vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__wb_write) {
            vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_zero 
                = (0U == (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data));
            vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value 
                = (0x7fffffffU & vlSelf->main__DOT__swic__DOT__sys_data);
        } else {
            if (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_running) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)))) {
                if ((1U == vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value)) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_zero = 1U;
                } else if (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_zero) 
                            & (IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_zero = 0U;
                }
            }
            if (((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_running))) {
                if (vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_zero) {
                    if (vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload) {
                        vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value 
                            = vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_interval_count;
                    }
                } else {
                    vlSelf->__Vdly__main__DOT__swic__DOT__u_timer_a__DOT__r_value 
                        = (0x7fffffffU & (vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value 
                                          - (IData)(1U)));
                }
            }
        }
    }
    if (((IData)(vlSelf->main__DOT____Vcellinp__swic__i_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__cmd_write = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__cmd_clear_cache = 0U;
    } else {
        if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_write)) 
                   | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall))))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__cmd_write 
                = vlSelf->main__DOT__swic__DOT__dbg_cpu_write;
        }
        if ((((IData)(vlSelf->main__DOT__swic__DOT__dbg_cmd_write) 
              & (IData)(vlSelf->main__DOT__swic__DOT__clear_cache_request)) 
             & (IData)(vlSelf->main__DOT__swic__DOT__halt_request))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__cmd_clear_cache = 1U;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_halt) 
                    & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__cmd_clear_cache = 0U;
        }
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
            & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr = 0U;
    } else {
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr)));
        }
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid) 
             | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_svalid))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr)));
        } else if (((1U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state)) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr)));
        } else if (((2U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state)) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr)));
        }
    }
    if (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__clear_table) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr = 0x3ffU;
    } else {
        if (((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy)) 
             & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb))) {
            if ((7U == (7U & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                      >> 0x21U))))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr 
                    = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr)));
            }
        }
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr 
            = (0x3ffU & ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb)) 
                                | (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb))))
                          ? ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr) 
                             - (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
                                 & (0xe00000000ULL 
                                    == (0xe00000000ULL 
                                        & vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword)))
                                 ? 0U : 1U)) : ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr) 
                                                - (IData)(1U))));
    }
    if (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
         & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word 
            = (0x3fffffffU & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword));
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__dw_bits 
            = (0x3fU & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                >> 0x1eU)));
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy)))) {
        if ((1U < (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__dw_bits 
                = (0x3fU & (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word 
                            >> 0x18U));
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word 
                = ((0x3fU & vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word) 
                   | (0x3fffffc0U & (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word 
                                     << 6U)));
        } else if ((1U & (~ ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits) 
                             >> 6U)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__dw_bits = 0x40U;
        }
    }
    if (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb) 
         & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy)))) {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb 
            = (1U & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__full_line) 
                     | (~ ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits) 
                           >> 6U))));
    } else if (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy) {
        if ((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb = 0U;
        }
    } else {
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb 
            = ((((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy)) 
                 & (~ ((IData)(vlSelf->main__DOT__wbu_cyc) 
                       | ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb) 
                          | (IData)(vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy))))) 
                & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_out_nl))) 
               & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_in_nl));
    }
    if (vlSelf->i_reset) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__hx_stb = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__cw_stb = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wbu_tx_stb = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len = 0U;
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__ln_stb = 0U;
        vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount = 0xc8U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckedge = 0U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckcount = 0xfffU;
        vlSelf->__Vdly__main__DOT__spioi__DOT__r_led = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga = 0x1387U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys = 0x1387U;
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__bus_err = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 0U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr = 0U;
    } else {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present 
            = ((6U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present) 
                      << 1U)) | (IData)(vlSelf->i_sdcard_detect));
        if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy))))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__hx_stb 
                = vlSelf->main__DOT__genbus__DOT__rx_valid;
        }
        vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb 
            = ((6U & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb) 
                      << 1U)) | ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
                                 & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cod_busy))));
        if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb)) 
                   | (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))))))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__cw_stb 
                = vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__w_stb;
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wbu_tx_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__ps_full))))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wbu_tx_stb 
                = vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb;
        }
        if ((1U & (((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb)) 
                    | (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))))) 
                   | (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__w_stb))))) {
            if ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
                  & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy))) 
                 & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid)))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len = 0U;
            } else if ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len) 
                         == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)) 
                        & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len 
                    = (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
                        & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy)))
                        ? 1U : 0U);
            } else if (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
                        & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy)))) {
                vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len 
                    = (7U & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len)));
            }
        }
        if ((((IData)(vlSelf->main__DOT____Vcellinp__u_i2cdma__S_VALID) 
              & (IData)(vlSelf->main__DOT__i2cdma_ready)) 
             & ((IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid) 
                & (~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready))))) {
            vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid = 1U;
        } else if (vlSelf->main__DOT__u_i2cdma__DOT__skd_ready) {
            vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
              & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy))) 
             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len = 0U;
        } else if ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
                     & (~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy))) 
                    & ((0U == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)) 
                       | (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__w_stb)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len 
                = ((3U == (3U & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits) 
                                 >> 4U))) ? 2U : ((2U 
                                                   == 
                                                   (3U 
                                                    & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits) 
                                                       >> 4U)))
                                                   ? 1U
                                                   : 
                                                  ((2U 
                                                    == 
                                                    (7U 
                                                     & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits) 
                                                        >> 3U)))
                                                    ? 2U
                                                    : 
                                                   ((1U 
                                                     == 
                                                     (7U 
                                                      & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits) 
                                                         >> 3U)))
                                                     ? 
                                                    (7U 
                                                     & ((IData)(2U) 
                                                        + 
                                                        (3U 
                                                         & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits) 
                                                            >> 1U))))
                                                     : 6U))));
        } else if (((((~ (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb)) 
                      | (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))))) 
                     & ((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len) 
                        == (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len))) 
                    & (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len = 0U;
        }
        if (((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy)) 
             & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen 
                = ((0x40U & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_bits))
                    ? 0U : (0x7fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen))));
        }
        if ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
              & (0x600000000ULL == (0xe00000000ULL 
                                    & vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word))) 
             & (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb)))))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr 
                = (0xffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr)));
        }
        if (((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb) 
             & (~ (IData)((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb)))))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw 
                = (3U & (IData)((vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                 >> 0x22U)));
        }
        if (((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
             & (~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len 
                = ((0U == (7U & (IData)((vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                         >> 0x21U))))
                    ? 1U : ((2U == (0xfU & (IData)(
                                                   (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                    >> 0x20U))))
                             ? 6U : (7U & ((3U == (0xfU 
                                                   & (IData)(
                                                             (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                              >> 0x20U))))
                                            ? ((IData)(2U) 
                                               + (3U 
                                                  & (IData)(
                                                            (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                             >> 0x1eU))))
                                            : ((1U 
                                                == 
                                                (3U 
                                                 & (IData)(
                                                           (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                            >> 0x22U))))
                                                ? 2U
                                                : (
                                                   (2U 
                                                    == 
                                                    (3U 
                                                     & (IData)(
                                                               (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                                >> 0x22U))))
                                                    ? 1U
                                                    : 6U))))));
        } else if (((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy)) 
                    & (0U < (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len)))) {
            vlSelf->__Vdly__main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len 
                = (7U & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len) 
                         - (IData)(1U)));
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge)) 
                   | (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch))))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount 
                = (0xfffU & ((0U < (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount))
                              ? ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount) 
                                 - (IData)(1U)) : (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ckcount)));
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge 
                = ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge)
                    ? (0U == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ckcount))
                    : (1U >= (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount)));
        }
        if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckedge)) 
                   | (~ (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_stretch))))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckcount 
                = (0xfffU & ((0U < (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckcount))
                              ? ((IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckcount) 
                                 - (IData)(1U)) : (IData)(vlSelf->main__DOT__i2ci__DOT__ckcount)));
            vlSelf->__Vdly__main__DOT__i2ci__DOT__i2c_ckedge 
                = ((IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckedge)
                    ? (0U == (IData)(vlSelf->main__DOT__i2ci__DOT__ckcount))
                    : (1U >= (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_ckcount)));
        }
        if ((((IData)(vlSelf->main__DOT__wb32_spio_stb) 
              & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                 >> 9U)) & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                    >> 0x24U)))) {
            vlSelf->__Vdly__main__DOT__spioi__DOT__r_led 
                = (0xffU & ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                           >> 0x25U)))
                             ? (((IData)(vlSelf->main__DOT__spioi__DOT__r_led) 
                                 & (~ ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                        << 0x18U) | 
                                       (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                        >> 8U)))) | 
                                (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                 & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                     << 0x18U) | (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                                  >> 8U))))
                             : vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U]));
        }
        if ((1U & ((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                     & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
                    >> 7U) & (~ (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                 >> 0x1aU))))) {
            if ((0U == (3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                              >> 0x18U)))) {
                if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                   >> 0x1cU)))) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga 
                        = ((0x1f00U & (IData)(vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga)) 
                           | (0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]));
                }
                if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                   >> 0x1dU)))) {
                    vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga 
                        = ((0xffU & (IData)(vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga)) 
                           | (0x1f00U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]));
                }
            }
            if ((0U != (3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                              >> 0x18U)))) {
                if ((1U == (3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                  >> 0x18U)))) {
                    if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                       >> 0x1cU)))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys 
                            = ((0x1f00U & (IData)(vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys)) 
                               | (0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]));
                    }
                    if ((1U & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                       >> 0x1dU)))) {
                        vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys 
                            = ((0xffU & (IData)(vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys)) 
                               | (0x1f00U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]));
                    }
                }
            }
        } else {
            if ((0x1387U <= (IData)(vlSelf->main__DOT__u_fan__DOT__ctl_fpga))) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_fpga = 0x1387U;
            }
            if ((0x1387U <= (IData)(vlSelf->main__DOT__u_fan__DOT__ctl_sys))) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__ctl_sys = 0x1387U;
            }
        }
        if (((IData)(vlSelf->main__DOT__wbwide_i2cdma_cyc) 
             & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))) {
            vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__bus_err = 1U;
        } else if ((0x10U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                             & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)))) {
            if ((2U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) {
                vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__bus_err 
                    = ((1U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])
                        ? ((IData)(vlSelf->main__DOT__u_i2cdma__DOT__bus_err) 
                           & (0ULL == (0xf0000ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel)))
                        : ((IData)(vlSelf->main__DOT__u_i2cdma__DOT__bus_err) 
                           & (0ULL == (0xf0000ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))));
            }
        }
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc) 
             | ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
                & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr)));
        }
        if ((((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
                & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
               & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle))) 
              & (0xc0U == (0xf0U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn)))) 
             | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid) 
                 & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready)) 
                & (0xcU == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn))))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr 
                = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__jump_target;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr 
                = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__abort_address;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr 
                = (0x1fU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]);
        }
        if (((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
               & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready)) 
              & (0x200U == (0xf00U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn)))) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 1U;
        }
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
              & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready)) 
             & (0x900U == (0xf00U & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 1U;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write) {
            if (((IData)(((0U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])) 
                          & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U] 
                             >> 0x13U))) & (IData)(
                                                   (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                    >> 0x1eU)))) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 1U;
            }
            if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_manual) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 1U;
            }
            if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) 
                 & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted))) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted = 0U;
            }
        }
        if (((((IData)(vlSelf->main__DOT__i2ci__DOT__insn_valid) 
               & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready)) 
              & (0x200U == (0xf00U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn)))) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__soft_halt_request))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
        }
        if (((IData)(vlSelf->main__DOT__i2ci__DOT__soft_halt_request) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_abort))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_illegal))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__i2ci__DOT__insn_valid) 
              & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready)) 
             & (0x900U == (0xf00U & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
        }
        if (vlSelf->main__DOT__i2ci__DOT__bus_write) {
            if (((IData)(((0U == (0x3000000U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U])) 
                          & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[3U] 
                             >> 0x13U))) & (IData)(
                                                   (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                    >> 0xeU)))) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
            }
            if (vlSelf->main__DOT__i2ci__DOT__bus_manual) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 1U;
            }
            if (((IData)(vlSelf->main__DOT__i2ci__DOT__bus_jump) 
                 & (IData)(vlSelf->main__DOT__i2ci__DOT__r_halted))) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__r_halted = 0U;
            }
        }
        if (((IData)(vlSelf->main__DOT__i2ci__DOT__cpu_new_pc) 
             | ((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
                & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr 
                = (0xfffffffU & ((IData)(1U) + vlSelf->main__DOT__i2ci__DOT__pf_jump_addr));
        }
        if ((((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
                & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
               & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle))) 
              & (0xc0U == (0xf0U & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_insn)))) 
             | (((IData)(vlSelf->main__DOT__i2ci__DOT__half_valid) 
                 & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready)) 
                & (0xcU == (IData)(vlSelf->main__DOT__i2ci__DOT__half_insn))))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr 
                = vlSelf->main__DOT__i2ci__DOT__jump_target;
        }
        if (vlSelf->main__DOT__i2ci__DOT__i2c_abort) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr 
                = vlSelf->main__DOT__i2ci__DOT__abort_address;
        }
        if (vlSelf->main__DOT__i2ci__DOT__bus_jump) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_jump_addr 
                = (0xfffffffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[3U]);
        }
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc))))) {
        vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v0 = 1U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel)))) {
        if (vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available) {
            vlSelf->__Vdlyvval__main__DOT__wb32_xbar__DOT__grant__v1 
                = vlSelf->main__DOT__wb32_xbar__DOT__request
                [0U];
            vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v1 = 1U;
        } else if (vlSelf->main__DOT__wb32_xbar__DOT__m_stb) {
            vlSelf->__Vdlyvset__main__DOT__wb32_xbar__DOT__grant__v2 = 1U;
        }
    }
    __Vtableidx11 = (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb) 
                      << 5U) | (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb) 
                                 << 4U) | (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner) 
                                            << 3U) 
                                           | (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__ALT__DOT__last_owner) 
                                               << 2U) 
                                              | (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc) 
                                                  << 1U) 
                                                 | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc))))));
    if (Vmain__ConstPool__TABLE_heed7669e_0[__Vtableidx11]) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner 
            = Vmain__ConstPool__TABLE_hdf55cab5_0[__Vtableidx11];
    }
    if ((1U & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant))) {
        if (((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
              [0U]) & ((IData)(vlSelf->main__DOT__wbu_cyc) 
                       >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                       [0U]))) {
            if ((1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb)) 
                       | (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_stall))))) {
                vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
                    = ((2U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb)) 
                       | (1U & (((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                  [0U]) ? vlSelf->main__DOT__wbu_xbar__DOT__request
                                 [vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                 [0U]] : 0U) & (~ (
                                                   (0U 
                                                    >= 
                                                    vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                                    [0U]) 
                                                   & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mfull) 
                                                      >> 
                                                      vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                                      [0U]))))));
            }
        } else {
            vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
                = (2U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb));
        }
    } else {
        vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
            = (2U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb));
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_err)))) {
        vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
            = (2U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb));
    }
    if ((2U & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant))) {
        if (((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
              [1U]) & ((IData)(vlSelf->main__DOT__wbu_cyc) 
                       >> vlSelf->main__DOT__wbu_xbar__DOT__sindex
                       [1U]))) {
            if ((1U & ((~ ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb) 
                           >> 1U)) | (~ ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_stall) 
                                         >> 1U))))) {
                vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
                    = ((1U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb)) 
                       | (2U & (((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                  [1U]) ? (0xfffffffeU 
                                           & vlSelf->main__DOT__wbu_xbar__DOT__request
                                           [vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                           [1U]]) : 0U) 
                                & ((~ ((0U >= vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                        [1U]) & ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mfull) 
                                                 >> 
                                                 vlSelf->main__DOT__wbu_xbar__DOT__sindex
                                                 [1U]))) 
                                   << 1U))));
            }
        } else {
            vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
                = (1U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb));
        }
    } else {
        vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
            = (1U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb));
    }
    if ((1U & ((IData)(vlSelf->i_reset) | ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__s_err) 
                                           >> 1U)))) {
        vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb 
            = (1U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbu_xbar__o_sstb));
    }
    if (vlSelf->main__DOT__wbwide_wbdown_stall) {
        if ((1U & ((~ (IData)(vlSelf->main__DOT__wb32_wbdown_stb)) 
                   | (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))))) {
            VL_SHIFTL_WWI(512,512,32, __Vtemp_h211bbf5b__0, vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data, 
                          ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift) 
                           << 5U));
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0U] 
                = __Vtemp_h211bbf5b__0[0U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[1U] 
                = __Vtemp_h211bbf5b__0[1U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[2U] 
                = __Vtemp_h211bbf5b__0[2U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[3U] 
                = __Vtemp_h211bbf5b__0[3U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[4U] 
                = __Vtemp_h211bbf5b__0[4U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[5U] 
                = __Vtemp_h211bbf5b__0[5U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[6U] 
                = __Vtemp_h211bbf5b__0[6U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[7U] 
                = __Vtemp_h211bbf5b__0[7U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[8U] 
                = __Vtemp_h211bbf5b__0[8U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[9U] 
                = __Vtemp_h211bbf5b__0[9U];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xaU] 
                = __Vtemp_h211bbf5b__0[0xaU];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xbU] 
                = __Vtemp_h211bbf5b__0[0xbU];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xcU] 
                = __Vtemp_h211bbf5b__0[0xcU];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xdU] 
                = __Vtemp_h211bbf5b__0[0xdU];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xeU] 
                = __Vtemp_h211bbf5b__0[0xeU];
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xfU] 
                = __Vtemp_h211bbf5b__0[0xfU];
        }
        if ((((~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb)) 
              & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first)) 
             | ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb) 
                & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid))))) {
            vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr 
                = ((0xf0U & (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr)) 
                   | (0xfU & ((IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr) 
                              + (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift))));
        }
    } else {
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[1U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[1U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[2U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[2U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[3U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[3U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[4U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[4U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[5U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[5U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[6U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[6U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[7U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[7U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[8U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[8U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[9U] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[9U];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xaU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xaU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xbU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xbU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xcU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xcU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xdU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xdU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xeU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xeU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xfU] 
            = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xfU];
        vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr 
            = (0xf0U & (vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[0U] 
                        << 4U));
    }
    vlSelf->__Vdly__main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err 
        = ((~ (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc))) 
               | (~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc)))) 
           & (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
        = ((2U & (IData)(vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant)) 
           | (1U & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant)));
    if ((1U & (vlSelf->main__DOT__wbu_xbar__DOT__request
               [0U] & ((~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__mgrant)) 
                       | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__mempty))))) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
            = (1U | (IData)(vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant));
    }
    if (vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
            = (2U & (IData)(vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant));
    }
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
        = ((1U & (IData)(vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant)) 
           | (2U & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__sgrant)));
    if ((1U & ((vlSelf->main__DOT__wbu_xbar__DOT__request
                [0U] >> 1U) & ((~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__mgrant)) 
                               | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__mempty))))) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
            = (2U | (IData)(vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant));
    }
    if (vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant 
            = (1U & (IData)(vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__sgrant));
    }
    vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
        = ((IData)(vlSelf->main__DOT__wb32_xbar__DOT__mgrant) 
           & (0xf000U >> vlSelf->main__DOT__wb32_xbar__DOT__mindex
              [0U]));
    if ((0x1000U & vlSelf->main__DOT__wb32_xbar__DOT__grant
         [0U])) {
        vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr 
            = (1U & (~ (IData)(vlSelf->main__DOT__wb32_wbdown_err)));
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc))) 
               | (IData)(vlSelf->main__DOT__wb32_wbdown_err)))) {
        vlSelf->__Vdly__main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr = 0U;
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_release_from_interrupt))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag = 0U;
    } else {
        if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
             & (0x1eU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))) {
            if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) {
                if ((1U & (~ (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                              >> 5U)))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap 
                        = (1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv)));
                }
            } else {
                vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap 
                    = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap) 
                       & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                          >> 9U));
            }
        }
        if (((((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)) 
               | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv)) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce)) 
             & (0x1eU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag 
                = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag) 
                   & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl 
                      >> 0xbU));
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_error) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag = 1U;
        }
    }
    vlSelf->__Vdly__main__DOT__swic__DOT__wdt_reset 
        = ((~ (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                | (IData)(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__wb_write)) 
               | (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt))) 
           & (1U == vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value));
    if ((1U & ((~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_triggered)) 
               | (~ ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                     >> 2U))))) {
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stopped = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped)))) {
        vlSelf->__Vdly__main__DOT__i2cscopei__DOT__dr_stopped 
            = (vlSelf->main__DOT__i2cscopei__DOT__holdoff_counter 
               >= vlSelf->main__DOT__i2cscopei__DOT__br_holdoff);
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_triggered)) 
               | (~ ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                     >> 2U))))) {
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stopped = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped)))) {
        vlSelf->__Vdly__main__DOT__sdioscopei__DOT__dr_stopped 
            = (vlSelf->main__DOT__sdioscopei__DOT__holdoff_counter 
               >= vlSelf->main__DOT__sdioscopei__DOT__br_holdoff);
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_triggered)) 
               | (~ ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                     >> 2U))))) {
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stopped = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped)))) {
        vlSelf->__Vdly__main__DOT__emmcscopei__DOT__dr_stopped 
            = (vlSelf->main__DOT__emmcscopei__DOT__holdoff_counter 
               >= vlSelf->main__DOT__emmcscopei__DOT__br_holdoff);
    }
    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err 
        = ((~ (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort)) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy)))) 
           & (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy) 
               & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_err)) 
              | ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err))));
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en))) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset)))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr = 0U;
    } else if ((1U & (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid)) 
                       | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                      | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)));
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en))) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset)))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr = 0U;
    } else if ((1U & (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid)) 
                       | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                      | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_write) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = 0U;
        if ((((IData)(vlSelf->main__DOT__swic__DOT__cmd_waddr) 
              == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Bid)) 
             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rB))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = 1U;
        }
        if ((7U == (7U & ((IData)(vlSelf->main__DOT__swic__DOT__cmd_waddr) 
                          >> 1U)))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = 1U;
        }
    } else {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe = 0U;
    }
    if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_addr 
            = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr 
            = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr;
    } else {
        if (vlSelf->main__DOT__u_fan__DOT__mem_stb) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_addr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_fan__DOT__mem_addr)));
        }
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr 
                = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr)));
        }
    }
    if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset) 
         | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc))) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal = 0U;
    } else {
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__mem_ack))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid = 1U;
        } else if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid 
                = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid;
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc)) 
             & (IData)(vlSelf->main__DOT__u_fan__DOT__mem_ack))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid 
                = (1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)));
        } else if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid = 0U;
        }
        if ((1U & (((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid)) 
                    | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
                   & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal))))) {
            if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid) {
                vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal 
                    = vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_illegal;
            }
        }
    }
    if ((((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
          | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache)) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_new_pc))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_illegal = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_illegal 
            = ((((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err)) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid)) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__isrc))) 
               & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache 
                  == (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                                  >> 9U))));
    }
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v4 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + vlSelf->main__DOT__clock_generator__DOT__times_five);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v6 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + vlSelf->main__DOT__clock_generator__DOT__times_seven);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v2 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + vlSelf->main__DOT__clock_generator__DOT__times_three);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v5 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + (vlSelf->main__DOT__clock_generator__DOT__times_three 
                   << 1U));
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v0 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + vlSelf->main__DOT__clock_generator__DOT__r_delay);
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v1 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + (vlSelf->main__DOT__clock_generator__DOT__r_delay 
                   << 1U));
    vlSelf->__Vdlyvval__main__DOT__clock_generator__DOT__counter__v3 
        = (vlSelf->main__DOT__clock_generator__DOT__counter
           [0U] + (vlSelf->main__DOT__clock_generator__DOT__r_delay 
                   << 2U));
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_cyc = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_stb = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc) {
        if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_stb = 0U;
        } else if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb) 
                     & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stall))) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_addr))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_stb = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack) 
              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack)) 
             | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_cyc = 0U;
        }
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__needload) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_new_pc)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_cyc = 1U;
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__pf_stb = 1U;
    }
    if (vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr) {
        vlSelf->__Vdlyvval__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 
            = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_shift;
        vlSelf->__Vdlyvset__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem__v0 
            = (0x1fU & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr));
    }
    if ((1U & ((((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc))) 
                | ((IData)(vlSelf->main__DOT__wbwide_wbu_arbiter_cyc) 
                   & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                      >> 3U))) | (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err)))) {
        vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc = 0U;
    } else if ((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                      & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb)))) {
        vlSelf->__Vdly__main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc = 1U;
    }
    if ((((IData)(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set) 
          & VL_LTS_III(32, 0U, vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_wb)) 
         & ((vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_when 
             >> 0x1fU) | (~ (IData)(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__u_jiffies__DOT__int_when 
            = vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_when;
    }
    if ((IData)((((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                    >> 9U) & (0x100U == (0x700U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))) 
                  & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                     >> 9U)) & (0xf000000000ULL == 
                                (0xf000000000ULL & vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))))) {
        vlSelf->__Vdly__o_gpio = (0xffU & (((IData)(vlSelf->o_gpio) 
                                            & (~ ((
                                                   vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                                   << 0x10U) 
                                                  | (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                                     >> 0x10U)))) 
                                           | (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                              & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                                  << 0x10U) 
                                                 | (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U] 
                                                    >> 0x10U)))));
    }
    if (vlSelf->main__DOT__console__DOT__rx_uart_reset) {
        vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__r_fill = 0U;
        vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_overflow = 0U;
        vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_underflow = 1U;
    } else {
        if ((1U == (((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write) 
                     << 1U) | (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read)))) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__r_fill 
                = (0x3fU & ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill) 
                            - (IData)(1U)));
        } else if ((2U == (((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write) 
                            << 1U) | (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read)))) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__r_fill 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill)));
        }
        if (vlSelf->main__DOT__console__DOT__rxf_wb_read) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_overflow 
                = ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow) 
                   & (IData)(vlSelf->main__DOT__w_console_rx_stb));
        } else if (vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_overflow 
                = ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow) 
                   | ((0x3fU & ((IData)(2U) + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr))) 
                      == (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr)));
        } else if (((0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr))) 
                    == (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr))) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_overflow = 1U;
        }
        if (vlSelf->main__DOT__w_console_rx_stb) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_underflow = 0U;
        } else if (vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read) {
            vlSelf->__Vdly__main__DOT__console__DOT__rxfifo__DOT__will_underflow 
                = ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow) 
                   | ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_next) 
                      == (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr)));
        }
    }
    if (vlSelf->main__DOT__console__DOT__tx_uart_reset) {
        vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__r_fill = 0x3fU;
        vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow = 0U;
        vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_underflow = 1U;
    } else {
        if ((1U == (((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write) 
                     << 1U) | (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_read)))) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__r_fill 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill)));
        } else if ((2U == (((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write) 
                            << 1U) | (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_read)))) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__r_fill 
                = (0x3fU & ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                            - (IData)(1U)));
        }
        if (vlSelf->main__DOT__console__DOT____Vcellinp__txfifo____pinNumber6) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow 
                = ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow) 
                   & (IData)(vlSelf->main__DOT__console__DOT__txf_wb_write));
        } else if (vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow 
                = ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow) 
                   | ((0x3fU & ((IData)(2U) + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr))) 
                      == (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr)));
        } else if (((0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr))) 
                    == (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr))) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_overflow = 1U;
        }
        if (vlSelf->main__DOT__console__DOT__txf_wb_write) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_underflow = 0U;
        } else if (vlSelf->main__DOT__console__DOT__txfifo__DOT__w_read) {
            vlSelf->__Vdly__main__DOT__console__DOT__txfifo__DOT__will_underflow 
                = ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow) 
                   | ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_next) 
                      == (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr)));
        }
    }
    if (vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write) {
        vlSelf->__Vdlyvval__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 
            = vlSelf->main__DOT__w_console_rx_data;
        vlSelf->__Vdlyvset__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__console__DOT__rxfifo__DOT__fifo__v0 
            = vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr;
    }
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done 
        = ((~ ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done))) 
           & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response)) 
              | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done) 
                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb))));
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done 
        = ((~ ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done))) 
           & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response)) 
              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done) 
                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb))));
    if ((1U & ((((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                 | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err))) 
                | ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc)) 
                   & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce)))) 
               | (3U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_svalid) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending 
            = ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce)
                ? 1U : 0U);
    } else if ((1U == (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                        << 1U) | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending 
            = (0x1fU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending) 
                        - (IData)(1U)));
    } else if ((2U == (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce) 
                        << 1U) | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc) 
                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending 
            = (0x1fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending)));
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid) 
                & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
                   | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce)))) {
        if ((0U != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock 
                = (3U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock) 
                         - (IData)(1U)));
        } else if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OPLOCK__DOT__r_op_lock) {
            vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock = 3U;
        }
    }
    if (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
         | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] = 0U;
    } else {
        if ((((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid) 
              & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full))) 
             & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] = 0U;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] = 0U;
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid) 
                    & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)))) {
            __Vtemp_hc94fac31__0[0U] = Vmain__ConstPool__CONST_h93e1b771_0[0U];
            __Vtemp_hc94fac31__0[1U] = Vmain__ConstPool__CONST_h93e1b771_0[1U];
            __Vtemp_hc94fac31__0[2U] = Vmain__ConstPool__CONST_h93e1b771_0[2U];
            __Vtemp_hc94fac31__0[3U] = Vmain__ConstPool__CONST_h93e1b771_0[3U];
            __Vtemp_hc94fac31__0[4U] = Vmain__ConstPool__CONST_h93e1b771_0[4U];
            __Vtemp_hc94fac31__0[5U] = Vmain__ConstPool__CONST_h93e1b771_0[5U];
            __Vtemp_hc94fac31__0[6U] = Vmain__ConstPool__CONST_h93e1b771_0[6U];
            __Vtemp_hc94fac31__0[7U] = Vmain__ConstPool__CONST_h93e1b771_0[7U];
            __Vtemp_hc94fac31__0[8U] = Vmain__ConstPool__CONST_h93e1b771_0[8U];
            __Vtemp_hc94fac31__0[9U] = Vmain__ConstPool__CONST_h93e1b771_0[9U];
            __Vtemp_hc94fac31__0[0xaU] = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
            __Vtemp_hc94fac31__0[0xbU] = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
            __Vtemp_hc94fac31__0[0xcU] = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
            __Vtemp_hc94fac31__0[0xdU] = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
            __Vtemp_hc94fac31__0[0xeU] = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
            __Vtemp_hc94fac31__0[0xfU] = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
            __Vtemp_hc94fac31__0[0x10U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U];
            __Vtemp_hc94fac31__0[0x11U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U];
            __Vtemp_hc94fac31__0[0x12U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U];
            __Vtemp_hc94fac31__0[0x13U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U];
            __Vtemp_hc94fac31__0[0x14U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U];
            __Vtemp_hc94fac31__0[0x15U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U];
            __Vtemp_hc94fac31__0[0x16U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U];
            __Vtemp_hc94fac31__0[0x17U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U];
            __Vtemp_hc94fac31__0[0x18U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U];
            __Vtemp_hc94fac31__0[0x19U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U];
            __Vtemp_hc94fac31__0[0x1aU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU];
            __Vtemp_hc94fac31__0[0x1bU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU];
            __Vtemp_hc94fac31__0[0x1cU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU];
            __Vtemp_hc94fac31__0[0x1dU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU];
            __Vtemp_hc94fac31__0[0x1eU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU];
            __Vtemp_hc94fac31__0[0x1fU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU];
            VL_SHIFTR_WWI(1024,1024,32, __Vtemp_hfa8722fc__0, __Vtemp_hc94fac31__0, 
                          ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift) 
                           << 3U));
            if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0U] 
                       | __Vtemp_hfa8722fc__0[0U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[1U] 
                       | __Vtemp_hfa8722fc__0[1U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[2U] 
                       | __Vtemp_hfa8722fc__0[2U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[3U] 
                       | __Vtemp_hfa8722fc__0[3U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[4U] 
                       | __Vtemp_hfa8722fc__0[4U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[5U] 
                       | __Vtemp_hfa8722fc__0[5U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[6U] 
                       | __Vtemp_hfa8722fc__0[6U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[7U] 
                       | __Vtemp_hfa8722fc__0[7U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[8U] 
                       | __Vtemp_hfa8722fc__0[8U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[9U] 
                       | __Vtemp_hfa8722fc__0[9U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0xaU] 
                       | __Vtemp_hfa8722fc__0[0xaU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0xbU] 
                       | __Vtemp_hfa8722fc__0[0xbU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0xcU] 
                       | __Vtemp_hfa8722fc__0[0xcU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0xdU] 
                       | __Vtemp_hfa8722fc__0[0xdU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0xeU] 
                       | __Vtemp_hfa8722fc__0[0xeU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] 
                    = (Vmain__ConstPool__CONST_h93e1b771_0[0xfU] 
                       | __Vtemp_hfa8722fc__0[0xfU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] 
                       | __Vtemp_hfa8722fc__0[0x10U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] 
                       | __Vtemp_hfa8722fc__0[0x11U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] 
                       | __Vtemp_hfa8722fc__0[0x12U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] 
                       | __Vtemp_hfa8722fc__0[0x13U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] 
                       | __Vtemp_hfa8722fc__0[0x14U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] 
                       | __Vtemp_hfa8722fc__0[0x15U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] 
                       | __Vtemp_hfa8722fc__0[0x16U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] 
                       | __Vtemp_hfa8722fc__0[0x17U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] 
                       | __Vtemp_hfa8722fc__0[0x18U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] 
                       | __Vtemp_hfa8722fc__0[0x19U]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] 
                       | __Vtemp_hfa8722fc__0[0x1aU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] 
                       | __Vtemp_hfa8722fc__0[0x1bU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] 
                       | __Vtemp_hfa8722fc__0[0x1cU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] 
                       | __Vtemp_hfa8722fc__0[0x1dU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] 
                       | __Vtemp_hfa8722fc__0[0x1eU]);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] 
                    = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] 
                       | __Vtemp_hfa8722fc__0[0x1fU]);
            } else {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[1U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[2U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[3U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[4U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[5U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[6U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[7U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[8U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[9U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] 
                    = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU];
            }
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready))) {
            __Vtemp_hc94fac31__1[0U] = Vmain__ConstPool__CONST_h93e1b771_0[0U];
            __Vtemp_hc94fac31__1[1U] = Vmain__ConstPool__CONST_h93e1b771_0[1U];
            __Vtemp_hc94fac31__1[2U] = Vmain__ConstPool__CONST_h93e1b771_0[2U];
            __Vtemp_hc94fac31__1[3U] = Vmain__ConstPool__CONST_h93e1b771_0[3U];
            __Vtemp_hc94fac31__1[4U] = Vmain__ConstPool__CONST_h93e1b771_0[4U];
            __Vtemp_hc94fac31__1[5U] = Vmain__ConstPool__CONST_h93e1b771_0[5U];
            __Vtemp_hc94fac31__1[6U] = Vmain__ConstPool__CONST_h93e1b771_0[6U];
            __Vtemp_hc94fac31__1[7U] = Vmain__ConstPool__CONST_h93e1b771_0[7U];
            __Vtemp_hc94fac31__1[8U] = Vmain__ConstPool__CONST_h93e1b771_0[8U];
            __Vtemp_hc94fac31__1[9U] = Vmain__ConstPool__CONST_h93e1b771_0[9U];
            __Vtemp_hc94fac31__1[0xaU] = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
            __Vtemp_hc94fac31__1[0xbU] = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
            __Vtemp_hc94fac31__1[0xcU] = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
            __Vtemp_hc94fac31__1[0xdU] = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
            __Vtemp_hc94fac31__1[0xeU] = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
            __Vtemp_hc94fac31__1[0xfU] = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
            __Vtemp_hc94fac31__1[0x10U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0U];
            __Vtemp_hc94fac31__1[0x11U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[1U];
            __Vtemp_hc94fac31__1[0x12U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[2U];
            __Vtemp_hc94fac31__1[0x13U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[3U];
            __Vtemp_hc94fac31__1[0x14U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[4U];
            __Vtemp_hc94fac31__1[0x15U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[5U];
            __Vtemp_hc94fac31__1[0x16U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[6U];
            __Vtemp_hc94fac31__1[0x17U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[7U];
            __Vtemp_hc94fac31__1[0x18U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[8U];
            __Vtemp_hc94fac31__1[0x19U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[9U];
            __Vtemp_hc94fac31__1[0x1aU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xaU];
            __Vtemp_hc94fac31__1[0x1bU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xbU];
            __Vtemp_hc94fac31__1[0x1cU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xcU];
            __Vtemp_hc94fac31__1[0x1dU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xdU];
            __Vtemp_hc94fac31__1[0x1eU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xeU];
            __Vtemp_hc94fac31__1[0x1fU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data[0xfU];
            VL_SHIFTR_WWI(1024,1024,32, __Vtemp_hb4dafc67__0, __Vtemp_hc94fac31__1, 
                          ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift) 
                           << 3U));
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0U] 
                   | __Vtemp_hb4dafc67__0[0U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[1U] 
                   | __Vtemp_hb4dafc67__0[1U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[2U] 
                   | __Vtemp_hb4dafc67__0[2U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[3U] 
                   | __Vtemp_hb4dafc67__0[3U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[4U] 
                   | __Vtemp_hb4dafc67__0[4U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[5U] 
                   | __Vtemp_hb4dafc67__0[5U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[6U] 
                   | __Vtemp_hb4dafc67__0[6U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[7U] 
                   | __Vtemp_hb4dafc67__0[7U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[8U] 
                   | __Vtemp_hb4dafc67__0[8U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[9U] 
                   | __Vtemp_hb4dafc67__0[9U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xaU] 
                   | __Vtemp_hb4dafc67__0[0xaU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xbU] 
                   | __Vtemp_hb4dafc67__0[0xbU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xcU] 
                   | __Vtemp_hb4dafc67__0[0xcU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xdU] 
                   | __Vtemp_hb4dafc67__0[0xdU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xeU] 
                   | __Vtemp_hb4dafc67__0[0xeU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0xfU] 
                   | __Vtemp_hb4dafc67__0[0xfU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U] 
                   | __Vtemp_hb4dafc67__0[0x10U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U] 
                   | __Vtemp_hb4dafc67__0[0x11U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U] 
                   | __Vtemp_hb4dafc67__0[0x12U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U] 
                   | __Vtemp_hb4dafc67__0[0x13U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U] 
                   | __Vtemp_hb4dafc67__0[0x14U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U] 
                   | __Vtemp_hb4dafc67__0[0x15U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U] 
                   | __Vtemp_hb4dafc67__0[0x16U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U] 
                   | __Vtemp_hb4dafc67__0[0x17U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U] 
                   | __Vtemp_hb4dafc67__0[0x18U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U] 
                   | __Vtemp_hb4dafc67__0[0x19U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU] 
                   | __Vtemp_hb4dafc67__0[0x1aU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU] 
                   | __Vtemp_hb4dafc67__0[0x1bU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU] 
                   | __Vtemp_hb4dafc67__0[0x1cU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU] 
                   | __Vtemp_hb4dafc67__0[0x1dU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU] 
                   | __Vtemp_hb4dafc67__0[0x1eU]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] 
                = (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU] 
                   | __Vtemp_hb4dafc67__0[0x1fU]);
        }
        if (((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_empty)) 
             & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__tx_ready))) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill 
                = (0x7fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0x10U]);
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[1U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[2U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[3U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[4U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[5U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[6U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[7U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[8U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[9U];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xaU];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xbU];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xcU];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xdU];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xeU];
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xfU];
        } else if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_valid) 
                    & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_ready))) {
            VL_SHIFTL_WWI(512,512,32, __Vtemp_h04488e48__0, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg, 8U);
            VL_SHIFTL_WWI(512,512,32, __Vtemp_h0448bebe__0, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg, 0x10U);
            VL_SHIFTL_WWI(512,512,32, __Vtemp_h0448985a__0, vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg, 0x20U);
            if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_last) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill = 0U;
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[1U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[2U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[3U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[4U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[5U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[6U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[7U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[8U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[9U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
            } else if ((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_size))) {
                if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_size))) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill 
                        = (0x7fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill) 
                                    - (IData)(1U)));
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
                        = __Vtemp_h04488e48__0[0U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
                        = __Vtemp_h04488e48__0[1U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
                        = __Vtemp_h04488e48__0[2U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
                        = __Vtemp_h04488e48__0[3U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
                        = __Vtemp_h04488e48__0[4U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
                        = __Vtemp_h04488e48__0[5U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
                        = __Vtemp_h04488e48__0[6U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
                        = __Vtemp_h04488e48__0[7U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
                        = __Vtemp_h04488e48__0[8U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
                        = __Vtemp_h04488e48__0[9U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
                        = __Vtemp_h04488e48__0[0xaU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
                        = __Vtemp_h04488e48__0[0xbU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
                        = __Vtemp_h04488e48__0[0xcU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
                        = __Vtemp_h04488e48__0[0xdU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
                        = __Vtemp_h04488e48__0[0xeU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
                        = __Vtemp_h04488e48__0[0xfU];
                } else {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill 
                        = (0x7fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill) 
                                    - (IData)(2U)));
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
                        = __Vtemp_h0448bebe__0[0U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
                        = __Vtemp_h0448bebe__0[1U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
                        = __Vtemp_h0448bebe__0[2U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
                        = __Vtemp_h0448bebe__0[3U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
                        = __Vtemp_h0448bebe__0[4U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
                        = __Vtemp_h0448bebe__0[5U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
                        = __Vtemp_h0448bebe__0[6U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
                        = __Vtemp_h0448bebe__0[7U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
                        = __Vtemp_h0448bebe__0[8U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
                        = __Vtemp_h0448bebe__0[9U];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
                        = __Vtemp_h0448bebe__0[0xaU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
                        = __Vtemp_h0448bebe__0[0xbU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
                        = __Vtemp_h0448bebe__0[0xcU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
                        = __Vtemp_h0448bebe__0[0xdU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
                        = __Vtemp_h0448bebe__0[0xeU];
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
                        = __Vtemp_h0448bebe__0[0xfU];
                }
            } else if ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_size))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill 
                    = (0x7fU & ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill) 
                                - (IData)(4U)));
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
                    = __Vtemp_h0448985a__0[0U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
                    = __Vtemp_h0448985a__0[1U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
                    = __Vtemp_h0448985a__0[2U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
                    = __Vtemp_h0448985a__0[3U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
                    = __Vtemp_h0448985a__0[4U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
                    = __Vtemp_h0448985a__0[5U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
                    = __Vtemp_h0448985a__0[6U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
                    = __Vtemp_h0448985a__0[7U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
                    = __Vtemp_h0448985a__0[8U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
                    = __Vtemp_h0448985a__0[9U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
                    = __Vtemp_h0448985a__0[0xaU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
                    = __Vtemp_h0448985a__0[0xbU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
                    = __Vtemp_h0448985a__0[0xcU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
                    = __Vtemp_h0448985a__0[0xdU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
                    = __Vtemp_h0448985a__0[0xeU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
                    = __Vtemp_h0448985a__0[0xfU];
            } else {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill 
                    = (0x7fU & 0U);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[1U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[1U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[2U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[2U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[3U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[3U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[4U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[4U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[5U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[5U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[6U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[6U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[7U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[7U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[8U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[8U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[9U] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[9U];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xaU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xbU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xcU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xdU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xeU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg[0xfU] 
                    = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
            }
        }
    }
    if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr) {
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[1U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[2U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[3U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[4U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[5U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[6U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[7U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[8U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[9U] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0xaU] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0xbU] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0xcU] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0xdU] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0xeU] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0xfU] 
            = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU];
        vlSelf->__Vdlyvval__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0[0x10U] 
            = (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last) 
                << 7U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_bytes));
        vlSelf->__Vdlyvset__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem__v0 
            = (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr));
    }
    if (vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write) {
        vlSelf->__Vdlyvval__main__DOT__console__DOT__txfifo__DOT__fifo__v0 
            = vlSelf->main__DOT__console__DOT__txf_wb_data;
        vlSelf->__Vdlyvset__main__DOT__console__DOT__txfifo__DOT__fifo__v0 = 1U;
        vlSelf->__Vdlyvdim0__main__DOT__console__DOT__txfifo__DOT__fifo__v0 
            = vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr;
    }
    if ((((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc)) 
         | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort))) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = 0U;
    } else if (((~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle)) 
                & (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid) 
                    & ((3U == (0xfU & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                                       >> 4U))) | (0xdU 
                                                   == 
                                                   (0xfU 
                                                    & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn) 
                                                       >> 4U))))) 
                   | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid) 
                       & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready)) 
                      & ((3U == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn)) 
                         | (0xdU == (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn))))))) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = 1U;
    } else {
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
             | ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_override) 
                & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_ready)))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle = 0U;
        }
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__rx_en = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en = 0U;
    } else {
        if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb) 
              & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                         >> 0x19U))) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                         >> 0xbU) | 
                                        (2U == (3U 
                                                & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                                   >> 8U)))))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = 0U;
        } else if ((((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                       & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
                      >> 6U) & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                        >> 0x18U))) 
                    & ((2U == (7U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                     >> 0x10U))) | 
                       (3U == (7U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                     >> 0x10U)))))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr 
                = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr)));
        }
        if (((IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en) 
             & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__rx_en = 0U;
        } else if ((((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                     & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request))) 
                    & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__rx_en = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb) 
              & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                         >> 0x19U))) & (((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                          >> 0xbU) 
                                         | (2U == (3U 
                                                   & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                                      >> 8U)))) 
                                        | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo) 
                                           != (1U & 
                                               (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U] 
                                                >> 0xcU)))))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = 0U;
        } else if ((((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                       >> 6U) & (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 6U))) & (IData)(
                                                       (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                        >> 0x18U))) 
                    & ((2U == (7U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                     >> 0x10U))) | 
                       (3U == (7U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                     >> 0x10U)))))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr 
                = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr)));
        }
        if ((1U & (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en)) 
                    | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent)) 
                   | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid) 
                       & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                      & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_last))))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid = 0U;
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = 0U;
        } else if ((1U & (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid)) 
                           | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                          | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid))))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid 
                = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid;
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
              & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent)) 
             & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en = 0U;
        } else if ((((((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                       & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request))) 
                      & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en))) 
                     & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__dat0_busy))) 
                    & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en 
                = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request;
        }
    }
    if (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__rx_en = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en = 0U;
    } else {
        if ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb) 
              & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                         >> 0x21U))) & ((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                         >> 0xbU) | 
                                        (2U == (3U 
                                                & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                                   >> 8U)))))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr = 0U;
        } else if ((((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                       & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
                      >> 8U) & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                        >> 0x20U))) 
                    & ((2U == (7U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U])) 
                       | (3U == (7U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr 
                = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr)));
        }
        if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en) 
             & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__rx_en = 0U;
        } else if ((((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                     & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request))) 
                    & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__rx_en = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb) 
              & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                         >> 0x21U))) & (((vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                          >> 0xbU) 
                                         | (2U == (3U 
                                                   & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                                      >> 8U)))) 
                                        | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo) 
                                           != (1U & 
                                               (vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U] 
                                                >> 0xcU)))))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr = 0U;
        } else if ((((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                       >> 8U) & (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 8U))) & (IData)(
                                                       (vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                        >> 0x20U))) 
                    & ((2U == (7U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U])) 
                       | (3U == (7U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr 
                = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr)));
        }
        if ((1U & (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en)) 
                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent)) 
                   | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid) 
                       & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                      & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_last))))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid = 0U;
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = 0U;
        } else if ((1U & (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid)) 
                           | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready)) 
                          | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid))))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid 
                = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid;
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid = 1U;
        }
        if ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
              & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent)) 
             & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en = 0U;
        } else if ((((((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy)) 
                       & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request))) 
                      & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en))) 
                     & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__dat0_busy))) 
                    & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en 
                = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request;
        }
    }
    vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd 
        = ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)) 
           & ((((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce) 
                  | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce)) 
                 & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond)) 
                & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid)) 
               & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_wF) 
                  | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR) 
                     & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                        == (0xeU | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                    << 4U)))))) | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd) 
                                                   & (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy) 
                                                       | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy)) 
                                                      | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy)))));
    vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted 
        = ((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
           | ((IData)(vlSelf->main__DOT__swic__DOT__cmd_halt) 
              & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted) 
                 | (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase)) 
                     & (~ (IData)((0U != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock))))) 
                    & (((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_valid) 
                          & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy))) 
                         & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy))) 
                        & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy))) 
                       & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid) 
                          | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal)))))));
    __Vtableidx3 = (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count) 
                     << 7U) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready) 
                                << 6U) | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) 
                                           << 5U) | 
                                          (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width) 
                                            << 3U) 
                                           | (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate) 
                                               << 1U) 
                                              | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset))))));
    if (Vmain__ConstPool__TABLE_h88ad91a4_0[__Vtableidx3]) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count 
            = Vmain__ConstPool__TABLE_h5f0541c3_0[__Vtableidx3];
    }
    __Vtableidx6 = (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count) 
                     << 7U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready) 
                                << 6U) | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) 
                                           << 5U) | 
                                          (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width) 
                                            << 3U) 
                                           | (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate) 
                                               << 1U) 
                                              | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset))))));
    if (Vmain__ConstPool__TABLE_h88ad91a4_0[__Vtableidx6]) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count 
            = Vmain__ConstPool__TABLE_h5f0541c3_0[__Vtableidx6];
    }
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__ck_sreg 
        = (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid))
            ? 0U : ((2U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__ck_sreg) 
                           << 1U)) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_dedge)));
    vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__pck_sreg 
        = (((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active))
            ? 0U : ((2U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__pck_sreg) 
                           << 1U)) | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_pedge)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__ck_sreg 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)
            ? 0U : ((0x3cU & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__ck_sreg) 
                              << 2U)) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_dedge)));
    vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pck_sreg 
        = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active)
            ? 0U : ((0x3cU & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pck_sreg) 
                              << 2U)) | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_pedge)));
    __Vtableidx4 = (((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight) 
                     << 4U) | ((8U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                      << 2U)) | ((4U 
                                                  & ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                                                     << 1U)) 
                                                 | (((IData)(vlSelf->main__DOT__wbwide_i2cm_stb) 
                                                     << 1U) 
                                                    | (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc)))));
    if (Vmain__ConstPool__TABLE_hd397e023_0[__Vtableidx4]) {
        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__inflight 
            = Vmain__ConstPool__TABLE_h9becc847_0[__Vtableidx4];
    }
    if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc = 0U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb = 0U;
    } else if (vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb 
            = (1U & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__last_stb)));
        if (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__last_stb) 
             & (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight) 
                 + ((IData)(vlSelf->main__DOT__u_fan__DOT__mem_stb)
                     ? 1U : 0U)) == ((IData)(vlSelf->main__DOT__u_fan__DOT__mem_ack)
                                      ? 1U : 0U)))) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb = 0U;
        }
        if (vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc) {
            vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc = 0U;
            vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb = 0U;
        }
    } else if ((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc) 
                 | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__invalid_bus_cycle)) 
                | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid) 
                    & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready)) 
                   & (~ (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_illegal))))) {
        vlSelf->__Vdly__main__DOT__u_fan__DOT__mem_stb = 1U;
        vlSelf->__Vdly__main__DOT__u_fan__DOT__ign_mem_cyc = 1U;
    }
    vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack 
        = ((IData)(vlSelf->main__DOT__wbu_xbar__DOT__mgrant) 
           & (((0xfffffffeU & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                               & (((~ (IData)(vlSelf->cpu_sim_cyc)) 
                                   & (IData)(vlSelf->main__DOT__raw_cpu_dbg_ack)) 
                                  << 1U))) | ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                                              & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_ack))) 
              >> vlSelf->main__DOT__wbu_xbar__DOT__mindex
              [0U]));
    if ((4U & vlSelf->main__DOT__wbu_xbar__DOT__grant
         [0U])) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = 0U;
    }
    if ((1U & (((IData)(vlSelf->i_reset) | (~ (IData)(vlSelf->main__DOT__wbu_cyc))) 
               | (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)))) {
        vlSelf->__Vdly__main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack = 0U;
    }
    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb 
        = ((~ ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
                | (0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb))) 
           & ((2U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))
               ? ((0x88U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)) 
                  & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))
               : ((0x30U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)) 
                  & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))));
    if ((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc) 
               | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid))))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending = 0U;
    } else if (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_break) 
                & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending)))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending 
            = (1U & (((((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy)) 
                        & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy))) 
                       & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy))) 
                      & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce))) 
                     & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__step)) 
                        | (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_user_stepped)))));
    }
    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb 
        = ((~ ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
                | (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb))) 
           & ((2U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))
               ? ((0x88U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)) 
                  & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))
               : ((0x30U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)) 
                  & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))));
    if (vlSelf->main__DOT__i2ci__DOT__cpu_new_pc) {
        vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_insn_addr 
            = vlSelf->main__DOT__i2ci__DOT__pf_jump_addr;
        vlSelf->__Vdly__main__DOT__wbwide_i2cm_addr 
            = (0x3fffffU & (vlSelf->main__DOT__i2ci__DOT__pf_jump_addr 
                            >> 6U));
    } else {
        if (((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_insn_addr = 0U;
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_insn_addr 
                = (0xfffffffU & ((IData)(1U) + vlSelf->main__DOT__i2ci__DOT__pf_insn_addr));
        }
        if (((IData)(vlSelf->main__DOT__wbwide_i2cm_stb) 
             & (~ ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                   >> 1U)))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cm_addr 
                = (0x3fffffU & ((IData)(1U) + vlSelf->main__DOT__wbwide_i2cm_addr));
        }
    }
    if ((((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__i2ci__DOT__cpu_new_pc)) 
         | (IData)(vlSelf->main__DOT__i2ci__DOT__i2c_abort))) {
        vlSelf->__Vdly__main__DOT__i2ci__DOT__imm_cycle = 0U;
    } else if (((~ (IData)(vlSelf->main__DOT__i2ci__DOT__imm_cycle)) 
                & (((IData)(vlSelf->main__DOT__i2ci__DOT__next_valid) 
                    & ((3U == (0xfU & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                       >> 4U))) | (0xdU 
                                                   == 
                                                   (0xfU 
                                                    & ((IData)(vlSelf->main__DOT__i2ci__DOT__next_insn) 
                                                       >> 4U))))) 
                   | (((IData)(vlSelf->main__DOT__i2ci__DOT__half_valid) 
                       & (IData)(vlSelf->main__DOT__i2ci__DOT__half_ready)) 
                      & ((3U == (IData)(vlSelf->main__DOT__i2ci__DOT__half_insn)) 
                         | (0xdU == (IData)(vlSelf->main__DOT__i2ci__DOT__half_insn))))))) {
        vlSelf->__Vdly__main__DOT__i2ci__DOT__imm_cycle = 1U;
    } else {
        if (vlSelf->main__DOT__i2ci__DOT__bus_jump) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__imm_cycle = 0U;
        }
        if ((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
             | ((IData)(vlSelf->main__DOT__i2ci__DOT__bus_override) 
                & (IData)(vlSelf->main__DOT__i2ci__DOT__ovw_ready)))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__imm_cycle = 0U;
        }
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
               | ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog)) 
                  & (0U != ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                            << 1U)))))) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout = 0x7fffffU;
    } else if ((0U != vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout)) {
        vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog 
            = (1U >= vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout);
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout 
            = (0x7fffffU & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout 
                            - (IData)(1U)));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
               | ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog)) 
                  & (0U != ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                            << 1U)))))) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout = 0x7fffffU;
    } else if ((0U != vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout)) {
        vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog 
            = (1U >= vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout);
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout 
            = (0x7fffffU & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout 
                            - (IData)(1U)));
    }
    if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid)) 
               | (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)))) {
        if (((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid) 
             & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)))) {
            VL_SHIFTL_WWI(512,512,32, __Vtemp_h434d0da1__0, vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word, 8U);
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U] 
                = __Vtemp_h434d0da1__0[0U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U] 
                = __Vtemp_h434d0da1__0[1U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U] 
                = __Vtemp_h434d0da1__0[2U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U] 
                = __Vtemp_h434d0da1__0[3U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U] 
                = __Vtemp_h434d0da1__0[4U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U] 
                = __Vtemp_h434d0da1__0[5U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U] 
                = __Vtemp_h434d0da1__0[6U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U] 
                = __Vtemp_h434d0da1__0[7U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U] 
                = __Vtemp_h434d0da1__0[8U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U] 
                = __Vtemp_h434d0da1__0[9U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU] 
                = __Vtemp_h434d0da1__0[0xaU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU] 
                = __Vtemp_h434d0da1__0[0xbU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU] 
                = __Vtemp_h434d0da1__0[0xcU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU] 
                = __Vtemp_h434d0da1__0[0xdU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU] 
                = __Vtemp_h434d0da1__0[0xeU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
                = __Vtemp_h434d0da1__0[0xfU];
        } else if ((1U & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                           >> 1U) & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid))))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x10U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x11U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x12U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x13U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x14U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x15U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x16U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x17U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x18U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x19U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1aU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1bU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1cU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1dU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1eU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
                = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x1fU];
            VL_SHIFTL_WWI(512,512,32, __Vtemp_hfc2bf96b__0, vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted, 8U);
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U] 
                = __Vtemp_hfc2bf96b__0[0U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U] 
                = __Vtemp_hfc2bf96b__0[1U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U] 
                = __Vtemp_hfc2bf96b__0[2U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U] 
                = __Vtemp_hfc2bf96b__0[3U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U] 
                = __Vtemp_hfc2bf96b__0[4U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U] 
                = __Vtemp_hfc2bf96b__0[5U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U] 
                = __Vtemp_hfc2bf96b__0[6U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U] 
                = __Vtemp_hfc2bf96b__0[7U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U] 
                = __Vtemp_hfc2bf96b__0[8U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U] 
                = __Vtemp_hfc2bf96b__0[9U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU] 
                = __Vtemp_hfc2bf96b__0[0xaU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU] 
                = __Vtemp_hfc2bf96b__0[0xbU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU] 
                = __Vtemp_hfc2bf96b__0[0xcU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU] 
                = __Vtemp_hfc2bf96b__0[0xdU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU] 
                = __Vtemp_hfc2bf96b__0[0xeU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
                = __Vtemp_hfc2bf96b__0[0xfU];
        } else {
            VL_SHIFTL_WWI(512,512,32, __Vtemp_h02cc08c7__0, vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn, 8U);
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0U] 
                = __Vtemp_h02cc08c7__0[0U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[1U] 
                = __Vtemp_h02cc08c7__0[1U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[2U] 
                = __Vtemp_h02cc08c7__0[2U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[3U] 
                = __Vtemp_h02cc08c7__0[3U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[4U] 
                = __Vtemp_h02cc08c7__0[4U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[5U] 
                = __Vtemp_h02cc08c7__0[5U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[6U] 
                = __Vtemp_h02cc08c7__0[6U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[7U] 
                = __Vtemp_h02cc08c7__0[7U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[8U] 
                = __Vtemp_h02cc08c7__0[8U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[9U] 
                = __Vtemp_h02cc08c7__0[9U];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xaU] 
                = __Vtemp_h02cc08c7__0[0xaU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xbU] 
                = __Vtemp_h02cc08c7__0[0xbU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xcU] 
                = __Vtemp_h02cc08c7__0[0xcU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xdU] 
                = __Vtemp_h02cc08c7__0[0xdU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xeU] 
                = __Vtemp_h02cc08c7__0[0xeU];
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn[0xfU] 
                = __Vtemp_h02cc08c7__0[0xfU];
        }
    }
    if (((((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
           | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort)) 
          | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_err)) 
         | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err))) {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 0U;
    } else if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy) {
        if ((1U == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state))) {
            if ((0U == vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length)) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = 0U;
            } else if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_trigger) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 2U;
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 1U;
            }
        } else if ((2U == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state))) {
            if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 0U;
            }
            if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy)) 
                       & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request))))) {
                if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_inc) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr 
                        = (0xfffffffU & (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr 
                                         + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen)));
                }
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length 
                    = ((vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length 
                        > (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen))
                        ? (0xfffffffU & (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length 
                                         - (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen)))
                        : 0U);
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 3U;
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request = 1U;
            }
        } else if ((3U == (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state))) {
            if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request) 
                 & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy)))) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request = 0U;
            }
            if ((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy)) 
                       & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request))))) {
                if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_trigger) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 2U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 1U;
                } else {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 1U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 0U;
                }
                if (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen) 
                     > vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length)) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen 
                        = (0x7ffU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length);
                }
                if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_inc) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr 
                        = (0xfffffffU & (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr 
                                         + (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen)));
                }
                if ((0U == vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length)) {
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 0U;
                    vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = 0U;
                }
            }
        }
    } else {
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen 
            = (0x7ffU & ((vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length 
                          < (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_transferlen))
                          ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length
                          : (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_transferlen)));
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 0U;
        vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 0U;
        if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request) {
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy = 1U;
            if (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_trigger) {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 2U;
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 1U;
            } else {
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state = 1U;
                vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request = 0U;
            }
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst;
            vlSelf->__Vdly__main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length 
                = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length;
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en)) 
                  & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = 0ULL;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID) 
                & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_ready))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = 0xffffffffffffffffULL;
        if ((0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
            if ((1U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                if ((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                    if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) {
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U];
                        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U];
                    }
                }
            }
            if ((1U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) {
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U];
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U];
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U];
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U];
                }
                if ((1U & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)))) {
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w;
                }
            } else if ((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                if ((1U & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)))) {
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U];
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U];
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U];
                    vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                        = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U];
                }
            }
        }
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = 0xffffU;
        if ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
            if ((1U & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)))) {
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                    = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__prior 
                    = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__prior;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                       >> 0x1fU);
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x1eU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x1dU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x1cU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x1bU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x1aU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x19U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x18U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x17U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x16U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x15U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x14U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x13U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x12U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x11U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0x10U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0xfU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0xeU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0xdU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0xcU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0xbU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 0xaU));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 9U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 8U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 7U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 6U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 5U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 4U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 3U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 2U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data 
                             >> 1U));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit 
                    = (1U & __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__i_crc_data);
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__44__Vfuncout;
                __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__Vfuncout 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__fill;
                vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg 
                    = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__43__Vfuncout;
            }
        }
    } else if (((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb) 
                  & (0U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                 & (1U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                & (0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts)))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
            = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U];
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
            = (0xffffffffULL | ((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg)) 
                                << 0x20U));
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = 0xffffU;
    }
    if (vlSelf->main__DOT__u_emmc__DOT__rx_en) {
        if ((0U != ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                    << 1U))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                = ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width))
                    ? ((3U == ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                               << 1U)) ? ((0xffffcU 
                                           & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                              << 2U)) 
                                          | (2U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data) 
                                                   << 1U)))
                        : ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb)
                            ? ((0xffffeU & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                            << 1U)) 
                               | (1U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data)))
                            : (0xffffeU & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                           << 1U))))
                    : ((1U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width))
                        ? ((3U == ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                                   << 1U)) ? ((0xfff00U 
                                               & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                  << 8U)) 
                                              | (0xf0U 
                                                 & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data) 
                                                    << 4U)))
                            : ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb)
                                ? ((0xffff0U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                << 4U)) 
                                   | (0xfU & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data)))
                                : (0xffff0U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                               << 4U))))
                        : ((3U == ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                                   << 1U)) ? ((0xf0000U 
                                               & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                  << 0x10U)) 
                                              | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data) 
                                                 << 8U))
                            : ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb)
                                ? ((0xfff00U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                << 8U)) 
                                   | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data))
                                : (0xfff00U & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                               << 8U))))));
        }
    } else {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg = 0U;
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en)) 
                  & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid)))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = 0ULL;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = 0U;
    } else if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID) 
                & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_ready))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg = 0xffffffffffffffffULL;
        if ((0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
            if ((1U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                if ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                    if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) {
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[0U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[1U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[2U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[3U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[4U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[5U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[6U];
                        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
                            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d[7U];
                    }
                }
            }
            if ((1U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U];
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U];
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U];
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U];
                }
                if ((1U & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)))) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w;
                }
            } else if ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
                if ((1U & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)))) {
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[0U];
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[1U];
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[2U];
                    vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
                        = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w[3U];
                }
            }
        }
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = 0xffffU;
        if ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width))) {
            if ((1U & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr)))) {
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                    = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__prior 
                    = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__prior;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                       >> 0x1fU);
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x1eU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x1dU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x1cU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x1bU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x1aU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x19U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x18U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x17U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x16U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x15U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x14U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x13U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x12U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x11U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0x10U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0xfU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0xeU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0xdU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0xcU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0xbU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 0xaU));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 9U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 8U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 7U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 6U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 5U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 4U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 3U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 2U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & (__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data 
                             >> 1U));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit 
                    = (1U & __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__i_crc_data);
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout 
                    = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                 >> 0xfU) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__i_bit)))
                        ? (0x1021U ^ (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                                 << 1U)))
                        : (0xfffeU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__prior) 
                                      << 1U)));
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__STEPCRC__86__Vfuncout;
                __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__Vfuncout 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__fill;
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg 
                    = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__APPLYCRC32__85__Vfuncout;
            }
        }
    } else if (((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb) 
                  & (0U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                 & (1U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate))) 
                & (0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts)))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[0U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[1U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[2U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[3U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[4U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[5U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[7U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg[6U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U] = 0xffffffffU;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[0U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[1U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[3U] 
            = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg[2U];
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg 
            = (0xffffffffULL | ((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg)) 
                                << 0x20U));
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg = 0xffffU;
    }
    if (vlSelf->main__DOT__u_sdcard__DOT__rx_en) {
        if ((0U != ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                    << 1U))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                = ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width))
                    ? ((3U == ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                               << 1U)) ? ((0xffffcU 
                                           & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                              << 2U)) 
                                          | (2U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data) 
                                                   << 1U)))
                        : ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb)
                            ? ((0xffffeU & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                            << 1U)) 
                               | (1U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data)))
                            : (0xffffeU & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                           << 1U))))
                    : ((1U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width))
                        ? ((3U == ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                                   << 1U)) ? ((0xfff00U 
                                               & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                  << 8U)) 
                                              | (0xf0U 
                                                 & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data) 
                                                    << 4U)))
                            : ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb)
                                ? ((0xffff0U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                << 4U)) 
                                   | (0xfU & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data)))
                                : (0xffff0U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                               << 4U))))
                        : ((3U == ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                                   << 1U)) ? ((0xf0000U 
                                               & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                  << 0x10U)) 
                                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data) 
                                                 << 8U))
                            : ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb)
                                ? ((0xfff00U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                                << 8U)) 
                                   | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data))
                                : (0xfff00U & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg 
                                               << 8U))))));
        }
    } else {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg = 0U;
    }
    if (((IData)(vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset) 
         | (IData)(vlSelf->main__DOT__i2ci__DOT__cpu_new_pc))) {
        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid = 0U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_valid = 0U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_illegal = 0U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid = 0U;
        vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count = 0U;
    } else {
        if ((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__wbwide_i2cm_cyc)) 
             & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                 | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)) 
                >> 1U))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid 
                = (1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
                         | (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)));
        } else if (((IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready) 
                    & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid = 0U;
        }
        if (((IData)(vlSelf->main__DOT__wbwide_i2cm_cyc) 
             & (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                 | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr)) 
                >> 1U))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_valid = 1U;
        } else if (vlSelf->main__DOT__i2ci__DOT__pf_ready) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_valid 
                = ((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid) 
                   | (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid));
        }
        if ((1U & (((~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)) 
                    & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid)) 
                       | (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready))) 
                   & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_illegal))))) {
            if (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_illegal 
                    = vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_illegal;
            } else if (((IData)(vlSelf->main__DOT__wbwide_i2cm_cyc) 
                        & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                           >> 1U))) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__pf_illegal = 1U;
            }
        }
        if (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__r_valid) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid 
                = (1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
                         | (1U < (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count))));
        } else if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid)) 
                          | (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid = 0U;
            if (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid = 1U;
            }
            if ((((IData)(vlSelf->main__DOT__wbwide_i2cm_cyc) 
                  & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                     >> 1U)) & (~ (IData)((0x3fU == (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_shift)))))) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid = 1U;
            }
        }
        if ((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
              & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
             & (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid))) {
            vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count 
                = (0x7fU & ((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count) 
                            - (IData)(1U)));
        } else if ((1U & ((~ (IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid)) 
                          | ((IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready) 
                             & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid)))))) {
            if (vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count = 0x3fU;
            } else if (((IData)(vlSelf->main__DOT__wbwide_i2cm_cyc) 
                        & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                           >> 1U))) {
                vlSelf->__Vdly__main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count 
                    = (0x3fU & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_shift)));
            }
        }
    }
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset) {
        vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pf_pc 
            = ((4U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc))
                ? ((2U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc))
                    ? 0x4000000U : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc))
                                     ? (0xffffffcU 
                                        & (((IData)(1U) 
                                            + (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pf_pc 
                                               >> 2U)) 
                                           << 2U)) : 
                                    (0xffffffcU & (
                                                   ((IData)(1U) 
                                                    + 
                                                    (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc 
                                                     >> 2U)) 
                                                   << 2U))))
                : ((2U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc))
                    ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc))
                        ? (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc)
                        : (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ipc))
                    : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc))
                        ? (0xffffffcU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl)
                        : 0x4000000U)));
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill = 0U;
    } else if ((1U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type) 
                      | (7U < (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))))) {
        if ((3U == ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb) 
                    << 1U))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__i_bit 
                = vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__fill 
                = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__33__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__Vfuncout 
                = ((0x40U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__fill))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__fill) 
                                                     << 1U)));
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__32__Vfuncout;
        } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__i_bit 
                = vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__fill 
                = vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__fill) 
                                                     << 1U)));
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__34__Vfuncout;
        }
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active)))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg = 0ULL;
    } else {
        if ((0xc0U > (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count 
                = (0xffU & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count) 
                            + ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb)
                                ? 1U : 0U)));
        }
        if (vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
                = ((0xfffffffffeULL & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
                                       << 1U)) | (QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data)));
        }
    }
    if ((1U & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
                | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active)) 
               | (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = 0x3ffffffU;
    } else if (((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout)) 
                & (0U != ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb) 
                          << 1U)))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = 0x3ffffffU;
    } else {
        if ((0U != vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter)) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter 
                = (0x3ffffffU & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter 
                                 - (IData)(1U)));
        }
        if ((1U >= vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter)) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 1U;
        }
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active)))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg = 0ULL;
    } else {
        if ((0xc0U > (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count 
                = (0xffU & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count) 
                            + ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb)
                                ? 1U : 0U)));
        }
        if (vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
                = ((0xfffffffffeULL & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg 
                                       << 1U)) | (QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_data)));
        }
    }
    if ((1U & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                 | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))) 
                | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active)) 
               | (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done)))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = 0x3ffffffU;
    } else if (((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout)) 
                & (0U != ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb) 
                          << 1U)))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter = 0x3ffffffU;
    } else {
        if ((0U != vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter)) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter 
                = (0x3ffffffU & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter 
                                 - (IData)(1U)));
        }
        if ((1U >= vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter)) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout = 1U;
        }
    }
    if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy = 0U;
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg = 0xffffffffffffULL;
    } else {
        if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy) {
            if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done) {
                vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy = 0U;
            }
        } else {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy 
                = (((IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en) 
                    & (0U < (0x1fffU & ((IData)(1U) 
                                        << (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk))))) 
                   & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done)));
        }
        if (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request) 
             & (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy)))) {
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                = (((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd)) 
                    << 0x20U) | (QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x27U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)
                    ? 9U : 0U);
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x26U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x25U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x24U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x23U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x22U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x21U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x20U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x1fU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x1eU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x1dU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x1cU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x1bU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x1aU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x19U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x18U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x17U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x16U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x15U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x14U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x13U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x12U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x11U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0x10U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0xfU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0xeU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0xdU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0xcU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0xbU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 0xaU)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 9U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 8U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 7U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 6U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 5U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 4U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 3U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 2U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd 
                                 >> 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit 
                = (1U & (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__cmd));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__31__Vfuncout;
            __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__Vfuncout 
                = __Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__fill;
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                = (((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd)) 
                    << 0x28U) | (((QData)((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg)) 
                                  << 8U) | (QData)((IData)(
                                                           (1U 
                                                            | ((IData)(__Vfunc_main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__30__Vfuncout) 
                                                               << 1U))))));
        } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb) {
            vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                = ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl)
                    ? (3ULL | (0xfffffffffffcULL & 
                               (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                << 2U))) : (1ULL | 
                                            (0xfffffffffffeULL 
                                             & (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                                << 1U))));
        }
    }
    if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy = 0U;
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg = 0xffffffffffffULL;
    } else {
        if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy) {
            if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done) {
                vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy = 0U;
            }
        } else {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy 
                = (((IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en) 
                    & (0U < (0x1fffU & ((IData)(1U) 
                                        << (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk))))) 
                   & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done)));
        }
        if (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request) 
             & (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy)))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                = (((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd)) 
                    << 0x20U) | (QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x27U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)
                    ? 9U : 0U);
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x26U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x25U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x24U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x23U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x22U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x21U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x20U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x1fU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x1eU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x1dU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x1cU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x1bU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x1aU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x19U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x18U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x17U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x16U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x15U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x14U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x13U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x12U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x11U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0x10U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0xfU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0xeU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0xdU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0xcU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0xbU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 0xaU)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 9U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 8U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 7U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 6U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 5U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 4U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 3U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 2U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)((__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd 
                                 >> 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit 
                = (1U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__cmd));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__73__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__Vfuncout 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__fill;
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                = (((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd)) 
                    << 0x28U) | (((QData)((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg)) 
                                  << 8U) | (QData)((IData)(
                                                           (1U 
                                                            | ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__CMDCRC__72__Vfuncout) 
                                                               << 1U))))));
        } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb) {
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                = ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl)
                    ? (3ULL | (0xfffffffffffcULL & 
                               (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                << 2U))) : (1ULL | 
                                            (0xfffffffffffeULL 
                                             & (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                                << 1U))));
        }
    }
    if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill = 0U;
    } else if ((1U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type) 
                      | (7U < (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count))))) {
        if ((3U == ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb) 
                    << 1U))) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__i_bit 
                = vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_data;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__fill 
                = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__fill) 
                                                     << 1U)));
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__75__Vfuncout;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__Vfuncout 
                = ((0x40U & (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__fill))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__fill) 
                                                     << 1U)));
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__74__Vfuncout;
        } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb) {
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__i_bit 
                = vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_data;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__fill 
                = vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill;
            __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__Vfuncout 
                = ((IData)((((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__fill) 
                             >> 6U) ^ (IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__i_bit)))
                    ? (9U ^ (0x7eU & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__fill) 
                                      << 1U))) : (0x7eU 
                                                  & ((IData)(__Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__fill) 
                                                     << 1U)));
            vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill 
                = __Vfunc_main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__STEPCRC__76__Vfuncout;
        }
    }
    if (((IData)(vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset) 
         | ((IData)(vlSelf->main__DOT__wbwide_i2cm_cyc) 
            & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
               >> 1U)))) {
        vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc = 0U;
        vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb = 0U;
    } else if (vlSelf->main__DOT__wbwide_i2cm_cyc) {
        if ((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_i2cm_stb)) 
                   | (~ ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                         >> 1U))))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb 
                = (1U & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__last_stb)));
        }
        if (((((~ (IData)(vlSelf->main__DOT__wbwide_i2cm_stb)) 
               | (~ ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                     >> 1U))) & (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__last_stb)) 
             & (((IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight) 
                 + ((IData)(vlSelf->main__DOT__wbwide_i2cm_stb)
                     ? 1U : 0U)) == ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack))
                                      ? 1U : 0U)))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc = 0U;
            vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb = 0U;
        }
        if (vlSelf->main__DOT__i2ci__DOT__cpu_new_pc) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc = 0U;
            vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb = 0U;
        }
    } else if ((((IData)(vlSelf->main__DOT__i2ci__DOT__cpu_new_pc) 
                 | (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__invalid_bus_cycle)) 
                | ((((IData)(vlSelf->main__DOT__i2ci__DOT__pf_valid) 
                     & (IData)(vlSelf->main__DOT__i2ci__DOT__pf_ready)) 
                    & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid))) 
                   & (~ (IData)(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_illegal))))) {
        vlSelf->__Vdly__main__DOT__wbwide_i2cm_cyc = 1U;
        vlSelf->__Vdly__main__DOT__wbwide_i2cm_stb = 1U;
    }
    if (((IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_reset) 
         | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__bus_err))) {
        vlSelf->__Vdly__main__DOT__wbwide_i2cdma_sel 
            = (0x8000000000000000ULL >> (0x3fU & vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr));
        vlSelf->__Vdly__main__DOT__wbwide_i2cdma_addr 
            = (0x3fffffU & (vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr 
                            >> 6U));
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__subaddr 
            = (0x3fU & vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr);
    } else if ((((~ (IData)(vlSelf->main__DOT__wbwide_i2cdma_stb)) 
                 | (~ (IData)(vlSelf->__VdfgTmp_h503d14d1__0))) 
                & ((IData)(vlSelf->main__DOT__u_i2cdma__DOT__wb_last) 
                   | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_overflow)))) {
        vlSelf->__Vdly__main__DOT__wbwide_i2cdma_sel 
            = (0x8000000000000000ULL >> (0x3fU & vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr));
        vlSelf->__Vdly__main__DOT__wbwide_i2cdma_addr 
            = (0x3fffffU & (vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr 
                            >> 6U));
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__subaddr 
            = (0x3fU & vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr);
    } else {
        if (((IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid) 
             & (IData)(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cdma_sel 
                = (((QData)((IData)((1U & (IData)(vlSelf->main__DOT__wbwide_i2cdma_sel)))) 
                    << 0x3fU) | (vlSelf->main__DOT__wbwide_i2cdma_sel 
                                 >> 1U));
        }
        if ((((IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid) 
              & (IData)(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready)) 
             & (~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_overflow)))) {
            vlSelf->__Vdly__main__DOT__wbwide_i2cdma_addr 
                = (0x3fffffU & (((IData)(1U) + ((vlSelf->main__DOT__wbwide_i2cdma_addr 
                                                 << 6U) 
                                                | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__subaddr))) 
                                >> 6U));
            vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__subaddr 
                = (0x3fU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_i2cdma__DOT__subaddr)));
        }
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (2U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = 0U;
    } else if (vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_valid) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr)));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (2U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type))) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr = 0U;
    } else if (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_valid) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr 
            = (0x3ffU & ((IData)(1U) + (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr)));
    }
    if (vlSelf->main__DOT__u_i2cdma__DOT__r_reset) {
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow = 0U;
    } else if ((((~ (IData)(vlSelf->main__DOT__wbwide_i2cdma_stb)) 
                 | (~ (IData)(vlSelf->__VdfgTmp_h503d14d1__0))) 
                & (IData)(vlSelf->main__DOT__u_i2cdma__DOT__wb_last))) {
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow = 0U;
    } else if ((((IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid) 
                 & (IData)(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready)) 
                & ((IData)(vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data) 
                   >> 8U))) {
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow = 0U;
    } else if ((1U & (~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__r_overflow)))) {
        vlSelf->__Vdly__main__DOT__u_i2cdma__DOT__r_overflow 
            = ((((IData)(1U) + ((vlSelf->main__DOT__wbwide_i2cdma_addr 
                                 << 6U) | (IData)(vlSelf->main__DOT__u_i2cdma__DOT__subaddr))) 
                - vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr) 
               >= vlSelf->main__DOT__u_i2cdma__DOT__r_memlen);
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en))) 
               | (~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase))))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill = 0U;
    } else if ((0U == ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                       << 1U))) {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
            = (7U & (IData)(vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill));
    } else {
        vlSelf->__Vdly__main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
            = (0x1fU & ((0U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width))
                         ? ((7U & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)) 
                            + ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb)
                                ? 1U : 0U)) : ((1U 
                                                == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width))
                                                ? (
                                                   (7U 
                                                    & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)) 
                                                   + 
                                                   ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb)
                                                     ? 4U
                                                     : 0U))
                                                : (
                                                   (7U 
                                                    & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)) 
                                                   + 
                                                   ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb)
                                                     ? 8U
                                                     : 0U)))));
    }
    if ((1U & (((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset) 
                | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en))) 
               | (~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase))))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill = 0U;
    } else if ((0U == ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                       << 1U))) {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
            = (7U & (IData)(vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill));
    } else {
        vlSelf->__Vdly__main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill 
            = (0x1fU & ((0U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width))
                         ? ((7U & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)) 
                            + ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb)
                                ? 1U : 0U)) : ((1U 
                                                == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width))
                                                ? (
                                                   (7U 
                                                    & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)) 
                                                   + 
                                                   ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb)
                                                     ? 4U
                                                     : 0U))
                                                : (
                                                   (7U 
                                                    & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill)) 
                                                   + 
                                                   ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb)
                                                     ? 8U
                                                     : 0U)))));
    }
    if ((1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) {
        if ((1U & ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                   >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                   [0U]))) {
            if ((1U & ((~ (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb)) 
                       | (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall))))) {
                vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
                    = ((6U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb)) 
                       | (1U & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                [vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                [0U]] & (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                            >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                            [0U])))));
            }
        } else {
            vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
                = (6U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
        }
    } else {
        vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
            = (6U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
    }
    if ((1U & ((IData)(vlSelf->i_reset) | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_err)))) {
        vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
            = (6U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
    }
    if ((2U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) {
        if ((1U & ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                   >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                   [1U]))) {
            if ((1U & ((~ ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb) 
                           >> 1U)) | (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall) 
                                         >> 1U))))) {
                vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
                    = ((5U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb)) 
                       | (2U & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                [vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                [1U]] & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                             >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                             [1U])) 
                                         << 1U))));
            }
        } else {
            vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
                = (5U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
        }
    } else {
        vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
            = (5U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
    }
    if ((1U & ((IData)(vlSelf->i_reset) | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_err) 
                                           >> 1U)))) {
        vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
            = (5U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
    }
    if ((4U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant))) {
        if ((1U & ((IData)(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc) 
                   >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                   [2U]))) {
            if ((1U & ((~ ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb) 
                           >> 2U)) | (~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall) 
                                         >> 2U))))) {
                vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
                    = ((3U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb)) 
                       | (4U & (vlSelf->main__DOT__wbwide_xbar__DOT__request
                                [vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                [2U]] & ((~ ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__mfull) 
                                             >> vlSelf->main__DOT__wbwide_xbar__DOT__sindex
                                             [2U])) 
                                         << 2U))));
            }
        } else {
            vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
                = (3U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
        }
    } else {
        vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
            = (3U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
    }
    if ((1U & ((IData)(vlSelf->i_reset) | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__s_err) 
                                           >> 2U)))) {
        vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb 
            = (3U & (IData)(vlSelf->__Vdly__main__DOT____Vcellout__wbwide_xbar__o_sstb));
    }
}
