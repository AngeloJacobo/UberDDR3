// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals
#include "verilated_vcd_c.h"
#include "Vmain__Syms.h"


VL_ATTR_COLD void Vmain___024root__trace_init_sub__TOP__0(Vmain___024root* vlSelf, VerilatedVcd* tracep) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root__trace_init_sub__TOP__0\n"); );
    // Init
    const int c = vlSymsp->__Vm_baseCode;
    // Body
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declArray(c+4903,"i_ddr3_controller_iserdes_data", false,-1, 511,0);
    tracep->declQuad(c+4919,"i_ddr3_controller_iserdes_dqs", false,-1, 63,0);
    tracep->declQuad(c+4921,"i_ddr3_controller_iserdes_bitslip_reference", false,-1, 63,0);
    tracep->declBit(c+4923,"i_ddr3_controller_idelayctrl_rdy", false,-1);
    tracep->declArray(c+4924,"o_ddr3_controller_cmd", false,-1, 95,0);
    tracep->declBit(c+4927,"o_ddr3_controller_dqs_tri_control", false,-1);
    tracep->declBit(c+4928,"o_ddr3_controller_dq_tri_control", false,-1);
    tracep->declBit(c+4929,"o_ddr3_controller_toggle_dqs", false,-1);
    tracep->declArray(c+4930,"o_ddr3_controller_data", false,-1, 511,0);
    tracep->declQuad(c+4946,"o_ddr3_controller_dm", false,-1, 63,0);
    tracep->declBus(c+4948,"o_ddr3_controller_odelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4949,"o_ddr3_controller_odelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4950,"o_ddr3_controller_idelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4951,"o_ddr3_controller_idelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4952,"o_ddr3_controller_odelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4953,"o_ddr3_controller_odelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4954,"o_ddr3_controller_idelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4955,"o_ddr3_controller_idelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4956,"o_ddr3_controller_bitslip", false,-1, 7,0);
    tracep->declBus(c+4957,"o_sirefclk_word", false,-1, 7,0);
    tracep->declBit(c+4958,"o_sirefclk_ce", false,-1);
    tracep->declBit(c+4959,"i_fan_sda", false,-1);
    tracep->declBit(c+4960,"i_fan_scl", false,-1);
    tracep->declBit(c+4961,"o_fan_sda", false,-1);
    tracep->declBit(c+4962,"o_fan_scl", false,-1);
    tracep->declBit(c+4963,"o_fpga_pwm", false,-1);
    tracep->declBit(c+4964,"o_sys_pwm", false,-1);
    tracep->declBit(c+4965,"i_fan_tach", false,-1);
    tracep->declBit(c+4966,"o_emmc_clk", false,-1);
    tracep->declBit(c+4967,"i_emmc_ds", false,-1);
    tracep->declBit(c+4968,"io_emmc_cmd_tristate", false,-1);
    tracep->declBit(c+4969,"o_emmc_cmd", false,-1);
    tracep->declBit(c+4970,"i_emmc_cmd", false,-1);
    tracep->declBus(c+4971,"io_emmc_dat_tristate", false,-1, 7,0);
    tracep->declBus(c+4972,"o_emmc_dat", false,-1, 7,0);
    tracep->declBus(c+4973,"i_emmc_dat", false,-1, 7,0);
    tracep->declBit(c+4974,"i_emmc_detect", false,-1);
    tracep->declBit(c+4975,"i_i2c_sda", false,-1);
    tracep->declBit(c+4976,"i_i2c_scl", false,-1);
    tracep->declBit(c+4977,"o_i2c_sda", false,-1);
    tracep->declBit(c+4978,"o_i2c_scl", false,-1);
    tracep->declBit(c+4979,"o_sdcard_clk", false,-1);
    tracep->declBit(c+4980,"i_sdcard_ds", false,-1);
    tracep->declBit(c+4981,"io_sdcard_cmd_tristate", false,-1);
    tracep->declBit(c+4982,"o_sdcard_cmd", false,-1);
    tracep->declBit(c+4983,"i_sdcard_cmd", false,-1);
    tracep->declBus(c+4984,"io_sdcard_dat_tristate", false,-1, 3,0);
    tracep->declBus(c+4985,"o_sdcard_dat", false,-1, 3,0);
    tracep->declBus(c+4986,"i_sdcard_dat", false,-1, 3,0);
    tracep->declBit(c+4987,"i_sdcard_detect", false,-1);
    tracep->declBit(c+4988,"cpu_sim_cyc", false,-1);
    tracep->declBit(c+4989,"cpu_sim_stb", false,-1);
    tracep->declBit(c+4990,"cpu_sim_we", false,-1);
    tracep->declBus(c+4991,"cpu_sim_addr", false,-1, 6,0);
    tracep->declBus(c+4992,"cpu_sim_data", false,-1, 31,0);
    tracep->declBit(c+4993,"cpu_sim_stall", false,-1);
    tracep->declBit(c+4994,"cpu_sim_ack", false,-1);
    tracep->declBus(c+4995,"cpu_sim_idata", false,-1, 31,0);
    tracep->declBit(c+4996,"cpu_prof_stb", false,-1);
    tracep->declBus(c+4997,"cpu_prof_addr", false,-1, 27,0);
    tracep->declBus(c+4998,"cpu_prof_ticks", false,-1, 31,0);
    tracep->declBit(c+4999,"i_cpu_reset", false,-1);
    tracep->declBit(c+5000,"i_wbu_uart_rx", false,-1);
    tracep->declBit(c+5001,"o_wbu_uart_tx", false,-1);
    tracep->declBit(c+5002,"o_wbu_uart_cts_n", false,-1);
    tracep->declBus(c+5003,"i_gpio", false,-1, 15,0);
    tracep->declBus(c+5004,"o_gpio", false,-1, 7,0);
    tracep->declBus(c+5005,"i_sw", false,-1, 7,0);
    tracep->declBus(c+5006,"i_btn", false,-1, 4,0);
    tracep->declBus(c+5007,"o_led", false,-1, 7,0);
    tracep->declBit(c+5008,"i_clk200", false,-1);
    tracep->pushNamePrefix("main ");
    tracep->declDouble(c+5056,"DDR3_CONTROLLERCONTROLLER_CLK_PERIOD", false,-1);
    tracep->declDouble(c+5058,"DDR3_CLK_PERIOD", false,-1);
    tracep->declBus(c+5060,"DDR3_CONTROLLERROW_BITS", false,-1, 31,0);
    tracep->declBus(c+5061,"DDR3_CONTROLLERCOL_BITS", false,-1, 31,0);
    tracep->declBus(c+5062,"DDR3_CONTROLLERBA_BITS", false,-1, 31,0);
    tracep->declBus(c+5063,"DDR3_CONTROLLERDQ_BITS", false,-1, 31,0);
    tracep->declBus(c+5063,"DDR3_CONTROLLERLANES", false,-1, 31,0);
    tracep->declBus(c+5064,"DDR3_CONTROLLERAUX_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5065,"DDR3_CONTROLLERSERDES_RATIO", false,-1, 31,0);
    tracep->declBus(c+5066,"DDR3_CONTROLLERCMD_LEN", false,-1, 31,0);
    tracep->declBus(c+5067,"RESET_ADDRESS", false,-1, 31,0);
    tracep->declBus(c+5068,"ZIP_ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5069,"ZIP_INTS", false,-1, 31,0);
    tracep->declBus(c+5070,"ZIP_START_HALTED", false,-1, 0,0);
    tracep->declBus(c+5071,"BUSUART", false,-1, 23,0);
    tracep->declBus(c+5072,"DBGBUSBITS", false,-1, 31,0);
    tracep->declBus(c+5069,"DBGBUSWATCHDOG_RAW", false,-1, 31,0);
    tracep->declBus(c+5073,"DBGBUSWATCHDOG", false,-1, 31,0);
    tracep->declBus(c+5062,"ICAPE_LGDIV", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declArray(c+4903,"i_ddr3_controller_iserdes_data", false,-1, 511,0);
    tracep->declQuad(c+4919,"i_ddr3_controller_iserdes_dqs", false,-1, 63,0);
    tracep->declQuad(c+4921,"i_ddr3_controller_iserdes_bitslip_reference", false,-1, 63,0);
    tracep->declBit(c+4923,"i_ddr3_controller_idelayctrl_rdy", false,-1);
    tracep->declArray(c+4924,"o_ddr3_controller_cmd", false,-1, 95,0);
    tracep->declBit(c+4927,"o_ddr3_controller_dqs_tri_control", false,-1);
    tracep->declBit(c+4928,"o_ddr3_controller_dq_tri_control", false,-1);
    tracep->declBit(c+4929,"o_ddr3_controller_toggle_dqs", false,-1);
    tracep->declArray(c+4930,"o_ddr3_controller_data", false,-1, 511,0);
    tracep->declQuad(c+4946,"o_ddr3_controller_dm", false,-1, 63,0);
    tracep->declBus(c+4948,"o_ddr3_controller_odelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4949,"o_ddr3_controller_odelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4950,"o_ddr3_controller_idelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4951,"o_ddr3_controller_idelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4952,"o_ddr3_controller_odelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4953,"o_ddr3_controller_odelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4954,"o_ddr3_controller_idelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4955,"o_ddr3_controller_idelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4956,"o_ddr3_controller_bitslip", false,-1, 7,0);
    tracep->declBus(c+4957,"o_sirefclk_word", false,-1, 7,0);
    tracep->declBit(c+4958,"o_sirefclk_ce", false,-1);
    tracep->declBit(c+4959,"i_fan_sda", false,-1);
    tracep->declBit(c+4960,"i_fan_scl", false,-1);
    tracep->declBit(c+4961,"o_fan_sda", false,-1);
    tracep->declBit(c+4962,"o_fan_scl", false,-1);
    tracep->declBit(c+4963,"o_fpga_pwm", false,-1);
    tracep->declBit(c+4964,"o_sys_pwm", false,-1);
    tracep->declBit(c+4965,"i_fan_tach", false,-1);
    tracep->declBit(c+4966,"o_emmc_clk", false,-1);
    tracep->declBit(c+4967,"i_emmc_ds", false,-1);
    tracep->declBit(c+4968,"io_emmc_cmd_tristate", false,-1);
    tracep->declBit(c+4969,"o_emmc_cmd", false,-1);
    tracep->declBit(c+4970,"i_emmc_cmd", false,-1);
    tracep->declBus(c+4971,"io_emmc_dat_tristate", false,-1, 7,0);
    tracep->declBus(c+4972,"o_emmc_dat", false,-1, 7,0);
    tracep->declBus(c+4973,"i_emmc_dat", false,-1, 7,0);
    tracep->declBit(c+4974,"i_emmc_detect", false,-1);
    tracep->declBit(c+4975,"i_i2c_sda", false,-1);
    tracep->declBit(c+4976,"i_i2c_scl", false,-1);
    tracep->declBit(c+4977,"o_i2c_sda", false,-1);
    tracep->declBit(c+4978,"o_i2c_scl", false,-1);
    tracep->declBit(c+4979,"o_sdcard_clk", false,-1);
    tracep->declBit(c+4980,"i_sdcard_ds", false,-1);
    tracep->declBit(c+4981,"io_sdcard_cmd_tristate", false,-1);
    tracep->declBit(c+4982,"o_sdcard_cmd", false,-1);
    tracep->declBit(c+4983,"i_sdcard_cmd", false,-1);
    tracep->declBus(c+4984,"io_sdcard_dat_tristate", false,-1, 3,0);
    tracep->declBus(c+4985,"o_sdcard_dat", false,-1, 3,0);
    tracep->declBus(c+4986,"i_sdcard_dat", false,-1, 3,0);
    tracep->declBit(c+4987,"i_sdcard_detect", false,-1);
    tracep->declBit(c+4988,"cpu_sim_cyc", false,-1);
    tracep->declBit(c+4989,"cpu_sim_stb", false,-1);
    tracep->declBit(c+4990,"cpu_sim_we", false,-1);
    tracep->declBus(c+4991,"cpu_sim_addr", false,-1, 6,0);
    tracep->declBus(c+4992,"cpu_sim_data", false,-1, 31,0);
    tracep->declBit(c+4993,"cpu_sim_stall", false,-1);
    tracep->declBit(c+4994,"cpu_sim_ack", false,-1);
    tracep->declBus(c+4995,"cpu_sim_idata", false,-1, 31,0);
    tracep->declBit(c+4996,"cpu_prof_stb", false,-1);
    tracep->declBus(c+4997,"cpu_prof_addr", false,-1, 27,0);
    tracep->declBus(c+4998,"cpu_prof_ticks", false,-1, 31,0);
    tracep->declBit(c+4999,"i_cpu_reset", false,-1);
    tracep->declBit(c+5000,"i_wbu_uart_rx", false,-1);
    tracep->declBit(c+5001,"o_wbu_uart_tx", false,-1);
    tracep->declBit(c+5002,"o_wbu_uart_cts_n", false,-1);
    tracep->declBus(c+5069,"NGPI", false,-1, 31,0);
    tracep->declBus(c+5063,"NGPO", false,-1, 31,0);
    tracep->declBus(c+5003,"i_gpio", false,-1, 15,0);
    tracep->declBus(c+5004,"o_gpio", false,-1, 7,0);
    tracep->declBus(c+5005,"i_sw", false,-1, 7,0);
    tracep->declBus(c+5006,"i_btn", false,-1, 4,0);
    tracep->declBus(c+5007,"o_led", false,-1, 7,0);
    tracep->declBit(c+158,"emmcscope_int", false,-1);
    tracep->declBit(c+159,"sdioscope_int", false,-1);
    tracep->declBit(c+160,"emmc_int", false,-1);
    tracep->declBit(c+161,"sdcard_int", false,-1);
    tracep->declBit(c+162,"uartrxf_int", false,-1);
    tracep->declBit(c+163,"uarttx_int", false,-1);
    tracep->declBit(c+164,"uarttxf_int", false,-1);
    tracep->declBit(c+165,"uartrx_int", false,-1);
    tracep->declBit(c+166,"i2cscope_int", false,-1);
    tracep->declBit(c+167,"gpio_int", false,-1);
    tracep->declBit(c+168,"spio_int", false,-1);
    tracep->declBus(c+4032,"ddr3_controller_aux_out", false,-1, 0,0);
    tracep->declBit(c+169,"r_sirefclk_en", false,-1);
    tracep->declBus(c+170,"r_sirefclk_data", false,-1, 29,0);
    tracep->declBit(c+171,"w_sirefclk_unused_stb", false,-1);
    tracep->declBit(c+172,"r_sirefclk_ack", false,-1);
    tracep->declBit(c+173,"i2cdma_ready", false,-1);
    tracep->declBus(c+5009,"fan_debug", false,-1, 31,0);
    tracep->declBit(c+5074,"w_emmc_1p8v", false,-1);
    tracep->declBus(c+36,"emmc_debug", false,-1, 31,0);
    tracep->declBus(c+5075,"I2C_ID_WIDTH", false,-1, 31,0);
    tracep->declBit(c+174,"i2c_valid", false,-1);
    tracep->declBit(c+175,"i2c_ready", false,-1);
    tracep->declBit(c+176,"i2c_last", false,-1);
    tracep->declBus(c+177,"i2c_data", false,-1, 7,0);
    tracep->declBus(c+178,"i2c_id", false,-1, 1,0);
    tracep->declBus(c+37,"i2c_debug", false,-1, 31,0);
    tracep->declBit(c+5074,"w_sdcard_1p8v", false,-1);
    tracep->declBus(c+179,"sdcard_debug", false,-1, 31,0);
    tracep->declBit(c+180,"w_console_rx_stb", false,-1);
    tracep->declBit(c+181,"w_console_tx_stb", false,-1);
    tracep->declBit(c+182,"w_console_busy", false,-1);
    tracep->declBus(c+183,"w_console_rx_data", false,-1, 6,0);
    tracep->declBus(c+184,"w_console_tx_data", false,-1, 6,0);
    tracep->declBus(c+185,"uart_debug", false,-1, 31,0);
    tracep->declBit(c+186,"raw_cpu_dbg_stall", false,-1);
    tracep->declBit(c+187,"raw_cpu_dbg_ack", false,-1);
    tracep->declBus(c+5076,"zip_debug", false,-1, 31,0);
    tracep->declBit(c+5074,"zip_trigger", false,-1);
    tracep->declBus(c+188,"zip_int_vector", false,-1, 15,0);
    tracep->declBit(c+189,"zip_cpu_int", false,-1);
    tracep->declBit(c+5008,"i_clk200", false,-1);
    tracep->declBus(c+190,"wbu_rx_data", false,-1, 7,0);
    tracep->declBus(c+191,"wbu_tx_data", false,-1, 7,0);
    tracep->declBit(c+192,"wbu_rx_stb", false,-1);
    tracep->declBit(c+193,"wbu_tx_stb", false,-1);
    tracep->declBit(c+194,"wbu_tx_busy", false,-1);
    tracep->declBus(c+195,"wbubus_dbg", false,-1, 0,0);
    tracep->declBus(c+5076,"cfg_debug", false,-1, 31,0);
    tracep->declBus(c+196,"w_led", false,-1, 7,0);
    tracep->declBus(c+197,"sys_int_vector", false,-1, 14,0);
    tracep->declBus(c+198,"alt_int_vector", false,-1, 14,0);
    tracep->declBit(c+199,"wbwide_i2cdma_cyc", false,-1);
    tracep->declBit(c+200,"wbwide_i2cdma_stb", false,-1);
    tracep->declBit(c+5077,"wbwide_i2cdma_we", false,-1);
    tracep->declBus(c+201,"wbwide_i2cdma_addr", false,-1, 21,0);
    tracep->declArray(c+202,"wbwide_i2cdma_data", false,-1, 511,0);
    tracep->declQuad(c+218,"wbwide_i2cdma_sel", false,-1, 63,0);
    tracep->declBit(c+220,"wbwide_i2cdma_stall", false,-1);
    tracep->declBit(c+221,"wbwide_i2cdma_ack", false,-1);
    tracep->declBit(c+222,"wbwide_i2cdma_err", false,-1);
    tracep->declArray(c+223,"wbwide_i2cdma_idata", false,-1, 511,0);
    tracep->declBit(c+239,"wbwide_i2cm_cyc", false,-1);
    tracep->declBit(c+240,"wbwide_i2cm_stb", false,-1);
    tracep->declBit(c+5074,"wbwide_i2cm_we", false,-1);
    tracep->declBus(c+241,"wbwide_i2cm_addr", false,-1, 21,0);
    tracep->declArray(c+5078,"wbwide_i2cm_data", false,-1, 511,0);
    tracep->declQuad(c+5094,"wbwide_i2cm_sel", false,-1, 63,0);
    tracep->declBit(c+242,"wbwide_i2cm_stall", false,-1);
    tracep->declBit(c+243,"wbwide_i2cm_ack", false,-1);
    tracep->declBit(c+244,"wbwide_i2cm_err", false,-1);
    tracep->declArray(c+245,"wbwide_i2cm_idata", false,-1, 511,0);
    tracep->declBit(c+261,"wbwide_zip_cyc", false,-1);
    tracep->declBit(c+262,"wbwide_zip_stb", false,-1);
    tracep->declBit(c+263,"wbwide_zip_we", false,-1);
    tracep->declBus(c+264,"wbwide_zip_addr", false,-1, 21,0);
    tracep->declArray(c+265,"wbwide_zip_data", false,-1, 511,0);
    tracep->declQuad(c+281,"wbwide_zip_sel", false,-1, 63,0);
    tracep->declBit(c+283,"wbwide_zip_stall", false,-1);
    tracep->declBit(c+284,"wbwide_zip_ack", false,-1);
    tracep->declBit(c+285,"wbwide_zip_err", false,-1);
    tracep->declArray(c+286,"wbwide_zip_idata", false,-1, 511,0);
    tracep->declBit(c+302,"wbwide_wbu_arbiter_cyc", false,-1);
    tracep->declBit(c+303,"wbwide_wbu_arbiter_stb", false,-1);
    tracep->declBit(c+304,"wbwide_wbu_arbiter_we", false,-1);
    tracep->declBus(c+305,"wbwide_wbu_arbiter_addr", false,-1, 21,0);
    tracep->declArray(c+306,"wbwide_wbu_arbiter_data", false,-1, 511,0);
    tracep->declQuad(c+322,"wbwide_wbu_arbiter_sel", false,-1, 63,0);
    tracep->declBit(c+324,"wbwide_wbu_arbiter_stall", false,-1);
    tracep->declBit(c+325,"wbwide_wbu_arbiter_ack", false,-1);
    tracep->declBit(c+326,"wbwide_wbu_arbiter_err", false,-1);
    tracep->declArray(c+327,"wbwide_wbu_arbiter_idata", false,-1, 511,0);
    tracep->declBit(c+4419,"wbwide_wbdown_cyc", false,-1);
    tracep->declBit(c+4420,"wbwide_wbdown_stb", false,-1);
    tracep->declBit(c+4421,"wbwide_wbdown_we", false,-1);
    tracep->declBus(c+4422,"wbwide_wbdown_addr", false,-1, 21,0);
    tracep->declArray(c+4423,"wbwide_wbdown_data", false,-1, 511,0);
    tracep->declQuad(c+4439,"wbwide_wbdown_sel", false,-1, 63,0);
    tracep->declBit(c+343,"wbwide_wbdown_stall", false,-1);
    tracep->declBit(c+344,"wbwide_wbdown_ack", false,-1);
    tracep->declBit(c+4441,"wbwide_wbdown_err", false,-1);
    tracep->declArray(c+345,"wbwide_wbdown_idata", false,-1, 511,0);
    tracep->declBit(c+4442,"wbwide_bkram_cyc", false,-1);
    tracep->declBit(c+4443,"wbwide_bkram_stb", false,-1);
    tracep->declBit(c+4444,"wbwide_bkram_we", false,-1);
    tracep->declBus(c+4445,"wbwide_bkram_addr", false,-1, 21,0);
    tracep->declArray(c+4446,"wbwide_bkram_data", false,-1, 511,0);
    tracep->declQuad(c+4462,"wbwide_bkram_sel", false,-1, 63,0);
    tracep->declBit(c+5074,"wbwide_bkram_stall", false,-1);
    tracep->declBit(c+361,"wbwide_bkram_ack", false,-1);
    tracep->declBit(c+5074,"wbwide_bkram_err", false,-1);
    tracep->declArray(c+362,"wbwide_bkram_idata", false,-1, 511,0);
    tracep->declBit(c+4464,"wbwide_ddr3_controller_cyc", false,-1);
    tracep->declBit(c+4465,"wbwide_ddr3_controller_stb", false,-1);
    tracep->declBit(c+4466,"wbwide_ddr3_controller_we", false,-1);
    tracep->declBus(c+4467,"wbwide_ddr3_controller_addr", false,-1, 21,0);
    tracep->declArray(c+4468,"wbwide_ddr3_controller_data", false,-1, 511,0);
    tracep->declQuad(c+4484,"wbwide_ddr3_controller_sel", false,-1, 63,0);
    tracep->declBit(c+4033,"wbwide_ddr3_controller_stall", false,-1);
    tracep->declBit(c+4034,"wbwide_ddr3_controller_ack", false,-1);
    tracep->declBit(c+5074,"wbwide_ddr3_controller_err", false,-1);
    tracep->declArray(c+4035,"wbwide_ddr3_controller_idata", false,-1, 511,0);
    tracep->declBit(c+4486,"wb32_wbdown_cyc", false,-1);
    tracep->declBit(c+378,"wb32_wbdown_stb", false,-1);
    tracep->declBit(c+379,"wb32_wbdown_we", false,-1);
    tracep->declBus(c+380,"wb32_wbdown_addr", false,-1, 7,0);
    tracep->declBus(c+381,"wb32_wbdown_data", false,-1, 31,0);
    tracep->declBus(c+382,"wb32_wbdown_sel", false,-1, 3,0);
    tracep->declBit(c+383,"wb32_wbdown_stall", false,-1);
    tracep->declBit(c+384,"wb32_wbdown_ack", false,-1);
    tracep->declBit(c+4487,"wb32_wbdown_err", false,-1);
    tracep->declBus(c+385,"wb32_wbdown_idata", false,-1, 31,0);
    tracep->declBit(c+4488,"wb32_buildtime_cyc", false,-1);
    tracep->declBit(c+4489,"wb32_buildtime_stb", false,-1);
    tracep->declBit(c+4490,"wb32_buildtime_we", false,-1);
    tracep->declBus(c+5096,"wb32_buildtime_addr", false,-1, 7,0);
    tracep->declBus(c+4491,"wb32_buildtime_data", false,-1, 31,0);
    tracep->declBus(c+4492,"wb32_buildtime_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_buildtime_stall", false,-1);
    tracep->declBit(c+4489,"wb32_buildtime_ack", false,-1);
    tracep->declBit(c+5097,"wb32_buildtime_err", false,-1);
    tracep->declBus(c+5098,"wb32_buildtime_idata", false,-1, 31,0);
    tracep->declBit(c+4488,"wb32_gpio_cyc", false,-1);
    tracep->declBit(c+4493,"wb32_gpio_stb", false,-1);
    tracep->declBit(c+4490,"wb32_gpio_we", false,-1);
    tracep->declBus(c+5099,"wb32_gpio_addr", false,-1, 7,0);
    tracep->declBus(c+4491,"wb32_gpio_data", false,-1, 31,0);
    tracep->declBus(c+4492,"wb32_gpio_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_gpio_stall", false,-1);
    tracep->declBit(c+4493,"wb32_gpio_ack", false,-1);
    tracep->declBit(c+5100,"wb32_gpio_err", false,-1);
    tracep->declBus(c+5010,"wb32_gpio_idata", false,-1, 31,0);
    tracep->declBit(c+4488,"wb32_sirefclk_cyc", false,-1);
    tracep->declBit(c+4494,"wb32_sirefclk_stb", false,-1);
    tracep->declBit(c+4490,"wb32_sirefclk_we", false,-1);
    tracep->declBus(c+5101,"wb32_sirefclk_addr", false,-1, 7,0);
    tracep->declBus(c+4491,"wb32_sirefclk_data", false,-1, 31,0);
    tracep->declBus(c+4492,"wb32_sirefclk_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_sirefclk_stall", false,-1);
    tracep->declBit(c+172,"wb32_sirefclk_ack", false,-1);
    tracep->declBit(c+5102,"wb32_sirefclk_err", false,-1);
    tracep->declBus(c+386,"wb32_sirefclk_idata", false,-1, 31,0);
    tracep->declBit(c+4488,"wb32_spio_cyc", false,-1);
    tracep->declBit(c+4495,"wb32_spio_stb", false,-1);
    tracep->declBit(c+4490,"wb32_spio_we", false,-1);
    tracep->declBus(c+5103,"wb32_spio_addr", false,-1, 7,0);
    tracep->declBus(c+4491,"wb32_spio_data", false,-1, 31,0);
    tracep->declBus(c+4492,"wb32_spio_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_spio_stall", false,-1);
    tracep->declBit(c+387,"wb32_spio_ack", false,-1);
    tracep->declBit(c+5104,"wb32_spio_err", false,-1);
    tracep->declBus(c+388,"wb32_spio_idata", false,-1, 31,0);
    tracep->declBit(c+4488,"wb32_version_cyc", false,-1);
    tracep->declBit(c+4496,"wb32_version_stb", false,-1);
    tracep->declBit(c+4490,"wb32_version_we", false,-1);
    tracep->declBus(c+5105,"wb32_version_addr", false,-1, 7,0);
    tracep->declBus(c+4491,"wb32_version_data", false,-1, 31,0);
    tracep->declBus(c+4492,"wb32_version_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_version_stall", false,-1);
    tracep->declBit(c+4496,"wb32_version_ack", false,-1);
    tracep->declBit(c+5106,"wb32_version_err", false,-1);
    tracep->declBus(c+5107,"wb32_version_idata", false,-1, 31,0);
    tracep->declBit(c+4497,"wb32_emmcscope_cyc", false,-1);
    tracep->declBit(c+4498,"wb32_emmcscope_stb", false,-1);
    tracep->declBit(c+4499,"wb32_emmcscope_we", false,-1);
    tracep->declBus(c+4500,"wb32_emmcscope_addr", false,-1, 7,0);
    tracep->declBus(c+4501,"wb32_emmcscope_data", false,-1, 31,0);
    tracep->declBus(c+4502,"wb32_emmcscope_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_emmcscope_stall", false,-1);
    tracep->declBit(c+389,"wb32_emmcscope_ack", false,-1);
    tracep->declBit(c+5074,"wb32_emmcscope_err", false,-1);
    tracep->declBus(c+390,"wb32_emmcscope_idata", false,-1, 31,0);
    tracep->declBit(c+4503,"wb32_i2cscope_cyc", false,-1);
    tracep->declBit(c+4504,"wb32_i2cscope_stb", false,-1);
    tracep->declBit(c+4505,"wb32_i2cscope_we", false,-1);
    tracep->declBus(c+4506,"wb32_i2cscope_addr", false,-1, 7,0);
    tracep->declBus(c+4507,"wb32_i2cscope_data", false,-1, 31,0);
    tracep->declBus(c+4508,"wb32_i2cscope_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_i2cscope_stall", false,-1);
    tracep->declBit(c+391,"wb32_i2cscope_ack", false,-1);
    tracep->declBit(c+5074,"wb32_i2cscope_err", false,-1);
    tracep->declBus(c+392,"wb32_i2cscope_idata", false,-1, 31,0);
    tracep->declBit(c+4509,"wb32_sdioscope_cyc", false,-1);
    tracep->declBit(c+4510,"wb32_sdioscope_stb", false,-1);
    tracep->declBit(c+4511,"wb32_sdioscope_we", false,-1);
    tracep->declBus(c+4512,"wb32_sdioscope_addr", false,-1, 7,0);
    tracep->declBus(c+4513,"wb32_sdioscope_data", false,-1, 31,0);
    tracep->declBus(c+4514,"wb32_sdioscope_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_sdioscope_stall", false,-1);
    tracep->declBit(c+393,"wb32_sdioscope_ack", false,-1);
    tracep->declBit(c+5074,"wb32_sdioscope_err", false,-1);
    tracep->declBus(c+394,"wb32_sdioscope_idata", false,-1, 31,0);
    tracep->declBit(c+4515,"wb32_i2cs_cyc", false,-1);
    tracep->declBit(c+4516,"wb32_i2cs_stb", false,-1);
    tracep->declBit(c+4517,"wb32_i2cs_we", false,-1);
    tracep->declBus(c+4518,"wb32_i2cs_addr", false,-1, 7,0);
    tracep->declBus(c+4519,"wb32_i2cs_data", false,-1, 31,0);
    tracep->declBus(c+4520,"wb32_i2cs_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_i2cs_stall", false,-1);
    tracep->declBit(c+395,"wb32_i2cs_ack", false,-1);
    tracep->declBit(c+5074,"wb32_i2cs_err", false,-1);
    tracep->declBus(c+396,"wb32_i2cs_idata", false,-1, 31,0);
    tracep->declBit(c+4521,"wb32_i2cdma_cyc", false,-1);
    tracep->declBit(c+4522,"wb32_i2cdma_stb", false,-1);
    tracep->declBit(c+4523,"wb32_i2cdma_we", false,-1);
    tracep->declBus(c+4524,"wb32_i2cdma_addr", false,-1, 7,0);
    tracep->declBus(c+4525,"wb32_i2cdma_data", false,-1, 31,0);
    tracep->declBus(c+4526,"wb32_i2cdma_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_i2cdma_stall", false,-1);
    tracep->declBit(c+397,"wb32_i2cdma_ack", false,-1);
    tracep->declBit(c+5074,"wb32_i2cdma_err", false,-1);
    tracep->declBus(c+398,"wb32_i2cdma_idata", false,-1, 31,0);
    tracep->declBit(c+4527,"wb32_uart_cyc", false,-1);
    tracep->declBit(c+4528,"wb32_uart_stb", false,-1);
    tracep->declBit(c+4529,"wb32_uart_we", false,-1);
    tracep->declBus(c+4530,"wb32_uart_addr", false,-1, 7,0);
    tracep->declBus(c+4531,"wb32_uart_data", false,-1, 31,0);
    tracep->declBus(c+4532,"wb32_uart_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_uart_stall", false,-1);
    tracep->declBit(c+399,"wb32_uart_ack", false,-1);
    tracep->declBit(c+5074,"wb32_uart_err", false,-1);
    tracep->declBus(c+400,"wb32_uart_idata", false,-1, 31,0);
    tracep->declBit(c+4533,"wb32_emmc_cyc", false,-1);
    tracep->declBit(c+4534,"wb32_emmc_stb", false,-1);
    tracep->declBit(c+4535,"wb32_emmc_we", false,-1);
    tracep->declBus(c+4536,"wb32_emmc_addr", false,-1, 7,0);
    tracep->declBus(c+4537,"wb32_emmc_data", false,-1, 31,0);
    tracep->declBus(c+4538,"wb32_emmc_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_emmc_stall", false,-1);
    tracep->declBit(c+401,"wb32_emmc_ack", false,-1);
    tracep->declBit(c+5074,"wb32_emmc_err", false,-1);
    tracep->declBus(c+402,"wb32_emmc_idata", false,-1, 31,0);
    tracep->declBit(c+4539,"wb32_fan_cyc", false,-1);
    tracep->declBit(c+4540,"wb32_fan_stb", false,-1);
    tracep->declBit(c+4541,"wb32_fan_we", false,-1);
    tracep->declBus(c+4542,"wb32_fan_addr", false,-1, 7,0);
    tracep->declBus(c+4543,"wb32_fan_data", false,-1, 31,0);
    tracep->declBus(c+4544,"wb32_fan_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_fan_stall", false,-1);
    tracep->declBit(c+403,"wb32_fan_ack", false,-1);
    tracep->declBit(c+5074,"wb32_fan_err", false,-1);
    tracep->declBus(c+404,"wb32_fan_idata", false,-1, 31,0);
    tracep->declBit(c+4545,"wb32_sdcard_cyc", false,-1);
    tracep->declBit(c+4546,"wb32_sdcard_stb", false,-1);
    tracep->declBit(c+4547,"wb32_sdcard_we", false,-1);
    tracep->declBus(c+4548,"wb32_sdcard_addr", false,-1, 7,0);
    tracep->declBus(c+4549,"wb32_sdcard_data", false,-1, 31,0);
    tracep->declBus(c+4550,"wb32_sdcard_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_sdcard_stall", false,-1);
    tracep->declBit(c+405,"wb32_sdcard_ack", false,-1);
    tracep->declBit(c+5074,"wb32_sdcard_err", false,-1);
    tracep->declBus(c+406,"wb32_sdcard_idata", false,-1, 31,0);
    tracep->declBit(c+4488,"wb32_sio_cyc", false,-1);
    tracep->declBit(c+4551,"wb32_sio_stb", false,-1);
    tracep->declBit(c+4490,"wb32_sio_we", false,-1);
    tracep->declBus(c+4552,"wb32_sio_addr", false,-1, 7,0);
    tracep->declBus(c+4491,"wb32_sio_data", false,-1, 31,0);
    tracep->declBus(c+4492,"wb32_sio_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_sio_stall", false,-1);
    tracep->declBit(c+407,"wb32_sio_ack", false,-1);
    tracep->declBit(c+5074,"wb32_sio_err", false,-1);
    tracep->declBus(c+408,"wb32_sio_idata", false,-1, 31,0);
    tracep->declBit(c+4553,"wb32_cfg_cyc", false,-1);
    tracep->declBit(c+4554,"wb32_cfg_stb", false,-1);
    tracep->declBit(c+4555,"wb32_cfg_we", false,-1);
    tracep->declBus(c+4556,"wb32_cfg_addr", false,-1, 7,0);
    tracep->declBus(c+4557,"wb32_cfg_data", false,-1, 31,0);
    tracep->declBus(c+4558,"wb32_cfg_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"wb32_cfg_stall", false,-1);
    tracep->declBit(c+409,"wb32_cfg_ack", false,-1);
    tracep->declBit(c+5074,"wb32_cfg_err", false,-1);
    tracep->declBus(c+5076,"wb32_cfg_idata", false,-1, 31,0);
    tracep->declBit(c+4559,"wb32_ddr3_phy_cyc", false,-1);
    tracep->declBit(c+4560,"wb32_ddr3_phy_stb", false,-1);
    tracep->declBit(c+4561,"wb32_ddr3_phy_we", false,-1);
    tracep->declBus(c+4562,"wb32_ddr3_phy_addr", false,-1, 7,0);
    tracep->declBus(c+4563,"wb32_ddr3_phy_data", false,-1, 31,0);
    tracep->declBus(c+4564,"wb32_ddr3_phy_sel", false,-1, 3,0);
    tracep->declBit(c+4051,"wb32_ddr3_phy_stall", false,-1);
    tracep->declBit(c+4052,"wb32_ddr3_phy_ack", false,-1);
    tracep->declBit(c+5074,"wb32_ddr3_phy_err", false,-1);
    tracep->declBus(c+4053,"wb32_ddr3_phy_idata", false,-1, 31,0);
    tracep->declBit(c+410,"wbu_cyc", false,-1);
    tracep->declBit(c+411,"wbu_stb", false,-1);
    tracep->declBit(c+412,"wbu_we", false,-1);
    tracep->declBus(c+413,"wbu_addr", false,-1, 26,0);
    tracep->declBus(c+414,"wbu_data", false,-1, 31,0);
    tracep->declBus(c+5108,"wbu_sel", false,-1, 3,0);
    tracep->declBit(c+415,"wbu_stall", false,-1);
    tracep->declBit(c+416,"wbu_ack", false,-1);
    tracep->declBit(c+417,"wbu_err", false,-1);
    tracep->declBus(c+418,"wbu_idata", false,-1, 31,0);
    tracep->declBit(c+419,"wbu_wbu_arbiter_cyc", false,-1);
    tracep->declBit(c+420,"wbu_wbu_arbiter_stb", false,-1);
    tracep->declBit(c+421,"wbu_wbu_arbiter_we", false,-1);
    tracep->declBus(c+422,"wbu_wbu_arbiter_addr", false,-1, 26,0);
    tracep->declBus(c+423,"wbu_wbu_arbiter_data", false,-1, 31,0);
    tracep->declBus(c+424,"wbu_wbu_arbiter_sel", false,-1, 3,0);
    tracep->declBit(c+425,"wbu_wbu_arbiter_stall", false,-1);
    tracep->declBit(c+426,"wbu_wbu_arbiter_ack", false,-1);
    tracep->declBit(c+427,"wbu_wbu_arbiter_err", false,-1);
    tracep->declBus(c+428,"wbu_wbu_arbiter_idata", false,-1, 31,0);
    tracep->declBit(c+429,"wbu_zip_cyc", false,-1);
    tracep->declBit(c+430,"wbu_zip_stb", false,-1);
    tracep->declBit(c+431,"wbu_zip_we", false,-1);
    tracep->declBus(c+432,"wbu_zip_addr", false,-1, 26,0);
    tracep->declBus(c+433,"wbu_zip_data", false,-1, 31,0);
    tracep->declBus(c+434,"wbu_zip_sel", false,-1, 3,0);
    tracep->declBit(c+5011,"wbu_zip_stall", false,-1);
    tracep->declBit(c+5012,"wbu_zip_ack", false,-1);
    tracep->declBit(c+5074,"wbu_zip_err", false,-1);
    tracep->declBus(c+435,"wbu_zip_idata", false,-1, 31,0);
    tracep->declBit(c+407,"r_wb32_sio_ack", false,-1);
    tracep->declBus(c+408,"r_wb32_sio_data", false,-1, 31,0);
    tracep->declBit(c+5074,"zip_unused", false,-1);
    tracep->declBit(c+189,"w_bus_int", false,-1);
    tracep->declBus(c+436,"wbu_tmp_addr", false,-1, 29,0);
    tracep->declBit(c+409,"r_cfg_ack", false,-1);
    tracep->declBit(c+5074,"cfg_unused", false,-1);
    tracep->declBus(c+5109,"INITIAL_GPIO", false,-1, 7,0);
    tracep->pushNamePrefix("bkrami ");
    tracep->declBus(c+5110,"LGMEMSZ", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5064,"EXTRACLOCK", false,-1, 31,0);
    tracep->declBus(c+5112,"HEXFILE", false,-1, 7,0);
    tracep->declBus(c+5113,"OPT_ROM", false,-1, 0,0);
    tracep->declBus(c+5060,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4442,"i_wb_cyc", false,-1);
    tracep->declBit(c+4443,"i_wb_stb", false,-1);
    tracep->declBit(c+4444,"i_wb_we", false,-1);
    tracep->declBus(c+4565,"i_wb_addr", false,-1, 13,0);
    tracep->declArray(c+4446,"i_wb_data", false,-1, 511,0);
    tracep->declQuad(c+4462,"i_wb_sel", false,-1, 63,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+361,"o_wb_ack", false,-1);
    tracep->declArray(c+362,"o_wb_data", false,-1, 511,0);
    tracep->declBit(c+437,"w_wstb", false,-1);
    tracep->declBit(c+438,"w_stb", false,-1);
    tracep->declArray(c+439,"w_data", false,-1, 511,0);
    tracep->declBus(c+455,"w_addr", false,-1, 13,0);
    tracep->declQuad(c+456,"w_sel", false,-1, 63,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("EXTRA_MEM_CLOCK_CYCLE ");
    tracep->declBit(c+437,"last_wstb", false,-1);
    tracep->declBit(c+438,"last_stb", false,-1);
    tracep->declBus(c+455,"last_addr", false,-1, 13,0);
    tracep->declArray(c+439,"last_data", false,-1, 511,0);
    tracep->declQuad(c+456,"last_sel", false,-1, 63,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("WRITE_TO_MEMORY ");
    tracep->declBus(c+458,"ik", false,-1, 31,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("clock_generator ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBus(c+5063,"UPSAMPLE", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBus(c+459,"i_delay", false,-1, 31,0);
    tracep->declBus(c+4957,"o_word", false,-1, 7,0);
    tracep->declBit(c+171,"o_stb", false,-1);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+460+i*1,"counter", true,(i+0), 31,0);
    }
    tracep->declBus(c+468,"r_delay", false,-1, 31,0);
    tracep->declBus(c+469,"times_three", false,-1, 31,0);
    tracep->declBus(c+470,"times_five", false,-1, 31,0);
    tracep->declBus(c+471,"times_seven", false,-1, 31,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("console ");
    tracep->declBus(c+5115,"LGFLEN", false,-1, 3,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+4527,"i_wb_cyc", false,-1);
    tracep->declBit(c+4528,"i_wb_stb", false,-1);
    tracep->declBit(c+4529,"i_wb_we", false,-1);
    tracep->declBus(c+4566,"i_wb_addr", false,-1, 1,0);
    tracep->declBus(c+4531,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4532,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+399,"o_wb_ack", false,-1);
    tracep->declBus(c+400,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+181,"o_uart_stb", false,-1);
    tracep->declBus(c+184,"o_uart_data", false,-1, 6,0);
    tracep->declBit(c+182,"i_uart_busy", false,-1);
    tracep->declBit(c+180,"i_uart_stb", false,-1);
    tracep->declBus(c+183,"i_uart_data", false,-1, 6,0);
    tracep->declBit(c+165,"o_uart_rx_int", false,-1);
    tracep->declBit(c+163,"o_uart_tx_int", false,-1);
    tracep->declBit(c+162,"o_uart_rxfifo_int", false,-1);
    tracep->declBit(c+164,"o_uart_txfifo_int", false,-1);
    tracep->declBus(c+185,"o_debug", false,-1, 31,0);
    tracep->declBus(c+5115,"LCLLGFLEN", false,-1, 3,0);
    tracep->declBus(c+5116,"UART_SETUP", false,-1, 1,0);
    tracep->declBus(c+5117,"UART_FIFO", false,-1, 1,0);
    tracep->declBus(c+5118,"UART_RXREG", false,-1, 1,0);
    tracep->declBus(c+5119,"UART_TXREG", false,-1, 1,0);
    tracep->declBit(c+472,"rx_uart_reset", false,-1);
    tracep->declBit(c+165,"rx_empty_n", false,-1);
    tracep->declBit(c+473,"rx_fifo_err", false,-1);
    tracep->declBus(c+474,"rxf_wb_data", false,-1, 6,0);
    tracep->declBus(c+475,"rxf_status", false,-1, 15,0);
    tracep->declBit(c+476,"rxf_wb_read", false,-1);
    tracep->declBus(c+477,"wb_rx_data", false,-1, 31,0);
    tracep->declBit(c+181,"tx_empty_n", false,-1);
    tracep->declBit(c+478,"txf_err", false,-1);
    tracep->declBus(c+479,"txf_status", false,-1, 15,0);
    tracep->declBit(c+480,"txf_wb_write", false,-1);
    tracep->declBit(c+481,"tx_uart_reset", false,-1);
    tracep->declBus(c+482,"txf_wb_data", false,-1, 6,0);
    tracep->declBus(c+483,"wb_tx_data", false,-1, 31,0);
    tracep->declBus(c+484,"wb_fifo_data", false,-1, 31,0);
    tracep->declBus(c+485,"r_wb_addr", false,-1, 1,0);
    tracep->declBit(c+486,"r_wb_ack", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("rxfifo ");
    tracep->declBus(c+5072,"BW", false,-1, 31,0);
    tracep->declBus(c+5115,"LGFLEN", false,-1, 3,0);
    tracep->declBus(c+5070,"RXFIFO", false,-1, 0,0);
    tracep->declBus(c+5120,"FLEN", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+472,"i_reset", false,-1);
    tracep->declBit(c+180,"i_wr", false,-1);
    tracep->declBus(c+183,"i_data", false,-1, 6,0);
    tracep->declBit(c+165,"o_empty_n", false,-1);
    tracep->declBit(c+476,"i_rd", false,-1);
    tracep->declBus(c+474,"o_data", false,-1, 6,0);
    tracep->declBus(c+475,"o_status", false,-1, 15,0);
    tracep->declBit(c+473,"o_err", false,-1);
    tracep->declBus(c+487,"r_data", false,-1, 6,0);
    tracep->declBus(c+488,"last_write", false,-1, 6,0);
    tracep->declBus(c+489,"wr_addr", false,-1, 5,0);
    tracep->declBus(c+490,"rd_addr", false,-1, 5,0);
    tracep->declBus(c+491,"r_next", false,-1, 5,0);
    tracep->declBit(c+492,"will_overflow", false,-1);
    tracep->declBit(c+493,"will_underflow", false,-1);
    tracep->declBit(c+494,"osrc", false,-1);
    tracep->declBus(c+495,"w_waddr_plus_one", false,-1, 5,0);
    tracep->declBus(c+496,"w_waddr_plus_two", false,-1, 5,0);
    tracep->declBit(c+497,"w_write", false,-1);
    tracep->declBit(c+498,"w_read", false,-1);
    tracep->declBus(c+499,"r_fill", false,-1, 5,0);
    tracep->declBus(c+5115,"lglen", false,-1, 3,0);
    tracep->declBit(c+162,"w_half_full", false,-1);
    tracep->declBus(c+500,"w_fill", false,-1, 9,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("txfifo ");
    tracep->declBus(c+5072,"BW", false,-1, 31,0);
    tracep->declBus(c+5115,"LGFLEN", false,-1, 3,0);
    tracep->declBus(c+5113,"RXFIFO", false,-1, 0,0);
    tracep->declBus(c+5120,"FLEN", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+481,"i_reset", false,-1);
    tracep->declBit(c+480,"i_wr", false,-1);
    tracep->declBus(c+482,"i_data", false,-1, 6,0);
    tracep->declBit(c+181,"o_empty_n", false,-1);
    tracep->declBit(c+501,"i_rd", false,-1);
    tracep->declBus(c+184,"o_data", false,-1, 6,0);
    tracep->declBus(c+479,"o_status", false,-1, 15,0);
    tracep->declBit(c+478,"o_err", false,-1);
    tracep->declBus(c+502,"r_data", false,-1, 6,0);
    tracep->declBus(c+503,"last_write", false,-1, 6,0);
    tracep->declBus(c+504,"wr_addr", false,-1, 5,0);
    tracep->declBus(c+505,"rd_addr", false,-1, 5,0);
    tracep->declBus(c+506,"r_next", false,-1, 5,0);
    tracep->declBit(c+507,"will_overflow", false,-1);
    tracep->declBit(c+508,"will_underflow", false,-1);
    tracep->declBit(c+509,"osrc", false,-1);
    tracep->declBus(c+510,"w_waddr_plus_one", false,-1, 5,0);
    tracep->declBus(c+511,"w_waddr_plus_two", false,-1, 5,0);
    tracep->declBit(c+512,"w_write", false,-1);
    tracep->declBit(c+513,"w_read", false,-1);
    tracep->declBus(c+514,"r_fill", false,-1, 5,0);
    tracep->declBus(c+5115,"lglen", false,-1, 3,0);
    tracep->declBit(c+164,"w_half_full", false,-1);
    tracep->declBus(c+515,"w_fill", false,-1, 9,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("ddr3_controller_inst ");
    tracep->declDouble(c+5056,"CONTROLLER_CLK_PERIOD", false,-1);
    tracep->declDouble(c+5058,"DDR3_CLK_PERIOD", false,-1);
    tracep->declBus(c+5060,"ROW_BITS", false,-1, 31,0);
    tracep->declBus(c+5061,"COL_BITS", false,-1, 31,0);
    tracep->declBus(c+5062,"BA_BITS", false,-1, 31,0);
    tracep->declBus(c+5063,"DQ_BITS", false,-1, 31,0);
    tracep->declBus(c+5063,"LANES", false,-1, 31,0);
    tracep->declBus(c+5064,"AUX_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5114,"WB2_ADDR_BITS", false,-1, 31,0);
    tracep->declBus(c+5114,"WB2_DATA_BITS", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_BUS_ABORT", false,-1, 0,0);
    tracep->declBus(c+5065,"serdes_ratio", false,-1, 31,0);
    tracep->declBus(c+5111,"wb_data_bits", false,-1, 31,0);
    tracep->declBus(c+5121,"wb_addr_bits", false,-1, 31,0);
    tracep->declBus(c+5120,"wb_sel_bits", false,-1, 31,0);
    tracep->declBus(c+5065,"wb2_sel_bits", false,-1, 31,0);
    tracep->declBus(c+5066,"cmd_len", false,-1, 31,0);
    tracep->declBit(c+4901,"i_controller_clk", false,-1);
    tracep->declBit(c+5013,"i_rst_n", false,-1);
    tracep->declBit(c+4464,"i_wb_cyc", false,-1);
    tracep->declBit(c+4465,"i_wb_stb", false,-1);
    tracep->declBit(c+4466,"i_wb_we", false,-1);
    tracep->declBus(c+4567,"i_wb_addr", false,-1, 20,0);
    tracep->declArray(c+4468,"i_wb_data", false,-1, 511,0);
    tracep->declQuad(c+4484,"i_wb_sel", false,-1, 63,0);
    tracep->declBus(c+5074,"i_aux", false,-1, 0,0);
    tracep->declBit(c+4033,"o_wb_stall", false,-1);
    tracep->declBit(c+4034,"o_wb_ack", false,-1);
    tracep->declArray(c+4035,"o_wb_data", false,-1, 511,0);
    tracep->declBus(c+4032,"o_aux", false,-1, 0,0);
    tracep->declBit(c+4559,"i_wb2_cyc", false,-1);
    tracep->declBit(c+4560,"i_wb2_stb", false,-1);
    tracep->declBit(c+4561,"i_wb2_we", false,-1);
    tracep->declBus(c+4568,"i_wb2_addr", false,-1, 31,0);
    tracep->declBus(c+4564,"i_wb2_sel", false,-1, 3,0);
    tracep->declBus(c+4563,"i_wb2_data", false,-1, 31,0);
    tracep->declBit(c+4051,"o_wb2_stall", false,-1);
    tracep->declBit(c+4052,"o_wb2_ack", false,-1);
    tracep->declBus(c+4053,"o_wb2_data", false,-1, 31,0);
    tracep->declArray(c+4903,"i_phy_iserdes_data", false,-1, 511,0);
    tracep->declQuad(c+4919,"i_phy_iserdes_dqs", false,-1, 63,0);
    tracep->declQuad(c+4921,"i_phy_iserdes_bitslip_reference", false,-1, 63,0);
    tracep->declBit(c+4923,"i_phy_idelayctrl_rdy", false,-1);
    tracep->declArray(c+4924,"o_phy_cmd", false,-1, 95,0);
    tracep->declBit(c+4927,"o_phy_dqs_tri_control", false,-1);
    tracep->declBit(c+4928,"o_phy_dq_tri_control", false,-1);
    tracep->declBit(c+4929,"o_phy_toggle_dqs", false,-1);
    tracep->declArray(c+4930,"o_phy_data", false,-1, 511,0);
    tracep->declQuad(c+4946,"o_phy_dm", false,-1, 63,0);
    tracep->declBus(c+4948,"o_phy_odelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4949,"o_phy_odelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4950,"o_phy_idelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4951,"o_phy_idelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4952,"o_phy_odelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4953,"o_phy_odelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4954,"o_phy_idelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4955,"o_phy_idelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4956,"o_phy_bitslip", false,-1, 7,0);
    tracep->declBus(c+5122,"CMD_MRS", false,-1, 3,0);
    tracep->declBus(c+5123,"CMD_REF", false,-1, 3,0);
    tracep->declBus(c+5124,"CMD_PRE", false,-1, 3,0);
    tracep->declBus(c+5125,"CMD_ACT", false,-1, 3,0);
    tracep->declBus(c+5126,"CMD_WR", false,-1, 3,0);
    tracep->declBus(c+5127,"CMD_RD", false,-1, 3,0);
    tracep->declBus(c+5128,"CMD_NOP", false,-1, 3,0);
    tracep->declBus(c+5129,"CMD_DES", false,-1, 3,0);
    tracep->declBus(c+5115,"CMD_ZQC", false,-1, 3,0);
    tracep->declBus(c+5130,"RST_DONE", false,-1, 31,0);
    tracep->declBus(c+5130,"REF_IDLE", false,-1, 31,0);
    tracep->declBus(c+5131,"USE_TIMER", false,-1, 31,0);
    tracep->declBus(c+5132,"A10_CONTROL", false,-1, 31,0);
    tracep->declBus(c+5066,"CLOCK_EN", false,-1, 31,0);
    tracep->declBus(c+5133,"RESET_N", false,-1, 31,0);
    tracep->declBus(c+5068,"DDR3_CMD_START", false,-1, 31,0);
    tracep->declBus(c+5073,"DDR3_CMD_END", false,-1, 31,0);
    tracep->declBus(c+5134,"MRS_BANK_START", false,-1, 31,0);
    tracep->declBus(c+5133,"CMD_CS_N", false,-1, 31,0);
    tracep->declBus(c+5068,"CMD_RAS_N", false,-1, 31,0);
    tracep->declBus(c+5121,"CMD_CAS_N", false,-1, 31,0);
    tracep->declBus(c+5110,"CMD_WE_N", false,-1, 31,0);
    tracep->declBus(c+5073,"CMD_ODT", false,-1, 31,0);
    tracep->declBus(c+5134,"CMD_CKE", false,-1, 31,0);
    tracep->declBus(c+5135,"CMD_RESET_N", false,-1, 31,0);
    tracep->declBus(c+5069,"CMD_BANK_START", false,-1, 31,0);
    tracep->declBus(c+5136,"CMD_ADDRESS_START", false,-1, 31,0);
    tracep->declBus(c+5118,"READ_SLOT", false,-1, 1,0);
    tracep->declBus(c+5119,"WRITE_SLOT", false,-1, 1,0);
    tracep->declBus(c+5116,"ACTIVATE_SLOT", false,-1, 1,0);
    tracep->declBus(c+5117,"PRECHARGE_SLOT", false,-1, 1,0);
    tracep->declBus(c+5076,"DATA_INITIAL_ODELAY_TAP", false,-1, 31,0);
    tracep->declBus(c+5063,"DQS_INITIAL_ODELAY_TAP", false,-1, 31,0);
    tracep->declBus(c+5076,"DATA_INITIAL_IDELAY_TAP", false,-1, 31,0);
    tracep->declBus(c+5063,"DQS_INITIAL_IDELAY_TAP", false,-1, 31,0);
    tracep->declBus(c+5073,"DELAY_SLOT_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5137,"POWER_ON_RESET_HIGH", false,-1, 31,0);
    tracep->declBus(c+5138,"INITIAL_CKE_LOW", false,-1, 31,0);
    tracep->declDouble(c+5139,"tRCD", false,-1);
    tracep->declDouble(c+5139,"tRP", false,-1);
    tracep->declBus(c+5141,"tRAS", false,-1, 31,0);
    tracep->declDouble(c+5142,"tRFC", false,-1);
    tracep->declBus(c+5144,"tREFI", false,-1, 31,0);
    tracep->declDouble(c+5145,"tXPR", false,-1);
    tracep->declBus(c+5065,"tMRD", false,-1, 31,0);
    tracep->declDouble(c+5147,"tWR", false,-1);
    tracep->declDouble(c+5056,"tWTR", false,-1);
    tracep->declBus(c+5149,"tWLMRD", false,-1, 18,0);
    tracep->declDouble(c+5150,"tWLO", false,-1);
    tracep->declBus(c+5075,"tWLOE", false,-1, 31,0);
    tracep->declDouble(c+5056,"tRTP", false,-1);
    tracep->declBus(c+5065,"tCCD", false,-1, 31,0);
    tracep->declBus(c+5062,"tMOD", false,-1, 31,0);
    tracep->declBus(c+5152,"tZQinit", false,-1, 31,0);
    tracep->declBus(c+5153,"CL_nCK", false,-1, 31,0);
    tracep->declBus(c+5154,"CWL_nCK", false,-1, 31,0);
    tracep->declBus(c+5155,"DELAY_MAX_VALUE", false,-1, 18,0);
    tracep->declBus(c+5069,"DELAY_COUNTER_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5075,"CALIBRATION_DELAY", false,-1, 31,0);
    tracep->declBus(c+5123,"PRECHARGE_TO_ACTIVATE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5125,"ACTIVATE_TO_PRECHARGE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5122,"ACTIVATE_TO_WRITE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5122,"ACTIVATE_TO_READ_DELAY", false,-1, 3,0);
    tracep->declBus(c+5123,"READ_TO_WRITE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5122,"READ_TO_READ_DELAY", false,-1, 3,0);
    tracep->declBus(c+5123,"READ_TO_PRECHARGE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5122,"WRITE_TO_WRITE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5125,"WRITE_TO_READ_DELAY", false,-1, 3,0);
    tracep->declBus(c+5126,"WRITE_TO_PRECHARGE_DELAY", false,-1, 3,0);
    tracep->declBus(c+5154,"PRE_REFRESH_DELAY", false,-1, 31,0);
    tracep->declBus(c+5127,"MARGIN_BEFORE_ANTICIPATE", false,-1, 3,0);
    tracep->declBus(c+5075,"STAGE2_DATA_DEPTH", false,-1, 31,0);
    tracep->declBus(c+5076,"READ_DELAY", false,-1, 31,0);
    tracep->declBus(c+5154,"READ_ACK_PIPE_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5069,"MAX_ADDED_READ_ACK_DELAY", false,-1, 31,0);
    tracep->declBus(c+5136,"DELAY_BEFORE_WRITE_LEVEL_FEEDBACK", false,-1, 31,0);
    tracep->declBus(c+5076,"IDLE", false,-1, 31,0);
    tracep->declBus(c+5064,"BITSLIP_DQS_TRAIN_1", false,-1, 31,0);
    tracep->declBus(c+5075,"MPR_READ", false,-1, 31,0);
    tracep->declBus(c+5062,"COLLECT_DQS", false,-1, 31,0);
    tracep->declBus(c+5065,"ANALYZE_DQS", false,-1, 31,0);
    tracep->declBus(c+5154,"CALIBRATE_DQS", false,-1, 31,0);
    tracep->declBus(c+5153,"BITSLIP_DQS_TRAIN_2", false,-1, 31,0);
    tracep->declBus(c+5072,"START_WRITE_LEVEL", false,-1, 31,0);
    tracep->declBus(c+5063,"WAIT_FOR_FEEDBACK", false,-1, 31,0);
    tracep->declBus(c+5156,"ISSUE_WRITE_1", false,-1, 31,0);
    tracep->declBus(c+5061,"ISSUE_WRITE_2", false,-1, 31,0);
    tracep->declBus(c+5157,"ISSUE_READ", false,-1, 31,0);
    tracep->declBus(c+5158,"READ_DATA", false,-1, 31,0);
    tracep->declBus(c+5136,"ANALYZE_DATA", false,-1, 31,0);
    tracep->declBus(c+5060,"DONE_CALIBRATE", false,-1, 31,0);
    tracep->declBus(c+5154,"STORED_DQS_SIZE", false,-1, 31,0);
    tracep->declBus(c+5064,"REPEAT_DQS_ANALYZE", false,-1, 31,0);
    tracep->declBus(c+5159,"PASR", false,-1, 2,0);
    tracep->declBus(c+5159,"CWL", false,-1, 2,0);
    tracep->declBus(c+5070,"ASR", false,-1, 0,0);
    tracep->declBus(c+5113,"SRT", false,-1, 0,0);
    tracep->declBus(c+5116,"RTT_WR", false,-1, 1,0);
    tracep->declBus(c+5160,"MR2_SEL", false,-1, 2,0);
    tracep->declBus(c+5161,"MR2", false,-1, 18,0);
    tracep->declBus(c+5116,"MPR_LOC", false,-1, 1,0);
    tracep->declBus(c+5070,"MPR_EN", false,-1, 0,0);
    tracep->declBus(c+5113,"MPR_DIS", false,-1, 0,0);
    tracep->declBus(c+5162,"MR3_SEL", false,-1, 2,0);
    tracep->declBus(c+5163,"MR3_MPR_EN", false,-1, 18,0);
    tracep->declBus(c+5164,"MR3_MPR_DIS", false,-1, 18,0);
    tracep->declBus(c+5165,"MR3_RD_ADDR", false,-1, 16,0);
    tracep->declBus(c+5113,"DLL_EN", false,-1, 0,0);
    tracep->declBus(c+5116,"DIC", false,-1, 1,0);
    tracep->declBus(c+5162,"RTT_NOM", false,-1, 2,0);
    tracep->declBus(c+5070,"WL_EN", false,-1, 0,0);
    tracep->declBus(c+5113,"WL_DIS", false,-1, 0,0);
    tracep->declBus(c+5116,"AL", false,-1, 1,0);
    tracep->declBus(c+5070,"TDQS", false,-1, 0,0);
    tracep->declBus(c+5113,"QOFF", false,-1, 0,0);
    tracep->declBus(c+5166,"MR1_SEL", false,-1, 2,0);
    tracep->declBus(c+5167,"MR1_WL_EN", false,-1, 18,0);
    tracep->declBus(c+5168,"MR1_WL_DIS", false,-1, 18,0);
    tracep->declBus(c+5116,"BL", false,-1, 1,0);
    tracep->declBus(c+5126,"CL", false,-1, 3,0);
    tracep->declBus(c+5113,"RBT", false,-1, 0,0);
    tracep->declBus(c+5070,"DLL_RST", false,-1, 0,0);
    tracep->declBus(c+5162,"WR", false,-1, 2,0);
    tracep->declBus(c+5113,"PPD", false,-1, 0,0);
    tracep->declBus(c+5159,"MR0_SEL", false,-1, 2,0);
    tracep->declBus(c+5169,"MR0", false,-1, 18,0);
    tracep->declBus(c+5170,"INITIAL_RESET_INSTRUCTION", false,-1, 27,0);
    tracep->declBus(c+4054,"index", false,-1, 31,0);
    tracep->declBus(c+4055,"instruction_address", false,-1, 4,0);
    tracep->declBus(c+4056,"instruction", false,-1, 27,0);
    tracep->declBus(c+4057,"delay_counter", false,-1, 15,0);
    tracep->declBit(c+4058,"delay_counter_is_zero", false,-1);
    tracep->declBit(c+4059,"reset_done", false,-1);
    tracep->declBit(c+4060,"pause_counter", false,-1);
    tracep->declBit(c+4061,"issue_read_command", false,-1);
    tracep->declBit(c+5074,"issue_write_command", false,-1);
    tracep->declBit(c+4062,"stage2_update", false,-1);
    tracep->declBit(c+4828,"stage2_stall", false,-1);
    tracep->declBit(c+4829,"stage1_stall", false,-1);
    tracep->declBus(c+4063,"bank_status_q", false,-1, 7,0);
    tracep->declBus(c+4830,"bank_status_d", false,-1, 7,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4064+i*1,"bank_active_row_q", true,(i+0), 13,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4831+i*1,"bank_active_row_d", true,(i+0), 13,0);
    }
    tracep->declBit(c+4072,"stage1_pending", false,-1);
    tracep->declBus(c+4073,"stage1_aux", false,-1, 0,0);
    tracep->declBit(c+4074,"stage1_we", false,-1);
    tracep->declArray(c+4075,"stage1_data", false,-1, 511,0);
    tracep->declQuad(c+4091,"stage1_dm", false,-1, 63,0);
    tracep->declBus(c+4093,"stage1_col", false,-1, 9,0);
    tracep->declBus(c+4094,"stage1_bank", false,-1, 2,0);
    tracep->declBus(c+4095,"stage1_row", false,-1, 13,0);
    tracep->declBus(c+4096,"stage1_next_bank", false,-1, 2,0);
    tracep->declBus(c+4097,"stage1_next_row", false,-1, 13,0);
    tracep->declBus(c+4569,"wb_addr_plus_anticipate", false,-1, 20,0);
    tracep->declBit(c+4098,"stage2_pending", false,-1);
    tracep->declBus(c+4099,"stage2_aux", false,-1, 0,0);
    tracep->declBit(c+4100,"stage2_we", false,-1);
    tracep->declQuad(c+4101,"stage2_dm_unaligned", false,-1, 63,0);
    for (int i = 0; i < 2; ++i) {
        tracep->declQuad(c+4103+i*2,"stage2_dm", true,(i+0), 63,0);
    }
    tracep->declArray(c+4107,"stage2_data_unaligned", false,-1, 511,0);
    for (int i = 0; i < 2; ++i) {
        tracep->declArray(c+4123+i*16,"stage2_data", true,(i+0), 511,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declQuad(c+4155+i*2,"unaligned_data", true,(i+0), 63,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4171+i*1,"unaligned_dm", true,(i+0), 7,0);
    }
    tracep->declBus(c+4179,"stage2_col", false,-1, 9,0);
    tracep->declBus(c+4180,"stage2_bank", false,-1, 2,0);
    tracep->declBus(c+4181,"stage2_row", false,-1, 13,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4182+i*1,"delay_before_precharge_counter_q", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4839+i*1,"delay_before_precharge_counter_d", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4190+i*1,"delay_before_activate_counter_q", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4847+i*1,"delay_before_activate_counter_d", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4198+i*1,"delay_before_write_counter_q", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4855+i*1,"delay_before_write_counter_d", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4206+i*1,"delay_before_read_counter_q", true,(i+0), 3,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4863+i*1,"delay_before_read_counter_d", true,(i+0), 3,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+4871+i*1,"cmd_d", true,(i+0), 23,0);
    }
    tracep->declBit(c+4214,"cmd_odt_q", false,-1);
    tracep->declBit(c+4875,"cmd_odt", false,-1);
    tracep->declBit(c+4876,"cmd_ck_en", false,-1);
    tracep->declBit(c+4877,"cmd_reset_n", false,-1);
    tracep->declBit(c+4215,"o_wb_stall_q", false,-1);
    tracep->declBit(c+4878,"o_wb_stall_d", false,-1);
    tracep->declBit(c+4879,"precharge_slot_busy", false,-1);
    tracep->declBit(c+4880,"activate_slot_busy", false,-1);
    tracep->declBus(c+4216,"write_dqs_q", false,-1, 1,0);
    tracep->declBit(c+4217,"write_dqs_d", false,-1);
    tracep->declBus(c+4218,"write_dqs", false,-1, 2,0);
    tracep->declBus(c+4219,"write_dqs_val", false,-1, 2,0);
    tracep->declBit(c+4220,"write_dq_q", false,-1);
    tracep->declBit(c+4221,"write_dq_d", false,-1);
    tracep->declBus(c+4222,"write_dq", false,-1, 3,0);
    tracep->declBus(c+5171,"aligned_cmd", false,-1, 23,0);
    tracep->declBus(c+5172,"serial_index", false,-1, 1,0);
    tracep->declBus(c+5173,"serial_index_q", false,-1, 1,0);
    tracep->declBus(c+5174,"test_OFB", false,-1, 7,0);
    tracep->declBus(c+4223,"state_calibrate", false,-1, 4,0);
    tracep->declQuad(c+4224,"dqs_store", false,-1, 39,0);
    tracep->declBus(c+4226,"dqs_count_repeat", false,-1, 3,0);
    tracep->declBus(c+4227,"dqs_start_index", false,-1, 5,0);
    tracep->declBus(c+4228,"dqs_start_index_stored", false,-1, 5,0);
    tracep->declBus(c+4229,"dqs_target_index", false,-1, 5,0);
    tracep->declBus(c+4230,"dqs_target_index_orig", false,-1, 5,0);
    tracep->declBus(c+4231,"dq_target_index", false,-1, 5,0);
    tracep->declBus(c+4232,"dqs_target_index_value", false,-1, 5,0);
    tracep->declBus(c+4233,"dqs_start_index_repeat", false,-1, 0,0);
    tracep->declBus(c+4234,"train_delay", false,-1, 1,0);
    tracep->declBus(c+4235,"delay_before_read_data", false,-1, 3,0);
    tracep->declBus(c+4236,"delay_before_write_level_feedback", false,-1, 4,0);
    tracep->declBit(c+4237,"initial_dqs", false,-1);
    tracep->declBus(c+4238,"lane", false,-1, 2,0);
    tracep->declBus(c+4239,"lane_times_8", false,-1, 5,0);
    tracep->declBus(c+4240,"dqs_bitslip_arrangement", false,-1, 15,0);
    tracep->declBus(c+4241,"added_read_pipe_max", false,-1, 3,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4242+i*1,"added_read_pipe", true,(i+0), 3,0);
    }
    for (int i = 0; i < 5; ++i) {
        tracep->declBus(c+4250+i*1,"shift_reg_read_pipe_q", true,(i+0), 1,0);
    }
    for (int i = 0; i < 5; ++i) {
        tracep->declBus(c+4255+i*1,"shift_reg_read_pipe_d", true,(i+0), 1,0);
    }
    tracep->declBit(c+4260,"index_read_pipe", false,-1);
    tracep->declBit(c+4261,"index_wb_data", false,-1);
    for (int i = 0; i < 2; ++i) {
        tracep->declBus(c+4262+i*1,"delay_read_pipe", true,(i+0), 15,0);
    }
    for (int i = 0; i < 2; ++i) {
        tracep->declArray(c+4264+i*16,"o_wb_data_q", true,(i+0), 511,0);
    }
    for (int i = 0; i < 16; ++i) {
        tracep->declBus(c+4296+i*1,"o_wb_ack_read_q", true,(i+0), 1,0);
    }
    tracep->declBit(c+4312,"write_calib_stb", false,-1);
    tracep->declBus(c+4313,"write_calib_aux", false,-1, 0,0);
    tracep->declBit(c+4314,"write_calib_we", false,-1);
    tracep->declBus(c+4315,"write_calib_col", false,-1, 9,0);
    tracep->declArray(c+4316,"write_calib_data", false,-1, 511,0);
    tracep->declBit(c+4332,"write_calib_odt", false,-1);
    tracep->declBit(c+4333,"write_calib_dqs", false,-1);
    tracep->declBit(c+4334,"write_calib_dq", false,-1);
    tracep->declBit(c+4335,"prev_write_level_feedback", false,-1);
    tracep->declArray(c+4336,"read_data_store", false,-1, 511,0);
    tracep->declArray(c+4352,"write_pattern", false,-1, 127,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4356+i*1,"data_start_index", true,(i+0), 6,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4364+i*1,"odelay_data_cntvaluein", true,(i+0), 4,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4372+i*1,"odelay_dqs_cntvaluein", true,(i+0), 4,0);
    }
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4380+i*1,"idelay_data_cntvaluein", true,(i+0), 4,0);
    }
    tracep->declBus(c+4388,"idelay_data_cntvaluein_prev", false,-1, 4,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+4389+i*1,"idelay_dqs_cntvaluein", true,(i+0), 4,0);
    }
    tracep->declBit(c+4397,"wb2_stb", false,-1);
    tracep->declBit(c+4398,"wb2_update", false,-1);
    tracep->declBit(c+4399,"wb2_we", false,-1);
    tracep->declBus(c+4400,"wb2_addr", false,-1, 31,0);
    tracep->declBus(c+4401,"wb2_data", false,-1, 31,0);
    tracep->declBus(c+4402,"wb2_sel", false,-1, 3,0);
    tracep->declBus(c+5175,"wb2_read_lane", false,-1, 2,0);
    tracep->declBus(c+4403,"wb2_phy_odelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4404,"wb2_phy_odelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4405,"wb2_phy_idelay_data_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4406,"wb2_phy_idelay_dqs_cntvaluein", false,-1, 4,0);
    tracep->declBus(c+4407,"wb2_phy_odelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4408,"wb2_phy_odelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4409,"wb2_phy_idelay_data_ld", false,-1, 7,0);
    tracep->declBus(c+4410,"wb2_phy_idelay_dqs_ld", false,-1, 7,0);
    tracep->declBus(c+4411,"wb2_write_lane", false,-1, 2,0);
    tracep->declBus(c+4412,"ns_to_cycles__Vstatic__result", false,-1, 31,0);
    tracep->declBus(c+1,"nCK_to_cycles__Vstatic__result", false,-1, 31,0);
    tracep->declBus(c+5176,"get_slot__Vstatic__delay", false,-1, 31,0);
    tracep->declBus(c+5177,"get_slot__Vstatic__slot_number", false,-1, 1,0);
    tracep->declBus(c+5178,"get_slot__Vstatic__read_slot", false,-1, 1,0);
    tracep->declBus(c+5179,"get_slot__Vstatic__write_slot", false,-1, 1,0);
    tracep->declBus(c+5180,"get_slot__Vstatic__anticipate_activate_slot", false,-1, 1,0);
    tracep->declBus(c+5181,"get_slot__Vstatic__anticipate_precharge_slot", false,-1, 1,0);
    tracep->declBus(c+5182,"find_delay__Vstatic__k", false,-1, 31,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("emmcscopei ");
    tracep->declBus(c+5183,"LGMEM", false,-1, 4,0);
    tracep->declBus(c+5114,"BUSW", false,-1, 31,0);
    tracep->declBus(c+5184,"NELM", false,-1, 31,0);
    tracep->declBus(c+5070,"SYNCHRONOUS", false,-1, 0,0);
    tracep->declBus(c+5110,"HOLDOFFBITS", false,-1, 31,0);
    tracep->declBus(c+5185,"DEFAULT_HOLDOFF", false,-1, 19,0);
    tracep->declBus(c+5184,"STEP_BITS", false,-1, 31,0);
    tracep->declBus(c+5186,"MAX_STEP", false,-1, 30,0);
    tracep->declBit(c+4901,"i_data_clk", false,-1);
    tracep->declBit(c+5077,"i_ce", false,-1);
    tracep->declBit(c+516,"i_trigger", false,-1);
    tracep->declBus(c+38,"i_data", false,-1, 30,0);
    tracep->declBit(c+4901,"i_wb_clk", false,-1);
    tracep->declBit(c+4497,"i_wb_cyc", false,-1);
    tracep->declBit(c+4498,"i_wb_stb", false,-1);
    tracep->declBit(c+4499,"i_wb_we", false,-1);
    tracep->declBit(c+4570,"i_wb_addr", false,-1);
    tracep->declBus(c+4501,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4502,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+389,"o_wb_ack", false,-1);
    tracep->declBus(c+390,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+158,"o_interrupt", false,-1);
    tracep->declBit(c+4571,"write_stb", false,-1);
    tracep->declBit(c+4572,"read_from_data", false,-1);
    tracep->declBit(c+4573,"write_to_control", false,-1);
    tracep->declBus(c+390,"o_bus_data", false,-1, 31,0);
    tracep->declBit(c+4901,"bus_clock", false,-1);
    tracep->declBit(c+517,"read_address", false,-1);
    tracep->declBus(c+4501,"i_bus_data", false,-1, 31,0);
    tracep->declBus(c+518,"raddr", false,-1, 11,0);
    tracep->declBus(c+519,"waddr", false,-1, 11,0);
    tracep->declBit(c+520,"bw_reset_request", false,-1);
    tracep->declBit(c+521,"bw_manual_trigger", false,-1);
    tracep->declBit(c+522,"bw_disable_trigger", false,-1);
    tracep->declBit(c+520,"bw_reset_complete", false,-1);
    tracep->declBus(c+523,"br_config", false,-1, 2,0);
    tracep->declBus(c+524,"br_holdoff", false,-1, 19,0);
    tracep->declBus(c+525,"holdoff_counter", false,-1, 19,0);
    tracep->declBit(c+520,"dw_reset", false,-1);
    tracep->declBit(c+521,"dw_manual_trigger", false,-1);
    tracep->declBit(c+522,"dw_disable_trigger", false,-1);
    tracep->declBit(c+526,"dr_triggered", false,-1);
    tracep->declBit(c+527,"dr_primed", false,-1);
    tracep->declBit(c+528,"dw_trigger", false,-1);
    tracep->declBit(c+529,"dr_stopped", false,-1);
    tracep->declBus(c+5154,"DLYSTOP", false,-1, 31,0);
    tracep->declBus(c+530,"dr_stop_pipe", false,-1, 4,0);
    tracep->declBit(c+531,"dw_final_stop", false,-1);
    tracep->declBus(c+532,"ck_addr", false,-1, 30,0);
    tracep->declBus(c+533,"qd_data", false,-1, 30,0);
    tracep->declBit(c+534,"dr_force_write", false,-1);
    tracep->declBit(c+535,"dr_run_timeout", false,-1);
    tracep->declBit(c+536,"new_data", false,-1);
    tracep->declBit(c+537,"dr_force_inhibit", false,-1);
    tracep->declBus(c+533,"w_data", false,-1, 30,0);
    tracep->declBit(c+538,"imm_adr", false,-1);
    tracep->declBit(c+539,"lst_adr", false,-1);
    tracep->declBus(c+540,"lst_val", false,-1, 30,0);
    tracep->declBus(c+541,"imm_val", false,-1, 30,0);
    tracep->declBit(c+542,"record_ce", false,-1);
    tracep->declBus(c+543,"r_data", false,-1, 31,0);
    tracep->declBit(c+531,"bw_stopped", false,-1);
    tracep->declBit(c+526,"bw_triggered", false,-1);
    tracep->declBit(c+527,"bw_primed", false,-1);
    tracep->declBit(c+389,"br_wb_ack", false,-1);
    tracep->declBit(c+544,"br_pre_wb_ack", false,-1);
    tracep->declBit(c+4498,"bw_cyc_stb", false,-1);
    tracep->declBus(c+545,"this_addr", false,-1, 11,0);
    tracep->declBus(c+546,"nxt_mem", false,-1, 31,0);
    tracep->declBus(c+524,"full_holdoff", false,-1, 19,0);
    tracep->declBus(c+5183,"bw_lgmem", false,-1, 4,0);
    tracep->declBit(c+547,"br_level_interrupt", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("genbus ");
    tracep->declBus(c+5073,"LGWATCHDOG", false,-1, 31,0);
    tracep->declBus(c+5153,"LGINPUT_FIFO", false,-1, 31,0);
    tracep->declBus(c+5061,"LGOUTPUT_FIFO", false,-1, 31,0);
    tracep->declBus(c+5113,"CMD_PORT_OFF_UNTIL_ACCESSED", false,-1, 0,0);
    tracep->declBus(c+5187,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+192,"i_rx_stb", false,-1);
    tracep->declBus(c+190,"i_rx_data", false,-1, 7,0);
    tracep->declBit(c+410,"o_wb_cyc", false,-1);
    tracep->declBit(c+411,"o_wb_stb", false,-1);
    tracep->declBit(c+412,"o_wb_we", false,-1);
    tracep->declBus(c+436,"o_wb_addr", false,-1, 29,0);
    tracep->declBus(c+414,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+415,"i_wb_stall", false,-1);
    tracep->declBit(c+416,"i_wb_ack", false,-1);
    tracep->declBus(c+418,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+417,"i_wb_err", false,-1);
    tracep->declBit(c+189,"i_interrupt", false,-1);
    tracep->declBit(c+193,"o_tx_stb", false,-1);
    tracep->declBus(c+191,"o_tx_data", false,-1, 7,0);
    tracep->declBit(c+194,"i_tx_busy", false,-1);
    tracep->declBit(c+181,"i_console_stb", false,-1);
    tracep->declBus(c+184,"i_console_data", false,-1, 6,0);
    tracep->declBit(c+182,"o_console_busy", false,-1);
    tracep->declBit(c+180,"o_console_stb", false,-1);
    tracep->declBus(c+183,"o_console_data", false,-1, 6,0);
    tracep->declBit(c+195,"o_dbg", false,-1);
    tracep->declBit(c+548,"soft_reset", false,-1);
    tracep->declBit(c+195,"r_wdt_reset", false,-1);
    tracep->declBit(c+5077,"cmd_port_active", false,-1);
    tracep->declBit(c+549,"rx_valid", false,-1);
    tracep->declBus(c+550,"rx_data", false,-1, 7,0);
    tracep->declBit(c+551,"in_stb", false,-1);
    tracep->declBit(c+552,"in_active", false,-1);
    tracep->declQuad(c+553,"in_word", false,-1, 35,0);
    tracep->declBit(c+193,"ps_full", false,-1);
    tracep->declBus(c+191,"ps_data", false,-1, 7,0);
    tracep->declBit(c+555,"wbu_tx_stb", false,-1);
    tracep->declBus(c+556,"wbu_tx_data", false,-1, 7,0);
    tracep->declBit(c+557,"ififo_valid", false,-1);
    tracep->declQuad(c+558,"ififo_codword", false,-1, 35,0);
    tracep->declBit(c+560,"exec_stb", false,-1);
    tracep->declQuad(c+561,"exec_word", false,-1, 35,0);
    tracep->declBit(c+563,"ofifo_rd", false,-1);
    tracep->declQuad(c+564,"ofifo_codword", false,-1, 35,0);
    tracep->declBit(c+566,"ofifo_err", false,-1);
    tracep->declBit(c+567,"ofifo_empty_n", false,-1);
    tracep->declBit(c+568,"w_bus_busy", false,-1);
    tracep->declBit(c+195,"w_bus_reset", false,-1);
    tracep->declBus(c+569,"r_wdt_timer", false,-1, 18,0);
    tracep->declBit(c+570,"ign_input_busy", false,-1);
    tracep->declBit(c+571,"output_busy", false,-1);
    tracep->declBit(c+572,"out_active", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_OUTBOUND_FIFO ");
    tracep->pushNamePrefix("busoutfifo ");
    tracep->declBus(c+5188,"BW", false,-1, 31,0);
    tracep->declBus(c+5061,"LGFLEN", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+195,"i_reset", false,-1);
    tracep->declBit(c+560,"i_wr", false,-1);
    tracep->declQuad(c+561,"i_data", false,-1, 35,0);
    tracep->declBit(c+563,"i_rd", false,-1);
    tracep->declQuad(c+564,"o_data", false,-1, 35,0);
    tracep->declBit(c+567,"o_empty_n", false,-1);
    tracep->declBit(c+566,"o_err", false,-1);
    tracep->declBus(c+5189,"FLEN", false,-1, 31,0);
    tracep->declBus(c+573,"r_wrptr", false,-1, 10,0);
    tracep->declBus(c+574,"r_rdptr", false,-1, 10,0);
    tracep->declBus(c+575,"nxt_wrptr", false,-1, 10,0);
    tracep->declBus(c+576,"nxt_rdptr", false,-1, 10,0);
    tracep->declBit(c+577,"will_overflow", false,-1);
    tracep->declBit(c+578,"will_underflow", false,-1);
    tracep->declBit(c+579,"r_empty_n", false,-1);
    tracep->declBit(c+580,"w_write", false,-1);
    tracep->declBit(c+581,"w_read", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("INPUT_FIFO ");
    tracep->declBit(c+557,"ififo_empty_n", false,-1);
    tracep->declBit(c+582,"ififo_err", false,-1);
    tracep->declBit(c+583,"ififo_rd", false,-1);
    tracep->declBit(c+5074,"gen_unused", false,-1);
    tracep->pushNamePrefix("padififo ");
    tracep->declBus(c+5188,"BW", false,-1, 31,0);
    tracep->declBus(c+5153,"LGFLEN", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+195,"i_reset", false,-1);
    tracep->declBit(c+551,"i_wr", false,-1);
    tracep->declQuad(c+553,"i_data", false,-1, 35,0);
    tracep->declBit(c+583,"i_rd", false,-1);
    tracep->declQuad(c+558,"o_data", false,-1, 35,0);
    tracep->declBit(c+557,"o_empty_n", false,-1);
    tracep->declBit(c+582,"o_err", false,-1);
    tracep->declBus(c+5120,"FLEN", false,-1, 31,0);
    tracep->declBus(c+584,"r_wrptr", false,-1, 6,0);
    tracep->declBus(c+585,"r_rdptr", false,-1, 6,0);
    tracep->declBus(c+586,"nxt_wrptr", false,-1, 6,0);
    tracep->declBus(c+587,"nxt_rdptr", false,-1, 6,0);
    tracep->declBit(c+588,"will_overflow", false,-1);
    tracep->declBit(c+589,"will_underflow", false,-1);
    tracep->declBit(c+590,"r_empty_n", false,-1);
    tracep->declBit(c+591,"w_write", false,-1);
    tracep->declBit(c+592,"w_read", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("getinput ");
    tracep->declBus(c+5070,"OPT_COMPRESSION", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+549,"i_stb", false,-1);
    tracep->declBit(c+570,"o_busy", false,-1);
    tracep->declBus(c+550,"i_byte", false,-1, 7,0);
    tracep->declBit(c+548,"o_soft_reset", false,-1);
    tracep->declBit(c+551,"o_stb", false,-1);
    tracep->declBit(c+5074,"i_busy", false,-1);
    tracep->declQuad(c+553,"o_codword", false,-1, 35,0);
    tracep->declBit(c+552,"o_active", false,-1);
    tracep->declBit(c+593,"hx_stb", false,-1);
    tracep->declBit(c+594,"hx_valid", false,-1);
    tracep->declBus(c+595,"hx_hexbits", false,-1, 5,0);
    tracep->declBit(c+596,"cw_stb", false,-1);
    tracep->declBit(c+597,"cw_busy", false,-1);
    tracep->declBit(c+598,"cw_active", false,-1);
    tracep->declQuad(c+599,"cw_word", false,-1, 35,0);
    tracep->declBit(c+601,"cod_busy", false,-1);
    tracep->declBit(c+602,"cod_active", false,-1);
    tracep->pushNamePrefix("GEN_COMPRESSION ");
    tracep->pushNamePrefix("unpack ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+596,"i_stb", false,-1);
    tracep->declBit(c+601,"o_busy", false,-1);
    tracep->declQuad(c+599,"i_word", false,-1, 35,0);
    tracep->declBit(c+551,"o_stb", false,-1);
    tracep->declBit(c+5074,"i_busy", false,-1);
    tracep->declQuad(c+553,"o_word", false,-1, 35,0);
    tracep->declBit(c+602,"o_active", false,-1);
    tracep->declBus(c+603,"wr_addr", false,-1, 7,0);
    tracep->declQuad(c+604,"r_word", false,-1, 35,0);
    tracep->declBus(c+606,"cmd_addr", false,-1, 7,0);
    tracep->declBus(c+607,"r_addr", false,-1, 24,0);
    tracep->declBus(c+608,"w_addr", false,-1, 31,0);
    tracep->declBus(c+609,"rd_len", false,-1, 9,0);
    tracep->declBus(c+610,"cword", false,-1, 31,0);
    tracep->declBus(c+611,"r_stb", false,-1, 2,0);
    tracep->declBit(c+612,"cmd_write_not_compressed", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("formcw ");
    tracep->declBus(c+5113,"OPT_SKIDBUFFER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+593,"i_stb", false,-1);
    tracep->declBit(c+597,"o_busy", false,-1);
    tracep->declBit(c+594,"i_valid", false,-1);
    tracep->declBus(c+595,"i_hexbits", false,-1, 5,0);
    tracep->declBit(c+596,"o_stb", false,-1);
    tracep->declBit(c+601,"i_busy", false,-1);
    tracep->declQuad(c+599,"o_codword", false,-1, 35,0);
    tracep->declBit(c+598,"o_active", false,-1);
    tracep->declBus(c+613,"r_len", false,-1, 2,0);
    tracep->declBus(c+614,"cw_len", false,-1, 2,0);
    tracep->declBus(c+615,"lastcw", false,-1, 1,0);
    tracep->declBit(c+616,"w_stb", false,-1);
    tracep->declQuad(c+617,"shiftreg", false,-1, 35,0);
    tracep->declBit(c+593,"skd_stb", false,-1);
    tracep->declBit(c+594,"skd_valid", false,-1);
    tracep->declBus(c+595,"skd_hexbits", false,-1, 5,0);
    tracep->declBit(c+597,"skd_busy", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("tobits ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+549,"i_stb", false,-1);
    tracep->declBit(c+570,"o_busy", false,-1);
    tracep->declBus(c+550,"i_byte", false,-1, 7,0);
    tracep->declBit(c+548,"o_soft_reset", false,-1);
    tracep->declBit(c+593,"o_stb", false,-1);
    tracep->declBit(c+594,"o_valid", false,-1);
    tracep->declBit(c+597,"i_busy", false,-1);
    tracep->declBus(c+595,"o_hexbits", false,-1, 5,0);
    tracep->declBus(c+2,"k", false,-1, 31,0);
    tracep->declBus(c+3,"newv", false,-1, 6,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("runwb ");
    tracep->declBus(c+5113,"OPT_COUNT_FIFO", false,-1, 0,0);
    tracep->declBus(c+5065,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5187,"AW", false,-1, 31,0);
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+195,"i_reset", false,-1);
    tracep->declBit(c+557,"i_valid", false,-1);
    tracep->declQuad(c+558,"i_codword", false,-1, 35,0);
    tracep->declBit(c+568,"o_busy", false,-1);
    tracep->declBit(c+410,"o_wb_cyc", false,-1);
    tracep->declBit(c+411,"o_wb_stb", false,-1);
    tracep->declBit(c+412,"o_wb_we", false,-1);
    tracep->declBus(c+436,"o_wb_addr", false,-1, 29,0);
    tracep->declBus(c+414,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+415,"i_wb_stall", false,-1);
    tracep->declBit(c+416,"i_wb_ack", false,-1);
    tracep->declBus(c+418,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+417,"i_wb_err", false,-1);
    tracep->declBit(c+560,"o_stb", false,-1);
    tracep->declQuad(c+561,"o_codword", false,-1, 35,0);
    tracep->declBit(c+563,"i_fifo_rd", false,-1);
    tracep->declBus(c+5116,"WB_IDLE", false,-1, 1,0);
    tracep->declBus(c+5117,"WB_READ_REQUEST", false,-1, 1,0);
    tracep->declBus(c+5118,"WB_WRITE_REQUEST", false,-1, 1,0);
    tracep->declBus(c+5119,"WB_FLUSH_WRITE_REQUESTS", false,-1, 1,0);
    tracep->declBus(c+5117,"WRITE_PREFIX", false,-1, 1,0);
    tracep->declBus(c+619,"w_cod_data", false,-1, 31,0);
    tracep->declBus(c+620,"wb_state", false,-1, 1,0);
    tracep->declBus(c+621,"r_acks_needed", false,-1, 9,0);
    tracep->declBus(c+622,"r_len", false,-1, 9,0);
    tracep->declBit(c+623,"r_inc", false,-1);
    tracep->declBit(c+624,"r_new_addr", false,-1);
    tracep->declBit(c+625,"last_read_request", false,-1);
    tracep->declBit(c+626,"last_ack", false,-1);
    tracep->declBit(c+627,"zero_acks", false,-1);
    tracep->declBit(c+568,"r_busy", false,-1);
    tracep->declBus(c+628,"wide_addr", false,-1, 31,0);
    tracep->declBus(c+5190,"fifo_space_available", false,-1, 4,0);
    tracep->declBit(c+5077,"space_available", false,-1);
    tracep->pushNamePrefix("NO_FIFO ");
    tracep->declBit(c+5074,"unused_count", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("wroutput ");
    tracep->declBus(c+5070,"OPT_COMPRESSION", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_IDLES", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+195,"i_soft_reset", false,-1);
    tracep->declBit(c+563,"i_stb", false,-1);
    tracep->declBit(c+571,"o_busy", false,-1);
    tracep->declQuad(c+564,"i_codword", false,-1, 35,0);
    tracep->declBit(c+410,"i_wb_cyc", false,-1);
    tracep->declBit(c+189,"i_int", false,-1);
    tracep->declBit(c+629,"i_bus_busy", false,-1);
    tracep->declBit(c+555,"o_stb", false,-1);
    tracep->declBit(c+572,"o_active", false,-1);
    tracep->declBus(c+556,"o_char", false,-1, 7,0);
    tracep->declBit(c+193,"i_tx_busy", false,-1);
    tracep->declBit(c+630,"dw_busy", false,-1);
    tracep->declBit(c+571,"cw_stb", false,-1);
    tracep->declBit(c+571,"cw_busy", false,-1);
    tracep->declBit(c+631,"cp_stb", false,-1);
    tracep->declBit(c+630,"dw_stb", false,-1);
    tracep->declBit(c+632,"ln_stb", false,-1);
    tracep->declBit(c+633,"ln_busy", false,-1);
    tracep->declBit(c+634,"cp_busy", false,-1);
    tracep->declBit(c+635,"byte_busy", false,-1);
    tracep->declBit(c+636,"cp_active", false,-1);
    tracep->declBit(c+637,"dw_active", false,-1);
    tracep->declBit(c+638,"ln_active", false,-1);
    tracep->declQuad(c+639,"cw_codword", false,-1, 35,0);
    tracep->declQuad(c+641,"cp_word", false,-1, 35,0);
    tracep->declBus(c+643,"dw_bits", false,-1, 6,0);
    tracep->declBus(c+644,"ln_bits", false,-1, 6,0);
    tracep->declBit(c+645,"r_active", false,-1);
    tracep->pushNamePrefix("GEN_COMPRESSION ");
    tracep->pushNamePrefix("packit ");
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declBus(c+5188,"CW", false,-1, 31,0);
    tracep->declBus(c+5061,"TBITS", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+195,"i_reset", false,-1);
    tracep->declBit(c+571,"i_stb", false,-1);
    tracep->declQuad(c+639,"i_codword", false,-1, 35,0);
    tracep->declBit(c+630,"i_busy", false,-1);
    tracep->declBit(c+631,"o_stb", false,-1);
    tracep->declQuad(c+641,"o_cword", false,-1, 35,0);
    tracep->declBit(c+634,"o_busy", false,-1);
    tracep->declBit(c+636,"o_active", false,-1);
    tracep->declBit(c+646,"aword_valid", false,-1);
    tracep->declQuad(c+647,"a_addrword", false,-1, 35,0);
    tracep->declBus(c+649,"w_addr", false,-1, 31,0);
    tracep->declBus(c+650,"addr_zcheck", false,-1, 3,0);
    tracep->declBit(c+651,"tbl_busy", false,-1);
    tracep->declBit(c+652,"w_accepted", false,-1);
    tracep->declQuad(c+653,"r_word", false,-1, 35,0);
    tracep->declBus(c+655,"tbl_addr", false,-1, 9,0);
    tracep->declBit(c+656,"tbl_filled", false,-1);
    tracep->declBus(c+657,"rd_addr", false,-1, 9,0);
    tracep->declBit(c+658,"pmatch", false,-1);
    tracep->declBit(c+659,"dmatch", false,-1);
    tracep->declBit(c+660,"vaddr", false,-1);
    tracep->declBus(c+661,"cword", false,-1, 31,0);
    tracep->declBus(c+662,"maddr", false,-1, 9,0);
    tracep->declBit(c+663,"matched", false,-1);
    tracep->declBit(c+664,"zmatch", false,-1);
    tracep->declBit(c+665,"hmatch", false,-1);
    tracep->declBus(c+666,"adr_dbld", false,-1, 9,0);
    tracep->declBus(c+667,"adr_hlfd", false,-1, 2,0);
    tracep->declQuad(c+641,"r_cword", false,-1, 35,0);
    tracep->declBus(c+668,"dffaddr", false,-1, 9,0);
    tracep->declBit(c+669,"clear_table", false,-1);
    tracep->declBit(c+670,"addr_within_table", false,-1);
    tracep->declBit(c+671,"w_match", false,-1);
    tracep->declBus(c+4,"k", false,-1, 31,0);
    tracep->declBit(c+672,"unused", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("GEN_IDLES ");
    tracep->pushNamePrefix("buildcw ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+195,"i_reset", false,-1);
    tracep->declBit(c+563,"i_stb", false,-1);
    tracep->declQuad(c+564,"i_codword", false,-1, 35,0);
    tracep->declBit(c+410,"i_cyc", false,-1);
    tracep->declBit(c+629,"i_busy", false,-1);
    tracep->declBit(c+189,"i_int", false,-1);
    tracep->declBit(c+571,"o_stb", false,-1);
    tracep->declQuad(c+639,"o_codword", false,-1, 35,0);
    tracep->declBit(c+571,"o_busy", false,-1);
    tracep->declBit(c+673,"i_tx_busy", false,-1);
    tracep->declQuad(c+5191,"CW_INTERRUPT", false,-1, 35,0);
    tracep->declQuad(c+5193,"CW_BUSBUSY", false,-1, 35,0);
    tracep->declQuad(c+5195,"CW_IDLE", false,-1, 35,0);
    tracep->declBus(c+5068,"IDLEBITS", false,-1, 31,0);
    tracep->declBit(c+674,"int_request", false,-1);
    tracep->declBit(c+675,"int_sent", false,-1);
    tracep->declBit(c+676,"idle_expired", false,-1);
    tracep->declBit(c+677,"idle_state", false,-1);
    tracep->declBus(c+678,"idle_counter", false,-1, 21,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("deword ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+631,"i_stb", false,-1);
    tracep->declQuad(c+641,"i_word", false,-1, 35,0);
    tracep->declBit(c+633,"i_tx_busy", false,-1);
    tracep->declBit(c+630,"o_stb", false,-1);
    tracep->declBus(c+643,"o_nl_hexbits", false,-1, 6,0);
    tracep->declBit(c+630,"o_busy", false,-1);
    tracep->declBit(c+637,"o_active", false,-1);
    tracep->declBus(c+679,"w_len", false,-1, 2,0);
    tracep->declBus(c+680,"r_len", false,-1, 2,0);
    tracep->declBus(c+681,"r_word", false,-1, 29,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("linepacker ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+630,"i_stb", false,-1);
    tracep->declBus(c+643,"i_nl_hexbits", false,-1, 6,0);
    tracep->declBit(c+632,"o_stb", false,-1);
    tracep->declBus(c+644,"o_nl_hexbits", false,-1, 6,0);
    tracep->declBit(c+682,"i_bus_busy", false,-1);
    tracep->declBit(c+635,"i_tx_busy", false,-1);
    tracep->declBit(c+633,"o_busy", false,-1);
    tracep->declBit(c+638,"o_active", false,-1);
    tracep->declBus(c+5197,"MAX_LINE_LENGTH", false,-1, 6,0);
    tracep->declBus(c+5198,"TRIGGER_LENGTH", false,-1, 6,0);
    tracep->declBit(c+683,"last_out_nl", false,-1);
    tracep->declBit(c+684,"last_in_nl", false,-1);
    tracep->declBit(c+685,"full_line", false,-1);
    tracep->declBit(c+686,"r_busy", false,-1);
    tracep->declBus(c+687,"linelen", false,-1, 6,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("mkbytes ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+632,"i_stb", false,-1);
    tracep->declBus(c+644,"i_bits", false,-1, 6,0);
    tracep->declBit(c+555,"o_stb", false,-1);
    tracep->declBus(c+556,"o_char", false,-1, 7,0);
    tracep->declBit(c+635,"o_busy", false,-1);
    tracep->declBit(c+193,"i_busy", false,-1);
    tracep->declBus(c+5,"newv", false,-1, 6,0);
    tracep->declBus(c+6,"k", false,-1, 31,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("gpioi ");
    tracep->declBus(c+5069,"NIN", false,-1, 31,0);
    tracep->declBus(c+5063,"NOUT", false,-1, 31,0);
    tracep->declBus(c+5109,"DEFAULT", false,-1, 7,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4488,"i_wb_cyc", false,-1);
    tracep->declBit(c+4493,"i_wb_stb", false,-1);
    tracep->declBit(c+4490,"i_wb_we", false,-1);
    tracep->declBus(c+4491,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4492,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+4493,"o_wb_ack", false,-1);
    tracep->declBus(c+5010,"o_wb_data", false,-1, 31,0);
    tracep->declBus(c+5003,"i_gpio", false,-1, 15,0);
    tracep->declBus(c+5004,"o_gpio", false,-1, 7,0);
    tracep->declBit(c+167,"o_int", false,-1);
    tracep->declBus(c+688,"r_gpio", false,-1, 15,0);
    tracep->declBus(c+689,"x_gpio", false,-1, 15,0);
    tracep->declBus(c+690,"q_gpio", false,-1, 15,0);
    tracep->declBus(c+688,"hi_bits", false,-1, 15,0);
    tracep->declBus(c+5014,"low_bits", false,-1, 15,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("i2ci ");
    tracep->declBus(c+5068,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"DATA_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5063,"I2C_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5075,"AXIS_ID_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5116,"DEF_CHANNEL", false,-1, 1,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5063,"RW", false,-1, 31,0);
    tracep->declBus(c+5199,"BAW", false,-1, 31,0);
    tracep->declBus(c+5200,"RESET_ADDRESS", false,-1, 27,0);
    tracep->declBus(c+5070,"OPT_START_HALTED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_MANUAL", false,-1, 0,0);
    tracep->declBus(c+5076,"OPT_WATCHDOG", false,-1, 31,0);
    tracep->declBus(c+5201,"DEF_CKCOUNT", false,-1, 11,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4515,"i_wb_cyc", false,-1);
    tracep->declBit(c+4516,"i_wb_stb", false,-1);
    tracep->declBit(c+4517,"i_wb_we", false,-1);
    tracep->declBus(c+4574,"i_wb_addr", false,-1, 1,0);
    tracep->declBus(c+4519,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4520,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+395,"o_wb_ack", false,-1);
    tracep->declBus(c+396,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+239,"o_pf_cyc", false,-1);
    tracep->declBit(c+240,"o_pf_stb", false,-1);
    tracep->declBit(c+5074,"o_pf_we", false,-1);
    tracep->declBus(c+241,"o_pf_addr", false,-1, 21,0);
    tracep->declArray(c+5078,"o_pf_data", false,-1, 511,0);
    tracep->declQuad(c+5094,"o_pf_sel", false,-1, 63,0);
    tracep->declBit(c+242,"i_pf_stall", false,-1);
    tracep->declBit(c+243,"i_pf_ack", false,-1);
    tracep->declBit(c+244,"i_pf_err", false,-1);
    tracep->declArray(c+245,"i_pf_data", false,-1, 511,0);
    tracep->declBit(c+4975,"i_i2c_sda", false,-1);
    tracep->declBit(c+4976,"i_i2c_scl", false,-1);
    tracep->declBit(c+4977,"o_i2c_sda", false,-1);
    tracep->declBit(c+4978,"o_i2c_scl", false,-1);
    tracep->declBit(c+174,"M_AXIS_TVALID", false,-1);
    tracep->declBit(c+175,"M_AXIS_TREADY", false,-1);
    tracep->declBus(c+177,"M_AXIS_TDATA", false,-1, 7,0);
    tracep->declBit(c+176,"M_AXIS_TLAST", false,-1);
    tracep->declBus(c+178,"M_AXIS_TID", false,-1, 1,0);
    tracep->declBit(c+5074,"i_sync_signal", false,-1);
    tracep->declBus(c+37,"o_debug", false,-1, 31,0);
    tracep->declBus(c+5116,"ADR_CONTROL", false,-1, 1,0);
    tracep->declBus(c+5117,"ADR_OVERRIDE", false,-1, 1,0);
    tracep->declBus(c+5118,"ADR_ADDRESS", false,-1, 1,0);
    tracep->declBus(c+5119,"ADR_CKCOUNT", false,-1, 1,0);
    tracep->declBus(c+5073,"HALT_BIT", false,-1, 31,0);
    tracep->declBus(c+5110,"ERR_BIT", false,-1, 31,0);
    tracep->declBus(c+5121,"ABORT_BIT", false,-1, 31,0);
    tracep->declBus(c+5068,"SOFTHALT_BIT", false,-1, 31,0);
    tracep->declBus(c+5156,"OVW_VALID", false,-1, 31,0);
    tracep->declBus(c+5157,"MANUAL_BIT", false,-1, 31,0);
    tracep->declBus(c+5122,"CMD_NOOP", false,-1, 3,0);
    tracep->declBus(c+5124,"CMD_STOP", false,-1, 3,0);
    tracep->declBus(c+5125,"CMD_SEND", false,-1, 3,0);
    tracep->declBus(c+5126,"CMD_RXK", false,-1, 3,0);
    tracep->declBus(c+5127,"CMD_RXN", false,-1, 3,0);
    tracep->declBus(c+5115,"CMD_RXLK", false,-1, 3,0);
    tracep->declBus(c+5128,"CMD_RXLN", false,-1, 3,0);
    tracep->declBus(c+5129,"CMD_WAIT", false,-1, 3,0);
    tracep->declBus(c+5202,"CMD_HALT", false,-1, 3,0);
    tracep->declBus(c+5203,"CMD_ABORT", false,-1, 3,0);
    tracep->declBus(c+5204,"CMD_TARGET", false,-1, 3,0);
    tracep->declBus(c+5205,"CMD_JUMP", false,-1, 3,0);
    tracep->declBus(c+5206,"CMD_CHANNEL", false,-1, 3,0);
    tracep->declBit(c+691,"cpu_reset", false,-1);
    tracep->declBit(c+5074,"cpu_clear_cache", false,-1);
    tracep->declBit(c+692,"cpu_new_pc", false,-1);
    tracep->declBus(c+693,"pf_jump_addr", false,-1, 27,0);
    tracep->declBit(c+694,"pf_valid", false,-1);
    tracep->declBit(c+695,"pf_ready", false,-1);
    tracep->declBus(c+696,"pf_insn", false,-1, 7,0);
    tracep->declBus(c+697,"pf_insn_addr", false,-1, 27,0);
    tracep->declBit(c+698,"pf_illegal", false,-1);
    tracep->declBit(c+699,"half_valid", false,-1);
    tracep->declBit(c+700,"imm_cycle", false,-1);
    tracep->declBit(c+4575,"next_valid", false,-1);
    tracep->declBus(c+4576,"next_insn", false,-1, 7,0);
    tracep->declBit(c+701,"insn_ready", false,-1);
    tracep->declBit(c+702,"half_ready", false,-1);
    tracep->declBit(c+703,"i2c_abort", false,-1);
    tracep->declBit(c+704,"insn_valid", false,-1);
    tracep->declBus(c+705,"insn", false,-1, 11,0);
    tracep->declBus(c+706,"half_insn", false,-1, 3,0);
    tracep->declBit(c+707,"i2c_ckedge", false,-1);
    tracep->declBit(c+708,"i2c_stretch", false,-1);
    tracep->declBus(c+709,"i2c_ckcount", false,-1, 11,0);
    tracep->declBus(c+710,"ckcount", false,-1, 11,0);
    tracep->declBus(c+711,"abort_address", false,-1, 27,0);
    tracep->declBus(c+712,"jump_target", false,-1, 27,0);
    tracep->declBit(c+713,"r_wait", false,-1);
    tracep->declBit(c+714,"soft_halt_request", false,-1);
    tracep->declBit(c+691,"r_halted", false,-1);
    tracep->declBit(c+715,"r_err", false,-1);
    tracep->declBit(c+716,"r_aborted", false,-1);
    tracep->declBit(c+717,"r_manual", false,-1);
    tracep->declBit(c+718,"r_sda", false,-1);
    tracep->declBit(c+719,"r_scl", false,-1);
    tracep->declBit(c+720,"w_stopped", false,-1);
    tracep->declBit(c+721,"w_sda", false,-1);
    tracep->declBit(c+722,"w_scl", false,-1);
    tracep->declBit(c+4577,"bus_read", false,-1);
    tracep->declBit(c+4578,"bus_write", false,-1);
    tracep->declBit(c+4579,"bus_override", false,-1);
    tracep->declBit(c+4580,"bus_manual", false,-1);
    tracep->declBit(c+723,"ovw_ready", false,-1);
    tracep->declBit(c+4581,"bus_jump", false,-1);
    tracep->declBus(c+4574,"bus_write_addr", false,-1, 1,0);
    tracep->declBus(c+4574,"bus_read_addr", false,-1, 1,0);
    tracep->declBus(c+4519,"bus_write_data", false,-1, 31,0);
    tracep->declBus(c+4520,"bus_write_strb", false,-1, 3,0);
    tracep->declBus(c+396,"bus_read_data", false,-1, 31,0);
    tracep->declBit(c+724,"s_tvalid", false,-1);
    tracep->declBit(c+702,"s_tready", false,-1);
    tracep->declBus(c+725,"ovw_data", false,-1, 9,0);
    tracep->declBus(c+39,"w_control", false,-1, 31,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_MANUAL ");
    tracep->declBit(c+717,"manual", false,-1);
    tracep->declBit(c+719,"scl", false,-1);
    tracep->declBit(c+718,"sda", false,-1);
    tracep->declBit(c+726,"o_scl", false,-1);
    tracep->declBit(c+727,"o_sda", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_TID ");
    tracep->declBit(c+728,"mid_axis_pkt", false,-1);
    tracep->declBus(c+729,"r_channel", false,-1, 1,0);
    tracep->declBus(c+178,"axis_tid", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_axisi2c ");
    tracep->declBus(c+5076,"OPT_WATCHDOG", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"S_AXI_ACLK", false,-1);
    tracep->declBit(c+40,"S_AXI_ARESETN", false,-1);
    tracep->declBit(c+724,"S_AXIS_TVALID", false,-1);
    tracep->declBit(c+701,"S_AXIS_TREADY", false,-1);
    tracep->declBus(c+730,"S_AXIS_TDATA", false,-1, 10,0);
    tracep->declBit(c+174,"M_AXIS_TVALID", false,-1);
    tracep->declBit(c+175,"M_AXIS_TREADY", false,-1);
    tracep->declBus(c+177,"M_AXIS_TDATA", false,-1, 7,0);
    tracep->declBit(c+176,"M_AXIS_TLAST", false,-1);
    tracep->declBit(c+707,"i_ckedge", false,-1);
    tracep->declBit(c+708,"o_stretch", false,-1);
    tracep->declBit(c+4976,"i_scl", false,-1);
    tracep->declBit(c+4975,"i_sda", false,-1);
    tracep->declBit(c+722,"o_scl", false,-1);
    tracep->declBit(c+721,"o_sda", false,-1);
    tracep->declBit(c+703,"o_abort", false,-1);
    tracep->declBus(c+5122,"IDLE_STOPPED", false,-1, 3,0);
    tracep->declBus(c+5123,"START", false,-1, 3,0);
    tracep->declBus(c+5124,"IDLE_ACTIVE", false,-1, 3,0);
    tracep->declBus(c+5125,"STOP", false,-1, 3,0);
    tracep->declBus(c+5126,"DATA", false,-1, 3,0);
    tracep->declBus(c+5127,"CLOCK", false,-1, 3,0);
    tracep->declBus(c+5115,"ACK", false,-1, 3,0);
    tracep->declBus(c+5128,"CKACKLO", false,-1, 3,0);
    tracep->declBus(c+5129,"CKACKHI", false,-1, 3,0);
    tracep->declBus(c+5202,"RXNAK", false,-1, 3,0);
    tracep->declBus(c+5203,"ABORT", false,-1, 3,0);
    tracep->declBus(c+5204,"REPEAT_START", false,-1, 3,0);
    tracep->declBus(c+5205,"REPEAT_START2", false,-1, 3,0);
    tracep->declBus(c+5113,"D_RD", false,-1, 0,0);
    tracep->declBus(c+5070,"D_WR", false,-1, 0,0);
    tracep->declBus(c+5159,"CMD_NOOP", false,-1, 2,0);
    tracep->declBus(c+5166,"CMD_START", false,-1, 2,0);
    tracep->declBus(c+5160,"CMD_STOP", false,-1, 2,0);
    tracep->declBus(c+5162,"CMD_SEND", false,-1, 2,0);
    tracep->declBus(c+5207,"CMD_RXK", false,-1, 2,0);
    tracep->declBus(c+5208,"CMD_RXN", false,-1, 2,0);
    tracep->declBus(c+5209,"CMD_RXLK", false,-1, 2,0);
    tracep->declBus(c+5210,"CMD_RXLN", false,-1, 2,0);
    tracep->declBus(c+5113,"OPT_ABORT_REQUEST", false,-1, 0,0);
    tracep->declBit(c+731,"last_byte", false,-1);
    tracep->declBit(c+732,"dir", false,-1);
    tracep->declBit(c+733,"will_ack", false,-1);
    tracep->declBus(c+734,"state", false,-1, 3,0);
    tracep->declBus(c+735,"nbits", false,-1, 2,0);
    tracep->declBus(c+736,"sreg", false,-1, 7,0);
    tracep->declBit(c+737,"q_scl", false,-1);
    tracep->declBit(c+738,"q_sda", false,-1);
    tracep->declBit(c+739,"ck_scl", false,-1);
    tracep->declBit(c+740,"ck_sda", false,-1);
    tracep->declBit(c+741,"lst_scl", false,-1);
    tracep->declBit(c+742,"lst_sda", false,-1);
    tracep->declBit(c+743,"stop_bit", false,-1);
    tracep->declBit(c+744,"channel_busy", false,-1);
    tracep->declBit(c+5074,"watchdog_timeout", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_fetch ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5063,"INSN_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"DATA_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5199,"AW", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+41,"i_reset", false,-1);
    tracep->declBit(c+692,"i_new_pc", false,-1);
    tracep->declBit(c+5074,"i_clear_cache", false,-1);
    tracep->declBit(c+695,"i_ready", false,-1);
    tracep->declBus(c+693,"i_pc", false,-1, 27,0);
    tracep->declBit(c+694,"o_valid", false,-1);
    tracep->declBit(c+698,"o_illegal", false,-1);
    tracep->declBus(c+696,"o_insn", false,-1, 7,0);
    tracep->declBus(c+697,"o_pc", false,-1, 27,0);
    tracep->declBit(c+239,"o_wb_cyc", false,-1);
    tracep->declBit(c+240,"o_wb_stb", false,-1);
    tracep->declBit(c+5074,"o_wb_we", false,-1);
    tracep->declBus(c+241,"o_wb_addr", false,-1, 21,0);
    tracep->declArray(c+5078,"o_wb_data", false,-1, 511,0);
    tracep->declBit(c+242,"i_wb_stall", false,-1);
    tracep->declBit(c+243,"i_wb_ack", false,-1);
    tracep->declBit(c+244,"i_wb_err", false,-1);
    tracep->declArray(c+245,"i_wb_data", false,-1, 511,0);
    tracep->declBit(c+745,"last_stb", false,-1);
    tracep->declBit(c+746,"invalid_bus_cycle", false,-1);
    tracep->declArray(c+747,"cache_word", false,-1, 511,0);
    tracep->declBit(c+763,"cache_valid", false,-1);
    tracep->declBus(c+764,"inflight", false,-1, 1,0);
    tracep->declBit(c+765,"cache_illegal", false,-1);
    tracep->declBit(c+766,"r_valid", false,-1);
    tracep->declArray(c+767,"r_insn", false,-1, 511,0);
    tracep->declArray(c+783,"i_wb_shifted", false,-1, 511,0);
    tracep->pushNamePrefix("GEN_SUBSHIFT ");
    tracep->declBus(c+5153,"NSHIFT", false,-1, 31,0);
    tracep->declBit(c+766,"rg_valid", false,-1);
    tracep->declArray(c+767,"rg_insn", false,-1, 511,0);
    tracep->declBus(c+799,"r_count", false,-1, 6,0);
    tracep->declBus(c+800,"r_shift", false,-1, 5,0);
    tracep->declBit(c+5074,"unused_shift", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("i2cscopei ");
    tracep->declBus(c+5211,"LGMEM", false,-1, 4,0);
    tracep->declBus(c+5114,"BUSW", false,-1, 31,0);
    tracep->declBus(c+5184,"NELM", false,-1, 31,0);
    tracep->declBus(c+5070,"SYNCHRONOUS", false,-1, 0,0);
    tracep->declBus(c+5110,"HOLDOFFBITS", false,-1, 31,0);
    tracep->declBus(c+5212,"DEFAULT_HOLDOFF", false,-1, 19,0);
    tracep->declBus(c+5184,"STEP_BITS", false,-1, 31,0);
    tracep->declBus(c+5186,"MAX_STEP", false,-1, 30,0);
    tracep->declBit(c+4901,"i_data_clk", false,-1);
    tracep->declBit(c+5077,"i_ce", false,-1);
    tracep->declBit(c+716,"i_trigger", false,-1);
    tracep->declBus(c+42,"i_data", false,-1, 30,0);
    tracep->declBit(c+4901,"i_wb_clk", false,-1);
    tracep->declBit(c+4503,"i_wb_cyc", false,-1);
    tracep->declBit(c+4504,"i_wb_stb", false,-1);
    tracep->declBit(c+4505,"i_wb_we", false,-1);
    tracep->declBit(c+4582,"i_wb_addr", false,-1);
    tracep->declBus(c+4507,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4508,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+391,"o_wb_ack", false,-1);
    tracep->declBus(c+392,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+166,"o_interrupt", false,-1);
    tracep->declBit(c+4583,"write_stb", false,-1);
    tracep->declBit(c+4584,"read_from_data", false,-1);
    tracep->declBit(c+4585,"write_to_control", false,-1);
    tracep->declBus(c+392,"o_bus_data", false,-1, 31,0);
    tracep->declBit(c+4901,"bus_clock", false,-1);
    tracep->declBit(c+801,"read_address", false,-1);
    tracep->declBus(c+4507,"i_bus_data", false,-1, 31,0);
    tracep->declBus(c+802,"raddr", false,-1, 9,0);
    tracep->declBus(c+803,"waddr", false,-1, 9,0);
    tracep->declBit(c+804,"bw_reset_request", false,-1);
    tracep->declBit(c+805,"bw_manual_trigger", false,-1);
    tracep->declBit(c+806,"bw_disable_trigger", false,-1);
    tracep->declBit(c+804,"bw_reset_complete", false,-1);
    tracep->declBus(c+807,"br_config", false,-1, 2,0);
    tracep->declBus(c+808,"br_holdoff", false,-1, 19,0);
    tracep->declBus(c+809,"holdoff_counter", false,-1, 19,0);
    tracep->declBit(c+804,"dw_reset", false,-1);
    tracep->declBit(c+805,"dw_manual_trigger", false,-1);
    tracep->declBit(c+806,"dw_disable_trigger", false,-1);
    tracep->declBit(c+810,"dr_triggered", false,-1);
    tracep->declBit(c+811,"dr_primed", false,-1);
    tracep->declBit(c+812,"dw_trigger", false,-1);
    tracep->declBit(c+813,"dr_stopped", false,-1);
    tracep->declBus(c+5154,"DLYSTOP", false,-1, 31,0);
    tracep->declBus(c+814,"dr_stop_pipe", false,-1, 4,0);
    tracep->declBit(c+815,"dw_final_stop", false,-1);
    tracep->declBus(c+816,"ck_addr", false,-1, 30,0);
    tracep->declBus(c+817,"qd_data", false,-1, 30,0);
    tracep->declBit(c+818,"dr_force_write", false,-1);
    tracep->declBit(c+819,"dr_run_timeout", false,-1);
    tracep->declBit(c+820,"new_data", false,-1);
    tracep->declBit(c+821,"dr_force_inhibit", false,-1);
    tracep->declBus(c+817,"w_data", false,-1, 30,0);
    tracep->declBit(c+822,"imm_adr", false,-1);
    tracep->declBit(c+823,"lst_adr", false,-1);
    tracep->declBus(c+824,"lst_val", false,-1, 30,0);
    tracep->declBus(c+825,"imm_val", false,-1, 30,0);
    tracep->declBit(c+826,"record_ce", false,-1);
    tracep->declBus(c+827,"r_data", false,-1, 31,0);
    tracep->declBit(c+815,"bw_stopped", false,-1);
    tracep->declBit(c+810,"bw_triggered", false,-1);
    tracep->declBit(c+811,"bw_primed", false,-1);
    tracep->declBit(c+391,"br_wb_ack", false,-1);
    tracep->declBit(c+828,"br_pre_wb_ack", false,-1);
    tracep->declBit(c+4504,"bw_cyc_stb", false,-1);
    tracep->declBus(c+829,"this_addr", false,-1, 9,0);
    tracep->declBus(c+830,"nxt_mem", false,-1, 31,0);
    tracep->declBus(c+808,"full_holdoff", false,-1, 19,0);
    tracep->declBus(c+5211,"bw_lgmem", false,-1, 4,0);
    tracep->declBit(c+831,"br_level_interrupt", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("rcv ");
    tracep->declBus(c+5072,"TIMER_BITS", false,-1, 31,0);
    tracep->declBus(c+5213,"CLOCKS_PER_BAUD", false,-1, 6,0);
    tracep->declBus(c+5072,"TB", false,-1, 31,0);
    tracep->declBus(c+5122,"RXUL_BIT_ZERO", false,-1, 3,0);
    tracep->declBus(c+5123,"RXUL_BIT_ONE", false,-1, 3,0);
    tracep->declBus(c+5124,"RXUL_BIT_TWO", false,-1, 3,0);
    tracep->declBus(c+5125,"RXUL_BIT_THREE", false,-1, 3,0);
    tracep->declBus(c+5126,"RXUL_BIT_FOUR", false,-1, 3,0);
    tracep->declBus(c+5127,"RXUL_BIT_FIVE", false,-1, 3,0);
    tracep->declBus(c+5115,"RXUL_BIT_SIX", false,-1, 3,0);
    tracep->declBus(c+5128,"RXUL_BIT_SEVEN", false,-1, 3,0);
    tracep->declBus(c+5129,"RXUL_STOP", false,-1, 3,0);
    tracep->declBus(c+5202,"RXUL_WAIT", false,-1, 3,0);
    tracep->declBus(c+5108,"RXUL_IDLE", false,-1, 3,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5000,"i_uart_rx", false,-1);
    tracep->declBit(c+192,"o_wr", false,-1);
    tracep->declBus(c+190,"o_data", false,-1, 7,0);
    tracep->declBus(c+5214,"half_baud", false,-1, 6,0);
    tracep->declBus(c+832,"state", false,-1, 3,0);
    tracep->declBus(c+833,"baud_counter", false,-1, 6,0);
    tracep->declBit(c+834,"zero_baud_counter", false,-1);
    tracep->declBit(c+835,"q_uart", false,-1);
    tracep->declBit(c+836,"qq_uart", false,-1);
    tracep->declBit(c+837,"ck_uart", false,-1);
    tracep->declBus(c+838,"chg_counter", false,-1, 6,0);
    tracep->declBit(c+839,"half_baud_time", false,-1);
    tracep->declBus(c+840,"data_reg", false,-1, 7,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("sdioscopei ");
    tracep->declBus(c+5183,"LGMEM", false,-1, 4,0);
    tracep->declBus(c+5114,"BUSW", false,-1, 31,0);
    tracep->declBus(c+5184,"NELM", false,-1, 31,0);
    tracep->declBus(c+5070,"SYNCHRONOUS", false,-1, 0,0);
    tracep->declBus(c+5110,"HOLDOFFBITS", false,-1, 31,0);
    tracep->declBus(c+5185,"DEFAULT_HOLDOFF", false,-1, 19,0);
    tracep->declBus(c+5184,"STEP_BITS", false,-1, 31,0);
    tracep->declBus(c+5186,"MAX_STEP", false,-1, 30,0);
    tracep->declBit(c+4901,"i_data_clk", false,-1);
    tracep->declBit(c+5077,"i_ce", false,-1);
    tracep->declBit(c+841,"i_trigger", false,-1);
    tracep->declBus(c+842,"i_data", false,-1, 30,0);
    tracep->declBit(c+4901,"i_wb_clk", false,-1);
    tracep->declBit(c+4509,"i_wb_cyc", false,-1);
    tracep->declBit(c+4510,"i_wb_stb", false,-1);
    tracep->declBit(c+4511,"i_wb_we", false,-1);
    tracep->declBit(c+4586,"i_wb_addr", false,-1);
    tracep->declBus(c+4513,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4514,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+393,"o_wb_ack", false,-1);
    tracep->declBus(c+394,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+159,"o_interrupt", false,-1);
    tracep->declBit(c+4587,"write_stb", false,-1);
    tracep->declBit(c+4588,"read_from_data", false,-1);
    tracep->declBit(c+4589,"write_to_control", false,-1);
    tracep->declBus(c+394,"o_bus_data", false,-1, 31,0);
    tracep->declBit(c+4901,"bus_clock", false,-1);
    tracep->declBit(c+843,"read_address", false,-1);
    tracep->declBus(c+4513,"i_bus_data", false,-1, 31,0);
    tracep->declBus(c+844,"raddr", false,-1, 11,0);
    tracep->declBus(c+845,"waddr", false,-1, 11,0);
    tracep->declBit(c+846,"bw_reset_request", false,-1);
    tracep->declBit(c+847,"bw_manual_trigger", false,-1);
    tracep->declBit(c+848,"bw_disable_trigger", false,-1);
    tracep->declBit(c+846,"bw_reset_complete", false,-1);
    tracep->declBus(c+849,"br_config", false,-1, 2,0);
    tracep->declBus(c+850,"br_holdoff", false,-1, 19,0);
    tracep->declBus(c+851,"holdoff_counter", false,-1, 19,0);
    tracep->declBit(c+846,"dw_reset", false,-1);
    tracep->declBit(c+847,"dw_manual_trigger", false,-1);
    tracep->declBit(c+848,"dw_disable_trigger", false,-1);
    tracep->declBit(c+852,"dr_triggered", false,-1);
    tracep->declBit(c+853,"dr_primed", false,-1);
    tracep->declBit(c+854,"dw_trigger", false,-1);
    tracep->declBit(c+855,"dr_stopped", false,-1);
    tracep->declBus(c+5154,"DLYSTOP", false,-1, 31,0);
    tracep->declBus(c+856,"dr_stop_pipe", false,-1, 4,0);
    tracep->declBit(c+857,"dw_final_stop", false,-1);
    tracep->declBus(c+858,"ck_addr", false,-1, 30,0);
    tracep->declBus(c+859,"qd_data", false,-1, 30,0);
    tracep->declBit(c+860,"dr_force_write", false,-1);
    tracep->declBit(c+861,"dr_run_timeout", false,-1);
    tracep->declBit(c+862,"new_data", false,-1);
    tracep->declBit(c+863,"dr_force_inhibit", false,-1);
    tracep->declBus(c+859,"w_data", false,-1, 30,0);
    tracep->declBit(c+864,"imm_adr", false,-1);
    tracep->declBit(c+865,"lst_adr", false,-1);
    tracep->declBus(c+866,"lst_val", false,-1, 30,0);
    tracep->declBus(c+867,"imm_val", false,-1, 30,0);
    tracep->declBit(c+868,"record_ce", false,-1);
    tracep->declBus(c+869,"r_data", false,-1, 31,0);
    tracep->declBit(c+857,"bw_stopped", false,-1);
    tracep->declBit(c+852,"bw_triggered", false,-1);
    tracep->declBit(c+853,"bw_primed", false,-1);
    tracep->declBit(c+393,"br_wb_ack", false,-1);
    tracep->declBit(c+870,"br_pre_wb_ack", false,-1);
    tracep->declBit(c+4510,"bw_cyc_stb", false,-1);
    tracep->declBus(c+871,"this_addr", false,-1, 11,0);
    tracep->declBus(c+872,"nxt_mem", false,-1, 31,0);
    tracep->declBus(c+850,"full_holdoff", false,-1, 19,0);
    tracep->declBus(c+5183,"bw_lgmem", false,-1, 4,0);
    tracep->declBit(c+873,"br_level_interrupt", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("spioi ");
    tracep->declBus(c+5063,"NLEDS", false,-1, 31,0);
    tracep->declBus(c+5154,"NBTN", false,-1, 31,0);
    tracep->declBus(c+5063,"NSW", false,-1, 31,0);
    tracep->declBus(c+5075,"NFF", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4488,"i_wb_cyc", false,-1);
    tracep->declBit(c+4495,"i_wb_stb", false,-1);
    tracep->declBit(c+4490,"i_wb_we", false,-1);
    tracep->declBus(c+4491,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4492,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+387,"o_wb_ack", false,-1);
    tracep->declBus(c+388,"o_wb_data", false,-1, 31,0);
    tracep->declBus(c+5005,"i_sw", false,-1, 7,0);
    tracep->declBus(c+5006,"i_btn", false,-1, 4,0);
    tracep->declBus(c+196,"o_led", false,-1, 7,0);
    tracep->declBit(c+168,"o_int", false,-1);
    tracep->declBit(c+874,"led_demo", false,-1);
    tracep->declBus(c+875,"r_led", false,-1, 7,0);
    tracep->declBus(c+876,"w_btn", false,-1, 7,0);
    tracep->declBus(c+877,"bounced", false,-1, 7,0);
    tracep->declBus(c+878,"r_sw", false,-1, 7,0);
    tracep->declBit(c+879,"sw_int", false,-1);
    tracep->declBit(c+880,"btn_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_BUTTON ");
    tracep->declBus(c+4590,"next_btn", false,-1, 4,0);
    tracep->declBus(c+881,"s_btn", false,-1, 4,0);
    tracep->declBus(c+882,"r_btn", false,-1, 4,0);
    tracep->declBus(c+883,"btn_pipe", false,-1, 9,0);
    tracep->declBit(c+880,"r_btn_int", false,-1);
    tracep->declBit(c+4591,"next_int", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_SWITCHES ");
    tracep->declBus(c+884,"sw_pipe", false,-1, 15,0);
    tracep->declBus(c+878,"rr_sw", false,-1, 7,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("knightrider ");
    tracep->declBus(c+5063,"NLEDS", false,-1, 31,0);
    tracep->declBus(c+5132,"CTRBITS", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBus(c+877,"o_leds", false,-1, 7,0);
    tracep->declBus(c+885,"led_owner", false,-1, 7,0);
    tracep->declBit(c+886,"led_dir", false,-1);
    tracep->declBus(c+887,"led_ctr", false,-1, 24,0);
    tracep->declBit(c+888,"led_clk", false,-1);
    tracep->declBus(c+889,"br_ctr", false,-1, 4,0);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[0] ");
    tracep->declBus(c+890,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[1] ");
    tracep->declBus(c+891,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[2] ");
    tracep->declBus(c+892,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[3] ");
    tracep->declBus(c+893,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[4] ");
    tracep->declBus(c+894,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[5] ");
    tracep->declBus(c+895,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[6] ");
    tracep->declBus(c+896,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_BRIGHTNESS[7] ");
    tracep->declBus(c+897,"brightness", false,-1, 4,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("swic ");
    tracep->declBus(c+5067,"RESET_ADDRESS", false,-1, 31,0);
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5114,"DBG_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_PIPELINED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_EARLY_BRANCHING", false,-1, 0,0);
    tracep->declBus(c+5158,"OPT_LGICACHE", false,-1, 31,0);
    tracep->declBus(c+5158,"OPT_LGDCACHE", false,-1, 31,0);
    tracep->declBus(c+5070,"START_HALTED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DISTRIBUTED_REGS", false,-1, 0,0);
    tracep->declBus(c+5069,"EXTERNAL_INTERRUPTS", false,-1, 31,0);
    tracep->declBus(c+5062,"OPT_MPY", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_DIV", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_SHIFTS", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_FPU", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CIS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOCK", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_USERMODE", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DBGPORT", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_TRACE_PORT", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PROFILER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DMA", false,-1, 0,0);
    tracep->declBus(c+5061,"DMA_LGMEM", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_ACCOUNTING", false,-1, 0,0);
    tracep->declBus(c+5070,"DELAY_DBG_BUS", false,-1, 0,0);
    tracep->declBus(c+5113,"DELAY_EXT_BUS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_SIM", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_CLKGATE", false,-1, 0,0);
    tracep->declBus(c+5110,"RESET_DURATION", false,-1, 31,0);
    tracep->declBus(c+5068,"PAW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5015,"i_reset", false,-1);
    tracep->declBit(c+261,"o_wb_cyc", false,-1);
    tracep->declBit(c+262,"o_wb_stb", false,-1);
    tracep->declBit(c+263,"o_wb_we", false,-1);
    tracep->declBus(c+264,"o_wb_addr", false,-1, 21,0);
    tracep->declArray(c+265,"o_wb_data", false,-1, 511,0);
    tracep->declQuad(c+281,"o_wb_sel", false,-1, 63,0);
    tracep->declBit(c+283,"i_wb_stall", false,-1);
    tracep->declBit(c+284,"i_wb_ack", false,-1);
    tracep->declArray(c+286,"i_wb_data", false,-1, 511,0);
    tracep->declBit(c+285,"i_wb_err", false,-1);
    tracep->declBus(c+188,"i_ext_int", false,-1, 15,0);
    tracep->declBit(c+189,"o_ext_int", false,-1);
    tracep->declBit(c+43,"i_dbg_cyc", false,-1);
    tracep->declBit(c+44,"i_dbg_stb", false,-1);
    tracep->declBit(c+45,"i_dbg_we", false,-1);
    tracep->declBus(c+46,"i_dbg_addr", false,-1, 6,0);
    tracep->declBus(c+47,"i_dbg_data", false,-1, 31,0);
    tracep->declBus(c+5016,"i_dbg_sel", false,-1, 3,0);
    tracep->declBit(c+186,"o_dbg_stall", false,-1);
    tracep->declBit(c+187,"o_dbg_ack", false,-1);
    tracep->declBus(c+435,"o_dbg_data", false,-1, 31,0);
    tracep->declBus(c+5076,"o_cpu_debug", false,-1, 31,0);
    tracep->declBit(c+4996,"o_prof_stb", false,-1);
    tracep->declBus(c+4997,"o_prof_addr", false,-1, 27,0);
    tracep->declBus(c+4998,"o_prof_ticks", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5215,"PERIPHBASE", false,-1, 31,0);
    tracep->declBus(c+5112,"INTCTRL", false,-1, 7,0);
    tracep->declBus(c+5216,"WATCHDOG", false,-1, 7,0);
    tracep->declBus(c+5217,"BUSWATCHDOG", false,-1, 7,0);
    tracep->declBus(c+5218,"CTRINT", false,-1, 7,0);
    tracep->declBus(c+5219,"TIMER_A", false,-1, 7,0);
    tracep->declBus(c+5220,"TIMER_B", false,-1, 7,0);
    tracep->declBus(c+5221,"TIMER_C", false,-1, 7,0);
    tracep->declBus(c+5222,"JIFFIES", false,-1, 7,0);
    tracep->declBus(c+5223,"MSTR_TASK_CTR", false,-1, 7,0);
    tracep->declBus(c+5224,"MSTR_MSTL_CTR", false,-1, 7,0);
    tracep->declBus(c+5225,"MSTR_PSTL_CTR", false,-1, 7,0);
    tracep->declBus(c+5226,"MSTR_INST_CTR", false,-1, 7,0);
    tracep->declBus(c+5227,"USER_TASK_CTR", false,-1, 7,0);
    tracep->declBus(c+5228,"USER_MSTL_CTR", false,-1, 7,0);
    tracep->declBus(c+5229,"USER_PSTL_CTR", false,-1, 7,0);
    tracep->declBus(c+5230,"USER_INST_CTR", false,-1, 7,0);
    tracep->declBus(c+5231,"MMU_ADDR", false,-1, 7,0);
    tracep->declBus(c+5232,"DMAC_ADDR", false,-1, 7,0);
    tracep->declBus(c+5076,"HALT_BIT", false,-1, 31,0);
    tracep->declBus(c+5075,"STEP_BIT", false,-1, 31,0);
    tracep->declBus(c+5062,"RESET_BIT", false,-1, 31,0);
    tracep->declBus(c+5065,"CLEAR_CACHE_BIT", false,-1, 31,0);
    tracep->declBus(c+5154,"CATCH_BIT", false,-1, 31,0);
    tracep->declBus(c+5068,"VIRTUAL_ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5116,"DBG_ADDR_CTRL", false,-1, 1,0);
    tracep->declBus(c+5117,"DBG_ADDR_CPU", false,-1, 1,0);
    tracep->declBus(c+5118,"DBG_ADDR_SYS", false,-1, 1,0);
    tracep->declBus(c+898,"main_int_vector", false,-1, 14,0);
    tracep->declBus(c+899,"alt_int_vector", false,-1, 14,0);
    tracep->declBit(c+900,"ctri_int", false,-1);
    tracep->declBit(c+901,"tma_int", false,-1);
    tracep->declBit(c+902,"tmb_int", false,-1);
    tracep->declBit(c+903,"tmc_int", false,-1);
    tracep->declBit(c+904,"jif_int", false,-1);
    tracep->declBit(c+905,"dmac_int", false,-1);
    tracep->declBit(c+906,"mtc_int", false,-1);
    tracep->declBit(c+907,"moc_int", false,-1);
    tracep->declBit(c+908,"mpc_int", false,-1);
    tracep->declBit(c+909,"mic_int", false,-1);
    tracep->declBit(c+910,"utc_int", false,-1);
    tracep->declBit(c+911,"uoc_int", false,-1);
    tracep->declBit(c+912,"upc_int", false,-1);
    tracep->declBit(c+913,"uic_int", false,-1);
    tracep->declBus(c+914,"actr_data", false,-1, 31,0);
    tracep->declBit(c+915,"actr_ack", false,-1);
    tracep->declBit(c+5074,"actr_stall", false,-1);
    tracep->declBit(c+916,"cpu_clken", false,-1);
    tracep->declBit(c+917,"sys_cyc", false,-1);
    tracep->declBit(c+918,"sys_stb", false,-1);
    tracep->declBit(c+919,"sys_we", false,-1);
    tracep->declBus(c+920,"sys_addr", false,-1, 7,0);
    tracep->declBus(c+921,"sys_data", false,-1, 31,0);
    tracep->declBus(c+922,"cpu_addr", false,-1, 21,0);
    tracep->declBus(c+923,"sys_idata", false,-1, 31,0);
    tracep->declBit(c+924,"sys_ack", false,-1);
    tracep->declBit(c+5074,"sys_stall", false,-1);
    tracep->declBit(c+915,"sel_counter", false,-1);
    tracep->declBit(c+925,"sel_timer", false,-1);
    tracep->declBit(c+926,"sel_pic", false,-1);
    tracep->declBit(c+927,"sel_apic", false,-1);
    tracep->declBit(c+928,"sel_watchdog", false,-1);
    tracep->declBit(c+929,"sel_bus_watchdog", false,-1);
    tracep->declBit(c+930,"sel_dmac", false,-1);
    tracep->declBit(c+931,"sel_mmus", false,-1);
    tracep->declBit(c+932,"dbg_cyc", false,-1);
    tracep->declBit(c+933,"dbg_stb", false,-1);
    tracep->declBit(c+934,"dbg_we", false,-1);
    tracep->declBus(c+935,"dbg_addr", false,-1, 6,0);
    tracep->declBus(c+936,"dbg_idata", false,-1, 31,0);
    tracep->declBit(c+937,"dbg_ack", false,-1);
    tracep->declBit(c+938,"dbg_stall", false,-1);
    tracep->declBus(c+939,"dbg_odata", false,-1, 31,0);
    tracep->declBus(c+940,"dbg_sel", false,-1, 3,0);
    tracep->declBit(c+941,"no_dbg_err", false,-1);
    tracep->declBit(c+942,"cpu_break", false,-1);
    tracep->declBit(c+943,"dbg_cmd_write", false,-1);
    tracep->declBit(c+944,"dbg_cpu_write", false,-1);
    tracep->declBit(c+945,"dbg_cpu_read", false,-1);
    tracep->declBus(c+936,"dbg_cmd_data", false,-1, 31,0);
    tracep->declBus(c+940,"dbg_cmd_strb", false,-1, 3,0);
    tracep->declBit(c+946,"reset_hold", false,-1);
    tracep->declBit(c+947,"halt_on_fault", false,-1);
    tracep->declBit(c+947,"dbg_catch", false,-1);
    tracep->declBit(c+948,"reset_request", false,-1);
    tracep->declBit(c+949,"release_request", false,-1);
    tracep->declBit(c+950,"halt_request", false,-1);
    tracep->declBit(c+951,"step_request", false,-1);
    tracep->declBit(c+952,"clear_cache_request", false,-1);
    tracep->declBit(c+953,"cmd_reset", false,-1);
    tracep->declBit(c+954,"cmd_halt", false,-1);
    tracep->declBit(c+955,"cmd_step", false,-1);
    tracep->declBit(c+956,"cmd_clear_cache", false,-1);
    tracep->declBit(c+957,"cmd_write", false,-1);
    tracep->declBit(c+958,"cmd_read", false,-1);
    tracep->declBus(c+959,"cmd_waddr", false,-1, 4,0);
    tracep->declBus(c+960,"cmd_wdata", false,-1, 31,0);
    tracep->declBus(c+961,"cpu_dbg_cc", false,-1, 2,0);
    tracep->declBit(c+953,"cpu_reset", false,-1);
    tracep->declBit(c+954,"cpu_halt", false,-1);
    tracep->declBit(c+962,"cpu_has_halted", false,-1);
    tracep->declBit(c+963,"cpu_dbg_stall", false,-1);
    tracep->declBus(c+964,"cpu_status", false,-1, 31,0);
    tracep->declBit(c+965,"cpu_gie", false,-1);
    tracep->declBit(c+5074,"wdt_stall", false,-1);
    tracep->declBit(c+966,"wdt_ack", false,-1);
    tracep->declBit(c+967,"wdt_reset", false,-1);
    tracep->declBus(c+968,"wdt_data", false,-1, 31,0);
    tracep->declBit(c+969,"wdbus_ack", false,-1);
    tracep->declBus(c+970,"r_wdbus_data", false,-1, 21,0);
    tracep->declBus(c+971,"pic_data", false,-1, 31,0);
    tracep->declBus(c+972,"wdbus_data", false,-1, 31,0);
    tracep->declBit(c+973,"reset_wdbus_timer", false,-1);
    tracep->declBit(c+974,"wdbus_int", false,-1);
    tracep->declBit(c+48,"cpu_op_stall", false,-1);
    tracep->declBit(c+975,"cpu_pf_stall", false,-1);
    tracep->declBit(c+976,"cpu_i_count", false,-1);
    tracep->declBit(c+977,"dmac_stb", false,-1);
    tracep->declBit(c+978,"dc_err", false,-1);
    tracep->declBus(c+979,"dmac_data", false,-1, 31,0);
    tracep->declBit(c+5074,"dmac_stall", false,-1);
    tracep->declBit(c+980,"dmac_ack", false,-1);
    tracep->declBit(c+981,"dc_cyc", false,-1);
    tracep->declBit(c+982,"dc_stb", false,-1);
    tracep->declBit(c+983,"dc_we", false,-1);
    tracep->declBit(c+984,"dc_stall", false,-1);
    tracep->declBit(c+985,"dc_ack", false,-1);
    tracep->declBus(c+986,"dc_addr", false,-1, 21,0);
    tracep->declArray(c+987,"dc_data", false,-1, 511,0);
    tracep->declQuad(c+1003,"dc_sel", false,-1, 63,0);
    tracep->declBit(c+1005,"cpu_gbl_cyc", false,-1);
    tracep->declBus(c+1006,"dmac_int_vec", false,-1, 31,0);
    tracep->declBit(c+1007,"ctri_sel", false,-1);
    tracep->declBit(c+5074,"ctri_stall", false,-1);
    tracep->declBit(c+1007,"ctri_ack", false,-1);
    tracep->declBus(c+1008,"ctri_data", false,-1, 31,0);
    tracep->declBit(c+5074,"tma_stall", false,-1);
    tracep->declBit(c+1009,"tma_ack", false,-1);
    tracep->declBit(c+5074,"tmb_stall", false,-1);
    tracep->declBit(c+1010,"tmb_ack", false,-1);
    tracep->declBit(c+5074,"tmc_stall", false,-1);
    tracep->declBit(c+1011,"tmc_ack", false,-1);
    tracep->declBit(c+5074,"jif_stall", false,-1);
    tracep->declBit(c+1012,"jif_ack", false,-1);
    tracep->declBus(c+1013,"tma_data", false,-1, 31,0);
    tracep->declBus(c+1014,"tmb_data", false,-1, 31,0);
    tracep->declBus(c+1015,"tmc_data", false,-1, 31,0);
    tracep->declBus(c+1016,"jif_data", false,-1, 31,0);
    tracep->declBit(c+5074,"pic_stall", false,-1);
    tracep->declBit(c+1017,"pic_ack", false,-1);
    tracep->declBit(c+1018,"cpu_gbl_stb", false,-1);
    tracep->declBit(c+1019,"cpu_lcl_cyc", false,-1);
    tracep->declBit(c+1020,"cpu_lcl_stb", false,-1);
    tracep->declBit(c+1021,"cpu_we", false,-1);
    tracep->declArray(c+1022,"cpu_data", false,-1, 511,0);
    tracep->declQuad(c+1038,"cpu_sel", false,-1, 63,0);
    tracep->declQuad(c+1038,"mmu_sel", false,-1, 63,0);
    tracep->declArray(c+1040,"cpu_idata", false,-1, 511,0);
    tracep->declBit(c+1056,"cpu_stall", false,-1);
    tracep->declBit(c+1057,"pic_interrupt", false,-1);
    tracep->declBit(c+1058,"cpu_ack", false,-1);
    tracep->declBit(c+1059,"cpu_err", false,-1);
    tracep->declBus(c+1060,"cpu_dbg_data", false,-1, 31,0);
    tracep->declBit(c+283,"ext_stall", false,-1);
    tracep->declBit(c+284,"ext_ack", false,-1);
    tracep->declBit(c+1005,"mmu_cyc", false,-1);
    tracep->declBit(c+1018,"mmu_stb", false,-1);
    tracep->declBit(c+1021,"mmu_we", false,-1);
    tracep->declBit(c+1061,"mmu_stall", false,-1);
    tracep->declBit(c+1062,"mmu_ack", false,-1);
    tracep->declBit(c+1063,"mmu_err", false,-1);
    tracep->declBit(c+5074,"mmus_stall", false,-1);
    tracep->declBit(c+1064,"mmus_ack", false,-1);
    tracep->declBus(c+922,"mmu_addr", false,-1, 21,0);
    tracep->declArray(c+1022,"mmu_data", false,-1, 511,0);
    tracep->declArray(c+286,"mmu_idata", false,-1, 511,0);
    tracep->declBus(c+5076,"mmus_data", false,-1, 31,0);
    tracep->declBit(c+5074,"cpu_miss", false,-1);
    tracep->declBit(c+1061,"mmu_cpu_stall", false,-1);
    tracep->declBit(c+1062,"mmu_cpu_ack", false,-1);
    tracep->declArray(c+286,"mmu_cpu_idata", false,-1, 511,0);
    tracep->declBit(c+5074,"pf_return_stb", false,-1);
    tracep->declBit(c+5074,"pf_return_we", false,-1);
    tracep->declBit(c+5074,"pf_return_cachable", false,-1);
    tracep->declBus(c+5233,"pf_return_v", false,-1, 19,0);
    tracep->declBus(c+5233,"pf_return_p", false,-1, 19,0);
    tracep->declBit(c+261,"ext_cyc", false,-1);
    tracep->declBit(c+262,"ext_stb", false,-1);
    tracep->declBit(c+263,"ext_we", false,-1);
    tracep->declBit(c+1065,"ext_err", false,-1);
    tracep->declBus(c+264,"ext_addr", false,-1, 21,0);
    tracep->declArray(c+265,"ext_odata", false,-1, 511,0);
    tracep->declQuad(c+281,"ext_sel", false,-1, 63,0);
    tracep->declArray(c+286,"ext_idata", false,-1, 511,0);
    tracep->declBus(c+1066,"tmr_data", false,-1, 31,0);
    tracep->declBus(c+1067,"w_ack_idx", false,-1, 2,0);
    tracep->declBus(c+1068,"ack_idx", false,-1, 2,0);
    tracep->declBit(c+1069,"last_sys_stb", false,-1);
    tracep->declBit(c+1070,"cmd_read_ack", false,-1);
    tracep->declBit(c+1064,"r_mmus_ack", false,-1);
    tracep->declBit(c+1071,"dbg_pre_ack", false,-1);
    tracep->declBus(c+1072,"dbg_pre_addr", false,-1, 1,0);
    tracep->declBus(c+1073,"dbg_cpu_status", false,-1, 31,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("ACCOUNTING_COUNTERS ");
    tracep->declBit(c+5074,"mtc_stall", false,-1);
    tracep->declBit(c+1074,"mtc_ack", false,-1);
    tracep->declBit(c+5074,"moc_stall", false,-1);
    tracep->declBit(c+1075,"moc_ack", false,-1);
    tracep->declBit(c+5074,"mpc_stall", false,-1);
    tracep->declBit(c+1076,"mpc_ack", false,-1);
    tracep->declBit(c+5074,"mic_stall", false,-1);
    tracep->declBit(c+1077,"mic_ack", false,-1);
    tracep->declBit(c+5074,"utc_stall", false,-1);
    tracep->declBit(c+1078,"utc_ack", false,-1);
    tracep->declBit(c+5074,"uoc_stall", false,-1);
    tracep->declBit(c+1079,"uoc_ack", false,-1);
    tracep->declBit(c+5074,"upc_stall", false,-1);
    tracep->declBit(c+1080,"upc_ack", false,-1);
    tracep->declBit(c+5074,"uic_stall", false,-1);
    tracep->declBit(c+1081,"uic_ack", false,-1);
    tracep->declBus(c+1082,"mtc_data", false,-1, 31,0);
    tracep->declBus(c+1083,"moc_data", false,-1, 31,0);
    tracep->declBus(c+1084,"mpc_data", false,-1, 31,0);
    tracep->declBus(c+1085,"mic_data", false,-1, 31,0);
    tracep->declBus(c+1086,"utc_data", false,-1, 31,0);
    tracep->declBus(c+1087,"uoc_data", false,-1, 31,0);
    tracep->declBus(c+1088,"upc_data", false,-1, 31,0);
    tracep->declBus(c+1089,"uic_data", false,-1, 31,0);
    tracep->declBus(c+914,"r_actr_data", false,-1, 31,0);
    tracep->pushNamePrefix("mins_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+976,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1090,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1077,"o_wb_ack", false,-1);
    tracep->declBus(c+1085,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+909,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("mmstall_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+48,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1091,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1075,"o_wb_ack", false,-1);
    tracep->declBus(c+1083,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+907,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("mpstall_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+975,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1092,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1076,"o_wb_ack", false,-1);
    tracep->declBus(c+1084,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+908,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("mtask_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+1093,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1094,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1074,"o_wb_ack", false,-1);
    tracep->declBus(c+1082,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+906,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("uins_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+1095,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1096,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1081,"o_wb_ack", false,-1);
    tracep->declBus(c+1089,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+913,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("umstall_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+49,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1097,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1079,"o_wb_ack", false,-1);
    tracep->declBus(c+1087,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+911,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("upstall_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+1098,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1099,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1080,"o_wb_ack", false,-1);
    tracep->declBus(c+1088,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+912,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("utask_ctr ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_reset", false,-1);
    tracep->declBit(c+1100,"i_event", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1101,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1078,"o_wb_ack", false,-1);
    tracep->declBus(c+1086,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+910,"o_int", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("DELAY_THE_DEBUG_BUS ");
    tracep->declBit(c+5074,"dbg_err", false,-1);
    tracep->pushNamePrefix("wbdelay ");
    tracep->declBus(c+5072,"AW", false,-1, 31,0);
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"DELAY_STALL", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5015,"i_reset", false,-1);
    tracep->declBit(c+43,"i_wb_cyc", false,-1);
    tracep->declBit(c+44,"i_wb_stb", false,-1);
    tracep->declBit(c+45,"i_wb_we", false,-1);
    tracep->declBus(c+46,"i_wb_addr", false,-1, 6,0);
    tracep->declBus(c+47,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+186,"o_wb_stall", false,-1);
    tracep->declBit(c+187,"o_wb_ack", false,-1);
    tracep->declBus(c+435,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+941,"o_wb_err", false,-1);
    tracep->declBit(c+932,"o_dly_cyc", false,-1);
    tracep->declBit(c+933,"o_dly_stb", false,-1);
    tracep->declBit(c+934,"o_dly_we", false,-1);
    tracep->declBus(c+935,"o_dly_addr", false,-1, 6,0);
    tracep->declBus(c+936,"o_dly_data", false,-1, 31,0);
    tracep->declBus(c+940,"o_dly_sel", false,-1, 3,0);
    tracep->declBit(c+938,"i_dly_stall", false,-1);
    tracep->declBit(c+937,"i_dly_ack", false,-1);
    tracep->declBus(c+939,"i_dly_data", false,-1, 31,0);
    tracep->declBit(c+5074,"i_dly_err", false,-1);
    tracep->pushNamePrefix("SKIDBUFFER ");
    tracep->declBit(c+186,"r_stb", false,-1);
    tracep->declBit(c+1102,"r_we", false,-1);
    tracep->declBus(c+1103,"r_addr", false,-1, 6,0);
    tracep->declBus(c+1104,"r_data", false,-1, 31,0);
    tracep->declBus(c+1105,"r_sel", false,-1, 3,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DMA ");
    tracep->pushNamePrefix("dma_controller ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5061,"LGMEMLEN", false,-1, 31,0);
    tracep->declBus(c+5199,"LGDMALENGTH", false,-1, 31,0);
    tracep->declBus(c+5114,"SLV_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_REGISTER_RAM", false,-1, 0,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+917,"i_swb_cyc", false,-1);
    tracep->declBit(c+977,"i_swb_stb", false,-1);
    tracep->declBit(c+919,"i_swb_we", false,-1);
    tracep->declBus(c+1106,"i_swb_addr", false,-1, 1,0);
    tracep->declBus(c+921,"i_swb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_swb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_swb_stall", false,-1);
    tracep->declBit(c+980,"o_swb_ack", false,-1);
    tracep->declBus(c+979,"o_swb_data", false,-1, 31,0);
    tracep->declBit(c+981,"o_mwb_cyc", false,-1);
    tracep->declBit(c+982,"o_mwb_stb", false,-1);
    tracep->declBit(c+983,"o_mwb_we", false,-1);
    tracep->declBus(c+986,"o_mwb_addr", false,-1, 21,0);
    tracep->declArray(c+987,"o_mwb_data", false,-1, 511,0);
    tracep->declQuad(c+1003,"o_mwb_sel", false,-1, 63,0);
    tracep->declBit(c+984,"i_mwb_stall", false,-1);
    tracep->declBit(c+985,"i_mwb_ack", false,-1);
    tracep->declArray(c+286,"i_mwb_data", false,-1, 511,0);
    tracep->declBit(c+978,"i_mwb_err", false,-1);
    tracep->declBus(c+1006,"i_dev_ints", false,-1, 31,0);
    tracep->declBit(c+905,"o_interrupt", false,-1);
    tracep->declBus(c+5234,"FIFO_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5065,"LGFIFO", false,-1, 31,0);
    tracep->declBit(c+1107,"dma_request", false,-1);
    tracep->declBit(c+1108,"dma_abort", false,-1);
    tracep->declBit(c+1109,"dma_busy", false,-1);
    tracep->declBit(c+1110,"dma_err", false,-1);
    tracep->declBus(c+1111,"dma_src", false,-1, 27,0);
    tracep->declBus(c+1112,"dma_dst", false,-1, 27,0);
    tracep->declBus(c+1113,"read_addr", false,-1, 27,0);
    tracep->declBus(c+1114,"write_addr", false,-1, 27,0);
    tracep->declBus(c+1115,"dma_length", false,-1, 27,0);
    tracep->declBus(c+1116,"remaining_len", false,-1, 27,0);
    tracep->declBus(c+1117,"dma_transferlen", false,-1, 10,0);
    tracep->declBit(c+1118,"dma_trigger", false,-1);
    tracep->declBit(c+1119,"mm2s_request", false,-1);
    tracep->declBit(c+1120,"s2mm_request", false,-1);
    tracep->declBit(c+1121,"mm2s_busy", false,-1);
    tracep->declBit(c+1122,"s2mm_busy", false,-1);
    tracep->declBit(c+1123,"mm2s_err", false,-1);
    tracep->declBit(c+1124,"s2mm_err", false,-1);
    tracep->declBit(c+1125,"mm2s_inc", false,-1);
    tracep->declBit(c+1126,"s2mm_inc", false,-1);
    tracep->declBus(c+1127,"mm2s_size", false,-1, 1,0);
    tracep->declBus(c+1128,"s2mm_size", false,-1, 1,0);
    tracep->declBus(c+1129,"mm2s_addr", false,-1, 27,0);
    tracep->declBus(c+1130,"s2mm_addr", false,-1, 27,0);
    tracep->declBus(c+1131,"mm2s_transferlen", false,-1, 10,0);
    tracep->declBus(c+1131,"s2mm_transferlen", false,-1, 10,0);
    tracep->declBit(c+1132,"mm2s_rd_cyc", false,-1);
    tracep->declBit(c+1133,"mm2s_rd_stb", false,-1);
    tracep->declBit(c+5074,"mm2s_rd_we", false,-1);
    tracep->declBit(c+1134,"mm2s_rd_stall", false,-1);
    tracep->declBit(c+1135,"mm2s_rd_ack", false,-1);
    tracep->declBit(c+1136,"mm2s_rd_err", false,-1);
    tracep->declBus(c+1137,"mm2s_rd_addr", false,-1, 21,0);
    tracep->declArray(c+5078,"mm2s_rd_data", false,-1, 511,0);
    tracep->declQuad(c+1138,"mm2s_rd_sel", false,-1, 63,0);
    tracep->declBit(c+1140,"mm2s_valid", false,-1);
    tracep->declBit(c+1141,"mm2s_ready", false,-1);
    tracep->declBit(c+1142,"mm2s_last", false,-1);
    tracep->declArray(c+1143,"mm2s_data", false,-1, 511,0);
    tracep->declBus(c+1159,"mm2s_bytes", false,-1, 6,0);
    tracep->declBit(c+1160,"rx_valid", false,-1);
    tracep->declBit(c+1161,"rx_ready", false,-1);
    tracep->declBit(c+1162,"rx_last", false,-1);
    tracep->declArray(c+1163,"rx_data", false,-1, 511,0);
    tracep->declBus(c+1179,"rx_bytes", false,-1, 6,0);
    tracep->declBit(c+1180,"tx_valid", false,-1);
    tracep->declBit(c+1181,"tx_ready", false,-1);
    tracep->declBit(c+1182,"tx_last", false,-1);
    tracep->declArray(c+1183,"tx_data", false,-1, 511,0);
    tracep->declBus(c+1199,"tx_bytes", false,-1, 6,0);
    tracep->declBit(c+1200,"sfifo_full", false,-1);
    tracep->declBit(c+1201,"sfifo_empty", false,-1);
    tracep->declBus(c+1202,"ign_sfifo_fill", false,-1, 4,0);
    tracep->declBit(c+1203,"s2mm_valid", false,-1);
    tracep->declBit(c+1204,"s2mm_ready", false,-1);
    tracep->declBit(c+1205,"s2mm_last", false,-1);
    tracep->declArray(c+1206,"s2mm_data", false,-1, 511,0);
    tracep->declBus(c+1222,"s2mm_bytes", false,-1, 6,0);
    tracep->declBit(c+1223,"s2mm_wr_cyc", false,-1);
    tracep->declBit(c+1224,"s2mm_wr_stb", false,-1);
    tracep->declBit(c+5077,"s2mm_wr_we", false,-1);
    tracep->declBit(c+1225,"s2mm_wr_stall", false,-1);
    tracep->declBit(c+1226,"s2mm_wr_ack", false,-1);
    tracep->declBit(c+1227,"s2mm_wr_err", false,-1);
    tracep->declBus(c+1228,"s2mm_wr_addr", false,-1, 21,0);
    tracep->declArray(c+987,"s2mm_wr_data", false,-1, 511,0);
    tracep->declQuad(c+1229,"s2mm_wr_sel", false,-1, 63,0);
    tracep->declBit(c+981,"wb_cyc", false,-1);
    tracep->declBit(c+982,"wb_stb", false,-1);
    tracep->declBit(c+983,"wb_we", false,-1);
    tracep->declBit(c+984,"wb_stall", false,-1);
    tracep->declBit(c+985,"wb_ack", false,-1);
    tracep->declBit(c+978,"wb_err", false,-1);
    tracep->declBus(c+986,"wb_addr", false,-1, 21,0);
    tracep->declArray(c+987,"wb_data", false,-1, 511,0);
    tracep->declArray(c+286,"wb_idata", false,-1, 511,0);
    tracep->declQuad(c+1003,"wb_sel", false,-1, 63,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("u_arbiter ");
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declArray(c+5235,"SCHEME", false,-1, 87,0);
    tracep->declBus(c+5113,"OPT_ZERO_ON_IDLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1132,"i_a_cyc", false,-1);
    tracep->declBit(c+1133,"i_a_stb", false,-1);
    tracep->declBit(c+5074,"i_a_we", false,-1);
    tracep->declBus(c+1137,"i_a_adr", false,-1, 21,0);
    tracep->declArray(c+987,"i_a_dat", false,-1, 511,0);
    tracep->declQuad(c+1138,"i_a_sel", false,-1, 63,0);
    tracep->declBit(c+1134,"o_a_stall", false,-1);
    tracep->declBit(c+1135,"o_a_ack", false,-1);
    tracep->declBit(c+1136,"o_a_err", false,-1);
    tracep->declBit(c+1223,"i_b_cyc", false,-1);
    tracep->declBit(c+1224,"i_b_stb", false,-1);
    tracep->declBit(c+5077,"i_b_we", false,-1);
    tracep->declBus(c+1228,"i_b_adr", false,-1, 21,0);
    tracep->declArray(c+987,"i_b_dat", false,-1, 511,0);
    tracep->declQuad(c+1229,"i_b_sel", false,-1, 63,0);
    tracep->declBit(c+1225,"o_b_stall", false,-1);
    tracep->declBit(c+1226,"o_b_ack", false,-1);
    tracep->declBit(c+1227,"o_b_err", false,-1);
    tracep->declBit(c+981,"o_cyc", false,-1);
    tracep->declBit(c+982,"o_stb", false,-1);
    tracep->declBit(c+983,"o_we", false,-1);
    tracep->declBus(c+986,"o_adr", false,-1, 21,0);
    tracep->declArray(c+987,"o_dat", false,-1, 511,0);
    tracep->declQuad(c+1003,"o_sel", false,-1, 63,0);
    tracep->declBit(c+984,"i_stall", false,-1);
    tracep->declBit(c+985,"i_ack", false,-1);
    tracep->declBit(c+978,"i_err", false,-1);
    tracep->declBit(c+1231,"r_a_owner", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("ALT ");
    tracep->declBit(c+1232,"last_owner", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_controller ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5061,"LGMEMLEN", false,-1, 31,0);
    tracep->declBus(c+5114,"SLV_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5199,"LGDMALENGTH", false,-1, 31,0);
    tracep->declBus(c+5238,"ABORT_KEY", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5199,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+917,"i_cyc", false,-1);
    tracep->declBit(c+977,"i_stb", false,-1);
    tracep->declBit(c+919,"i_we", false,-1);
    tracep->declBus(c+1106,"i_addr", false,-1, 1,0);
    tracep->declBus(c+921,"i_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_stall", false,-1);
    tracep->declBit(c+980,"o_ack", false,-1);
    tracep->declBus(c+979,"o_data", false,-1, 31,0);
    tracep->declBit(c+1107,"o_dma_request", false,-1);
    tracep->declBit(c+1108,"o_dma_abort", false,-1);
    tracep->declBit(c+1109,"i_dma_busy", false,-1);
    tracep->declBit(c+1110,"i_dma_err", false,-1);
    tracep->declBus(c+1111,"o_src_addr", false,-1, 27,0);
    tracep->declBus(c+1112,"o_dst_addr", false,-1, 27,0);
    tracep->declBus(c+1115,"o_length", false,-1, 27,0);
    tracep->declBus(c+1117,"o_transferlen", false,-1, 10,0);
    tracep->declBit(c+1125,"o_mm2s_inc", false,-1);
    tracep->declBit(c+1126,"o_s2mm_inc", false,-1);
    tracep->declBus(c+1127,"o_mm2s_size", false,-1, 1,0);
    tracep->declBus(c+1128,"o_s2mm_size", false,-1, 1,0);
    tracep->declBit(c+1118,"o_trigger", false,-1);
    tracep->declBus(c+1113,"i_current_src", false,-1, 27,0);
    tracep->declBus(c+1114,"i_current_dst", false,-1, 27,0);
    tracep->declBus(c+1116,"i_remaining_len", false,-1, 27,0);
    tracep->declBus(c+1006,"i_dma_int", false,-1, 31,0);
    tracep->declBit(c+905,"o_interrupt", false,-1);
    tracep->declBit(c+1233,"int_trigger", false,-1);
    tracep->declBit(c+1234,"r_err", false,-1);
    tracep->declBit(c+1235,"r_zero_len", false,-1);
    tracep->declBit(c+1236,"r_busy", false,-1);
    tracep->declBus(c+1237,"int_sel", false,-1, 4,0);
    tracep->declBus(c+1238,"next_src", false,-1, 31,0);
    tracep->declBus(c+1239,"next_dst", false,-1, 31,0);
    tracep->declBus(c+1240,"next_len", false,-1, 31,0);
    tracep->declBus(c+1241,"next_tlen", false,-1, 31,0);
    tracep->declBus(c+1242,"w_control_reg", false,-1, 31,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("UNUSED_LEN ");
    tracep->declBit(c+5074,"unused_len", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("UNUSED_WIDE_ADDR ");
    tracep->declBit(c+5074,"unused_addr", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_dma_fsm ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5199,"LGDMALENGTH", false,-1, 31,0);
    tracep->declBus(c+5061,"LGSUBLENGTH", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1108,"i_soft_reset", false,-1);
    tracep->declBit(c+1107,"i_dma_request", false,-1);
    tracep->declBit(c+1109,"o_dma_busy", false,-1);
    tracep->declBit(c+1110,"o_dma_err", false,-1);
    tracep->declBus(c+1111,"i_src_addr", false,-1, 27,0);
    tracep->declBus(c+1112,"i_dst_addr", false,-1, 27,0);
    tracep->declBus(c+1115,"i_length", false,-1, 27,0);
    tracep->declBus(c+1117,"i_transferlen", false,-1, 10,0);
    tracep->declBus(c+1116,"o_remaining_len", false,-1, 27,0);
    tracep->declBit(c+1118,"i_trigger", false,-1);
    tracep->declBit(c+1119,"o_mm2s_request", false,-1);
    tracep->declBit(c+1121,"i_mm2s_busy", false,-1);
    tracep->declBit(c+1123,"i_mm2s_err", false,-1);
    tracep->declBit(c+1125,"i_mm2s_inc", false,-1);
    tracep->declBus(c+1129,"o_mm2s_addr", false,-1, 27,0);
    tracep->declBus(c+1131,"o_mm2s_transferlen", false,-1, 10,0);
    tracep->declBit(c+1120,"o_s2mm_request", false,-1);
    tracep->declBit(c+1122,"i_s2mm_busy", false,-1);
    tracep->declBit(c+1124,"i_s2mm_err", false,-1);
    tracep->declBit(c+1126,"i_s2mm_inc", false,-1);
    tracep->declBus(c+1130,"o_s2mm_addr", false,-1, 27,0);
    tracep->declBus(c+1131,"o_s2mm_transferlen", false,-1, 10,0);
    tracep->declBus(c+5116,"S_IDLE", false,-1, 1,0);
    tracep->declBus(c+5117,"S_WAIT", false,-1, 1,0);
    tracep->declBus(c+5118,"S_READ", false,-1, 1,0);
    tracep->declBus(c+5119,"S_WRITE", false,-1, 1,0);
    tracep->declBus(c+1116,"r_length", false,-1, 27,0);
    tracep->declBus(c+1131,"r_transferlen", false,-1, 10,0);
    tracep->declBus(c+1243,"fsm_state", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_mm2s ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5061,"LGLENGTH", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+1244,"i_reset", false,-1);
    tracep->declBit(c+1119,"i_request", false,-1);
    tracep->declBit(c+1121,"o_busy", false,-1);
    tracep->declBit(c+1123,"o_err", false,-1);
    tracep->declBit(c+1125,"i_inc", false,-1);
    tracep->declBus(c+1127,"i_size", false,-1, 1,0);
    tracep->declBus(c+1131,"i_transferlen", false,-1, 10,0);
    tracep->declBus(c+1129,"i_addr", false,-1, 27,0);
    tracep->declBit(c+1132,"o_rd_cyc", false,-1);
    tracep->declBit(c+1133,"o_rd_stb", false,-1);
    tracep->declBit(c+5074,"o_rd_we", false,-1);
    tracep->declBus(c+1137,"o_rd_addr", false,-1, 21,0);
    tracep->declArray(c+5078,"o_rd_data", false,-1, 511,0);
    tracep->declQuad(c+1138,"o_rd_sel", false,-1, 63,0);
    tracep->declBit(c+1134,"i_rd_stall", false,-1);
    tracep->declBit(c+1135,"i_rd_ack", false,-1);
    tracep->declArray(c+286,"i_rd_data", false,-1, 511,0);
    tracep->declBit(c+1136,"i_rd_err", false,-1);
    tracep->declBit(c+1140,"M_VALID", false,-1);
    tracep->declBit(c+1141,"M_READY", false,-1);
    tracep->declArray(c+1143,"M_DATA", false,-1, 511,0);
    tracep->declBus(c+1159,"M_BYTES", false,-1, 6,0);
    tracep->declBit(c+1142,"M_LAST", false,-1);
    tracep->declBus(c+5119,"SZ_BYTE", false,-1, 1,0);
    tracep->declBus(c+5118,"SZ_16B", false,-1, 1,0);
    tracep->declBus(c+5117,"SZ_32B", false,-1, 1,0);
    tracep->declBus(c+5116,"SZ_BUS", false,-1, 1,0);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBus(c+1245,"nxtstb_size", false,-1, 6,0);
    tracep->declBus(c+1246,"rdstb_size", false,-1, 6,0);
    tracep->declBus(c+1247,"rdack_size", false,-1, 6,0);
    tracep->declBus(c+1248,"first_size", false,-1, 6,0);
    tracep->declBus(c+1249,"next_addr", false,-1, 27,0);
    tracep->declBus(c+1250,"last_request_addr", false,-1, 27,0);
    tracep->declBus(c+1251,"subaddr", false,-1, 5,0);
    tracep->declBus(c+1252,"rdack_subaddr", false,-1, 5,0);
    tracep->declQuad(c+1253,"nxtstb_sel", false,-1, 63,0);
    tracep->declQuad(c+1255,"first_sel", false,-1, 63,0);
    tracep->declQuad(c+1257,"base_sel", false,-1, 63,0);
    tracep->declQuad(c+1259,"ibase_sel", false,-1, 63,0);
    tracep->declBus(c+1261,"wb_outstanding", false,-1, 10,0);
    tracep->declBus(c+1262,"fill", false,-1, 7,0);
    tracep->declBus(c+1263,"next_fill", false,-1, 7,0);
    tracep->declBit(c+1140,"m_valid", false,-1);
    tracep->declBit(c+1142,"m_last", false,-1);
    tracep->declArray(c+1143,"sreg", false,-1, 511,0);
    tracep->declBus(c+1159,"m_bytes", false,-1, 6,0);
    tracep->declBus(c+1264,"rdstb_len", false,-1, 10,0);
    tracep->declBus(c+1265,"rdack_len", false,-1, 10,0);
    tracep->declBus(c+1266,"pre_shift", false,-1, 5,0);
    tracep->declArray(c+1267,"pre_shifted_data", false,-1, 511,0);
    tracep->declBit(c+1283,"r_inc", false,-1);
    tracep->declBus(c+1284,"r_size", false,-1, 1,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_rxgears ");
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1108,"i_soft_reset", false,-1);
    tracep->declBit(c+1140,"S_VALID", false,-1);
    tracep->declBit(c+1141,"S_READY", false,-1);
    tracep->declArray(c+1143,"S_DATA", false,-1, 511,0);
    tracep->declBus(c+1159,"S_BYTES", false,-1, 6,0);
    tracep->declBit(c+1142,"S_LAST", false,-1);
    tracep->declBit(c+1160,"M_VALID", false,-1);
    tracep->declBit(c+1161,"M_READY", false,-1);
    tracep->declArray(c+1163,"M_DATA", false,-1, 511,0);
    tracep->declBus(c+1179,"M_BYTES", false,-1, 6,0);
    tracep->declBit(c+1162,"M_LAST", false,-1);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declArray(c+1285,"sreg", false,-1, 1023,0);
    tracep->declBus(c+1317,"next_fill", false,-1, 7,0);
    tracep->declBus(c+1318,"fill", false,-1, 7,0);
    tracep->declBit(c+1160,"m_valid", false,-1);
    tracep->declBit(c+1162,"m_last", false,-1);
    tracep->declBit(c+1319,"next_last", false,-1);
    tracep->declBit(c+1320,"r_last", false,-1);
    tracep->declBit(c+1321,"r_full", false,-1);
    tracep->declBus(c+1179,"m_bytes", false,-1, 6,0);
    tracep->declBus(c+1322,"shift", false,-1, 5,0);
    tracep->declArray(c+1323,"s_data", false,-1, 511,0);
    tracep->declBus(c+5239,"ik", false,-1, 31,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_s2mm ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5061,"LGPIPE", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+1244,"i_reset", false,-1);
    tracep->declBit(c+1120,"i_request", false,-1);
    tracep->declBit(c+1122,"o_busy", false,-1);
    tracep->declBit(c+1124,"o_err", false,-1);
    tracep->declBit(c+1126,"i_inc", false,-1);
    tracep->declBus(c+1128,"i_size", false,-1, 1,0);
    tracep->declBus(c+1130,"i_addr", false,-1, 27,0);
    tracep->declBit(c+1203,"S_VALID", false,-1);
    tracep->declBit(c+1204,"S_READY", false,-1);
    tracep->declArray(c+1206,"S_DATA", false,-1, 511,0);
    tracep->declBus(c+1222,"S_BYTES", false,-1, 6,0);
    tracep->declBit(c+1205,"S_LAST", false,-1);
    tracep->declBit(c+1223,"o_wr_cyc", false,-1);
    tracep->declBit(c+1224,"o_wr_stb", false,-1);
    tracep->declBit(c+5077,"o_wr_we", false,-1);
    tracep->declBus(c+1228,"o_wr_addr", false,-1, 21,0);
    tracep->declArray(c+987,"o_wr_data", false,-1, 511,0);
    tracep->declQuad(c+1229,"o_wr_sel", false,-1, 63,0);
    tracep->declBit(c+1225,"i_wr_stall", false,-1);
    tracep->declBit(c+1226,"i_wr_ack", false,-1);
    tracep->declArray(c+286,"i_wr_data", false,-1, 511,0);
    tracep->declBit(c+1227,"i_wr_err", false,-1);
    tracep->declBus(c+5119,"SZ_BYTE", false,-1, 1,0);
    tracep->declBus(c+5118,"SZ_16B", false,-1, 1,0);
    tracep->declBus(c+5117,"SZ_32B", false,-1, 1,0);
    tracep->declBus(c+5116,"SZ_BUS", false,-1, 1,0);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBus(c+7,"ik", false,-1, 31,0);
    tracep->declBit(c+1339,"r_inc", false,-1);
    tracep->declBus(c+1340,"r_size", false,-1, 1,0);
    tracep->declBus(c+1341,"next_addr", false,-1, 28,0);
    tracep->declBus(c+1342,"subaddr", false,-1, 5,0);
    tracep->declArray(c+1343,"next_data", false,-1, 1023,0);
    tracep->declArray(c+1375,"r_data", false,-1, 511,0);
    tracep->declArray(c+1391,"next_sel", false,-1, 127,0);
    tracep->declArray(c+1395,"pre_sel", false,-1, 127,0);
    tracep->declQuad(c+1399,"r_sel", false,-1, 63,0);
    tracep->declBit(c+1401,"r_last", false,-1);
    tracep->declBus(c+1402,"wb_outstanding", false,-1, 9,0);
    tracep->declBit(c+1403,"wb_pipeline_full", false,-1);
    tracep->declBit(c+1404,"addr_overflow", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_sfifo ");
    tracep->declBus(c+5234,"BW", false,-1, 31,0);
    tracep->declBus(c+5065,"LGFLEN", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_ASYNC_READ", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_WRITE_ON_FULL", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_READ_ON_EMPTY", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+1244,"i_reset", false,-1);
    tracep->declBit(c+1160,"i_wr", false,-1);
    tracep->declArray(c+1405,"i_data", false,-1, 519,0);
    tracep->declBit(c+1200,"o_full", false,-1);
    tracep->declBus(c+1202,"o_fill", false,-1, 4,0);
    tracep->declBit(c+1181,"i_rd", false,-1);
    tracep->declArray(c+1422,"o_data", false,-1, 519,0);
    tracep->declBit(c+1201,"o_empty", false,-1);
    tracep->declBus(c+5069,"FLEN", false,-1, 31,0);
    tracep->declBit(c+1200,"r_full", false,-1);
    tracep->declBit(c+1201,"r_empty", false,-1);
    for (int i = 0; i < 16; ++i) {
        tracep->declArray(c+1439+i*17,"mem", true,(i+0), 519,0);
    }
    tracep->declBus(c+1711,"wr_addr", false,-1, 4,0);
    tracep->declBus(c+1712,"rd_addr", false,-1, 4,0);
    tracep->declBit(c+1713,"w_wr", false,-1);
    tracep->declBit(c+1714,"w_rd", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_txgears ");
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1108,"i_soft_reset", false,-1);
    tracep->declBus(c+1128,"i_size", false,-1, 1,0);
    tracep->declBit(c+1180,"S_VALID", false,-1);
    tracep->declBit(c+1181,"S_READY", false,-1);
    tracep->declArray(c+1183,"S_DATA", false,-1, 511,0);
    tracep->declBus(c+1199,"S_BYTES", false,-1, 6,0);
    tracep->declBit(c+1182,"S_LAST", false,-1);
    tracep->declBit(c+1203,"M_VALID", false,-1);
    tracep->declBit(c+1204,"M_READY", false,-1);
    tracep->declArray(c+1206,"M_DATA", false,-1, 511,0);
    tracep->declBus(c+1222,"M_BYTES", false,-1, 6,0);
    tracep->declBit(c+1205,"M_LAST", false,-1);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBus(c+5119,"SZ_BYTE", false,-1, 1,0);
    tracep->declBus(c+5118,"SZ_16B", false,-1, 1,0);
    tracep->declBus(c+5117,"SZ_32B", false,-1, 1,0);
    tracep->declBus(c+5116,"SZ_BUS", false,-1, 1,0);
    tracep->declBit(c+1203,"m_valid", false,-1);
    tracep->declBit(c+1205,"m_last", false,-1);
    tracep->declBit(c+1715,"r_last", false,-1);
    tracep->declBit(c+1716,"r_next", false,-1);
    tracep->declArray(c+1206,"sreg", false,-1, 511,0);
    tracep->declBus(c+1222,"m_bytes", false,-1, 6,0);
    tracep->declBus(c+1717,"fill", false,-1, 6,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("GEN_DBG_CATCH ");
    tracep->declBit(c+947,"r_dbg_catch", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("INITIAL_RESET_HOLD ");
    tracep->declBus(c+1718,"reset_counter", false,-1, 4,0);
    tracep->declBit(c+946,"r_reset_hold", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("MAIN_PIC ");
    tracep->pushNamePrefix("pic ");
    tracep->declBus(c+5240,"IUSED", false,-1, 31,0);
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1017,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1017,"o_wb_ack", false,-1);
    tracep->declBus(c+971,"o_wb_data", false,-1, 31,0);
    tracep->declBus(c+898,"i_brd_ints", false,-1, 14,0);
    tracep->declBit(c+1057,"o_interrupt", false,-1);
    tracep->declBus(c+1719,"r_int_state", false,-1, 14,0);
    tracep->declBus(c+1720,"r_int_enable", false,-1, 14,0);
    tracep->declBit(c+1721,"r_mie", false,-1);
    tracep->declBit(c+1722,"w_any", false,-1);
    tracep->declBit(c+1723,"wb_write", false,-1);
    tracep->declBit(c+1724,"enable_ints", false,-1);
    tracep->declBit(c+1725,"disable_ints", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("PIC_WITH_ACCOUNTING ");
    tracep->pushNamePrefix("ALT_PIC ");
    tracep->pushNamePrefix("ctri ");
    tracep->declBus(c+5240,"IUSED", false,-1, 31,0);
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+1007,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1007,"o_wb_ack", false,-1);
    tracep->declBus(c+1008,"o_wb_data", false,-1, 31,0);
    tracep->declBus(c+899,"i_brd_ints", false,-1, 14,0);
    tracep->declBit(c+900,"o_interrupt", false,-1);
    tracep->declBus(c+1726,"r_int_state", false,-1, 14,0);
    tracep->declBus(c+1727,"r_int_enable", false,-1, 14,0);
    tracep->declBit(c+1728,"r_mie", false,-1);
    tracep->declBit(c+1729,"w_any", false,-1);
    tracep->declBit(c+1730,"wb_write", false,-1);
    tracep->declBit(c+1731,"enable_ints", false,-1);
    tracep->declBit(c+1732,"disable_ints", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("dmacvcpu ");
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_ZERO_ON_IDLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+1005,"i_a_cyc", false,-1);
    tracep->declBit(c+1018,"i_a_stb", false,-1);
    tracep->declBit(c+1021,"i_a_we", false,-1);
    tracep->declBus(c+922,"i_a_adr", false,-1, 21,0);
    tracep->declArray(c+1022,"i_a_dat", false,-1, 511,0);
    tracep->declQuad(c+1038,"i_a_sel", false,-1, 63,0);
    tracep->declBit(c+1061,"o_a_stall", false,-1);
    tracep->declBit(c+1062,"o_a_ack", false,-1);
    tracep->declBit(c+1063,"o_a_err", false,-1);
    tracep->declBit(c+981,"i_b_cyc", false,-1);
    tracep->declBit(c+982,"i_b_stb", false,-1);
    tracep->declBit(c+983,"i_b_we", false,-1);
    tracep->declBus(c+986,"i_b_adr", false,-1, 21,0);
    tracep->declArray(c+987,"i_b_dat", false,-1, 511,0);
    tracep->declQuad(c+1003,"i_b_sel", false,-1, 63,0);
    tracep->declBit(c+984,"o_b_stall", false,-1);
    tracep->declBit(c+985,"o_b_ack", false,-1);
    tracep->declBit(c+978,"o_b_err", false,-1);
    tracep->declBit(c+261,"o_cyc", false,-1);
    tracep->declBit(c+262,"o_stb", false,-1);
    tracep->declBit(c+263,"o_we", false,-1);
    tracep->declBus(c+264,"o_adr", false,-1, 21,0);
    tracep->declArray(c+265,"o_dat", false,-1, 511,0);
    tracep->declQuad(c+281,"o_sel", false,-1, 63,0);
    tracep->declBit(c+283,"i_stall", false,-1);
    tracep->declBit(c+284,"i_ack", false,-1);
    tracep->declBit(c+1065,"i_err", false,-1);
    tracep->declBit(c+1733,"r_a_owner", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("thecpu ");
    tracep->declBus(c+5067,"RESET_ADDRESS", false,-1, 31,0);
    tracep->declBus(c+5068,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5158,"OPT_LGICACHE", false,-1, 31,0);
    tracep->declBus(c+5114,"DATA_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5062,"OPT_MPY", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_DIV", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_SHIFTS", false,-1, 0,0);
    tracep->declBus(c+5113,"IMPLEMENT_FPU", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_EARLY_BRANCHING", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CIS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DISTRIBUTED_REGS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PIPELINED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_START_HALTED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOCK", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5158,"OPT_LGDCACHE", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_SIM", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_CLKGATE", false,-1, 0,0);
    tracep->declBus(c+5070,"WITH_LOCAL_BUS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DBGPORT", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_TRACE_PORT", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PROFILER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_USERMODE", false,-1, 0,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1057,"i_interrupt", false,-1);
    tracep->declBit(c+916,"i_cpu_clken", false,-1);
    tracep->declBit(c+954,"i_halt", false,-1);
    tracep->declBit(c+956,"i_clear_cache", false,-1);
    tracep->declBus(c+959,"i_dbg_wreg", false,-1, 4,0);
    tracep->declBit(c+957,"i_dbg_we", false,-1);
    tracep->declBus(c+960,"i_dbg_data", false,-1, 31,0);
    tracep->declBus(c+1734,"i_dbg_rreg", false,-1, 4,0);
    tracep->declBit(c+963,"o_dbg_stall", false,-1);
    tracep->declBit(c+962,"o_halted", false,-1);
    tracep->declBus(c+1060,"o_dbg_reg", false,-1, 31,0);
    tracep->declBus(c+961,"o_dbg_cc", false,-1, 2,0);
    tracep->declBit(c+942,"o_break", false,-1);
    tracep->declBit(c+1005,"o_wb_gbl_cyc", false,-1);
    tracep->declBit(c+1018,"o_wb_gbl_stb", false,-1);
    tracep->declBit(c+1019,"o_wb_lcl_cyc", false,-1);
    tracep->declBit(c+1020,"o_wb_lcl_stb", false,-1);
    tracep->declBit(c+1021,"o_wb_we", false,-1);
    tracep->declBus(c+922,"o_wb_addr", false,-1, 21,0);
    tracep->declArray(c+1022,"o_wb_data", false,-1, 511,0);
    tracep->declQuad(c+1038,"o_wb_sel", false,-1, 63,0);
    tracep->declBit(c+1056,"i_wb_stall", false,-1);
    tracep->declBit(c+1058,"i_wb_ack", false,-1);
    tracep->declArray(c+1040,"i_wb_data", false,-1, 511,0);
    tracep->declBit(c+1059,"i_wb_err", false,-1);
    tracep->declBit(c+48,"o_op_stall", false,-1);
    tracep->declBit(c+975,"o_pf_stall", false,-1);
    tracep->declBit(c+976,"o_i_count", false,-1);
    tracep->declBus(c+5076,"o_debug", false,-1, 31,0);
    tracep->declBit(c+4996,"o_prof_stb", false,-1);
    tracep->declBus(c+4997,"o_prof_addr", false,-1, 27,0);
    tracep->declBus(c+4998,"o_prof_ticks", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_DCACHE", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PIPELINED_BUS_ACCESS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_MEMPIPE", false,-1, 0,0);
    tracep->declBus(c+5114,"INSN_WIDTH", false,-1, 31,0);
    tracep->declBit(c+5077,"cpu_clken", false,-1);
    tracep->declBit(c+4901,"cpu_clock", false,-1);
    tracep->declBit(c+5077,"clk_gate", false,-1);
    tracep->declBus(c+5076,"cpu_debug", false,-1, 31,0);
    tracep->declBit(c+1735,"pf_new_pc", false,-1);
    tracep->declBit(c+1736,"clear_icache", false,-1);
    tracep->declBit(c+50,"pf_ready", false,-1);
    tracep->declBus(c+1737,"pf_request_address", false,-1, 27,0);
    tracep->declBus(c+1738,"pf_instruction", false,-1, 31,0);
    tracep->declBus(c+1739,"pf_instruction_pc", false,-1, 27,0);
    tracep->declBit(c+1740,"pf_valid", false,-1);
    tracep->declBit(c+1741,"pf_illegal", false,-1);
    tracep->declBit(c+1742,"pf_cyc", false,-1);
    tracep->declBit(c+1743,"pf_stb", false,-1);
    tracep->declBit(c+1744,"pf_stall", false,-1);
    tracep->declBit(c+1745,"pf_ack", false,-1);
    tracep->declBit(c+1746,"pf_err", false,-1);
    tracep->declBus(c+1747,"pf_addr", false,-1, 21,0);
    tracep->declBit(c+5074,"pf_we", false,-1);
    tracep->declArray(c+5078,"pf_data", false,-1, 511,0);
    tracep->declBit(c+1748,"clear_dcache", false,-1);
    tracep->declBit(c+51,"mem_ce", false,-1);
    tracep->declBit(c+1749,"bus_lock", false,-1);
    tracep->declBus(c+1750,"mem_op", false,-1, 2,0);
    tracep->declBus(c+1751,"mem_cpu_addr", false,-1, 31,0);
    tracep->declBus(c+1752,"mem_lock_pc", false,-1, 27,0);
    tracep->declBus(c+1753,"mem_wdata", false,-1, 31,0);
    tracep->declArray(c+1022,"mem_data", false,-1, 511,0);
    tracep->declBus(c+1754,"mem_reg", false,-1, 4,0);
    tracep->declBit(c+1755,"mem_busy", false,-1);
    tracep->declBit(c+1756,"mem_rdbusy", false,-1);
    tracep->declBit(c+1757,"mem_pipe_stalled", false,-1);
    tracep->declBit(c+1758,"mem_valid", false,-1);
    tracep->declBit(c+1759,"mem_bus_err", false,-1);
    tracep->declBus(c+1760,"mem_wreg", false,-1, 4,0);
    tracep->declBus(c+1761,"mem_result", false,-1, 31,0);
    tracep->declBit(c+1762,"mem_stb_lcl", false,-1);
    tracep->declBit(c+1763,"mem_stb_gbl", false,-1);
    tracep->declBit(c+1764,"mem_cyc_lcl", false,-1);
    tracep->declBit(c+1765,"mem_cyc_gbl", false,-1);
    tracep->declBus(c+1766,"mem_bus_addr", false,-1, 21,0);
    tracep->declBit(c+1767,"mem_we", false,-1);
    tracep->declBit(c+1768,"mem_stall", false,-1);
    tracep->declBit(c+1769,"mem_ack", false,-1);
    tracep->declBit(c+1770,"mem_err", false,-1);
    tracep->declQuad(c+1771,"mem_sel", false,-1, 63,0);
    tracep->declBit(c+963,"w_dbg_stall", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("DATA_CACHE ");
    tracep->pushNamePrefix("mem ");
    tracep->declBus(c+5153,"LGCACHELEN", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5068,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5062,"LGNLINES", false,-1, 31,0);
    tracep->declBus(c+5154,"NAUX", false,-1, 31,0);
    tracep->declBus(c+5114,"DATA_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_LOCAL_BUS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PIPE", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOCK", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DUAL_READ_PORT", false,-1, 0,0);
    tracep->declBus(c+5065,"OPT_FIFO_DEPTH", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5153,"CS", false,-1, 31,0);
    tracep->declBus(c+5062,"LS", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5065,"DP", false,-1, 31,0);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBus(c+5116,"DC_IDLE", false,-1, 1,0);
    tracep->declBus(c+5117,"DC_WRITE", false,-1, 1,0);
    tracep->declBus(c+5118,"DC_READS", false,-1, 1,0);
    tracep->declBus(c+5119,"DC_READC", false,-1, 1,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1748,"i_clear", false,-1);
    tracep->declBit(c+51,"i_pipe_stb", false,-1);
    tracep->declBit(c+1749,"i_lock", false,-1);
    tracep->declBus(c+1750,"i_op", false,-1, 2,0);
    tracep->declBus(c+1751,"i_addr", false,-1, 31,0);
    tracep->declBus(c+1753,"i_data", false,-1, 31,0);
    tracep->declBus(c+1754,"i_oreg", false,-1, 4,0);
    tracep->declBit(c+1755,"o_busy", false,-1);
    tracep->declBit(c+1756,"o_rdbusy", false,-1);
    tracep->declBit(c+1757,"o_pipe_stalled", false,-1);
    tracep->declBit(c+1758,"o_valid", false,-1);
    tracep->declBit(c+1759,"o_err", false,-1);
    tracep->declBus(c+1760,"o_wreg", false,-1, 4,0);
    tracep->declBus(c+1761,"o_data", false,-1, 31,0);
    tracep->declBit(c+1765,"o_wb_cyc_gbl", false,-1);
    tracep->declBit(c+1764,"o_wb_cyc_lcl", false,-1);
    tracep->declBit(c+1763,"o_wb_stb_gbl", false,-1);
    tracep->declBit(c+1762,"o_wb_stb_lcl", false,-1);
    tracep->declBit(c+1767,"o_wb_we", false,-1);
    tracep->declBus(c+1766,"o_wb_addr", false,-1, 21,0);
    tracep->declArray(c+1022,"o_wb_data", false,-1, 511,0);
    tracep->declQuad(c+1771,"o_wb_sel", false,-1, 63,0);
    tracep->declBit(c+1768,"i_wb_stall", false,-1);
    tracep->declBit(c+1769,"i_wb_ack", false,-1);
    tracep->declBit(c+1770,"i_wb_err", false,-1);
    tracep->declArray(c+1040,"i_wb_data", false,-1, 511,0);
    tracep->declBus(c+5158,"FIF_WIDTH", false,-1, 31,0);
    tracep->declBus(c+1773,"ik", false,-1, 31,0);
    tracep->declBit(c+1774,"cyc", false,-1);
    tracep->declBit(c+1775,"stb", false,-1);
    tracep->declBit(c+1776,"last_ack", false,-1);
    tracep->declBit(c+1777,"end_of_line", false,-1);
    tracep->declBit(c+1778,"last_line_stb", false,-1);
    tracep->declBit(c+1779,"r_wb_cyc_gbl", false,-1);
    tracep->declBit(c+1780,"r_wb_cyc_lcl", false,-1);
    tracep->declBus(c+1781,"npending", false,-1, 4,0);
    tracep->declBus(c+1782,"c_v", false,-1, 7,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+1783+i*1,"c_vtags", true,(i+0), 18,0);
    }
    tracep->declBit(c+1791,"set_vflag", false,-1);
    tracep->declBus(c+1792,"state", false,-1, 1,0);
    tracep->declBus(c+1793,"wr_addr", false,-1, 5,0);
    tracep->declArray(c+1794,"cached_iword", false,-1, 511,0);
    tracep->declArray(c+1810,"cached_rword", false,-1, 511,0);
    tracep->declBit(c+1826,"lock_gbl", false,-1);
    tracep->declBit(c+1827,"lock_lcl", false,-1);
    tracep->declBit(c+1828,"c_wr", false,-1);
    tracep->declArray(c+1829,"c_wdata", false,-1, 511,0);
    tracep->declQuad(c+1845,"c_wsel", false,-1, 63,0);
    tracep->declBus(c+1847,"c_waddr", false,-1, 5,0);
    tracep->declBus(c+1848,"last_tag", false,-1, 18,0);
    tracep->declBit(c+1849,"last_tag_valid", false,-1);
    tracep->declBus(c+1850,"i_cline", false,-1, 2,0);
    tracep->declBus(c+1851,"i_caddr", false,-1, 5,0);
    tracep->declBit(c+1852,"cache_miss_inow", false,-1);
    tracep->declBit(c+1853,"w_cachable", false,-1);
    tracep->declBit(c+1854,"raw_cachable_address", false,-1);
    tracep->declBit(c+1855,"r_cachable", false,-1);
    tracep->declBit(c+1856,"r_svalid", false,-1);
    tracep->declBit(c+1857,"r_dvalid", false,-1);
    tracep->declBit(c+1858,"r_rd", false,-1);
    tracep->declBit(c+1859,"r_cache_miss", false,-1);
    tracep->declBit(c+1860,"r_rd_pending", false,-1);
    tracep->declBus(c+1861,"r_addr", false,-1, 21,0);
    tracep->declBus(c+1862,"r_cline", false,-1, 2,0);
    tracep->declBus(c+1863,"r_caddr", false,-1, 5,0);
    tracep->declBus(c+1864,"r_ctag", false,-1, 18,0);
    tracep->declBit(c+1865,"wr_cstb", false,-1);
    tracep->declBit(c+1866,"r_iv", false,-1);
    tracep->declBit(c+1867,"in_cache", false,-1);
    tracep->declBus(c+1868,"r_itag", false,-1, 18,0);
    tracep->declBus(c+1869,"req_data", false,-1, 12,0);
    tracep->declBit(c+1870,"gie", false,-1);
    tracep->declArray(c+1871,"pre_data", false,-1, 511,0);
    tracep->declArray(c+1887,"pre_shifted", false,-1, 511,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_SEL ");
    tracep->declBus(c+1903,"pre_sel", false,-1, 3,0);
    tracep->declQuad(c+1904,"full_sel", false,-1, 63,0);
    tracep->declQuad(c+1771,"r_wb_sel", false,-1, 63,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_WIDE_BUS ");
    tracep->declBus(c+1906,"pre_shift", false,-1, 31,0);
    tracep->declArray(c+1907,"wide_preshift", false,-1, 511,0);
    tracep->declArray(c+1923,"shifted_data", false,-1, 511,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_PIPE_FIFO ");
    for (int i = 0; i < 16; ++i) {
        tracep->declBus(c+1939+i*1,"fifo_data", true,(i+0), 11,0);
    }
    tracep->declBus(c+1955,"wraddr", false,-1, 4,0);
    tracep->declBus(c+1956,"rdaddr", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("UNUSED_BITS ");
    tracep->declBit(c+5241,"unused_aw", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("chkaddress ");
    tracep->declBus(c+1957,"i_addr", false,-1, 27,0);
    tracep->declBit(c+1854,"o_cachable", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("NO_CLOCK_GATE ");
    tracep->declBit(c+5074,"unused_clk", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("PFCACHE ");
    tracep->pushNamePrefix("pf ");
    tracep->declBus(c+5153,"LGCACHELEN", false,-1, 31,0);
    tracep->declBus(c+5068,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5062,"LGLINES", false,-1, 31,0);
    tracep->declBus(c+5111,"BUS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5120,"CACHELEN", false,-1, 31,0);
    tracep->declBus(c+5153,"CW", false,-1, 31,0);
    tracep->declBus(c+5062,"LS", false,-1, 31,0);
    tracep->declBus(c+5111,"BUSW", false,-1, 31,0);
    tracep->declBus(c+5114,"INSN_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1735,"i_new_pc", false,-1);
    tracep->declBit(c+1736,"i_clear_cache", false,-1);
    tracep->declBit(c+50,"i_ready", false,-1);
    tracep->declBus(c+1737,"i_pc", false,-1, 27,0);
    tracep->declBit(c+1740,"o_valid", false,-1);
    tracep->declBit(c+1741,"o_illegal", false,-1);
    tracep->declBus(c+1738,"o_insn", false,-1, 31,0);
    tracep->declBus(c+1739,"o_pc", false,-1, 27,0);
    tracep->declBit(c+1742,"o_wb_cyc", false,-1);
    tracep->declBit(c+1743,"o_wb_stb", false,-1);
    tracep->declBit(c+5074,"o_wb_we", false,-1);
    tracep->declBus(c+1747,"o_wb_addr", false,-1, 21,0);
    tracep->declArray(c+5078,"o_wb_data", false,-1, 511,0);
    tracep->declBit(c+1744,"i_wb_stall", false,-1);
    tracep->declBit(c+1745,"i_wb_ack", false,-1);
    tracep->declBit(c+1746,"i_wb_err", false,-1);
    tracep->declArray(c+1040,"i_wb_data", false,-1, 511,0);
    tracep->declBus(c+5075,"INLSB", false,-1, 31,0);
    tracep->declBit(c+1958,"r_v", false,-1);
    tracep->declArray(c+1959,"cache_word", false,-1, 511,0);
    for (int i = 0; i < 8; ++i) {
        tracep->declBus(c+1975+i*1,"cache_tags", true,(i+0), 15,0);
    }
    tracep->declBus(c+1983,"valid_mask", false,-1, 7,0);
    tracep->declBit(c+1984,"r_v_from_pc", false,-1);
    tracep->declBit(c+1985,"r_v_from_last", false,-1);
    tracep->declBit(c+1986,"rvsrc", false,-1);
    tracep->declBit(c+1987,"w_v_from_pc", false,-1);
    tracep->declBit(c+1988,"w_v_from_last", false,-1);
    tracep->declBus(c+1989,"lastpc", false,-1, 27,0);
    tracep->declBus(c+1990,"wraddr", false,-1, 5,0);
    tracep->declBus(c+1991,"pc_tag_lookup", false,-1, 21,3);
    tracep->declBus(c+1992,"last_tag_lookup", false,-1, 21,3);
    tracep->declBus(c+1993,"tag_lookup", false,-1, 21,3);
    tracep->declBus(c+1994,"pc_tag", false,-1, 21,3);
    tracep->declBus(c+1995,"lasttag", false,-1, 21,3);
    tracep->declBit(c+1996,"illegal_valid", false,-1);
    tracep->declBus(c+1997,"illegal_cache", false,-1, 21,3);
    tracep->declArray(c+1998,"r_pc_cache", false,-1, 511,0);
    tracep->declArray(c+2014,"r_last_cache", false,-1, 511,0);
    tracep->declBus(c+1739,"r_pc", false,-1, 27,0);
    tracep->declBit(c+2030,"isrc", false,-1);
    tracep->declBus(c+2031,"delay", false,-1, 1,0);
    tracep->declBit(c+2032,"svmask", false,-1);
    tracep->declBit(c+2033,"last_ack", false,-1);
    tracep->declBit(c+2034,"needload", false,-1);
    tracep->declBit(c+2035,"last_addr", false,-1);
    tracep->declBit(c+2036,"bus_abort", false,-1);
    tracep->declBus(c+2037,"saddr", false,-1, 2,0);
    tracep->declBit(c+52,"w_advance", false,-1);
    tracep->declBit(c+2038,"w_invalidate_result", false,-1);
    tracep->declBus(c+2039,"pc_line", false,-1, 2,0);
    tracep->declBus(c+2040,"last_line", false,-1, 2,0);
    tracep->pushNamePrefix("SHIFT_INSN ");
    tracep->declArray(c+2041,"shifted", false,-1, 511,0);
    tracep->declBus(c+2057,"shift", false,-1, 3,0);
    tracep->declBit(c+5074,"unused_shift", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("PRIORITY_DATA ");
    tracep->pushNamePrefix("pformem ");
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_ZERO_ON_IDLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1765,"i_a_cyc_a", false,-1);
    tracep->declBit(c+1764,"i_a_cyc_b", false,-1);
    tracep->declBit(c+1763,"i_a_stb_a", false,-1);
    tracep->declBit(c+1762,"i_a_stb_b", false,-1);
    tracep->declBit(c+1767,"i_a_we", false,-1);
    tracep->declBus(c+1766,"i_a_adr", false,-1, 21,0);
    tracep->declArray(c+1022,"i_a_dat", false,-1, 511,0);
    tracep->declQuad(c+1771,"i_a_sel", false,-1, 63,0);
    tracep->declBit(c+1768,"o_a_stall", false,-1);
    tracep->declBit(c+1769,"o_a_ack", false,-1);
    tracep->declBit(c+1770,"o_a_err", false,-1);
    tracep->declBit(c+1742,"i_b_cyc_a", false,-1);
    tracep->declBit(c+5074,"i_b_cyc_b", false,-1);
    tracep->declBit(c+1743,"i_b_stb_a", false,-1);
    tracep->declBit(c+5074,"i_b_stb_b", false,-1);
    tracep->declBit(c+5074,"i_b_we", false,-1);
    tracep->declBus(c+1747,"i_b_adr", false,-1, 21,0);
    tracep->declArray(c+1022,"i_b_dat", false,-1, 511,0);
    tracep->declQuad(c+5094,"i_b_sel", false,-1, 63,0);
    tracep->declBit(c+1744,"o_b_stall", false,-1);
    tracep->declBit(c+1745,"o_b_ack", false,-1);
    tracep->declBit(c+1746,"o_b_err", false,-1);
    tracep->declBit(c+1005,"o_cyc_a", false,-1);
    tracep->declBit(c+1019,"o_cyc_b", false,-1);
    tracep->declBit(c+1018,"o_stb_a", false,-1);
    tracep->declBit(c+1020,"o_stb_b", false,-1);
    tracep->declBit(c+1021,"o_we", false,-1);
    tracep->declBus(c+922,"o_adr", false,-1, 21,0);
    tracep->declArray(c+1022,"o_dat", false,-1, 511,0);
    tracep->declQuad(c+1038,"o_sel", false,-1, 63,0);
    tracep->declBit(c+1056,"i_stall", false,-1);
    tracep->declBit(c+1058,"i_ack", false,-1);
    tracep->declBit(c+1059,"i_err", false,-1);
    tracep->declBit(c+2058,"r_a_owner", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("core ");
    tracep->declBus(c+5131,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5067,"RESET_ADDRESS", false,-1, 31,0);
    tracep->declBus(c+5062,"OPT_MPY", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_SHIFTS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DIV", false,-1, 0,0);
    tracep->declBus(c+5113,"IMPLEMENT_FPU", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_EARLY_BRANCHING", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CIS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_SIM", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DISTRIBUTED_REGS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PIPELINED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PIPELINED_BUS_ACCESS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOCK", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DCACHE", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_USERMODE", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_CLKGATE", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_START_HALTED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DBGPORT", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_TRACE_PORT", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PROFILER", false,-1, 0,0);
    tracep->declBus(c+5131,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1057,"i_interrupt", false,-1);
    tracep->declBit(c+5077,"o_clken", false,-1);
    tracep->declBit(c+954,"i_halt", false,-1);
    tracep->declBit(c+956,"i_clear_cache", false,-1);
    tracep->declBus(c+959,"i_dbg_wreg", false,-1, 4,0);
    tracep->declBit(c+957,"i_dbg_we", false,-1);
    tracep->declBus(c+960,"i_dbg_data", false,-1, 31,0);
    tracep->declBus(c+1734,"i_dbg_rreg", false,-1, 4,0);
    tracep->declBit(c+963,"o_dbg_stall", false,-1);
    tracep->declBus(c+1060,"o_dbg_reg", false,-1, 31,0);
    tracep->declBus(c+961,"o_dbg_cc", false,-1, 2,0);
    tracep->declBit(c+942,"o_break", false,-1);
    tracep->declBit(c+1735,"o_pf_new_pc", false,-1);
    tracep->declBit(c+1736,"o_clear_icache", false,-1);
    tracep->declBit(c+50,"o_pf_ready", false,-1);
    tracep->declBus(c+1737,"o_pf_request_address", false,-1, 27,0);
    tracep->declBit(c+1740,"i_pf_valid", false,-1);
    tracep->declBit(c+1741,"i_pf_illegal", false,-1);
    tracep->declBus(c+1738,"i_pf_instruction", false,-1, 31,0);
    tracep->declBus(c+1739,"i_pf_instruction_pc", false,-1, 27,0);
    tracep->declBit(c+1748,"o_clear_dcache", false,-1);
    tracep->declBit(c+51,"o_mem_ce", false,-1);
    tracep->declBit(c+1749,"o_bus_lock", false,-1);
    tracep->declBus(c+1750,"o_mem_op", false,-1, 2,0);
    tracep->declBus(c+1751,"o_mem_addr", false,-1, 31,0);
    tracep->declBus(c+1753,"o_mem_data", false,-1, 31,0);
    tracep->declBus(c+1752,"o_mem_lock_pc", false,-1, 27,0);
    tracep->declBus(c+1754,"o_mem_reg", false,-1, 4,0);
    tracep->declBit(c+1755,"i_mem_busy", false,-1);
    tracep->declBit(c+1756,"i_mem_rdbusy", false,-1);
    tracep->declBit(c+1757,"i_mem_pipe_stalled", false,-1);
    tracep->declBit(c+1758,"i_mem_valid", false,-1);
    tracep->declBit(c+1759,"i_bus_err", false,-1);
    tracep->declBus(c+1760,"i_mem_wreg", false,-1, 4,0);
    tracep->declBus(c+1761,"i_mem_result", false,-1, 31,0);
    tracep->declBit(c+48,"o_op_stall", false,-1);
    tracep->declBit(c+975,"o_pf_stall", false,-1);
    tracep->declBit(c+976,"o_i_count", false,-1);
    tracep->declBus(c+5076,"o_debug", false,-1, 31,0);
    tracep->declBit(c+4996,"o_prof_stb", false,-1);
    tracep->declBus(c+4997,"o_prof_addr", false,-1, 27,0);
    tracep->declBus(c+4998,"o_prof_ticks", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_MEMPIPE", false,-1, 0,0);
    tracep->declBus(c+5242,"RESET_BUS_ADDRESS", false,-1, 25,0);
    tracep->declBus(c+5243,"CPU_CC_REG", false,-1, 3,0);
    tracep->declBus(c+5108,"CPU_PC_REG", false,-1, 3,0);
    tracep->declBus(c+5122,"CPU_SUB_OP", false,-1, 3,0);
    tracep->declBus(c+5123,"CPU_AND_OP", false,-1, 3,0);
    tracep->declBus(c+5129,"CPU_BREV_OP", false,-1, 3,0);
    tracep->declBus(c+5206,"CPU_MOV_OP", false,-1, 3,0);
    tracep->declBus(c+5240,"CPU_CLRDCACHE_BIT", false,-1, 31,0);
    tracep->declBus(c+5060,"CPU_CLRICACHE_BIT", false,-1, 31,0);
    tracep->declBus(c+5136,"CPU_PHASE_BIT", false,-1, 31,0);
    tracep->declBus(c+5158,"CPU_FPUERR_BIT", false,-1, 31,0);
    tracep->declBus(c+5157,"CPU_DIVERR_BIT", false,-1, 31,0);
    tracep->declBus(c+5061,"CPU_BUSERR_BIT", false,-1, 31,0);
    tracep->declBus(c+5156,"CPU_TRAP_BIT", false,-1, 31,0);
    tracep->declBus(c+5063,"CPU_ILL_BIT", false,-1, 31,0);
    tracep->declBus(c+5072,"CPU_BREAK_BIT", false,-1, 31,0);
    tracep->declBus(c+5153,"CPU_STEP_BIT", false,-1, 31,0);
    tracep->declBus(c+5154,"CPU_GIE_BIT", false,-1, 31,0);
    tracep->declBus(c+5065,"CPU_SLEEP_BIT", false,-1, 31,0);
    for (int i = 0; i < 32; ++i) {
        tracep->declBus(c+2059+i*1,"regset", true,(i+0), 31,0);
    }
    tracep->declBus(c+2091,"flags", false,-1, 3,0);
    tracep->declBus(c+2092,"iflags", false,-1, 3,0);
    tracep->declBus(c+2093,"w_uflags", false,-1, 15,0);
    tracep->declBus(c+2094,"w_iflags", false,-1, 15,0);
    tracep->declBit(c+2095,"break_en", false,-1);
    tracep->declBit(c+2096,"user_step", false,-1);
    tracep->declBit(c+2097,"sleep", false,-1);
    tracep->declBit(c+2098,"r_halted", false,-1);
    tracep->declBit(c+2099,"break_pending", false,-1);
    tracep->declBit(c+2100,"trap", false,-1);
    tracep->declBit(c+2101,"gie", false,-1);
    tracep->declBit(c+2102,"ubreak", false,-1);
    tracep->declBit(c+2103,"pending_interrupt", false,-1);
    tracep->declBit(c+2104,"stepped", false,-1);
    tracep->declBit(c+2105,"step", false,-1);
    tracep->declBit(c+2106,"ill_err_u", false,-1);
    tracep->declBit(c+2107,"ill_err_i", false,-1);
    tracep->declBit(c+2108,"ibus_err_flag", false,-1);
    tracep->declBit(c+2109,"ubus_err_flag", false,-1);
    tracep->declBit(c+2110,"idiv_err_flag", false,-1);
    tracep->declBit(c+2111,"udiv_err_flag", false,-1);
    tracep->declBit(c+5074,"ifpu_err_flag", false,-1);
    tracep->declBit(c+5074,"ufpu_err_flag", false,-1);
    tracep->declBit(c+2112,"ihalt_phase", false,-1);
    tracep->declBit(c+2113,"uhalt_phase", false,-1);
    tracep->declBit(c+2114,"master_ce", false,-1);
    tracep->declBit(c+53,"master_stall", false,-1);
    tracep->declBus(c+2115,"pf_pc", false,-1, 27,0);
    tracep->declBit(c+2116,"new_pc", false,-1);
    tracep->declBit(c+2116,"clear_pipeline", false,-1);
    tracep->declBit(c+54,"dcd_stalled", false,-1);
    tracep->declBit(c+2101,"pf_gie", false,-1);
    tracep->declBus(c+2117,"dcd_opn", false,-1, 3,0);
    tracep->declBit(c+55,"dcd_ce", false,-1);
    tracep->declBit(c+2118,"dcd_phase", false,-1);
    tracep->declBus(c+2119,"dcd_A", false,-1, 4,0);
    tracep->declBus(c+2120,"dcd_B", false,-1, 4,0);
    tracep->declBus(c+2121,"dcd_R", false,-1, 4,0);
    tracep->declBus(c+2122,"dcd_preA", false,-1, 4,0);
    tracep->declBus(c+2123,"dcd_preB", false,-1, 4,0);
    tracep->declBit(c+2124,"dcd_Acc", false,-1);
    tracep->declBit(c+2125,"dcd_Bcc", false,-1);
    tracep->declBit(c+2126,"dcd_Apc", false,-1);
    tracep->declBit(c+2127,"dcd_Bpc", false,-1);
    tracep->declBit(c+2128,"dcd_Rcc", false,-1);
    tracep->declBit(c+2129,"dcd_Rpc", false,-1);
    tracep->declBus(c+2130,"dcd_F", false,-1, 3,0);
    tracep->declBit(c+2131,"dcd_wR", false,-1);
    tracep->declBit(c+2132,"dcd_rA", false,-1);
    tracep->declBit(c+2133,"dcd_rB", false,-1);
    tracep->declBit(c+2134,"dcd_ALU", false,-1);
    tracep->declBit(c+2135,"dcd_M", false,-1);
    tracep->declBit(c+2136,"dcd_DIV", false,-1);
    tracep->declBit(c+2137,"dcd_FP", false,-1);
    tracep->declBit(c+2138,"dcd_wF", false,-1);
    tracep->declBit(c+2101,"dcd_gie", false,-1);
    tracep->declBit(c+2139,"dcd_break", false,-1);
    tracep->declBit(c+2140,"dcd_lock", false,-1);
    tracep->declBit(c+2141,"dcd_pipe", false,-1);
    tracep->declBit(c+2142,"dcd_ljmp", false,-1);
    tracep->declBit(c+2143,"dcd_valid", false,-1);
    tracep->declBus(c+5017,"dcd_pc", false,-1, 27,0);
    tracep->declBus(c+2144,"dcd_I", false,-1, 31,0);
    tracep->declBit(c+2145,"dcd_zI", false,-1);
    tracep->declBit(c+56,"dcd_A_stall", false,-1);
    tracep->declBit(c+57,"dcd_B_stall", false,-1);
    tracep->declBit(c+5018,"dcd_F_stall", false,-1);
    tracep->declBit(c+2146,"dcd_illegal", false,-1);
    tracep->declBit(c+2147,"dcd_early_branch", false,-1);
    tracep->declBit(c+2148,"dcd_early_branch_stb", false,-1);
    tracep->declBus(c+2149,"dcd_branch_pc", false,-1, 27,0);
    tracep->declBit(c+5019,"dcd_sim", false,-1);
    tracep->declBus(c+5020,"dcd_sim_immv", false,-1, 22,0);
    tracep->declBit(c+2150,"prelock_stall", false,-1);
    tracep->declBit(c+2151,"last_lock_insn", false,-1);
    tracep->declBit(c+2152,"cc_invalid_for_dcd", false,-1);
    tracep->declBit(c+2153,"pending_sreg_write", false,-1);
    tracep->declBit(c+5021,"op_valid", false,-1);
    tracep->declBit(c+2154,"op_valid_mem", false,-1);
    tracep->declBit(c+2155,"op_valid_alu", false,-1);
    tracep->declBit(c+2156,"op_valid_div", false,-1);
    tracep->declBit(c+2157,"op_valid_fpu", false,-1);
    tracep->declBit(c+58,"op_stall", false,-1);
    tracep->declBus(c+2158,"op_opn", false,-1, 3,0);
    tracep->declBus(c+1754,"op_R", false,-1, 4,0);
    tracep->declBit(c+2159,"op_Rcc", false,-1);
    tracep->declBus(c+2160,"op_Aid", false,-1, 4,0);
    tracep->declBus(c+2161,"op_Bid", false,-1, 4,0);
    tracep->declBit(c+2162,"op_rA", false,-1);
    tracep->declBit(c+2163,"op_rB", false,-1);
    tracep->declBus(c+2164,"r_op_Av", false,-1, 31,0);
    tracep->declBus(c+2165,"r_op_Bv", false,-1, 31,0);
    tracep->declBus(c+2166,"op_pc", false,-1, 27,0);
    tracep->declBus(c+2167,"w_op_Av", false,-1, 31,0);
    tracep->declBus(c+2168,"w_op_Bv", false,-1, 31,0);
    tracep->declBus(c+1753,"op_Av", false,-1, 31,0);
    tracep->declBus(c+1751,"op_Bv", false,-1, 31,0);
    tracep->declBus(c+59,"w_pcB_v", false,-1, 31,0);
    tracep->declBus(c+60,"w_pcA_v", false,-1, 31,0);
    tracep->declBus(c+2169,"w_op_BnI", false,-1, 31,0);
    tracep->declBit(c+2170,"op_wR", false,-1);
    tracep->declBit(c+2171,"op_wF", false,-1);
    tracep->declBit(c+2101,"op_gie", false,-1);
    tracep->declBus(c+2172,"op_Fl", false,-1, 3,0);
    tracep->declBus(c+2173,"r_op_F", false,-1, 6,0);
    tracep->declBus(c+2174,"op_F", false,-1, 7,0);
    tracep->declBit(c+61,"op_ce", false,-1);
    tracep->declBit(c+2175,"op_phase", false,-1);
    tracep->declBit(c+2176,"op_pipe", false,-1);
    tracep->declBit(c+2177,"r_op_break", false,-1);
    tracep->declBit(c+2178,"w_op_valid", false,-1);
    tracep->declBit(c+5074,"op_lowpower_clear", false,-1);
    tracep->declBus(c+5244,"w_cpu_info", false,-1, 8,0);
    tracep->declBit(c+2179,"op_illegal", false,-1);
    tracep->declBit(c+2177,"op_break", false,-1);
    tracep->declBit(c+2180,"op_lock", false,-1);
    tracep->declBit(c+5022,"op_sim", false,-1);
    tracep->declBus(c+5023,"op_sim_immv", false,-1, 22,0);
    tracep->declBit(c+5024,"alu_sim", false,-1);
    tracep->declBus(c+5025,"alu_sim_immv", false,-1, 22,0);
    tracep->declBus(c+2181,"alu_pc", false,-1, 27,0);
    tracep->declBus(c+2182,"alu_reg", false,-1, 4,0);
    tracep->declBit(c+2183,"r_alu_pc_valid", false,-1);
    tracep->declBit(c+2184,"mem_pc_valid", false,-1);
    tracep->declBit(c+2185,"alu_pc_valid", false,-1);
    tracep->declBit(c+2186,"alu_phase", false,-1);
    tracep->declBit(c+5026,"alu_ce", false,-1);
    tracep->declBit(c+62,"alu_stall", false,-1);
    tracep->declBus(c+2187,"alu_result", false,-1, 31,0);
    tracep->declBus(c+2188,"alu_flags", false,-1, 3,0);
    tracep->declBit(c+2189,"alu_valid", false,-1);
    tracep->declBit(c+2190,"alu_busy", false,-1);
    tracep->declBit(c+2191,"set_cond", false,-1);
    tracep->declBit(c+2192,"alu_wR", false,-1);
    tracep->declBit(c+2193,"alu_wF", false,-1);
    tracep->declBit(c+2101,"alu_gie", false,-1);
    tracep->declBit(c+2194,"alu_illegal", false,-1);
    tracep->declBit(c+63,"mem_ce", false,-1);
    tracep->declBit(c+64,"mem_stalled", false,-1);
    tracep->declBit(c+65,"div_ce", false,-1);
    tracep->declBit(c+2195,"div_error", false,-1);
    tracep->declBit(c+2196,"div_busy", false,-1);
    tracep->declBit(c+2197,"div_valid", false,-1);
    tracep->declBus(c+2198,"div_result", false,-1, 31,0);
    tracep->declBus(c+2199,"div_flags", false,-1, 3,0);
    tracep->declBit(c+5074,"fpu_ce", false,-1);
    tracep->declBit(c+5074,"fpu_error", false,-1);
    tracep->declBit(c+5074,"fpu_busy", false,-1);
    tracep->declBit(c+5074,"fpu_valid", false,-1);
    tracep->declBus(c+5076,"fpu_result", false,-1, 31,0);
    tracep->declBus(c+5122,"fpu_flags", false,-1, 3,0);
    tracep->declBit(c+66,"adf_ce_unconditional", false,-1);
    tracep->declBit(c+2200,"dbgv", false,-1);
    tracep->declBit(c+2201,"dbg_clear_pipe", false,-1);
    tracep->declBus(c+2202,"dbg_val", false,-1, 31,0);
    tracep->declBus(c+2203,"debug_pc", false,-1, 31,0);
    tracep->declBit(c+2204,"r_dbg_stall", false,-1);
    tracep->declBit(c+2205,"wr_write_pc", false,-1);
    tracep->declBit(c+2206,"wr_write_cc", false,-1);
    tracep->declBit(c+2207,"wr_write_scc", false,-1);
    tracep->declBit(c+2208,"wr_write_ucc", false,-1);
    tracep->declBit(c+2209,"wr_reg_ce", false,-1);
    tracep->declBit(c+2210,"wr_flags_ce", false,-1);
    tracep->declBus(c+2211,"wr_flags", false,-1, 3,0);
    tracep->declBus(c+2212,"wr_index", false,-1, 2,0);
    tracep->declBus(c+2213,"wr_reg_id", false,-1, 4,0);
    tracep->declBus(c+2214,"wr_gpreg_vl", false,-1, 31,0);
    tracep->declBus(c+2215,"wr_spreg_vl", false,-1, 31,0);
    tracep->declBit(c+2216,"w_switch_to_interrupt", false,-1);
    tracep->declBit(c+2217,"w_release_from_interrupt", false,-1);
    tracep->declBus(c+2218,"ipc", false,-1, 27,0);
    tracep->declBus(c+2219,"upc", false,-1, 27,0);
    tracep->declBit(c+2220,"last_write_to_cc", false,-1);
    tracep->declBit(c+2221,"cc_write_hold", false,-1);
    tracep->declBit(c+1736,"r_clear_icache", false,-1);
    tracep->declBit(c+67,"pfpcset", false,-1);
    tracep->declBus(c+68,"pfpcsrc", false,-1, 2,0);
    tracep->declBit(c+5077,"w_clken", false,-1);
    tracep->declBus(c+2222,"dcd_full_R", false,-1, 6,0);
    tracep->declBus(c+2223,"dcd_full_A", false,-1, 6,0);
    tracep->declBus(c+2224,"dcd_full_B", false,-1, 6,0);
    tracep->declBus(c+69,"avsrc", false,-1, 2,0);
    tracep->declBus(c+70,"bvsrc", false,-1, 2,0);
    tracep->declBus(c+2225,"bisrc", false,-1, 1,0);
    tracep->declBit(c+71,"cpu_sim", false,-1);
    tracep->declBus(c+5113,"OPT_SIM_DEBUG", false,-1, 0,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("ALU_SIM ");
    tracep->declBit(c+2226,"r_alu_sim", false,-1);
    tracep->declBus(c+2227,"r_alu_sim_immv", false,-1, 22,0);
    tracep->declBus(c+2228,"regid", false,-1, 4,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("BUSLOCK ");
    tracep->declBit(c+2150,"r_prelock_stall", false,-1);
    tracep->declBus(c+2229,"r_bus_lock", false,-1, 1,0);
    tracep->declBus(c+1752,"r_lock_pc", false,-1, 27,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("CLEAR_DCACHE ");
    tracep->declBit(c+1748,"r_clear_dcache", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("DIVERR ");
    tracep->declBit(c+2110,"r_idiv_err_flag", false,-1);
    tracep->pushNamePrefix("USER_DIVERR ");
    tracep->declBit(c+2111,"r_udiv_err_flag", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("DIVIDE ");
    tracep->pushNamePrefix("thedivide ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBus(c+5154,"LGBW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+2230,"i_reset", false,-1);
    tracep->declBit(c+65,"i_wr", false,-1);
    tracep->declBit(c+2231,"i_signed", false,-1);
    tracep->declBus(c+1753,"i_numerator", false,-1, 31,0);
    tracep->declBus(c+1751,"i_denominator", false,-1, 31,0);
    tracep->declBit(c+2196,"o_busy", false,-1);
    tracep->declBit(c+2197,"o_valid", false,-1);
    tracep->declBit(c+2195,"o_err", false,-1);
    tracep->declBus(c+2198,"o_quotient", false,-1, 31,0);
    tracep->declBus(c+2199,"o_flags", false,-1, 3,0);
    tracep->declBit(c+2232,"r_busy", false,-1);
    tracep->declBus(c+2233,"r_divisor", false,-1, 31,0);
    tracep->declQuad(c+2234,"r_dividend", false,-1, 62,0);
    tracep->declQuad(c+2236,"diff", false,-1, 32,0);
    tracep->declBit(c+2238,"r_sign", false,-1);
    tracep->declBit(c+2239,"pre_sign", false,-1);
    tracep->declBit(c+2240,"r_z", false,-1);
    tracep->declBit(c+2241,"r_c", false,-1);
    tracep->declBit(c+2242,"last_bit", false,-1);
    tracep->declBus(c+2243,"r_bit", false,-1, 4,0);
    tracep->declBit(c+2244,"zero_divisor", false,-1);
    tracep->declBit(c+2245,"w_n", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("FWD_OPERATION ");
    tracep->declBus(c+2158,"r_op_opn", false,-1, 3,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_ALU_PC ");
    tracep->declBus(c+2181,"r_alu_pc", false,-1, 27,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_ALU_PHASE ");
    tracep->declBit(c+2186,"r_alu_phase", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_ALU_STALL ");
    tracep->declBit(c+5074,"unused_alu_stall", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_DISTRIBUTED_REGS ");
    tracep->declBit(c+5074,"unused_prereg_addrs", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_IHALT_PHASE ");
    tracep->declBit(c+2112,"r_ihalt_phase", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_OPLOCK ");
    tracep->declBit(c+2180,"r_op_lock", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_OP_PIPE ");
    tracep->declBit(c+2176,"r_op_pipe", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_OP_STALL ");
    tracep->declBit(c+2152,"r_cc_invalid_for_dcd", false,-1);
    tracep->declBit(c+2153,"r_pending_sreg_write", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_OP_WR ");
    tracep->declBit(c+2170,"r_op_wR", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_PENDING_BREAK ");
    tracep->declBit(c+2099,"r_break_pending", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_PENDING_INTERRUPT ");
    tracep->declBit(c+2246,"r_pending_interrupt", false,-1);
    tracep->declBit(c+2104,"r_user_stepped", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_PROFILER ");
    tracep->declBit(c+2247,"prof_stb", false,-1);
    tracep->declBus(c+2248,"prof_addr", false,-1, 27,0);
    tracep->declBus(c+2249,"prof_ticks", false,-1, 31,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_UHALT_PHASE ");
    tracep->declBit(c+2113,"r_uhalt_phase", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_CIS_OP_PHASE ");
    tracep->declBit(c+2175,"r_op_phase", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OP_REG_ADVANEC ");
    tracep->declBus(c+1754,"r_op_R", false,-1, 4,0);
    tracep->declBus(c+2160,"r_op_Aid", false,-1, 4,0);
    tracep->declBus(c+2161,"r_op_Bid", false,-1, 4,0);
    tracep->declBit(c+2162,"r_op_rA", false,-1);
    tracep->declBit(c+2163,"r_op_rB", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OP_SIM ");
    tracep->declBit(c+2250,"r_op_sim", false,-1);
    tracep->declBus(c+2251,"r_op_sim_immv", false,-1, 22,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SETDBG ");
    tracep->declBus(c+2252,"pre_dbg_reg", false,-1, 31,0);
    tracep->declBus(c+1060,"r_dbg_reg", false,-1, 31,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_ALU_ILLEGAL ");
    tracep->declBit(c+2194,"r_alu_illegal", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_GIE ");
    tracep->declBit(c+2101,"r_gie", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_OP_PC ");
    tracep->declBus(c+2166,"r_op_pc", false,-1, 27,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_TRAP_N_UBREAK ");
    tracep->declBit(c+2100,"r_trap", false,-1);
    tracep->declBit(c+2102,"r_ubreak", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_USER_BUSERR ");
    tracep->declBit(c+2109,"r_ubus_err_flag", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_USER_ILLEGAL_INSN ");
    tracep->declBit(c+2106,"r_ill_err_u", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SET_USER_PC ");
    tracep->declBus(c+2219,"r_upc", false,-1, 27,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("UNUSED_AW ");
    tracep->declBit(c+5074,"generic_ignore", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("doalu ");
    tracep->declBus(c+5062,"OPT_MPY", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_SHIFTS", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+2230,"i_reset", false,-1);
    tracep->declBit(c+5026,"i_stb", false,-1);
    tracep->declBus(c+2158,"i_op", false,-1, 3,0);
    tracep->declBus(c+1753,"i_a", false,-1, 31,0);
    tracep->declBus(c+1751,"i_b", false,-1, 31,0);
    tracep->declBus(c+2187,"o_c", false,-1, 31,0);
    tracep->declBus(c+2188,"o_f", false,-1, 3,0);
    tracep->declBit(c+2189,"o_valid", false,-1);
    tracep->declBit(c+2190,"o_busy", false,-1);
    tracep->declBus(c+2253,"w_brev_result", false,-1, 31,0);
    tracep->declBit(c+2254,"z", false,-1);
    tracep->declBit(c+2255,"n", false,-1);
    tracep->declBit(c+2256,"v", false,-1);
    tracep->declBit(c+2257,"vx", false,-1);
    tracep->declBit(c+2258,"c", false,-1);
    tracep->declBit(c+2259,"pre_sign", false,-1);
    tracep->declBit(c+2260,"set_ovfl", false,-1);
    tracep->declBit(c+2261,"keep_sgn_on_ovfl", false,-1);
    tracep->declQuad(c+2262,"w_lsr_result", false,-1, 32,0);
    tracep->declQuad(c+2264,"w_asr_result", false,-1, 32,0);
    tracep->declQuad(c+2266,"w_lsl_result", false,-1, 32,0);
    tracep->declQuad(c+2268,"mpy_result", false,-1, 63,0);
    tracep->declBit(c+2270,"mpyhi", false,-1);
    tracep->declBit(c+2271,"mpybusy", false,-1);
    tracep->declBit(c+2272,"mpydone", false,-1);
    tracep->declBit(c+72,"this_is_a_multiply_op", false,-1);
    tracep->declBit(c+2190,"r_busy", false,-1);
    tracep->pushNamePrefix("IMPLEMENT_SHIFTS ");
    tracep->declQuad(c+2273,"w_pre_asr_input", false,-1, 32,0);
    tracep->declQuad(c+2275,"w_pre_asr_shifted", false,-1, 32,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("thempy ");
    tracep->declBus(c+5062,"OPT_MPY", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+2230,"i_reset", false,-1);
    tracep->declBit(c+72,"i_stb", false,-1);
    tracep->declBus(c+2277,"i_op", false,-1, 1,0);
    tracep->declBus(c+1753,"i_a", false,-1, 31,0);
    tracep->declBus(c+1751,"i_b", false,-1, 31,0);
    tracep->declBit(c+2272,"o_valid", false,-1);
    tracep->declBit(c+2271,"o_busy", false,-1);
    tracep->declQuad(c+2268,"o_result", false,-1, 63,0);
    tracep->declBit(c+2270,"o_hi", false,-1);
    tracep->pushNamePrefix("IMPY ");
    tracep->pushNamePrefix("MPN1 ");
    tracep->pushNamePrefix("MPN2 ");
    tracep->pushNamePrefix("MPY3CK ");
    tracep->declQuad(c+2278,"r_smpy_result", false,-1, 63,0);
    tracep->declQuad(c+2280,"r_umpy_result", false,-1, 63,0);
    tracep->declBus(c+2282,"r_mpy_a_input", false,-1, 31,0);
    tracep->declBus(c+2283,"r_mpy_b_input", false,-1, 31,0);
    tracep->declBus(c+2284,"mpypipe", false,-1, 1,0);
    tracep->declBus(c+2285,"r_sgn", false,-1, 1,0);
    tracep->declBit(c+2270,"r_hi", false,-1);
    tracep->declQuad(c+2286,"s_mpy_a_input", false,-1, 63,0);
    tracep->declQuad(c+2288,"s_mpy_b_input", false,-1, 63,0);
    tracep->declQuad(c+2290,"u_mpy_a_input", false,-1, 63,0);
    tracep->declQuad(c+2292,"u_mpy_b_input", false,-1, 63,0);
    tracep->popNamePrefix(6);
    tracep->pushNamePrefix("instruction_decoder ");
    tracep->declBus(c+5131,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_MPY", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_SHIFTS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_EARLY_BRANCHING", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_PIPELINED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DIVIDE", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_FPU", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CIS", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOCK", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_OPIPE", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_SIM", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_SUPPRESS_NULL_BRANCHES", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_USERMODE", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5131,"AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+2294,"i_reset", false,-1);
    tracep->declBit(c+55,"i_ce", false,-1);
    tracep->declBit(c+54,"i_stalled", false,-1);
    tracep->declBus(c+1738,"i_instruction", false,-1, 31,0);
    tracep->declBit(c+2101,"i_gie", false,-1);
    tracep->declBus(c+1739,"i_pc", false,-1, 27,0);
    tracep->declBit(c+1740,"i_pf_valid", false,-1);
    tracep->declBit(c+1741,"i_illegal", false,-1);
    tracep->declBit(c+2143,"o_valid", false,-1);
    tracep->declBit(c+2118,"o_phase", false,-1);
    tracep->declBit(c+2146,"o_illegal", false,-1);
    tracep->declBus(c+5017,"o_pc", false,-1, 27,0);
    tracep->declBus(c+2222,"o_dcdR", false,-1, 6,0);
    tracep->declBus(c+2223,"o_dcdA", false,-1, 6,0);
    tracep->declBus(c+2224,"o_dcdB", false,-1, 6,0);
    tracep->declBus(c+2122,"o_preA", false,-1, 4,0);
    tracep->declBus(c+2123,"o_preB", false,-1, 4,0);
    tracep->declBus(c+2144,"o_I", false,-1, 31,0);
    tracep->declBit(c+2145,"o_zI", false,-1);
    tracep->declBus(c+2130,"o_cond", false,-1, 3,0);
    tracep->declBit(c+2138,"o_wF", false,-1);
    tracep->declBus(c+2117,"o_op", false,-1, 3,0);
    tracep->declBit(c+2134,"o_ALU", false,-1);
    tracep->declBit(c+2135,"o_M", false,-1);
    tracep->declBit(c+2136,"o_DV", false,-1);
    tracep->declBit(c+2137,"o_FP", false,-1);
    tracep->declBit(c+2139,"o_break", false,-1);
    tracep->declBit(c+2140,"o_lock", false,-1);
    tracep->declBit(c+2131,"o_wR", false,-1);
    tracep->declBit(c+2132,"o_rA", false,-1);
    tracep->declBit(c+2133,"o_rB", false,-1);
    tracep->declBit(c+2147,"o_early_branch", false,-1);
    tracep->declBit(c+2148,"o_early_branch_stb", false,-1);
    tracep->declBus(c+2149,"o_branch_pc", false,-1, 27,0);
    tracep->declBit(c+2142,"o_ljmp", false,-1);
    tracep->declBit(c+2141,"o_pipe", false,-1);
    tracep->declBit(c+5019,"o_sim", false,-1);
    tracep->declBus(c+5020,"o_sim_immv", false,-1, 22,0);
    tracep->declBus(c+5206,"CPU_SP_REG", false,-1, 3,0);
    tracep->declBus(c+5243,"CPU_CC_REG", false,-1, 3,0);
    tracep->declBus(c+5108,"CPU_PC_REG", false,-1, 3,0);
    tracep->declBus(c+5184,"CISBIT", false,-1, 31,0);
    tracep->declBus(c+5133,"CISIMMSEL", false,-1, 31,0);
    tracep->declBus(c+5134,"IMMSEL", false,-1, 31,0);
    tracep->declBus(c+2295,"w_op", false,-1, 4,0);
    tracep->declBit(c+2296,"w_ldi", false,-1);
    tracep->declBit(c+2297,"w_mov", false,-1);
    tracep->declBit(c+2298,"w_cmptst", false,-1);
    tracep->declBit(c+2299,"w_ldilo", false,-1);
    tracep->declBit(c+2300,"w_ALU", false,-1);
    tracep->declBit(c+2301,"w_brev", false,-1);
    tracep->declBit(c+2302,"w_noop", false,-1);
    tracep->declBit(c+2303,"w_lock", false,-1);
    tracep->declBit(c+2304,"w_sim", false,-1);
    tracep->declBit(c+2305,"w_break", false,-1);
    tracep->declBit(c+2306,"w_special", false,-1);
    tracep->declBit(c+2307,"w_add", false,-1);
    tracep->declBit(c+2308,"w_mpy", false,-1);
    tracep->declBus(c+2122,"w_dcdR", false,-1, 4,0);
    tracep->declBus(c+2123,"w_dcdB", false,-1, 4,0);
    tracep->declBus(c+2122,"w_dcdA", false,-1, 4,0);
    tracep->declBit(c+2309,"w_dcdR_pc", false,-1);
    tracep->declBit(c+2310,"w_dcdR_cc", false,-1);
    tracep->declBit(c+2309,"w_dcdA_pc", false,-1);
    tracep->declBit(c+2310,"w_dcdA_cc", false,-1);
    tracep->declBit(c+2311,"w_dcdB_pc", false,-1);
    tracep->declBit(c+2312,"w_dcdB_cc", false,-1);
    tracep->declBus(c+2313,"w_cond", false,-1, 3,0);
    tracep->declBit(c+2314,"w_wF", false,-1);
    tracep->declBit(c+2315,"w_mem", false,-1);
    tracep->declBit(c+2316,"w_sto", false,-1);
    tracep->declBit(c+2317,"w_div", false,-1);
    tracep->declBit(c+2318,"w_fpu", false,-1);
    tracep->declBit(c+2319,"w_wR", false,-1);
    tracep->declBit(c+2320,"w_rA", false,-1);
    tracep->declBit(c+2321,"w_rB", false,-1);
    tracep->declBit(c+2322,"w_wR_n", false,-1);
    tracep->declBit(c+2323,"w_ljmp", false,-1);
    tracep->declBit(c+2142,"w_ljmp_dly", false,-1);
    tracep->declBit(c+2324,"w_cis_ljmp", false,-1);
    tracep->declBus(c+2325,"iword", false,-1, 31,0);
    tracep->declBit(c+2326,"pf_valid", false,-1);
    tracep->declBus(c+2327,"r_nxt_half", false,-1, 14,0);
    tracep->declBus(c+2328,"w_cis_op", false,-1, 4,0);
    tracep->declBus(c+2329,"r_I", false,-1, 22,0);
    tracep->declBus(c+2330,"w_fullI", false,-1, 22,0);
    tracep->declBus(c+2331,"w_I", false,-1, 22,0);
    tracep->declBit(c+2332,"w_Iz", false,-1);
    tracep->declBus(c+2333,"w_immsrc", false,-1, 1,0);
    tracep->declBit(c+2143,"r_valid", false,-1);
    tracep->declBit(c+2334,"insn_is_pipeable", false,-1);
    tracep->declBit(c+5074,"illegal_shift", false,-1);
    tracep->declBit(c+5074,"possibly_unused", false,-1);
    tracep->pushNamePrefix("GEN_CIS_IMMEDIATE ");
    tracep->declBus(c+2335,"w_halfI", false,-1, 7,0);
    tracep->declBus(c+2336,"w_halfbits", false,-1, 7,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_CIS_PHASE ");
    tracep->declBit(c+2118,"r_phase", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_EARLY_BRANCH_LOGIC ");
    tracep->declBit(c+2147,"r_early_branch", false,-1);
    tracep->declBit(c+2148,"r_early_branch_stb", false,-1);
    tracep->declBit(c+2142,"r_ljmp", false,-1);
    tracep->declBus(c+2149,"r_branch_pc", false,-1, 27,0);
    tracep->declBit(c+2337,"w_add_to_pc", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_OPIPE ");
    tracep->declBit(c+2141,"r_pipe", false,-1);
    tracep->declBit(c+2334,"r_insn_is_pipeable", false,-1);
    tracep->popNamePrefix(4);
    tracep->pushNamePrefix("u_jiffies ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1093,"i_ce", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+2338,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1012,"o_wb_ack", false,-1);
    tracep->declBus(c+1016,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+904,"o_int", false,-1);
    tracep->declBus(c+1016,"r_counter", false,-1, 31,0);
    tracep->declBit(c+2339,"int_set", false,-1);
    tracep->declBit(c+2340,"new_set", false,-1);
    tracep->declBit(c+2341,"int_now", false,-1);
    tracep->declBus(c+2342,"int_when", false,-1, 31,0);
    tracep->declBus(c+2343,"new_when", false,-1, 31,0);
    tracep->declBus(c+2344,"till_wb", false,-1, 31,0);
    tracep->declBus(c+2345,"till_when", false,-1, 31,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_timer_a ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBus(c+5184,"VW", false,-1, 31,0);
    tracep->declBus(c+5070,"RELOADABLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1093,"i_ce", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+2346,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1009,"o_wb_ack", false,-1);
    tracep->declBus(c+1013,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+901,"o_int", false,-1);
    tracep->declBit(c+2347,"r_running", false,-1);
    tracep->declBit(c+2348,"r_zero", false,-1);
    tracep->declBus(c+2349,"r_value", false,-1, 30,0);
    tracep->declBit(c+2350,"wb_write", false,-1);
    tracep->declBit(c+2351,"auto_reload", false,-1);
    tracep->declBus(c+2352,"interval_count", false,-1, 30,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_RELOAD ");
    tracep->declBit(c+2351,"r_auto_reload", false,-1);
    tracep->declBus(c+2352,"r_interval_count", false,-1, 30,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_timer_b ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBus(c+5184,"VW", false,-1, 31,0);
    tracep->declBus(c+5070,"RELOADABLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1093,"i_ce", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+2353,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1010,"o_wb_ack", false,-1);
    tracep->declBus(c+1014,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+902,"o_int", false,-1);
    tracep->declBit(c+2354,"r_running", false,-1);
    tracep->declBit(c+2355,"r_zero", false,-1);
    tracep->declBus(c+2356,"r_value", false,-1, 30,0);
    tracep->declBit(c+2357,"wb_write", false,-1);
    tracep->declBit(c+2358,"auto_reload", false,-1);
    tracep->declBus(c+2359,"interval_count", false,-1, 30,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_RELOAD ");
    tracep->declBit(c+2358,"r_auto_reload", false,-1);
    tracep->declBus(c+2359,"r_interval_count", false,-1, 30,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_timer_c ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBus(c+5184,"VW", false,-1, 31,0);
    tracep->declBus(c+5070,"RELOADABLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1093,"i_ce", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+2360,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+1011,"o_wb_ack", false,-1);
    tracep->declBus(c+1015,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+903,"o_int", false,-1);
    tracep->declBit(c+2361,"r_running", false,-1);
    tracep->declBit(c+2362,"r_zero", false,-1);
    tracep->declBus(c+2363,"r_value", false,-1, 30,0);
    tracep->declBit(c+2364,"wb_write", false,-1);
    tracep->declBit(c+2365,"auto_reload", false,-1);
    tracep->declBus(c+2366,"interval_count", false,-1, 30,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_RELOAD ");
    tracep->declBit(c+2365,"r_auto_reload", false,-1);
    tracep->declBus(c+2366,"r_interval_count", false,-1, 30,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_watchbus ");
    tracep->declBus(c+5060,"BW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+2367,"i_reset", false,-1);
    tracep->declBus(c+5245,"i_timeout", false,-1, 13,0);
    tracep->declBit(c+974,"o_int", false,-1);
    tracep->declBus(c+2368,"r_value", false,-1, 13,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_watchdog ");
    tracep->declBus(c+5114,"BW", false,-1, 31,0);
    tracep->declBus(c+5184,"VW", false,-1, 31,0);
    tracep->declBus(c+5113,"RELOADABLE", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+953,"i_reset", false,-1);
    tracep->declBit(c+1093,"i_ce", false,-1);
    tracep->declBit(c+917,"i_wb_cyc", false,-1);
    tracep->declBit(c+2369,"i_wb_stb", false,-1);
    tracep->declBit(c+919,"i_wb_we", false,-1);
    tracep->declBus(c+921,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+5108,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+966,"o_wb_ack", false,-1);
    tracep->declBus(c+968,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+967,"o_int", false,-1);
    tracep->declBit(c+2370,"r_running", false,-1);
    tracep->declBit(c+2371,"r_zero", false,-1);
    tracep->declBus(c+2372,"r_value", false,-1, 30,0);
    tracep->declBit(c+2373,"wb_write", false,-1);
    tracep->declBit(c+5074,"auto_reload", false,-1);
    tracep->declBus(c+5246,"interval_count", false,-1, 30,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("txv ");
    tracep->declBus(c+5247,"TIMING_BITS", false,-1, 4,0);
    tracep->declBus(c+5247,"TB", false,-1, 4,0);
    tracep->declBus(c+5213,"CLOCKS_PER_BAUD", false,-1, 6,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+193,"i_wr", false,-1);
    tracep->declBus(c+191,"i_data", false,-1, 7,0);
    tracep->declBit(c+5001,"o_uart_tx", false,-1);
    tracep->declBit(c+194,"o_busy", false,-1);
    tracep->declBus(c+5122,"TXUL_BIT_ZERO", false,-1, 3,0);
    tracep->declBus(c+5129,"TXUL_STOP", false,-1, 3,0);
    tracep->declBus(c+5108,"TXUL_IDLE", false,-1, 3,0);
    tracep->declBus(c+2374,"baud_counter", false,-1, 6,0);
    tracep->declBus(c+2375,"state", false,-1, 3,0);
    tracep->declBus(c+2376,"lcl_data", false,-1, 7,0);
    tracep->declBit(c+194,"r_busy", false,-1);
    tracep->declBit(c+2377,"zero_baud_counter", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_emmc ");
    tracep->declBus(c+5158,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5063,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_CARD_DETECT", false,-1, 0,0);
    tracep->declBus(c+5133,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+5074,"i_hsclk", false,-1);
    tracep->declBit(c+4533,"i_wb_cyc", false,-1);
    tracep->declBit(c+4534,"i_wb_stb", false,-1);
    tracep->declBit(c+4535,"i_wb_we", false,-1);
    tracep->declBus(c+4592,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4537,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4538,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+401,"o_wb_ack", false,-1);
    tracep->declBus(c+402,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+4966,"o_ck", false,-1);
    tracep->declBit(c+4967,"i_ds", false,-1);
    tracep->declBit(c+4968,"io_cmd_tristate", false,-1);
    tracep->declBit(c+4969,"o_cmd", false,-1);
    tracep->declBit(c+4970,"i_cmd", false,-1);
    tracep->declBus(c+4971,"io_dat_tristate", false,-1, 7,0);
    tracep->declBus(c+4972,"o_dat", false,-1, 7,0);
    tracep->declBus(c+4973,"i_dat", false,-1, 7,0);
    tracep->declBit(c+4974,"i_card_detect", false,-1);
    tracep->declBit(c+5074,"o_1p8v", false,-1);
    tracep->declBit(c+160,"o_int", false,-1);
    tracep->declBus(c+36,"o_debug", false,-1, 31,0);
    tracep->declBit(c+2378,"cfg_ddr", false,-1);
    tracep->declBus(c+2379,"cfg_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2380,"sdclk", false,-1, 7,0);
    tracep->declBit(c+2381,"cmd_en", false,-1);
    tracep->declBit(c+2382,"pp_cmd", false,-1);
    tracep->declBus(c+2383,"cmd_data", false,-1, 1,0);
    tracep->declBit(c+2384,"data_en", false,-1);
    tracep->declBit(c+2385,"pp_data", false,-1);
    tracep->declBit(c+2386,"rx_en", false,-1);
    tracep->declBus(c+2387,"tx_data", false,-1, 31,0);
    tracep->declBit(c+2388,"afifo_reset_n", false,-1);
    tracep->declBus(c+2389,"rply_strb", false,-1, 1,0);
    tracep->declBus(c+2390,"rply_data", false,-1, 1,0);
    tracep->declBit(c+2391,"card_busy", false,-1);
    tracep->declBus(c+2392,"rx_strb", false,-1, 1,0);
    tracep->declBus(c+2393,"rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"AC_VALID", false,-1);
    tracep->declBus(c+5116,"AC_DATA", false,-1, 1,0);
    tracep->declBit(c+5074,"AD_VALID", false,-1);
    tracep->declBus(c+5076,"AD_DATA", false,-1, 31,0);
    tracep->pushNamePrefix("u_sdfrontend ");
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5063,"NUMIO", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_hsclk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+2378,"i_cfg_ddr", false,-1);
    tracep->declBus(c+2379,"i_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2380,"i_sdclk", false,-1, 7,0);
    tracep->declBit(c+2381,"i_cmd_en", false,-1);
    tracep->declBit(c+2382,"i_pp_cmd", false,-1);
    tracep->declBus(c+2383,"i_cmd_data", false,-1, 1,0);
    tracep->declBit(c+2384,"i_data_en", false,-1);
    tracep->declBit(c+2386,"i_rx_en", false,-1);
    tracep->declBit(c+2385,"i_pp_data", false,-1);
    tracep->declBus(c+2387,"i_tx_data", false,-1, 31,0);
    tracep->declBit(c+2388,"i_afifo_reset_n", false,-1);
    tracep->declBit(c+2391,"o_data_busy", false,-1);
    tracep->declBus(c+2389,"o_cmd_strb", false,-1, 1,0);
    tracep->declBus(c+2390,"o_cmd_data", false,-1, 1,0);
    tracep->declBus(c+2392,"o_rx_strb", false,-1, 1,0);
    tracep->declBus(c+2393,"o_rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"MAC_VALID", false,-1);
    tracep->declBus(c+5116,"MAC_DATA", false,-1, 1,0);
    tracep->declBit(c+5074,"MAD_VALID", false,-1);
    tracep->declBus(c+5076,"MAD_DATA", false,-1, 31,0);
    tracep->declBit(c+4966,"o_ck", false,-1);
    tracep->declBit(c+4967,"i_ds", false,-1);
    tracep->declBit(c+4968,"io_cmd_tristate", false,-1);
    tracep->declBit(c+4969,"o_cmd", false,-1);
    tracep->declBit(c+4970,"i_cmd", false,-1);
    tracep->declBus(c+4971,"io_dat_tristate", false,-1, 7,0);
    tracep->declBus(c+4972,"o_dat", false,-1, 7,0);
    tracep->declBus(c+4973,"i_dat", false,-1, 7,0);
    tracep->declBus(c+36,"o_debug", false,-1, 31,0);
    tracep->declBit(c+2391,"dat0_busy", false,-1);
    tracep->declBit(c+2394,"wait_for_busy", false,-1);
    tracep->pushNamePrefix("GEN_NO_SERDES ");
    tracep->declBit(c+2395,"next_pedge", false,-1);
    tracep->declBit(c+2396,"next_dedge", false,-1);
    tracep->declBit(c+2397,"resp_started", false,-1);
    tracep->declBit(c+2398,"io_started", false,-1);
    tracep->declBit(c+2399,"last_ck", false,-1);
    tracep->declBit(c+2400,"r_cmd_data", false,-1);
    tracep->declBit(c+2401,"r_cmd_strb", false,-1);
    tracep->declBit(c+2402,"r_rx_strb", false,-1);
    tracep->declBus(c+2403,"r_rx_data", false,-1, 7,0);
    tracep->declBus(c+2404,"ck_sreg", false,-1, 1,0);
    tracep->declBus(c+2405,"pck_sreg", false,-1, 1,0);
    tracep->declBit(c+2406,"sample_ck", false,-1);
    tracep->declBit(c+2407,"cmd_sample_ck", false,-1);
    tracep->declBus(c+4973,"w_out", false,-1, 7,0);
    tracep->declBit(c+5074,"unused_no_serdes", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_sdio ");
    tracep->declBus(c+5158,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5063,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_CARD_DETECT", false,-1, 0,0);
    tracep->declBus(c+5133,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4533,"i_wb_cyc", false,-1);
    tracep->declBit(c+4534,"i_wb_stb", false,-1);
    tracep->declBit(c+4535,"i_wb_we", false,-1);
    tracep->declBus(c+4592,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4537,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4538,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+401,"o_wb_ack", false,-1);
    tracep->declBus(c+402,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+4974,"i_card_detect", false,-1);
    tracep->declBit(c+5074,"o_1p8v", false,-1);
    tracep->declBit(c+160,"o_int", false,-1);
    tracep->declBit(c+2378,"o_cfg_ddr", false,-1);
    tracep->declBus(c+2379,"o_cfg_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2380,"o_sdclk", false,-1, 7,0);
    tracep->declBit(c+2381,"o_cmd_en", false,-1);
    tracep->declBit(c+2382,"o_pp_cmd", false,-1);
    tracep->declBus(c+2383,"o_cmd_data", false,-1, 1,0);
    tracep->declBit(c+2384,"o_data_en", false,-1);
    tracep->declBit(c+2385,"o_pp_data", false,-1);
    tracep->declBit(c+2386,"o_rx_en", false,-1);
    tracep->declBus(c+2387,"o_tx_data", false,-1, 31,0);
    tracep->declBit(c+2388,"o_afifo_reset_n", false,-1);
    tracep->declBus(c+2389,"i_cmd_strb", false,-1, 1,0);
    tracep->declBus(c+2390,"i_cmd_data", false,-1, 1,0);
    tracep->declBit(c+2391,"i_card_busy", false,-1);
    tracep->declBus(c+2392,"i_rx_strb", false,-1, 1,0);
    tracep->declBus(c+2393,"i_rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"S_AC_VALID", false,-1);
    tracep->declBus(c+5116,"S_AC_DATA", false,-1, 1,0);
    tracep->declBit(c+5074,"S_AD_VALID", false,-1);
    tracep->declBus(c+5076,"S_AD_DATA", false,-1, 31,0);
    tracep->declBit(c+2408,"soft_reset", false,-1);
    tracep->declBit(c+2409,"cfg_clk90", false,-1);
    tracep->declBit(c+2410,"cfg_clk_shutdown", false,-1);
    tracep->declBit(c+2411,"cfg_ds", false,-1);
    tracep->declBus(c+2412,"cfg_ckspeed", false,-1, 7,0);
    tracep->declBus(c+2413,"cfg_width", false,-1, 1,0);
    tracep->declBit(c+2414,"clk_stb", false,-1);
    tracep->declBit(c+2415,"clk_half", false,-1);
    tracep->declBus(c+2416,"w_sdclk", false,-1, 7,0);
    tracep->declBus(c+2417,"clk_ckspd", false,-1, 7,0);
    tracep->declBit(c+2418,"cmd_request", false,-1);
    tracep->declBit(c+2419,"cmd_err", false,-1);
    tracep->declBit(c+2420,"cmd_busy", false,-1);
    tracep->declBit(c+2421,"cmd_done", false,-1);
    tracep->declBus(c+2422,"cmd_type", false,-1, 1,0);
    tracep->declBus(c+2423,"cmd_ercode", false,-1, 1,0);
    tracep->declBit(c+2424,"rsp_stb", false,-1);
    tracep->declBus(c+2425,"cmd_id", false,-1, 6,0);
    tracep->declBus(c+2426,"rsp_id", false,-1, 5,0);
    tracep->declBus(c+2427,"cmd_arg", false,-1, 31,0);
    tracep->declBus(c+2428,"rsp_arg", false,-1, 31,0);
    tracep->declBit(c+2429,"cmd_mem_valid", false,-1);
    tracep->declBus(c+5108,"cmd_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2430,"cmd_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2431,"cmd_mem_data", false,-1, 31,0);
    tracep->declBit(c+2432,"tx_en", false,-1);
    tracep->declBit(c+2433,"tx_mem_valid", false,-1);
    tracep->declBit(c+2434,"tx_mem_ready", false,-1);
    tracep->declBit(c+2435,"tx_mem_last", false,-1);
    tracep->declBus(c+2436,"tx_mem_data", false,-1, 31,0);
    tracep->declBit(c+5077,"crc_en", false,-1);
    tracep->declBus(c+2437,"rx_length", false,-1, 12,0);
    tracep->declBit(c+2438,"rx_mem_valid", false,-1);
    tracep->declBus(c+2439,"rx_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2440,"rx_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2441,"rx_mem_data", false,-1, 31,0);
    tracep->declBit(c+2442,"rx_done", false,-1);
    tracep->declBit(c+2443,"rx_err", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("u_clkgen ");
    tracep->declBus(c+5063,"LGMAXDIV", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+2409,"i_cfg_clk90", false,-1);
    tracep->declBus(c+2412,"i_cfg_ckspd", false,-1, 7,0);
    tracep->declBit(c+2410,"i_cfg_shutdown", false,-1);
    tracep->declBit(c+2414,"o_ckstb", false,-1);
    tracep->declBit(c+2415,"o_hlfck", false,-1);
    tracep->declBus(c+2416,"o_ckwide", false,-1, 7,0);
    tracep->declBus(c+2417,"o_ckspd", false,-1, 7,0);
    tracep->declBus(c+5061,"NCTR", false,-1, 31,0);
    tracep->declBit(c+2444,"nxt_stb", false,-1);
    tracep->declBit(c+2445,"nxt_clk", false,-1);
    tracep->declBus(c+2446,"nxt_counter", false,-1, 9,0);
    tracep->declBus(c+2447,"counter", false,-1, 9,0);
    tracep->declBit(c+2448,"clk90", false,-1);
    tracep->declBus(c+2449,"ckspd", false,-1, 7,0);
    tracep->declBit(c+2450,"w_clk90", false,-1);
    tracep->declBus(c+2451,"w_ckspd", false,-1, 7,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_control ");
    tracep->declBus(c+5158,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5063,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_CARD_DETECT", false,-1, 0,0);
    tracep->declBus(c+5061,"LGFIFOW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_DMA", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_1P8V", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4533,"i_wb_cyc", false,-1);
    tracep->declBit(c+4534,"i_wb_stb", false,-1);
    tracep->declBit(c+4535,"i_wb_we", false,-1);
    tracep->declBus(c+4592,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4537,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4538,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+401,"o_wb_ack", false,-1);
    tracep->declBus(c+402,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+2409,"o_cfg_clk90", false,-1);
    tracep->declBus(c+2412,"o_cfg_ckspeed", false,-1, 7,0);
    tracep->declBit(c+2410,"o_cfg_shutdown", false,-1);
    tracep->declBus(c+2413,"o_cfg_width", false,-1, 1,0);
    tracep->declBit(c+2411,"o_cfg_ds", false,-1);
    tracep->declBit(c+2378,"o_cfg_ddr", false,-1);
    tracep->declBit(c+2382,"o_pp_cmd", false,-1);
    tracep->declBit(c+2385,"o_pp_data", false,-1);
    tracep->declBus(c+2379,"o_cfg_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2417,"i_ckspd", false,-1, 7,0);
    tracep->declBit(c+2408,"o_soft_reset", false,-1);
    tracep->declBit(c+2418,"o_cmd_request", false,-1);
    tracep->declBus(c+2422,"o_cmd_type", false,-1, 1,0);
    tracep->declBus(c+2425,"o_cmd_id", false,-1, 6,0);
    tracep->declBus(c+2427,"o_arg", false,-1, 31,0);
    tracep->declBit(c+2420,"i_cmd_busy", false,-1);
    tracep->declBit(c+2421,"i_cmd_done", false,-1);
    tracep->declBit(c+2419,"i_cmd_err", false,-1);
    tracep->declBus(c+2423,"i_cmd_ercode", false,-1, 1,0);
    tracep->declBit(c+2424,"i_cmd_response", false,-1);
    tracep->declBus(c+2426,"i_resp", false,-1, 5,0);
    tracep->declBus(c+2428,"i_arg", false,-1, 31,0);
    tracep->declBit(c+2429,"i_cmd_mem_valid", false,-1);
    tracep->declBus(c+5108,"i_cmd_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2430,"i_cmd_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2431,"i_cmd_mem_data", false,-1, 31,0);
    tracep->declBit(c+2432,"o_tx_en", false,-1);
    tracep->declBit(c+2433,"o_tx_mem_valid", false,-1);
    tracep->declBit(c+2452,"i_tx_mem_ready", false,-1);
    tracep->declBus(c+2436,"o_tx_mem_data", false,-1, 31,0);
    tracep->declBit(c+2435,"o_tx_mem_last", false,-1);
    tracep->declBit(c+2384,"i_tx_busy", false,-1);
    tracep->declBit(c+2386,"o_rx_en", false,-1);
    tracep->declBit(c+5077,"o_crc_en", false,-1);
    tracep->declBus(c+2437,"o_length", false,-1, 12,0);
    tracep->declBit(c+2438,"i_rx_mem_valid", false,-1);
    tracep->declBus(c+2440,"i_rx_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2439,"i_rx_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2441,"i_rx_mem_data", false,-1, 31,0);
    tracep->declBit(c+2442,"i_rx_done", false,-1);
    tracep->declBit(c+2443,"i_rx_err", false,-1);
    tracep->declBit(c+4974,"i_card_detect", false,-1);
    tracep->declBit(c+2391,"i_card_busy", false,-1);
    tracep->declBit(c+5074,"o_1p8v", false,-1);
    tracep->declBit(c+160,"o_int", false,-1);
    tracep->declBus(c+5061,"LGFIFO32", false,-1, 31,0);
    tracep->declBus(c+5159,"ADDR_CMD", false,-1, 2,0);
    tracep->declBus(c+5166,"ADDR_ARG", false,-1, 2,0);
    tracep->declBus(c+5160,"ADDR_FIFOA", false,-1, 2,0);
    tracep->declBus(c+5162,"ADDR_FIFOB", false,-1, 2,0);
    tracep->declBus(c+5207,"ADDR_PHY", false,-1, 2,0);
    tracep->declBus(c+5117,"CMD_PREFIX", false,-1, 1,0);
    tracep->declBus(c+5116,"NUL_PREFIX", false,-1, 1,0);
    tracep->declBus(c+5116,"RNO_REPLY", false,-1, 1,0);
    tracep->declBus(c+5118,"R2_REPLY", false,-1, 1,0);
    tracep->declBus(c+5134,"CARD_REMOVED_BIT", false,-1, 31,0);
    tracep->declBus(c+5136,"USE_DMA_BIT", false,-1, 31,0);
    tracep->declBus(c+5158,"FIFO_ID_BIT", false,-1, 31,0);
    tracep->declBus(c+5157,"USE_FIFO_BIT", false,-1, 31,0);
    tracep->declBus(c+5061,"FIFO_WRITE_BIT", false,-1, 31,0);
    tracep->declBus(c+5116,"WIDTH_1W", false,-1, 1,0);
    tracep->declBus(c+5117,"WIDTH_4W", false,-1, 1,0);
    tracep->declBus(c+5118,"WIDTH_8W", false,-1, 1,0);
    tracep->declBit(c+4593,"wb_cmd_stb", false,-1);
    tracep->declBit(c+4594,"wb_phy_stb", false,-1);
    tracep->declBus(c+2425,"r_cmd", false,-1, 6,0);
    tracep->declBit(c+2453,"r_tx_request", false,-1);
    tracep->declBit(c+2454,"r_rx_request", false,-1);
    tracep->declBit(c+2455,"r_tx_sent", false,-1);
    tracep->declBit(c+2456,"r_fifo", false,-1);
    tracep->declBit(c+2457,"r_cmd_err", false,-1);
    tracep->declBus(c+2458,"r_cmd_ecode", false,-1, 1,0);
    tracep->declBus(c+2427,"r_arg", false,-1, 31,0);
    tracep->declBus(c+2459,"lgblk", false,-1, 3,0);
    tracep->declBus(c+2413,"r_width", false,-1, 1,0);
    tracep->declBus(c+2412,"r_ckspeed", false,-1, 7,0);
    tracep->declBus(c+2460,"w_cmd_word", false,-1, 31,0);
    tracep->declBus(c+2461,"w_phy_ctrl", false,-1, 31,0);
    tracep->declBus(c+2462,"blk_words", false,-1, 15,0);
    tracep->declBus(c+2463,"ika", false,-1, 31,0);
    tracep->declBus(c+2464,"ikb", false,-1, 31,0);
    tracep->declBus(c+5189,"NFIFOW", false,-1, 31,0);
    tracep->declBus(c+2465,"tx_fifo_a", false,-1, 31,0);
    tracep->declBus(c+2466,"tx_fifo_b", false,-1, 31,0);
    tracep->declBus(c+5113,"tx_shift", false,-1, 0,0);
    tracep->declBus(c+2467,"fif_wraddr", false,-1, 9,0);
    tracep->declBus(c+2468,"fif_rdaddr", false,-1, 9,0);
    tracep->declBus(c+2469,"fif_a_rdaddr", false,-1, 9,0);
    tracep->declBus(c+2470,"fif_b_rdaddr", false,-1, 9,0);
    tracep->declBus(c+2471,"tx_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2472,"next_tx_mem", false,-1, 31,0);
    tracep->declBit(c+2473,"tx_fifo_last", false,-1);
    tracep->declBit(c+2474,"pre_tx_last", false,-1);
    tracep->declBit(c+2475,"tx_pipe_valid", false,-1);
    tracep->declBit(c+5077,"card_present", false,-1);
    tracep->declBit(c+5074,"card_removed", false,-1);
    tracep->declBit(c+2476,"pre_ack", false,-1);
    tracep->declBus(c+2477,"pre_sel", false,-1, 1,0);
    tracep->declBus(c+2478,"pre_data", false,-1, 31,0);
    tracep->declBus(c+2479,"mem_wr_addr_a", false,-1, 9,0);
    tracep->declBus(c+2480,"mem_wr_addr_b", false,-1, 9,0);
    tracep->declBus(c+2481,"mem_wr_strb_a", false,-1, 3,0);
    tracep->declBus(c+2482,"mem_wr_strb_b", false,-1, 3,0);
    tracep->declBus(c+2483,"mem_wr_data_a", false,-1, 31,0);
    tracep->declBus(c+2484,"mem_wr_data_b", false,-1, 31,0);
    tracep->declBit(c+2485,"cmd_busy", false,-1);
    tracep->declBit(c+125,"new_cmd_request", false,-1);
    tracep->declBit(c+126,"new_data_request", false,-1);
    tracep->declBit(c+127,"new_tx_request", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("NO_CARD_DETECT_SIGNAL ");
    tracep->declBit(c+5074,"unused_card_detect", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_rxframe ");
    tracep->declBus(c+5158,"LGLEN", false,-1, 31,0);
    tracep->declBus(c+5065,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5061,"LGLENW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_DS", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5133,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+73,"i_reset", false,-1);
    tracep->declBit(c+2411,"i_cfg_ds", false,-1);
    tracep->declBit(c+2378,"i_cfg_ddr", false,-1);
    tracep->declBus(c+2413,"i_cfg_width", false,-1, 1,0);
    tracep->declBit(c+2386,"i_rx_en", false,-1);
    tracep->declBit(c+5077,"i_crc_en", false,-1);
    tracep->declBus(c+2437,"i_length", false,-1, 12,0);
    tracep->declBus(c+2392,"i_rx_strb", false,-1, 1,0);
    tracep->declBus(c+2393,"i_rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"S_ASYNC_VALID", false,-1);
    tracep->declBus(c+5076,"S_ASYNC_DATA", false,-1, 31,0);
    tracep->declBit(c+2438,"o_mem_valid", false,-1);
    tracep->declBus(c+2440,"o_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2439,"o_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2441,"o_mem_data", false,-1, 31,0);
    tracep->declBit(c+2442,"o_done", false,-1);
    tracep->declBit(c+2443,"o_err", false,-1);
    tracep->declBus(c+5116,"WIDTH_1W", false,-1, 1,0);
    tracep->declBus(c+5117,"WIDTH_4W", false,-1, 1,0);
    tracep->declBus(c+5118,"WIDTH_8W", false,-1, 1,0);
    tracep->declBus(c+5069,"NCRC", false,-1, 31,0);
    tracep->declBus(c+5248,"CRC_POLYNOMIAL", false,-1, 15,0);
    tracep->declBus(c+2486,"sync_fill", false,-1, 4,0);
    tracep->declBus(c+2487,"sync_sreg", false,-1, 19,0);
    tracep->declBit(c+2488,"s2_valid", false,-1);
    tracep->declBus(c+2489,"s2_fill", false,-1, 1,0);
    tracep->declBus(c+2490,"s2_data", false,-1, 15,0);
    tracep->declBit(c+2438,"mem_valid", false,-1);
    tracep->declBit(c+2491,"mem_full", false,-1);
    tracep->declBit(c+2492,"rnxt_strb", false,-1);
    tracep->declBus(c+2440,"mem_strb", false,-1, 3,0);
    tracep->declBus(c+2441,"mem_data", false,-1, 31,0);
    tracep->declBus(c+2439,"mem_addr", false,-1, 9,0);
    tracep->declBus(c+2493,"subaddr", false,-1, 1,0);
    tracep->declBus(c+2494,"next_subaddr", false,-1, 1,0);
    tracep->declBus(c+2495,"rnxt_data", false,-1, 7,0);
    tracep->declBit(c+2496,"busy", false,-1);
    tracep->declBit(c+2497,"data_phase", false,-1);
    tracep->declBit(c+2498,"load_crc", false,-1);
    tracep->declBit(c+2499,"pending_crc", false,-1);
    tracep->declBus(c+2500,"rail_count", false,-1, 15,0);
    tracep->declBus(c+2501,"err", false,-1, 7,0);
    tracep->declBus(c+2502,"r_timeout", false,-1, 22,0);
    tracep->declBit(c+2503,"r_watchdog", false,-1);
    tracep->declBit(c+2504,"last_strb", false,-1);
    tracep->declBit(c+2505,"w_done", false,-1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[0] ");
    tracep->declBus(c+2506,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2507,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2508,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[1] ");
    tracep->declBus(c+2509,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2510,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2511,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[2] ");
    tracep->declBus(c+2512,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2513,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2514,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[3] ");
    tracep->declBus(c+2515,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2516,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2517,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_sdcmd ");
    tracep->declBus(c+5113,"OPT_DS", false,-1, 0,0);
    tracep->declBus(c+5131,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBus(c+5061,"LGLEN", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+73,"i_reset", false,-1);
    tracep->declBit(c+2411,"i_cfg_ds", false,-1);
    tracep->declBit(c+2518,"i_cfg_dbl", false,-1);
    tracep->declBit(c+2414,"i_ckstb", false,-1);
    tracep->declBit(c+2418,"i_cmd_request", false,-1);
    tracep->declBus(c+2422,"i_cmd_type", false,-1, 1,0);
    tracep->declBus(c+2425,"i_cmd", false,-1, 6,0);
    tracep->declBus(c+2427,"i_arg", false,-1, 31,0);
    tracep->declBit(c+2420,"o_busy", false,-1);
    tracep->declBit(c+2421,"o_done", false,-1);
    tracep->declBit(c+2419,"o_err", false,-1);
    tracep->declBus(c+2423,"o_ercode", false,-1, 1,0);
    tracep->declBit(c+2381,"o_cmd_en", false,-1);
    tracep->declBus(c+2383,"o_cmd_data", false,-1, 1,0);
    tracep->declBus(c+2389,"i_cmd_strb", false,-1, 1,0);
    tracep->declBus(c+2390,"i_cmd_data", false,-1, 1,0);
    tracep->declBit(c+5074,"S_ASYNC_VALID", false,-1);
    tracep->declBus(c+5116,"S_ASYNC_DATA", false,-1, 1,0);
    tracep->declBit(c+2424,"o_cmd_response", false,-1);
    tracep->declBus(c+2426,"o_resp", false,-1, 5,0);
    tracep->declBus(c+2428,"o_arg", false,-1, 31,0);
    tracep->declBit(c+2429,"o_mem_valid", false,-1);
    tracep->declBus(c+5108,"o_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2430,"o_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2431,"o_mem_data", false,-1, 31,0);
    tracep->declBus(c+5116,"R_NONE", false,-1, 1,0);
    tracep->declBus(c+5117,"R_R1", false,-1, 1,0);
    tracep->declBus(c+5118,"R_R2", false,-1, 1,0);
    tracep->declBus(c+5116,"ECODE_TIMEOUT", false,-1, 1,0);
    tracep->declBus(c+5117,"ECODE_OKAY", false,-1, 1,0);
    tracep->declBus(c+5118,"ECODE_BADCRC", false,-1, 1,0);
    tracep->declBus(c+5119,"ECODE_FRAMEERR", false,-1, 1,0);
    tracep->declBus(c+5249,"CRC_POLYNOMIAL", false,-1, 6,0);
    tracep->declBit(c+2381,"active", false,-1);
    tracep->declBus(c+2519,"srcount", false,-1, 5,0);
    tracep->declQuad(c+2520,"tx_sreg", false,-1, 47,0);
    tracep->declBit(c+2522,"waiting_on_response", false,-1);
    tracep->declBit(c+2523,"cfg_ds", false,-1);
    tracep->declBit(c+2524,"cfg_dbl", false,-1);
    tracep->declBit(c+2525,"r_frame_err", false,-1);
    tracep->declBus(c+2526,"cmd_type", false,-1, 1,0);
    tracep->declBus(c+2527,"resp_count", false,-1, 7,0);
    tracep->declBit(c+2528,"frame_err", false,-1);
    tracep->declBit(c+2529,"w_done", false,-1);
    tracep->declBit(c+2530,"crc_err", false,-1);
    tracep->declBit(c+2531,"w_no_response", false,-1);
    tracep->declBus(c+2430,"mem_addr", false,-1, 9,0);
    tracep->declQuad(c+2532,"rx_sreg", false,-1, 39,0);
    tracep->declBit(c+2534,"rx_timeout", false,-1);
    tracep->declBus(c+2535,"rx_timeout_counter", false,-1, 25,0);
    tracep->declBus(c+2536,"crc_fill", false,-1, 6,0);
    tracep->declBit(c+2537,"r_busy", false,-1);
    tracep->declBit(c+2538,"new_data", false,-1);
    tracep->declBit(c+2539,"r_done", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_txframe ");
    tracep->declBus(c+5069,"NCRC", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5248,"CRC_POLYNOMIAL", false,-1, 15,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+73,"i_reset", false,-1);
    tracep->declBus(c+2412,"i_cfg_spd", false,-1, 7,0);
    tracep->declBus(c+2413,"i_cfg_width", false,-1, 1,0);
    tracep->declBit(c+2378,"i_cfg_ddr", false,-1);
    tracep->declBit(c+2432,"i_en", false,-1);
    tracep->declBit(c+2414,"i_ckstb", false,-1);
    tracep->declBit(c+2415,"i_hlfck", false,-1);
    tracep->declBit(c+2540,"S_VALID", false,-1);
    tracep->declBit(c+2434,"S_READY", false,-1);
    tracep->declBus(c+2436,"S_DATA", false,-1, 31,0);
    tracep->declBit(c+2435,"S_LAST", false,-1);
    tracep->declBit(c+2384,"tx_valid", false,-1);
    tracep->declBus(c+2387,"tx_data", false,-1, 31,0);
    tracep->declBus(c+5116,"P_IDLE", false,-1, 1,0);
    tracep->declBus(c+5117,"P_DATA", false,-1, 1,0);
    tracep->declBus(c+5118,"P_CRC", false,-1, 1,0);
    tracep->declBus(c+5119,"P_LAST", false,-1, 1,0);
    tracep->declBus(c+5116,"WIDTH_1W", false,-1, 1,0);
    tracep->declBus(c+5117,"WIDTH_4W", false,-1, 1,0);
    tracep->declBus(c+5118,"WIDTH_8W", false,-1, 1,0);
    tracep->declBus(c+5116,"P_1D", false,-1, 1,0);
    tracep->declBus(c+5117,"P_2D", false,-1, 1,0);
    tracep->declBus(c+5118,"P_4D", false,-1, 1,0);
    tracep->declBit(c+2541,"cfg_ddr", false,-1);
    tracep->declBus(c+2542,"cfg_width", false,-1, 1,0);
    tracep->declBus(c+2543,"cfg_period", false,-1, 1,0);
    tracep->declBit(c+2544,"start_packet", false,-1);
    tracep->declBit(c+2545,"pre_valid", false,-1);
    tracep->declBus(c+2546,"pstate", false,-1, 1,0);
    tracep->declBit(c+2547,"pre_ready", false,-1);
    tracep->declBus(c+2548,"pre_data", false,-1, 31,0);
    tracep->declBus(c+2549,"pre_count", false,-1, 3,0);
    tracep->declBus(c+5250,"ik", false,-1, 31,0);
    tracep->declBus(c+5250,"jk", false,-1, 31,0);
    tracep->declBus(c+2550,"crc_1w_reg", false,-1, 15,0);
    tracep->declBus(c+2551,"di_crc_2w", false,-1, 31,0);
    tracep->declBus(c+2552,"nxt_crc_2w", false,-1, 31,0);
    tracep->declBus(c+2553,"new_crc_2w", false,-1, 31,0);
    tracep->declBus(c+2554,"crc_2w_reg", false,-1, 31,0);
    tracep->declQuad(c+2555,"di_crc_4w", false,-1, 63,0);
    tracep->declQuad(c+2557,"nxt_crc_4w", false,-1, 63,0);
    tracep->declQuad(c+2559,"new_crc_4w", false,-1, 63,0);
    tracep->declQuad(c+2561,"crc_4w_reg", false,-1, 63,0);
    tracep->declArray(c+2563,"di_crc_8w", false,-1, 127,0);
    tracep->declArray(c+2567,"nxt_crc_8w", false,-1, 127,0);
    tracep->declArray(c+2571,"new_crc_8w", false,-1, 127,0);
    tracep->declArray(c+2575,"crc_8w_reg", false,-1, 127,0);
    tracep->declArray(c+2579,"di_crc_8d", false,-1, 255,0);
    tracep->declArray(c+2587,"nxt_crc_8d", false,-1, 255,0);
    tracep->declArray(c+2595,"new_crc_8d", false,-1, 255,0);
    tracep->declArray(c+2603,"crc_8d_reg", false,-1, 255,0);
    tracep->declBit(c+2384,"ck_valid", false,-1);
    tracep->declBus(c+2611,"ck_counts", false,-1, 4,0);
    tracep->declBus(c+2387,"ck_data", false,-1, 31,0);
    tracep->declBus(c+2612,"ck_sreg", false,-1, 31,0);
    tracep->declBit(c+2613,"ck_stop_bit", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("u_fan ");
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4539,"i_wb_cyc", false,-1);
    tracep->declBit(c+4540,"i_wb_stb", false,-1);
    tracep->declBit(c+4541,"i_wb_we", false,-1);
    tracep->declBus(c+4595,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4543,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4544,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+403,"o_wb_ack", false,-1);
    tracep->declBus(c+404,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+4959,"i_temp_sda", false,-1);
    tracep->declBit(c+4960,"i_temp_scl", false,-1);
    tracep->declBit(c+4961,"o_temp_sda", false,-1);
    tracep->declBit(c+4962,"o_temp_scl", false,-1);
    tracep->declBit(c+4963,"o_fpga_pwm", false,-1);
    tracep->declBit(c+4964,"o_sys_pwm", false,-1);
    tracep->declBit(c+4965,"i_fan_tach", false,-1);
    tracep->declBus(c+5009,"temp_debug", false,-1, 31,0);
    tracep->declBus(c+5251,"CK_PER_SECOND", false,-1, 31,0);
    tracep->declBus(c+5252,"CK_PER_MS", false,-1, 31,0);
    tracep->declBus(c+5253,"PWM_HZ", false,-1, 31,0);
    tracep->declBus(c+5254,"MAX_PWM", false,-1, 31,0);
    tracep->declBus(c+5136,"LGPWM", false,-1, 31,0);
    tracep->declBus(c+2614,"pwm_counter", false,-1, 12,0);
    tracep->declBus(c+2615,"ctl_fpga", false,-1, 12,0);
    tracep->declBus(c+2616,"ctl_sys", false,-1, 12,0);
    tracep->declBit(c+2617,"ck_tach", false,-1);
    tracep->declBit(c+2618,"last_tach", false,-1);
    tracep->declBus(c+2619,"pipe_tach", false,-1, 1,0);
    tracep->declBit(c+2620,"tach_reset", false,-1);
    tracep->declBus(c+2621,"tach_count", false,-1, 26,0);
    tracep->declBus(c+2622,"tach_counter", false,-1, 26,0);
    tracep->declBus(c+2623,"tach_timer", false,-1, 26,0);
    tracep->declBit(c+5074,"i2c_wb_stall", false,-1);
    tracep->declBit(c+2624,"i2c_wb_ack", false,-1);
    tracep->declBus(c+2625,"i2c_wb_data", false,-1, 31,0);
    tracep->declBit(c+2626,"ign_mem_cyc", false,-1);
    tracep->declBit(c+2627,"mem_stb", false,-1);
    tracep->declBit(c+5074,"ign_mem_we", false,-1);
    tracep->declBit(c+5070,"ign_mem_sel", false,-1);
    tracep->declBus(c+2628,"mem_addr", false,-1, 4,0);
    tracep->declBus(c+5112,"ign_mem_data", false,-1, 7,0);
    tracep->declBus(c+2629,"mem_data", false,-1, 7,0);
    tracep->declBit(c+2630,"mem_ack", false,-1);
    tracep->declBit(c+2631,"i2cd_valid", false,-1);
    tracep->declBit(c+2632,"i2cd_last", false,-1);
    tracep->declBit(c+5074,"ign_i2cd_id", false,-1);
    tracep->declBus(c+2633,"i2cd_data", false,-1, 7,0);
    tracep->declBit(c+2634,"pp_ms", false,-1);
    tracep->declBus(c+2635,"trigger_counter", false,-1, 16,0);
    tracep->declBus(c+2636,"temp_tmp", false,-1, 23,0);
    tracep->declBus(c+2637,"temp_data", false,-1, 31,0);
    tracep->declBit(c+2638,"pre_ack", false,-1);
    tracep->declBus(c+2639,"pre_data", false,-1, 31,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("u_i2ccpu ");
    tracep->declBus(c+5154,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5063,"DATA_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5063,"I2C_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5076,"AXIS_ID_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5113,"DEF_CHANNEL", false,-1, 0,0);
    tracep->declBus(c+5154,"AW", false,-1, 31,0);
    tracep->declBus(c+5063,"DW", false,-1, 31,0);
    tracep->declBus(c+5063,"RW", false,-1, 31,0);
    tracep->declBus(c+5154,"BAW", false,-1, 31,0);
    tracep->declBus(c+5190,"RESET_ADDRESS", false,-1, 4,0);
    tracep->declBus(c+5113,"OPT_START_HALTED", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_MANUAL", false,-1, 0,0);
    tracep->declBus(c+5076,"OPT_WATCHDOG", false,-1, 31,0);
    tracep->declBus(c+5255,"DEF_CKCOUNT", false,-1, 11,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4539,"i_wb_cyc", false,-1);
    tracep->declBit(c+4596,"i_wb_stb", false,-1);
    tracep->declBit(c+4541,"i_wb_we", false,-1);
    tracep->declBus(c+4597,"i_wb_addr", false,-1, 1,0);
    tracep->declBus(c+4543,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4544,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+2624,"o_wb_ack", false,-1);
    tracep->declBus(c+2625,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+2626,"o_pf_cyc", false,-1);
    tracep->declBit(c+2627,"o_pf_stb", false,-1);
    tracep->declBit(c+5074,"o_pf_we", false,-1);
    tracep->declBus(c+2628,"o_pf_addr", false,-1, 4,0);
    tracep->declBus(c+5112,"o_pf_data", false,-1, 7,0);
    tracep->declBus(c+5070,"o_pf_sel", false,-1, 0,0);
    tracep->declBit(c+5074,"i_pf_stall", false,-1);
    tracep->declBit(c+2630,"i_pf_ack", false,-1);
    tracep->declBit(c+5074,"i_pf_err", false,-1);
    tracep->declBus(c+2629,"i_pf_data", false,-1, 7,0);
    tracep->declBit(c+4959,"i_i2c_sda", false,-1);
    tracep->declBit(c+4960,"i_i2c_scl", false,-1);
    tracep->declBit(c+4961,"o_i2c_sda", false,-1);
    tracep->declBit(c+4962,"o_i2c_scl", false,-1);
    tracep->declBit(c+2631,"M_AXIS_TVALID", false,-1);
    tracep->declBit(c+5077,"M_AXIS_TREADY", false,-1);
    tracep->declBus(c+2633,"M_AXIS_TDATA", false,-1, 7,0);
    tracep->declBit(c+2632,"M_AXIS_TLAST", false,-1);
    tracep->declBus(c+5074,"M_AXIS_TID", false,-1, 0,0);
    tracep->declBit(c+2634,"i_sync_signal", false,-1);
    tracep->declBus(c+5009,"o_debug", false,-1, 31,0);
    tracep->declBus(c+5116,"ADR_CONTROL", false,-1, 1,0);
    tracep->declBus(c+5117,"ADR_OVERRIDE", false,-1, 1,0);
    tracep->declBus(c+5118,"ADR_ADDRESS", false,-1, 1,0);
    tracep->declBus(c+5119,"ADR_CKCOUNT", false,-1, 1,0);
    tracep->declBus(c+5073,"HALT_BIT", false,-1, 31,0);
    tracep->declBus(c+5110,"ERR_BIT", false,-1, 31,0);
    tracep->declBus(c+5121,"ABORT_BIT", false,-1, 31,0);
    tracep->declBus(c+5068,"SOFTHALT_BIT", false,-1, 31,0);
    tracep->declBus(c+5156,"OVW_VALID", false,-1, 31,0);
    tracep->declBus(c+5157,"MANUAL_BIT", false,-1, 31,0);
    tracep->declBus(c+5122,"CMD_NOOP", false,-1, 3,0);
    tracep->declBus(c+5124,"CMD_STOP", false,-1, 3,0);
    tracep->declBus(c+5125,"CMD_SEND", false,-1, 3,0);
    tracep->declBus(c+5126,"CMD_RXK", false,-1, 3,0);
    tracep->declBus(c+5127,"CMD_RXN", false,-1, 3,0);
    tracep->declBus(c+5115,"CMD_RXLK", false,-1, 3,0);
    tracep->declBus(c+5128,"CMD_RXLN", false,-1, 3,0);
    tracep->declBus(c+5129,"CMD_WAIT", false,-1, 3,0);
    tracep->declBus(c+5202,"CMD_HALT", false,-1, 3,0);
    tracep->declBus(c+5203,"CMD_ABORT", false,-1, 3,0);
    tracep->declBus(c+5204,"CMD_TARGET", false,-1, 3,0);
    tracep->declBus(c+5205,"CMD_JUMP", false,-1, 3,0);
    tracep->declBus(c+5206,"CMD_CHANNEL", false,-1, 3,0);
    tracep->declBit(c+2640,"cpu_reset", false,-1);
    tracep->declBit(c+5074,"cpu_clear_cache", false,-1);
    tracep->declBit(c+2641,"cpu_new_pc", false,-1);
    tracep->declBus(c+2642,"pf_jump_addr", false,-1, 4,0);
    tracep->declBit(c+2643,"pf_valid", false,-1);
    tracep->declBit(c+2644,"pf_ready", false,-1);
    tracep->declBus(c+2645,"pf_insn", false,-1, 7,0);
    tracep->declBus(c+2646,"pf_insn_addr", false,-1, 4,0);
    tracep->declBit(c+2647,"pf_illegal", false,-1);
    tracep->declBit(c+2648,"half_valid", false,-1);
    tracep->declBit(c+2649,"imm_cycle", false,-1);
    tracep->declBit(c+4598,"next_valid", false,-1);
    tracep->declBus(c+4599,"next_insn", false,-1, 7,0);
    tracep->declBit(c+2650,"insn_ready", false,-1);
    tracep->declBit(c+2651,"half_ready", false,-1);
    tracep->declBit(c+2652,"i2c_abort", false,-1);
    tracep->declBit(c+2653,"insn_valid", false,-1);
    tracep->declBus(c+2654,"insn", false,-1, 11,0);
    tracep->declBus(c+2655,"half_insn", false,-1, 3,0);
    tracep->declBit(c+2656,"i2c_ckedge", false,-1);
    tracep->declBit(c+2657,"i2c_stretch", false,-1);
    tracep->declBus(c+2658,"i2c_ckcount", false,-1, 11,0);
    tracep->declBus(c+2659,"ckcount", false,-1, 11,0);
    tracep->declBus(c+2660,"abort_address", false,-1, 4,0);
    tracep->declBus(c+2661,"jump_target", false,-1, 4,0);
    tracep->declBit(c+2662,"r_wait", false,-1);
    tracep->declBit(c+2663,"soft_halt_request", false,-1);
    tracep->declBit(c+2640,"r_halted", false,-1);
    tracep->declBit(c+2664,"r_err", false,-1);
    tracep->declBit(c+2665,"r_aborted", false,-1);
    tracep->declBit(c+2666,"r_manual", false,-1);
    tracep->declBit(c+2667,"r_sda", false,-1);
    tracep->declBit(c+2668,"r_scl", false,-1);
    tracep->declBit(c+2669,"w_stopped", false,-1);
    tracep->declBit(c+2670,"w_sda", false,-1);
    tracep->declBit(c+2671,"w_scl", false,-1);
    tracep->declBit(c+4600,"bus_read", false,-1);
    tracep->declBit(c+4601,"bus_write", false,-1);
    tracep->declBit(c+4602,"bus_override", false,-1);
    tracep->declBit(c+4603,"bus_manual", false,-1);
    tracep->declBit(c+2672,"ovw_ready", false,-1);
    tracep->declBit(c+4604,"bus_jump", false,-1);
    tracep->declBus(c+4597,"bus_write_addr", false,-1, 1,0);
    tracep->declBus(c+4597,"bus_read_addr", false,-1, 1,0);
    tracep->declBus(c+4543,"bus_write_data", false,-1, 31,0);
    tracep->declBus(c+4544,"bus_write_strb", false,-1, 3,0);
    tracep->declBus(c+2625,"bus_read_data", false,-1, 31,0);
    tracep->declBit(c+2673,"s_tvalid", false,-1);
    tracep->declBit(c+2651,"s_tready", false,-1);
    tracep->declBus(c+2674,"ovw_data", false,-1, 9,0);
    tracep->declBus(c+5027,"w_control", false,-1, 31,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_MANUAL ");
    tracep->declBit(c+2666,"manual", false,-1);
    tracep->declBit(c+2668,"scl", false,-1);
    tracep->declBit(c+2667,"sda", false,-1);
    tracep->declBit(c+2675,"o_scl", false,-1);
    tracep->declBit(c+2676,"o_sda", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_axisi2c ");
    tracep->declBus(c+5076,"OPT_WATCHDOG", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"S_AXI_ACLK", false,-1);
    tracep->declBit(c+74,"S_AXI_ARESETN", false,-1);
    tracep->declBit(c+2673,"S_AXIS_TVALID", false,-1);
    tracep->declBit(c+2650,"S_AXIS_TREADY", false,-1);
    tracep->declBus(c+2677,"S_AXIS_TDATA", false,-1, 10,0);
    tracep->declBit(c+2631,"M_AXIS_TVALID", false,-1);
    tracep->declBit(c+5077,"M_AXIS_TREADY", false,-1);
    tracep->declBus(c+2633,"M_AXIS_TDATA", false,-1, 7,0);
    tracep->declBit(c+2632,"M_AXIS_TLAST", false,-1);
    tracep->declBit(c+2656,"i_ckedge", false,-1);
    tracep->declBit(c+2657,"o_stretch", false,-1);
    tracep->declBit(c+4960,"i_scl", false,-1);
    tracep->declBit(c+4959,"i_sda", false,-1);
    tracep->declBit(c+2671,"o_scl", false,-1);
    tracep->declBit(c+2670,"o_sda", false,-1);
    tracep->declBit(c+2652,"o_abort", false,-1);
    tracep->declBus(c+5122,"IDLE_STOPPED", false,-1, 3,0);
    tracep->declBus(c+5123,"START", false,-1, 3,0);
    tracep->declBus(c+5124,"IDLE_ACTIVE", false,-1, 3,0);
    tracep->declBus(c+5125,"STOP", false,-1, 3,0);
    tracep->declBus(c+5126,"DATA", false,-1, 3,0);
    tracep->declBus(c+5127,"CLOCK", false,-1, 3,0);
    tracep->declBus(c+5115,"ACK", false,-1, 3,0);
    tracep->declBus(c+5128,"CKACKLO", false,-1, 3,0);
    tracep->declBus(c+5129,"CKACKHI", false,-1, 3,0);
    tracep->declBus(c+5202,"RXNAK", false,-1, 3,0);
    tracep->declBus(c+5203,"ABORT", false,-1, 3,0);
    tracep->declBus(c+5204,"REPEAT_START", false,-1, 3,0);
    tracep->declBus(c+5205,"REPEAT_START2", false,-1, 3,0);
    tracep->declBus(c+5113,"D_RD", false,-1, 0,0);
    tracep->declBus(c+5070,"D_WR", false,-1, 0,0);
    tracep->declBus(c+5159,"CMD_NOOP", false,-1, 2,0);
    tracep->declBus(c+5166,"CMD_START", false,-1, 2,0);
    tracep->declBus(c+5160,"CMD_STOP", false,-1, 2,0);
    tracep->declBus(c+5162,"CMD_SEND", false,-1, 2,0);
    tracep->declBus(c+5207,"CMD_RXK", false,-1, 2,0);
    tracep->declBus(c+5208,"CMD_RXN", false,-1, 2,0);
    tracep->declBus(c+5209,"CMD_RXLK", false,-1, 2,0);
    tracep->declBus(c+5210,"CMD_RXLN", false,-1, 2,0);
    tracep->declBus(c+5113,"OPT_ABORT_REQUEST", false,-1, 0,0);
    tracep->declBit(c+2678,"last_byte", false,-1);
    tracep->declBit(c+2679,"dir", false,-1);
    tracep->declBit(c+2680,"will_ack", false,-1);
    tracep->declBus(c+2681,"state", false,-1, 3,0);
    tracep->declBus(c+2682,"nbits", false,-1, 2,0);
    tracep->declBus(c+2683,"sreg", false,-1, 7,0);
    tracep->declBit(c+2684,"q_scl", false,-1);
    tracep->declBit(c+2685,"q_sda", false,-1);
    tracep->declBit(c+2686,"ck_scl", false,-1);
    tracep->declBit(c+2687,"ck_sda", false,-1);
    tracep->declBit(c+2688,"lst_scl", false,-1);
    tracep->declBit(c+2689,"lst_sda", false,-1);
    tracep->declBit(c+2690,"stop_bit", false,-1);
    tracep->declBit(c+2691,"channel_busy", false,-1);
    tracep->declBit(c+5074,"watchdog_timeout", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_fetch ");
    tracep->declBus(c+5154,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5063,"INSN_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5063,"DATA_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5154,"AW", false,-1, 31,0);
    tracep->declBus(c+5063,"DW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+75,"i_reset", false,-1);
    tracep->declBit(c+2641,"i_new_pc", false,-1);
    tracep->declBit(c+5074,"i_clear_cache", false,-1);
    tracep->declBit(c+2644,"i_ready", false,-1);
    tracep->declBus(c+2642,"i_pc", false,-1, 4,0);
    tracep->declBit(c+2643,"o_valid", false,-1);
    tracep->declBit(c+2647,"o_illegal", false,-1);
    tracep->declBus(c+2645,"o_insn", false,-1, 7,0);
    tracep->declBus(c+2646,"o_pc", false,-1, 4,0);
    tracep->declBit(c+2626,"o_wb_cyc", false,-1);
    tracep->declBit(c+2627,"o_wb_stb", false,-1);
    tracep->declBit(c+5074,"o_wb_we", false,-1);
    tracep->declBus(c+2628,"o_wb_addr", false,-1, 4,0);
    tracep->declBus(c+5112,"o_wb_data", false,-1, 7,0);
    tracep->declBit(c+5074,"i_wb_stall", false,-1);
    tracep->declBit(c+2630,"i_wb_ack", false,-1);
    tracep->declBit(c+5074,"i_wb_err", false,-1);
    tracep->declBus(c+2629,"i_wb_data", false,-1, 7,0);
    tracep->declBit(c+2692,"last_stb", false,-1);
    tracep->declBit(c+2693,"invalid_bus_cycle", false,-1);
    tracep->declBus(c+2694,"cache_word", false,-1, 7,0);
    tracep->declBit(c+2695,"cache_valid", false,-1);
    tracep->declBus(c+2696,"inflight", false,-1, 1,0);
    tracep->declBit(c+2697,"cache_illegal", false,-1);
    tracep->declBit(c+5074,"r_valid", false,-1);
    tracep->declBus(c+5112,"r_insn", false,-1, 7,0);
    tracep->declBus(c+2629,"i_wb_shifted", false,-1, 7,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("u_i2cdma ");
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declBus(c+5063,"SW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4521,"i_wb_cyc", false,-1);
    tracep->declBit(c+4522,"i_wb_stb", false,-1);
    tracep->declBit(c+4523,"i_wb_we", false,-1);
    tracep->declBus(c+4605,"i_wb_addr", false,-1, 1,0);
    tracep->declBus(c+4525,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4526,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+397,"o_wb_ack", false,-1);
    tracep->declBus(c+398,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+2698,"S_VALID", false,-1);
    tracep->declBit(c+173,"S_READY", false,-1);
    tracep->declBus(c+177,"S_DATA", false,-1, 7,0);
    tracep->declBit(c+176,"S_LAST", false,-1);
    tracep->declBit(c+199,"o_dma_cyc", false,-1);
    tracep->declBit(c+200,"o_dma_stb", false,-1);
    tracep->declBit(c+5077,"o_dma_we", false,-1);
    tracep->declBus(c+201,"o_dma_addr", false,-1, 21,0);
    tracep->declArray(c+202,"o_dma_data", false,-1, 511,0);
    tracep->declQuad(c+218,"o_dma_sel", false,-1, 63,0);
    tracep->declBit(c+220,"i_dma_stall", false,-1);
    tracep->declBit(c+221,"i_dma_ack", false,-1);
    tracep->declArray(c+223,"i_dma_data", false,-1, 511,0);
    tracep->declBit(c+222,"i_dma_err", false,-1);
    tracep->declBus(c+5076,"SUBLSB", false,-1, 31,0);
    tracep->declBus(c+5153,"WBLSB", false,-1, 31,0);
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+2699,"r_baseaddr", false,-1, 27,0);
    tracep->declBus(c+2700,"r_memlen", false,-1, 27,0);
    tracep->declBus(c+2701,"subaddr", false,-1, 5,0);
    tracep->declBus(c+2702,"current_addr", false,-1, 27,0);
    tracep->declBus(c+4606,"next_baseaddr", false,-1, 31,0);
    tracep->declBus(c+4607,"next_memlen", false,-1, 31,0);
    tracep->declBit(c+2703,"wb_last", false,-1);
    tracep->declBit(c+2704,"bus_err", false,-1);
    tracep->declBit(c+2705,"r_reset", false,-1);
    tracep->declBit(c+2706,"r_overflow", false,-1);
    tracep->declBit(c+2707,"skd_valid", false,-1);
    tracep->declBit(c+2708,"skd_ready", false,-1);
    tracep->declBit(c+2709,"skd_last", false,-1);
    tracep->declBus(c+2710,"skd_data", false,-1, 7,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("sskd ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5156,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+2698,"i_valid", false,-1);
    tracep->declBit(c+173,"o_ready", false,-1);
    tracep->declBus(c+2711,"i_data", false,-1, 8,0);
    tracep->declBit(c+2707,"o_valid", false,-1);
    tracep->declBit(c+2708,"i_ready", false,-1);
    tracep->declBus(c+2712,"o_data", false,-1, 8,0);
    tracep->declBus(c+2713,"w_data", false,-1, 8,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+2714,"r_valid", false,-1);
    tracep->declBus(c+2713,"r_data", false,-1, 8,0);
    tracep->pushNamePrefix("REG_OUTPUT ");
    tracep->declBit(c+2707,"ro_valid", false,-1);
    tracep->popNamePrefix(4);
    tracep->pushNamePrefix("u_sdcard ");
    tracep->declBus(c+5158,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5065,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CARD_DETECT", false,-1, 0,0);
    tracep->declBus(c+5133,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+5074,"i_hsclk", false,-1);
    tracep->declBit(c+4545,"i_wb_cyc", false,-1);
    tracep->declBit(c+4546,"i_wb_stb", false,-1);
    tracep->declBit(c+4547,"i_wb_we", false,-1);
    tracep->declBus(c+4608,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4549,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4550,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+405,"o_wb_ack", false,-1);
    tracep->declBus(c+406,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+4979,"o_ck", false,-1);
    tracep->declBit(c+4980,"i_ds", false,-1);
    tracep->declBit(c+4981,"io_cmd_tristate", false,-1);
    tracep->declBit(c+4982,"o_cmd", false,-1);
    tracep->declBit(c+4983,"i_cmd", false,-1);
    tracep->declBus(c+4984,"io_dat_tristate", false,-1, 3,0);
    tracep->declBus(c+4985,"o_dat", false,-1, 3,0);
    tracep->declBus(c+4986,"i_dat", false,-1, 3,0);
    tracep->declBit(c+4987,"i_card_detect", false,-1);
    tracep->declBit(c+5074,"o_1p8v", false,-1);
    tracep->declBit(c+161,"o_int", false,-1);
    tracep->declBus(c+179,"o_debug", false,-1, 31,0);
    tracep->declBit(c+2715,"cfg_ddr", false,-1);
    tracep->declBus(c+2716,"cfg_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2717,"sdclk", false,-1, 7,0);
    tracep->declBit(c+2718,"cmd_en", false,-1);
    tracep->declBit(c+2719,"pp_cmd", false,-1);
    tracep->declBus(c+2720,"cmd_data", false,-1, 1,0);
    tracep->declBit(c+2721,"data_en", false,-1);
    tracep->declBit(c+2722,"pp_data", false,-1);
    tracep->declBit(c+2723,"rx_en", false,-1);
    tracep->declBus(c+2724,"tx_data", false,-1, 31,0);
    tracep->declBit(c+2725,"afifo_reset_n", false,-1);
    tracep->declBus(c+2726,"rply_strb", false,-1, 1,0);
    tracep->declBus(c+2727,"rply_data", false,-1, 1,0);
    tracep->declBit(c+2728,"card_busy", false,-1);
    tracep->declBus(c+2729,"rx_strb", false,-1, 1,0);
    tracep->declBus(c+2730,"rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"AC_VALID", false,-1);
    tracep->declBus(c+5116,"AC_DATA", false,-1, 1,0);
    tracep->declBit(c+5074,"AD_VALID", false,-1);
    tracep->declBus(c+5076,"AD_DATA", false,-1, 31,0);
    tracep->pushNamePrefix("u_sdfrontend ");
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5065,"NUMIO", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5074,"i_hsclk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+2715,"i_cfg_ddr", false,-1);
    tracep->declBus(c+2716,"i_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2717,"i_sdclk", false,-1, 7,0);
    tracep->declBit(c+2718,"i_cmd_en", false,-1);
    tracep->declBit(c+2719,"i_pp_cmd", false,-1);
    tracep->declBus(c+2720,"i_cmd_data", false,-1, 1,0);
    tracep->declBit(c+2721,"i_data_en", false,-1);
    tracep->declBit(c+2723,"i_rx_en", false,-1);
    tracep->declBit(c+2722,"i_pp_data", false,-1);
    tracep->declBus(c+2724,"i_tx_data", false,-1, 31,0);
    tracep->declBit(c+2725,"i_afifo_reset_n", false,-1);
    tracep->declBit(c+2728,"o_data_busy", false,-1);
    tracep->declBus(c+2726,"o_cmd_strb", false,-1, 1,0);
    tracep->declBus(c+2727,"o_cmd_data", false,-1, 1,0);
    tracep->declBus(c+2729,"o_rx_strb", false,-1, 1,0);
    tracep->declBus(c+2730,"o_rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"MAC_VALID", false,-1);
    tracep->declBus(c+5116,"MAC_DATA", false,-1, 1,0);
    tracep->declBit(c+5074,"MAD_VALID", false,-1);
    tracep->declBus(c+5076,"MAD_DATA", false,-1, 31,0);
    tracep->declBit(c+4979,"o_ck", false,-1);
    tracep->declBit(c+4980,"i_ds", false,-1);
    tracep->declBit(c+4981,"io_cmd_tristate", false,-1);
    tracep->declBit(c+4982,"o_cmd", false,-1);
    tracep->declBit(c+4983,"i_cmd", false,-1);
    tracep->declBus(c+4984,"io_dat_tristate", false,-1, 3,0);
    tracep->declBus(c+4985,"o_dat", false,-1, 3,0);
    tracep->declBus(c+4986,"i_dat", false,-1, 3,0);
    tracep->declBus(c+179,"o_debug", false,-1, 31,0);
    tracep->declBit(c+2728,"dat0_busy", false,-1);
    tracep->declBit(c+2731,"wait_for_busy", false,-1);
    tracep->pushNamePrefix("GEN_IODDR_IO ");
    tracep->declBus(c+2732,"w_cmd", false,-1, 1,0);
    for (int i = 0; i < 16; ++i) {
        tracep->declBit(c+2733+i*1,"pre_dat", true,(i+0));
    }
    tracep->declBus(c+2749,"w_dat", false,-1, 15,0);
    tracep->declBus(c+2750,"next_pedge", false,-1, 1,0);
    tracep->declBus(c+2751,"next_dedge", false,-1, 1,0);
    tracep->declBus(c+2752,"ck_sreg", false,-1, 5,0);
    tracep->declBus(c+2753,"pck_sreg", false,-1, 5,0);
    tracep->declBus(c+2754,"sample_ck", false,-1, 1,0);
    tracep->declBus(c+2755,"cmd_sample_ck", false,-1, 1,0);
    tracep->declBit(c+2756,"resp_started", false,-1);
    tracep->declBit(c+2757,"io_started", false,-1);
    tracep->declBit(c+2758,"last_ck", false,-1);
    tracep->declBit(c+2759,"r_cmd_strb", false,-1);
    tracep->declBit(c+2760,"r_cmd_data", false,-1);
    tracep->declBit(c+2761,"r_rx_strb", false,-1);
    tracep->declBus(c+2762,"r_rx_data", false,-1, 7,0);
    tracep->declBit(c+2763,"io_clk_tristate", false,-1);
    tracep->declBit(c+4979,"ign_clk", false,-1);
    tracep->declBus(c+5250,"ipre", false,-1, 31,0);
    tracep->declBus(c+2764,"w_out", false,-1, 7,0);
    tracep->declBit(c+5074,"unused_ddr", false,-1);
    tracep->pushNamePrefix("DRIVE_DDR_IO[0] ");
    tracep->declBit(c+5028,"enable", false,-1);
    tracep->pushNamePrefix("u_dat_ddr ");
    tracep->declBus(c+5070,"OPT_BIDIR", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5028,"i_en", false,-1);
    tracep->declBus(c+5029,"i_data", false,-1, 1,0);
    tracep->declBit(c+2765,"io_pin_tristate", false,-1);
    tracep->declBit(c+5030,"i_pin", false,-1);
    tracep->declBit(c+76,"o_pin", false,-1);
    tracep->declBus(c+2766,"o_wide", false,-1, 1,0);
    tracep->declBit(c+77,"w_in", false,-1);
    tracep->declBit(c+76,"w_out", false,-1);
    tracep->declBit(c+2765,"high_z", false,-1);
    tracep->declBus(c+2767,"r_out", false,-1, 1,0);
    tracep->pushNamePrefix("GEN_BIDIRECTIONAL ");
    tracep->declBit(c+2768,"r_p", false,-1);
    tracep->declBit(c+4414,"r_n", false,-1);
    tracep->declBus(c+2766,"r_in", false,-1, 1,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DRIVE_DDR_IO[1] ");
    tracep->declBit(c+5031,"enable", false,-1);
    tracep->pushNamePrefix("u_dat_ddr ");
    tracep->declBus(c+5070,"OPT_BIDIR", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5031,"i_en", false,-1);
    tracep->declBus(c+5032,"i_data", false,-1, 1,0);
    tracep->declBit(c+2769,"io_pin_tristate", false,-1);
    tracep->declBit(c+5033,"i_pin", false,-1);
    tracep->declBit(c+78,"o_pin", false,-1);
    tracep->declBus(c+2770,"o_wide", false,-1, 1,0);
    tracep->declBit(c+79,"w_in", false,-1);
    tracep->declBit(c+78,"w_out", false,-1);
    tracep->declBit(c+2769,"high_z", false,-1);
    tracep->declBus(c+2771,"r_out", false,-1, 1,0);
    tracep->pushNamePrefix("GEN_BIDIRECTIONAL ");
    tracep->declBit(c+2772,"r_p", false,-1);
    tracep->declBit(c+4415,"r_n", false,-1);
    tracep->declBus(c+2770,"r_in", false,-1, 1,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DRIVE_DDR_IO[2] ");
    tracep->declBit(c+5034,"enable", false,-1);
    tracep->pushNamePrefix("u_dat_ddr ");
    tracep->declBus(c+5070,"OPT_BIDIR", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5034,"i_en", false,-1);
    tracep->declBus(c+5035,"i_data", false,-1, 1,0);
    tracep->declBit(c+2773,"io_pin_tristate", false,-1);
    tracep->declBit(c+5036,"i_pin", false,-1);
    tracep->declBit(c+80,"o_pin", false,-1);
    tracep->declBus(c+2774,"o_wide", false,-1, 1,0);
    tracep->declBit(c+81,"w_in", false,-1);
    tracep->declBit(c+80,"w_out", false,-1);
    tracep->declBit(c+2773,"high_z", false,-1);
    tracep->declBus(c+2775,"r_out", false,-1, 1,0);
    tracep->pushNamePrefix("GEN_BIDIRECTIONAL ");
    tracep->declBit(c+2776,"r_p", false,-1);
    tracep->declBit(c+4416,"r_n", false,-1);
    tracep->declBus(c+2774,"r_in", false,-1, 1,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DRIVE_DDR_IO[3] ");
    tracep->declBit(c+5037,"enable", false,-1);
    tracep->pushNamePrefix("u_dat_ddr ");
    tracep->declBus(c+5070,"OPT_BIDIR", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5037,"i_en", false,-1);
    tracep->declBus(c+5038,"i_data", false,-1, 1,0);
    tracep->declBit(c+2777,"io_pin_tristate", false,-1);
    tracep->declBit(c+5039,"i_pin", false,-1);
    tracep->declBit(c+82,"o_pin", false,-1);
    tracep->declBus(c+2778,"o_wide", false,-1, 1,0);
    tracep->declBit(c+83,"w_in", false,-1);
    tracep->declBit(c+82,"w_out", false,-1);
    tracep->declBit(c+2777,"high_z", false,-1);
    tracep->declBus(c+2779,"r_out", false,-1, 1,0);
    tracep->pushNamePrefix("GEN_BIDIRECTIONAL ");
    tracep->declBit(c+2780,"r_p", false,-1);
    tracep->declBit(c+4417,"r_n", false,-1);
    tracep->declBus(c+2778,"r_in", false,-1, 1,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("u_clk_oddr ");
    tracep->declBus(c+5113,"OPT_BIDIR", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5077,"i_en", false,-1);
    tracep->declBus(c+2781,"i_data", false,-1, 1,0);
    tracep->declBit(c+2763,"io_pin_tristate", false,-1);
    tracep->declBit(c+4979,"i_pin", false,-1);
    tracep->declBit(c+4979,"o_pin", false,-1);
    tracep->declBus(c+5119,"o_wide", false,-1, 1,0);
    tracep->declBit(c+4979,"w_in", false,-1);
    tracep->declBit(c+4979,"w_out", false,-1);
    tracep->declBit(c+2763,"high_z", false,-1);
    tracep->declBus(c+2782,"r_out", false,-1, 1,0);
    tracep->pushNamePrefix("GEN_OUTPUT ");
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_cmd_ddr ");
    tracep->declBus(c+5070,"OPT_BIDIR", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+5040,"i_en", false,-1);
    tracep->declBus(c+5041,"i_data", false,-1, 1,0);
    tracep->declBit(c+4981,"io_pin_tristate", false,-1);
    tracep->declBit(c+4983,"i_pin", false,-1);
    tracep->declBit(c+4982,"o_pin", false,-1);
    tracep->declBus(c+2732,"o_wide", false,-1, 1,0);
    tracep->declBit(c+84,"w_in", false,-1);
    tracep->declBit(c+4982,"w_out", false,-1);
    tracep->declBit(c+2783,"high_z", false,-1);
    tracep->declBus(c+2784,"r_out", false,-1, 1,0);
    tracep->pushNamePrefix("GEN_BIDIRECTIONAL ");
    tracep->declBit(c+2785,"r_p", false,-1);
    tracep->declBit(c+4418,"r_n", false,-1);
    tracep->declBus(c+2732,"r_in", false,-1, 1,0);
    tracep->popNamePrefix(4);
    tracep->pushNamePrefix("u_sdio ");
    tracep->declBus(c+5158,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5065,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CARD_DETECT", false,-1, 0,0);
    tracep->declBus(c+5133,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4545,"i_wb_cyc", false,-1);
    tracep->declBit(c+4546,"i_wb_stb", false,-1);
    tracep->declBit(c+4547,"i_wb_we", false,-1);
    tracep->declBus(c+4608,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4549,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4550,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+405,"o_wb_ack", false,-1);
    tracep->declBus(c+406,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+4987,"i_card_detect", false,-1);
    tracep->declBit(c+5074,"o_1p8v", false,-1);
    tracep->declBit(c+161,"o_int", false,-1);
    tracep->declBit(c+2715,"o_cfg_ddr", false,-1);
    tracep->declBus(c+2716,"o_cfg_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2717,"o_sdclk", false,-1, 7,0);
    tracep->declBit(c+2718,"o_cmd_en", false,-1);
    tracep->declBit(c+2719,"o_pp_cmd", false,-1);
    tracep->declBus(c+2720,"o_cmd_data", false,-1, 1,0);
    tracep->declBit(c+2721,"o_data_en", false,-1);
    tracep->declBit(c+2722,"o_pp_data", false,-1);
    tracep->declBit(c+2723,"o_rx_en", false,-1);
    tracep->declBus(c+2724,"o_tx_data", false,-1, 31,0);
    tracep->declBit(c+2725,"o_afifo_reset_n", false,-1);
    tracep->declBus(c+2726,"i_cmd_strb", false,-1, 1,0);
    tracep->declBus(c+2727,"i_cmd_data", false,-1, 1,0);
    tracep->declBit(c+2728,"i_card_busy", false,-1);
    tracep->declBus(c+2729,"i_rx_strb", false,-1, 1,0);
    tracep->declBus(c+2730,"i_rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"S_AC_VALID", false,-1);
    tracep->declBus(c+5116,"S_AC_DATA", false,-1, 1,0);
    tracep->declBit(c+5074,"S_AD_VALID", false,-1);
    tracep->declBus(c+5076,"S_AD_DATA", false,-1, 31,0);
    tracep->declBit(c+2786,"soft_reset", false,-1);
    tracep->declBit(c+2787,"cfg_clk90", false,-1);
    tracep->declBit(c+2788,"cfg_clk_shutdown", false,-1);
    tracep->declBit(c+2789,"cfg_ds", false,-1);
    tracep->declBus(c+2790,"cfg_ckspeed", false,-1, 7,0);
    tracep->declBus(c+2791,"cfg_width", false,-1, 1,0);
    tracep->declBit(c+2792,"clk_stb", false,-1);
    tracep->declBit(c+2793,"clk_half", false,-1);
    tracep->declBus(c+2794,"w_sdclk", false,-1, 7,0);
    tracep->declBus(c+2795,"clk_ckspd", false,-1, 7,0);
    tracep->declBit(c+2796,"cmd_request", false,-1);
    tracep->declBit(c+2797,"cmd_err", false,-1);
    tracep->declBit(c+2798,"cmd_busy", false,-1);
    tracep->declBit(c+2799,"cmd_done", false,-1);
    tracep->declBus(c+2800,"cmd_type", false,-1, 1,0);
    tracep->declBus(c+2801,"cmd_ercode", false,-1, 1,0);
    tracep->declBit(c+2802,"rsp_stb", false,-1);
    tracep->declBus(c+2803,"cmd_id", false,-1, 6,0);
    tracep->declBus(c+2804,"rsp_id", false,-1, 5,0);
    tracep->declBus(c+2805,"cmd_arg", false,-1, 31,0);
    tracep->declBus(c+2806,"rsp_arg", false,-1, 31,0);
    tracep->declBit(c+2807,"cmd_mem_valid", false,-1);
    tracep->declBus(c+5108,"cmd_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2808,"cmd_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2809,"cmd_mem_data", false,-1, 31,0);
    tracep->declBit(c+2810,"tx_en", false,-1);
    tracep->declBit(c+2811,"tx_mem_valid", false,-1);
    tracep->declBit(c+2812,"tx_mem_ready", false,-1);
    tracep->declBit(c+2813,"tx_mem_last", false,-1);
    tracep->declBus(c+2814,"tx_mem_data", false,-1, 31,0);
    tracep->declBit(c+5077,"crc_en", false,-1);
    tracep->declBus(c+2815,"rx_length", false,-1, 12,0);
    tracep->declBit(c+2816,"rx_mem_valid", false,-1);
    tracep->declBus(c+2817,"rx_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2818,"rx_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2819,"rx_mem_data", false,-1, 31,0);
    tracep->declBit(c+2820,"rx_done", false,-1);
    tracep->declBit(c+2821,"rx_err", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("u_clkgen ");
    tracep->declBus(c+5063,"LGMAXDIV", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+2787,"i_cfg_clk90", false,-1);
    tracep->declBus(c+2790,"i_cfg_ckspd", false,-1, 7,0);
    tracep->declBit(c+2788,"i_cfg_shutdown", false,-1);
    tracep->declBit(c+2792,"o_ckstb", false,-1);
    tracep->declBit(c+2793,"o_hlfck", false,-1);
    tracep->declBus(c+2794,"o_ckwide", false,-1, 7,0);
    tracep->declBus(c+2795,"o_ckspd", false,-1, 7,0);
    tracep->declBus(c+5061,"NCTR", false,-1, 31,0);
    tracep->declBit(c+2822,"nxt_stb", false,-1);
    tracep->declBit(c+2823,"nxt_clk", false,-1);
    tracep->declBus(c+2824,"nxt_counter", false,-1, 9,0);
    tracep->declBus(c+2825,"counter", false,-1, 9,0);
    tracep->declBit(c+2826,"clk90", false,-1);
    tracep->declBus(c+2827,"ckspd", false,-1, 7,0);
    tracep->declBit(c+2828,"w_clk90", false,-1);
    tracep->declBus(c+2829,"w_ckspd", false,-1, 7,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_control ");
    tracep->declBus(c+5158,"LGFIFO", false,-1, 31,0);
    tracep->declBus(c+5065,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DDR", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_CARD_DETECT", false,-1, 0,0);
    tracep->declBus(c+5061,"LGFIFOW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_DMA", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_1P8V", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4545,"i_wb_cyc", false,-1);
    tracep->declBit(c+4546,"i_wb_stb", false,-1);
    tracep->declBit(c+4547,"i_wb_we", false,-1);
    tracep->declBus(c+4608,"i_wb_addr", false,-1, 2,0);
    tracep->declBus(c+4549,"i_wb_data", false,-1, 31,0);
    tracep->declBus(c+4550,"i_wb_sel", false,-1, 3,0);
    tracep->declBit(c+5074,"o_wb_stall", false,-1);
    tracep->declBit(c+405,"o_wb_ack", false,-1);
    tracep->declBus(c+406,"o_wb_data", false,-1, 31,0);
    tracep->declBit(c+2787,"o_cfg_clk90", false,-1);
    tracep->declBus(c+2790,"o_cfg_ckspeed", false,-1, 7,0);
    tracep->declBit(c+2788,"o_cfg_shutdown", false,-1);
    tracep->declBus(c+2791,"o_cfg_width", false,-1, 1,0);
    tracep->declBit(c+2789,"o_cfg_ds", false,-1);
    tracep->declBit(c+2715,"o_cfg_ddr", false,-1);
    tracep->declBit(c+2719,"o_pp_cmd", false,-1);
    tracep->declBit(c+2722,"o_pp_data", false,-1);
    tracep->declBus(c+2716,"o_cfg_sample_shift", false,-1, 4,0);
    tracep->declBus(c+2795,"i_ckspd", false,-1, 7,0);
    tracep->declBit(c+2786,"o_soft_reset", false,-1);
    tracep->declBit(c+2796,"o_cmd_request", false,-1);
    tracep->declBus(c+2800,"o_cmd_type", false,-1, 1,0);
    tracep->declBus(c+2803,"o_cmd_id", false,-1, 6,0);
    tracep->declBus(c+2805,"o_arg", false,-1, 31,0);
    tracep->declBit(c+2798,"i_cmd_busy", false,-1);
    tracep->declBit(c+2799,"i_cmd_done", false,-1);
    tracep->declBit(c+2797,"i_cmd_err", false,-1);
    tracep->declBus(c+2801,"i_cmd_ercode", false,-1, 1,0);
    tracep->declBit(c+2802,"i_cmd_response", false,-1);
    tracep->declBus(c+2804,"i_resp", false,-1, 5,0);
    tracep->declBus(c+2806,"i_arg", false,-1, 31,0);
    tracep->declBit(c+2807,"i_cmd_mem_valid", false,-1);
    tracep->declBus(c+5108,"i_cmd_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2808,"i_cmd_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2809,"i_cmd_mem_data", false,-1, 31,0);
    tracep->declBit(c+2810,"o_tx_en", false,-1);
    tracep->declBit(c+2811,"o_tx_mem_valid", false,-1);
    tracep->declBit(c+2830,"i_tx_mem_ready", false,-1);
    tracep->declBus(c+2814,"o_tx_mem_data", false,-1, 31,0);
    tracep->declBit(c+2813,"o_tx_mem_last", false,-1);
    tracep->declBit(c+2721,"i_tx_busy", false,-1);
    tracep->declBit(c+2723,"o_rx_en", false,-1);
    tracep->declBit(c+5077,"o_crc_en", false,-1);
    tracep->declBus(c+2815,"o_length", false,-1, 12,0);
    tracep->declBit(c+2816,"i_rx_mem_valid", false,-1);
    tracep->declBus(c+2818,"i_rx_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2817,"i_rx_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2819,"i_rx_mem_data", false,-1, 31,0);
    tracep->declBit(c+2820,"i_rx_done", false,-1);
    tracep->declBit(c+2821,"i_rx_err", false,-1);
    tracep->declBit(c+4987,"i_card_detect", false,-1);
    tracep->declBit(c+2728,"i_card_busy", false,-1);
    tracep->declBit(c+5074,"o_1p8v", false,-1);
    tracep->declBit(c+161,"o_int", false,-1);
    tracep->declBus(c+5061,"LGFIFO32", false,-1, 31,0);
    tracep->declBus(c+5159,"ADDR_CMD", false,-1, 2,0);
    tracep->declBus(c+5166,"ADDR_ARG", false,-1, 2,0);
    tracep->declBus(c+5160,"ADDR_FIFOA", false,-1, 2,0);
    tracep->declBus(c+5162,"ADDR_FIFOB", false,-1, 2,0);
    tracep->declBus(c+5207,"ADDR_PHY", false,-1, 2,0);
    tracep->declBus(c+5117,"CMD_PREFIX", false,-1, 1,0);
    tracep->declBus(c+5116,"NUL_PREFIX", false,-1, 1,0);
    tracep->declBus(c+5116,"RNO_REPLY", false,-1, 1,0);
    tracep->declBus(c+5118,"R2_REPLY", false,-1, 1,0);
    tracep->declBus(c+5134,"CARD_REMOVED_BIT", false,-1, 31,0);
    tracep->declBus(c+5136,"USE_DMA_BIT", false,-1, 31,0);
    tracep->declBus(c+5158,"FIFO_ID_BIT", false,-1, 31,0);
    tracep->declBus(c+5157,"USE_FIFO_BIT", false,-1, 31,0);
    tracep->declBus(c+5061,"FIFO_WRITE_BIT", false,-1, 31,0);
    tracep->declBus(c+5116,"WIDTH_1W", false,-1, 1,0);
    tracep->declBus(c+5117,"WIDTH_4W", false,-1, 1,0);
    tracep->declBus(c+5118,"WIDTH_8W", false,-1, 1,0);
    tracep->declBit(c+4609,"wb_cmd_stb", false,-1);
    tracep->declBit(c+4610,"wb_phy_stb", false,-1);
    tracep->declBus(c+2803,"r_cmd", false,-1, 6,0);
    tracep->declBit(c+2831,"r_tx_request", false,-1);
    tracep->declBit(c+2832,"r_rx_request", false,-1);
    tracep->declBit(c+2833,"r_tx_sent", false,-1);
    tracep->declBit(c+2834,"r_fifo", false,-1);
    tracep->declBit(c+2835,"r_cmd_err", false,-1);
    tracep->declBus(c+2836,"r_cmd_ecode", false,-1, 1,0);
    tracep->declBus(c+2805,"r_arg", false,-1, 31,0);
    tracep->declBus(c+2837,"lgblk", false,-1, 3,0);
    tracep->declBus(c+2791,"r_width", false,-1, 1,0);
    tracep->declBus(c+2790,"r_ckspeed", false,-1, 7,0);
    tracep->declBus(c+2838,"w_cmd_word", false,-1, 31,0);
    tracep->declBus(c+2839,"w_phy_ctrl", false,-1, 31,0);
    tracep->declBus(c+2840,"blk_words", false,-1, 15,0);
    tracep->declBus(c+2841,"ika", false,-1, 31,0);
    tracep->declBus(c+2842,"ikb", false,-1, 31,0);
    tracep->declBus(c+5189,"NFIFOW", false,-1, 31,0);
    tracep->declBus(c+2843,"tx_fifo_a", false,-1, 31,0);
    tracep->declBus(c+2844,"tx_fifo_b", false,-1, 31,0);
    tracep->declBus(c+5113,"tx_shift", false,-1, 0,0);
    tracep->declBus(c+2845,"fif_wraddr", false,-1, 9,0);
    tracep->declBus(c+2846,"fif_rdaddr", false,-1, 9,0);
    tracep->declBus(c+2847,"fif_a_rdaddr", false,-1, 9,0);
    tracep->declBus(c+2848,"fif_b_rdaddr", false,-1, 9,0);
    tracep->declBus(c+2849,"tx_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2850,"next_tx_mem", false,-1, 31,0);
    tracep->declBit(c+2851,"tx_fifo_last", false,-1);
    tracep->declBit(c+2852,"pre_tx_last", false,-1);
    tracep->declBit(c+2853,"tx_pipe_valid", false,-1);
    tracep->declBit(c+2854,"card_present", false,-1);
    tracep->declBit(c+2855,"card_removed", false,-1);
    tracep->declBit(c+2856,"pre_ack", false,-1);
    tracep->declBus(c+2857,"pre_sel", false,-1, 1,0);
    tracep->declBus(c+2858,"pre_data", false,-1, 31,0);
    tracep->declBus(c+2859,"mem_wr_addr_a", false,-1, 9,0);
    tracep->declBus(c+2860,"mem_wr_addr_b", false,-1, 9,0);
    tracep->declBus(c+2861,"mem_wr_strb_a", false,-1, 3,0);
    tracep->declBus(c+2862,"mem_wr_strb_b", false,-1, 3,0);
    tracep->declBus(c+2863,"mem_wr_data_a", false,-1, 31,0);
    tracep->declBus(c+2864,"mem_wr_data_b", false,-1, 31,0);
    tracep->declBit(c+2865,"cmd_busy", false,-1);
    tracep->declBit(c+128,"new_cmd_request", false,-1);
    tracep->declBit(c+129,"new_data_request", false,-1);
    tracep->declBit(c+130,"new_tx_request", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("GEN_CARD_DETECT ");
    tracep->declBus(c+2866,"raw_card_present", false,-1, 2,0);
    tracep->declBus(c+2867,"card_detect_counter", false,-1, 9,0);
    tracep->declBit(c+2855,"r_card_removed", false,-1);
    tracep->declBit(c+2854,"r_card_present", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_rxframe ");
    tracep->declBus(c+5158,"LGLEN", false,-1, 31,0);
    tracep->declBus(c+5065,"NUMIO", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBus(c+5061,"LGLENW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_DS", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5133,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+85,"i_reset", false,-1);
    tracep->declBit(c+2789,"i_cfg_ds", false,-1);
    tracep->declBit(c+2715,"i_cfg_ddr", false,-1);
    tracep->declBus(c+2791,"i_cfg_width", false,-1, 1,0);
    tracep->declBit(c+2723,"i_rx_en", false,-1);
    tracep->declBit(c+5077,"i_crc_en", false,-1);
    tracep->declBus(c+2815,"i_length", false,-1, 12,0);
    tracep->declBus(c+2729,"i_rx_strb", false,-1, 1,0);
    tracep->declBus(c+2730,"i_rx_data", false,-1, 15,0);
    tracep->declBit(c+5074,"S_ASYNC_VALID", false,-1);
    tracep->declBus(c+5076,"S_ASYNC_DATA", false,-1, 31,0);
    tracep->declBit(c+2816,"o_mem_valid", false,-1);
    tracep->declBus(c+2818,"o_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2817,"o_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2819,"o_mem_data", false,-1, 31,0);
    tracep->declBit(c+2820,"o_done", false,-1);
    tracep->declBit(c+2821,"o_err", false,-1);
    tracep->declBus(c+5116,"WIDTH_1W", false,-1, 1,0);
    tracep->declBus(c+5117,"WIDTH_4W", false,-1, 1,0);
    tracep->declBus(c+5118,"WIDTH_8W", false,-1, 1,0);
    tracep->declBus(c+5069,"NCRC", false,-1, 31,0);
    tracep->declBus(c+5248,"CRC_POLYNOMIAL", false,-1, 15,0);
    tracep->declBus(c+2868,"sync_fill", false,-1, 4,0);
    tracep->declBus(c+2869,"sync_sreg", false,-1, 19,0);
    tracep->declBit(c+2870,"s2_valid", false,-1);
    tracep->declBus(c+2871,"s2_fill", false,-1, 1,0);
    tracep->declBus(c+2872,"s2_data", false,-1, 15,0);
    tracep->declBit(c+2816,"mem_valid", false,-1);
    tracep->declBit(c+2873,"mem_full", false,-1);
    tracep->declBit(c+2874,"rnxt_strb", false,-1);
    tracep->declBus(c+2818,"mem_strb", false,-1, 3,0);
    tracep->declBus(c+2819,"mem_data", false,-1, 31,0);
    tracep->declBus(c+2817,"mem_addr", false,-1, 9,0);
    tracep->declBus(c+2875,"subaddr", false,-1, 1,0);
    tracep->declBus(c+2876,"next_subaddr", false,-1, 1,0);
    tracep->declBus(c+2877,"rnxt_data", false,-1, 7,0);
    tracep->declBit(c+2878,"busy", false,-1);
    tracep->declBit(c+2879,"data_phase", false,-1);
    tracep->declBit(c+2880,"load_crc", false,-1);
    tracep->declBit(c+2881,"pending_crc", false,-1);
    tracep->declBus(c+2882,"rail_count", false,-1, 15,0);
    tracep->declBus(c+2883,"err", false,-1, 7,0);
    tracep->declBus(c+2884,"r_timeout", false,-1, 22,0);
    tracep->declBit(c+2885,"r_watchdog", false,-1);
    tracep->declBit(c+2886,"last_strb", false,-1);
    tracep->declBit(c+2887,"w_done", false,-1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[0] ");
    tracep->declBus(c+2888,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2889,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2890,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[1] ");
    tracep->declBus(c+2891,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2892,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2893,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[2] ");
    tracep->declBus(c+2894,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2895,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2896,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_RAIL_CRC[3] ");
    tracep->declBus(c+2897,"pedge_crc", false,-1, 15,0);
    tracep->declBus(c+2898,"nedge_crc", false,-1, 15,0);
    tracep->declBus(c+2899,"lcl_err", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("u_sdcmd ");
    tracep->declBus(c+5113,"OPT_DS", false,-1, 0,0);
    tracep->declBus(c+5131,"LGTIMEOUT", false,-1, 31,0);
    tracep->declBus(c+5061,"LGLEN", false,-1, 31,0);
    tracep->declBus(c+5114,"MW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+85,"i_reset", false,-1);
    tracep->declBit(c+2789,"i_cfg_ds", false,-1);
    tracep->declBit(c+2900,"i_cfg_dbl", false,-1);
    tracep->declBit(c+2792,"i_ckstb", false,-1);
    tracep->declBit(c+2796,"i_cmd_request", false,-1);
    tracep->declBus(c+2800,"i_cmd_type", false,-1, 1,0);
    tracep->declBus(c+2803,"i_cmd", false,-1, 6,0);
    tracep->declBus(c+2805,"i_arg", false,-1, 31,0);
    tracep->declBit(c+2798,"o_busy", false,-1);
    tracep->declBit(c+2799,"o_done", false,-1);
    tracep->declBit(c+2797,"o_err", false,-1);
    tracep->declBus(c+2801,"o_ercode", false,-1, 1,0);
    tracep->declBit(c+2718,"o_cmd_en", false,-1);
    tracep->declBus(c+2720,"o_cmd_data", false,-1, 1,0);
    tracep->declBus(c+2726,"i_cmd_strb", false,-1, 1,0);
    tracep->declBus(c+2727,"i_cmd_data", false,-1, 1,0);
    tracep->declBit(c+5074,"S_ASYNC_VALID", false,-1);
    tracep->declBus(c+5116,"S_ASYNC_DATA", false,-1, 1,0);
    tracep->declBit(c+2802,"o_cmd_response", false,-1);
    tracep->declBus(c+2804,"o_resp", false,-1, 5,0);
    tracep->declBus(c+2806,"o_arg", false,-1, 31,0);
    tracep->declBit(c+2807,"o_mem_valid", false,-1);
    tracep->declBus(c+5108,"o_mem_strb", false,-1, 3,0);
    tracep->declBus(c+2808,"o_mem_addr", false,-1, 9,0);
    tracep->declBus(c+2809,"o_mem_data", false,-1, 31,0);
    tracep->declBus(c+5116,"R_NONE", false,-1, 1,0);
    tracep->declBus(c+5117,"R_R1", false,-1, 1,0);
    tracep->declBus(c+5118,"R_R2", false,-1, 1,0);
    tracep->declBus(c+5116,"ECODE_TIMEOUT", false,-1, 1,0);
    tracep->declBus(c+5117,"ECODE_OKAY", false,-1, 1,0);
    tracep->declBus(c+5118,"ECODE_BADCRC", false,-1, 1,0);
    tracep->declBus(c+5119,"ECODE_FRAMEERR", false,-1, 1,0);
    tracep->declBus(c+5249,"CRC_POLYNOMIAL", false,-1, 6,0);
    tracep->declBit(c+2718,"active", false,-1);
    tracep->declBus(c+2901,"srcount", false,-1, 5,0);
    tracep->declQuad(c+2902,"tx_sreg", false,-1, 47,0);
    tracep->declBit(c+2904,"waiting_on_response", false,-1);
    tracep->declBit(c+2905,"cfg_ds", false,-1);
    tracep->declBit(c+2906,"cfg_dbl", false,-1);
    tracep->declBit(c+2907,"r_frame_err", false,-1);
    tracep->declBus(c+2908,"cmd_type", false,-1, 1,0);
    tracep->declBus(c+2909,"resp_count", false,-1, 7,0);
    tracep->declBit(c+2910,"frame_err", false,-1);
    tracep->declBit(c+2911,"w_done", false,-1);
    tracep->declBit(c+2912,"crc_err", false,-1);
    tracep->declBit(c+2913,"w_no_response", false,-1);
    tracep->declBus(c+2808,"mem_addr", false,-1, 9,0);
    tracep->declQuad(c+2914,"rx_sreg", false,-1, 39,0);
    tracep->declBit(c+2916,"rx_timeout", false,-1);
    tracep->declBus(c+2917,"rx_timeout_counter", false,-1, 25,0);
    tracep->declBus(c+2918,"crc_fill", false,-1, 6,0);
    tracep->declBit(c+2919,"r_busy", false,-1);
    tracep->declBit(c+2920,"new_data", false,-1);
    tracep->declBit(c+2921,"r_done", false,-1);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_txframe ");
    tracep->declBus(c+5069,"NCRC", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_SERDES", false,-1, 0,0);
    tracep->declBus(c+5248,"CRC_POLYNOMIAL", false,-1, 15,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+85,"i_reset", false,-1);
    tracep->declBus(c+2790,"i_cfg_spd", false,-1, 7,0);
    tracep->declBus(c+2791,"i_cfg_width", false,-1, 1,0);
    tracep->declBit(c+2715,"i_cfg_ddr", false,-1);
    tracep->declBit(c+2810,"i_en", false,-1);
    tracep->declBit(c+2792,"i_ckstb", false,-1);
    tracep->declBit(c+2793,"i_hlfck", false,-1);
    tracep->declBit(c+2922,"S_VALID", false,-1);
    tracep->declBit(c+2812,"S_READY", false,-1);
    tracep->declBus(c+2814,"S_DATA", false,-1, 31,0);
    tracep->declBit(c+2813,"S_LAST", false,-1);
    tracep->declBit(c+2721,"tx_valid", false,-1);
    tracep->declBus(c+2724,"tx_data", false,-1, 31,0);
    tracep->declBus(c+5116,"P_IDLE", false,-1, 1,0);
    tracep->declBus(c+5117,"P_DATA", false,-1, 1,0);
    tracep->declBus(c+5118,"P_CRC", false,-1, 1,0);
    tracep->declBus(c+5119,"P_LAST", false,-1, 1,0);
    tracep->declBus(c+5116,"WIDTH_1W", false,-1, 1,0);
    tracep->declBus(c+5117,"WIDTH_4W", false,-1, 1,0);
    tracep->declBus(c+5118,"WIDTH_8W", false,-1, 1,0);
    tracep->declBus(c+5116,"P_1D", false,-1, 1,0);
    tracep->declBus(c+5117,"P_2D", false,-1, 1,0);
    tracep->declBus(c+5118,"P_4D", false,-1, 1,0);
    tracep->declBit(c+2923,"cfg_ddr", false,-1);
    tracep->declBus(c+2924,"cfg_width", false,-1, 1,0);
    tracep->declBus(c+2925,"cfg_period", false,-1, 1,0);
    tracep->declBit(c+2926,"start_packet", false,-1);
    tracep->declBit(c+2927,"pre_valid", false,-1);
    tracep->declBus(c+2928,"pstate", false,-1, 1,0);
    tracep->declBit(c+2929,"pre_ready", false,-1);
    tracep->declBus(c+2930,"pre_data", false,-1, 31,0);
    tracep->declBus(c+2931,"pre_count", false,-1, 3,0);
    tracep->declBus(c+5250,"ik", false,-1, 31,0);
    tracep->declBus(c+5250,"jk", false,-1, 31,0);
    tracep->declBus(c+2932,"crc_1w_reg", false,-1, 15,0);
    tracep->declBus(c+2933,"di_crc_2w", false,-1, 31,0);
    tracep->declBus(c+2934,"nxt_crc_2w", false,-1, 31,0);
    tracep->declBus(c+2935,"new_crc_2w", false,-1, 31,0);
    tracep->declBus(c+2936,"crc_2w_reg", false,-1, 31,0);
    tracep->declQuad(c+2937,"di_crc_4w", false,-1, 63,0);
    tracep->declQuad(c+2939,"nxt_crc_4w", false,-1, 63,0);
    tracep->declQuad(c+2941,"new_crc_4w", false,-1, 63,0);
    tracep->declQuad(c+2943,"crc_4w_reg", false,-1, 63,0);
    tracep->declArray(c+2945,"di_crc_8w", false,-1, 127,0);
    tracep->declArray(c+2949,"nxt_crc_8w", false,-1, 127,0);
    tracep->declArray(c+2953,"new_crc_8w", false,-1, 127,0);
    tracep->declArray(c+2957,"crc_8w_reg", false,-1, 127,0);
    tracep->declArray(c+2961,"di_crc_8d", false,-1, 255,0);
    tracep->declArray(c+2969,"nxt_crc_8d", false,-1, 255,0);
    tracep->declArray(c+2977,"new_crc_8d", false,-1, 255,0);
    tracep->declArray(c+2985,"crc_8d_reg", false,-1, 255,0);
    tracep->declBit(c+2721,"ck_valid", false,-1);
    tracep->declBus(c+2993,"ck_counts", false,-1, 4,0);
    tracep->declBus(c+2724,"ck_data", false,-1, 31,0);
    tracep->declBus(c+2994,"ck_sreg", false,-1, 31,0);
    tracep->declBit(c+2995,"ck_stop_bit", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("u_wbdown ");
    tracep->declBus(c+5061,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"WIDE_DW", false,-1, 31,0);
    tracep->declBus(c+5114,"SMALL_DW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWLOGIC", false,-1, 0,0);
    tracep->declBus(c+5065,"WIDE_AW", false,-1, 31,0);
    tracep->declBus(c+5063,"SMALL_AW", false,-1, 31,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+4419,"i_wcyc", false,-1);
    tracep->declBit(c+4420,"i_wstb", false,-1);
    tracep->declBit(c+4421,"i_wwe", false,-1);
    tracep->declBus(c+4611,"i_waddr", false,-1, 3,0);
    tracep->declArray(c+4423,"i_wdata", false,-1, 511,0);
    tracep->declQuad(c+4439,"i_wsel", false,-1, 63,0);
    tracep->declBit(c+343,"o_wstall", false,-1);
    tracep->declBit(c+344,"o_wack", false,-1);
    tracep->declArray(c+345,"o_wdata", false,-1, 511,0);
    tracep->declBit(c+4441,"o_werr", false,-1);
    tracep->declBit(c+4486,"o_scyc", false,-1);
    tracep->declBit(c+378,"o_sstb", false,-1);
    tracep->declBit(c+379,"o_swe", false,-1);
    tracep->declBus(c+380,"o_saddr", false,-1, 7,0);
    tracep->declBus(c+381,"o_sdata", false,-1, 31,0);
    tracep->declBus(c+382,"o_ssel", false,-1, 3,0);
    tracep->declBit(c+383,"i_sstall", false,-1);
    tracep->declBit(c+384,"i_sack", false,-1);
    tracep->declBus(c+385,"i_sdata", false,-1, 31,0);
    tracep->declBit(c+4487,"i_serr", false,-1);
    tracep->declBus(c+5065,"WBLSB", false,-1, 31,0);
    tracep->pushNamePrefix("DOWNSIZE ");
    tracep->declBus(c+5154,"LGFIFO", false,-1, 31,0);
    tracep->declBit(c+4486,"r_cyc", false,-1);
    tracep->declBit(c+2996,"r_stb", false,-1);
    tracep->declBit(c+379,"r_we", false,-1);
    tracep->declBit(c+344,"r_ack", false,-1);
    tracep->declBit(c+4441,"r_err", false,-1);
    tracep->declBit(c+2997,"r_first", false,-1);
    tracep->declBus(c+380,"r_addr", false,-1, 7,0);
    tracep->declBit(c+2998,"s_null", false,-1);
    tracep->declBit(c+2999,"s_last", false,-1);
    tracep->declArray(c+3000,"s_data", false,-1, 511,0);
    tracep->declArray(c+345,"r_data", false,-1, 511,0);
    tracep->declArray(c+3016,"nxt_data", false,-1, 511,0);
    tracep->declQuad(c+3032,"s_sel", false,-1, 63,0);
    tracep->declQuad(c+3034,"nxt_sel", false,-1, 63,0);
    tracep->declBus(c+3036,"r_shift", false,-1, 3,0);
    tracep->declBus(c+3037,"fifo_addr", false,-1, 3,0);
    tracep->declBus(c+4612,"i_subaddr", false,-1, 3,0);
    tracep->declBit(c+3038,"fifo_full", false,-1);
    tracep->declBit(c+3039,"fifo_empty", false,-1);
    tracep->declBit(c+3040,"fifo_ack", false,-1);
    tracep->declBus(c+3041,"ign_fifo_fill", false,-1, 5,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("DOWNSIZE ");
    tracep->declBus(c+5250,"subaddr_fn__Vstatic__fnk", false,-1, 31,0);
    tracep->declBus(c+4613,"subaddr_fn__Vstatic__fm", false,-1, 31,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("u_fifo ");
    tracep->declBus(c+5154,"BW", false,-1, 31,0);
    tracep->declBus(c+5154,"LGFLEN", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_ASYNC_READ", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_WRITE_ON_FULL", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_READ_ON_EMPTY", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+131,"i_reset", false,-1);
    tracep->declBit(c+3042,"i_wr", false,-1);
    tracep->declBus(c+3043,"i_data", false,-1, 4,0);
    tracep->declBit(c+3038,"o_full", false,-1);
    tracep->declBus(c+3041,"o_fill", false,-1, 5,0);
    tracep->declBit(c+384,"i_rd", false,-1);
    tracep->declBus(c+3044,"o_data", false,-1, 4,0);
    tracep->declBit(c+3039,"o_empty", false,-1);
    tracep->declBus(c+5114,"FLEN", false,-1, 31,0);
    tracep->declBit(c+3045,"r_full", false,-1);
    tracep->declBit(c+3046,"r_empty", false,-1);
    for (int i = 0; i < 32; ++i) {
        tracep->declBus(c+3047+i*1,"mem", true,(i+0), 4,0);
    }
    tracep->declBus(c+3079,"wr_addr", false,-1, 5,0);
    tracep->declBus(c+3080,"rd_addr", false,-1, 5,0);
    tracep->declBit(c+3081,"w_wr", false,-1);
    tracep->declBit(c+3082,"w_rd", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("wb32_xbar ");
    tracep->declBus(c+5064,"NM", false,-1, 31,0);
    tracep->declBus(c+5158,"NS", false,-1, 31,0);
    tracep->declBus(c+5063,"AW", false,-1, 31,0);
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declArray(c+5256,"SLAVE_ADDR", false,-1, 95,0);
    tracep->declArray(c+5259,"SLAVE_MASK", false,-1, 95,0);
    tracep->declBus(c+5153,"LGMAXBURST", false,-1, 31,0);
    tracep->declBus(c+5076,"OPT_TIMEOUT", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_STARVATION_TIMEOUT", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DBLBUFFER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBus(c+4486,"i_mcyc", false,-1, 0,0);
    tracep->declBus(c+378,"i_mstb", false,-1, 0,0);
    tracep->declBus(c+379,"i_mwe", false,-1, 0,0);
    tracep->declBus(c+380,"i_maddr", false,-1, 7,0);
    tracep->declBus(c+381,"i_mdata", false,-1, 31,0);
    tracep->declBus(c+382,"i_msel", false,-1, 3,0);
    tracep->declBus(c+383,"o_mstall", false,-1, 0,0);
    tracep->declBus(c+384,"o_mack", false,-1, 0,0);
    tracep->declBus(c+385,"o_mdata", false,-1, 31,0);
    tracep->declBus(c+4487,"o_merr", false,-1, 0,0);
    tracep->declBus(c+4614,"o_scyc", false,-1, 11,0);
    tracep->declBus(c+4615,"o_sstb", false,-1, 11,0);
    tracep->declBus(c+4616,"o_swe", false,-1, 11,0);
    tracep->declArray(c+4617,"o_saddr", false,-1, 95,0);
    tracep->declArray(c+4620,"o_sdata", false,-1, 383,0);
    tracep->declQuad(c+4632,"o_ssel", false,-1, 47,0);
    tracep->declBus(c+4413,"i_sstall", false,-1, 11,0);
    tracep->declBus(c+3889,"i_sack", false,-1, 11,0);
    tracep->declArray(c+3890,"i_sdata", false,-1, 383,0);
    tracep->declBus(c+5262,"i_serr", false,-1, 11,0);
    tracep->declBus(c+5076,"TIMEOUT_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5064,"LGNM", false,-1, 31,0);
    tracep->declBus(c+5065,"LGNS", false,-1, 31,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+4634+i*1,"request", true,(i+0), 12,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+8+i*1,"requested", true,(i+0), 11,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3083+i*1,"grant", true,(i+0), 12,0);
    }
    tracep->declBus(c+3084,"mgrant", false,-1, 0,0);
    tracep->declBus(c+4635,"sgrant", false,-1, 11,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3085+i*1,"w_mpending", true,(i+0), 5,0);
    }
    tracep->declBus(c+3086,"mfull", false,-1, 0,0);
    tracep->declBus(c+3087,"mnearfull", false,-1, 0,0);
    tracep->declBus(c+3088,"mempty", false,-1, 0,0);
    tracep->declBus(c+5113,"timed_out", false,-1, 0,0);
    tracep->declBus(c+5064,"NMFULL", false,-1, 31,0);
    tracep->declBus(c+5069,"NSFULL", false,-1, 31,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+4636+i*1,"mindex", true,(i+0), 3,0);
    }
    for (int i = 0; i < 16; ++i) {
        tracep->declBus(c+9+i*1,"sindex", true,(i+0), 0,0);
    }
    tracep->declBus(c+4486,"m_cyc", false,-1, 0,0);
    tracep->declBus(c+4637,"m_stb", false,-1, 0,0);
    tracep->declBus(c+4638,"m_we", false,-1, 0,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+4639+i*1,"m_addr", true,(i+0), 7,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+4640+i*1,"m_data", true,(i+0), 31,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+4641+i*1,"m_sel", true,(i+0), 3,0);
    }
    tracep->declBus(c+4881,"m_stall", false,-1, 0,0);
    tracep->declBus(c+4882,"s_stall", false,-1, 15,0);
    for (int i = 0; i < 16; ++i) {
        tracep->declBus(c+3902+i*1,"s_data", true,(i+0), 31,0);
    }
    tracep->declBus(c+5042,"s_ack", false,-1, 15,0);
    tracep->declBus(c+5263,"s_err", false,-1, 15,0);
    tracep->declBus(c+4642,"dcd_stb", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_BUFFER_DECODER", false,-1, 0,0);
    tracep->declBus(c+3089,"iN", false,-1, 31,0);
    tracep->declBus(c+5043,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("ARBITRATE_REQUESTS[0] ");
    tracep->declBus(c+4643,"regrant", false,-1, 12,0);
    tracep->declBus(c+5044,"reindex", false,-1, 3,0);
    tracep->declBit(c+4644,"stay_on_channel", false,-1);
    tracep->declBit(c+4645,"requested_channel_is_available", false,-1);
    tracep->pushNamePrefix("MINDEX_MULTIPLE_SLAVES ");
    tracep->declBus(c+4646,"r_mindex", false,-1, 3,0);
    tracep->declBus(c+4643,"r_regrant", false,-1, 12,0);
    tracep->declBus(c+5044,"r_reindex", false,-1, 3,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("COUNT_PENDING_TRANSACTIONS[0] ");
    tracep->declBus(c+3090,"lclpending", false,-1, 5,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("DECODE_REQUEST[0] ");
    tracep->declBit(c+132,"skd_stb", false,-1);
    tracep->declBit(c+4883,"skd_stall", false,-1);
    tracep->declBit(c+4647,"skd_we", false,-1);
    tracep->declBus(c+4648,"skd_addr", false,-1, 7,0);
    tracep->declBus(c+4649,"skd_data", false,-1, 31,0);
    tracep->declBus(c+4650,"skd_sel", false,-1, 3,0);
    tracep->declBus(c+3091,"decoded", false,-1, 12,0);
    tracep->declBit(c+3092,"iskd_ready", false,-1);
    tracep->pushNamePrefix("adcd ");
    tracep->declBus(c+5158,"NS", false,-1, 31,0);
    tracep->declBus(c+5063,"AW", false,-1, 31,0);
    tracep->declBus(c+5264,"DW", false,-1, 31,0);
    tracep->declArray(c+5256,"SLAVE_ADDR", false,-1, 95,0);
    tracep->declArray(c+5259,"SLAVE_MASK", false,-1, 95,0);
    tracep->declBus(c+5201,"ACCESS_ALLOWED", false,-1, 11,0);
    tracep->declBus(c+5070,"OPT_REGISTERED", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+133,"i_valid", false,-1);
    tracep->declBit(c+4883,"o_stall", false,-1);
    tracep->declBus(c+4648,"i_addr", false,-1, 7,0);
    tracep->declQuad(c+4651,"i_data", false,-1, 36,0);
    tracep->declBit(c+4642,"o_valid", false,-1);
    tracep->declBit(c+4884,"i_stall", false,-1);
    tracep->declBus(c+3091,"o_decode", false,-1, 12,0);
    tracep->declBus(c+3093,"o_addr", false,-1, 7,0);
    tracep->declQuad(c+4653,"o_data", false,-1, 36,0);
    tracep->declBus(c+5070,"OPT_NONESEL", false,-1, 0,0);
    tracep->declBus(c+134,"request", false,-1, 12,0);
    tracep->declBus(c+4655,"prerequest", false,-1, 11,0);
    tracep->declBus(c+25,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("NO_DEFAULT_REQUEST ");
    tracep->declBus(c+135,"r_request", false,-1, 11,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_NONESEL_REQUEST ");
    tracep->declBit(c+136,"r_request_NS", false,-1);
    tracep->declBit(c+137,"r_none_sel", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("iskid ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5265,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+138,"i_reset", false,-1);
    tracep->declBit(c+378,"i_valid", false,-1);
    tracep->declBit(c+3092,"o_ready", false,-1);
    tracep->declQuad(c+3094,"i_data", false,-1, 44,0);
    tracep->declBit(c+132,"o_valid", false,-1);
    tracep->declBit(c+4885,"i_ready", false,-1);
    tracep->declQuad(c+4656,"o_data", false,-1, 44,0);
    tracep->declQuad(c+3096,"w_data", false,-1, 44,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+383,"r_valid", false,-1);
    tracep->declQuad(c+3096,"r_data", false,-1, 44,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DOUBLE_BUFFERRED_STALL ");
    tracep->declBus(c+384,"r_mack", false,-1, 0,0);
    tracep->declBus(c+4487,"r_merr", false,-1, 0,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[0] ");
    tracep->declBit(c+139,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[10] ");
    tracep->declBit(c+140,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[11] ");
    tracep->declBit(c+141,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[1] ");
    tracep->declBit(c+142,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[2] ");
    tracep->declBit(c+143,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[3] ");
    tracep->declBit(c+144,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[4] ");
    tracep->declBit(c+145,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[5] ");
    tracep->declBit(c+146,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[6] ");
    tracep->declBit(c+147,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[7] ");
    tracep->declBit(c+148,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[8] ");
    tracep->declBit(c+149,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[9] ");
    tracep->declBit(c+150,"drop_sgrant", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("wbu_arbiter_upsz ");
    tracep->declBus(c+5199,"ADDRESS_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5111,"WIDE_DW", false,-1, 31,0);
    tracep->declBus(c+5114,"SMALL_DW", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_LITTLE_ENDIAN", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+419,"i_scyc", false,-1);
    tracep->declBit(c+420,"i_sstb", false,-1);
    tracep->declBit(c+421,"i_swe", false,-1);
    tracep->declBus(c+3098,"i_saddr", false,-1, 25,0);
    tracep->declBus(c+423,"i_sdata", false,-1, 31,0);
    tracep->declBus(c+424,"i_ssel", false,-1, 3,0);
    tracep->declBit(c+425,"o_sstall", false,-1);
    tracep->declBit(c+426,"o_sack", false,-1);
    tracep->declBus(c+428,"o_sdata", false,-1, 31,0);
    tracep->declBit(c+427,"o_serr", false,-1);
    tracep->declBit(c+302,"o_wcyc", false,-1);
    tracep->declBit(c+303,"o_wstb", false,-1);
    tracep->declBit(c+304,"o_wwe", false,-1);
    tracep->declBus(c+305,"o_waddr", false,-1, 21,0);
    tracep->declArray(c+306,"o_wdata", false,-1, 511,0);
    tracep->declQuad(c+322,"o_wsel", false,-1, 63,0);
    tracep->declBit(c+324,"i_wstall", false,-1);
    tracep->declBit(c+325,"i_wack", false,-1);
    tracep->declArray(c+327,"i_wdata", false,-1, 511,0);
    tracep->declBit(c+326,"i_werr", false,-1);
    tracep->pushNamePrefix("UPSIZE ");
    tracep->declBus(c+5154,"LGFIFO", false,-1, 31,0);
    tracep->declBit(c+302,"r_cyc", false,-1);
    tracep->declBit(c+3099,"r_stb", false,-1);
    tracep->declBit(c+304,"r_we", false,-1);
    tracep->declBit(c+426,"r_ack", false,-1);
    tracep->declBit(c+427,"r_err", false,-1);
    tracep->declBus(c+305,"r_addr", false,-1, 21,0);
    tracep->declArray(c+306,"r_data", false,-1, 511,0);
    tracep->declArray(c+3100,"rtn_data", false,-1, 511,0);
    tracep->declQuad(c+322,"r_sel", false,-1, 63,0);
    tracep->declBus(c+3116,"r_shift", false,-1, 3,0);
    tracep->declBit(c+3117,"fifo_full", false,-1);
    tracep->declBit(c+3118,"ign_fifo_empty", false,-1);
    tracep->declBus(c+3119,"ign_fifo_fill", false,-1, 5,0);
    tracep->declBus(c+3120,"w_shift", false,-1, 3,0);
    tracep->declBus(c+3121,"fifo_shift", false,-1, 3,0);
    tracep->declArray(c+3122,"w_data", false,-1, 511,0);
    tracep->declQuad(c+3138,"w_sel", false,-1, 63,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("u_fifo ");
    tracep->declBus(c+5065,"BW", false,-1, 31,0);
    tracep->declBus(c+5154,"LGFLEN", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_ASYNC_READ", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_WRITE_ON_FULL", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_READ_ON_EMPTY", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+86,"i_reset", false,-1);
    tracep->declBit(c+3140,"i_wr", false,-1);
    tracep->declBus(c+3116,"i_data", false,-1, 3,0);
    tracep->declBit(c+3117,"o_full", false,-1);
    tracep->declBus(c+3119,"o_fill", false,-1, 5,0);
    tracep->declBit(c+325,"i_rd", false,-1);
    tracep->declBus(c+3121,"o_data", false,-1, 3,0);
    tracep->declBit(c+3118,"o_empty", false,-1);
    tracep->declBus(c+5114,"FLEN", false,-1, 31,0);
    tracep->declBit(c+3117,"r_full", false,-1);
    tracep->declBit(c+3118,"r_empty", false,-1);
    for (int i = 0; i < 32; ++i) {
        tracep->declBus(c+3141+i*1,"mem", true,(i+0), 3,0);
    }
    tracep->declBus(c+3173,"wr_addr", false,-1, 5,0);
    tracep->declBus(c+3174,"rd_addr", false,-1, 5,0);
    tracep->declBit(c+3175,"w_wr", false,-1);
    tracep->declBit(c+3176,"w_rd", false,-1);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("wbu_xbar ");
    tracep->declBus(c+5064,"NM", false,-1, 31,0);
    tracep->declBus(c+5075,"NS", false,-1, 31,0);
    tracep->declBus(c+5130,"AW", false,-1, 31,0);
    tracep->declBus(c+5114,"DW", false,-1, 31,0);
    tracep->declQuad(c+5266,"SLAVE_ADDR", false,-1, 53,0);
    tracep->declQuad(c+5268,"SLAVE_MASK", false,-1, 53,0);
    tracep->declBus(c+5153,"LGMAXBURST", false,-1, 31,0);
    tracep->declBus(c+5076,"OPT_TIMEOUT", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_STARVATION_TIMEOUT", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DBLBUFFER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBus(c+410,"i_mcyc", false,-1, 0,0);
    tracep->declBus(c+411,"i_mstb", false,-1, 0,0);
    tracep->declBus(c+412,"i_mwe", false,-1, 0,0);
    tracep->declBus(c+413,"i_maddr", false,-1, 26,0);
    tracep->declBus(c+414,"i_mdata", false,-1, 31,0);
    tracep->declBus(c+5108,"i_msel", false,-1, 3,0);
    tracep->declBus(c+415,"o_mstall", false,-1, 0,0);
    tracep->declBus(c+416,"o_mack", false,-1, 0,0);
    tracep->declBus(c+418,"o_mdata", false,-1, 31,0);
    tracep->declBus(c+417,"o_merr", false,-1, 0,0);
    tracep->declBus(c+3177,"o_scyc", false,-1, 1,0);
    tracep->declBus(c+3178,"o_sstb", false,-1, 1,0);
    tracep->declBus(c+3179,"o_swe", false,-1, 1,0);
    tracep->declQuad(c+3180,"o_saddr", false,-1, 53,0);
    tracep->declQuad(c+3182,"o_sdata", false,-1, 63,0);
    tracep->declBus(c+3184,"o_ssel", false,-1, 7,0);
    tracep->declBus(c+5045,"i_sstall", false,-1, 1,0);
    tracep->declBus(c+5046,"i_sack", false,-1, 1,0);
    tracep->declQuad(c+3185,"i_sdata", false,-1, 63,0);
    tracep->declBus(c+3187,"i_serr", false,-1, 1,0);
    tracep->declBus(c+5076,"TIMEOUT_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5064,"LGNM", false,-1, 31,0);
    tracep->declBus(c+5075,"LGNS", false,-1, 31,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3188+i*1,"request", true,(i+0), 2,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+26+i*1,"requested", true,(i+0), 1,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3189+i*1,"grant", true,(i+0), 2,0);
    }
    tracep->declBus(c+3190,"mgrant", false,-1, 0,0);
    tracep->declBus(c+3191,"sgrant", false,-1, 1,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3192+i*1,"w_mpending", true,(i+0), 5,0);
    }
    tracep->declBus(c+3193,"mfull", false,-1, 0,0);
    tracep->declBus(c+3194,"mnearfull", false,-1, 0,0);
    tracep->declBus(c+3195,"mempty", false,-1, 0,0);
    tracep->declBus(c+5113,"timed_out", false,-1, 0,0);
    tracep->declBus(c+5064,"NMFULL", false,-1, 31,0);
    tracep->declBus(c+5065,"NSFULL", false,-1, 31,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+4658+i*1,"mindex", true,(i+0), 1,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+27+i*1,"sindex", true,(i+0), 0,0);
    }
    tracep->declBus(c+410,"m_cyc", false,-1, 0,0);
    tracep->declBus(c+3196,"m_stb", false,-1, 0,0);
    tracep->declBus(c+3197,"m_we", false,-1, 0,0);
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3198+i*1,"m_addr", true,(i+0), 26,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3199+i*1,"m_data", true,(i+0), 31,0);
    }
    for (int i = 0; i < 1; ++i) {
        tracep->declBus(c+3200+i*1,"m_sel", true,(i+0), 3,0);
    }
    tracep->declBus(c+151,"m_stall", false,-1, 0,0);
    tracep->declBus(c+87,"s_stall", false,-1, 3,0);
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+3201+i*1,"s_data", true,(i+0), 31,0);
    }
    tracep->declBus(c+5047,"s_ack", false,-1, 3,0);
    tracep->declBus(c+3205,"s_err", false,-1, 3,0);
    tracep->declBus(c+3206,"dcd_stb", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_BUFFER_DECODER", false,-1, 0,0);
    tracep->declBus(c+3207,"iN", false,-1, 31,0);
    tracep->declBus(c+5048,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("ARBITRATE_REQUESTS[0] ");
    tracep->declBus(c+4659,"regrant", false,-1, 2,0);
    tracep->declBus(c+5049,"reindex", false,-1, 1,0);
    tracep->declBit(c+3208,"stay_on_channel", false,-1);
    tracep->declBit(c+3209,"requested_channel_is_available", false,-1);
    tracep->pushNamePrefix("MINDEX_MULTIPLE_SLAVES ");
    tracep->declBus(c+4660,"r_mindex", false,-1, 1,0);
    tracep->declBus(c+4659,"r_regrant", false,-1, 2,0);
    tracep->declBus(c+5049,"r_reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("COUNT_PENDING_TRANSACTIONS[0] ");
    tracep->declBus(c+3210,"lclpending", false,-1, 5,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("DECODE_REQUEST[0] ");
    tracep->declBit(c+88,"skd_stb", false,-1);
    tracep->declBit(c+152,"skd_stall", false,-1);
    tracep->declBit(c+3211,"skd_we", false,-1);
    tracep->declBus(c+3212,"skd_addr", false,-1, 26,0);
    tracep->declBus(c+3213,"skd_data", false,-1, 31,0);
    tracep->declBus(c+3214,"skd_sel", false,-1, 3,0);
    tracep->declBus(c+3215,"decoded", false,-1, 2,0);
    tracep->declBit(c+3216,"iskd_ready", false,-1);
    tracep->pushNamePrefix("adcd ");
    tracep->declBus(c+5075,"NS", false,-1, 31,0);
    tracep->declBus(c+5130,"AW", false,-1, 31,0);
    tracep->declBus(c+5264,"DW", false,-1, 31,0);
    tracep->declQuad(c+5266,"SLAVE_ADDR", false,-1, 53,0);
    tracep->declQuad(c+5268,"SLAVE_MASK", false,-1, 53,0);
    tracep->declBus(c+5119,"ACCESS_ALLOWED", false,-1, 1,0);
    tracep->declBus(c+5070,"OPT_REGISTERED", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+89,"i_valid", false,-1);
    tracep->declBit(c+152,"o_stall", false,-1);
    tracep->declBus(c+3212,"i_addr", false,-1, 26,0);
    tracep->declQuad(c+3217,"i_data", false,-1, 36,0);
    tracep->declBit(c+3206,"o_valid", false,-1);
    tracep->declBit(c+153,"i_stall", false,-1);
    tracep->declBus(c+3215,"o_decode", false,-1, 2,0);
    tracep->declBus(c+3219,"o_addr", false,-1, 26,0);
    tracep->declQuad(c+3220,"o_data", false,-1, 36,0);
    tracep->declBus(c+5070,"OPT_NONESEL", false,-1, 0,0);
    tracep->declBus(c+90,"request", false,-1, 2,0);
    tracep->declBus(c+3222,"prerequest", false,-1, 1,0);
    tracep->declBus(c+31,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("NO_DEFAULT_REQUEST ");
    tracep->declBus(c+91,"r_request", false,-1, 1,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_NONESEL_REQUEST ");
    tracep->declBit(c+92,"r_request_NS", false,-1);
    tracep->declBit(c+93,"r_none_sel", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("iskid ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5120,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+94,"i_reset", false,-1);
    tracep->declBit(c+411,"i_valid", false,-1);
    tracep->declBit(c+3216,"o_ready", false,-1);
    tracep->declQuad(c+3223,"i_data", false,-1, 63,0);
    tracep->declBit(c+88,"o_valid", false,-1);
    tracep->declBit(c+154,"i_ready", false,-1);
    tracep->declQuad(c+3225,"o_data", false,-1, 63,0);
    tracep->declQuad(c+3227,"w_data", false,-1, 63,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+415,"r_valid", false,-1);
    tracep->declQuad(c+3227,"r_data", false,-1, 63,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DOUBLE_BUFFERRED_STALL ");
    tracep->declBus(c+416,"r_mack", false,-1, 0,0);
    tracep->declBus(c+417,"r_merr", false,-1, 0,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[0] ");
    tracep->declBit(c+95,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[1] ");
    tracep->declBit(c+96,"drop_sgrant", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("wbwide_xbar ");
    tracep->declBus(c+5065,"NM", false,-1, 31,0);
    tracep->declBus(c+5062,"NS", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5111,"DW", false,-1, 31,0);
    tracep->declArray(c+5270,"SLAVE_ADDR", false,-1, 65,0);
    tracep->declArray(c+5273,"SLAVE_MASK", false,-1, 65,0);
    tracep->declBus(c+5153,"LGMAXBURST", false,-1, 31,0);
    tracep->declBus(c+5076,"OPT_TIMEOUT", false,-1, 31,0);
    tracep->declBus(c+5113,"OPT_STARVATION_TIMEOUT", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_DBLBUFFER", false,-1, 0,0);
    tracep->declBus(c+5070,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBus(c+4661,"i_mcyc", false,-1, 3,0);
    tracep->declBus(c+3229,"i_mstb", false,-1, 3,0);
    tracep->declBus(c+3230,"i_mwe", false,-1, 3,0);
    tracep->declArray(c+3231,"i_maddr", false,-1, 87,0);
    tracep->declArray(c+3234,"i_mdata", false,-1, 2047,0);
    tracep->declArray(c+3298,"i_msel", false,-1, 255,0);
    tracep->declBus(c+3306,"o_mstall", false,-1, 3,0);
    tracep->declBus(c+3307,"o_mack", false,-1, 3,0);
    tracep->declArray(c+3308,"o_mdata", false,-1, 2047,0);
    tracep->declBus(c+3372,"o_merr", false,-1, 3,0);
    tracep->declBus(c+4662,"o_scyc", false,-1, 2,0);
    tracep->declBus(c+4663,"o_sstb", false,-1, 2,0);
    tracep->declBus(c+4664,"o_swe", false,-1, 2,0);
    tracep->declArray(c+4665,"o_saddr", false,-1, 65,0);
    tracep->declArray(c+4668,"o_sdata", false,-1, 1535,0);
    tracep->declArray(c+4716,"o_ssel", false,-1, 191,0);
    tracep->declBus(c+3918,"i_sstall", false,-1, 2,0);
    tracep->declBus(c+3919,"i_sack", false,-1, 2,0);
    tracep->declArray(c+3920,"i_sdata", false,-1, 1535,0);
    tracep->declBus(c+4722,"i_serr", false,-1, 2,0);
    tracep->declBus(c+5076,"TIMEOUT_WIDTH", false,-1, 31,0);
    tracep->declBus(c+5075,"LGNM", false,-1, 31,0);
    tracep->declBus(c+5075,"LGNS", false,-1, 31,0);
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+3373+i*1,"request", true,(i+0), 3,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+3377+i*1,"requested", true,(i+0), 2,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+3381+i*1,"grant", true,(i+0), 3,0);
    }
    tracep->declBus(c+3385,"mgrant", false,-1, 3,0);
    tracep->declBus(c+4723,"sgrant", false,-1, 2,0);
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+3386+i*1,"w_mpending", true,(i+0), 5,0);
    }
    tracep->declBus(c+3390,"mfull", false,-1, 3,0);
    tracep->declBus(c+3391,"mnearfull", false,-1, 3,0);
    tracep->declBus(c+3392,"mempty", false,-1, 3,0);
    tracep->declBus(c+5122,"timed_out", false,-1, 3,0);
    tracep->declBus(c+5065,"NMFULL", false,-1, 31,0);
    tracep->declBus(c+5065,"NSFULL", false,-1, 31,0);
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+4724+i*1,"mindex", true,(i+0), 1,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+4728+i*1,"sindex", true,(i+0), 1,0);
    }
    tracep->declBus(c+4661,"m_cyc", false,-1, 3,0);
    tracep->declBus(c+3393,"m_stb", false,-1, 3,0);
    tracep->declBus(c+4732,"m_we", false,-1, 3,0);
    for (int i = 0; i < 4; ++i) {
        tracep->declBus(c+4733+i*1,"m_addr", true,(i+0), 21,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declArray(c+4737+i*16,"m_data", true,(i+0), 511,0);
    }
    for (int i = 0; i < 4; ++i) {
        tracep->declQuad(c+4801+i*2,"m_sel", true,(i+0), 63,0);
    }
    tracep->declBus(c+4886,"m_stall", false,-1, 3,0);
    tracep->declBus(c+4887,"s_stall", false,-1, 3,0);
    for (int i = 0; i < 4; ++i) {
        tracep->declArray(c+3968+i*16,"s_data", true,(i+0), 511,0);
    }
    tracep->declBus(c+4888,"s_ack", false,-1, 3,0);
    tracep->declBus(c+4809,"s_err", false,-1, 3,0);
    tracep->declBus(c+3394,"dcd_stb", false,-1, 3,0);
    tracep->declBus(c+5070,"OPT_BUFFER_DECODER", false,-1, 0,0);
    tracep->declBus(c+5050,"iN", false,-1, 31,0);
    tracep->declBus(c+5051,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("ARBITRATE_REQUESTS[0] ");
    tracep->declBus(c+4810,"regrant", false,-1, 3,0);
    tracep->declBus(c+5052,"reindex", false,-1, 1,0);
    tracep->declBit(c+3395,"stay_on_channel", false,-1);
    tracep->declBit(c+4811,"requested_channel_is_available", false,-1);
    tracep->pushNamePrefix("MINDEX_MULTIPLE_SLAVES ");
    tracep->declBus(c+4812,"r_mindex", false,-1, 1,0);
    tracep->declBus(c+4810,"r_regrant", false,-1, 3,0);
    tracep->declBus(c+5052,"r_reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("ARBITRATE_REQUESTS[1] ");
    tracep->declBus(c+4813,"regrant", false,-1, 3,0);
    tracep->declBus(c+5053,"reindex", false,-1, 1,0);
    tracep->declBit(c+3396,"stay_on_channel", false,-1);
    tracep->declBit(c+4814,"requested_channel_is_available", false,-1);
    tracep->pushNamePrefix("MINDEX_MULTIPLE_SLAVES ");
    tracep->declBus(c+4815,"r_mindex", false,-1, 1,0);
    tracep->declBus(c+4813,"r_regrant", false,-1, 3,0);
    tracep->declBus(c+5053,"r_reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("ARBITRATE_REQUESTS[2] ");
    tracep->declBus(c+4816,"regrant", false,-1, 3,0);
    tracep->declBus(c+5054,"reindex", false,-1, 1,0);
    tracep->declBit(c+3397,"stay_on_channel", false,-1);
    tracep->declBit(c+4817,"requested_channel_is_available", false,-1);
    tracep->pushNamePrefix("MINDEX_MULTIPLE_SLAVES ");
    tracep->declBus(c+4818,"r_mindex", false,-1, 1,0);
    tracep->declBus(c+4816,"r_regrant", false,-1, 3,0);
    tracep->declBus(c+5054,"r_reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("ARBITRATE_REQUESTS[3] ");
    tracep->declBus(c+4819,"regrant", false,-1, 3,0);
    tracep->declBus(c+5055,"reindex", false,-1, 1,0);
    tracep->declBit(c+3398,"stay_on_channel", false,-1);
    tracep->declBit(c+4820,"requested_channel_is_available", false,-1);
    tracep->pushNamePrefix("MINDEX_MULTIPLE_SLAVES ");
    tracep->declBus(c+4821,"r_mindex", false,-1, 1,0);
    tracep->declBus(c+4819,"r_regrant", false,-1, 3,0);
    tracep->declBus(c+5055,"r_reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("COUNT_PENDING_TRANSACTIONS[0] ");
    tracep->declBus(c+3399,"lclpending", false,-1, 5,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("COUNT_PENDING_TRANSACTIONS[1] ");
    tracep->declBus(c+3400,"lclpending", false,-1, 5,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("COUNT_PENDING_TRANSACTIONS[2] ");
    tracep->declBus(c+3401,"lclpending", false,-1, 5,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("COUNT_PENDING_TRANSACTIONS[3] ");
    tracep->declBus(c+3402,"lclpending", false,-1, 5,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("DECODE_REQUEST[0] ");
    tracep->declBit(c+97,"skd_stb", false,-1);
    tracep->declBit(c+4889,"skd_stall", false,-1);
    tracep->declBit(c+3403,"skd_we", false,-1);
    tracep->declBus(c+3404,"skd_addr", false,-1, 21,0);
    tracep->declArray(c+3405,"skd_data", false,-1, 511,0);
    tracep->declQuad(c+3421,"skd_sel", false,-1, 63,0);
    tracep->declBus(c+3423,"decoded", false,-1, 3,0);
    tracep->declBit(c+3424,"iskd_ready", false,-1);
    tracep->pushNamePrefix("adcd ");
    tracep->declBus(c+5062,"NS", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5276,"DW", false,-1, 31,0);
    tracep->declArray(c+5270,"SLAVE_ADDR", false,-1, 65,0);
    tracep->declArray(c+5273,"SLAVE_MASK", false,-1, 65,0);
    tracep->declBus(c+5210,"ACCESS_ALLOWED", false,-1, 2,0);
    tracep->declBus(c+5070,"OPT_REGISTERED", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+98,"i_valid", false,-1);
    tracep->declBit(c+4889,"o_stall", false,-1);
    tracep->declBus(c+3404,"i_addr", false,-1, 21,0);
    tracep->declArray(c+3425,"i_data", false,-1, 576,0);
    tracep->declBit(c+3444,"o_valid", false,-1);
    tracep->declBit(c+4890,"i_stall", false,-1);
    tracep->declBus(c+3423,"o_decode", false,-1, 3,0);
    tracep->declBus(c+3445,"o_addr", false,-1, 21,0);
    tracep->declArray(c+3446,"o_data", false,-1, 576,0);
    tracep->declBus(c+5070,"OPT_NONESEL", false,-1, 0,0);
    tracep->declBus(c+99,"request", false,-1, 3,0);
    tracep->declBus(c+3465,"prerequest", false,-1, 2,0);
    tracep->declBus(c+32,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("NO_DEFAULT_REQUEST ");
    tracep->declBus(c+100,"r_request", false,-1, 2,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_NONESEL_REQUEST ");
    tracep->declBit(c+101,"r_request_NS", false,-1);
    tracep->declBit(c+102,"r_none_sel", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("iskid ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5277,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+103,"i_reset", false,-1);
    tracep->declBit(c+200,"i_valid", false,-1);
    tracep->declBit(c+3424,"o_ready", false,-1);
    tracep->declArray(c+3466,"i_data", false,-1, 598,0);
    tracep->declBit(c+97,"o_valid", false,-1);
    tracep->declBit(c+4891,"i_ready", false,-1);
    tracep->declArray(c+3485,"o_data", false,-1, 598,0);
    tracep->declArray(c+3504,"w_data", false,-1, 598,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+3523,"r_valid", false,-1);
    tracep->declArray(c+3504,"r_data", false,-1, 598,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DECODE_REQUEST[1] ");
    tracep->declBit(c+104,"skd_stb", false,-1);
    tracep->declBit(c+4892,"skd_stall", false,-1);
    tracep->declBit(c+3524,"skd_we", false,-1);
    tracep->declBus(c+3525,"skd_addr", false,-1, 21,0);
    tracep->declArray(c+3526,"skd_data", false,-1, 511,0);
    tracep->declQuad(c+3542,"skd_sel", false,-1, 63,0);
    tracep->declBus(c+3544,"decoded", false,-1, 3,0);
    tracep->declBit(c+3545,"iskd_ready", false,-1);
    tracep->pushNamePrefix("adcd ");
    tracep->declBus(c+5062,"NS", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5276,"DW", false,-1, 31,0);
    tracep->declArray(c+5270,"SLAVE_ADDR", false,-1, 65,0);
    tracep->declArray(c+5273,"SLAVE_MASK", false,-1, 65,0);
    tracep->declBus(c+5210,"ACCESS_ALLOWED", false,-1, 2,0);
    tracep->declBus(c+5070,"OPT_REGISTERED", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+105,"i_valid", false,-1);
    tracep->declBit(c+4892,"o_stall", false,-1);
    tracep->declBus(c+3525,"i_addr", false,-1, 21,0);
    tracep->declArray(c+3546,"i_data", false,-1, 576,0);
    tracep->declBit(c+3565,"o_valid", false,-1);
    tracep->declBit(c+4893,"i_stall", false,-1);
    tracep->declBus(c+3544,"o_decode", false,-1, 3,0);
    tracep->declBus(c+3566,"o_addr", false,-1, 21,0);
    tracep->declArray(c+3567,"o_data", false,-1, 576,0);
    tracep->declBus(c+5070,"OPT_NONESEL", false,-1, 0,0);
    tracep->declBus(c+106,"request", false,-1, 3,0);
    tracep->declBus(c+3586,"prerequest", false,-1, 2,0);
    tracep->declBus(c+33,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("NO_DEFAULT_REQUEST ");
    tracep->declBus(c+107,"r_request", false,-1, 2,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_NONESEL_REQUEST ");
    tracep->declBit(c+108,"r_request_NS", false,-1);
    tracep->declBit(c+109,"r_none_sel", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("iskid ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5277,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+110,"i_reset", false,-1);
    tracep->declBit(c+240,"i_valid", false,-1);
    tracep->declBit(c+3545,"o_ready", false,-1);
    tracep->declArray(c+3587,"i_data", false,-1, 598,0);
    tracep->declBit(c+104,"o_valid", false,-1);
    tracep->declBit(c+4894,"i_ready", false,-1);
    tracep->declArray(c+3606,"o_data", false,-1, 598,0);
    tracep->declArray(c+3625,"w_data", false,-1, 598,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+3644,"r_valid", false,-1);
    tracep->declArray(c+3625,"r_data", false,-1, 598,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DECODE_REQUEST[2] ");
    tracep->declBit(c+111,"skd_stb", false,-1);
    tracep->declBit(c+4895,"skd_stall", false,-1);
    tracep->declBit(c+3645,"skd_we", false,-1);
    tracep->declBus(c+3646,"skd_addr", false,-1, 21,0);
    tracep->declArray(c+3647,"skd_data", false,-1, 511,0);
    tracep->declQuad(c+3663,"skd_sel", false,-1, 63,0);
    tracep->declBus(c+3665,"decoded", false,-1, 3,0);
    tracep->declBit(c+3666,"iskd_ready", false,-1);
    tracep->pushNamePrefix("adcd ");
    tracep->declBus(c+5062,"NS", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5276,"DW", false,-1, 31,0);
    tracep->declArray(c+5270,"SLAVE_ADDR", false,-1, 65,0);
    tracep->declArray(c+5273,"SLAVE_MASK", false,-1, 65,0);
    tracep->declBus(c+5210,"ACCESS_ALLOWED", false,-1, 2,0);
    tracep->declBus(c+5070,"OPT_REGISTERED", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+112,"i_valid", false,-1);
    tracep->declBit(c+4895,"o_stall", false,-1);
    tracep->declBus(c+3646,"i_addr", false,-1, 21,0);
    tracep->declArray(c+3667,"i_data", false,-1, 576,0);
    tracep->declBit(c+3686,"o_valid", false,-1);
    tracep->declBit(c+4896,"i_stall", false,-1);
    tracep->declBus(c+3665,"o_decode", false,-1, 3,0);
    tracep->declBus(c+3687,"o_addr", false,-1, 21,0);
    tracep->declArray(c+3688,"o_data", false,-1, 576,0);
    tracep->declBus(c+5070,"OPT_NONESEL", false,-1, 0,0);
    tracep->declBus(c+113,"request", false,-1, 3,0);
    tracep->declBus(c+3707,"prerequest", false,-1, 2,0);
    tracep->declBus(c+34,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("NO_DEFAULT_REQUEST ");
    tracep->declBus(c+114,"r_request", false,-1, 2,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_NONESEL_REQUEST ");
    tracep->declBit(c+115,"r_request_NS", false,-1);
    tracep->declBit(c+116,"r_none_sel", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("iskid ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5277,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+117,"i_reset", false,-1);
    tracep->declBit(c+262,"i_valid", false,-1);
    tracep->declBit(c+3666,"o_ready", false,-1);
    tracep->declArray(c+3708,"i_data", false,-1, 598,0);
    tracep->declBit(c+111,"o_valid", false,-1);
    tracep->declBit(c+4897,"i_ready", false,-1);
    tracep->declArray(c+3727,"o_data", false,-1, 598,0);
    tracep->declArray(c+3746,"w_data", false,-1, 598,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+3765,"r_valid", false,-1);
    tracep->declArray(c+3746,"r_data", false,-1, 598,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DECODE_REQUEST[3] ");
    tracep->declBit(c+118,"skd_stb", false,-1);
    tracep->declBit(c+4898,"skd_stall", false,-1);
    tracep->declBit(c+3766,"skd_we", false,-1);
    tracep->declBus(c+3767,"skd_addr", false,-1, 21,0);
    tracep->declArray(c+3768,"skd_data", false,-1, 511,0);
    tracep->declQuad(c+3784,"skd_sel", false,-1, 63,0);
    tracep->declBus(c+3786,"decoded", false,-1, 3,0);
    tracep->declBit(c+3787,"iskd_ready", false,-1);
    tracep->pushNamePrefix("adcd ");
    tracep->declBus(c+5062,"NS", false,-1, 31,0);
    tracep->declBus(c+5068,"AW", false,-1, 31,0);
    tracep->declBus(c+5276,"DW", false,-1, 31,0);
    tracep->declArray(c+5270,"SLAVE_ADDR", false,-1, 65,0);
    tracep->declArray(c+5273,"SLAVE_MASK", false,-1, 65,0);
    tracep->declBus(c+5210,"ACCESS_ALLOWED", false,-1, 2,0);
    tracep->declBus(c+5070,"OPT_REGISTERED", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+4902,"i_reset", false,-1);
    tracep->declBit(c+119,"i_valid", false,-1);
    tracep->declBit(c+4898,"o_stall", false,-1);
    tracep->declBus(c+3767,"i_addr", false,-1, 21,0);
    tracep->declArray(c+3788,"i_data", false,-1, 576,0);
    tracep->declBit(c+3807,"o_valid", false,-1);
    tracep->declBit(c+4899,"i_stall", false,-1);
    tracep->declBus(c+3786,"o_decode", false,-1, 3,0);
    tracep->declBus(c+3808,"o_addr", false,-1, 21,0);
    tracep->declArray(c+3809,"o_data", false,-1, 576,0);
    tracep->declBus(c+5070,"OPT_NONESEL", false,-1, 0,0);
    tracep->declBus(c+120,"request", false,-1, 3,0);
    tracep->declBus(c+3828,"prerequest", false,-1, 2,0);
    tracep->declBus(c+35,"iM", false,-1, 31,0);
    tracep->pushNamePrefix("NO_DEFAULT_REQUEST ");
    tracep->declBus(c+121,"r_request", false,-1, 2,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("OPT_NONESEL_REQUEST ");
    tracep->declBit(c+122,"r_request_NS", false,-1);
    tracep->declBit(c+123,"r_none_sel", false,-1);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("iskid ");
    tracep->declBus(c+5113,"OPT_LOWPOWER", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_OUTREG", false,-1, 0,0);
    tracep->declBus(c+5113,"OPT_PASSTHROUGH", false,-1, 0,0);
    tracep->declBus(c+5277,"DW", false,-1, 31,0);
    tracep->declBus(c+5070,"OPT_INITIAL", false,-1, 0,0);
    tracep->declBit(c+4901,"i_clk", false,-1);
    tracep->declBit(c+124,"i_reset", false,-1);
    tracep->declBit(c+303,"i_valid", false,-1);
    tracep->declBit(c+3787,"o_ready", false,-1);
    tracep->declArray(c+3829,"i_data", false,-1, 598,0);
    tracep->declBit(c+118,"o_valid", false,-1);
    tracep->declBit(c+4900,"i_ready", false,-1);
    tracep->declArray(c+3848,"o_data", false,-1, 598,0);
    tracep->declArray(c+3867,"w_data", false,-1, 598,0);
    tracep->declBit(c+5074,"unused", false,-1);
    tracep->pushNamePrefix("LOGIC ");
    tracep->declBit(c+324,"r_valid", false,-1);
    tracep->declArray(c+3867,"r_data", false,-1, 598,0);
    tracep->popNamePrefix(3);
    tracep->pushNamePrefix("DOUBLE_BUFFERRED_STALL ");
    tracep->declBus(c+3307,"r_mack", false,-1, 3,0);
    tracep->declBus(c+3372,"r_merr", false,-1, 3,0);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("GEN_SINDEX[0] ");
    tracep->pushNamePrefix("SINDEX_MORE_THAN_ONE_MASTER ");
    tracep->declBus(c+3886,"r_sindex", false,-1, 1,0);
    tracep->declBus(c+4822,"regrant", false,-1, 3,0);
    tracep->declBus(c+4823,"reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("GEN_SINDEX[1] ");
    tracep->pushNamePrefix("SINDEX_MORE_THAN_ONE_MASTER ");
    tracep->declBus(c+3887,"r_sindex", false,-1, 1,0);
    tracep->declBus(c+4824,"regrant", false,-1, 3,0);
    tracep->declBus(c+4825,"reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("GEN_SINDEX[2] ");
    tracep->pushNamePrefix("SINDEX_MORE_THAN_ONE_MASTER ");
    tracep->declBus(c+3888,"r_sindex", false,-1, 1,0);
    tracep->declBus(c+4826,"regrant", false,-1, 3,0);
    tracep->declBus(c+4827,"reindex", false,-1, 1,0);
    tracep->popNamePrefix(2);
    tracep->pushNamePrefix("SLAVE_GRANT[0] ");
    tracep->declBit(c+155,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[1] ");
    tracep->declBit(c+156,"drop_sgrant", false,-1);
    tracep->popNamePrefix(1);
    tracep->pushNamePrefix("SLAVE_GRANT[2] ");
    tracep->declBit(c+157,"drop_sgrant", false,-1);
    tracep->popNamePrefix(3);
}

VL_ATTR_COLD void Vmain___024root__trace_init_top(Vmain___024root* vlSelf, VerilatedVcd* tracep) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root__trace_init_top\n"); );
    // Body
    Vmain___024root__trace_init_sub__TOP__0(vlSelf, tracep);
}

VL_ATTR_COLD void Vmain___024root__trace_full_top_0(void* voidSelf, VerilatedVcd::Buffer* bufp);
void Vmain___024root__trace_chg_top_0(void* voidSelf, VerilatedVcd::Buffer* bufp);
void Vmain___024root__trace_cleanup(void* voidSelf, VerilatedVcd* /*unused*/);

VL_ATTR_COLD void Vmain___024root__trace_register(Vmain___024root* vlSelf, VerilatedVcd* tracep) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root__trace_register\n"); );
    // Body
    tracep->addFullCb(&Vmain___024root__trace_full_top_0, vlSelf);
    tracep->addChgCb(&Vmain___024root__trace_chg_top_0, vlSelf);
    tracep->addCleanupCb(&Vmain___024root__trace_cleanup, vlSelf);
}

VL_ATTR_COLD void Vmain___024root__trace_full_sub_0(Vmain___024root* vlSelf, VerilatedVcd::Buffer* bufp);

VL_ATTR_COLD void Vmain___024root__trace_full_top_0(void* voidSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root__trace_full_top_0\n"); );
    // Init
    Vmain___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<Vmain___024root*>(voidSelf);
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    // Body
    Vmain___024root__trace_full_sub_0((&vlSymsp->TOP), bufp);
}

extern const VlWide<15>/*479:0*/ Vmain__ConstPool__CONST_hbd99daea_0;
extern const VlWide<16>/*511:0*/ Vmain__ConstPool__CONST_h93e1b771_0;
extern const VlWide<18>/*575:0*/ Vmain__ConstPool__CONST_hb679b2e5_0;

VL_ATTR_COLD void Vmain___024root__trace_full_sub_0(Vmain___024root* vlSelf, VerilatedVcd::Buffer* bufp) {
    if (false && vlSelf) {}  // Prevent unused
    Vmain__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vmain___024root__trace_full_sub_0\n"); );
    // Init
    uint32_t* const oldp VL_ATTR_UNUSED = bufp->oldp(vlSymsp->__Vm_baseCode);
    VlWide<16>/*511:0*/ __Vtemp_h053daff0__0;
    VlWide<16>/*511:0*/ __Vtemp_h3711b190__0;
    VlWide<16>/*511:0*/ __Vtemp_h58eb921b__0;
    VlWide<16>/*511:0*/ __Vtemp_hc1d82fb0__0;
    VlWide<16>/*511:0*/ __Vtemp_hc1851150__0;
    VlWide<16>/*511:0*/ __Vtemp_hd1e4c677__0;
    VlWide<16>/*511:0*/ __Vtemp_h6ddae8d1__0;
    VlWide<16>/*511:0*/ __Vtemp_hc1d82fb0__1;
    VlWide<16>/*511:0*/ __Vtemp_h6d0d1506__0;
    VlWide<17>/*543:0*/ __Vtemp_h6b3f223d__0;
    VlWide<16>/*511:0*/ __Vtemp_h01ff8f7b__0;
    VlWide<16>/*511:0*/ __Vtemp_he3c3974d__0;
    VlWide<16>/*511:0*/ __Vtemp_hcfafa750__0;
    VlWide<3>/*95:0*/ __Vtemp_h708d16f1__0;
    VlWide<64>/*2047:0*/ __Vtemp_h95b27ed2__0;
    VlWide<8>/*255:0*/ __Vtemp_h7cab7483__0;
    VlWide<16>/*511:0*/ __Vtemp_h53a5df10__0;
    VlWide<19>/*607:0*/ __Vtemp_hb52cb2db__0;
    VlWide<16>/*511:0*/ __Vtemp_hebded4b4__0;
    VlWide<19>/*607:0*/ __Vtemp_h0a2cdfa5__0;
    VlWide<19>/*607:0*/ __Vtemp_he57bd368__0;
    VlWide<16>/*511:0*/ __Vtemp_h0964a254__0;
    VlWide<19>/*607:0*/ __Vtemp_h925b4b87__0;
    VlWide<16>/*511:0*/ __Vtemp_h5b5f8605__0;
    VlWide<19>/*607:0*/ __Vtemp_hfe9179b2__0;
    VlWide<12>/*383:0*/ __Vtemp_ha40692d2__0;
    VlWide<48>/*1535:0*/ __Vtemp_h8a06d21b__0;
    VlWide<16>/*511:0*/ __Vtemp_hc035b709__1;
    VlWide<16>/*511:0*/ __Vtemp_hf82de6ac__0;
    VlWide<16>/*511:0*/ __Vtemp_hf74e670c__0;
    VlWide<16>/*511:0*/ __Vtemp_h21e563ec__0;
    VlWide<3>/*95:0*/ __Vtemp_hf465e4c8__0;
    VlWide<3>/*95:0*/ __Vtemp_hba125475__0;
    VlWide<3>/*95:0*/ __Vtemp_hca679e21__0;
    VlWide<3>/*95:0*/ __Vtemp_h0730ce07__0;
    VlWide<3>/*95:0*/ __Vtemp_h754c1427__0;
    // Body
    bufp->fullIData(oldp+1,(vlSelf->main__DOT__ddr3_controller_inst__DOT__nCK_to_cycles__Vstatic__result),32);
    bufp->fullIData(oldp+2,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__k),32);
    bufp->fullCData(oldp+3,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__tobits__DOT__newv),7);
    bufp->fullIData(oldp+4,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__k),32);
    bufp->fullCData(oldp+5,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__newv),7);
    bufp->fullIData(oldp+6,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__mkbytes__DOT__k),32);
    bufp->fullIData(oldp+7,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__ik),32);
    bufp->fullSData(oldp+8,(vlSelf->main__DOT__wb32_xbar__DOT__requested[0]),12);
    bufp->fullBit(oldp+9,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[0]));
    bufp->fullBit(oldp+10,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[1]));
    bufp->fullBit(oldp+11,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[2]));
    bufp->fullBit(oldp+12,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[3]));
    bufp->fullBit(oldp+13,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[4]));
    bufp->fullBit(oldp+14,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[5]));
    bufp->fullBit(oldp+15,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[6]));
    bufp->fullBit(oldp+16,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[7]));
    bufp->fullBit(oldp+17,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[8]));
    bufp->fullBit(oldp+18,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[9]));
    bufp->fullBit(oldp+19,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[10]));
    bufp->fullBit(oldp+20,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[11]));
    bufp->fullBit(oldp+21,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[12]));
    bufp->fullBit(oldp+22,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[13]));
    bufp->fullBit(oldp+23,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[14]));
    bufp->fullBit(oldp+24,(vlSelf->main__DOT__wb32_xbar__DOT__sindex[15]));
    bufp->fullIData(oldp+25,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM),32);
    bufp->fullCData(oldp+26,(vlSelf->main__DOT__wbu_xbar__DOT__requested[0]),2);
    bufp->fullBit(oldp+27,(vlSelf->main__DOT__wbu_xbar__DOT__sindex[0]));
    bufp->fullBit(oldp+28,(vlSelf->main__DOT__wbu_xbar__DOT__sindex[1]));
    bufp->fullBit(oldp+29,(vlSelf->main__DOT__wbu_xbar__DOT__sindex[2]));
    bufp->fullBit(oldp+30,(vlSelf->main__DOT__wbu_xbar__DOT__sindex[3]));
    bufp->fullIData(oldp+31,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM),32);
    bufp->fullIData(oldp+32,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__iM),32);
    bufp->fullIData(oldp+33,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__iM),32);
    bufp->fullIData(oldp+34,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__iM),32);
    bufp->fullIData(oldp+35,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__iM),32);
    bufp->fullIData(oldp+36,((((IData)(vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber3) 
                               << 0x1fU) | vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber4)),32);
    bufp->fullIData(oldp+37,((((IData)(vlSelf->main__DOT__i2ci__DOT__r_aborted) 
                               << 0x1fU) | vlSelf->main__DOT____Vcellinp__i2cscopei____pinNumber4)),32);
    bufp->fullIData(oldp+38,(vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber4),31);
    bufp->fullIData(oldp+39,((((IData)(vlSelf->main__DOT__i2ci__DOT__half_insn) 
                               << 0x1cU) | (((IData)(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual) 
                                             << 0x18U) 
                                            | vlSelf->main__DOT__i2ci__DOT____VdfgTmp_h373818eb__0))),32);
    bufp->fullBit(oldp+40,(vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN));
    bufp->fullBit(oldp+41,(vlSelf->main__DOT__i2ci__DOT____Vcellinp__u_fetch__i_reset));
    bufp->fullIData(oldp+42,(vlSelf->main__DOT____Vcellinp__i2cscopei____pinNumber4),31);
    bufp->fullBit(oldp+43,(vlSelf->main__DOT____Vcellinp__swic__i_dbg_cyc));
    bufp->fullBit(oldp+44,(vlSelf->main__DOT____Vcellinp__swic__i_dbg_stb));
    bufp->fullBit(oldp+45,(vlSelf->main__DOT____Vcellinp__swic__i_dbg_we));
    bufp->fullCData(oldp+46,(vlSelf->main__DOT____Vcellinp__swic__i_dbg_addr),7);
    bufp->fullIData(oldp+47,(vlSelf->main__DOT____Vcellinp__swic__i_dbg_data),32);
    bufp->fullBit(oldp+48,(vlSelf->main__DOT__swic__DOT__cpu_op_stall));
    bufp->fullBit(oldp+49,(((IData)(vlSelf->main__DOT__swic__DOT__cpu_op_stall) 
                            & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                               >> 1U))));
    bufp->fullBit(oldp+50,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ready));
    bufp->fullBit(oldp+51,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ce));
    bufp->fullBit(oldp+52,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_advance));
    bufp->fullBit(oldp+53,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall));
    bufp->fullBit(oldp+54,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_stalled));
    bufp->fullBit(oldp+55,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ce));
    bufp->fullBit(oldp+56,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rA) 
                            & (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0) 
                                & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_he857573c__0) 
                                   & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                                      >> 6U))) | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                                                   >> 6U) 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd))))));
    bufp->fullBit(oldp+57,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB) 
                            & ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_h39e03a19__0) 
                                 | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy)) 
                                & (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_zI)) 
                                    & ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                                         == (0x1fU 
                                             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))) 
                                        & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR)) 
                                       | (((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_pipe)) 
                                           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy)) 
                                          | ((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy) 
                                               | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy) 
                                                  | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy))) 
                                              & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_reg) 
                                                 == 
                                                 (0x1fU 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B)))) 
                                             | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                                                & (0xeU 
                                                   == 
                                                   (0xeU 
                                                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))))))) 
                                   | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_he857573c__0) 
                                      & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                                         >> 6U)))) 
                               | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                                   >> 6U) & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd))))));
    bufp->fullBit(oldp+58,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_stall));
    bufp->fullIData(oldp+59,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcB_v),32);
    bufp->fullIData(oldp+60,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_pcA_v),32);
    bufp->fullBit(oldp+61,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_ce));
    bufp->fullBit(oldp+62,(((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_stall) 
                              | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy)) 
                             & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu)) 
                            | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_ha62fb8d9__0))));
    bufp->fullBit(oldp+63,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_ce));
    bufp->fullBit(oldp+64,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_stalled));
    bufp->fullBit(oldp+65,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_ce));
    bufp->fullBit(oldp+66,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional));
    bufp->fullBit(oldp+67,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcset));
    bufp->fullCData(oldp+68,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pfpcsrc),3);
    bufp->fullCData(oldp+69,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__avsrc),3);
    bufp->fullCData(oldp+70,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bvsrc),3);
    bufp->fullBit(oldp+71,(((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_reset)) 
                            & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc)) 
                               & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__adf_ce_unconditional) 
                                  & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond) 
                                     & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim) 
                                        & ((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce) 
                                               & ((0xfU 
                                                   == 
                                                   (0xfU 
                                                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id))) 
                                                  & ((1U 
                                                      & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id) 
                                                         >> 4U)) 
                                                     == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie))))) 
                                           & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu)))))))));
    bufp->fullBit(oldp+72,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__this_is_a_multiply_op));
    bufp->fullBit(oldp+73,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset));
    bufp->fullBit(oldp+74,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_axisi2c__S_AXI_ARESETN));
    bufp->fullBit(oldp+75,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT____Vcellinp__u_fetch__i_reset));
    bufp->fullBit(oldp+76,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__o_pin));
    bufp->fullBit(oldp+77,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__w_in));
    bufp->fullBit(oldp+78,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__o_pin));
    bufp->fullBit(oldp+79,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__w_in));
    bufp->fullBit(oldp+80,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__o_pin));
    bufp->fullBit(oldp+81,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__w_in));
    bufp->fullBit(oldp+82,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT____Vcellout__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__o_pin));
    bufp->fullBit(oldp+83,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__w_in));
    bufp->fullBit(oldp+84,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__w_in));
    bufp->fullBit(oldp+85,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_reset));
    bufp->fullBit(oldp+86,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT____Vcellinp__UPSIZE__DOT__u_fifo__i_reset));
    bufp->fullCData(oldp+87,(vlSelf->main__DOT__wbu_xbar__DOT__s_stall),4);
    bufp->fullBit(oldp+88,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb));
    bufp->fullBit(oldp+89,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid));
    bufp->fullCData(oldp+90,((((IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS) 
                               << 2U) | ((- (IData)((IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid))) 
                                         & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest)))),3);
    bufp->fullCData(oldp+91,(((- (IData)((IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid))) 
                              & (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest))),2);
    bufp->fullBit(oldp+92,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS));
    bufp->fullBit(oldp+93,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel));
    bufp->fullBit(oldp+94,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset));
    bufp->fullBit(oldp+95,(vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+96,(vlSelf->main__DOT__wbu_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+97,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb));
    bufp->fullBit(oldp+98,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid));
    bufp->fullCData(oldp+99,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS) 
                               << 3U) | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request))),4);
    bufp->fullCData(oldp+100,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request),3);
    bufp->fullBit(oldp+101,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS));
    bufp->fullBit(oldp+102,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel));
    bufp->fullBit(oldp+103,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset));
    bufp->fullBit(oldp+104,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stb));
    bufp->fullBit(oldp+105,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_valid));
    bufp->fullCData(oldp+106,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS) 
                                << 3U) | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request))),4);
    bufp->fullCData(oldp+107,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request),3);
    bufp->fullBit(oldp+108,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS));
    bufp->fullBit(oldp+109,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel));
    bufp->fullBit(oldp+110,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__iskid__i_reset));
    bufp->fullBit(oldp+111,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stb));
    bufp->fullBit(oldp+112,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_valid));
    bufp->fullCData(oldp+113,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS) 
                                << 3U) | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request))),4);
    bufp->fullCData(oldp+114,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request),3);
    bufp->fullBit(oldp+115,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS));
    bufp->fullBit(oldp+116,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel));
    bufp->fullBit(oldp+117,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_reset));
    bufp->fullBit(oldp+118,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stb));
    bufp->fullBit(oldp+119,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_valid));
    bufp->fullCData(oldp+120,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS) 
                                << 3U) | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request))),4);
    bufp->fullCData(oldp+121,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request),3);
    bufp->fullBit(oldp+122,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS));
    bufp->fullBit(oldp+123,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel));
    bufp->fullBit(oldp+124,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_reset));
    bufp->fullBit(oldp+125,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request));
    bufp->fullBit(oldp+126,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_data_request));
    bufp->fullBit(oldp+127,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__new_tx_request));
    bufp->fullBit(oldp+128,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_cmd_request));
    bufp->fullBit(oldp+129,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_data_request));
    bufp->fullBit(oldp+130,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__new_tx_request));
    bufp->fullBit(oldp+131,(vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_reset));
    bufp->fullBit(oldp+132,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stb));
    bufp->fullBit(oldp+133,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_valid));
    bufp->fullSData(oldp+134,((((IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS) 
                                << 0xcU) | (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request))),13);
    bufp->fullSData(oldp+135,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__NO_DEFAULT_REQUEST__DOT__r_request),12);
    bufp->fullBit(oldp+136,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_request_NS));
    bufp->fullBit(oldp+137,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__OPT_NONESEL_REQUEST__DOT__r_none_sel));
    bufp->fullBit(oldp+138,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_reset));
    bufp->fullBit(oldp+139,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+140,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__10__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+141,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__11__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+142,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+143,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+144,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__3__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+145,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__4__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+146,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__5__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+147,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__6__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+148,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__7__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+149,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__8__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+150,(vlSelf->main__DOT__wb32_xbar__DOT__SLAVE_GRANT__BRA__9__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+151,(vlSelf->main__DOT__wbu_xbar__DOT__m_stall));
    bufp->fullBit(oldp+152,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall));
    bufp->fullBit(oldp+153,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall));
    bufp->fullBit(oldp+154,((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall)))));
    bufp->fullBit(oldp+155,(vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__0__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+156,(vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__1__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+157,(vlSelf->main__DOT__wbwide_xbar__DOT__SLAVE_GRANT__BRA__2__KET____DOT__drop_sgrant));
    bufp->fullBit(oldp+158,(vlSelf->main__DOT__emmcscope_int));
    bufp->fullBit(oldp+159,(vlSelf->main__DOT__sdioscope_int));
    bufp->fullBit(oldp+160,(vlSelf->main__DOT__emmc_int));
    bufp->fullBit(oldp+161,(vlSelf->main__DOT__sdcard_int));
    bufp->fullBit(oldp+162,((1U & ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill) 
                                   >> 5U))));
    bufp->fullBit(oldp+163,((1U & (~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow)))));
    bufp->fullBit(oldp+164,((1U & ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                                   >> 5U))));
    bufp->fullBit(oldp+165,((1U & (~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)))));
    bufp->fullBit(oldp+166,(vlSelf->main__DOT__i2cscope_int));
    bufp->fullBit(oldp+167,(vlSelf->main__DOT__gpio_int));
    bufp->fullBit(oldp+168,(vlSelf->main__DOT__spio_int));
    bufp->fullBit(oldp+169,(vlSelf->main__DOT__r_sirefclk_en));
    bufp->fullIData(oldp+170,(vlSelf->main__DOT__r_sirefclk_data),30);
    bufp->fullBit(oldp+171,(vlSelf->main__DOT__w_sirefclk_unused_stb));
    bufp->fullBit(oldp+172,(vlSelf->main__DOT__r_sirefclk_ack));
    bufp->fullBit(oldp+173,((1U & (~ (IData)(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid)))));
    bufp->fullBit(oldp+174,(vlSelf->main__DOT__i2c_valid));
    bufp->fullBit(oldp+175,(vlSelf->main__DOT__i2c_ready));
    bufp->fullBit(oldp+176,(vlSelf->main__DOT__i2c_last));
    bufp->fullCData(oldp+177,(vlSelf->main__DOT__i2c_data),8);
    bufp->fullCData(oldp+178,(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__axis_tid),2);
    bufp->fullIData(oldp+179,((((IData)(vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber3) 
                                << 0x1fU) | vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber4)),32);
    bufp->fullBit(oldp+180,(vlSelf->main__DOT__w_console_rx_stb));
    bufp->fullBit(oldp+181,((1U & (~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow)))));
    bufp->fullBit(oldp+182,(vlSelf->main__DOT__w_console_busy));
    bufp->fullCData(oldp+183,(vlSelf->main__DOT__w_console_rx_data),7);
    bufp->fullCData(oldp+184,(vlSelf->main__DOT__w_console_tx_data),7);
    bufp->fullIData(oldp+185,(vlSelf->main__DOT__uart_debug),32);
    bufp->fullBit(oldp+186,(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb));
    bufp->fullBit(oldp+187,(vlSelf->main__DOT__raw_cpu_dbg_ack));
    bufp->fullSData(oldp+188,((((IData)(vlSelf->main__DOT__gpio_int) 
                                << 0xfU) | (((IData)(vlSelf->main__DOT__i2cscope_int) 
                                             << 0xeU) 
                                            | ((0x2000U 
                                                & ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)) 
                                                   << 0xdU)) 
                                               | ((0x1000U 
                                                   & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow)) 
                                                      << 0xcU)) 
                                                  | (((IData)(vlSelf->main__DOT__emmc_int) 
                                                      << 0xbU) 
                                                     | (((IData)(vlSelf->main__DOT__sdioscope_int) 
                                                         << 0xaU) 
                                                        | (((IData)(vlSelf->main__DOT__emmcscope_int) 
                                                            << 9U) 
                                                           | (IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0))))))))),16);
    bufp->fullBit(oldp+189,(vlSelf->main__DOT__zip_cpu_int));
    bufp->fullCData(oldp+190,(vlSelf->main__DOT__wbu_rx_data),8);
    bufp->fullCData(oldp+191,(vlSelf->main__DOT__genbus__DOT__ps_data),8);
    bufp->fullBit(oldp+192,(vlSelf->main__DOT__wbu_rx_stb));
    bufp->fullBit(oldp+193,(vlSelf->main__DOT__genbus__DOT__ps_full));
    bufp->fullBit(oldp+194,(vlSelf->main__DOT__txv__DOT__r_busy));
    bufp->fullBit(oldp+195,(vlSelf->main__DOT__genbus__DOT__r_wdt_reset));
    bufp->fullCData(oldp+196,(vlSelf->main__DOT__w_led),8);
    bufp->fullSData(oldp+197,((((IData)(vlSelf->main__DOT__spio_int) 
                                << 9U) | ((0x100U & 
                                           ((IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill) 
                                            << 3U)) 
                                          | ((0x80U 
                                              & ((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill) 
                                                 << 2U)) 
                                             | ((IData)(vlSelf->main__DOT__sdcard_int) 
                                                << 6U))))),15);
    bufp->fullSData(oldp+198,((((IData)(vlSelf->main__DOT__gpio_int) 
                                << 0xeU) | (((IData)(vlSelf->main__DOT__i2cscope_int) 
                                             << 0xdU) 
                                            | ((0x1000U 
                                                & ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)) 
                                                   << 0xcU)) 
                                               | ((0x800U 
                                                   & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow)) 
                                                      << 0xbU)) 
                                                  | (((IData)(vlSelf->main__DOT__emmc_int) 
                                                      << 0xaU) 
                                                     | (((IData)(vlSelf->main__DOT__sdioscope_int) 
                                                         << 9U) 
                                                        | ((IData)(vlSelf->main__DOT__emmcscope_int) 
                                                           << 8U)))))))),15);
    bufp->fullBit(oldp+199,(vlSelf->main__DOT__wbwide_i2cdma_cyc));
    bufp->fullBit(oldp+200,(vlSelf->main__DOT__wbwide_i2cdma_stb));
    bufp->fullIData(oldp+201,(vlSelf->main__DOT__wbwide_i2cdma_addr),22);
    bufp->fullWData(oldp+202,(vlSelf->main__DOT__wbwide_i2cdma_data),512);
    bufp->fullQData(oldp+218,(vlSelf->main__DOT__wbwide_i2cdma_sel),64);
    bufp->fullBit(oldp+220,((1U & (IData)(vlSelf->__VdfgTmp_h503d14d1__0))));
    bufp->fullBit(oldp+221,((1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack))));
    bufp->fullBit(oldp+222,((1U & (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr))));
    __Vtemp_h053daff0__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0U];
    __Vtemp_h053daff0__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[1U];
    __Vtemp_h053daff0__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[2U];
    __Vtemp_h053daff0__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[3U];
    __Vtemp_h053daff0__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[4U];
    __Vtemp_h053daff0__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[5U];
    __Vtemp_h053daff0__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[6U];
    __Vtemp_h053daff0__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[7U];
    __Vtemp_h053daff0__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[8U];
    __Vtemp_h053daff0__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[9U];
    __Vtemp_h053daff0__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0xaU];
    __Vtemp_h053daff0__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0xbU];
    __Vtemp_h053daff0__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0xcU];
    __Vtemp_h053daff0__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0xdU];
    __Vtemp_h053daff0__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0xeU];
    __Vtemp_h053daff0__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0xfU];
    bufp->fullWData(oldp+223,(__Vtemp_h053daff0__0),512);
    bufp->fullBit(oldp+239,(vlSelf->main__DOT__wbwide_i2cm_cyc));
    bufp->fullBit(oldp+240,(vlSelf->main__DOT__wbwide_i2cm_stb));
    bufp->fullIData(oldp+241,(vlSelf->main__DOT__wbwide_i2cm_addr),22);
    bufp->fullBit(oldp+242,((1U & ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                                   >> 1U))));
    bufp->fullBit(oldp+243,((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                   >> 1U))));
    bufp->fullBit(oldp+244,((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                                   >> 1U))));
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
    bufp->fullWData(oldp+245,(__Vtemp_h3711b190__0),512);
    bufp->fullBit(oldp+261,(vlSelf->main__DOT__wbwide_zip_cyc));
    bufp->fullBit(oldp+262,(vlSelf->main__DOT__wbwide_zip_stb));
    bufp->fullBit(oldp+263,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)
                                    ? (IData)(vlSelf->main__DOT__swic__DOT__cpu_we)
                                    : (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner))))));
    bufp->fullIData(oldp+264,(vlSelf->main__DOT__wbwide_zip_addr),22);
    if (vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner) {
        __Vtemp_h58eb921b__0[0U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U];
        __Vtemp_h58eb921b__0[1U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U];
        __Vtemp_h58eb921b__0[2U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U];
        __Vtemp_h58eb921b__0[3U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U];
        __Vtemp_h58eb921b__0[4U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U];
        __Vtemp_h58eb921b__0[5U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U];
        __Vtemp_h58eb921b__0[6U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U];
        __Vtemp_h58eb921b__0[7U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U];
        __Vtemp_h58eb921b__0[8U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U];
        __Vtemp_h58eb921b__0[9U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U];
        __Vtemp_h58eb921b__0[0xaU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU];
        __Vtemp_h58eb921b__0[0xbU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU];
        __Vtemp_h58eb921b__0[0xcU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU];
        __Vtemp_h58eb921b__0[0xdU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU];
        __Vtemp_h58eb921b__0[0xeU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU];
        __Vtemp_h58eb921b__0[0xfU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU];
    } else {
        __Vtemp_h58eb921b__0[0U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0U];
        __Vtemp_h58eb921b__0[1U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[1U];
        __Vtemp_h58eb921b__0[2U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[2U];
        __Vtemp_h58eb921b__0[3U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[3U];
        __Vtemp_h58eb921b__0[4U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[4U];
        __Vtemp_h58eb921b__0[5U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[5U];
        __Vtemp_h58eb921b__0[6U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[6U];
        __Vtemp_h58eb921b__0[7U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[7U];
        __Vtemp_h58eb921b__0[8U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[8U];
        __Vtemp_h58eb921b__0[9U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[9U];
        __Vtemp_h58eb921b__0[0xaU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xaU];
        __Vtemp_h58eb921b__0[0xbU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xbU];
        __Vtemp_h58eb921b__0[0xcU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xcU];
        __Vtemp_h58eb921b__0[0xdU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xdU];
        __Vtemp_h58eb921b__0[0xeU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xeU];
        __Vtemp_h58eb921b__0[0xfU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xfU];
    }
    bufp->fullWData(oldp+265,(__Vtemp_h58eb921b__0),512);
    bufp->fullQData(oldp+281,(((IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)
                                ? ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner)
                                    ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel
                                    : 0xffffffffffffffffULL)
                                : ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner)
                                    ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_sel
                                    : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_sel))),64);
    bufp->fullBit(oldp+283,((1U & ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                                   >> 2U))));
    bufp->fullBit(oldp+284,((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                   >> 2U))));
    bufp->fullBit(oldp+285,((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                                   >> 2U))));
    __Vtemp_hc1d82fb0__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x20U];
    __Vtemp_hc1d82fb0__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x21U];
    __Vtemp_hc1d82fb0__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x22U];
    __Vtemp_hc1d82fb0__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x23U];
    __Vtemp_hc1d82fb0__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x24U];
    __Vtemp_hc1d82fb0__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x25U];
    __Vtemp_hc1d82fb0__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x26U];
    __Vtemp_hc1d82fb0__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x27U];
    __Vtemp_hc1d82fb0__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x28U];
    __Vtemp_hc1d82fb0__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x29U];
    __Vtemp_hc1d82fb0__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2aU];
    __Vtemp_hc1d82fb0__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2bU];
    __Vtemp_hc1d82fb0__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2cU];
    __Vtemp_hc1d82fb0__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2dU];
    __Vtemp_hc1d82fb0__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2eU];
    __Vtemp_hc1d82fb0__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2fU];
    bufp->fullWData(oldp+286,(__Vtemp_hc1d82fb0__0),512);
    bufp->fullBit(oldp+302,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_cyc));
    bufp->fullBit(oldp+303,(vlSelf->main__DOT__wbwide_wbu_arbiter_stb));
    bufp->fullBit(oldp+304,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_we));
    bufp->fullIData(oldp+305,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_addr),22);
    bufp->fullWData(oldp+306,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data),512);
    bufp->fullQData(oldp+322,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_sel),64);
    bufp->fullBit(oldp+324,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+325,((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                   >> 3U))));
    bufp->fullBit(oldp+326,((1U & ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr) 
                                   >> 3U))));
    __Vtemp_hc1851150__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x30U];
    __Vtemp_hc1851150__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x31U];
    __Vtemp_hc1851150__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x32U];
    __Vtemp_hc1851150__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x33U];
    __Vtemp_hc1851150__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x34U];
    __Vtemp_hc1851150__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x35U];
    __Vtemp_hc1851150__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x36U];
    __Vtemp_hc1851150__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x37U];
    __Vtemp_hc1851150__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x38U];
    __Vtemp_hc1851150__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x39U];
    __Vtemp_hc1851150__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x3aU];
    __Vtemp_hc1851150__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x3bU];
    __Vtemp_hc1851150__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x3cU];
    __Vtemp_hc1851150__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x3dU];
    __Vtemp_hc1851150__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x3eU];
    __Vtemp_hc1851150__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x3fU];
    bufp->fullWData(oldp+327,(__Vtemp_hc1851150__0),512);
    bufp->fullBit(oldp+343,(vlSelf->main__DOT__wbwide_wbdown_stall));
    bufp->fullBit(oldp+344,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_ack));
    bufp->fullWData(oldp+345,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data),512);
    bufp->fullBit(oldp+361,(vlSelf->main__DOT__wbwide_bkram_ack));
    bufp->fullWData(oldp+362,(vlSelf->main__DOT__wbwide_bkram_idata),512);
    bufp->fullBit(oldp+378,(vlSelf->main__DOT__wb32_wbdown_stb));
    bufp->fullBit(oldp+379,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_we));
    bufp->fullCData(oldp+380,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_addr),8);
    bufp->fullIData(oldp+381,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data[0xfU]),32);
    bufp->fullCData(oldp+382,((0xfU & (IData)((vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel 
                                               >> 0x3cU)))),4);
    bufp->fullBit(oldp+383,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+384,(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    bufp->fullIData(oldp+385,(vlSelf->main__DOT__wb32_wbdown_idata),32);
    bufp->fullIData(oldp+386,((((~ (IData)(vlSelf->main__DOT__r_sirefclk_en)) 
                                << 0x1fU) | vlSelf->main__DOT__r_sirefclk_data)),32);
    bufp->fullBit(oldp+387,(vlSelf->main__DOT__wb32_spio_ack));
    bufp->fullIData(oldp+388,((((IData)(vlSelf->main__DOT__spioi__DOT__led_demo) 
                                << 0x18U) | (((IData)(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__r_btn) 
                                              << 0x10U) 
                                             | (((IData)(vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw) 
                                                 << 8U) 
                                                | (IData)(vlSelf->main__DOT__spioi__DOT__r_led))))),32);
    bufp->fullBit(oldp+389,(vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack));
    bufp->fullIData(oldp+390,(vlSelf->main__DOT__emmcscopei__DOT__o_bus_data),32);
    bufp->fullBit(oldp+391,(vlSelf->main__DOT__i2cscopei__DOT__br_wb_ack));
    bufp->fullIData(oldp+392,(vlSelf->main__DOT__i2cscopei__DOT__o_bus_data),32);
    bufp->fullBit(oldp+393,(vlSelf->main__DOT__sdioscopei__DOT__br_wb_ack));
    bufp->fullIData(oldp+394,(vlSelf->main__DOT__sdioscopei__DOT__o_bus_data),32);
    bufp->fullBit(oldp+395,(vlSelf->main__DOT__wb32_i2cs_ack));
    bufp->fullIData(oldp+396,(vlSelf->main__DOT__i2ci__DOT__bus_read_data),32);
    bufp->fullBit(oldp+397,(vlSelf->main__DOT__wb32_i2cdma_ack));
    bufp->fullIData(oldp+398,(vlSelf->main__DOT__wb32_i2cdma_idata),32);
    bufp->fullBit(oldp+399,(vlSelf->main__DOT__wb32_uart_ack));
    bufp->fullIData(oldp+400,(vlSelf->main__DOT__wb32_uart_idata),32);
    bufp->fullBit(oldp+401,(vlSelf->main__DOT__wb32_emmc_ack));
    bufp->fullIData(oldp+402,(vlSelf->main__DOT__wb32_emmc_idata),32);
    bufp->fullBit(oldp+403,(vlSelf->main__DOT__wb32_fan_ack));
    bufp->fullIData(oldp+404,(vlSelf->main__DOT__wb32_fan_idata),32);
    bufp->fullBit(oldp+405,(vlSelf->main__DOT__wb32_sdcard_ack));
    bufp->fullIData(oldp+406,(vlSelf->main__DOT__wb32_sdcard_idata),32);
    bufp->fullBit(oldp+407,(vlSelf->main__DOT__r_wb32_sio_ack));
    bufp->fullIData(oldp+408,(vlSelf->main__DOT__r_wb32_sio_data),32);
    bufp->fullBit(oldp+409,(vlSelf->main__DOT__r_cfg_ack));
    bufp->fullBit(oldp+410,(vlSelf->main__DOT__wbu_cyc));
    bufp->fullBit(oldp+411,(vlSelf->main__DOT__wbu_stb));
    bufp->fullBit(oldp+412,(vlSelf->main__DOT__wbu_we));
    bufp->fullIData(oldp+413,((0x7ffffffU & vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr)),27);
    bufp->fullIData(oldp+414,(vlSelf->main__DOT__wbu_data),32);
    bufp->fullBit(oldp+415,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+416,(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack));
    bufp->fullBit(oldp+417,(vlSelf->main__DOT__wbu_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    bufp->fullIData(oldp+418,(vlSelf->main__DOT__wbu_idata),32);
    bufp->fullBit(oldp+419,((1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc))));
    bufp->fullBit(oldp+420,((1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb))));
    bufp->fullBit(oldp+421,((1U & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_swe))));
    bufp->fullIData(oldp+422,((0x7ffffffU & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr))),27);
    bufp->fullIData(oldp+423,((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sdata)),32);
    bufp->fullCData(oldp+424,((0xfU & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_ssel))),4);
    bufp->fullBit(oldp+425,(vlSelf->main__DOT__wbu_wbu_arbiter_stall));
    bufp->fullBit(oldp+426,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_ack));
    bufp->fullBit(oldp+427,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err));
    bufp->fullIData(oldp+428,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__rtn_data[0xfU]),32);
    bufp->fullBit(oldp+429,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                                   >> 1U))));
    bufp->fullBit(oldp+430,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb) 
                                   >> 1U))));
    bufp->fullBit(oldp+431,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_swe) 
                                   >> 1U))));
    bufp->fullIData(oldp+432,((0x7ffffffU & (IData)(
                                                    (vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr 
                                                     >> 0x1bU)))),27);
    bufp->fullIData(oldp+433,((IData)((vlSelf->main__DOT____Vcellout__wbu_xbar__o_sdata 
                                       >> 0x20U))),32);
    bufp->fullCData(oldp+434,((0xfU & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_ssel) 
                                       >> 4U))),4);
    bufp->fullIData(oldp+435,(vlSelf->main__DOT__wbu_zip_idata),32);
    bufp->fullIData(oldp+436,((0x3fffffffU & vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr)),30);
    bufp->fullBit(oldp+437,(vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_wstb));
    bufp->fullBit(oldp+438,(vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_stb));
    bufp->fullWData(oldp+439,(vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_data),512);
    bufp->fullSData(oldp+455,(vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_addr),14);
    bufp->fullQData(oldp+456,(vlSelf->main__DOT__bkrami__DOT__EXTRA_MEM_CLOCK_CYCLE__DOT__last_sel),64);
    bufp->fullIData(oldp+458,(vlSelf->main__DOT__bkrami__DOT__WRITE_TO_MEMORY__DOT__ik),32);
    bufp->fullIData(oldp+459,(vlSelf->main__DOT__r_sirefclk_data),32);
    bufp->fullIData(oldp+460,(vlSelf->main__DOT__clock_generator__DOT__counter[0]),32);
    bufp->fullIData(oldp+461,(vlSelf->main__DOT__clock_generator__DOT__counter[1]),32);
    bufp->fullIData(oldp+462,(vlSelf->main__DOT__clock_generator__DOT__counter[2]),32);
    bufp->fullIData(oldp+463,(vlSelf->main__DOT__clock_generator__DOT__counter[3]),32);
    bufp->fullIData(oldp+464,(vlSelf->main__DOT__clock_generator__DOT__counter[4]),32);
    bufp->fullIData(oldp+465,(vlSelf->main__DOT__clock_generator__DOT__counter[5]),32);
    bufp->fullIData(oldp+466,(vlSelf->main__DOT__clock_generator__DOT__counter[6]),32);
    bufp->fullIData(oldp+467,(vlSelf->main__DOT__clock_generator__DOT__counter[7]),32);
    bufp->fullIData(oldp+468,(vlSelf->main__DOT__clock_generator__DOT__r_delay),32);
    bufp->fullIData(oldp+469,(vlSelf->main__DOT__clock_generator__DOT__times_three),32);
    bufp->fullIData(oldp+470,(vlSelf->main__DOT__clock_generator__DOT__times_five),32);
    bufp->fullIData(oldp+471,(vlSelf->main__DOT__clock_generator__DOT__times_seven),32);
    bufp->fullBit(oldp+472,(vlSelf->main__DOT__console__DOT__rx_uart_reset));
    bufp->fullBit(oldp+473,(((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write)) 
                             & (IData)(vlSelf->main__DOT__w_console_rx_stb))));
    bufp->fullCData(oldp+474,(vlSelf->main__DOT__console__DOT__rxf_wb_data),7);
    bufp->fullSData(oldp+475,(vlSelf->main__DOT__console__DOT__rxf_status),16);
    bufp->fullBit(oldp+476,(vlSelf->main__DOT__console__DOT__rxf_wb_read));
    bufp->fullIData(oldp+477,(((((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write)) 
                                 & (IData)(vlSelf->main__DOT__w_console_rx_stb)) 
                                << 0xcU) | (((IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow) 
                                             << 8U) 
                                            | (IData)(vlSelf->main__DOT__console__DOT__rxf_wb_data)))),32);
    bufp->fullBit(oldp+478,(((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write)) 
                             & (IData)(vlSelf->main__DOT__console__DOT__txf_wb_write))));
    bufp->fullSData(oldp+479,(vlSelf->main__DOT__console__DOT__txf_status),16);
    bufp->fullBit(oldp+480,(vlSelf->main__DOT__console__DOT__txf_wb_write));
    bufp->fullBit(oldp+481,(vlSelf->main__DOT__console__DOT__tx_uart_reset));
    bufp->fullCData(oldp+482,(vlSelf->main__DOT__console__DOT__txf_wb_data),7);
    bufp->fullIData(oldp+483,((((IData)(vlSelf->__VdfgTmp_ha46ae6a3__0) 
                                << 0xdU) | ((((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write)) 
                                              & (IData)(vlSelf->main__DOT__console__DOT__txf_wb_write)) 
                                             << 0xcU) 
                                            | ((0x400U 
                                                & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow)) 
                                                   << 0xaU)) 
                                               | (((IData)(vlSelf->main__DOT__console__DOT____VdfgTmp_h60af6732__0) 
                                                   << 8U) 
                                                  | ((IData)(vlSelf->main__DOT__console__DOT____VdfgTmp_h60af6732__0)
                                                      ? (IData)(vlSelf->main__DOT__console__DOT__txf_wb_data)
                                                      : 0U)))))),32);
    bufp->fullIData(oldp+484,((((IData)(vlSelf->main__DOT__console__DOT__txf_status) 
                                << 0x10U) | (IData)(vlSelf->main__DOT__console__DOT__rxf_status))),32);
    bufp->fullCData(oldp+485,(vlSelf->main__DOT__console__DOT__r_wb_addr),2);
    bufp->fullBit(oldp+486,(vlSelf->main__DOT__console__DOT__r_wb_ack));
    bufp->fullCData(oldp+487,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_data),7);
    bufp->fullCData(oldp+488,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__last_write),7);
    bufp->fullCData(oldp+489,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr),6);
    bufp->fullCData(oldp+490,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__rd_addr),6);
    bufp->fullCData(oldp+491,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_next),6);
    bufp->fullBit(oldp+492,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_overflow));
    bufp->fullBit(oldp+493,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow));
    bufp->fullBit(oldp+494,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__osrc));
    bufp->fullCData(oldp+495,((0x3fU & ((IData)(1U) 
                                        + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr)))),6);
    bufp->fullCData(oldp+496,((0x3fU & ((IData)(2U) 
                                        + (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__wr_addr)))),6);
    bufp->fullBit(oldp+497,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_write));
    bufp->fullBit(oldp+498,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_read));
    bufp->fullCData(oldp+499,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__r_fill),6);
    bufp->fullSData(oldp+500,(vlSelf->main__DOT__console__DOT__rxfifo__DOT__w_fill),10);
    bufp->fullBit(oldp+501,(vlSelf->main__DOT__console__DOT____Vcellinp__txfifo____pinNumber6));
    bufp->fullCData(oldp+502,(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_data),7);
    bufp->fullCData(oldp+503,(vlSelf->main__DOT__console__DOT__txfifo__DOT__last_write),7);
    bufp->fullCData(oldp+504,(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr),6);
    bufp->fullCData(oldp+505,(vlSelf->main__DOT__console__DOT__txfifo__DOT__rd_addr),6);
    bufp->fullCData(oldp+506,(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_next),6);
    bufp->fullBit(oldp+507,(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow));
    bufp->fullBit(oldp+508,(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_underflow));
    bufp->fullBit(oldp+509,(vlSelf->main__DOT__console__DOT__txfifo__DOT__osrc));
    bufp->fullCData(oldp+510,((0x3fU & ((IData)(1U) 
                                        + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr)))),6);
    bufp->fullCData(oldp+511,((0x3fU & ((IData)(2U) 
                                        + (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__wr_addr)))),6);
    bufp->fullBit(oldp+512,(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_write));
    bufp->fullBit(oldp+513,(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_read));
    bufp->fullCData(oldp+514,(vlSelf->main__DOT__console__DOT__txfifo__DOT__r_fill),6);
    bufp->fullSData(oldp+515,(vlSelf->main__DOT__console__DOT__txfifo__DOT__w_fill),10);
    bufp->fullBit(oldp+516,(vlSelf->main__DOT____Vcellinp__emmcscopei____pinNumber3));
    bufp->fullBit(oldp+517,(vlSelf->main__DOT__emmcscopei__DOT__read_address));
    bufp->fullSData(oldp+518,(vlSelf->main__DOT__emmcscopei__DOT__raddr),12);
    bufp->fullSData(oldp+519,(vlSelf->main__DOT__emmcscopei__DOT__waddr),12);
    bufp->fullBit(oldp+520,((1U & (~ ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                                      >> 2U)))));
    bufp->fullBit(oldp+521,((1U & ((IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config) 
                                   >> 1U))));
    bufp->fullBit(oldp+522,((1U & (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_config))));
    bufp->fullCData(oldp+523,(vlSelf->main__DOT__emmcscopei__DOT__br_config),3);
    bufp->fullIData(oldp+524,(vlSelf->main__DOT__emmcscopei__DOT__br_holdoff),20);
    bufp->fullIData(oldp+525,(vlSelf->main__DOT__emmcscopei__DOT__holdoff_counter),20);
    bufp->fullBit(oldp+526,(vlSelf->main__DOT__emmcscopei__DOT__dr_triggered));
    bufp->fullBit(oldp+527,(vlSelf->main__DOT__emmcscopei__DOT__dr_primed));
    bufp->fullBit(oldp+528,(vlSelf->main__DOT__emmcscopei__DOT__dw_trigger));
    bufp->fullBit(oldp+529,(vlSelf->main__DOT__emmcscopei__DOT__dr_stopped));
    bufp->fullCData(oldp+530,(vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe),5);
    bufp->fullBit(oldp+531,((1U & ((IData)(vlSelf->main__DOT__emmcscopei__DOT__dr_stop_pipe) 
                                   >> 4U))));
    bufp->fullIData(oldp+532,(vlSelf->main__DOT__emmcscopei__DOT__ck_addr),31);
    bufp->fullIData(oldp+533,(vlSelf->main__DOT__emmcscopei__DOT__qd_data),31);
    bufp->fullBit(oldp+534,(vlSelf->main__DOT__emmcscopei__DOT__dr_force_write));
    bufp->fullBit(oldp+535,(vlSelf->main__DOT__emmcscopei__DOT__dr_run_timeout));
    bufp->fullBit(oldp+536,(vlSelf->main__DOT__emmcscopei__DOT__new_data));
    bufp->fullBit(oldp+537,(vlSelf->main__DOT__emmcscopei__DOT__dr_force_inhibit));
    bufp->fullBit(oldp+538,(vlSelf->main__DOT__emmcscopei__DOT__imm_adr));
    bufp->fullBit(oldp+539,(vlSelf->main__DOT__emmcscopei__DOT__lst_adr));
    bufp->fullIData(oldp+540,(vlSelf->main__DOT__emmcscopei__DOT__lst_val),31);
    bufp->fullIData(oldp+541,(vlSelf->main__DOT__emmcscopei__DOT__imm_val),31);
    bufp->fullBit(oldp+542,(vlSelf->main__DOT__emmcscopei__DOT__record_ce));
    bufp->fullIData(oldp+543,(vlSelf->main__DOT__emmcscopei__DOT__r_data),32);
    bufp->fullBit(oldp+544,(vlSelf->main__DOT__emmcscopei__DOT__br_pre_wb_ack));
    bufp->fullSData(oldp+545,(vlSelf->main__DOT__emmcscopei__DOT__this_addr),12);
    bufp->fullIData(oldp+546,(vlSelf->main__DOT__emmcscopei__DOT__nxt_mem),32);
    bufp->fullBit(oldp+547,(vlSelf->main__DOT__emmcscopei__DOT__br_level_interrupt));
    bufp->fullBit(oldp+548,(vlSelf->main__DOT__genbus__DOT__soft_reset));
    bufp->fullBit(oldp+549,(vlSelf->main__DOT__genbus__DOT__rx_valid));
    bufp->fullCData(oldp+550,((0x7fU & (IData)(vlSelf->main__DOT__wbu_rx_data))),8);
    bufp->fullBit(oldp+551,(vlSelf->main__DOT__genbus__DOT__in_stb));
    bufp->fullBit(oldp+552,(((IData)(vlSelf->main__DOT__genbus__DOT__rx_valid) 
                             | ((((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
                                  | (IData)(vlSelf->main__DOT__genbus__DOT__in_stb)) 
                                 | (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))) 
                                | (0U < (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len))))));
    bufp->fullQData(oldp+553,(vlSelf->main__DOT__genbus__DOT__in_word),36);
    bufp->fullBit(oldp+555,(vlSelf->main__DOT__genbus__DOT__wbu_tx_stb));
    bufp->fullCData(oldp+556,(vlSelf->main__DOT__genbus__DOT__wbu_tx_data),8);
    bufp->fullBit(oldp+557,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n));
    bufp->fullQData(oldp+558,(vlSelf->main__DOT__genbus__DOT__ififo_codword),36);
    bufp->fullBit(oldp+560,(vlSelf->main__DOT__genbus__DOT__exec_stb));
    bufp->fullQData(oldp+561,(vlSelf->main__DOT__genbus__DOT__exec_word),36);
    bufp->fullBit(oldp+563,(vlSelf->main__DOT__genbus__DOT__ofifo_rd));
    bufp->fullQData(oldp+564,(vlSelf->main__DOT__genbus__DOT__ofifo_codword),36);
    bufp->fullBit(oldp+566,((((IData)(vlSelf->main__DOT__genbus__DOT__exec_stb) 
                              & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_rd)) 
                                 & (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow))) 
                             | ((~ (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_empty_n)) 
                                & (IData)(vlSelf->main__DOT__genbus__DOT__ofifo_rd)))));
    bufp->fullBit(oldp+567,(vlSelf->main__DOT__genbus__DOT__ofifo_empty_n));
    bufp->fullBit(oldp+568,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_busy));
    bufp->fullIData(oldp+569,(vlSelf->main__DOT__genbus__DOT__r_wdt_timer),19);
    bufp->fullBit(oldp+570,(((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy) 
                             & (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb))));
    bufp->fullBit(oldp+571,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb));
    bufp->fullBit(oldp+572,(((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb) 
                             | (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__r_active))));
    bufp->fullSData(oldp+573,(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr),11);
    bufp->fullSData(oldp+574,(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr),11);
    bufp->fullSData(oldp+575,((0x7ffU & ((IData)(1U) 
                                         + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_wrptr)))),11);
    bufp->fullSData(oldp+576,((0x7ffU & ((IData)(1U) 
                                         + (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__r_rdptr)))),11);
    bufp->fullBit(oldp+577,(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_overflow));
    bufp->fullBit(oldp+578,(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow));
    bufp->fullBit(oldp+579,((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__will_underflow)))));
    bufp->fullBit(oldp+580,(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_write));
    bufp->fullBit(oldp+581,(vlSelf->main__DOT__genbus__DOT__GEN_OUTBOUND_FIFO__DOT__busoutfifo__DOT__w_read));
    bufp->fullBit(oldp+582,((((IData)(vlSelf->main__DOT__genbus__DOT__in_stb) 
                              & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd)) 
                                 & (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow))) 
                             | ((~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_empty_n)) 
                                & (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd)))));
    bufp->fullBit(oldp+583,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__ififo_rd));
    bufp->fullCData(oldp+584,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr),7);
    bufp->fullCData(oldp+585,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr),7);
    bufp->fullCData(oldp+586,((0x7fU & ((IData)(1U) 
                                        + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_wrptr)))),7);
    bufp->fullCData(oldp+587,((0x7fU & ((IData)(1U) 
                                        + (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__r_rdptr)))),7);
    bufp->fullBit(oldp+588,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_overflow));
    bufp->fullBit(oldp+589,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow));
    bufp->fullBit(oldp+590,((1U & (~ (IData)(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__will_underflow)))));
    bufp->fullBit(oldp+591,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_write));
    bufp->fullBit(oldp+592,(vlSelf->main__DOT__genbus__DOT__INPUT_FIFO__DOT__padififo__DOT__w_read));
    bufp->fullBit(oldp+593,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb));
    bufp->fullBit(oldp+594,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_valid));
    bufp->fullCData(oldp+595,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_hexbits),6);
    bufp->fullBit(oldp+596,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_stb));
    bufp->fullBit(oldp+597,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__skd_busy));
    bufp->fullBit(oldp+598,(((IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__hx_stb) 
                             | (0U < (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len)))));
    bufp->fullQData(oldp+599,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word),36);
    bufp->fullBit(oldp+601,((0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb))));
    bufp->fullBit(oldp+602,(((IData)(vlSelf->main__DOT__genbus__DOT__in_stb) 
                             | (0U != (IData)(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb)))));
    bufp->fullCData(oldp+603,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__wr_addr),8);
    bufp->fullQData(oldp+604,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_word),36);
    bufp->fullCData(oldp+606,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cmd_addr),8);
    bufp->fullIData(oldp+607,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_addr),25);
    bufp->fullIData(oldp+608,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__w_addr),32);
    bufp->fullSData(oldp+609,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__rd_len),10);
    bufp->fullIData(oldp+610,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__cword),32);
    bufp->fullCData(oldp+611,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__GEN_COMPRESSION__DOT__unpack__DOT__r_stb),3);
    bufp->fullBit(oldp+612,((3U == (7U & (IData)((vlSelf->main__DOT__genbus__DOT__getinput__DOT__cw_word 
                                                  >> 0x21U))))));
    bufp->fullCData(oldp+613,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__r_len),3);
    bufp->fullCData(oldp+614,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__cw_len),3);
    bufp->fullCData(oldp+615,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__lastcw),2);
    bufp->fullBit(oldp+616,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__w_stb));
    bufp->fullQData(oldp+617,(vlSelf->main__DOT__genbus__DOT__getinput__DOT__formcw__DOT__shiftreg),36);
    bufp->fullIData(oldp+619,((((IData)((vlSelf->main__DOT__genbus__DOT__ififo_codword 
                                         >> 0x1fU)) 
                                << 0x1eU) | (0x3fffffffU 
                                             & (IData)(vlSelf->main__DOT__genbus__DOT__ififo_codword)))),32);
    bufp->fullCData(oldp+620,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__wb_state),2);
    bufp->fullSData(oldp+621,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_acks_needed),10);
    bufp->fullSData(oldp+622,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_len),10);
    bufp->fullBit(oldp+623,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_inc));
    bufp->fullBit(oldp+624,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__r_new_addr));
    bufp->fullBit(oldp+625,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_read_request));
    bufp->fullBit(oldp+626,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__last_ack));
    bufp->fullBit(oldp+627,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__zero_acks));
    bufp->fullIData(oldp+628,(vlSelf->main__DOT__genbus__DOT__runwb__DOT__wide_addr),32);
    bufp->fullBit(oldp+629,(vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy));
    bufp->fullBit(oldp+630,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb));
    bufp->fullBit(oldp+631,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb));
    bufp->fullBit(oldp+632,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_stb));
    bufp->fullBit(oldp+633,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_busy));
    bufp->fullBit(oldp+634,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_busy));
    bufp->fullBit(oldp+635,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy));
    bufp->fullBit(oldp+636,(((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb) 
                             | ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__aword_valid) 
                                | (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb)))));
    bufp->fullBit(oldp+637,(((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb) 
                             | (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb))));
    bufp->fullBit(oldp+638,(((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_stb) 
                             | ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__byte_busy) 
                                & ((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_out_nl)) 
                                   & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_in_nl))))));
    bufp->fullQData(oldp+639,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword),36);
    bufp->fullQData(oldp+641,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword),36);
    bufp->fullCData(oldp+643,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__dw_bits),7);
    bufp->fullCData(oldp+644,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__ln_bits),7);
    bufp->fullBit(oldp+645,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__r_active));
    bufp->fullBit(oldp+646,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__aword_valid));
    bufp->fullQData(oldp+647,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__a_addrword),36);
    bufp->fullIData(oldp+649,((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_codword)),32);
    bufp->fullCData(oldp+650,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_zcheck),4);
    bufp->fullBit(oldp+651,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy));
    bufp->fullBit(oldp+652,(((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_busy)) 
                             & (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cp_stb))));
    bufp->fullQData(oldp+653,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_word),36);
    bufp->fullSData(oldp+655,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_addr),10);
    bufp->fullBit(oldp+656,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__tbl_filled));
    bufp->fullSData(oldp+657,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__rd_addr),10);
    bufp->fullBit(oldp+658,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__pmatch));
    bufp->fullBit(oldp+659,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dmatch));
    bufp->fullBit(oldp+660,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__vaddr));
    bufp->fullIData(oldp+661,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__cword),32);
    bufp->fullSData(oldp+662,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__maddr),10);
    bufp->fullBit(oldp+663,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__matched));
    bufp->fullBit(oldp+664,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__zmatch));
    bufp->fullBit(oldp+665,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__hmatch));
    bufp->fullSData(oldp+666,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_dbld),10);
    bufp->fullCData(oldp+667,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_hlfd),3);
    bufp->fullSData(oldp+668,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__dffaddr),10);
    bufp->fullBit(oldp+669,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__clear_table));
    bufp->fullBit(oldp+670,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__addr_within_table));
    bufp->fullBit(oldp+671,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__w_match));
    bufp->fullBit(oldp+672,((1U & ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__adr_dbld) 
                                   >> 9U))));
    bufp->fullBit(oldp+673,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT____Vcellinp__GEN_IDLES__DOT__buildcw__i_tx_busy));
    bufp->fullBit(oldp+674,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_request));
    bufp->fullBit(oldp+675,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__int_sent));
    bufp->fullBit(oldp+676,(((~ (IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state)) 
                             & (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter 
                                >> 0x15U))));
    bufp->fullBit(oldp+677,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_state));
    bufp->fullIData(oldp+678,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_IDLES__DOT__buildcw__DOT__idle_counter),22);
    bufp->fullCData(oldp+679,(((0U == (7U & (IData)(
                                                    (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                     >> 0x21U))))
                                ? 1U : ((2U == (0xfU 
                                                & (IData)(
                                                          (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                           >> 0x20U))))
                                         ? 6U : (7U 
                                                 & ((3U 
                                                     == 
                                                     (0xfU 
                                                      & (IData)(
                                                                (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                                 >> 0x20U))))
                                                     ? 
                                                    ((IData)(2U) 
                                                     + 
                                                     (3U 
                                                      & (IData)(
                                                                (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                                 >> 0x1eU))))
                                                     : 
                                                    ((1U 
                                                      == 
                                                      (3U 
                                                       & (IData)(
                                                                 (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                                  >> 0x22U))))
                                                      ? 2U
                                                      : 
                                                     ((2U 
                                                       == 
                                                       (3U 
                                                        & (IData)(
                                                                  (vlSelf->main__DOT__genbus__DOT__wroutput__DOT__GEN_COMPRESSION__DOT__packit__DOT__r_cword 
                                                                   >> 0x22U))))
                                                       ? 1U
                                                       : 6U))))))),3);
    bufp->fullCData(oldp+680,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_len),3);
    bufp->fullIData(oldp+681,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__deword__DOT__r_word),30);
    bufp->fullBit(oldp+682,(((IData)(vlSelf->main__DOT__wbu_cyc) 
                             | ((IData)(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__cw_stb) 
                                | (IData)(vlSelf->main__DOT__genbus__DOT____Vcellinp__wroutput__i_bus_busy)))));
    bufp->fullBit(oldp+683,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_out_nl));
    bufp->fullBit(oldp+684,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__last_in_nl));
    bufp->fullBit(oldp+685,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__full_line));
    bufp->fullBit(oldp+686,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__r_busy));
    bufp->fullCData(oldp+687,(vlSelf->main__DOT__genbus__DOT__wroutput__DOT__linepacker__DOT__linelen),7);
    bufp->fullSData(oldp+688,(vlSelf->main__DOT__gpioi__DOT__r_gpio),16);
    bufp->fullSData(oldp+689,(vlSelf->main__DOT__gpioi__DOT__x_gpio),16);
    bufp->fullSData(oldp+690,(vlSelf->main__DOT__gpioi__DOT__q_gpio),16);
    bufp->fullBit(oldp+691,(vlSelf->main__DOT__i2ci__DOT__r_halted));
    bufp->fullBit(oldp+692,(vlSelf->main__DOT__i2ci__DOT__cpu_new_pc));
    bufp->fullIData(oldp+693,(vlSelf->main__DOT__i2ci__DOT__pf_jump_addr),28);
    bufp->fullBit(oldp+694,(vlSelf->main__DOT__i2ci__DOT__pf_valid));
    bufp->fullBit(oldp+695,(vlSelf->main__DOT__i2ci__DOT__pf_ready));
    bufp->fullCData(oldp+696,(vlSelf->main__DOT__i2ci__DOT__pf_insn),8);
    bufp->fullIData(oldp+697,(vlSelf->main__DOT__i2ci__DOT__pf_insn_addr),28);
    bufp->fullBit(oldp+698,(vlSelf->main__DOT__i2ci__DOT__pf_illegal));
    bufp->fullBit(oldp+699,(vlSelf->main__DOT__i2ci__DOT__half_valid));
    bufp->fullBit(oldp+700,(vlSelf->main__DOT__i2ci__DOT__imm_cycle));
    bufp->fullBit(oldp+701,(vlSelf->main__DOT__i2ci__DOT__insn_ready));
    bufp->fullBit(oldp+702,(vlSelf->main__DOT__i2ci__DOT__half_ready));
    bufp->fullBit(oldp+703,(vlSelf->main__DOT__i2ci__DOT__i2c_abort));
    bufp->fullBit(oldp+704,(vlSelf->main__DOT__i2ci__DOT__insn_valid));
    bufp->fullSData(oldp+705,(vlSelf->main__DOT__i2ci__DOT__insn),12);
    bufp->fullCData(oldp+706,(vlSelf->main__DOT__i2ci__DOT__half_insn),4);
    bufp->fullBit(oldp+707,(vlSelf->main__DOT__i2ci__DOT__i2c_ckedge));
    bufp->fullBit(oldp+708,(vlSelf->main__DOT__i2ci__DOT__i2c_stretch));
    bufp->fullSData(oldp+709,(vlSelf->main__DOT__i2ci__DOT__i2c_ckcount),12);
    bufp->fullSData(oldp+710,(vlSelf->main__DOT__i2ci__DOT__ckcount),12);
    bufp->fullIData(oldp+711,(vlSelf->main__DOT__i2ci__DOT__abort_address),28);
    bufp->fullIData(oldp+712,(vlSelf->main__DOT__i2ci__DOT__jump_target),28);
    bufp->fullBit(oldp+713,(vlSelf->main__DOT__i2ci__DOT__r_wait));
    bufp->fullBit(oldp+714,(vlSelf->main__DOT__i2ci__DOT__soft_halt_request));
    bufp->fullBit(oldp+715,(vlSelf->main__DOT__i2ci__DOT__r_err));
    bufp->fullBit(oldp+716,(vlSelf->main__DOT__i2ci__DOT__r_aborted));
    bufp->fullBit(oldp+717,(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__manual));
    bufp->fullBit(oldp+718,(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__sda));
    bufp->fullBit(oldp+719,(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__scl));
    bufp->fullBit(oldp+720,(((IData)(vlSelf->main__DOT__i2ci__DOT__r_halted) 
                             | (IData)(vlSelf->main__DOT__i2ci__DOT__r_wait))));
    bufp->fullBit(oldp+721,(vlSelf->main__DOT__i2ci__DOT__w_sda));
    bufp->fullBit(oldp+722,(vlSelf->main__DOT__i2ci__DOT__w_scl));
    bufp->fullBit(oldp+723,(vlSelf->main__DOT__i2ci__DOT__ovw_ready));
    bufp->fullBit(oldp+724,(vlSelf->main__DOT__i2ci__DOT__s_tvalid));
    bufp->fullSData(oldp+725,(vlSelf->main__DOT__i2ci__DOT__ovw_data),10);
    bufp->fullBit(oldp+726,(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_scl));
    bufp->fullBit(oldp+727,(vlSelf->main__DOT__i2ci__DOT__GEN_MANUAL__DOT__o_sda));
    bufp->fullBit(oldp+728,(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__mid_axis_pkt));
    bufp->fullCData(oldp+729,(vlSelf->main__DOT__i2ci__DOT__GEN_TID__DOT__r_channel),2);
    bufp->fullSData(oldp+730,((0x7ffU & (IData)(vlSelf->main__DOT__i2ci__DOT__insn))),11);
    bufp->fullBit(oldp+731,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__last_byte));
    bufp->fullBit(oldp+732,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__dir));
    bufp->fullBit(oldp+733,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__will_ack));
    bufp->fullCData(oldp+734,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__state),4);
    bufp->fullCData(oldp+735,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__nbits),3);
    bufp->fullCData(oldp+736,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__sreg),8);
    bufp->fullBit(oldp+737,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__q_scl));
    bufp->fullBit(oldp+738,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__q_sda));
    bufp->fullBit(oldp+739,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_scl));
    bufp->fullBit(oldp+740,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__ck_sda));
    bufp->fullBit(oldp+741,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__lst_scl));
    bufp->fullBit(oldp+742,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__lst_sda));
    bufp->fullBit(oldp+743,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__stop_bit));
    bufp->fullBit(oldp+744,(vlSelf->main__DOT__i2ci__DOT__u_axisi2c__DOT__channel_busy));
    bufp->fullBit(oldp+745,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__last_stb));
    bufp->fullBit(oldp+746,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__invalid_bus_cycle));
    bufp->fullWData(oldp+747,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_word),512);
    bufp->fullBit(oldp+763,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_valid));
    bufp->fullCData(oldp+764,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__inflight),2);
    bufp->fullBit(oldp+765,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__cache_illegal));
    bufp->fullBit(oldp+766,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_valid));
    bufp->fullWData(oldp+767,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__rg_insn),512);
    bufp->fullWData(oldp+783,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__i_wb_shifted),512);
    bufp->fullCData(oldp+799,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_count),7);
    bufp->fullCData(oldp+800,(vlSelf->main__DOT__i2ci__DOT__u_fetch__DOT__GEN_SUBSHIFT__DOT__r_shift),6);
    bufp->fullBit(oldp+801,(vlSelf->main__DOT__i2cscopei__DOT__read_address));
    bufp->fullSData(oldp+802,(vlSelf->main__DOT__i2cscopei__DOT__raddr),10);
    bufp->fullSData(oldp+803,(vlSelf->main__DOT__i2cscopei__DOT__waddr),10);
    bufp->fullBit(oldp+804,((1U & (~ ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                                      >> 2U)))));
    bufp->fullBit(oldp+805,((1U & ((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config) 
                                   >> 1U))));
    bufp->fullBit(oldp+806,((1U & (IData)(vlSelf->main__DOT__i2cscopei__DOT__br_config))));
    bufp->fullCData(oldp+807,(vlSelf->main__DOT__i2cscopei__DOT__br_config),3);
    bufp->fullIData(oldp+808,(vlSelf->main__DOT__i2cscopei__DOT__br_holdoff),20);
    bufp->fullIData(oldp+809,(vlSelf->main__DOT__i2cscopei__DOT__holdoff_counter),20);
    bufp->fullBit(oldp+810,(vlSelf->main__DOT__i2cscopei__DOT__dr_triggered));
    bufp->fullBit(oldp+811,(vlSelf->main__DOT__i2cscopei__DOT__dr_primed));
    bufp->fullBit(oldp+812,(vlSelf->main__DOT__i2cscopei__DOT__dw_trigger));
    bufp->fullBit(oldp+813,(vlSelf->main__DOT__i2cscopei__DOT__dr_stopped));
    bufp->fullCData(oldp+814,(vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe),5);
    bufp->fullBit(oldp+815,((1U & ((IData)(vlSelf->main__DOT__i2cscopei__DOT__dr_stop_pipe) 
                                   >> 4U))));
    bufp->fullIData(oldp+816,(vlSelf->main__DOT__i2cscopei__DOT__ck_addr),31);
    bufp->fullIData(oldp+817,(vlSelf->main__DOT__i2cscopei__DOT__qd_data),31);
    bufp->fullBit(oldp+818,(vlSelf->main__DOT__i2cscopei__DOT__dr_force_write));
    bufp->fullBit(oldp+819,(vlSelf->main__DOT__i2cscopei__DOT__dr_run_timeout));
    bufp->fullBit(oldp+820,(vlSelf->main__DOT__i2cscopei__DOT__new_data));
    bufp->fullBit(oldp+821,(vlSelf->main__DOT__i2cscopei__DOT__dr_force_inhibit));
    bufp->fullBit(oldp+822,(vlSelf->main__DOT__i2cscopei__DOT__imm_adr));
    bufp->fullBit(oldp+823,(vlSelf->main__DOT__i2cscopei__DOT__lst_adr));
    bufp->fullIData(oldp+824,(vlSelf->main__DOT__i2cscopei__DOT__lst_val),31);
    bufp->fullIData(oldp+825,(vlSelf->main__DOT__i2cscopei__DOT__imm_val),31);
    bufp->fullBit(oldp+826,(vlSelf->main__DOT__i2cscopei__DOT__record_ce));
    bufp->fullIData(oldp+827,(vlSelf->main__DOT__i2cscopei__DOT__r_data),32);
    bufp->fullBit(oldp+828,(vlSelf->main__DOT__i2cscopei__DOT__br_pre_wb_ack));
    bufp->fullSData(oldp+829,(vlSelf->main__DOT__i2cscopei__DOT__this_addr),10);
    bufp->fullIData(oldp+830,(vlSelf->main__DOT__i2cscopei__DOT__nxt_mem),32);
    bufp->fullBit(oldp+831,(vlSelf->main__DOT__i2cscopei__DOT__br_level_interrupt));
    bufp->fullCData(oldp+832,(vlSelf->main__DOT__rcv__DOT__state),4);
    bufp->fullCData(oldp+833,(vlSelf->main__DOT__rcv__DOT__baud_counter),7);
    bufp->fullBit(oldp+834,(vlSelf->main__DOT__rcv__DOT__zero_baud_counter));
    bufp->fullBit(oldp+835,(vlSelf->main__DOT__rcv__DOT__q_uart));
    bufp->fullBit(oldp+836,(vlSelf->main__DOT__rcv__DOT__qq_uart));
    bufp->fullBit(oldp+837,(vlSelf->main__DOT__rcv__DOT__ck_uart));
    bufp->fullCData(oldp+838,(vlSelf->main__DOT__rcv__DOT__chg_counter),7);
    bufp->fullBit(oldp+839,(vlSelf->main__DOT__rcv__DOT__half_baud_time));
    bufp->fullCData(oldp+840,(vlSelf->main__DOT__rcv__DOT__data_reg),8);
    bufp->fullBit(oldp+841,(vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber3));
    bufp->fullIData(oldp+842,(vlSelf->main__DOT____Vcellinp__sdioscopei____pinNumber4),31);
    bufp->fullBit(oldp+843,(vlSelf->main__DOT__sdioscopei__DOT__read_address));
    bufp->fullSData(oldp+844,(vlSelf->main__DOT__sdioscopei__DOT__raddr),12);
    bufp->fullSData(oldp+845,(vlSelf->main__DOT__sdioscopei__DOT__waddr),12);
    bufp->fullBit(oldp+846,((1U & (~ ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                                      >> 2U)))));
    bufp->fullBit(oldp+847,((1U & ((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config) 
                                   >> 1U))));
    bufp->fullBit(oldp+848,((1U & (IData)(vlSelf->main__DOT__sdioscopei__DOT__br_config))));
    bufp->fullCData(oldp+849,(vlSelf->main__DOT__sdioscopei__DOT__br_config),3);
    bufp->fullIData(oldp+850,(vlSelf->main__DOT__sdioscopei__DOT__br_holdoff),20);
    bufp->fullIData(oldp+851,(vlSelf->main__DOT__sdioscopei__DOT__holdoff_counter),20);
    bufp->fullBit(oldp+852,(vlSelf->main__DOT__sdioscopei__DOT__dr_triggered));
    bufp->fullBit(oldp+853,(vlSelf->main__DOT__sdioscopei__DOT__dr_primed));
    bufp->fullBit(oldp+854,(vlSelf->main__DOT__sdioscopei__DOT__dw_trigger));
    bufp->fullBit(oldp+855,(vlSelf->main__DOT__sdioscopei__DOT__dr_stopped));
    bufp->fullCData(oldp+856,(vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe),5);
    bufp->fullBit(oldp+857,((1U & ((IData)(vlSelf->main__DOT__sdioscopei__DOT__dr_stop_pipe) 
                                   >> 4U))));
    bufp->fullIData(oldp+858,(vlSelf->main__DOT__sdioscopei__DOT__ck_addr),31);
    bufp->fullIData(oldp+859,(vlSelf->main__DOT__sdioscopei__DOT__qd_data),31);
    bufp->fullBit(oldp+860,(vlSelf->main__DOT__sdioscopei__DOT__dr_force_write));
    bufp->fullBit(oldp+861,(vlSelf->main__DOT__sdioscopei__DOT__dr_run_timeout));
    bufp->fullBit(oldp+862,(vlSelf->main__DOT__sdioscopei__DOT__new_data));
    bufp->fullBit(oldp+863,(vlSelf->main__DOT__sdioscopei__DOT__dr_force_inhibit));
    bufp->fullBit(oldp+864,(vlSelf->main__DOT__sdioscopei__DOT__imm_adr));
    bufp->fullBit(oldp+865,(vlSelf->main__DOT__sdioscopei__DOT__lst_adr));
    bufp->fullIData(oldp+866,(vlSelf->main__DOT__sdioscopei__DOT__lst_val),31);
    bufp->fullIData(oldp+867,(vlSelf->main__DOT__sdioscopei__DOT__imm_val),31);
    bufp->fullBit(oldp+868,(vlSelf->main__DOT__sdioscopei__DOT__record_ce));
    bufp->fullIData(oldp+869,(vlSelf->main__DOT__sdioscopei__DOT__r_data),32);
    bufp->fullBit(oldp+870,(vlSelf->main__DOT__sdioscopei__DOT__br_pre_wb_ack));
    bufp->fullSData(oldp+871,(vlSelf->main__DOT__sdioscopei__DOT__this_addr),12);
    bufp->fullIData(oldp+872,(vlSelf->main__DOT__sdioscopei__DOT__nxt_mem),32);
    bufp->fullBit(oldp+873,(vlSelf->main__DOT__sdioscopei__DOT__br_level_interrupt));
    bufp->fullBit(oldp+874,(vlSelf->main__DOT__spioi__DOT__led_demo));
    bufp->fullCData(oldp+875,(vlSelf->main__DOT__spioi__DOT__r_led),8);
    bufp->fullCData(oldp+876,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__r_btn),8);
    bufp->fullCData(oldp+877,(vlSelf->main__DOT__spioi__DOT__bounced),8);
    bufp->fullCData(oldp+878,(vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__rr_sw),8);
    bufp->fullBit(oldp+879,(vlSelf->main__DOT__spioi__DOT__sw_int));
    bufp->fullBit(oldp+880,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__r_btn_int));
    bufp->fullCData(oldp+881,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__s_btn),5);
    bufp->fullCData(oldp+882,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__r_btn),5);
    bufp->fullSData(oldp+883,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__btn_pipe),10);
    bufp->fullSData(oldp+884,(vlSelf->main__DOT__spioi__DOT__GEN_SWITCHES__DOT__sw_pipe),16);
    bufp->fullCData(oldp+885,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_owner),8);
    bufp->fullBit(oldp+886,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_dir));
    bufp->fullIData(oldp+887,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_ctr),25);
    bufp->fullBit(oldp+888,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__led_clk));
    bufp->fullCData(oldp+889,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__br_ctr),5);
    bufp->fullCData(oldp+890,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__0__KET____DOT__brightness),5);
    bufp->fullCData(oldp+891,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__1__KET____DOT__brightness),5);
    bufp->fullCData(oldp+892,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__2__KET____DOT__brightness),5);
    bufp->fullCData(oldp+893,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__3__KET____DOT__brightness),5);
    bufp->fullCData(oldp+894,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__4__KET____DOT__brightness),5);
    bufp->fullCData(oldp+895,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__5__KET____DOT__brightness),5);
    bufp->fullCData(oldp+896,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__6__KET____DOT__brightness),5);
    bufp->fullCData(oldp+897,(vlSelf->main__DOT__spioi__DOT__knightrider__DOT__GEN_BRIGHTNESS__BRA__7__KET____DOT__brightness),5);
    bufp->fullSData(oldp+898,(vlSelf->main__DOT__swic__DOT__main_int_vector),15);
    bufp->fullSData(oldp+899,(vlSelf->main__DOT__swic__DOT__alt_int_vector),15);
    bufp->fullBit(oldp+900,(vlSelf->main__DOT__swic__DOT__ctri_int));
    bufp->fullBit(oldp+901,(vlSelf->main__DOT__swic__DOT__tma_int));
    bufp->fullBit(oldp+902,(vlSelf->main__DOT__swic__DOT__tmb_int));
    bufp->fullBit(oldp+903,(vlSelf->main__DOT__swic__DOT__tmc_int));
    bufp->fullBit(oldp+904,(vlSelf->main__DOT__swic__DOT__jif_int));
    bufp->fullBit(oldp+905,(vlSelf->main__DOT__swic__DOT__dmac_int));
    bufp->fullBit(oldp+906,(vlSelf->main__DOT__swic__DOT__mtc_int));
    bufp->fullBit(oldp+907,(vlSelf->main__DOT__swic__DOT__moc_int));
    bufp->fullBit(oldp+908,(vlSelf->main__DOT__swic__DOT__mpc_int));
    bufp->fullBit(oldp+909,(vlSelf->main__DOT__swic__DOT__mic_int));
    bufp->fullBit(oldp+910,(vlSelf->main__DOT__swic__DOT__utc_int));
    bufp->fullBit(oldp+911,(vlSelf->main__DOT__swic__DOT__uoc_int));
    bufp->fullBit(oldp+912,(vlSelf->main__DOT__swic__DOT__upc_int));
    bufp->fullBit(oldp+913,(vlSelf->main__DOT__swic__DOT__uic_int));
    bufp->fullIData(oldp+914,(((4U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                ? ((2U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                    ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data
                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data)
                                    : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data
                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data))
                                : ((2U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                    ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data
                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data)
                                    : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                        ? vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data
                                        : vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data)))),32);
    bufp->fullBit(oldp+915,(vlSelf->main__DOT__swic__DOT__actr_ack));
    bufp->fullBit(oldp+916,(((IData)(vlSelf->main__DOT__swic__DOT__cmd_write) 
                             | ((IData)(vlSelf->main__DOT__swic__DOT__cmd_read) 
                                | ((~ ((IData)(vlSelf->main__DOT__swic__DOT__dbg_addr) 
                                       >> 6U)) & (IData)(vlSelf->main__DOT__swic__DOT__dbg_stb))))));
    bufp->fullBit(oldp+917,(vlSelf->main__DOT__swic__DOT__sys_cyc));
    bufp->fullBit(oldp+918,(vlSelf->main__DOT__swic__DOT__sys_stb));
    bufp->fullBit(oldp+919,(vlSelf->main__DOT__swic__DOT__sys_we));
    bufp->fullCData(oldp+920,(vlSelf->main__DOT__swic__DOT__sys_addr),8);
    bufp->fullIData(oldp+921,(vlSelf->main__DOT__swic__DOT__sys_data),32);
    bufp->fullIData(oldp+922,(vlSelf->main__DOT__swic__DOT__cpu_addr),22);
    bufp->fullIData(oldp+923,(vlSelf->main__DOT__swic__DOT__sys_idata),32);
    bufp->fullBit(oldp+924,(vlSelf->main__DOT__swic__DOT__sys_ack));
    bufp->fullBit(oldp+925,(vlSelf->main__DOT__swic__DOT__sel_timer));
    bufp->fullBit(oldp+926,(vlSelf->main__DOT__swic__DOT__sel_pic));
    bufp->fullBit(oldp+927,(vlSelf->main__DOT__swic__DOT__sel_apic));
    bufp->fullBit(oldp+928,(vlSelf->main__DOT__swic__DOT__sel_watchdog));
    bufp->fullBit(oldp+929,(vlSelf->main__DOT__swic__DOT__sel_bus_watchdog));
    bufp->fullBit(oldp+930,(vlSelf->main__DOT__swic__DOT__sel_dmac));
    bufp->fullBit(oldp+931,(((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
                             & ((IData)(vlSelf->main__DOT__swic__DOT__sys_addr) 
                                >> 7U))));
    bufp->fullBit(oldp+932,(vlSelf->main__DOT__swic__DOT__dbg_cyc));
    bufp->fullBit(oldp+933,(vlSelf->main__DOT__swic__DOT__dbg_stb));
    bufp->fullBit(oldp+934,(vlSelf->main__DOT__swic__DOT__dbg_we));
    bufp->fullCData(oldp+935,(vlSelf->main__DOT__swic__DOT__dbg_addr),7);
    bufp->fullIData(oldp+936,(vlSelf->main__DOT__swic__DOT__dbg_idata),32);
    bufp->fullBit(oldp+937,(vlSelf->main__DOT__swic__DOT__dbg_ack));
    bufp->fullBit(oldp+938,(vlSelf->main__DOT__swic__DOT__dbg_stall));
    bufp->fullIData(oldp+939,(vlSelf->main__DOT__swic__DOT__dbg_odata),32);
    bufp->fullCData(oldp+940,(vlSelf->main__DOT__swic__DOT__dbg_sel),4);
    bufp->fullBit(oldp+941,(vlSelf->main__DOT__swic__DOT__no_dbg_err));
    bufp->fullBit(oldp+942,(vlSelf->main__DOT__swic__DOT__cpu_break));
    bufp->fullBit(oldp+943,(vlSelf->main__DOT__swic__DOT__dbg_cmd_write));
    bufp->fullBit(oldp+944,(vlSelf->main__DOT__swic__DOT__dbg_cpu_write));
    bufp->fullBit(oldp+945,(vlSelf->main__DOT__swic__DOT__dbg_cpu_read));
    bufp->fullBit(oldp+946,(vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__r_reset_hold));
    bufp->fullBit(oldp+947,(vlSelf->main__DOT__swic__DOT__GEN_DBG_CATCH__DOT__r_dbg_catch));
    bufp->fullBit(oldp+948,(vlSelf->main__DOT__swic__DOT__reset_request));
    bufp->fullBit(oldp+949,(((~ vlSelf->main__DOT__swic__DOT__dbg_idata) 
                             & (IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h145b7951__0))));
    bufp->fullBit(oldp+950,(vlSelf->main__DOT__swic__DOT__halt_request));
    bufp->fullBit(oldp+951,(vlSelf->main__DOT__swic__DOT__step_request));
    bufp->fullBit(oldp+952,(vlSelf->main__DOT__swic__DOT__clear_cache_request));
    bufp->fullBit(oldp+953,(vlSelf->main__DOT__swic__DOT__cmd_reset));
    bufp->fullBit(oldp+954,(vlSelf->main__DOT__swic__DOT__cmd_halt));
    bufp->fullBit(oldp+955,(vlSelf->main__DOT__swic__DOT__cmd_step));
    bufp->fullBit(oldp+956,(vlSelf->main__DOT__swic__DOT__cmd_clear_cache));
    bufp->fullBit(oldp+957,(vlSelf->main__DOT__swic__DOT__cmd_write));
    bufp->fullBit(oldp+958,(vlSelf->main__DOT__swic__DOT__cmd_read));
    bufp->fullCData(oldp+959,(vlSelf->main__DOT__swic__DOT__cmd_waddr),5);
    bufp->fullIData(oldp+960,(vlSelf->main__DOT__swic__DOT__cmd_wdata),32);
    bufp->fullCData(oldp+961,(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc),3);
    bufp->fullBit(oldp+962,((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall)))));
    bufp->fullBit(oldp+963,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall));
    bufp->fullIData(oldp+964,(((((IData)(vlSelf->main__DOT__gpio_int) 
                                 << 0x1bU) | (((IData)(vlSelf->main__DOT__i2cscope_int) 
                                               << 0x1aU) 
                                              | ((0x2000000U 
                                                  & ((~ (IData)(vlSelf->main__DOT__console__DOT__rxfifo__DOT__will_underflow)) 
                                                     << 0x19U)) 
                                                 | ((0x1000000U 
                                                     & ((~ (IData)(vlSelf->main__DOT__console__DOT__txfifo__DOT__will_overflow)) 
                                                        << 0x18U)) 
                                                    | (((IData)(vlSelf->main__DOT__emmc_int) 
                                                        << 0x17U) 
                                                       | (((IData)(vlSelf->main__DOT__sdioscope_int) 
                                                           << 0x16U) 
                                                          | (((IData)(vlSelf->main__DOT__emmcscope_int) 
                                                              << 0x15U) 
                                                             | ((IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0) 
                                                                << 0xcU)))))))) 
                               | (((IData)(vlSelf->main__DOT__swic__DOT__cpu_break) 
                                   << 0xbU) | (((IData)(vlSelf->main__DOT__swic__DOT__pic_interrupt) 
                                                << 0xaU) 
                                               | ((0x300U 
                                                   & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                                                      << 8U)) 
                                                  | (((IData)(vlSelf->main__DOT__swic__DOT__GEN_DBG_CATCH__DOT__r_dbg_catch) 
                                                      << 5U) 
                                                     | (((IData)(vlSelf->main__DOT__swic__DOT__cmd_reset) 
                                                         << 3U) 
                                                        | ((2U 
                                                            & ((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__w_dbg_stall)) 
                                                               << 1U)) 
                                                           | (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt))))))))),32);
    bufp->fullBit(oldp+965,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                                   >> 1U))));
    bufp->fullBit(oldp+966,(vlSelf->main__DOT__swic__DOT__wdt_ack));
    bufp->fullBit(oldp+967,(vlSelf->main__DOT__swic__DOT__wdt_reset));
    bufp->fullIData(oldp+968,(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value),32);
    bufp->fullBit(oldp+969,(vlSelf->main__DOT__swic__DOT__wdbus_ack));
    bufp->fullIData(oldp+970,(vlSelf->main__DOT__swic__DOT__r_wdbus_data),22);
    bufp->fullIData(oldp+971,(vlSelf->main__DOT__swic__DOT__pic_data),32);
    bufp->fullIData(oldp+972,(vlSelf->main__DOT__swic__DOT__r_wdbus_data),32);
    bufp->fullBit(oldp+973,((1U & ((~ (IData)(vlSelf->main__DOT__wbwide_zip_cyc)) 
                                   | ((IData)(vlSelf->main__DOT__wbwide_zip_stb) 
                                      | ((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                                         >> 2U))))));
    bufp->fullBit(oldp+974,(vlSelf->main__DOT__swic__DOT__wdbus_int));
    bufp->fullBit(oldp+975,(vlSelf->main__DOT__swic__DOT__cpu_pf_stall));
    bufp->fullBit(oldp+976,(vlSelf->main__DOT__swic__DOT__cpu_i_count));
    bufp->fullBit(oldp+977,(vlSelf->main__DOT__swic__DOT__dmac_stb));
    bufp->fullBit(oldp+978,(vlSelf->main__DOT__swic__DOT__dc_err));
    bufp->fullIData(oldp+979,(vlSelf->main__DOT__swic__DOT__dmac_data),32);
    bufp->fullBit(oldp+980,(vlSelf->main__DOT__swic__DOT__dmac_ack));
    bufp->fullBit(oldp+981,(vlSelf->main__DOT__swic__DOT__dc_cyc));
    bufp->fullBit(oldp+982,(vlSelf->main__DOT__swic__DOT__dc_stb));
    bufp->fullBit(oldp+983,((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner)))));
    bufp->fullBit(oldp+984,(vlSelf->main__DOT__swic__DOT__dc_stall));
    bufp->fullBit(oldp+985,(vlSelf->main__DOT__swic__DOT__dc_ack));
    bufp->fullIData(oldp+986,(((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner)
                                ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_addr
                                : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_addr)),22);
    bufp->fullWData(oldp+987,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data),512);
    bufp->fullQData(oldp+1003,(((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner)
                                 ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_sel
                                 : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_sel)),64);
    bufp->fullBit(oldp+1005,(vlSelf->main__DOT__swic__DOT__cpu_gbl_cyc));
    bufp->fullIData(oldp+1006,((((IData)(vlSelf->main__DOT__swic__DOT__alt_int_vector) 
                                 << 0x10U) | (((IData)(vlSelf->main__DOT__swic__DOT____VdfgTmp_h29ee39ef__0) 
                                               << 6U) 
                                              | (((IData)(vlSelf->main__DOT__swic__DOT__ctri_int) 
                                                  << 5U) 
                                                 | (((IData)(vlSelf->main__DOT__swic__DOT__tma_int) 
                                                     << 4U) 
                                                    | (((IData)(vlSelf->main__DOT__swic__DOT__tmb_int) 
                                                        << 3U) 
                                                       | (((IData)(vlSelf->main__DOT__swic__DOT__tmc_int) 
                                                           << 2U) 
                                                          | ((IData)(vlSelf->main__DOT__swic__DOT__jif_int) 
                                                             << 1U)))))))),32);
    bufp->fullBit(oldp+1007,(((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
                              & (IData)(vlSelf->main__DOT__swic__DOT__sel_apic))));
    bufp->fullIData(oldp+1008,(vlSelf->main__DOT__swic__DOT__ctri_data),32);
    bufp->fullBit(oldp+1009,(vlSelf->main__DOT__swic__DOT__tma_ack));
    bufp->fullBit(oldp+1010,(vlSelf->main__DOT__swic__DOT__tmb_ack));
    bufp->fullBit(oldp+1011,(vlSelf->main__DOT__swic__DOT__tmc_ack));
    bufp->fullBit(oldp+1012,(vlSelf->main__DOT__swic__DOT__jif_ack));
    bufp->fullIData(oldp+1013,((((IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                 << 0x1fU) | vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value)),32);
    bufp->fullIData(oldp+1014,((((IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                 << 0x1fU) | vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value)),32);
    bufp->fullIData(oldp+1015,((((IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                 << 0x1fU) | vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value)),32);
    bufp->fullIData(oldp+1016,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter),32);
    bufp->fullBit(oldp+1017,(((IData)(vlSelf->main__DOT__swic__DOT__sys_cyc) 
                              & ((IData)(vlSelf->main__DOT__swic__DOT__sys_stb) 
                                 & (IData)(vlSelf->main__DOT__swic__DOT__sel_pic)))));
    bufp->fullBit(oldp+1018,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner)
                               ? (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl)
                               : (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb))));
    bufp->fullBit(oldp+1019,(vlSelf->main__DOT__swic__DOT__cpu_lcl_cyc));
    bufp->fullBit(oldp+1020,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner) 
                              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl))));
    bufp->fullBit(oldp+1021,(vlSelf->main__DOT__swic__DOT__cpu_we));
    bufp->fullWData(oldp+1022,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data),512);
    bufp->fullQData(oldp+1038,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner)
                                 ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel
                                 : 0xffffffffffffffffULL)),64);
    bufp->fullWData(oldp+1040,(vlSelf->main__DOT__swic__DOT__cpu_idata),512);
    bufp->fullBit(oldp+1056,(vlSelf->main__DOT__swic__DOT__cpu_stall));
    bufp->fullBit(oldp+1057,(vlSelf->main__DOT__swic__DOT__pic_interrupt));
    bufp->fullBit(oldp+1058,(vlSelf->main__DOT__swic__DOT__cpu_ack));
    bufp->fullBit(oldp+1059,(vlSelf->main__DOT__swic__DOT__cpu_err));
    bufp->fullIData(oldp+1060,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SETDBG__DOT__r_dbg_reg),32);
    bufp->fullBit(oldp+1061,((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)) 
                                    | ((IData)(vlSelf->__VdfgTmp_h503d14d1__0) 
                                       >> 2U)))));
    bufp->fullBit(oldp+1062,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack) 
                               >> 2U) & (IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner))));
    bufp->fullBit(oldp+1063,(((IData)(vlSelf->main__DOT__swic__DOT__ext_err) 
                              & (IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner))));
    bufp->fullBit(oldp+1064,(vlSelf->main__DOT__swic__DOT__r_mmus_ack));
    bufp->fullBit(oldp+1065,(vlSelf->main__DOT__swic__DOT__ext_err));
    bufp->fullIData(oldp+1066,(((2U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                 ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                     ? vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__r_counter
                                     : (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                         << 0x1fU) 
                                        | vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value))
                                 : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))
                                     ? (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                         << 0x1fU) 
                                        | vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value)
                                     : (((IData)(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload) 
                                         << 0x1fU) 
                                        | vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value)))),32);
    bufp->fullCData(oldp+1067,(vlSelf->main__DOT__swic__DOT__w_ack_idx),3);
    bufp->fullCData(oldp+1068,(vlSelf->main__DOT__swic__DOT__ack_idx),3);
    bufp->fullBit(oldp+1069,(vlSelf->main__DOT__swic__DOT__last_sys_stb));
    bufp->fullBit(oldp+1070,(vlSelf->main__DOT__swic__DOT__cmd_read_ack));
    bufp->fullBit(oldp+1071,(vlSelf->main__DOT__swic__DOT__dbg_pre_ack));
    bufp->fullCData(oldp+1072,(vlSelf->main__DOT__swic__DOT__dbg_pre_addr),2);
    bufp->fullIData(oldp+1073,(vlSelf->main__DOT__swic__DOT__dbg_cpu_status),32);
    bufp->fullBit(oldp+1074,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_ack));
    bufp->fullBit(oldp+1075,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_ack));
    bufp->fullBit(oldp+1076,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_ack));
    bufp->fullBit(oldp+1077,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_ack));
    bufp->fullBit(oldp+1078,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_ack));
    bufp->fullBit(oldp+1079,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_ack));
    bufp->fullBit(oldp+1080,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_ack));
    bufp->fullBit(oldp+1081,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_ack));
    bufp->fullIData(oldp+1082,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mtc_data),32);
    bufp->fullIData(oldp+1083,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__moc_data),32);
    bufp->fullIData(oldp+1084,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mpc_data),32);
    bufp->fullIData(oldp+1085,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__mic_data),32);
    bufp->fullIData(oldp+1086,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__utc_data),32);
    bufp->fullIData(oldp+1087,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uoc_data),32);
    bufp->fullIData(oldp+1088,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__upc_data),32);
    bufp->fullIData(oldp+1089,(vlSelf->main__DOT__swic__DOT__ACCOUNTING_COUNTERS__DOT__uic_data),32);
    bufp->fullBit(oldp+1090,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mins_ctr____pinNumber5));
    bufp->fullBit(oldp+1091,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mmstall_ctr____pinNumber5));
    bufp->fullBit(oldp+1092,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mpstall_ctr____pinNumber5));
    bufp->fullBit(oldp+1093,((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)))));
    bufp->fullBit(oldp+1094,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__mtask_ctr____pinNumber5));
    bufp->fullBit(oldp+1095,(((IData)(vlSelf->main__DOT__swic__DOT__cpu_i_count) 
                              & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                                 >> 1U))));
    bufp->fullBit(oldp+1096,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__uins_ctr____pinNumber5));
    bufp->fullBit(oldp+1097,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__umstall_ctr____pinNumber5));
    bufp->fullBit(oldp+1098,(((IData)(vlSelf->main__DOT__swic__DOT__cpu_pf_stall) 
                              & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                                 >> 1U))));
    bufp->fullBit(oldp+1099,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__upstall_ctr____pinNumber5));
    bufp->fullBit(oldp+1100,((1U & ((~ (IData)(vlSelf->main__DOT__swic__DOT__cmd_halt)) 
                                    & ((IData)(vlSelf->main__DOT__swic__DOT__cpu_dbg_cc) 
                                       >> 1U)))));
    bufp->fullBit(oldp+1101,(vlSelf->main__DOT__swic__DOT____Vcellinp__ACCOUNTING_COUNTERS__DOT__utask_ctr____pinNumber5));
    bufp->fullBit(oldp+1102,(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_we));
    bufp->fullCData(oldp+1103,(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_addr),7);
    bufp->fullIData(oldp+1104,(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_data),32);
    bufp->fullCData(oldp+1105,(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_sel),4);
    bufp->fullCData(oldp+1106,((3U & (IData)(vlSelf->main__DOT__swic__DOT__sys_addr))),2);
    bufp->fullBit(oldp+1107,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_request));
    bufp->fullBit(oldp+1108,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_abort));
    bufp->fullBit(oldp+1109,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_busy));
    bufp->fullBit(oldp+1110,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_err));
    bufp->fullIData(oldp+1111,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_src),28);
    bufp->fullIData(oldp+1112,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_dst),28);
    bufp->fullIData(oldp+1113,((vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_addr 
                                << 6U)),28);
    bufp->fullIData(oldp+1114,((vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_addr 
                                << 6U)),28);
    bufp->fullIData(oldp+1115,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_length),28);
    bufp->fullIData(oldp+1116,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_length),28);
    bufp->fullSData(oldp+1117,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_transferlen),11);
    bufp->fullBit(oldp+1118,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__dma_trigger));
    bufp->fullBit(oldp+1119,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_request));
    bufp->fullBit(oldp+1120,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_request));
    bufp->fullBit(oldp+1121,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_busy));
    bufp->fullBit(oldp+1122,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_busy));
    bufp->fullBit(oldp+1123,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_err));
    bufp->fullBit(oldp+1124,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_err));
    bufp->fullBit(oldp+1125,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_inc));
    bufp->fullBit(oldp+1126,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_inc));
    bufp->fullCData(oldp+1127,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size),2);
    bufp->fullCData(oldp+1128,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_size),2);
    bufp->fullIData(oldp+1129,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr),28);
    bufp->fullIData(oldp+1130,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_addr),28);
    bufp->fullSData(oldp+1131,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__r_transferlen),11);
    bufp->fullBit(oldp+1132,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_cyc));
    bufp->fullBit(oldp+1133,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stb));
    bufp->fullBit(oldp+1134,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_stall));
    bufp->fullBit(oldp+1135,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_ack));
    bufp->fullBit(oldp+1136,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_err));
    bufp->fullIData(oldp+1137,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_addr),22);
    bufp->fullQData(oldp+1138,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_sel),64);
    bufp->fullBit(oldp+1140,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_valid));
    bufp->fullBit(oldp+1141,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_ready));
    bufp->fullBit(oldp+1142,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_last));
    bufp->fullWData(oldp+1143,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__sreg),512);
    bufp->fullCData(oldp+1159,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__m_bytes),7);
    bufp->fullBit(oldp+1160,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_valid));
    bufp->fullBit(oldp+1161,((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full)))));
    bufp->fullBit(oldp+1162,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last));
    __Vtemp_hd1e4c677__0[0U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U];
    __Vtemp_hd1e4c677__0[1U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U];
    __Vtemp_hd1e4c677__0[2U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U];
    __Vtemp_hd1e4c677__0[3U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U];
    __Vtemp_hd1e4c677__0[4U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U];
    __Vtemp_hd1e4c677__0[5U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U];
    __Vtemp_hd1e4c677__0[6U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U];
    __Vtemp_hd1e4c677__0[7U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U];
    __Vtemp_hd1e4c677__0[8U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U];
    __Vtemp_hd1e4c677__0[9U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U];
    __Vtemp_hd1e4c677__0[0xaU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU];
    __Vtemp_hd1e4c677__0[0xbU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU];
    __Vtemp_hd1e4c677__0[0xcU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU];
    __Vtemp_hd1e4c677__0[0xdU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU];
    __Vtemp_hd1e4c677__0[0xeU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU];
    __Vtemp_hd1e4c677__0[0xfU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU];
    bufp->fullWData(oldp+1163,(__Vtemp_hd1e4c677__0),512);
    bufp->fullCData(oldp+1179,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_bytes),7);
    bufp->fullBit(oldp+1180,((1U & (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_empty)))));
    bufp->fullBit(oldp+1181,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__tx_ready));
    bufp->fullBit(oldp+1182,((1U & (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0x10U] 
                                    >> 7U))));
    __Vtemp_h6ddae8d1__0[0U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0U];
    __Vtemp_h6ddae8d1__0[1U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[1U];
    __Vtemp_h6ddae8d1__0[2U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[2U];
    __Vtemp_h6ddae8d1__0[3U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[3U];
    __Vtemp_h6ddae8d1__0[4U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[4U];
    __Vtemp_h6ddae8d1__0[5U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[5U];
    __Vtemp_h6ddae8d1__0[6U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[6U];
    __Vtemp_h6ddae8d1__0[7U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[7U];
    __Vtemp_h6ddae8d1__0[8U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[8U];
    __Vtemp_h6ddae8d1__0[9U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[9U];
    __Vtemp_h6ddae8d1__0[0xaU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xaU];
    __Vtemp_h6ddae8d1__0[0xbU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xbU];
    __Vtemp_h6ddae8d1__0[0xcU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xcU];
    __Vtemp_h6ddae8d1__0[0xdU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xdU];
    __Vtemp_h6ddae8d1__0[0xeU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xeU];
    __Vtemp_h6ddae8d1__0[0xfU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0xfU];
    bufp->fullWData(oldp+1183,(__Vtemp_h6ddae8d1__0),512);
    bufp->fullCData(oldp+1199,((0x7fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data[0x10U])),7);
    bufp->fullBit(oldp+1200,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_full));
    bufp->fullBit(oldp+1201,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__r_empty));
    bufp->fullCData(oldp+1202,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__ign_sfifo_fill),5);
    bufp->fullBit(oldp+1203,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_valid));
    bufp->fullBit(oldp+1204,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_ready));
    bufp->fullBit(oldp+1205,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_last));
    bufp->fullWData(oldp+1206,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__sreg),512);
    bufp->fullCData(oldp+1222,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__m_bytes),7);
    bufp->fullBit(oldp+1223,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_cyc));
    bufp->fullBit(oldp+1224,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stb));
    bufp->fullBit(oldp+1225,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_stall));
    bufp->fullBit(oldp+1226,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_ack));
    bufp->fullBit(oldp+1227,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_err));
    bufp->fullIData(oldp+1228,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_addr),22);
    bufp->fullQData(oldp+1229,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_sel),64);
    bufp->fullBit(oldp+1231,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner));
    bufp->fullBit(oldp+1232,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__ALT__DOT__last_owner));
    bufp->fullBit(oldp+1233,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_trigger));
    bufp->fullBit(oldp+1234,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_err));
    bufp->fullBit(oldp+1235,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_zero_len));
    bufp->fullBit(oldp+1236,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__r_busy));
    bufp->fullCData(oldp+1237,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__int_sel),5);
    bufp->fullIData(oldp+1238,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_src),32);
    bufp->fullIData(oldp+1239,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_dst),32);
    bufp->fullIData(oldp+1240,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_len),32);
    bufp->fullIData(oldp+1241,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__next_tlen),32);
    bufp->fullIData(oldp+1242,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_controller__DOT__w_control_reg),32);
    bufp->fullCData(oldp+1243,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_dma_fsm__DOT__fsm_state),2);
    bufp->fullBit(oldp+1244,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellinp__u_sfifo__i_reset));
    bufp->fullCData(oldp+1245,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_size),7);
    bufp->fullCData(oldp+1246,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_size),7);
    bufp->fullCData(oldp+1247,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_size),7);
    bufp->fullCData(oldp+1248,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__first_size),7);
    bufp->fullIData(oldp+1249,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__next_addr),28);
    bufp->fullIData(oldp+1250,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__last_request_addr),28);
    bufp->fullCData(oldp+1251,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__subaddr),6);
    bufp->fullCData(oldp+1252,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_subaddr),6);
    bufp->fullQData(oldp+1253,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__nxtstb_sel),64);
    bufp->fullQData(oldp+1255,(((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                 ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                     ? (0x8000000000000000ULL 
                                        >> (0x3fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))
                                     : ((0x4000000000000000ULL 
                                         | ((QData)((IData)(
                                                            (1U 
                                                             & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))) 
                                            << 0x3fU)) 
                                        >> (0x3eU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)))
                                 : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                     ? ((2U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)
                                         ? ((1U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)
                                             ? (0x1000000000000000ULL 
                                                >> 
                                                (0x3cU 
                                                 & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))
                                             : (0x3000000000000000ULL 
                                                >> 
                                                (0x3cU 
                                                 & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)))
                                         : ((1U & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)
                                             ? (0x7000000000000000ULL 
                                                >> 
                                                (0x3cU 
                                                 & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))
                                             : (0xf000000000000000ULL 
                                                >> 
                                                (0x3cU 
                                                 & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))))
                                     : (0xffffffffffffffffULL 
                                        >> (0x3fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))))),64);
    bufp->fullQData(oldp+1257,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__base_sel),64);
    bufp->fullQData(oldp+1259,(((2U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                 ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                     ? (0x8000000000000000ULL 
                                        >> (0x3fU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))
                                     : (0xc000000000000000ULL 
                                        >> (0x3eU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr)))
                                 : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_size))
                                     ? (0xf000000000000000ULL 
                                        >> (0x3cU & vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_addr))
                                     : 0xffffffffffffffffULL))),64);
    bufp->fullSData(oldp+1261,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__wb_outstanding),11);
    bufp->fullCData(oldp+1262,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__fill),8);
    bufp->fullCData(oldp+1263,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__next_fill),8);
    bufp->fullSData(oldp+1264,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdstb_len),11);
    bufp->fullSData(oldp+1265,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__rdack_len),11);
    bufp->fullCData(oldp+1266,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift),6);
    __Vtemp_hc1d82fb0__1[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x20U];
    __Vtemp_hc1d82fb0__1[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x21U];
    __Vtemp_hc1d82fb0__1[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x22U];
    __Vtemp_hc1d82fb0__1[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x23U];
    __Vtemp_hc1d82fb0__1[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x24U];
    __Vtemp_hc1d82fb0__1[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x25U];
    __Vtemp_hc1d82fb0__1[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x26U];
    __Vtemp_hc1d82fb0__1[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x27U];
    __Vtemp_hc1d82fb0__1[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x28U];
    __Vtemp_hc1d82fb0__1[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x29U];
    __Vtemp_hc1d82fb0__1[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2aU];
    __Vtemp_hc1d82fb0__1[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2bU];
    __Vtemp_hc1d82fb0__1[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2cU];
    __Vtemp_hc1d82fb0__1[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2dU];
    __Vtemp_hc1d82fb0__1[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2eU];
    __Vtemp_hc1d82fb0__1[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata[0x2fU];
    VL_SHIFTL_WWI(512,512,32, __Vtemp_h6d0d1506__0, __Vtemp_hc1d82fb0__1, 
                  ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__pre_shift) 
                   << 3U));
    bufp->fullWData(oldp+1267,(__Vtemp_h6d0d1506__0),512);
    bufp->fullBit(oldp+1283,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_inc));
    bufp->fullCData(oldp+1284,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_mm2s__DOT__r_size),2);
    bufp->fullWData(oldp+1285,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg),1024);
    bufp->fullCData(oldp+1317,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__next_fill),8);
    bufp->fullCData(oldp+1318,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill),8);
    bufp->fullBit(oldp+1319,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__next_last));
    bufp->fullBit(oldp+1320,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__r_last));
    bufp->fullBit(oldp+1321,((0x40U <= (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__fill))));
    bufp->fullCData(oldp+1322,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__shift),6);
    bufp->fullWData(oldp+1323,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__s_data),512);
    bufp->fullBit(oldp+1339,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_inc));
    bufp->fullCData(oldp+1340,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_size),2);
    bufp->fullIData(oldp+1341,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_addr),29);
    bufp->fullCData(oldp+1342,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__subaddr),6);
    bufp->fullWData(oldp+1343,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_data),1024);
    bufp->fullWData(oldp+1375,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_data),512);
    bufp->fullWData(oldp+1391,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_sel),128);
    bufp->fullWData(oldp+1395,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__pre_sel),128);
    bufp->fullQData(oldp+1399,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_sel),64);
    bufp->fullBit(oldp+1401,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__r_last));
    bufp->fullSData(oldp+1402,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_outstanding),10);
    bufp->fullBit(oldp+1403,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__wb_pipeline_full));
    bufp->fullBit(oldp+1404,((1U & (vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_s2mm__DOT__next_addr 
                                    >> 0x1cU))));
    __Vtemp_h6b3f223d__0[0U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x10U];
    __Vtemp_h6b3f223d__0[1U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x11U];
    __Vtemp_h6b3f223d__0[2U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x12U];
    __Vtemp_h6b3f223d__0[3U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x13U];
    __Vtemp_h6b3f223d__0[4U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x14U];
    __Vtemp_h6b3f223d__0[5U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x15U];
    __Vtemp_h6b3f223d__0[6U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x16U];
    __Vtemp_h6b3f223d__0[7U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x17U];
    __Vtemp_h6b3f223d__0[8U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x18U];
    __Vtemp_h6b3f223d__0[9U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x19U];
    __Vtemp_h6b3f223d__0[0xaU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1aU];
    __Vtemp_h6b3f223d__0[0xbU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1bU];
    __Vtemp_h6b3f223d__0[0xcU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1cU];
    __Vtemp_h6b3f223d__0[0xdU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1dU];
    __Vtemp_h6b3f223d__0[0xeU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1eU];
    __Vtemp_h6b3f223d__0[0xfU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__sreg[0x1fU];
    __Vtemp_h6b3f223d__0[0x10U] = (((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_last) 
                                    << 7U) | (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_rxgears__DOT__m_bytes));
    bufp->fullWData(oldp+1405,(__Vtemp_h6b3f223d__0),520);
    bufp->fullWData(oldp+1422,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT____Vcellout__u_sfifo__o_data),520);
    bufp->fullWData(oldp+1439,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[0]),520);
    bufp->fullWData(oldp+1456,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[1]),520);
    bufp->fullWData(oldp+1473,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[2]),520);
    bufp->fullWData(oldp+1490,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[3]),520);
    bufp->fullWData(oldp+1507,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[4]),520);
    bufp->fullWData(oldp+1524,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[5]),520);
    bufp->fullWData(oldp+1541,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[6]),520);
    bufp->fullWData(oldp+1558,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[7]),520);
    bufp->fullWData(oldp+1575,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[8]),520);
    bufp->fullWData(oldp+1592,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[9]),520);
    bufp->fullWData(oldp+1609,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[10]),520);
    bufp->fullWData(oldp+1626,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[11]),520);
    bufp->fullWData(oldp+1643,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[12]),520);
    bufp->fullWData(oldp+1660,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[13]),520);
    bufp->fullWData(oldp+1677,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[14]),520);
    bufp->fullWData(oldp+1694,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__mem[15]),520);
    bufp->fullCData(oldp+1711,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__wr_addr),5);
    bufp->fullCData(oldp+1712,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__rd_addr),5);
    bufp->fullBit(oldp+1713,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_wr));
    bufp->fullBit(oldp+1714,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_sfifo__DOT__w_rd));
    bufp->fullBit(oldp+1715,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_last));
    bufp->fullBit(oldp+1716,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__r_next));
    bufp->fullCData(oldp+1717,(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_txgears__DOT__fill),7);
    bufp->fullCData(oldp+1718,(vlSelf->main__DOT__swic__DOT__INITIAL_RESET_HOLD__DOT__reset_counter),5);
    bufp->fullSData(oldp+1719,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_state),15);
    bufp->fullSData(oldp+1720,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_int_enable),15);
    bufp->fullBit(oldp+1721,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__r_mie));
    bufp->fullBit(oldp+1722,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__w_any));
    bufp->fullBit(oldp+1723,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__wb_write));
    bufp->fullBit(oldp+1724,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__enable_ints));
    bufp->fullBit(oldp+1725,(vlSelf->main__DOT__swic__DOT__MAIN_PIC__DOT__pic__DOT__disable_ints));
    bufp->fullSData(oldp+1726,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_state),15);
    bufp->fullSData(oldp+1727,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_int_enable),15);
    bufp->fullBit(oldp+1728,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__r_mie));
    bufp->fullBit(oldp+1729,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__w_any));
    bufp->fullBit(oldp+1730,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__wb_write));
    bufp->fullBit(oldp+1731,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__enable_ints));
    bufp->fullBit(oldp+1732,(vlSelf->main__DOT__swic__DOT__PIC_WITH_ACCOUNTING__DOT__ALT_PIC__DOT__ctri__DOT__disable_ints));
    bufp->fullBit(oldp+1733,(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner));
    bufp->fullCData(oldp+1734,((0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))),5);
    bufp->fullBit(oldp+1735,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_new_pc));
    bufp->fullBit(oldp+1736,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_clear_icache));
    bufp->fullIData(oldp+1737,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address),28);
    bufp->fullIData(oldp+1738,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__SHIFT_INSN__DOT__shifted[0xfU]),32);
    bufp->fullIData(oldp+1739,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc),28);
    bufp->fullBit(oldp+1740,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_valid));
    bufp->fullBit(oldp+1741,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_illegal));
    bufp->fullBit(oldp+1742,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_cyc));
    bufp->fullBit(oldp+1743,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stb));
    bufp->fullBit(oldp+1744,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_stall));
    bufp->fullBit(oldp+1745,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_ack));
    bufp->fullBit(oldp+1746,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_err));
    bufp->fullIData(oldp+1747,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_addr),22);
    bufp->fullBit(oldp+1748,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__CLEAR_DCACHE__DOT__r_clear_dcache));
    bufp->fullBit(oldp+1749,((0U != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock))));
    bufp->fullCData(oldp+1750,((7U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))),3);
    bufp->fullIData(oldp+1751,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr),32);
    bufp->fullIData(oldp+1752,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_lock_pc),28);
    bufp->fullIData(oldp+1753,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata),32);
    bufp->fullCData(oldp+1754,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R),5);
    bufp->fullBit(oldp+1755,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_busy));
    bufp->fullBit(oldp+1756,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_rdbusy));
    bufp->fullBit(oldp+1757,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_pipe_stalled));
    bufp->fullBit(oldp+1758,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_valid));
    bufp->fullBit(oldp+1759,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_err));
    bufp->fullCData(oldp+1760,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wreg),5);
    bufp->fullIData(oldp+1761,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_result),32);
    bufp->fullBit(oldp+1762,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_lcl));
    bufp->fullBit(oldp+1763,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stb_gbl));
    bufp->fullBit(oldp+1764,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_lcl));
    bufp->fullBit(oldp+1765,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cyc_gbl));
    bufp->fullIData(oldp+1766,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_bus_addr),22);
    bufp->fullBit(oldp+1767,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_we));
    bufp->fullBit(oldp+1768,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_stall));
    bufp->fullBit(oldp+1769,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_ack));
    bufp->fullBit(oldp+1770,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_err));
    bufp->fullQData(oldp+1771,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel),64);
    bufp->fullIData(oldp+1773,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__ik),32);
    bufp->fullBit(oldp+1774,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cyc));
    bufp->fullBit(oldp+1775,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__stb));
    bufp->fullBit(oldp+1776,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_ack));
    bufp->fullBit(oldp+1777,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__end_of_line));
    bufp->fullBit(oldp+1778,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_line_stb));
    bufp->fullBit(oldp+1779,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_gbl));
    bufp->fullBit(oldp+1780,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_wb_cyc_lcl));
    bufp->fullCData(oldp+1781,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__npending),5);
    bufp->fullCData(oldp+1782,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_v),8);
    bufp->fullIData(oldp+1783,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[0]),19);
    bufp->fullIData(oldp+1784,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[1]),19);
    bufp->fullIData(oldp+1785,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[2]),19);
    bufp->fullIData(oldp+1786,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[3]),19);
    bufp->fullIData(oldp+1787,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[4]),19);
    bufp->fullIData(oldp+1788,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[5]),19);
    bufp->fullIData(oldp+1789,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[6]),19);
    bufp->fullIData(oldp+1790,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_vtags[7]),19);
    bufp->fullBit(oldp+1791,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__set_vflag));
    bufp->fullCData(oldp+1792,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state),2);
    bufp->fullCData(oldp+1793,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_addr),6);
    bufp->fullWData(oldp+1794,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword),512);
    bufp->fullWData(oldp+1810,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword),512);
    bufp->fullBit(oldp+1826,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_gbl));
    bufp->fullBit(oldp+1827,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__lock_lcl));
    bufp->fullBit(oldp+1828,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wr));
    bufp->fullWData(oldp+1829,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wdata),512);
    bufp->fullQData(oldp+1845,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_wsel),64);
    bufp->fullCData(oldp+1847,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__c_waddr),6);
    bufp->fullIData(oldp+1848,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag),19);
    bufp->fullBit(oldp+1849,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__last_tag_valid));
    bufp->fullCData(oldp+1850,((7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                      >> 9U))),3);
    bufp->fullCData(oldp+1851,((0x3fU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                         >> 6U))),6);
    bufp->fullBit(oldp+1852,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cache_miss_inow));
    bufp->fullBit(oldp+1853,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__w_cachable));
    bufp->fullBit(oldp+1854,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__raw_cachable_address));
    bufp->fullBit(oldp+1855,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cachable));
    bufp->fullBit(oldp+1856,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_svalid));
    bufp->fullBit(oldp+1857,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_dvalid));
    bufp->fullBit(oldp+1858,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd));
    bufp->fullBit(oldp+1859,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_cache_miss));
    bufp->fullBit(oldp+1860,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_rd_pending));
    bufp->fullIData(oldp+1861,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr),22);
    bufp->fullCData(oldp+1862,((7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                                      >> 3U))),3);
    bufp->fullCData(oldp+1863,((0x3fU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr)),6);
    bufp->fullIData(oldp+1864,((0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_addr 
                                            >> 3U))),19);
    bufp->fullBit(oldp+1865,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__wr_cstb));
    bufp->fullBit(oldp+1866,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_iv));
    bufp->fullBit(oldp+1867,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__in_cache));
    bufp->fullIData(oldp+1868,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_itag),19);
    bufp->fullSData(oldp+1869,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__req_data),13);
    bufp->fullBit(oldp+1870,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__gie));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__r_svalid) {
        __Vtemp_h01ff8f7b__0[0U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0U];
        __Vtemp_h01ff8f7b__0[1U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[1U];
        __Vtemp_h01ff8f7b__0[2U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[2U];
        __Vtemp_h01ff8f7b__0[3U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[3U];
        __Vtemp_h01ff8f7b__0[4U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[4U];
        __Vtemp_h01ff8f7b__0[5U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[5U];
        __Vtemp_h01ff8f7b__0[6U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[6U];
        __Vtemp_h01ff8f7b__0[7U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[7U];
        __Vtemp_h01ff8f7b__0[8U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[8U];
        __Vtemp_h01ff8f7b__0[9U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[9U];
        __Vtemp_h01ff8f7b__0[0xaU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0xaU];
        __Vtemp_h01ff8f7b__0[0xbU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0xbU];
        __Vtemp_h01ff8f7b__0[0xcU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0xcU];
        __Vtemp_h01ff8f7b__0[0xdU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0xdU];
        __Vtemp_h01ff8f7b__0[0xeU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0xeU];
        __Vtemp_h01ff8f7b__0[0xfU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_iword[0xfU];
    } else if ((2U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__state))) {
        __Vtemp_h01ff8f7b__0[0U] = vlSelf->main__DOT__swic__DOT__cpu_idata[0U];
        __Vtemp_h01ff8f7b__0[1U] = vlSelf->main__DOT__swic__DOT__cpu_idata[1U];
        __Vtemp_h01ff8f7b__0[2U] = vlSelf->main__DOT__swic__DOT__cpu_idata[2U];
        __Vtemp_h01ff8f7b__0[3U] = vlSelf->main__DOT__swic__DOT__cpu_idata[3U];
        __Vtemp_h01ff8f7b__0[4U] = vlSelf->main__DOT__swic__DOT__cpu_idata[4U];
        __Vtemp_h01ff8f7b__0[5U] = vlSelf->main__DOT__swic__DOT__cpu_idata[5U];
        __Vtemp_h01ff8f7b__0[6U] = vlSelf->main__DOT__swic__DOT__cpu_idata[6U];
        __Vtemp_h01ff8f7b__0[7U] = vlSelf->main__DOT__swic__DOT__cpu_idata[7U];
        __Vtemp_h01ff8f7b__0[8U] = vlSelf->main__DOT__swic__DOT__cpu_idata[8U];
        __Vtemp_h01ff8f7b__0[9U] = vlSelf->main__DOT__swic__DOT__cpu_idata[9U];
        __Vtemp_h01ff8f7b__0[0xaU] = vlSelf->main__DOT__swic__DOT__cpu_idata[0xaU];
        __Vtemp_h01ff8f7b__0[0xbU] = vlSelf->main__DOT__swic__DOT__cpu_idata[0xbU];
        __Vtemp_h01ff8f7b__0[0xcU] = vlSelf->main__DOT__swic__DOT__cpu_idata[0xcU];
        __Vtemp_h01ff8f7b__0[0xdU] = vlSelf->main__DOT__swic__DOT__cpu_idata[0xdU];
        __Vtemp_h01ff8f7b__0[0xeU] = vlSelf->main__DOT__swic__DOT__cpu_idata[0xeU];
        __Vtemp_h01ff8f7b__0[0xfU] = vlSelf->main__DOT__swic__DOT__cpu_idata[0xfU];
    } else {
        __Vtemp_h01ff8f7b__0[0U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0U];
        __Vtemp_h01ff8f7b__0[1U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[1U];
        __Vtemp_h01ff8f7b__0[2U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[2U];
        __Vtemp_h01ff8f7b__0[3U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[3U];
        __Vtemp_h01ff8f7b__0[4U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[4U];
        __Vtemp_h01ff8f7b__0[5U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[5U];
        __Vtemp_h01ff8f7b__0[6U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[6U];
        __Vtemp_h01ff8f7b__0[7U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[7U];
        __Vtemp_h01ff8f7b__0[8U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[8U];
        __Vtemp_h01ff8f7b__0[9U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[9U];
        __Vtemp_h01ff8f7b__0[0xaU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0xaU];
        __Vtemp_h01ff8f7b__0[0xbU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0xbU];
        __Vtemp_h01ff8f7b__0[0xcU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0xcU];
        __Vtemp_h01ff8f7b__0[0xdU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0xdU];
        __Vtemp_h01ff8f7b__0[0xeU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0xeU];
        __Vtemp_h01ff8f7b__0[0xfU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__cached_rword[0xfU];
    }
    bufp->fullWData(oldp+1871,(__Vtemp_h01ff8f7b__0),512);
    bufp->fullWData(oldp+1887,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__pre_shifted),512);
    bufp->fullCData(oldp+1903,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel),4);
    bufp->fullQData(oldp+1904,(((0xffU == (vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr 
                                           >> 0x18U))
                                 ? ((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel)) 
                                    >> (3U & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr))
                                 : (((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__pre_sel)) 
                                     << 0x3cU) >> (0x3fU 
                                                   & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr)))),64);
    bufp->fullIData(oldp+1906,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_WIDE_BUS__DOT__pre_shift),32);
    bufp->fullWData(oldp+1907,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_WIDE_BUS__DOT__wide_preshift),512);
    bufp->fullWData(oldp+1923,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_WIDE_BUS__DOT__shifted_data),512);
    bufp->fullSData(oldp+1939,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[0]),12);
    bufp->fullSData(oldp+1940,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[1]),12);
    bufp->fullSData(oldp+1941,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[2]),12);
    bufp->fullSData(oldp+1942,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[3]),12);
    bufp->fullSData(oldp+1943,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[4]),12);
    bufp->fullSData(oldp+1944,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[5]),12);
    bufp->fullSData(oldp+1945,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[6]),12);
    bufp->fullSData(oldp+1946,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[7]),12);
    bufp->fullSData(oldp+1947,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[8]),12);
    bufp->fullSData(oldp+1948,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[9]),12);
    bufp->fullSData(oldp+1949,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[10]),12);
    bufp->fullSData(oldp+1950,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[11]),12);
    bufp->fullSData(oldp+1951,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[12]),12);
    bufp->fullSData(oldp+1952,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[13]),12);
    bufp->fullSData(oldp+1953,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[14]),12);
    bufp->fullSData(oldp+1954,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__fifo_data[15]),12);
    bufp->fullCData(oldp+1955,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__wraddr),5);
    bufp->fullCData(oldp+1956,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__OPT_PIPE_FIFO__DOT__rdaddr),5);
    bufp->fullIData(oldp+1957,((0xfffffffU & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr)),28);
    bufp->fullBit(oldp+1958,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v));
    if (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__isrc) {
        __Vtemp_he3c3974d__0[0U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0U];
        __Vtemp_he3c3974d__0[1U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[1U];
        __Vtemp_he3c3974d__0[2U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[2U];
        __Vtemp_he3c3974d__0[3U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[3U];
        __Vtemp_he3c3974d__0[4U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[4U];
        __Vtemp_he3c3974d__0[5U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[5U];
        __Vtemp_he3c3974d__0[6U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[6U];
        __Vtemp_he3c3974d__0[7U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[7U];
        __Vtemp_he3c3974d__0[8U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[8U];
        __Vtemp_he3c3974d__0[9U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[9U];
        __Vtemp_he3c3974d__0[0xaU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0xaU];
        __Vtemp_he3c3974d__0[0xbU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0xbU];
        __Vtemp_he3c3974d__0[0xcU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0xcU];
        __Vtemp_he3c3974d__0[0xdU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0xdU];
        __Vtemp_he3c3974d__0[0xeU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0xeU];
        __Vtemp_he3c3974d__0[0xfU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache[0xfU];
    } else {
        __Vtemp_he3c3974d__0[0U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0U];
        __Vtemp_he3c3974d__0[1U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[1U];
        __Vtemp_he3c3974d__0[2U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[2U];
        __Vtemp_he3c3974d__0[3U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[3U];
        __Vtemp_he3c3974d__0[4U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[4U];
        __Vtemp_he3c3974d__0[5U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[5U];
        __Vtemp_he3c3974d__0[6U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[6U];
        __Vtemp_he3c3974d__0[7U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[7U];
        __Vtemp_he3c3974d__0[8U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[8U];
        __Vtemp_he3c3974d__0[9U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[9U];
        __Vtemp_he3c3974d__0[0xaU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0xaU];
        __Vtemp_he3c3974d__0[0xbU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0xbU];
        __Vtemp_he3c3974d__0[0xcU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0xcU];
        __Vtemp_he3c3974d__0[0xdU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0xdU];
        __Vtemp_he3c3974d__0[0xeU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0xeU];
        __Vtemp_he3c3974d__0[0xfU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache[0xfU];
    }
    bufp->fullWData(oldp+1959,(__Vtemp_he3c3974d__0),512);
    bufp->fullSData(oldp+1975,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[0]),16);
    bufp->fullSData(oldp+1976,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[1]),16);
    bufp->fullSData(oldp+1977,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[2]),16);
    bufp->fullSData(oldp+1978,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[3]),16);
    bufp->fullSData(oldp+1979,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[4]),16);
    bufp->fullSData(oldp+1980,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[5]),16);
    bufp->fullSData(oldp+1981,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[6]),16);
    bufp->fullSData(oldp+1982,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__cache_tags[7]),16);
    bufp->fullCData(oldp+1983,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__valid_mask),8);
    bufp->fullBit(oldp+1984,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v_from_pc));
    bufp->fullBit(oldp+1985,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_v_from_last));
    bufp->fullBit(oldp+1986,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__rvsrc));
    bufp->fullBit(oldp+1987,((((0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address 
                                            >> 9U)) 
                               == (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                                               >> 9U))) 
                              & ((vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__tag_lookup 
                                  == (0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address 
                                                  >> 9U))) 
                                 & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__valid_mask) 
                                    >> (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address 
                                              >> 9U)))))));
    bufp->fullBit(oldp+1988,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_v_from_last));
    bufp->fullIData(oldp+1989,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc),28);
    bufp->fullCData(oldp+1990,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__wraddr),6);
    bufp->fullIData(oldp+1991,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__pc_tag_lookup),19);
    bufp->fullIData(oldp+1992,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_tag_lookup),19);
    bufp->fullIData(oldp+1993,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__tag_lookup),19);
    bufp->fullIData(oldp+1994,((0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address 
                                            >> 9U))),19);
    bufp->fullIData(oldp+1995,((0x7ffffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                                            >> 9U))),19);
    bufp->fullBit(oldp+1996,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_valid));
    bufp->fullIData(oldp+1997,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__illegal_cache),19);
    bufp->fullWData(oldp+1998,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc_cache),512);
    bufp->fullWData(oldp+2014,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_last_cache),512);
    bufp->fullBit(oldp+2030,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__isrc));
    bufp->fullCData(oldp+2031,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__delay),2);
    bufp->fullBit(oldp+2032,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__svmask));
    bufp->fullBit(oldp+2033,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_ack));
    bufp->fullBit(oldp+2034,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__needload));
    bufp->fullBit(oldp+2035,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__last_addr));
    bufp->fullBit(oldp+2036,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__bus_abort));
    bufp->fullCData(oldp+2037,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__saddr),3);
    bufp->fullBit(oldp+2038,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__w_invalidate_result));
    bufp->fullCData(oldp+2039,((7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__pf_request_address 
                                      >> 9U))),3);
    bufp->fullCData(oldp+2040,((7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__lastpc 
                                      >> 9U))),3);
    bufp->fullWData(oldp+2041,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__SHIFT_INSN__DOT__shifted),512);
    bufp->fullCData(oldp+2057,((0xfU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__r_pc 
                                        >> 2U))),4);
    bufp->fullBit(oldp+2058,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner));
    bufp->fullIData(oldp+2059,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[0]),32);
    bufp->fullIData(oldp+2060,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[1]),32);
    bufp->fullIData(oldp+2061,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[2]),32);
    bufp->fullIData(oldp+2062,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[3]),32);
    bufp->fullIData(oldp+2063,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[4]),32);
    bufp->fullIData(oldp+2064,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[5]),32);
    bufp->fullIData(oldp+2065,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[6]),32);
    bufp->fullIData(oldp+2066,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[7]),32);
    bufp->fullIData(oldp+2067,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[8]),32);
    bufp->fullIData(oldp+2068,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[9]),32);
    bufp->fullIData(oldp+2069,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[10]),32);
    bufp->fullIData(oldp+2070,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[11]),32);
    bufp->fullIData(oldp+2071,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[12]),32);
    bufp->fullIData(oldp+2072,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[13]),32);
    bufp->fullIData(oldp+2073,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[14]),32);
    bufp->fullIData(oldp+2074,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[15]),32);
    bufp->fullIData(oldp+2075,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[16]),32);
    bufp->fullIData(oldp+2076,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[17]),32);
    bufp->fullIData(oldp+2077,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[18]),32);
    bufp->fullIData(oldp+2078,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[19]),32);
    bufp->fullIData(oldp+2079,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[20]),32);
    bufp->fullIData(oldp+2080,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[21]),32);
    bufp->fullIData(oldp+2081,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[22]),32);
    bufp->fullIData(oldp+2082,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[23]),32);
    bufp->fullIData(oldp+2083,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[24]),32);
    bufp->fullIData(oldp+2084,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[25]),32);
    bufp->fullIData(oldp+2085,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[26]),32);
    bufp->fullIData(oldp+2086,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[27]),32);
    bufp->fullIData(oldp+2087,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[28]),32);
    bufp->fullIData(oldp+2088,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[29]),32);
    bufp->fullIData(oldp+2089,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[30]),32);
    bufp->fullIData(oldp+2090,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset[31]),32);
    bufp->fullCData(oldp+2091,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__flags),4);
    bufp->fullCData(oldp+2092,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__iflags),4);
    bufp->fullSData(oldp+2093,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_uflags),16);
    bufp->fullSData(oldp+2094,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_iflags),16);
    bufp->fullBit(oldp+2095,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__break_en));
    bufp->fullBit(oldp+2096,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__user_step));
    bufp->fullBit(oldp+2097,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__sleep));
    bufp->fullBit(oldp+2098,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_halted));
    bufp->fullBit(oldp+2099,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_BREAK__DOT__r_break_pending));
    bufp->fullBit(oldp+2100,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_trap));
    bufp->fullBit(oldp+2101,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie));
    bufp->fullBit(oldp+2102,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_TRAP_N_UBREAK__DOT__r_ubreak));
    bufp->fullBit(oldp+2103,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pending_interrupt));
    bufp->fullBit(oldp+2104,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_user_stepped));
    bufp->fullBit(oldp+2105,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__step));
    bufp->fullBit(oldp+2106,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_ILLEGAL_INSN__DOT__r_ill_err_u));
    bufp->fullBit(oldp+2107,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ill_err_i));
    bufp->fullBit(oldp+2108,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ibus_err_flag));
    bufp->fullBit(oldp+2109,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_BUSERR__DOT__r_ubus_err_flag));
    bufp->fullBit(oldp+2110,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__r_idiv_err_flag));
    bufp->fullBit(oldp+2111,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVERR__DOT__USER_DIVERR__DOT__r_udiv_err_flag));
    bufp->fullBit(oldp+2112,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_IHALT_PHASE__DOT__r_ihalt_phase));
    bufp->fullBit(oldp+2113,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_UHALT_PHASE__DOT__r_uhalt_phase));
    bufp->fullBit(oldp+2114,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__master_ce));
    bufp->fullIData(oldp+2115,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__pf_pc),28);
    bufp->fullBit(oldp+2116,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__new_pc));
    bufp->fullCData(oldp+2117,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_opn),4);
    bufp->fullBit(oldp+2118,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase));
    bufp->fullCData(oldp+2119,((0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A))),5);
    bufp->fullCData(oldp+2120,((0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))),5);
    bufp->fullCData(oldp+2121,((0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R))),5);
    bufp->fullCData(oldp+2122,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preA),5);
    bufp->fullCData(oldp+2123,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_preB),5);
    bufp->fullBit(oldp+2124,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                                    >> 6U))));
    bufp->fullBit(oldp+2125,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                                    >> 6U))));
    bufp->fullBit(oldp+2126,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A) 
                                    >> 5U))));
    bufp->fullBit(oldp+2127,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B) 
                                    >> 5U))));
    bufp->fullBit(oldp+2128,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R) 
                                    >> 6U))));
    bufp->fullBit(oldp+2129,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R) 
                                    >> 5U))));
    bufp->fullCData(oldp+2130,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_F),4);
    bufp->fullBit(oldp+2131,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wR));
    bufp->fullBit(oldp+2132,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rA));
    bufp->fullBit(oldp+2133,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_rB));
    bufp->fullBit(oldp+2134,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_ALU));
    bufp->fullBit(oldp+2135,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_M));
    bufp->fullBit(oldp+2136,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_DIV));
    bufp->fullBit(oldp+2137,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_FP));
    bufp->fullBit(oldp+2138,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_wF));
    bufp->fullBit(oldp+2139,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_break));
    bufp->fullBit(oldp+2140,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_lock));
    bufp->fullBit(oldp+2141,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_pipe));
    bufp->fullBit(oldp+2142,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_ljmp));
    bufp->fullBit(oldp+2143,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_valid));
    bufp->fullIData(oldp+2144,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_I),32);
    bufp->fullBit(oldp+2145,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_zI));
    bufp->fullBit(oldp+2146,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_illegal));
    bufp->fullBit(oldp+2147,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch));
    bufp->fullBit(oldp+2148,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_early_branch_stb));
    bufp->fullIData(oldp+2149,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_EARLY_BRANCH_LOGIC__DOT__r_branch_pc),28);
    bufp->fullBit(oldp+2150,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_prelock_stall));
    bufp->fullBit(oldp+2151,((1U >= (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock))));
    bufp->fullBit(oldp+2152,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_cc_invalid_for_dcd));
    bufp->fullBit(oldp+2153,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_pending_sreg_write));
    bufp->fullBit(oldp+2154,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_mem));
    bufp->fullBit(oldp+2155,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_alu));
    bufp->fullBit(oldp+2156,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_div));
    bufp->fullBit(oldp+2157,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid_fpu));
    bufp->fullCData(oldp+2158,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn),4);
    bufp->fullBit(oldp+2159,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_Rcc));
    bufp->fullCData(oldp+2160,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Aid),5);
    bufp->fullCData(oldp+2161,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_Bid),5);
    bufp->fullBit(oldp+2162,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rA));
    bufp->fullBit(oldp+2163,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_rB));
    bufp->fullIData(oldp+2164,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_Av),32);
    bufp->fullIData(oldp+2165,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_Bv),32);
    bufp->fullIData(oldp+2166,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_OP_PC__DOT__r_op_pc),28);
    bufp->fullIData(oldp+2167,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Av),32);
    bufp->fullIData(oldp+2168,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Bv),32);
    bufp->fullIData(oldp+2169,(((2U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bisrc))
                                 ? ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bisrc))
                                     ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Bv
                                     : (0xeb800000U 
                                        | ((0x7f0000U 
                                            & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_Bv) 
                                           | ((0x10U 
                                               & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B))
                                               ? (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_uflags)
                                               : (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_iflags)))))
                                 : ((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bisrc))
                                     ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_gpreg_vl
                                     : 0U))),32);
    bufp->fullBit(oldp+2170,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_WR__DOT__r_op_wR));
    bufp->fullBit(oldp+2171,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_wF));
    bufp->fullCData(oldp+2172,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie)
                                 ? (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_hefd95ffe__0)
                                 : (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_hb0e009d2__0))),4);
    bufp->fullCData(oldp+2173,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_F),7);
    bufp->fullCData(oldp+2174,(((0x80U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_F) 
                                          << 4U)) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_F))),8);
    bufp->fullBit(oldp+2175,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OPT_CIS_OP_PHASE__DOT__r_op_phase));
    bufp->fullBit(oldp+2176,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_PIPE__DOT__r_op_pipe));
    bufp->fullBit(oldp+2177,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_op_break));
    bufp->fullBit(oldp+2178,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_op_valid));
    bufp->fullBit(oldp+2179,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_illegal));
    bufp->fullBit(oldp+2180,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OPLOCK__DOT__r_op_lock));
    bufp->fullIData(oldp+2181,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PC__DOT__r_alu_pc),28);
    bufp->fullCData(oldp+2182,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_reg),5);
    bufp->fullBit(oldp+2183,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_alu_pc_valid));
    bufp->fullBit(oldp+2184,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__mem_pc_valid));
    bufp->fullBit(oldp+2185,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_pc_valid));
    bufp->fullBit(oldp+2186,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_ALU_PHASE__DOT__r_alu_phase));
    bufp->fullIData(oldp+2187,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result),32);
    bufp->fullCData(oldp+2188,(((((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__set_ovfl) 
                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0)) 
                                 << 3U) | ((4U & ((4U 
                                                   & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result 
                                                      >> 0x1dU)) 
                                                  ^ 
                                                  (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__keep_sgn_on_ovfl) 
                                                    & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0)) 
                                                   << 2U))) 
                                           | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__c) 
                                               << 1U) 
                                              | (0U 
                                                 == vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result))))),4);
    bufp->fullBit(oldp+2189,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_valid));
    bufp->fullBit(oldp+2190,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__r_busy));
    bufp->fullBit(oldp+2191,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__set_cond));
    bufp->fullBit(oldp+2192,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_wR));
    bufp->fullBit(oldp+2193,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_wF));
    bufp->fullBit(oldp+2194,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_ALU_ILLEGAL__DOT__r_alu_illegal));
    bufp->fullBit(oldp+2195,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_error));
    bufp->fullBit(oldp+2196,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_busy));
    bufp->fullBit(oldp+2197,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_valid));
    bufp->fullIData(oldp+2198,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result),32);
    bufp->fullCData(oldp+2199,(((4U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                                       >> 0x1dU)) | 
                                (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_c) 
                                  << 1U) | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_z)))),4);
    bufp->fullBit(oldp+2200,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbgv));
    bufp->fullBit(oldp+2201,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_clear_pipe));
    bufp->fullIData(oldp+2202,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dbg_val),32);
    bufp->fullIData(oldp+2203,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__debug_pc),32);
    bufp->fullBit(oldp+2204,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__r_dbg_stall));
    bufp->fullBit(oldp+2205,((0xfU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))));
    bufp->fullBit(oldp+2206,((0xeU == (0xfU & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id)))));
    bufp->fullBit(oldp+2207,((0xeU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id))));
    bufp->fullBit(oldp+2208,((0x1eU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id))));
    bufp->fullBit(oldp+2209,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_ce));
    bufp->fullBit(oldp+2210,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_flags_ce));
    bufp->fullCData(oldp+2211,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_flags),4);
    bufp->fullCData(oldp+2212,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_index),3);
    bufp->fullCData(oldp+2213,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_reg_id),5);
    bufp->fullIData(oldp+2214,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_gpreg_vl),32);
    bufp->fullIData(oldp+2215,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__wr_spreg_vl),32);
    bufp->fullBit(oldp+2216,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_switch_to_interrupt));
    bufp->fullBit(oldp+2217,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__w_release_from_interrupt));
    bufp->fullIData(oldp+2218,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ipc),28);
    bufp->fullIData(oldp+2219,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_USER_PC__DOT__r_upc),28);
    bufp->fullBit(oldp+2220,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__last_write_to_cc));
    bufp->fullBit(oldp+2221,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____VdfgTmp_ha62fb8d9__0) 
                              | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__last_write_to_cc))));
    bufp->fullCData(oldp+2222,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_R),7);
    bufp->fullCData(oldp+2223,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_A),7);
    bufp->fullCData(oldp+2224,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_full_B),7);
    bufp->fullCData(oldp+2225,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__bisrc),2);
    bufp->fullBit(oldp+2226,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim));
    bufp->fullIData(oldp+2227,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__r_alu_sim_immv),23);
    bufp->fullCData(oldp+2228,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__ALU_SIM__DOT__regid),5);
    bufp->fullCData(oldp+2229,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__BUSLOCK__DOT__r_bus_lock),2);
    bufp->fullBit(oldp+2230,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__doalu__i_reset));
    bufp->fullBit(oldp+2231,((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))));
    bufp->fullBit(oldp+2232,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_busy));
    bufp->fullIData(oldp+2233,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_divisor),32);
    bufp->fullQData(oldp+2234,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_dividend),63);
    bufp->fullQData(oldp+2236,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__diff),33);
    bufp->fullBit(oldp+2238,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_sign));
    bufp->fullBit(oldp+2239,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__pre_sign));
    bufp->fullBit(oldp+2240,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_z));
    bufp->fullBit(oldp+2241,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_c));
    bufp->fullBit(oldp+2242,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__last_bit));
    bufp->fullCData(oldp+2243,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__r_bit),5);
    bufp->fullBit(oldp+2244,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__DIVIDE__DOT__thedivide__DOT__zero_divisor));
    bufp->fullBit(oldp+2245,((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__div_result 
                              >> 0x1fU)));
    bufp->fullBit(oldp+2246,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PENDING_INTERRUPT__DOT__r_pending_interrupt));
    bufp->fullBit(oldp+2247,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_stb));
    bufp->fullIData(oldp+2248,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_addr),28);
    bufp->fullIData(oldp+2249,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_PROFILER__DOT__prof_ticks),32);
    bufp->fullBit(oldp+2250,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim));
    bufp->fullIData(oldp+2251,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_SIM__DOT__r_op_sim_immv),23);
    bufp->fullIData(oldp+2252,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__regset
                               [(0x1fU & (IData)(vlSelf->main__DOT__swic__DOT__dbg_addr))]),32);
    bufp->fullIData(oldp+2253,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_brev_result),32);
    bufp->fullBit(oldp+2254,((0U == vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result)));
    bufp->fullBit(oldp+2255,((vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_result 
                              >> 0x1fU)));
    bufp->fullBit(oldp+2256,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__set_ovfl) 
                              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0))));
    bufp->fullBit(oldp+2257,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__keep_sgn_on_ovfl) 
                              & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT____VdfgTmp_heed50945__0))));
    bufp->fullBit(oldp+2258,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__c));
    bufp->fullBit(oldp+2259,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__pre_sign));
    bufp->fullBit(oldp+2260,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__set_ovfl));
    bufp->fullBit(oldp+2261,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__keep_sgn_on_ovfl));
    bufp->fullQData(oldp+2262,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_lsr_result),33);
    bufp->fullQData(oldp+2264,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_asr_result),33);
    bufp->fullQData(oldp+2266,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__w_lsl_result),33);
    bufp->fullQData(oldp+2268,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__mpy_result),64);
    bufp->fullBit(oldp+2270,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_hi));
    bufp->fullBit(oldp+2271,((1U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe))));
    bufp->fullBit(oldp+2272,((1U & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe) 
                                    >> 1U))));
    bufp->fullQData(oldp+2273,(((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata)) 
                                << 1U)),33);
    bufp->fullQData(oldp+2275,((0x1ffffffffULL & VL_SHIFTRS_QQI(33,33,5, 
                                                                ((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_wdata)) 
                                                                 << 1U), 
                                                                (0x1fU 
                                                                 & vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_cpu_addr)))),33);
    bufp->fullCData(oldp+2277,((3U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__FWD_OPERATION__DOT__r_op_opn))),2);
    bufp->fullQData(oldp+2278,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_smpy_result),64);
    bufp->fullQData(oldp+2280,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_umpy_result),64);
    bufp->fullIData(oldp+2282,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_a_input),32);
    bufp->fullIData(oldp+2283,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_b_input),32);
    bufp->fullCData(oldp+2284,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__mpypipe),2);
    bufp->fullCData(oldp+2285,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_sgn),2);
    bufp->fullQData(oldp+2286,((((QData)((IData)((- (IData)(
                                                            (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_a_input 
                                                             >> 0x1fU))))) 
                                 << 0x20U) | (QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_a_input)))),64);
    bufp->fullQData(oldp+2288,((((QData)((IData)((- (IData)(
                                                            (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_b_input 
                                                             >> 0x1fU))))) 
                                 << 0x20U) | (QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_b_input)))),64);
    bufp->fullQData(oldp+2290,((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_a_input))),64);
    bufp->fullQData(oldp+2292,((QData)((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__doalu__DOT__thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT__r_mpy_b_input))),64);
    bufp->fullBit(oldp+2294,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT____Vcellinp__instruction_decoder__i_reset));
    bufp->fullCData(oldp+2295,((0x1fU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                         >> 0x16U))),5);
    bufp->fullBit(oldp+2296,((0xcU == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                               >> 1U)))));
    bufp->fullBit(oldp+2297,((0xdU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op))));
    bufp->fullBit(oldp+2298,((8U == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                             >> 1U)))));
    bufp->fullBit(oldp+2299,((9U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op))));
    bufp->fullBit(oldp+2300,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_ALU));
    bufp->fullBit(oldp+2301,((8U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op))));
    bufp->fullBit(oldp+2302,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_noop));
    bufp->fullBit(oldp+2303,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_lock));
    bufp->fullBit(oldp+2304,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
                              & (0x7800000U == (0x7c00000U 
                                                & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword)))));
    bufp->fullBit(oldp+2305,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
                              & (0x7000000U == (0x7c00000U 
                                                & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword)))));
    bufp->fullBit(oldp+2306,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special));
    bufp->fullBit(oldp+2307,((2U == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op))));
    bufp->fullBit(oldp+2308,(((5U == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                              >> 1U))) 
                              | (0xcU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)))));
    bufp->fullBit(oldp+2309,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_pc));
    bufp->fullBit(oldp+2310,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_dcdR_cc));
    bufp->fullBit(oldp+2311,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB) 
                              & (0xfU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h20660d0e__0)))));
    bufp->fullBit(oldp+2312,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB) 
                              & (0xeU == (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h20660d0e__0)))));
    bufp->fullCData(oldp+2313,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h9ed30f6d__0)
                                 ? 8U : (((0U == (7U 
                                                  & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                     >> 0x13U))) 
                                          << 3U) | 
                                         (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                >> 0x13U))))),4);
    bufp->fullBit(oldp+2314,(((8U == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                              >> 1U))) 
                              | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_h9ed30f6d__0) 
                                  | (0U == (7U & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                  >> 0x13U)))) 
                                 & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_he52a0fcf__0) 
                                    | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_ALU) 
                                       & ((0xdU != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                          & ((9U != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                             & ((8U 
                                                 != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                                & (7U 
                                                   != 
                                                   (7U 
                                                    & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                       >> 0x1cU))))))))))));
    bufp->fullBit(oldp+2315,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_mem));
    bufp->fullBit(oldp+2316,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_sto));
    bufp->fullBit(oldp+2317,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_div));
    bufp->fullBit(oldp+2318,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_fpu));
    bufp->fullBit(oldp+2319,((1U & (~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_sto) 
                                       | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
                                          | (8U == 
                                             (0xfU 
                                              & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                                 >> 1U)))))))));
    bufp->fullBit(oldp+2320,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT____VdfgTmp_he52a0fcf__0) 
                              | (((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_ALU) 
                                  & ((8U != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)) 
                                     & (0xdU != (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op)))) 
                                 | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_sto) 
                                    | (8U == (0xfU 
                                              & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                                 >> 1U))))))));
    bufp->fullBit(oldp+2321,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_rB));
    bufp->fullBit(oldp+2322,(((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_sto) 
                              | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_special) 
                                 | (8U == (0xfU & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op) 
                                                   >> 1U)))))));
    bufp->fullBit(oldp+2323,((0x7c87c000U == vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword)));
    bufp->fullBit(oldp+2324,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_ljmp));
    bufp->fullIData(oldp+2325,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword),32);
    bufp->fullBit(oldp+2326,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__pf_valid));
    bufp->fullSData(oldp+2327,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_nxt_half),15);
    bufp->fullCData(oldp+2328,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_cis_op),5);
    bufp->fullIData(oldp+2329,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__r_I),23);
    bufp->fullIData(oldp+2330,((0x7fffffU & ((2U & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_immsrc))
                                              ? ((1U 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_immsrc))
                                                  ? 
                                                 ((0x7fc000U 
                                                   & ((- (IData)(
                                                                 (1U 
                                                                  & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                                     >> 0xdU)))) 
                                                      << 0xeU)) 
                                                  | (0x3fffU 
                                                     & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword))
                                                  : 
                                                 ((0x7c0000U 
                                                   & ((- (IData)(
                                                                 (1U 
                                                                  & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                                     >> 0x11U)))) 
                                                      << 0x12U)) 
                                                  | (0x3ffffU 
                                                     & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword)))
                                              : ((1U 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_immsrc))
                                                  ? 
                                                 ((0x7fe000U 
                                                   & ((- (IData)(
                                                                 (1U 
                                                                  & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                                                     >> 0xcU)))) 
                                                      << 0xdU)) 
                                                  | (0x1fffU 
                                                     & vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword))
                                                  : vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword)))),23);
    bufp->fullIData(oldp+2331,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_I),23);
    bufp->fullBit(oldp+2332,((0U == vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_I)));
    bufp->fullCData(oldp+2333,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__w_immsrc),2);
    bufp->fullBit(oldp+2334,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_OPIPE__DOT__r_insn_is_pipeable));
    bufp->fullCData(oldp+2335,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_IMMEDIATE__DOT__w_halfI),8);
    bufp->fullCData(oldp+2336,((0xffU & (vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__iword 
                                         >> 0x10U))),8);
    bufp->fullBit(oldp+2337,(((~ (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__GEN_CIS_PHASE__DOT__r_phase)) 
                              & (IData)((0x78800000U 
                                         == (0xfffc0000U 
                                             & vlSelf->main__DOT__swic__DOT__thecpu__DOT__PFCACHE__DOT__pf__DOT__SHIFT_INSN__DOT__shifted[0xfU]))))));
    bufp->fullBit(oldp+2338,(vlSelf->main__DOT__swic__DOT____Vcellinp__u_jiffies__i_wb_stb));
    bufp->fullBit(oldp+2339,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_set));
    bufp->fullBit(oldp+2340,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_set));
    bufp->fullBit(oldp+2341,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_now));
    bufp->fullIData(oldp+2342,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__int_when),32);
    bufp->fullIData(oldp+2343,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__new_when),32);
    bufp->fullIData(oldp+2344,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_wb),32);
    bufp->fullIData(oldp+2345,(vlSelf->main__DOT__swic__DOT__u_jiffies__DOT__till_when),32);
    bufp->fullBit(oldp+2346,(vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_a__i_wb_stb));
    bufp->fullBit(oldp+2347,(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_running));
    bufp->fullBit(oldp+2348,(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_zero));
    bufp->fullIData(oldp+2349,(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__r_value),31);
    bufp->fullBit(oldp+2350,(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__wb_write));
    bufp->fullBit(oldp+2351,(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_auto_reload));
    bufp->fullIData(oldp+2352,(vlSelf->main__DOT__swic__DOT__u_timer_a__DOT__GEN_RELOAD__DOT__r_interval_count),31);
    bufp->fullBit(oldp+2353,(vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_b__i_wb_stb));
    bufp->fullBit(oldp+2354,(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_running));
    bufp->fullBit(oldp+2355,(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_zero));
    bufp->fullIData(oldp+2356,(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__r_value),31);
    bufp->fullBit(oldp+2357,(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__wb_write));
    bufp->fullBit(oldp+2358,(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_auto_reload));
    bufp->fullIData(oldp+2359,(vlSelf->main__DOT__swic__DOT__u_timer_b__DOT__GEN_RELOAD__DOT__r_interval_count),31);
    bufp->fullBit(oldp+2360,(vlSelf->main__DOT__swic__DOT____Vcellinp__u_timer_c__i_wb_stb));
    bufp->fullBit(oldp+2361,(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_running));
    bufp->fullBit(oldp+2362,(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_zero));
    bufp->fullIData(oldp+2363,(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__r_value),31);
    bufp->fullBit(oldp+2364,(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__wb_write));
    bufp->fullBit(oldp+2365,(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_auto_reload));
    bufp->fullIData(oldp+2366,(vlSelf->main__DOT__swic__DOT__u_timer_c__DOT__GEN_RELOAD__DOT__r_interval_count),31);
    bufp->fullBit(oldp+2367,(vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchbus____pinNumber2));
    bufp->fullSData(oldp+2368,(vlSelf->main__DOT__swic__DOT__u_watchbus__DOT__r_value),14);
    bufp->fullBit(oldp+2369,(vlSelf->main__DOT__swic__DOT____Vcellinp__u_watchdog__i_wb_stb));
    bufp->fullBit(oldp+2370,(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_running));
    bufp->fullBit(oldp+2371,(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_zero));
    bufp->fullIData(oldp+2372,(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__r_value),31);
    bufp->fullBit(oldp+2373,(vlSelf->main__DOT__swic__DOT__u_watchdog__DOT__wb_write));
    bufp->fullCData(oldp+2374,(vlSelf->main__DOT__txv__DOT__baud_counter),7);
    bufp->fullCData(oldp+2375,(vlSelf->main__DOT__txv__DOT__state),4);
    bufp->fullCData(oldp+2376,(vlSelf->main__DOT__txv__DOT__lcl_data),8);
    bufp->fullBit(oldp+2377,(vlSelf->main__DOT__txv__DOT__zero_baud_counter));
    bufp->fullBit(oldp+2378,(vlSelf->main__DOT__u_emmc__DOT__cfg_ddr));
    bufp->fullCData(oldp+2379,(vlSelf->main__DOT__u_emmc__DOT__cfg_sample_shift),5);
    bufp->fullCData(oldp+2380,(vlSelf->main__DOT__u_emmc__DOT__sdclk),8);
    bufp->fullBit(oldp+2381,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__active));
    bufp->fullBit(oldp+2382,(vlSelf->main__DOT__u_emmc__DOT__pp_cmd));
    bufp->fullCData(oldp+2383,((3U & (IData)((vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                              >> 0x2eU)))),2);
    bufp->fullBit(oldp+2384,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid));
    bufp->fullBit(oldp+2385,(vlSelf->main__DOT__u_emmc__DOT__pp_data));
    bufp->fullBit(oldp+2386,(vlSelf->main__DOT__u_emmc__DOT__rx_en));
    bufp->fullIData(oldp+2387,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_data),32);
    bufp->fullBit(oldp+2388,(((IData)(vlSelf->main__DOT__u_emmc__DOT__rx_en) 
                              & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds))));
    bufp->fullCData(oldp+2389,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb) 
                                << 1U)),2);
    bufp->fullCData(oldp+2390,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data) 
                                << 1U)),2);
    bufp->fullBit(oldp+2391,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__dat0_busy));
    bufp->fullCData(oldp+2392,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb) 
                                << 1U)),2);
    bufp->fullSData(oldp+2393,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data) 
                                << 8U)),16);
    bufp->fullBit(oldp+2394,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__wait_for_busy));
    bufp->fullBit(oldp+2395,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_pedge));
    bufp->fullBit(oldp+2396,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__next_dedge));
    bufp->fullBit(oldp+2397,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__resp_started));
    bufp->fullBit(oldp+2398,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__io_started));
    bufp->fullBit(oldp+2399,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__last_ck));
    bufp->fullBit(oldp+2400,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_data));
    bufp->fullBit(oldp+2401,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_cmd_strb));
    bufp->fullBit(oldp+2402,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_strb));
    bufp->fullCData(oldp+2403,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__r_rx_data),8);
    bufp->fullCData(oldp+2404,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__ck_sreg),2);
    bufp->fullCData(oldp+2405,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__pck_sreg),2);
    bufp->fullBit(oldp+2406,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__sample_ck));
    bufp->fullBit(oldp+2407,(vlSelf->main__DOT__u_emmc__DOT__u_sdfrontend__DOT__GEN_NO_SERDES__DOT__cmd_sample_ck));
    bufp->fullBit(oldp+2408,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__soft_reset));
    bufp->fullBit(oldp+2409,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk90));
    bufp->fullBit(oldp+2410,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_clk_shutdown));
    bufp->fullBit(oldp+2411,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cfg_ds));
    bufp->fullCData(oldp+2412,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed),8);
    bufp->fullCData(oldp+2413,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_width),2);
    bufp->fullBit(oldp+2414,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_stb));
    bufp->fullBit(oldp+2415,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_half));
    bufp->fullCData(oldp+2416,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__w_sdclk),8);
    bufp->fullCData(oldp+2417,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__clk_ckspd),8);
    bufp->fullBit(oldp+2418,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_request));
    bufp->fullBit(oldp+2419,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_err));
    bufp->fullBit(oldp+2420,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_busy));
    bufp->fullBit(oldp+2421,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_done));
    bufp->fullCData(oldp+2422,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_type),2);
    bufp->fullCData(oldp+2423,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_ercode),2);
    bufp->fullBit(oldp+2424,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_stb));
    bufp->fullCData(oldp+2425,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd),7);
    bufp->fullCData(oldp+2426,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_id),6);
    bufp->fullIData(oldp+2427,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_arg),32);
    bufp->fullIData(oldp+2428,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rsp_arg),32);
    bufp->fullBit(oldp+2429,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_valid));
    bufp->fullSData(oldp+2430,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr),10);
    bufp->fullIData(oldp+2431,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__cmd_mem_data),32);
    bufp->fullBit(oldp+2432,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en));
    bufp->fullBit(oldp+2433,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_valid));
    bufp->fullBit(oldp+2434,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_ready));
    bufp->fullBit(oldp+2435,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_last));
    bufp->fullIData(oldp+2436,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_mem_data),32);
    bufp->fullSData(oldp+2437,((0x1fffU & ((IData)(1U) 
                                           << (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk)))),13);
    bufp->fullBit(oldp+2438,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid));
    bufp->fullSData(oldp+2439,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr),10);
    bufp->fullCData(oldp+2440,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb),4);
    bufp->fullIData(oldp+2441,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data),32);
    bufp->fullBit(oldp+2442,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_done));
    bufp->fullBit(oldp+2443,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__rx_err));
    bufp->fullBit(oldp+2444,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_stb));
    bufp->fullBit(oldp+2445,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk));
    bufp->fullSData(oldp+2446,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter),10);
    bufp->fullSData(oldp+2447,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__counter),10);
    bufp->fullBit(oldp+2448,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__clk90));
    bufp->fullCData(oldp+2449,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__ckspd),8);
    bufp->fullBit(oldp+2450,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90));
    bufp->fullCData(oldp+2451,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd),8);
    bufp->fullBit(oldp+2452,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready));
    bufp->fullBit(oldp+2453,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_request));
    bufp->fullBit(oldp+2454,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_rx_request));
    bufp->fullBit(oldp+2455,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent));
    bufp->fullBit(oldp+2456,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo));
    bufp->fullBit(oldp+2457,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err));
    bufp->fullCData(oldp+2458,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode),2);
    bufp->fullCData(oldp+2459,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk),4);
    bufp->fullIData(oldp+2460,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word),32);
    bufp->fullIData(oldp+2461,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl),32);
    bufp->fullSData(oldp+2462,((0xffffU & (((0xfU >= 
                                             ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                              - (IData)(2U)))
                                             ? ((IData)(1U) 
                                                << 
                                                ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                                 - (IData)(2U)))
                                             : 0U) 
                                           - (IData)(1U)))),16);
    bufp->fullIData(oldp+2463,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__ika),32);
    bufp->fullIData(oldp+2464,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__ikb),32);
    bufp->fullIData(oldp+2465,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a),32);
    bufp->fullIData(oldp+2466,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b),32);
    bufp->fullSData(oldp+2467,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr),10);
    bufp->fullSData(oldp+2468,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr),10);
    bufp->fullSData(oldp+2469,((((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo)) 
                                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en))
                                 ? (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
                                 : (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))),10);
    bufp->fullSData(oldp+2470,((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
                                 & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo))
                                 ? (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
                                 : (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))),10);
    bufp->fullSData(oldp+2471,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr),10);
    bufp->fullIData(oldp+2472,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__r_fifo)
                                 ? vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b
                                 : vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a)),32);
    bufp->fullBit(oldp+2473,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_last));
    bufp->fullBit(oldp+2474,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__tx_en) 
                              & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr) 
                                 >= (0xffffU & (((0xfU 
                                                  >= 
                                                  ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                                   - (IData)(2U)))
                                                  ? 
                                                 ((IData)(1U) 
                                                  << 
                                                  ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                                   - (IData)(2U)))
                                                  : 0U) 
                                                - (IData)(1U)))))));
    bufp->fullBit(oldp+2475,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid));
    bufp->fullBit(oldp+2476,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_ack));
    bufp->fullCData(oldp+2477,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_sel),2);
    bufp->fullIData(oldp+2478,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__pre_data),32);
    bufp->fullSData(oldp+2479,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_a),10);
    bufp->fullSData(oldp+2480,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_b),10);
    bufp->fullCData(oldp+2481,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_a),4);
    bufp->fullCData(oldp+2482,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_b),4);
    bufp->fullIData(oldp+2483,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_a),32);
    bufp->fullIData(oldp+2484,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_b),32);
    bufp->fullBit(oldp+2485,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__cmd_busy));
    bufp->fullCData(oldp+2486,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill),5);
    bufp->fullIData(oldp+2487,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg),20);
    bufp->fullBit(oldp+2488,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid));
    bufp->fullCData(oldp+2489,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill),2);
    bufp->fullSData(oldp+2490,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data),16);
    bufp->fullBit(oldp+2491,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full));
    bufp->fullBit(oldp+2492,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb));
    bufp->fullCData(oldp+2493,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr),2);
    bufp->fullCData(oldp+2494,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr),2);
    bufp->fullCData(oldp+2495,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data),8);
    bufp->fullBit(oldp+2496,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__busy));
    bufp->fullBit(oldp+2497,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase));
    bufp->fullBit(oldp+2498,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc));
    bufp->fullBit(oldp+2499,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__pending_crc));
    bufp->fullSData(oldp+2500,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count),16);
    bufp->fullCData(oldp+2501,(((0x80U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err) 
                                          << 6U)) | 
                                ((0x40U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err) 
                                           << 5U)) 
                                 | ((0x20U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err) 
                                              << 4U)) 
                                    | ((0x10U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err) 
                                                 << 3U)) 
                                       | ((8U & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err) 
                                                 << 3U)) 
                                          | ((4U & 
                                              ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err) 
                                               << 2U)) 
                                             | ((2U 
                                                 & ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err) 
                                                    << 1U)) 
                                                | (1U 
                                                   & (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err)))))))))),8);
    bufp->fullIData(oldp+2502,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout),23);
    bufp->fullBit(oldp+2503,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog));
    bufp->fullBit(oldp+2504,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb));
    bufp->fullBit(oldp+2505,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__w_done));
    bufp->fullSData(oldp+2506,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2507,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2508,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err),2);
    bufp->fullSData(oldp+2509,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2510,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2511,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err),2);
    bufp->fullSData(oldp+2512,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2513,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2514,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err),2);
    bufp->fullSData(oldp+2515,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2516,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2517,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err),2);
    bufp->fullBit(oldp+2518,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_cfg_dbl));
    bufp->fullCData(oldp+2519,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount),6);
    bufp->fullQData(oldp+2520,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg),48);
    bufp->fullBit(oldp+2522,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response));
    bufp->fullBit(oldp+2523,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_ds));
    bufp->fullBit(oldp+2524,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl));
    bufp->fullBit(oldp+2525,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err));
    bufp->fullCData(oldp+2526,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type),2);
    bufp->fullCData(oldp+2527,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count),8);
    bufp->fullBit(oldp+2528,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err) 
                              | ((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response) 
                                 & ((((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type) 
                                      >> 1U) & ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                                                & (0x30U 
                                                   == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))) 
                                    | ((2U == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
                                       & ((~ (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                                          & (0x88U 
                                             == (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))))))));
    bufp->fullBit(oldp+2529,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done));
    bufp->fullBit(oldp+2530,(((IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) 
                              & (9U != (IData)(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill)))));
    bufp->fullBit(oldp+2531,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response));
    bufp->fullQData(oldp+2532,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg),40);
    bufp->fullBit(oldp+2534,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout));
    bufp->fullIData(oldp+2535,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter),26);
    bufp->fullCData(oldp+2536,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill),7);
    bufp->fullBit(oldp+2537,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy));
    bufp->fullBit(oldp+2538,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data));
    bufp->fullBit(oldp+2539,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done));
    bufp->fullBit(oldp+2540,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID));
    bufp->fullBit(oldp+2541,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr));
    bufp->fullCData(oldp+2542,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width),2);
    bufp->fullCData(oldp+2543,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period),2);
    bufp->fullBit(oldp+2544,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__start_packet));
    bufp->fullBit(oldp+2545,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid));
    bufp->fullCData(oldp+2546,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pstate),2);
    bufp->fullBit(oldp+2547,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready));
    bufp->fullIData(oldp+2548,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_data),32);
    bufp->fullCData(oldp+2549,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__pre_count),4);
    bufp->fullSData(oldp+2550,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg),16);
    bufp->fullIData(oldp+2551,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w),32);
    bufp->fullIData(oldp+2552,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w),32);
    bufp->fullIData(oldp+2553,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w),32);
    bufp->fullIData(oldp+2554,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg),32);
    bufp->fullQData(oldp+2555,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w),64);
    bufp->fullQData(oldp+2557,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w),64);
    bufp->fullQData(oldp+2559,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w),64);
    bufp->fullQData(oldp+2561,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg),64);
    bufp->fullWData(oldp+2563,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w),128);
    bufp->fullWData(oldp+2567,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w),128);
    bufp->fullWData(oldp+2571,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w),128);
    bufp->fullWData(oldp+2575,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg),128);
    bufp->fullWData(oldp+2579,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d),256);
    bufp->fullWData(oldp+2587,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d),256);
    bufp->fullWData(oldp+2595,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d),256);
    bufp->fullWData(oldp+2603,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg),256);
    bufp->fullCData(oldp+2611,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts),5);
    bufp->fullIData(oldp+2612,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg),32);
    bufp->fullBit(oldp+2613,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_txframe__DOT__ck_stop_bit));
    bufp->fullSData(oldp+2614,(vlSelf->main__DOT__u_fan__DOT__pwm_counter),13);
    bufp->fullSData(oldp+2615,(vlSelf->main__DOT__u_fan__DOT__ctl_fpga),13);
    bufp->fullSData(oldp+2616,(vlSelf->main__DOT__u_fan__DOT__ctl_sys),13);
    bufp->fullBit(oldp+2617,(vlSelf->main__DOT__u_fan__DOT__ck_tach));
    bufp->fullBit(oldp+2618,(vlSelf->main__DOT__u_fan__DOT__last_tach));
    bufp->fullCData(oldp+2619,(vlSelf->main__DOT__u_fan__DOT__pipe_tach),2);
    bufp->fullBit(oldp+2620,(vlSelf->main__DOT__u_fan__DOT__tach_reset));
    bufp->fullIData(oldp+2621,(vlSelf->main__DOT__u_fan__DOT__tach_count),27);
    bufp->fullIData(oldp+2622,(vlSelf->main__DOT__u_fan__DOT__tach_counter),27);
    bufp->fullIData(oldp+2623,(vlSelf->main__DOT__u_fan__DOT__tach_timer),27);
    bufp->fullBit(oldp+2624,(vlSelf->main__DOT__u_fan__DOT__i2c_wb_ack));
    bufp->fullIData(oldp+2625,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_read_data),32);
    bufp->fullBit(oldp+2626,(vlSelf->main__DOT__u_fan__DOT__ign_mem_cyc));
    bufp->fullBit(oldp+2627,(vlSelf->main__DOT__u_fan__DOT__mem_stb));
    bufp->fullCData(oldp+2628,(vlSelf->main__DOT__u_fan__DOT__mem_addr),5);
    bufp->fullCData(oldp+2629,(vlSelf->main__DOT__u_fan__DOT__mem_data),8);
    bufp->fullBit(oldp+2630,(vlSelf->main__DOT__u_fan__DOT__mem_ack));
    bufp->fullBit(oldp+2631,(vlSelf->main__DOT__u_fan__DOT__i2cd_valid));
    bufp->fullBit(oldp+2632,(vlSelf->main__DOT__u_fan__DOT__i2cd_last));
    bufp->fullCData(oldp+2633,(vlSelf->main__DOT__u_fan__DOT__i2cd_data),8);
    bufp->fullBit(oldp+2634,(vlSelf->main__DOT__u_fan__DOT__pp_ms));
    bufp->fullIData(oldp+2635,(vlSelf->main__DOT__u_fan__DOT__trigger_counter),17);
    bufp->fullIData(oldp+2636,(vlSelf->main__DOT__u_fan__DOT__temp_tmp),24);
    bufp->fullIData(oldp+2637,(vlSelf->main__DOT__u_fan__DOT__temp_data),32);
    bufp->fullBit(oldp+2638,(vlSelf->main__DOT__u_fan__DOT__pre_ack));
    bufp->fullIData(oldp+2639,(vlSelf->main__DOT__u_fan__DOT__pre_data),32);
    bufp->fullBit(oldp+2640,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted));
    bufp->fullBit(oldp+2641,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__cpu_new_pc));
    bufp->fullCData(oldp+2642,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_jump_addr),5);
    bufp->fullBit(oldp+2643,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_valid));
    bufp->fullBit(oldp+2644,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_ready));
    bufp->fullCData(oldp+2645,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn),8);
    bufp->fullCData(oldp+2646,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_insn_addr),5);
    bufp->fullBit(oldp+2647,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__pf_illegal));
    bufp->fullBit(oldp+2648,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid));
    bufp->fullBit(oldp+2649,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle));
    bufp->fullBit(oldp+2650,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_ready));
    bufp->fullBit(oldp+2651,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_ready));
    bufp->fullBit(oldp+2652,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort));
    bufp->fullBit(oldp+2653,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid));
    bufp->fullSData(oldp+2654,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn),12);
    bufp->fullCData(oldp+2655,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn),4);
    bufp->fullBit(oldp+2656,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckedge));
    bufp->fullBit(oldp+2657,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch));
    bufp->fullSData(oldp+2658,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_ckcount),12);
    bufp->fullSData(oldp+2659,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ckcount),12);
    bufp->fullCData(oldp+2660,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__abort_address),5);
    bufp->fullCData(oldp+2661,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__jump_target),5);
    bufp->fullBit(oldp+2662,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait));
    bufp->fullBit(oldp+2663,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request));
    bufp->fullBit(oldp+2664,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err));
    bufp->fullBit(oldp+2665,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted));
    bufp->fullBit(oldp+2666,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual));
    bufp->fullBit(oldp+2667,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__sda));
    bufp->fullBit(oldp+2668,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__scl));
    bufp->fullBit(oldp+2669,(((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted) 
                              | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait))));
    bufp->fullBit(oldp+2670,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_sda));
    bufp->fullBit(oldp+2671,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__w_scl));
    bufp->fullBit(oldp+2672,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_ready));
    bufp->fullBit(oldp+2673,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__s_tvalid));
    bufp->fullSData(oldp+2674,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data),10);
    bufp->fullBit(oldp+2675,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl));
    bufp->fullBit(oldp+2676,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda));
    bufp->fullSData(oldp+2677,((0x7ffU & (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))),11);
    bufp->fullBit(oldp+2678,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__last_byte));
    bufp->fullBit(oldp+2679,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__dir));
    bufp->fullBit(oldp+2680,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__will_ack));
    bufp->fullCData(oldp+2681,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__state),4);
    bufp->fullCData(oldp+2682,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__nbits),3);
    bufp->fullCData(oldp+2683,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__sreg),8);
    bufp->fullBit(oldp+2684,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__q_scl));
    bufp->fullBit(oldp+2685,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__q_sda));
    bufp->fullBit(oldp+2686,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_scl));
    bufp->fullBit(oldp+2687,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__ck_sda));
    bufp->fullBit(oldp+2688,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__lst_scl));
    bufp->fullBit(oldp+2689,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__lst_sda));
    bufp->fullBit(oldp+2690,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__stop_bit));
    bufp->fullBit(oldp+2691,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_axisi2c__DOT__channel_busy));
    bufp->fullBit(oldp+2692,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__last_stb));
    bufp->fullBit(oldp+2693,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__invalid_bus_cycle));
    bufp->fullCData(oldp+2694,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_word),8);
    bufp->fullBit(oldp+2695,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_valid));
    bufp->fullCData(oldp+2696,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__inflight),2);
    bufp->fullBit(oldp+2697,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__u_fetch__DOT__cache_illegal));
    bufp->fullBit(oldp+2698,(vlSelf->main__DOT____Vcellinp__u_i2cdma__S_VALID));
    bufp->fullIData(oldp+2699,(vlSelf->main__DOT__u_i2cdma__DOT__r_baseaddr),28);
    bufp->fullIData(oldp+2700,(vlSelf->main__DOT__u_i2cdma__DOT__r_memlen),28);
    bufp->fullCData(oldp+2701,(vlSelf->main__DOT__u_i2cdma__DOT__subaddr),6);
    bufp->fullIData(oldp+2702,(vlSelf->main__DOT__u_i2cdma__DOT__current_addr),28);
    bufp->fullBit(oldp+2703,(vlSelf->main__DOT__u_i2cdma__DOT__wb_last));
    bufp->fullBit(oldp+2704,(vlSelf->main__DOT__u_i2cdma__DOT__bus_err));
    bufp->fullBit(oldp+2705,(vlSelf->main__DOT__u_i2cdma__DOT__r_reset));
    bufp->fullBit(oldp+2706,(vlSelf->main__DOT__u_i2cdma__DOT__r_overflow));
    bufp->fullBit(oldp+2707,(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__REG_OUTPUT__DOT__ro_valid));
    bufp->fullBit(oldp+2708,(vlSelf->main__DOT__u_i2cdma__DOT__skd_ready));
    bufp->fullBit(oldp+2709,((1U & ((IData)(vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data) 
                                    >> 8U))));
    bufp->fullCData(oldp+2710,((0xffU & (IData)(vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data))),8);
    bufp->fullSData(oldp+2711,(vlSelf->main__DOT__u_i2cdma__DOT____Vcellinp__sskd__i_data),9);
    bufp->fullSData(oldp+2712,(vlSelf->main__DOT__u_i2cdma__DOT____Vcellout__sskd__o_data),9);
    bufp->fullSData(oldp+2713,(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_data),9);
    bufp->fullBit(oldp+2714,(vlSelf->main__DOT__u_i2cdma__DOT__sskd__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+2715,(vlSelf->main__DOT__u_sdcard__DOT__cfg_ddr));
    bufp->fullCData(oldp+2716,(vlSelf->main__DOT__u_sdcard__DOT__cfg_sample_shift),5);
    bufp->fullCData(oldp+2717,(vlSelf->main__DOT__u_sdcard__DOT__sdclk),8);
    bufp->fullBit(oldp+2718,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active));
    bufp->fullBit(oldp+2719,(vlSelf->main__DOT__u_sdcard__DOT__pp_cmd));
    bufp->fullCData(oldp+2720,((3U & (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                              >> 0x2eU)))),2);
    bufp->fullBit(oldp+2721,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid));
    bufp->fullBit(oldp+2722,(vlSelf->main__DOT__u_sdcard__DOT__pp_data));
    bufp->fullBit(oldp+2723,(vlSelf->main__DOT__u_sdcard__DOT__rx_en));
    bufp->fullIData(oldp+2724,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data),32);
    bufp->fullBit(oldp+2725,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__rx_en) 
                              & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds))));
    bufp->fullCData(oldp+2726,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb) 
                                << 1U)),2);
    bufp->fullCData(oldp+2727,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_data) 
                                << 1U)),2);
    bufp->fullBit(oldp+2728,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__dat0_busy));
    bufp->fullCData(oldp+2729,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb) 
                                << 1U)),2);
    bufp->fullSData(oldp+2730,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data) 
                                << 8U)),16);
    bufp->fullBit(oldp+2731,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__wait_for_busy));
    bufp->fullCData(oldp+2732,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in),2);
    bufp->fullBit(oldp+2733,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[0]));
    bufp->fullBit(oldp+2734,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[1]));
    bufp->fullBit(oldp+2735,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[2]));
    bufp->fullBit(oldp+2736,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[3]));
    bufp->fullBit(oldp+2737,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[4]));
    bufp->fullBit(oldp+2738,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[5]));
    bufp->fullBit(oldp+2739,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[6]));
    bufp->fullBit(oldp+2740,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[7]));
    bufp->fullBit(oldp+2741,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[8]));
    bufp->fullBit(oldp+2742,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[9]));
    bufp->fullBit(oldp+2743,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[10]));
    bufp->fullBit(oldp+2744,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[11]));
    bufp->fullBit(oldp+2745,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[12]));
    bufp->fullBit(oldp+2746,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[13]));
    bufp->fullBit(oldp+2747,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[14]));
    bufp->fullBit(oldp+2748,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pre_dat[15]));
    bufp->fullSData(oldp+2749,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__w_dat),16);
    bufp->fullCData(oldp+2750,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_pedge),2);
    bufp->fullCData(oldp+2751,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__next_dedge),2);
    bufp->fullCData(oldp+2752,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__ck_sreg),6);
    bufp->fullCData(oldp+2753,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__pck_sreg),6);
    bufp->fullCData(oldp+2754,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__sample_ck),2);
    bufp->fullCData(oldp+2755,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__cmd_sample_ck),2);
    bufp->fullBit(oldp+2756,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__resp_started));
    bufp->fullBit(oldp+2757,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__io_started));
    bufp->fullBit(oldp+2758,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__last_ck));
    bufp->fullBit(oldp+2759,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_strb));
    bufp->fullBit(oldp+2760,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_cmd_data));
    bufp->fullBit(oldp+2761,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_strb));
    bufp->fullCData(oldp+2762,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__r_rx_data),8);
    bufp->fullBit(oldp+2763,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__high_z));
    bufp->fullCData(oldp+2764,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__w_out),8);
    bufp->fullBit(oldp+2765,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__high_z));
    bufp->fullCData(oldp+2766,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in),2);
    bufp->fullCData(oldp+2767,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__r_out),2);
    bufp->fullBit(oldp+2768,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p));
    bufp->fullBit(oldp+2769,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__high_z));
    bufp->fullCData(oldp+2770,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in),2);
    bufp->fullCData(oldp+2771,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__r_out),2);
    bufp->fullBit(oldp+2772,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p));
    bufp->fullBit(oldp+2773,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__high_z));
    bufp->fullCData(oldp+2774,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in),2);
    bufp->fullCData(oldp+2775,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__r_out),2);
    bufp->fullBit(oldp+2776,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p));
    bufp->fullBit(oldp+2777,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__high_z));
    bufp->fullCData(oldp+2778,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_in),2);
    bufp->fullCData(oldp+2779,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__r_out),2);
    bufp->fullBit(oldp+2780,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p));
    bufp->fullCData(oldp+2781,(((2U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__sdclk) 
                                       >> 6U)) | (1U 
                                                  & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__sdclk) 
                                                     >> 3U)))),2);
    bufp->fullCData(oldp+2782,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_clk_oddr__DOT__r_out),2);
    bufp->fullBit(oldp+2783,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__high_z));
    bufp->fullCData(oldp+2784,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__r_out),2);
    bufp->fullBit(oldp+2785,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_p));
    bufp->fullBit(oldp+2786,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__soft_reset));
    bufp->fullBit(oldp+2787,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk90));
    bufp->fullBit(oldp+2788,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_clk_shutdown));
    bufp->fullBit(oldp+2789,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cfg_ds));
    bufp->fullCData(oldp+2790,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_ckspeed),8);
    bufp->fullCData(oldp+2791,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_width),2);
    bufp->fullBit(oldp+2792,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_stb));
    bufp->fullBit(oldp+2793,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_half));
    bufp->fullCData(oldp+2794,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__w_sdclk),8);
    bufp->fullCData(oldp+2795,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__clk_ckspd),8);
    bufp->fullBit(oldp+2796,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_request));
    bufp->fullBit(oldp+2797,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_err));
    bufp->fullBit(oldp+2798,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_busy));
    bufp->fullBit(oldp+2799,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_done));
    bufp->fullCData(oldp+2800,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_type),2);
    bufp->fullCData(oldp+2801,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_ercode),2);
    bufp->fullBit(oldp+2802,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_stb));
    bufp->fullCData(oldp+2803,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd),7);
    bufp->fullCData(oldp+2804,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_id),6);
    bufp->fullIData(oldp+2805,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_arg),32);
    bufp->fullIData(oldp+2806,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rsp_arg),32);
    bufp->fullBit(oldp+2807,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_valid));
    bufp->fullSData(oldp+2808,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__mem_addr),10);
    bufp->fullIData(oldp+2809,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__cmd_mem_data),32);
    bufp->fullBit(oldp+2810,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en));
    bufp->fullBit(oldp+2811,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_valid));
    bufp->fullBit(oldp+2812,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_ready));
    bufp->fullBit(oldp+2813,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_last));
    bufp->fullIData(oldp+2814,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_mem_data),32);
    bufp->fullSData(oldp+2815,((0x1fffU & ((IData)(1U) 
                                           << (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk)))),13);
    bufp->fullBit(oldp+2816,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_valid));
    bufp->fullSData(oldp+2817,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_addr),10);
    bufp->fullCData(oldp+2818,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_strb),4);
    bufp->fullIData(oldp+2819,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_data),32);
    bufp->fullBit(oldp+2820,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_done));
    bufp->fullBit(oldp+2821,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__rx_err));
    bufp->fullBit(oldp+2822,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_stb));
    bufp->fullBit(oldp+2823,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_clk));
    bufp->fullSData(oldp+2824,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__nxt_counter),10);
    bufp->fullSData(oldp+2825,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__counter),10);
    bufp->fullBit(oldp+2826,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__clk90));
    bufp->fullCData(oldp+2827,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__ckspd),8);
    bufp->fullBit(oldp+2828,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_clk90));
    bufp->fullCData(oldp+2829,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_clkgen__DOT__w_ckspd),8);
    bufp->fullBit(oldp+2830,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_control__i_tx_mem_ready));
    bufp->fullBit(oldp+2831,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_request));
    bufp->fullBit(oldp+2832,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_rx_request));
    bufp->fullBit(oldp+2833,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_tx_sent));
    bufp->fullBit(oldp+2834,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo));
    bufp->fullBit(oldp+2835,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_err));
    bufp->fullCData(oldp+2836,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_cmd_ecode),2);
    bufp->fullCData(oldp+2837,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk),4);
    bufp->fullIData(oldp+2838,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_cmd_word),32);
    bufp->fullIData(oldp+2839,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__w_phy_ctrl),32);
    bufp->fullSData(oldp+2840,((0xffffU & (((0xfU >= 
                                             ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                              - (IData)(2U)))
                                             ? ((IData)(1U) 
                                                << 
                                                ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                                 - (IData)(2U)))
                                             : 0U) 
                                           - (IData)(1U)))),16);
    bufp->fullIData(oldp+2841,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__ika),32);
    bufp->fullIData(oldp+2842,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__ikb),32);
    bufp->fullIData(oldp+2843,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a),32);
    bufp->fullIData(oldp+2844,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b),32);
    bufp->fullSData(oldp+2845,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_wraddr),10);
    bufp->fullSData(oldp+2846,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr),10);
    bufp->fullSData(oldp+2847,((((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo)) 
                                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en))
                                 ? (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
                                 : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))),10);
    bufp->fullSData(oldp+2848,((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
                                 & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo))
                                 ? (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr)
                                 : (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__fif_rdaddr))),10);
    bufp->fullSData(oldp+2849,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr),10);
    bufp->fullIData(oldp+2850,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__r_fifo)
                                 ? vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_b
                                 : vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_a)),32);
    bufp->fullBit(oldp+2851,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_fifo_last));
    bufp->fullBit(oldp+2852,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__tx_en) 
                              & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_mem_addr) 
                                 >= (0xffffU & (((0xfU 
                                                  >= 
                                                  ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                                   - (IData)(2U)))
                                                  ? 
                                                 ((IData)(1U) 
                                                  << 
                                                  ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__lgblk) 
                                                   - (IData)(2U)))
                                                  : 0U) 
                                                - (IData)(1U)))))));
    bufp->fullBit(oldp+2853,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__tx_pipe_valid));
    bufp->fullBit(oldp+2854,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_present));
    bufp->fullBit(oldp+2855,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__r_card_removed));
    bufp->fullBit(oldp+2856,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_ack));
    bufp->fullCData(oldp+2857,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_sel),2);
    bufp->fullIData(oldp+2858,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__pre_data),32);
    bufp->fullSData(oldp+2859,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_a),10);
    bufp->fullSData(oldp+2860,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_addr_b),10);
    bufp->fullCData(oldp+2861,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_a),4);
    bufp->fullCData(oldp+2862,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_strb_b),4);
    bufp->fullIData(oldp+2863,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_a),32);
    bufp->fullIData(oldp+2864,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__mem_wr_data_b),32);
    bufp->fullBit(oldp+2865,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__cmd_busy));
    bufp->fullCData(oldp+2866,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__raw_card_present),3);
    bufp->fullSData(oldp+2867,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__GEN_CARD_DETECT__DOT__card_detect_counter),10);
    bufp->fullCData(oldp+2868,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_fill),5);
    bufp->fullIData(oldp+2869,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__sync_sreg),20);
    bufp->fullBit(oldp+2870,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_valid));
    bufp->fullCData(oldp+2871,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_fill),2);
    bufp->fullSData(oldp+2872,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__s2_data),16);
    bufp->fullBit(oldp+2873,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__mem_full));
    bufp->fullBit(oldp+2874,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_strb));
    bufp->fullCData(oldp+2875,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__subaddr),2);
    bufp->fullCData(oldp+2876,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__next_subaddr),2);
    bufp->fullCData(oldp+2877,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rnxt_data),8);
    bufp->fullBit(oldp+2878,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__busy));
    bufp->fullBit(oldp+2879,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__data_phase));
    bufp->fullBit(oldp+2880,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__load_crc));
    bufp->fullBit(oldp+2881,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__pending_crc));
    bufp->fullSData(oldp+2882,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__rail_count),16);
    bufp->fullCData(oldp+2883,(((0x80U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err) 
                                          << 6U)) | 
                                ((0x40U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err) 
                                           << 5U)) 
                                 | ((0x20U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err) 
                                              << 4U)) 
                                    | ((0x10U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err) 
                                                 << 3U)) 
                                       | ((8U & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err) 
                                                 << 3U)) 
                                          | ((4U & 
                                              ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err) 
                                               << 2U)) 
                                             | ((2U 
                                                 & ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err) 
                                                    << 1U)) 
                                                | (1U 
                                                   & (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err)))))))))),8);
    bufp->fullIData(oldp+2884,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_timeout),23);
    bufp->fullBit(oldp+2885,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__r_watchdog));
    bufp->fullBit(oldp+2886,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__last_strb));
    bufp->fullBit(oldp+2887,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__w_done));
    bufp->fullSData(oldp+2888,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2889,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2890,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__0__KET____DOT__lcl_err),2);
    bufp->fullSData(oldp+2891,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2892,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2893,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__1__KET____DOT__lcl_err),2);
    bufp->fullSData(oldp+2894,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2895,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2896,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__2__KET____DOT__lcl_err),2);
    bufp->fullSData(oldp+2897,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__pedge_crc),16);
    bufp->fullSData(oldp+2898,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__nedge_crc),16);
    bufp->fullCData(oldp+2899,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_rxframe__DOT__GEN_RAIL_CRC__BRA__3__KET____DOT__lcl_err),2);
    bufp->fullBit(oldp+2900,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_sdcmd__i_cfg_dbl));
    bufp->fullCData(oldp+2901,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__srcount),6);
    bufp->fullQData(oldp+2902,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg),48);
    bufp->fullBit(oldp+2904,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response));
    bufp->fullBit(oldp+2905,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_ds));
    bufp->fullBit(oldp+2906,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cfg_dbl));
    bufp->fullBit(oldp+2907,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err));
    bufp->fullCData(oldp+2908,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type),2);
    bufp->fullCData(oldp+2909,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count),8);
    bufp->fullBit(oldp+2910,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_frame_err) 
                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__waiting_on_response) 
                                 & ((((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type) 
                                      >> 1U) & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                                                & (0x30U 
                                                   == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))) 
                                    | ((2U == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__cmd_type)) 
                                       & ((~ (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg)) 
                                          & (0x88U 
                                             == (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__resp_count)))))))));
    bufp->fullBit(oldp+2911,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done));
    bufp->fullBit(oldp+2912,(((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_done) 
                              & (9U != (IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill)))));
    bufp->fullBit(oldp+2913,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__w_no_response));
    bufp->fullQData(oldp+2914,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_sreg),40);
    bufp->fullBit(oldp+2916,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout));
    bufp->fullIData(oldp+2917,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__rx_timeout_counter),26);
    bufp->fullCData(oldp+2918,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__crc_fill),7);
    bufp->fullBit(oldp+2919,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_busy));
    bufp->fullBit(oldp+2920,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__new_data));
    bufp->fullBit(oldp+2921,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__r_done));
    bufp->fullBit(oldp+2922,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT____Vcellinp__u_txframe__S_VALID));
    bufp->fullBit(oldp+2923,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_ddr));
    bufp->fullCData(oldp+2924,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_width),2);
    bufp->fullCData(oldp+2925,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__cfg_period),2);
    bufp->fullBit(oldp+2926,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__start_packet));
    bufp->fullBit(oldp+2927,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_valid));
    bufp->fullCData(oldp+2928,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pstate),2);
    bufp->fullBit(oldp+2929,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_ready));
    bufp->fullIData(oldp+2930,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_data),32);
    bufp->fullCData(oldp+2931,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__pre_count),4);
    bufp->fullSData(oldp+2932,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_1w_reg),16);
    bufp->fullIData(oldp+2933,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_2w),32);
    bufp->fullIData(oldp+2934,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_2w),32);
    bufp->fullIData(oldp+2935,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_2w),32);
    bufp->fullIData(oldp+2936,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_2w_reg),32);
    bufp->fullQData(oldp+2937,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_4w),64);
    bufp->fullQData(oldp+2939,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_4w),64);
    bufp->fullQData(oldp+2941,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_4w),64);
    bufp->fullQData(oldp+2943,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_4w_reg),64);
    bufp->fullWData(oldp+2945,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8w),128);
    bufp->fullWData(oldp+2949,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8w),128);
    bufp->fullWData(oldp+2953,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8w),128);
    bufp->fullWData(oldp+2957,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8w_reg),128);
    bufp->fullWData(oldp+2961,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__di_crc_8d),256);
    bufp->fullWData(oldp+2969,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__nxt_crc_8d),256);
    bufp->fullWData(oldp+2977,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__new_crc_8d),256);
    bufp->fullWData(oldp+2985,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__crc_8d_reg),256);
    bufp->fullCData(oldp+2993,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_counts),5);
    bufp->fullIData(oldp+2994,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_sreg),32);
    bufp->fullBit(oldp+2995,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_stop_bit));
    bufp->fullBit(oldp+2996,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_stb));
    bufp->fullBit(oldp+2997,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_first));
    bufp->fullBit(oldp+2998,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_null));
    bufp->fullBit(oldp+2999,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_last));
    bufp->fullWData(oldp+3000,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_data),512);
    bufp->fullWData(oldp+3016,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_data),512);
    bufp->fullQData(oldp+3032,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__s_sel),64);
    bufp->fullQData(oldp+3034,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__nxt_sel),64);
    bufp->fullCData(oldp+3036,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_shift),4);
    bufp->fullCData(oldp+3037,((0xfU & (IData)(vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data))),4);
    bufp->fullBit(oldp+3038,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_full));
    bufp->fullBit(oldp+3039,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__fifo_empty));
    bufp->fullBit(oldp+3040,((1U & ((IData)(vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data) 
                                    >> 4U))));
    bufp->fullCData(oldp+3041,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__ign_fifo_fill),6);
    bufp->fullBit(oldp+3042,(vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_wr));
    bufp->fullCData(oldp+3043,(vlSelf->main__DOT__u_wbdown__DOT____Vcellinp__DOWNSIZE__DOT__u_fifo__i_data),5);
    bufp->fullCData(oldp+3044,(vlSelf->main__DOT__u_wbdown__DOT____Vcellout__DOWNSIZE__DOT__u_fifo__o_data),5);
    bufp->fullBit(oldp+3045,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_full));
    bufp->fullBit(oldp+3046,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__r_empty));
    bufp->fullCData(oldp+3047,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[0]),5);
    bufp->fullCData(oldp+3048,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[1]),5);
    bufp->fullCData(oldp+3049,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[2]),5);
    bufp->fullCData(oldp+3050,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[3]),5);
    bufp->fullCData(oldp+3051,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[4]),5);
    bufp->fullCData(oldp+3052,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[5]),5);
    bufp->fullCData(oldp+3053,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[6]),5);
    bufp->fullCData(oldp+3054,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[7]),5);
    bufp->fullCData(oldp+3055,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[8]),5);
    bufp->fullCData(oldp+3056,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[9]),5);
    bufp->fullCData(oldp+3057,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[10]),5);
    bufp->fullCData(oldp+3058,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[11]),5);
    bufp->fullCData(oldp+3059,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[12]),5);
    bufp->fullCData(oldp+3060,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[13]),5);
    bufp->fullCData(oldp+3061,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[14]),5);
    bufp->fullCData(oldp+3062,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[15]),5);
    bufp->fullCData(oldp+3063,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[16]),5);
    bufp->fullCData(oldp+3064,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[17]),5);
    bufp->fullCData(oldp+3065,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[18]),5);
    bufp->fullCData(oldp+3066,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[19]),5);
    bufp->fullCData(oldp+3067,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[20]),5);
    bufp->fullCData(oldp+3068,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[21]),5);
    bufp->fullCData(oldp+3069,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[22]),5);
    bufp->fullCData(oldp+3070,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[23]),5);
    bufp->fullCData(oldp+3071,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[24]),5);
    bufp->fullCData(oldp+3072,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[25]),5);
    bufp->fullCData(oldp+3073,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[26]),5);
    bufp->fullCData(oldp+3074,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[27]),5);
    bufp->fullCData(oldp+3075,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[28]),5);
    bufp->fullCData(oldp+3076,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[29]),5);
    bufp->fullCData(oldp+3077,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[30]),5);
    bufp->fullCData(oldp+3078,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__mem[31]),5);
    bufp->fullCData(oldp+3079,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__wr_addr),6);
    bufp->fullCData(oldp+3080,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__rd_addr),6);
    bufp->fullBit(oldp+3081,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_wr));
    bufp->fullBit(oldp+3082,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__u_fifo__DOT__w_rd));
    bufp->fullSData(oldp+3083,(vlSelf->main__DOT__wb32_xbar__DOT__grant[0]),13);
    bufp->fullBit(oldp+3084,(vlSelf->main__DOT__wb32_xbar__DOT__mgrant));
    bufp->fullCData(oldp+3085,(vlSelf->main__DOT__wb32_xbar__DOT__w_mpending[0]),6);
    bufp->fullBit(oldp+3086,(vlSelf->main__DOT__wb32_xbar__DOT__mfull));
    bufp->fullBit(oldp+3087,(vlSelf->main__DOT__wb32_xbar__DOT__mnearfull));
    bufp->fullBit(oldp+3088,(vlSelf->main__DOT__wb32_xbar__DOT__mempty));
    bufp->fullIData(oldp+3089,(vlSelf->main__DOT__wb32_xbar__DOT__iN),32);
    bufp->fullCData(oldp+3090,(vlSelf->main__DOT__wb32_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending),6);
    bufp->fullSData(oldp+3091,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded),13);
    bufp->fullBit(oldp+3092,((1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))));
    bufp->fullCData(oldp+3093,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr),8);
    bufp->fullQData(oldp+3094,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data),45);
    bufp->fullQData(oldp+3096,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data),45);
    bufp->fullIData(oldp+3098,((0x3ffffffU & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr))),26);
    bufp->fullBit(oldp+3099,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_stb));
    bufp->fullWData(oldp+3100,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__rtn_data),512);
    bufp->fullCData(oldp+3116,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_shift),4);
    bufp->fullBit(oldp+3117,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_full));
    bufp->fullBit(oldp+3118,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__r_empty));
    bufp->fullCData(oldp+3119,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__ign_fifo_fill),6);
    bufp->fullCData(oldp+3120,((0xfU & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr))),4);
    bufp->fullCData(oldp+3121,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem
                               [(0x1fU & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr))]),4);
    __Vtemp_hcfafa750__0[0U] = Vmain__ConstPool__CONST_hbd99daea_0[0U];
    __Vtemp_hcfafa750__0[1U] = Vmain__ConstPool__CONST_hbd99daea_0[1U];
    __Vtemp_hcfafa750__0[2U] = Vmain__ConstPool__CONST_hbd99daea_0[2U];
    __Vtemp_hcfafa750__0[3U] = Vmain__ConstPool__CONST_hbd99daea_0[3U];
    __Vtemp_hcfafa750__0[4U] = Vmain__ConstPool__CONST_hbd99daea_0[4U];
    __Vtemp_hcfafa750__0[5U] = Vmain__ConstPool__CONST_hbd99daea_0[5U];
    __Vtemp_hcfafa750__0[6U] = Vmain__ConstPool__CONST_hbd99daea_0[6U];
    __Vtemp_hcfafa750__0[7U] = Vmain__ConstPool__CONST_hbd99daea_0[7U];
    __Vtemp_hcfafa750__0[8U] = Vmain__ConstPool__CONST_hbd99daea_0[8U];
    __Vtemp_hcfafa750__0[9U] = Vmain__ConstPool__CONST_hbd99daea_0[9U];
    __Vtemp_hcfafa750__0[0xaU] = Vmain__ConstPool__CONST_hbd99daea_0[0xaU];
    __Vtemp_hcfafa750__0[0xbU] = Vmain__ConstPool__CONST_hbd99daea_0[0xbU];
    __Vtemp_hcfafa750__0[0xcU] = Vmain__ConstPool__CONST_hbd99daea_0[0xcU];
    __Vtemp_hcfafa750__0[0xdU] = Vmain__ConstPool__CONST_hbd99daea_0[0xdU];
    __Vtemp_hcfafa750__0[0xeU] = Vmain__ConstPool__CONST_hbd99daea_0[0xeU];
    __Vtemp_hcfafa750__0[0xfU] = (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sdata);
    bufp->fullWData(oldp+3122,(__Vtemp_hcfafa750__0),512);
    bufp->fullQData(oldp+3138,(((QData)((IData)((0xfU 
                                                 & (IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_ssel)))) 
                                << 0x3cU)),64);
    bufp->fullBit(oldp+3140,(((~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)) 
                              & (IData)(vlSelf->main__DOT__wbwide_wbu_arbiter_stb))));
    bufp->fullCData(oldp+3141,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[0]),4);
    bufp->fullCData(oldp+3142,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[1]),4);
    bufp->fullCData(oldp+3143,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[2]),4);
    bufp->fullCData(oldp+3144,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[3]),4);
    bufp->fullCData(oldp+3145,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[4]),4);
    bufp->fullCData(oldp+3146,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[5]),4);
    bufp->fullCData(oldp+3147,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[6]),4);
    bufp->fullCData(oldp+3148,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[7]),4);
    bufp->fullCData(oldp+3149,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[8]),4);
    bufp->fullCData(oldp+3150,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[9]),4);
    bufp->fullCData(oldp+3151,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[10]),4);
    bufp->fullCData(oldp+3152,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[11]),4);
    bufp->fullCData(oldp+3153,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[12]),4);
    bufp->fullCData(oldp+3154,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[13]),4);
    bufp->fullCData(oldp+3155,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[14]),4);
    bufp->fullCData(oldp+3156,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[15]),4);
    bufp->fullCData(oldp+3157,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[16]),4);
    bufp->fullCData(oldp+3158,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[17]),4);
    bufp->fullCData(oldp+3159,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[18]),4);
    bufp->fullCData(oldp+3160,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[19]),4);
    bufp->fullCData(oldp+3161,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[20]),4);
    bufp->fullCData(oldp+3162,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[21]),4);
    bufp->fullCData(oldp+3163,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[22]),4);
    bufp->fullCData(oldp+3164,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[23]),4);
    bufp->fullCData(oldp+3165,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[24]),4);
    bufp->fullCData(oldp+3166,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[25]),4);
    bufp->fullCData(oldp+3167,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[26]),4);
    bufp->fullCData(oldp+3168,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[27]),4);
    bufp->fullCData(oldp+3169,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[28]),4);
    bufp->fullCData(oldp+3170,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[29]),4);
    bufp->fullCData(oldp+3171,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[30]),4);
    bufp->fullCData(oldp+3172,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__mem[31]),4);
    bufp->fullCData(oldp+3173,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__wr_addr),6);
    bufp->fullCData(oldp+3174,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__rd_addr),6);
    bufp->fullBit(oldp+3175,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_wr));
    bufp->fullBit(oldp+3176,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__u_fifo__DOT__w_rd));
    bufp->fullCData(oldp+3177,(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc),2);
    bufp->fullCData(oldp+3178,(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sstb),2);
    bufp->fullCData(oldp+3179,(vlSelf->main__DOT____Vcellout__wbu_xbar__o_swe),2);
    bufp->fullQData(oldp+3180,(vlSelf->main__DOT____Vcellout__wbu_xbar__o_saddr),54);
    bufp->fullQData(oldp+3182,(vlSelf->main__DOT____Vcellout__wbu_xbar__o_sdata),64);
    bufp->fullCData(oldp+3184,(vlSelf->main__DOT____Vcellout__wbu_xbar__o_ssel),8);
    bufp->fullQData(oldp+3185,((((QData)((IData)(vlSelf->main__DOT__wbu_zip_idata)) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__rtn_data[0xfU])))),64);
    bufp->fullCData(oldp+3187,(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_err),2);
    bufp->fullCData(oldp+3188,(vlSelf->main__DOT__wbu_xbar__DOT__request[0]),3);
    bufp->fullCData(oldp+3189,(vlSelf->main__DOT__wbu_xbar__DOT__grant[0]),3);
    bufp->fullBit(oldp+3190,(vlSelf->main__DOT__wbu_xbar__DOT__mgrant));
    bufp->fullCData(oldp+3191,(vlSelf->main__DOT__wbu_xbar__DOT__sgrant),2);
    bufp->fullCData(oldp+3192,(vlSelf->main__DOT__wbu_xbar__DOT__w_mpending[0]),6);
    bufp->fullBit(oldp+3193,(vlSelf->main__DOT__wbu_xbar__DOT__mfull));
    bufp->fullBit(oldp+3194,(vlSelf->main__DOT__wbu_xbar__DOT__mnearfull));
    bufp->fullBit(oldp+3195,(vlSelf->main__DOT__wbu_xbar__DOT__mempty));
    bufp->fullBit(oldp+3196,(vlSelf->main__DOT__wbu_xbar__DOT__m_stb));
    bufp->fullBit(oldp+3197,((1U & (IData)((vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data 
                                            >> 0x24U)))));
    bufp->fullIData(oldp+3198,(vlSelf->main__DOT__wbu_xbar__DOT__m_addr[0]),27);
    bufp->fullIData(oldp+3199,(vlSelf->main__DOT__wbu_xbar__DOT__m_data[0]),32);
    bufp->fullCData(oldp+3200,(vlSelf->main__DOT__wbu_xbar__DOT__m_sel[0]),4);
    bufp->fullIData(oldp+3201,(vlSelf->main__DOT__wbu_xbar__DOT__s_data[0]),32);
    bufp->fullIData(oldp+3202,(vlSelf->main__DOT__wbu_xbar__DOT__s_data[1]),32);
    bufp->fullIData(oldp+3203,(vlSelf->main__DOT__wbu_xbar__DOT__s_data[2]),32);
    bufp->fullIData(oldp+3204,(vlSelf->main__DOT__wbu_xbar__DOT__s_data[3]),32);
    bufp->fullCData(oldp+3205,(vlSelf->main__DOT__wbu_xbar__DOT__s_err),4);
    bufp->fullBit(oldp+3206,(vlSelf->main__DOT__wbu_xbar__DOT__dcd_stb));
    bufp->fullIData(oldp+3207,(vlSelf->main__DOT__wbu_xbar__DOT__iN),32);
    bufp->fullBit(oldp+3208,(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel));
    bufp->fullBit(oldp+3209,(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available));
    bufp->fullCData(oldp+3210,(vlSelf->main__DOT__wbu_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending),6);
    bufp->fullBit(oldp+3211,((1U & (IData)((vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                            >> 0x3fU)))));
    bufp->fullIData(oldp+3212,((0x7ffffffU & (IData)(
                                                     (vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                                      >> 0x24U)))),27);
    bufp->fullIData(oldp+3213,((IData)((vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                        >> 4U))),32);
    bufp->fullCData(oldp+3214,((0xfU & (IData)(vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data))),4);
    bufp->fullCData(oldp+3215,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded),3);
    bufp->fullBit(oldp+3216,((1U & (~ (IData)(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))));
    bufp->fullQData(oldp+3217,((((QData)((IData)((1U 
                                                  & (IData)(
                                                            (vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                                             >> 0x3fU))))) 
                                 << 0x24U) | (0xfffffffffULL 
                                              & vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data))),37);
    bufp->fullIData(oldp+3219,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr),27);
    bufp->fullQData(oldp+3220,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data),37);
    bufp->fullCData(oldp+3222,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest),2);
    bufp->fullQData(oldp+3223,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data),64);
    bufp->fullQData(oldp+3225,(vlSelf->main__DOT__wbu_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data),64);
    bufp->fullQData(oldp+3227,(vlSelf->main__DOT__wbu_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data),64);
    bufp->fullCData(oldp+3229,((((IData)(vlSelf->main__DOT__wbwide_wbu_arbiter_stb) 
                                 << 3U) | (((IData)(vlSelf->main__DOT__wbwide_zip_stb) 
                                            << 2U) 
                                           | (((IData)(vlSelf->main__DOT__wbwide_i2cm_stb) 
                                               << 1U) 
                                              | (IData)(vlSelf->main__DOT__wbwide_i2cdma_stb))))),4);
    bufp->fullCData(oldp+3230,((1U | (((IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_we) 
                                       << 3U) | (4U 
                                                 & (((IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)
                                                      ? (IData)(vlSelf->main__DOT__swic__DOT__cpu_we)
                                                      : 
                                                     (~ (IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner))) 
                                                    << 2U))))),4);
    __Vtemp_h708d16f1__0[0U] = (IData)((((QData)((IData)(vlSelf->main__DOT__wbwide_i2cm_addr)) 
                                         << 0x16U) 
                                        | (QData)((IData)(vlSelf->main__DOT__wbwide_i2cdma_addr))));
    __Vtemp_h708d16f1__0[1U] = ((vlSelf->main__DOT__wbwide_zip_addr 
                                 << 0xcU) | (IData)(
                                                    ((((QData)((IData)(vlSelf->main__DOT__wbwide_i2cm_addr)) 
                                                       << 0x16U) 
                                                      | (QData)((IData)(vlSelf->main__DOT__wbwide_i2cdma_addr))) 
                                                     >> 0x20U)));
    __Vtemp_h708d16f1__0[2U] = ((vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_addr 
                                 << 2U) | (vlSelf->main__DOT__wbwide_zip_addr 
                                           >> 0x14U));
    bufp->fullWData(oldp+3231,(__Vtemp_h708d16f1__0),88);
    __Vtemp_h95b27ed2__0[0U] = vlSelf->main__DOT__wbwide_i2cdma_data[0U];
    __Vtemp_h95b27ed2__0[1U] = vlSelf->main__DOT__wbwide_i2cdma_data[1U];
    __Vtemp_h95b27ed2__0[2U] = vlSelf->main__DOT__wbwide_i2cdma_data[2U];
    __Vtemp_h95b27ed2__0[3U] = vlSelf->main__DOT__wbwide_i2cdma_data[3U];
    __Vtemp_h95b27ed2__0[4U] = vlSelf->main__DOT__wbwide_i2cdma_data[4U];
    __Vtemp_h95b27ed2__0[5U] = vlSelf->main__DOT__wbwide_i2cdma_data[5U];
    __Vtemp_h95b27ed2__0[6U] = vlSelf->main__DOT__wbwide_i2cdma_data[6U];
    __Vtemp_h95b27ed2__0[7U] = vlSelf->main__DOT__wbwide_i2cdma_data[7U];
    __Vtemp_h95b27ed2__0[8U] = vlSelf->main__DOT__wbwide_i2cdma_data[8U];
    __Vtemp_h95b27ed2__0[9U] = vlSelf->main__DOT__wbwide_i2cdma_data[9U];
    __Vtemp_h95b27ed2__0[0xaU] = vlSelf->main__DOT__wbwide_i2cdma_data[0xaU];
    __Vtemp_h95b27ed2__0[0xbU] = vlSelf->main__DOT__wbwide_i2cdma_data[0xbU];
    __Vtemp_h95b27ed2__0[0xcU] = vlSelf->main__DOT__wbwide_i2cdma_data[0xcU];
    __Vtemp_h95b27ed2__0[0xdU] = vlSelf->main__DOT__wbwide_i2cdma_data[0xdU];
    __Vtemp_h95b27ed2__0[0xeU] = vlSelf->main__DOT__wbwide_i2cdma_data[0xeU];
    __Vtemp_h95b27ed2__0[0xfU] = vlSelf->main__DOT__wbwide_i2cdma_data[0xfU];
    __Vtemp_h95b27ed2__0[0x10U] = Vmain__ConstPool__CONST_h93e1b771_0[0U];
    __Vtemp_h95b27ed2__0[0x11U] = Vmain__ConstPool__CONST_h93e1b771_0[1U];
    __Vtemp_h95b27ed2__0[0x12U] = Vmain__ConstPool__CONST_h93e1b771_0[2U];
    __Vtemp_h95b27ed2__0[0x13U] = Vmain__ConstPool__CONST_h93e1b771_0[3U];
    __Vtemp_h95b27ed2__0[0x14U] = Vmain__ConstPool__CONST_h93e1b771_0[4U];
    __Vtemp_h95b27ed2__0[0x15U] = Vmain__ConstPool__CONST_h93e1b771_0[5U];
    __Vtemp_h95b27ed2__0[0x16U] = Vmain__ConstPool__CONST_h93e1b771_0[6U];
    __Vtemp_h95b27ed2__0[0x17U] = Vmain__ConstPool__CONST_h93e1b771_0[7U];
    __Vtemp_h95b27ed2__0[0x18U] = Vmain__ConstPool__CONST_h93e1b771_0[8U];
    __Vtemp_h95b27ed2__0[0x19U] = Vmain__ConstPool__CONST_h93e1b771_0[9U];
    __Vtemp_h95b27ed2__0[0x1aU] = Vmain__ConstPool__CONST_h93e1b771_0[0xaU];
    __Vtemp_h95b27ed2__0[0x1bU] = Vmain__ConstPool__CONST_h93e1b771_0[0xbU];
    __Vtemp_h95b27ed2__0[0x1cU] = Vmain__ConstPool__CONST_h93e1b771_0[0xcU];
    __Vtemp_h95b27ed2__0[0x1dU] = Vmain__ConstPool__CONST_h93e1b771_0[0xdU];
    __Vtemp_h95b27ed2__0[0x1eU] = Vmain__ConstPool__CONST_h93e1b771_0[0xeU];
    __Vtemp_h95b27ed2__0[0x1fU] = Vmain__ConstPool__CONST_h93e1b771_0[0xfU];
    if (vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner) {
        __Vtemp_h95b27ed2__0[0x20U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0U];
        __Vtemp_h95b27ed2__0[0x21U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[1U];
        __Vtemp_h95b27ed2__0[0x22U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[2U];
        __Vtemp_h95b27ed2__0[0x23U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[3U];
        __Vtemp_h95b27ed2__0[0x24U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[4U];
        __Vtemp_h95b27ed2__0[0x25U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[5U];
        __Vtemp_h95b27ed2__0[0x26U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[6U];
        __Vtemp_h95b27ed2__0[0x27U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[7U];
        __Vtemp_h95b27ed2__0[0x28U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[8U];
        __Vtemp_h95b27ed2__0[0x29U] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[9U];
        __Vtemp_h95b27ed2__0[0x2aU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xaU];
        __Vtemp_h95b27ed2__0[0x2bU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xbU];
        __Vtemp_h95b27ed2__0[0x2cU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xcU];
        __Vtemp_h95b27ed2__0[0x2dU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xdU];
        __Vtemp_h95b27ed2__0[0x2eU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xeU];
        __Vtemp_h95b27ed2__0[0x2fU] = vlSelf->main__DOT__swic__DOT__thecpu__DOT__mem_data[0xfU];
    } else {
        __Vtemp_h95b27ed2__0[0x20U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0U];
        __Vtemp_h95b27ed2__0[0x21U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[1U];
        __Vtemp_h95b27ed2__0[0x22U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[2U];
        __Vtemp_h95b27ed2__0[0x23U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[3U];
        __Vtemp_h95b27ed2__0[0x24U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[4U];
        __Vtemp_h95b27ed2__0[0x25U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[5U];
        __Vtemp_h95b27ed2__0[0x26U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[6U];
        __Vtemp_h95b27ed2__0[0x27U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[7U];
        __Vtemp_h95b27ed2__0[0x28U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[8U];
        __Vtemp_h95b27ed2__0[0x29U] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[9U];
        __Vtemp_h95b27ed2__0[0x2aU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xaU];
        __Vtemp_h95b27ed2__0[0x2bU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xbU];
        __Vtemp_h95b27ed2__0[0x2cU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xcU];
        __Vtemp_h95b27ed2__0[0x2dU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xdU];
        __Vtemp_h95b27ed2__0[0x2eU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xeU];
        __Vtemp_h95b27ed2__0[0x2fU] = vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_data[0xfU];
    }
    __Vtemp_h95b27ed2__0[0x30U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0U];
    __Vtemp_h95b27ed2__0[0x31U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[1U];
    __Vtemp_h95b27ed2__0[0x32U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[2U];
    __Vtemp_h95b27ed2__0[0x33U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[3U];
    __Vtemp_h95b27ed2__0[0x34U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[4U];
    __Vtemp_h95b27ed2__0[0x35U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[5U];
    __Vtemp_h95b27ed2__0[0x36U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[6U];
    __Vtemp_h95b27ed2__0[0x37U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[7U];
    __Vtemp_h95b27ed2__0[0x38U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[8U];
    __Vtemp_h95b27ed2__0[0x39U] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[9U];
    __Vtemp_h95b27ed2__0[0x3aU] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xaU];
    __Vtemp_h95b27ed2__0[0x3bU] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xbU];
    __Vtemp_h95b27ed2__0[0x3cU] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xcU];
    __Vtemp_h95b27ed2__0[0x3dU] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xdU];
    __Vtemp_h95b27ed2__0[0x3eU] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xeU];
    __Vtemp_h95b27ed2__0[0x3fU] = vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_data[0xfU];
    bufp->fullWData(oldp+3234,(__Vtemp_h95b27ed2__0),2048);
    __Vtemp_h7cab7483__0[0U] = (IData)(vlSelf->main__DOT__wbwide_i2cdma_sel);
    __Vtemp_h7cab7483__0[1U] = (IData)((vlSelf->main__DOT__wbwide_i2cdma_sel 
                                        >> 0x20U));
    __Vtemp_h7cab7483__0[2U] = 0xffffffffU;
    __Vtemp_h7cab7483__0[3U] = 0xffffffffU;
    __Vtemp_h7cab7483__0[4U] = (IData)(((IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)
                                         ? ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner)
                                             ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel
                                             : 0xffffffffffffffffULL)
                                         : ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner)
                                             ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_sel
                                             : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_sel)));
    __Vtemp_h7cab7483__0[5U] = (IData)((((IData)(vlSelf->main__DOT__swic__DOT__dmacvcpu__DOT__r_a_owner)
                                          ? ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__PRIORITY_DATA__DOT__pformem__DOT__r_a_owner)
                                              ? vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__GEN_SEL__DOT__r_wb_sel
                                              : 0xffffffffffffffffULL)
                                          : ((IData)(vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__u_arbiter__DOT__r_a_owner)
                                              ? vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__mm2s_rd_sel
                                              : vlSelf->main__DOT__swic__DOT__DMA__DOT__dma_controller__DOT__s2mm_wr_sel)) 
                                        >> 0x20U));
    __Vtemp_h7cab7483__0[6U] = (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_sel);
    __Vtemp_h7cab7483__0[7U] = (IData)((vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_sel 
                                        >> 0x20U));
    bufp->fullWData(oldp+3298,(__Vtemp_h7cab7483__0),256);
    bufp->fullCData(oldp+3306,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid) 
                                 << 3U) | (IData)(vlSelf->__VdfgTmp_h503d14d1__0))),4);
    bufp->fullCData(oldp+3307,(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_mack),4);
    bufp->fullWData(oldp+3308,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_mdata),2048);
    bufp->fullCData(oldp+3372,(vlSelf->main__DOT__wbwide_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr),4);
    bufp->fullCData(oldp+3373,(vlSelf->main__DOT__wbwide_xbar__DOT__request[0]),4);
    bufp->fullCData(oldp+3374,(vlSelf->main__DOT__wbwide_xbar__DOT__request[1]),4);
    bufp->fullCData(oldp+3375,(vlSelf->main__DOT__wbwide_xbar__DOT__request[2]),4);
    bufp->fullCData(oldp+3376,(vlSelf->main__DOT__wbwide_xbar__DOT__request[3]),4);
    bufp->fullCData(oldp+3377,(vlSelf->main__DOT__wbwide_xbar__DOT__requested[0]),3);
    bufp->fullCData(oldp+3378,(vlSelf->main__DOT__wbwide_xbar__DOT__requested[1]),3);
    bufp->fullCData(oldp+3379,(vlSelf->main__DOT__wbwide_xbar__DOT__requested[2]),3);
    bufp->fullCData(oldp+3380,(vlSelf->main__DOT__wbwide_xbar__DOT__requested[3]),3);
    bufp->fullCData(oldp+3381,(vlSelf->main__DOT__wbwide_xbar__DOT__grant[0]),4);
    bufp->fullCData(oldp+3382,(vlSelf->main__DOT__wbwide_xbar__DOT__grant[1]),4);
    bufp->fullCData(oldp+3383,(vlSelf->main__DOT__wbwide_xbar__DOT__grant[2]),4);
    bufp->fullCData(oldp+3384,(vlSelf->main__DOT__wbwide_xbar__DOT__grant[3]),4);
    bufp->fullCData(oldp+3385,(vlSelf->main__DOT__wbwide_xbar__DOT__mgrant),4);
    bufp->fullCData(oldp+3386,(vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[0]),6);
    bufp->fullCData(oldp+3387,(vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[1]),6);
    bufp->fullCData(oldp+3388,(vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[2]),6);
    bufp->fullCData(oldp+3389,(vlSelf->main__DOT__wbwide_xbar__DOT__w_mpending[3]),6);
    bufp->fullCData(oldp+3390,(vlSelf->main__DOT__wbwide_xbar__DOT__mfull),4);
    bufp->fullCData(oldp+3391,(vlSelf->main__DOT__wbwide_xbar__DOT__mnearfull),4);
    bufp->fullCData(oldp+3392,(vlSelf->main__DOT__wbwide_xbar__DOT__mempty),4);
    bufp->fullCData(oldp+3393,(vlSelf->main__DOT__wbwide_xbar__DOT__m_stb),4);
    bufp->fullCData(oldp+3394,((((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_valid) 
                                 << 3U) | (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_valid) 
                                            << 2U) 
                                           | (((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_valid) 
                                               << 1U) 
                                              | (IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_valid))))),4);
    bufp->fullBit(oldp+3395,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel));
    bufp->fullBit(oldp+3396,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__stay_on_channel));
    bufp->fullBit(oldp+3397,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__stay_on_channel));
    bufp->fullBit(oldp+3398,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__stay_on_channel));
    bufp->fullCData(oldp+3399,(vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__0__KET____DOT__lclpending),6);
    bufp->fullCData(oldp+3400,(vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__1__KET____DOT__lclpending),6);
    bufp->fullCData(oldp+3401,(vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__2__KET____DOT__lclpending),6);
    bufp->fullCData(oldp+3402,(vlSelf->main__DOT__wbwide_xbar__DOT__COUNT_PENDING_TRANSACTIONS__BRA__3__KET____DOT__lclpending),6);
    bufp->fullBit(oldp+3403,((1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U] 
                                    >> 0x16U))));
    bufp->fullIData(oldp+3404,((0x3fffffU & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U])),22);
    __Vtemp_h53a5df10__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[2U];
    __Vtemp_h53a5df10__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[3U];
    __Vtemp_h53a5df10__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[4U];
    __Vtemp_h53a5df10__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[5U];
    __Vtemp_h53a5df10__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[6U];
    __Vtemp_h53a5df10__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[7U];
    __Vtemp_h53a5df10__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[8U];
    __Vtemp_h53a5df10__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[9U];
    __Vtemp_h53a5df10__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_h53a5df10__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_h53a5df10__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_h53a5df10__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_h53a5df10__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_h53a5df10__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_h53a5df10__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_h53a5df10__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x11U];
    bufp->fullWData(oldp+3405,(__Vtemp_h53a5df10__0),512);
    bufp->fullQData(oldp+3421,((((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[1U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0U])))),64);
    bufp->fullCData(oldp+3423,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__decoded),4);
    bufp->fullBit(oldp+3424,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))));
    __Vtemp_hb52cb2db__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0U];
    __Vtemp_hb52cb2db__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[1U];
    __Vtemp_hb52cb2db__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[2U];
    __Vtemp_hb52cb2db__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[3U];
    __Vtemp_hb52cb2db__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[4U];
    __Vtemp_hb52cb2db__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[5U];
    __Vtemp_hb52cb2db__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[6U];
    __Vtemp_hb52cb2db__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[7U];
    __Vtemp_hb52cb2db__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[8U];
    __Vtemp_hb52cb2db__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[9U];
    __Vtemp_hb52cb2db__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_hb52cb2db__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_hb52cb2db__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_hb52cb2db__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_hb52cb2db__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_hb52cb2db__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_hb52cb2db__0[0x10U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_hb52cb2db__0[0x11U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x11U];
    __Vtemp_hb52cb2db__0[0x12U] = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data[0x12U] 
                                         >> 0x16U));
    bufp->fullWData(oldp+3425,(__Vtemp_hb52cb2db__0),577);
    bufp->fullBit(oldp+3444,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_valid));
    bufp->fullIData(oldp+3445,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_addr),22);
    bufp->fullWData(oldp+3446,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data),577);
    bufp->fullCData(oldp+3465,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest),3);
    bufp->fullWData(oldp+3466,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__iskid__i_data),599);
    bufp->fullWData(oldp+3485,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data),599);
    bufp->fullWData(oldp+3504,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_data),599);
    bufp->fullBit(oldp+3523,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+3524,((1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U] 
                                    >> 0x16U))));
    bufp->fullIData(oldp+3525,((0x3fffffU & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U])),22);
    __Vtemp_hebded4b4__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[2U];
    __Vtemp_hebded4b4__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[3U];
    __Vtemp_hebded4b4__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[4U];
    __Vtemp_hebded4b4__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[5U];
    __Vtemp_hebded4b4__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[6U];
    __Vtemp_hebded4b4__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[7U];
    __Vtemp_hebded4b4__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[8U];
    __Vtemp_hebded4b4__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[9U];
    __Vtemp_hebded4b4__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_hebded4b4__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_hebded4b4__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_hebded4b4__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_hebded4b4__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_hebded4b4__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_hebded4b4__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_hebded4b4__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x11U];
    bufp->fullWData(oldp+3526,(__Vtemp_hebded4b4__0),512);
    bufp->fullQData(oldp+3542,((((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[1U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0U])))),64);
    bufp->fullCData(oldp+3544,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__decoded),4);
    bufp->fullBit(oldp+3545,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))));
    __Vtemp_h0a2cdfa5__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0U];
    __Vtemp_h0a2cdfa5__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[1U];
    __Vtemp_h0a2cdfa5__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[2U];
    __Vtemp_h0a2cdfa5__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[3U];
    __Vtemp_h0a2cdfa5__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[4U];
    __Vtemp_h0a2cdfa5__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[5U];
    __Vtemp_h0a2cdfa5__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[6U];
    __Vtemp_h0a2cdfa5__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[7U];
    __Vtemp_h0a2cdfa5__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[8U];
    __Vtemp_h0a2cdfa5__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[9U];
    __Vtemp_h0a2cdfa5__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_h0a2cdfa5__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_h0a2cdfa5__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_h0a2cdfa5__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_h0a2cdfa5__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_h0a2cdfa5__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_h0a2cdfa5__0[0x10U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_h0a2cdfa5__0[0x11U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x11U];
    __Vtemp_h0a2cdfa5__0[0x12U] = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data[0x12U] 
                                         >> 0x16U));
    bufp->fullWData(oldp+3546,(__Vtemp_h0a2cdfa5__0),577);
    bufp->fullBit(oldp+3565,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_valid));
    bufp->fullIData(oldp+3566,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_addr),22);
    bufp->fullWData(oldp+3567,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__adcd__o_data),577);
    bufp->fullCData(oldp+3586,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__adcd__DOT__prerequest),3);
    __Vtemp_he57bd368__0[0U] = Vmain__ConstPool__CONST_hb679b2e5_0[0U];
    __Vtemp_he57bd368__0[1U] = Vmain__ConstPool__CONST_hb679b2e5_0[1U];
    __Vtemp_he57bd368__0[2U] = Vmain__ConstPool__CONST_hb679b2e5_0[2U];
    __Vtemp_he57bd368__0[3U] = Vmain__ConstPool__CONST_hb679b2e5_0[3U];
    __Vtemp_he57bd368__0[4U] = Vmain__ConstPool__CONST_hb679b2e5_0[4U];
    __Vtemp_he57bd368__0[5U] = Vmain__ConstPool__CONST_hb679b2e5_0[5U];
    __Vtemp_he57bd368__0[6U] = Vmain__ConstPool__CONST_hb679b2e5_0[6U];
    __Vtemp_he57bd368__0[7U] = Vmain__ConstPool__CONST_hb679b2e5_0[7U];
    __Vtemp_he57bd368__0[8U] = Vmain__ConstPool__CONST_hb679b2e5_0[8U];
    __Vtemp_he57bd368__0[9U] = Vmain__ConstPool__CONST_hb679b2e5_0[9U];
    __Vtemp_he57bd368__0[0xaU] = Vmain__ConstPool__CONST_hb679b2e5_0[0xaU];
    __Vtemp_he57bd368__0[0xbU] = Vmain__ConstPool__CONST_hb679b2e5_0[0xbU];
    __Vtemp_he57bd368__0[0xcU] = Vmain__ConstPool__CONST_hb679b2e5_0[0xcU];
    __Vtemp_he57bd368__0[0xdU] = Vmain__ConstPool__CONST_hb679b2e5_0[0xdU];
    __Vtemp_he57bd368__0[0xeU] = Vmain__ConstPool__CONST_hb679b2e5_0[0xeU];
    __Vtemp_he57bd368__0[0xfU] = Vmain__ConstPool__CONST_hb679b2e5_0[0xfU];
    __Vtemp_he57bd368__0[0x10U] = Vmain__ConstPool__CONST_hb679b2e5_0[0x10U];
    __Vtemp_he57bd368__0[0x11U] = Vmain__ConstPool__CONST_hb679b2e5_0[0x11U];
    __Vtemp_he57bd368__0[0x12U] = vlSelf->main__DOT__wbwide_i2cm_addr;
    bufp->fullWData(oldp+3587,(__Vtemp_he57bd368__0),599);
    bufp->fullWData(oldp+3606,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__1__KET____DOT__iskid__o_data),599);
    bufp->fullWData(oldp+3625,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_data),599);
    bufp->fullBit(oldp+3644,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+3645,((1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x12U] 
                                    >> 0x16U))));
    bufp->fullIData(oldp+3646,((0x3fffffU & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x12U])),22);
    __Vtemp_h0964a254__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[2U];
    __Vtemp_h0964a254__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[3U];
    __Vtemp_h0964a254__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[4U];
    __Vtemp_h0964a254__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[5U];
    __Vtemp_h0964a254__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[6U];
    __Vtemp_h0964a254__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[7U];
    __Vtemp_h0964a254__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[8U];
    __Vtemp_h0964a254__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[9U];
    __Vtemp_h0964a254__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_h0964a254__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_h0964a254__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_h0964a254__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_h0964a254__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_h0964a254__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_h0964a254__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_h0964a254__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x11U];
    bufp->fullWData(oldp+3647,(__Vtemp_h0964a254__0),512);
    bufp->fullQData(oldp+3663,((((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[1U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0U])))),64);
    bufp->fullCData(oldp+3665,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__decoded),4);
    bufp->fullBit(oldp+3666,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))));
    __Vtemp_h925b4b87__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0U];
    __Vtemp_h925b4b87__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[1U];
    __Vtemp_h925b4b87__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[2U];
    __Vtemp_h925b4b87__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[3U];
    __Vtemp_h925b4b87__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[4U];
    __Vtemp_h925b4b87__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[5U];
    __Vtemp_h925b4b87__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[6U];
    __Vtemp_h925b4b87__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[7U];
    __Vtemp_h925b4b87__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[8U];
    __Vtemp_h925b4b87__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[9U];
    __Vtemp_h925b4b87__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_h925b4b87__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_h925b4b87__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_h925b4b87__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_h925b4b87__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_h925b4b87__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_h925b4b87__0[0x10U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_h925b4b87__0[0x11U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x11U];
    __Vtemp_h925b4b87__0[0x12U] = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data[0x12U] 
                                         >> 0x16U));
    bufp->fullWData(oldp+3667,(__Vtemp_h925b4b87__0),577);
    bufp->fullBit(oldp+3686,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_valid));
    bufp->fullIData(oldp+3687,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_addr),22);
    bufp->fullWData(oldp+3688,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__adcd__o_data),577);
    bufp->fullCData(oldp+3707,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__adcd__DOT__prerequest),3);
    bufp->fullWData(oldp+3708,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__iskid__i_data),599);
    bufp->fullWData(oldp+3727,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__2__KET____DOT__iskid__o_data),599);
    bufp->fullWData(oldp+3746,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_data),599);
    bufp->fullBit(oldp+3765,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid));
    bufp->fullBit(oldp+3766,((1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U] 
                                    >> 0x16U))));
    bufp->fullIData(oldp+3767,((0x3fffffU & vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U])),22);
    __Vtemp_h5b5f8605__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[2U];
    __Vtemp_h5b5f8605__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[3U];
    __Vtemp_h5b5f8605__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[4U];
    __Vtemp_h5b5f8605__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[5U];
    __Vtemp_h5b5f8605__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[6U];
    __Vtemp_h5b5f8605__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[7U];
    __Vtemp_h5b5f8605__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[8U];
    __Vtemp_h5b5f8605__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[9U];
    __Vtemp_h5b5f8605__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_h5b5f8605__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_h5b5f8605__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_h5b5f8605__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_h5b5f8605__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_h5b5f8605__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_h5b5f8605__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_h5b5f8605__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x11U];
    bufp->fullWData(oldp+3768,(__Vtemp_h5b5f8605__0),512);
    bufp->fullQData(oldp+3784,((((QData)((IData)(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[1U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0U])))),64);
    bufp->fullCData(oldp+3786,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__decoded),4);
    bufp->fullBit(oldp+3787,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_valid)))));
    __Vtemp_hfe9179b2__0[0U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0U];
    __Vtemp_hfe9179b2__0[1U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[1U];
    __Vtemp_hfe9179b2__0[2U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[2U];
    __Vtemp_hfe9179b2__0[3U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[3U];
    __Vtemp_hfe9179b2__0[4U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[4U];
    __Vtemp_hfe9179b2__0[5U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[5U];
    __Vtemp_hfe9179b2__0[6U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[6U];
    __Vtemp_hfe9179b2__0[7U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[7U];
    __Vtemp_hfe9179b2__0[8U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[8U];
    __Vtemp_hfe9179b2__0[9U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[9U];
    __Vtemp_hfe9179b2__0[0xaU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xaU];
    __Vtemp_hfe9179b2__0[0xbU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xbU];
    __Vtemp_hfe9179b2__0[0xcU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xcU];
    __Vtemp_hfe9179b2__0[0xdU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xdU];
    __Vtemp_hfe9179b2__0[0xeU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xeU];
    __Vtemp_hfe9179b2__0[0xfU] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0xfU];
    __Vtemp_hfe9179b2__0[0x10U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x10U];
    __Vtemp_hfe9179b2__0[0x11U] = vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x11U];
    __Vtemp_hfe9179b2__0[0x12U] = (1U & (vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data[0x12U] 
                                         >> 0x16U));
    bufp->fullWData(oldp+3788,(__Vtemp_hfe9179b2__0),577);
    bufp->fullBit(oldp+3807,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_valid));
    bufp->fullIData(oldp+3808,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_addr),22);
    bufp->fullWData(oldp+3809,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__adcd__o_data),577);
    bufp->fullCData(oldp+3828,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__adcd__DOT__prerequest),3);
    bufp->fullWData(oldp+3829,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__iskid__i_data),599);
    bufp->fullWData(oldp+3848,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__3__KET____DOT__iskid__o_data),599);
    bufp->fullWData(oldp+3867,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__iskid__DOT__LOGIC__DOT__r_data),599);
    bufp->fullCData(oldp+3886,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__r_sindex),2);
    bufp->fullCData(oldp+3887,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__r_sindex),2);
    bufp->fullCData(oldp+3888,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__r_sindex),2);
    bufp->fullSData(oldp+3889,((((IData)(vlSelf->main__DOT__wb32_ddr3_phy_ack) 
                                 << 0xbU) | (((IData)(vlSelf->main__DOT__r_cfg_ack) 
                                              << 0xaU) 
                                             | (((IData)(vlSelf->main__DOT__r_wb32_sio_ack) 
                                                 << 9U) 
                                                | (((IData)(vlSelf->main__DOT__wb32_sdcard_ack) 
                                                    << 8U) 
                                                   | (((IData)(vlSelf->main__DOT__wb32_fan_ack) 
                                                       << 7U) 
                                                      | (((IData)(vlSelf->main__DOT__wb32_emmc_ack) 
                                                          << 6U) 
                                                         | (((IData)(vlSelf->main__DOT__wb32_uart_ack) 
                                                             << 5U) 
                                                            | (((IData)(vlSelf->main__DOT__wb32_i2cdma_ack) 
                                                                << 4U) 
                                                               | (((IData)(vlSelf->main__DOT__wb32_i2cs_ack) 
                                                                   << 3U) 
                                                                  | (((IData)(vlSelf->main__DOT__sdioscopei__DOT__br_wb_ack) 
                                                                      << 2U) 
                                                                     | (((IData)(vlSelf->main__DOT__i2cscopei__DOT__br_wb_ack) 
                                                                         << 1U) 
                                                                        | (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack))))))))))))),12);
    __Vtemp_ha40692d2__0[0U] = vlSelf->main__DOT__emmcscopei__DOT__o_bus_data;
    __Vtemp_ha40692d2__0[1U] = vlSelf->main__DOT__i2cscopei__DOT__o_bus_data;
    __Vtemp_ha40692d2__0[2U] = vlSelf->main__DOT__sdioscopei__DOT__o_bus_data;
    __Vtemp_ha40692d2__0[3U] = vlSelf->main__DOT__i2ci__DOT__bus_read_data;
    __Vtemp_ha40692d2__0[4U] = vlSelf->main__DOT__wb32_i2cdma_idata;
    __Vtemp_ha40692d2__0[5U] = vlSelf->main__DOT__wb32_uart_idata;
    __Vtemp_ha40692d2__0[6U] = vlSelf->main__DOT__wb32_emmc_idata;
    __Vtemp_ha40692d2__0[7U] = vlSelf->main__DOT__wb32_fan_idata;
    __Vtemp_ha40692d2__0[8U] = vlSelf->main__DOT__wb32_sdcard_idata;
    __Vtemp_ha40692d2__0[9U] = vlSelf->main__DOT__r_wb32_sio_data;
    __Vtemp_ha40692d2__0[0xaU] = (IData)(((QData)((IData)(vlSelf->main__DOT__wb32_ddr3_phy_idata)) 
                                          << 0x20U));
    __Vtemp_ha40692d2__0[0xbU] = (IData)((((QData)((IData)(vlSelf->main__DOT__wb32_ddr3_phy_idata)) 
                                           << 0x20U) 
                                          >> 0x20U));
    bufp->fullWData(oldp+3890,(__Vtemp_ha40692d2__0),384);
    bufp->fullIData(oldp+3902,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[0]),32);
    bufp->fullIData(oldp+3903,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[1]),32);
    bufp->fullIData(oldp+3904,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[2]),32);
    bufp->fullIData(oldp+3905,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[3]),32);
    bufp->fullIData(oldp+3906,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[4]),32);
    bufp->fullIData(oldp+3907,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[5]),32);
    bufp->fullIData(oldp+3908,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[6]),32);
    bufp->fullIData(oldp+3909,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[7]),32);
    bufp->fullIData(oldp+3910,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[8]),32);
    bufp->fullIData(oldp+3911,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[9]),32);
    bufp->fullIData(oldp+3912,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[10]),32);
    bufp->fullIData(oldp+3913,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[11]),32);
    bufp->fullIData(oldp+3914,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[12]),32);
    bufp->fullIData(oldp+3915,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[13]),32);
    bufp->fullIData(oldp+3916,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[14]),32);
    bufp->fullIData(oldp+3917,(vlSelf->main__DOT__wb32_xbar__DOT__s_data[15]),32);
    bufp->fullCData(oldp+3918,((((IData)(vlSelf->main__DOT__wbwide_ddr3_controller_stall) 
                                 << 2U) | (IData)(vlSelf->main__DOT__wbwide_wbdown_stall))),3);
    bufp->fullCData(oldp+3919,((((vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q
                                  [0U] & (0xeU == (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__state_calibrate))) 
                                 << 2U) | (((IData)(vlSelf->main__DOT__wbwide_bkram_ack) 
                                            << 1U) 
                                           | (IData)(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_ack)))),3);
    __Vtemp_h8a06d21b__0[0U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0U];
    __Vtemp_h8a06d21b__0[1U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[1U];
    __Vtemp_h8a06d21b__0[2U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[2U];
    __Vtemp_h8a06d21b__0[3U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[3U];
    __Vtemp_h8a06d21b__0[4U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[4U];
    __Vtemp_h8a06d21b__0[5U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[5U];
    __Vtemp_h8a06d21b__0[6U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[6U];
    __Vtemp_h8a06d21b__0[7U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[7U];
    __Vtemp_h8a06d21b__0[8U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[8U];
    __Vtemp_h8a06d21b__0[9U] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[9U];
    __Vtemp_h8a06d21b__0[0xaU] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xaU];
    __Vtemp_h8a06d21b__0[0xbU] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xbU];
    __Vtemp_h8a06d21b__0[0xcU] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xcU];
    __Vtemp_h8a06d21b__0[0xdU] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xdU];
    __Vtemp_h8a06d21b__0[0xeU] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xeU];
    __Vtemp_h8a06d21b__0[0xfU] = vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_data[0xfU];
    __Vtemp_h8a06d21b__0[0x10U] = vlSelf->main__DOT__wbwide_bkram_idata[0U];
    __Vtemp_h8a06d21b__0[0x11U] = vlSelf->main__DOT__wbwide_bkram_idata[1U];
    __Vtemp_h8a06d21b__0[0x12U] = vlSelf->main__DOT__wbwide_bkram_idata[2U];
    __Vtemp_h8a06d21b__0[0x13U] = vlSelf->main__DOT__wbwide_bkram_idata[3U];
    __Vtemp_h8a06d21b__0[0x14U] = vlSelf->main__DOT__wbwide_bkram_idata[4U];
    __Vtemp_h8a06d21b__0[0x15U] = vlSelf->main__DOT__wbwide_bkram_idata[5U];
    __Vtemp_h8a06d21b__0[0x16U] = vlSelf->main__DOT__wbwide_bkram_idata[6U];
    __Vtemp_h8a06d21b__0[0x17U] = vlSelf->main__DOT__wbwide_bkram_idata[7U];
    __Vtemp_h8a06d21b__0[0x18U] = vlSelf->main__DOT__wbwide_bkram_idata[8U];
    __Vtemp_h8a06d21b__0[0x19U] = vlSelf->main__DOT__wbwide_bkram_idata[9U];
    __Vtemp_h8a06d21b__0[0x1aU] = vlSelf->main__DOT__wbwide_bkram_idata[0xaU];
    __Vtemp_h8a06d21b__0[0x1bU] = vlSelf->main__DOT__wbwide_bkram_idata[0xbU];
    __Vtemp_h8a06d21b__0[0x1cU] = vlSelf->main__DOT__wbwide_bkram_idata[0xcU];
    __Vtemp_h8a06d21b__0[0x1dU] = vlSelf->main__DOT__wbwide_bkram_idata[0xdU];
    __Vtemp_h8a06d21b__0[0x1eU] = vlSelf->main__DOT__wbwide_bkram_idata[0xeU];
    __Vtemp_h8a06d21b__0[0x1fU] = vlSelf->main__DOT__wbwide_bkram_idata[0xfU];
    __Vtemp_h8a06d21b__0[0x20U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0U];
    __Vtemp_h8a06d21b__0[0x21U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][1U];
    __Vtemp_h8a06d21b__0[0x22U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][2U];
    __Vtemp_h8a06d21b__0[0x23U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][3U];
    __Vtemp_h8a06d21b__0[0x24U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][4U];
    __Vtemp_h8a06d21b__0[0x25U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][5U];
    __Vtemp_h8a06d21b__0[0x26U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][6U];
    __Vtemp_h8a06d21b__0[0x27U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][7U];
    __Vtemp_h8a06d21b__0[0x28U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][8U];
    __Vtemp_h8a06d21b__0[0x29U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][9U];
    __Vtemp_h8a06d21b__0[0x2aU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xaU];
    __Vtemp_h8a06d21b__0[0x2bU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xbU];
    __Vtemp_h8a06d21b__0[0x2cU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xcU];
    __Vtemp_h8a06d21b__0[0x2dU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xdU];
    __Vtemp_h8a06d21b__0[0x2eU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xeU];
    __Vtemp_h8a06d21b__0[0x2fU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xfU];
    bufp->fullWData(oldp+3920,(__Vtemp_h8a06d21b__0),1536);
    bufp->fullWData(oldp+3968,(vlSelf->main__DOT__wbwide_xbar__DOT__s_data[0]),512);
    bufp->fullWData(oldp+3984,(vlSelf->main__DOT__wbwide_xbar__DOT__s_data[1]),512);
    bufp->fullWData(oldp+4000,(vlSelf->main__DOT__wbwide_xbar__DOT__s_data[2]),512);
    bufp->fullWData(oldp+4016,(vlSelf->main__DOT__wbwide_xbar__DOT__s_data[3]),512);
    bufp->fullBit(oldp+4032,((1U & (vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q
                                    [0U] >> 1U))));
    bufp->fullBit(oldp+4033,(vlSelf->main__DOT__wbwide_ddr3_controller_stall));
    bufp->fullBit(oldp+4034,((vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q
                              [0U] & (0xeU == (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__state_calibrate)))));
    __Vtemp_hc035b709__1[0U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0U];
    __Vtemp_hc035b709__1[1U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][1U];
    __Vtemp_hc035b709__1[2U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][2U];
    __Vtemp_hc035b709__1[3U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][3U];
    __Vtemp_hc035b709__1[4U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][4U];
    __Vtemp_hc035b709__1[5U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][5U];
    __Vtemp_hc035b709__1[6U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][6U];
    __Vtemp_hc035b709__1[7U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][7U];
    __Vtemp_hc035b709__1[8U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][8U];
    __Vtemp_hc035b709__1[9U] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][9U];
    __Vtemp_hc035b709__1[0xaU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xaU];
    __Vtemp_hc035b709__1[0xbU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xbU];
    __Vtemp_hc035b709__1[0xcU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xcU];
    __Vtemp_hc035b709__1[0xdU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xdU];
    __Vtemp_hc035b709__1[0xeU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xeU];
    __Vtemp_hc035b709__1[0xfU] = vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q
        [vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data][0xfU];
    bufp->fullWData(oldp+4035,(__Vtemp_hc035b709__1),512);
    bufp->fullBit(oldp+4051,(vlSelf->main__DOT__wb32_ddr3_phy_stall));
    bufp->fullBit(oldp+4052,(vlSelf->main__DOT__wb32_ddr3_phy_ack));
    bufp->fullIData(oldp+4053,(vlSelf->main__DOT__wb32_ddr3_phy_idata),32);
    bufp->fullIData(oldp+4054,(vlSelf->main__DOT__ddr3_controller_inst__DOT__index),32);
    bufp->fullCData(oldp+4055,(vlSelf->main__DOT__ddr3_controller_inst__DOT__instruction_address),5);
    bufp->fullIData(oldp+4056,(vlSelf->main__DOT__ddr3_controller_inst__DOT__instruction),28);
    bufp->fullSData(oldp+4057,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_counter),16);
    bufp->fullBit(oldp+4058,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_counter_is_zero));
    bufp->fullBit(oldp+4059,(vlSelf->main__DOT__ddr3_controller_inst__DOT__reset_done));
    bufp->fullBit(oldp+4060,(vlSelf->main__DOT__ddr3_controller_inst__DOT__pause_counter));
    bufp->fullBit(oldp+4061,((2U == (IData)(vlSelf->main__DOT__ddr3_controller_inst__DOT__state_calibrate))));
    bufp->fullBit(oldp+4062,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_update));
    bufp->fullCData(oldp+4063,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_q),8);
    bufp->fullSData(oldp+4064,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[0]),14);
    bufp->fullSData(oldp+4065,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[1]),14);
    bufp->fullSData(oldp+4066,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[2]),14);
    bufp->fullSData(oldp+4067,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[3]),14);
    bufp->fullSData(oldp+4068,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[4]),14);
    bufp->fullSData(oldp+4069,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[5]),14);
    bufp->fullSData(oldp+4070,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[6]),14);
    bufp->fullSData(oldp+4071,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_q[7]),14);
    bufp->fullBit(oldp+4072,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_pending));
    bufp->fullBit(oldp+4073,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_aux));
    bufp->fullBit(oldp+4074,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_we));
    bufp->fullWData(oldp+4075,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_data),512);
    bufp->fullQData(oldp+4091,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_dm),64);
    bufp->fullSData(oldp+4093,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_col),10);
    bufp->fullCData(oldp+4094,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_bank),3);
    bufp->fullSData(oldp+4095,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_row),14);
    bufp->fullCData(oldp+4096,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_next_bank),3);
    bufp->fullSData(oldp+4097,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_next_row),14);
    bufp->fullBit(oldp+4098,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_pending));
    bufp->fullBit(oldp+4099,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_aux));
    bufp->fullBit(oldp+4100,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_we));
    bufp->fullQData(oldp+4101,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm_unaligned),64);
    bufp->fullQData(oldp+4103,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm[0]),64);
    bufp->fullQData(oldp+4105,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_dm[1]),64);
    bufp->fullWData(oldp+4107,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data_unaligned),512);
    bufp->fullWData(oldp+4123,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[0]),512);
    bufp->fullWData(oldp+4139,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_data[1]),512);
    bufp->fullQData(oldp+4155,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[0]),64);
    bufp->fullQData(oldp+4157,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[1]),64);
    bufp->fullQData(oldp+4159,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[2]),64);
    bufp->fullQData(oldp+4161,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[3]),64);
    bufp->fullQData(oldp+4163,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[4]),64);
    bufp->fullQData(oldp+4165,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[5]),64);
    bufp->fullQData(oldp+4167,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[6]),64);
    bufp->fullQData(oldp+4169,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_data[7]),64);
    bufp->fullCData(oldp+4171,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[0]),8);
    bufp->fullCData(oldp+4172,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[1]),8);
    bufp->fullCData(oldp+4173,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[2]),8);
    bufp->fullCData(oldp+4174,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[3]),8);
    bufp->fullCData(oldp+4175,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[4]),8);
    bufp->fullCData(oldp+4176,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[5]),8);
    bufp->fullCData(oldp+4177,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[6]),8);
    bufp->fullCData(oldp+4178,(vlSelf->main__DOT__ddr3_controller_inst__DOT__unaligned_dm[7]),8);
    bufp->fullSData(oldp+4179,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_col),10);
    bufp->fullCData(oldp+4180,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_bank),3);
    bufp->fullSData(oldp+4181,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_row),14);
    bufp->fullCData(oldp+4182,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[0]),4);
    bufp->fullCData(oldp+4183,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[1]),4);
    bufp->fullCData(oldp+4184,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[2]),4);
    bufp->fullCData(oldp+4185,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[3]),4);
    bufp->fullCData(oldp+4186,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[4]),4);
    bufp->fullCData(oldp+4187,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[5]),4);
    bufp->fullCData(oldp+4188,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[6]),4);
    bufp->fullCData(oldp+4189,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_q[7]),4);
    bufp->fullCData(oldp+4190,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[0]),4);
    bufp->fullCData(oldp+4191,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[1]),4);
    bufp->fullCData(oldp+4192,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[2]),4);
    bufp->fullCData(oldp+4193,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[3]),4);
    bufp->fullCData(oldp+4194,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[4]),4);
    bufp->fullCData(oldp+4195,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[5]),4);
    bufp->fullCData(oldp+4196,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[6]),4);
    bufp->fullCData(oldp+4197,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_q[7]),4);
    bufp->fullCData(oldp+4198,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[0]),4);
    bufp->fullCData(oldp+4199,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[1]),4);
    bufp->fullCData(oldp+4200,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[2]),4);
    bufp->fullCData(oldp+4201,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[3]),4);
    bufp->fullCData(oldp+4202,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[4]),4);
    bufp->fullCData(oldp+4203,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[5]),4);
    bufp->fullCData(oldp+4204,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[6]),4);
    bufp->fullCData(oldp+4205,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_q[7]),4);
    bufp->fullCData(oldp+4206,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[0]),4);
    bufp->fullCData(oldp+4207,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[1]),4);
    bufp->fullCData(oldp+4208,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[2]),4);
    bufp->fullCData(oldp+4209,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[3]),4);
    bufp->fullCData(oldp+4210,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[4]),4);
    bufp->fullCData(oldp+4211,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[5]),4);
    bufp->fullCData(oldp+4212,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[6]),4);
    bufp->fullCData(oldp+4213,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_q[7]),4);
    bufp->fullBit(oldp+4214,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_odt_q));
    bufp->fullBit(oldp+4215,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_stall_q));
    bufp->fullCData(oldp+4216,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_q),2);
    bufp->fullBit(oldp+4217,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_d));
    bufp->fullCData(oldp+4218,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs),3);
    bufp->fullCData(oldp+4219,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dqs_val),3);
    bufp->fullBit(oldp+4220,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq_q));
    bufp->fullBit(oldp+4221,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq_d));
    bufp->fullCData(oldp+4222,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_dq),4);
    bufp->fullCData(oldp+4223,(vlSelf->main__DOT__ddr3_controller_inst__DOT__state_calibrate),5);
    bufp->fullQData(oldp+4224,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_store),40);
    bufp->fullCData(oldp+4226,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_count_repeat),4);
    bufp->fullCData(oldp+4227,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index),6);
    bufp->fullCData(oldp+4228,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_stored),6);
    bufp->fullCData(oldp+4229,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index),6);
    bufp->fullCData(oldp+4230,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index_orig),6);
    bufp->fullCData(oldp+4231,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dq_target_index),6);
    bufp->fullCData(oldp+4232,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_target_index_value),6);
    bufp->fullBit(oldp+4233,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_start_index_repeat));
    bufp->fullCData(oldp+4234,(vlSelf->main__DOT__ddr3_controller_inst__DOT__train_delay),2);
    bufp->fullCData(oldp+4235,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_data),4);
    bufp->fullCData(oldp+4236,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_level_feedback),5);
    bufp->fullBit(oldp+4237,(vlSelf->main__DOT__ddr3_controller_inst__DOT__initial_dqs));
    bufp->fullCData(oldp+4238,(vlSelf->main__DOT__ddr3_controller_inst__DOT__lane),3);
    bufp->fullCData(oldp+4239,(vlSelf->main__DOT__ddr3_controller_inst__DOT__lane_times_8),6);
    bufp->fullSData(oldp+4240,(vlSelf->main__DOT__ddr3_controller_inst__DOT__dqs_bitslip_arrangement),16);
    bufp->fullCData(oldp+4241,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe_max),4);
    bufp->fullCData(oldp+4242,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[0]),4);
    bufp->fullCData(oldp+4243,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[1]),4);
    bufp->fullCData(oldp+4244,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[2]),4);
    bufp->fullCData(oldp+4245,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[3]),4);
    bufp->fullCData(oldp+4246,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[4]),4);
    bufp->fullCData(oldp+4247,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[5]),4);
    bufp->fullCData(oldp+4248,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[6]),4);
    bufp->fullCData(oldp+4249,(vlSelf->main__DOT__ddr3_controller_inst__DOT__added_read_pipe[7]),4);
    bufp->fullCData(oldp+4250,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[0]),2);
    bufp->fullCData(oldp+4251,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[1]),2);
    bufp->fullCData(oldp+4252,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[2]),2);
    bufp->fullCData(oldp+4253,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[3]),2);
    bufp->fullCData(oldp+4254,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_q[4]),2);
    bufp->fullCData(oldp+4255,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[0]),2);
    bufp->fullCData(oldp+4256,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[1]),2);
    bufp->fullCData(oldp+4257,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[2]),2);
    bufp->fullCData(oldp+4258,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[3]),2);
    bufp->fullCData(oldp+4259,(vlSelf->main__DOT__ddr3_controller_inst__DOT__shift_reg_read_pipe_d[4]),2);
    bufp->fullBit(oldp+4260,(vlSelf->main__DOT__ddr3_controller_inst__DOT__index_read_pipe));
    bufp->fullBit(oldp+4261,(vlSelf->main__DOT__ddr3_controller_inst__DOT__index_wb_data));
    bufp->fullSData(oldp+4262,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_read_pipe[0]),16);
    bufp->fullSData(oldp+4263,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_read_pipe[1]),16);
    bufp->fullWData(oldp+4264,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q[0]),512);
    bufp->fullWData(oldp+4280,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_data_q[1]),512);
    bufp->fullCData(oldp+4296,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[0]),2);
    bufp->fullCData(oldp+4297,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[1]),2);
    bufp->fullCData(oldp+4298,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[2]),2);
    bufp->fullCData(oldp+4299,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[3]),2);
    bufp->fullCData(oldp+4300,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[4]),2);
    bufp->fullCData(oldp+4301,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[5]),2);
    bufp->fullCData(oldp+4302,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[6]),2);
    bufp->fullCData(oldp+4303,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[7]),2);
    bufp->fullCData(oldp+4304,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[8]),2);
    bufp->fullCData(oldp+4305,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[9]),2);
    bufp->fullCData(oldp+4306,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[10]),2);
    bufp->fullCData(oldp+4307,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[11]),2);
    bufp->fullCData(oldp+4308,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[12]),2);
    bufp->fullCData(oldp+4309,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[13]),2);
    bufp->fullCData(oldp+4310,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[14]),2);
    bufp->fullCData(oldp+4311,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_ack_read_q[15]),2);
    bufp->fullBit(oldp+4312,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_stb));
    bufp->fullBit(oldp+4313,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_aux));
    bufp->fullBit(oldp+4314,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_we));
    bufp->fullSData(oldp+4315,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_col),10);
    bufp->fullWData(oldp+4316,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_data),512);
    bufp->fullBit(oldp+4332,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_odt));
    bufp->fullBit(oldp+4333,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dqs));
    bufp->fullBit(oldp+4334,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_calib_dq));
    bufp->fullBit(oldp+4335,(vlSelf->main__DOT__ddr3_controller_inst__DOT__prev_write_level_feedback));
    bufp->fullWData(oldp+4336,(vlSelf->main__DOT__ddr3_controller_inst__DOT__read_data_store),512);
    bufp->fullWData(oldp+4352,(vlSelf->main__DOT__ddr3_controller_inst__DOT__write_pattern),128);
    bufp->fullCData(oldp+4356,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[0]),7);
    bufp->fullCData(oldp+4357,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[1]),7);
    bufp->fullCData(oldp+4358,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[2]),7);
    bufp->fullCData(oldp+4359,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[3]),7);
    bufp->fullCData(oldp+4360,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[4]),7);
    bufp->fullCData(oldp+4361,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[5]),7);
    bufp->fullCData(oldp+4362,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[6]),7);
    bufp->fullCData(oldp+4363,(vlSelf->main__DOT__ddr3_controller_inst__DOT__data_start_index[7]),7);
    bufp->fullCData(oldp+4364,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[0]),5);
    bufp->fullCData(oldp+4365,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[1]),5);
    bufp->fullCData(oldp+4366,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[2]),5);
    bufp->fullCData(oldp+4367,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[3]),5);
    bufp->fullCData(oldp+4368,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[4]),5);
    bufp->fullCData(oldp+4369,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[5]),5);
    bufp->fullCData(oldp+4370,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[6]),5);
    bufp->fullCData(oldp+4371,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_data_cntvaluein[7]),5);
    bufp->fullCData(oldp+4372,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[0]),5);
    bufp->fullCData(oldp+4373,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[1]),5);
    bufp->fullCData(oldp+4374,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[2]),5);
    bufp->fullCData(oldp+4375,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[3]),5);
    bufp->fullCData(oldp+4376,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[4]),5);
    bufp->fullCData(oldp+4377,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[5]),5);
    bufp->fullCData(oldp+4378,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[6]),5);
    bufp->fullCData(oldp+4379,(vlSelf->main__DOT__ddr3_controller_inst__DOT__odelay_dqs_cntvaluein[7]),5);
    bufp->fullCData(oldp+4380,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[0]),5);
    bufp->fullCData(oldp+4381,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[1]),5);
    bufp->fullCData(oldp+4382,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[2]),5);
    bufp->fullCData(oldp+4383,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[3]),5);
    bufp->fullCData(oldp+4384,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[4]),5);
    bufp->fullCData(oldp+4385,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[5]),5);
    bufp->fullCData(oldp+4386,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[6]),5);
    bufp->fullCData(oldp+4387,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein[7]),5);
    bufp->fullCData(oldp+4388,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_data_cntvaluein_prev),5);
    bufp->fullCData(oldp+4389,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[0]),5);
    bufp->fullCData(oldp+4390,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[1]),5);
    bufp->fullCData(oldp+4391,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[2]),5);
    bufp->fullCData(oldp+4392,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[3]),5);
    bufp->fullCData(oldp+4393,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[4]),5);
    bufp->fullCData(oldp+4394,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[5]),5);
    bufp->fullCData(oldp+4395,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[6]),5);
    bufp->fullCData(oldp+4396,(vlSelf->main__DOT__ddr3_controller_inst__DOT__idelay_dqs_cntvaluein[7]),5);
    bufp->fullBit(oldp+4397,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_stb));
    bufp->fullBit(oldp+4398,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_update));
    bufp->fullBit(oldp+4399,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_we));
    bufp->fullIData(oldp+4400,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_addr),32);
    bufp->fullIData(oldp+4401,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_data),32);
    bufp->fullCData(oldp+4402,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_sel),4);
    bufp->fullCData(oldp+4403,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_data_cntvaluein),5);
    bufp->fullCData(oldp+4404,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_dqs_cntvaluein),5);
    bufp->fullCData(oldp+4405,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_data_cntvaluein),5);
    bufp->fullCData(oldp+4406,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_dqs_cntvaluein),5);
    bufp->fullCData(oldp+4407,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_data_ld),8);
    bufp->fullCData(oldp+4408,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_odelay_dqs_ld),8);
    bufp->fullCData(oldp+4409,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_data_ld),8);
    bufp->fullCData(oldp+4410,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_phy_idelay_dqs_ld),8);
    bufp->fullCData(oldp+4411,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_write_lane),3);
    bufp->fullIData(oldp+4412,(vlSelf->main__DOT__ddr3_controller_inst__DOT__ns_to_cycles__Vstatic__result),32);
    bufp->fullSData(oldp+4413,(((IData)(vlSelf->main__DOT__wb32_ddr3_phy_stall) 
                                << 0xbU)),12);
    bufp->fullBit(oldp+4414,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__0__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n));
    bufp->fullBit(oldp+4415,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__1__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n));
    bufp->fullBit(oldp+4416,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__2__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n));
    bufp->fullBit(oldp+4417,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__DRIVE_DDR_IO__BRA__3__KET____DOT__u_dat_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n));
    bufp->fullBit(oldp+4418,(vlSelf->main__DOT__u_sdcard__DOT__u_sdfrontend__DOT__GEN_IODDR_IO__DOT__u_cmd_ddr__DOT__GEN_BIDIRECTIONAL__DOT__r_n));
    bufp->fullBit(oldp+4419,((1U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc))));
    bufp->fullBit(oldp+4420,((1U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb))));
    bufp->fullBit(oldp+4421,((1U & (IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_swe))));
    bufp->fullIData(oldp+4422,((0x3fffffU & vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[0U])),22);
    __Vtemp_hf82de6ac__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0U];
    __Vtemp_hf82de6ac__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[1U];
    __Vtemp_hf82de6ac__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[2U];
    __Vtemp_hf82de6ac__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[3U];
    __Vtemp_hf82de6ac__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[4U];
    __Vtemp_hf82de6ac__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[5U];
    __Vtemp_hf82de6ac__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[6U];
    __Vtemp_hf82de6ac__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[7U];
    __Vtemp_hf82de6ac__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[8U];
    __Vtemp_hf82de6ac__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[9U];
    __Vtemp_hf82de6ac__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xaU];
    __Vtemp_hf82de6ac__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xbU];
    __Vtemp_hf82de6ac__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xcU];
    __Vtemp_hf82de6ac__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xdU];
    __Vtemp_hf82de6ac__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xeU];
    __Vtemp_hf82de6ac__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0xfU];
    bufp->fullWData(oldp+4423,(__Vtemp_hf82de6ac__0),512);
    bufp->fullQData(oldp+4439,((((QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[1U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[0U])))),64);
    bufp->fullBit(oldp+4441,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err));
    bufp->fullBit(oldp+4442,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc) 
                                    >> 1U))));
    bufp->fullBit(oldp+4443,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb) 
                                    >> 1U))));
    bufp->fullBit(oldp+4444,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_swe) 
                                    >> 1U))));
    bufp->fullIData(oldp+4445,((0x3fffffU & ((vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[1U] 
                                              << 0xaU) 
                                             | (vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[0U] 
                                                >> 0x16U)))),22);
    __Vtemp_hf74e670c__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x10U];
    __Vtemp_hf74e670c__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x11U];
    __Vtemp_hf74e670c__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x12U];
    __Vtemp_hf74e670c__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x13U];
    __Vtemp_hf74e670c__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x14U];
    __Vtemp_hf74e670c__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x15U];
    __Vtemp_hf74e670c__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x16U];
    __Vtemp_hf74e670c__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x17U];
    __Vtemp_hf74e670c__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x18U];
    __Vtemp_hf74e670c__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x19U];
    __Vtemp_hf74e670c__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x1aU];
    __Vtemp_hf74e670c__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x1bU];
    __Vtemp_hf74e670c__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x1cU];
    __Vtemp_hf74e670c__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x1dU];
    __Vtemp_hf74e670c__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x1eU];
    __Vtemp_hf74e670c__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x1fU];
    bufp->fullWData(oldp+4446,(__Vtemp_hf74e670c__0),512);
    bufp->fullQData(oldp+4462,((((QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[3U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[2U])))),64);
    bufp->fullBit(oldp+4464,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc) 
                                    >> 2U))));
    bufp->fullBit(oldp+4465,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb) 
                                    >> 2U))));
    bufp->fullBit(oldp+4466,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_swe) 
                                    >> 2U))));
    bufp->fullIData(oldp+4467,((0x3fffffU & ((vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[2U] 
                                              << 0x14U) 
                                             | (vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[1U] 
                                                >> 0xcU)))),22);
    __Vtemp_h21e563ec__0[0U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x20U];
    __Vtemp_h21e563ec__0[1U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x21U];
    __Vtemp_h21e563ec__0[2U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x22U];
    __Vtemp_h21e563ec__0[3U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x23U];
    __Vtemp_h21e563ec__0[4U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x24U];
    __Vtemp_h21e563ec__0[5U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x25U];
    __Vtemp_h21e563ec__0[6U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x26U];
    __Vtemp_h21e563ec__0[7U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x27U];
    __Vtemp_h21e563ec__0[8U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x28U];
    __Vtemp_h21e563ec__0[9U] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x29U];
    __Vtemp_h21e563ec__0[0xaU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x2aU];
    __Vtemp_h21e563ec__0[0xbU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x2bU];
    __Vtemp_h21e563ec__0[0xcU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x2cU];
    __Vtemp_h21e563ec__0[0xdU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x2dU];
    __Vtemp_h21e563ec__0[0xeU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x2eU];
    __Vtemp_h21e563ec__0[0xfU] = vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata[0x2fU];
    bufp->fullWData(oldp+4468,(__Vtemp_h21e563ec__0),512);
    bufp->fullQData(oldp+4484,((((QData)((IData)(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[5U])) 
                                 << 0x20U) | (QData)((IData)(
                                                             vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel[4U])))),64);
    bufp->fullBit(oldp+4486,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_cyc));
    bufp->fullBit(oldp+4487,(vlSelf->main__DOT__wb32_xbar__DOT__DOUBLE_BUFFERRED_STALL__DOT__r_merr));
    bufp->fullBit(oldp+4488,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 9U))));
    bufp->fullBit(oldp+4489,((IData)((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                       >> 9U) & (0U 
                                                 == 
                                                 (0x700U 
                                                  & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))))));
    bufp->fullBit(oldp+4490,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 9U))));
    bufp->fullIData(oldp+4491,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[9U]),32);
    bufp->fullCData(oldp+4492,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x24U)))),4);
    bufp->fullBit(oldp+4493,((IData)((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                       >> 9U) & (0x100U 
                                                 == 
                                                 (0x700U 
                                                  & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))))));
    bufp->fullBit(oldp+4494,(vlSelf->main__DOT__wb32_sirefclk_stb));
    bufp->fullBit(oldp+4495,(vlSelf->main__DOT__wb32_spio_stb));
    bufp->fullBit(oldp+4496,((IData)((((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                       >> 9U) & (0x400U 
                                                 == 
                                                 (0x700U 
                                                  & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U]))))));
    bufp->fullBit(oldp+4497,((1U & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc))));
    bufp->fullBit(oldp+4498,((1U & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb))));
    bufp->fullBit(oldp+4499,((1U & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe))));
    bufp->fullCData(oldp+4500,((0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U])),8);
    bufp->fullIData(oldp+4501,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[0U]),32);
    bufp->fullCData(oldp+4502,((0xfU & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel))),4);
    bufp->fullBit(oldp+4503,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 1U))));
    bufp->fullBit(oldp+4504,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 1U))));
    bufp->fullBit(oldp+4505,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 1U))));
    bufp->fullCData(oldp+4506,((0xffU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                         >> 8U))),8);
    bufp->fullIData(oldp+4507,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[1U]),32);
    bufp->fullCData(oldp+4508,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 4U)))),4);
    bufp->fullBit(oldp+4509,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 2U))));
    bufp->fullBit(oldp+4510,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 2U))));
    bufp->fullBit(oldp+4511,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 2U))));
    bufp->fullCData(oldp+4512,((0xffU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                         >> 0x10U))),8);
    bufp->fullIData(oldp+4513,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[2U]),32);
    bufp->fullCData(oldp+4514,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 8U)))),4);
    bufp->fullBit(oldp+4515,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 3U))));
    bufp->fullBit(oldp+4516,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 3U))));
    bufp->fullBit(oldp+4517,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 3U))));
    bufp->fullCData(oldp+4518,((vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                >> 0x18U)),8);
    bufp->fullIData(oldp+4519,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[3U]),32);
    bufp->fullCData(oldp+4520,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0xcU)))),4);
    bufp->fullBit(oldp+4521,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 4U))));
    bufp->fullBit(oldp+4522,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 4U))));
    bufp->fullBit(oldp+4523,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 4U))));
    bufp->fullCData(oldp+4524,((0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])),8);
    bufp->fullIData(oldp+4525,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[4U]),32);
    bufp->fullCData(oldp+4526,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x10U)))),4);
    bufp->fullBit(oldp+4527,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 5U))));
    bufp->fullBit(oldp+4528,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 5U))));
    bufp->fullBit(oldp+4529,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 5U))));
    bufp->fullCData(oldp+4530,((0xffU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                         >> 8U))),8);
    bufp->fullIData(oldp+4531,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[5U]),32);
    bufp->fullCData(oldp+4532,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x14U)))),4);
    bufp->fullBit(oldp+4533,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 6U))));
    bufp->fullBit(oldp+4534,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 6U))));
    bufp->fullBit(oldp+4535,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 6U))));
    bufp->fullCData(oldp+4536,((0xffU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                         >> 0x10U))),8);
    bufp->fullIData(oldp+4537,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[6U]),32);
    bufp->fullCData(oldp+4538,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x18U)))),4);
    bufp->fullBit(oldp+4539,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 7U))));
    bufp->fullBit(oldp+4540,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 7U))));
    bufp->fullBit(oldp+4541,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 7U))));
    bufp->fullCData(oldp+4542,((vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                >> 0x18U)),8);
    bufp->fullIData(oldp+4543,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[7U]),32);
    bufp->fullCData(oldp+4544,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x1cU)))),4);
    bufp->fullBit(oldp+4545,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 8U))));
    bufp->fullBit(oldp+4546,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 8U))));
    bufp->fullBit(oldp+4547,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 8U))));
    bufp->fullCData(oldp+4548,((0xffU & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U])),8);
    bufp->fullIData(oldp+4549,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[8U]),32);
    bufp->fullCData(oldp+4550,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x20U)))),4);
    bufp->fullBit(oldp+4551,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 9U))));
    bufp->fullCData(oldp+4552,((0xffU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U] 
                                         >> 8U))),8);
    bufp->fullBit(oldp+4553,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 0xaU))));
    bufp->fullBit(oldp+4554,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 0xaU))));
    bufp->fullBit(oldp+4555,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 0xaU))));
    bufp->fullCData(oldp+4556,((0xffU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U] 
                                         >> 0x10U))),8);
    bufp->fullIData(oldp+4557,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[0xaU]),32);
    bufp->fullCData(oldp+4558,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x28U)))),4);
    bufp->fullBit(oldp+4559,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                    >> 0xbU))));
    bufp->fullBit(oldp+4560,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    >> 0xbU))));
    bufp->fullBit(oldp+4561,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 0xbU))));
    bufp->fullCData(oldp+4562,((vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U] 
                                >> 0x18U)),8);
    bufp->fullIData(oldp+4563,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata[0xbU]),32);
    bufp->fullCData(oldp+4564,((0xfU & (IData)((vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel 
                                                >> 0x2cU)))),4);
    bufp->fullSData(oldp+4565,((0x3fffU & ((vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[1U] 
                                            << 0xaU) 
                                           | (vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[0U] 
                                              >> 0x16U)))),14);
    bufp->fullCData(oldp+4566,((3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                      >> 8U))),2);
    bufp->fullIData(oldp+4567,((0x1fffffU & ((vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[2U] 
                                              << 0x14U) 
                                             | (vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[1U] 
                                                >> 0xcU)))),21);
    bufp->fullIData(oldp+4568,((0x7fU & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U] 
                                         >> 0x18U))),32);
    bufp->fullIData(oldp+4569,((0x1fffffU & ((IData)(5U) 
                                             + ((vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[2U] 
                                                 << 0x14U) 
                                                | (vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[1U] 
                                                   >> 0xcU))))),21);
    bufp->fullBit(oldp+4570,((1U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U])));
    bufp->fullBit(oldp+4571,((1U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                    & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)))));
    bufp->fullBit(oldp+4572,(vlSelf->main__DOT__emmcscopei__DOT__read_from_data));
    bufp->fullBit(oldp+4573,(vlSelf->main__DOT__emmcscopei__DOT__write_to_control));
    bufp->fullCData(oldp+4574,((3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                      >> 0x18U))),2);
    bufp->fullBit(oldp+4575,(vlSelf->main__DOT__i2ci__DOT__next_valid));
    bufp->fullCData(oldp+4576,(vlSelf->main__DOT__i2ci__DOT__next_insn),8);
    bufp->fullBit(oldp+4577,((1U & (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                     >> 3U) & (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                                  >> 3U))))));
    bufp->fullBit(oldp+4578,(vlSelf->main__DOT__i2ci__DOT__bus_write));
    bufp->fullBit(oldp+4579,(vlSelf->main__DOT__i2ci__DOT__bus_override));
    bufp->fullBit(oldp+4580,(vlSelf->main__DOT__i2ci__DOT__bus_manual));
    bufp->fullBit(oldp+4581,(vlSelf->main__DOT__i2ci__DOT__bus_jump));
    bufp->fullBit(oldp+4582,((1U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                    >> 8U))));
    bufp->fullBit(oldp+4583,((1U & (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                     & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
                                    >> 1U))));
    bufp->fullBit(oldp+4584,(vlSelf->main__DOT__i2cscopei__DOT__read_from_data));
    bufp->fullBit(oldp+4585,(vlSelf->main__DOT__i2cscopei__DOT__write_to_control));
    bufp->fullBit(oldp+4586,((1U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[0U] 
                                    >> 0x10U))));
    bufp->fullBit(oldp+4587,((1U & (((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb) 
                                     & (IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe)) 
                                    >> 2U))));
    bufp->fullBit(oldp+4588,(vlSelf->main__DOT__sdioscopei__DOT__read_from_data));
    bufp->fullBit(oldp+4589,(vlSelf->main__DOT__sdioscopei__DOT__write_to_control));
    bufp->fullCData(oldp+4590,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__next_btn),5);
    bufp->fullBit(oldp+4591,(vlSelf->main__DOT__spioi__DOT__GEN_BUTTON__DOT__next_int));
    bufp->fullCData(oldp+4592,((7U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                      >> 0x10U))),3);
    bufp->fullBit(oldp+4593,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb));
    bufp->fullBit(oldp+4594,(vlSelf->main__DOT__u_emmc__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb));
    bufp->fullCData(oldp+4595,((7U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                      >> 0x18U))),3);
    bufp->fullBit(oldp+4596,(vlSelf->main__DOT__u_fan__DOT____Vcellinp__u_i2ccpu__i_wb_stb));
    bufp->fullCData(oldp+4597,((3U & (vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U] 
                                      >> 0x18U))),2);
    bufp->fullBit(oldp+4598,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_valid));
    bufp->fullCData(oldp+4599,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__next_insn),8);
    bufp->fullBit(oldp+4600,(((IData)(vlSelf->main__DOT__u_fan__DOT____Vcellinp__u_i2ccpu__i_wb_stb) 
                              & (~ ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe) 
                                    >> 7U)))));
    bufp->fullBit(oldp+4601,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_write));
    bufp->fullBit(oldp+4602,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_override));
    bufp->fullBit(oldp+4603,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_manual));
    bufp->fullBit(oldp+4604,(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__bus_jump));
    bufp->fullCData(oldp+4605,((3U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[1U])),2);
    bufp->fullIData(oldp+4606,(vlSelf->main__DOT__u_i2cdma__DOT__next_baseaddr),32);
    bufp->fullIData(oldp+4607,(vlSelf->main__DOT__u_i2cdma__DOT__next_memlen),32);
    bufp->fullCData(oldp+4608,((7U & vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr[2U])),3);
    bufp->fullBit(oldp+4609,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_cmd_stb));
    bufp->fullBit(oldp+4610,(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_control__DOT__wb_phy_stb));
    bufp->fullCData(oldp+4611,((0xfU & vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr[0U])),4);
    bufp->fullCData(oldp+4612,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__i_subaddr),4);
    bufp->fullIData(oldp+4613,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__DOWNSIZE__DOT__subaddr_fn__Vstatic__fm),32);
    bufp->fullSData(oldp+4614,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc),12);
    bufp->fullSData(oldp+4615,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sstb),12);
    bufp->fullSData(oldp+4616,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_swe),12);
    bufp->fullWData(oldp+4617,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_saddr),96);
    bufp->fullWData(oldp+4620,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_sdata),384);
    bufp->fullQData(oldp+4632,(vlSelf->main__DOT____Vcellout__wb32_xbar__o_ssel),48);
    bufp->fullSData(oldp+4634,(vlSelf->main__DOT__wb32_xbar__DOT__request[0]),13);
    bufp->fullSData(oldp+4635,(vlSelf->main__DOT__wb32_xbar__DOT__sgrant),12);
    bufp->fullCData(oldp+4636,(vlSelf->main__DOT__wb32_xbar__DOT__mindex[0]),4);
    bufp->fullBit(oldp+4637,(vlSelf->main__DOT__wb32_xbar__DOT__m_stb));
    bufp->fullBit(oldp+4638,((1U & (IData)((vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data 
                                            >> 0x24U)))));
    bufp->fullCData(oldp+4639,(vlSelf->main__DOT__wb32_xbar__DOT__m_addr[0]),8);
    bufp->fullIData(oldp+4640,(vlSelf->main__DOT__wb32_xbar__DOT__m_data[0]),32);
    bufp->fullCData(oldp+4641,(vlSelf->main__DOT__wb32_xbar__DOT__m_sel[0]),4);
    bufp->fullBit(oldp+4642,(vlSelf->main__DOT__wb32_xbar__DOT__dcd_stb));
    bufp->fullSData(oldp+4643,(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant),13);
    bufp->fullBit(oldp+4644,(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__stay_on_channel));
    bufp->fullBit(oldp+4645,(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available));
    bufp->fullCData(oldp+4646,(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex),4);
    bufp->fullBit(oldp+4647,((1U & (IData)((vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                            >> 0x2cU)))));
    bufp->fullCData(oldp+4648,((0xffU & (IData)((vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                                 >> 0x24U)))),8);
    bufp->fullIData(oldp+4649,((IData)((vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                        >> 4U))),32);
    bufp->fullCData(oldp+4650,((0xfU & (IData)(vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data))),4);
    bufp->fullQData(oldp+4651,((((QData)((IData)((1U 
                                                  & (IData)(
                                                            (vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data 
                                                             >> 0x2cU))))) 
                                 << 0x24U) | (0xfffffffffULL 
                                              & vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data))),37);
    bufp->fullQData(oldp+4653,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__adcd__o_data),37);
    bufp->fullSData(oldp+4655,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__adcd__DOT__prerequest),12);
    bufp->fullQData(oldp+4656,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellout__DECODE_REQUEST__BRA__0__KET____DOT__iskid__o_data),45);
    bufp->fullCData(oldp+4658,(vlSelf->main__DOT__wbu_xbar__DOT__mindex[0]),2);
    bufp->fullCData(oldp+4659,(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant),3);
    bufp->fullCData(oldp+4660,(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex),2);
    bufp->fullCData(oldp+4661,(vlSelf->main__DOT____Vcellinp__wbwide_xbar__i_mcyc),4);
    bufp->fullCData(oldp+4662,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_scyc),3);
    bufp->fullCData(oldp+4663,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sstb),3);
    bufp->fullCData(oldp+4664,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_swe),3);
    bufp->fullWData(oldp+4665,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_saddr),66);
    bufp->fullWData(oldp+4668,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_sdata),1536);
    bufp->fullWData(oldp+4716,(vlSelf->main__DOT____Vcellout__wbwide_xbar__o_ssel),192);
    bufp->fullCData(oldp+4722,(vlSelf->main__DOT__u_wbdown__DOT__DOWNSIZE__DOT__r_err),3);
    bufp->fullCData(oldp+4723,(vlSelf->main__DOT__wbwide_xbar__DOT__sgrant),3);
    bufp->fullCData(oldp+4724,(vlSelf->main__DOT__wbwide_xbar__DOT__mindex[0]),2);
    bufp->fullCData(oldp+4725,(vlSelf->main__DOT__wbwide_xbar__DOT__mindex[1]),2);
    bufp->fullCData(oldp+4726,(vlSelf->main__DOT__wbwide_xbar__DOT__mindex[2]),2);
    bufp->fullCData(oldp+4727,(vlSelf->main__DOT__wbwide_xbar__DOT__mindex[3]),2);
    bufp->fullCData(oldp+4728,(vlSelf->main__DOT__wbwide_xbar__DOT__sindex[0]),2);
    bufp->fullCData(oldp+4729,(vlSelf->main__DOT__wbwide_xbar__DOT__sindex[1]),2);
    bufp->fullCData(oldp+4730,(vlSelf->main__DOT__wbwide_xbar__DOT__sindex[2]),2);
    bufp->fullCData(oldp+4731,(vlSelf->main__DOT__wbwide_xbar__DOT__sindex[3]),2);
    bufp->fullCData(oldp+4732,(vlSelf->main__DOT__wbwide_xbar__DOT__m_we),4);
    bufp->fullIData(oldp+4733,(vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[0]),22);
    bufp->fullIData(oldp+4734,(vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[1]),22);
    bufp->fullIData(oldp+4735,(vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[2]),22);
    bufp->fullIData(oldp+4736,(vlSelf->main__DOT__wbwide_xbar__DOT__m_addr[3]),22);
    bufp->fullWData(oldp+4737,(vlSelf->main__DOT__wbwide_xbar__DOT__m_data[0]),512);
    bufp->fullWData(oldp+4753,(vlSelf->main__DOT__wbwide_xbar__DOT__m_data[1]),512);
    bufp->fullWData(oldp+4769,(vlSelf->main__DOT__wbwide_xbar__DOT__m_data[2]),512);
    bufp->fullWData(oldp+4785,(vlSelf->main__DOT__wbwide_xbar__DOT__m_data[3]),512);
    bufp->fullQData(oldp+4801,(vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[0]),64);
    bufp->fullQData(oldp+4803,(vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[1]),64);
    bufp->fullQData(oldp+4805,(vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[2]),64);
    bufp->fullQData(oldp+4807,(vlSelf->main__DOT__wbwide_xbar__DOT__m_sel[3]),64);
    bufp->fullCData(oldp+4809,(vlSelf->main__DOT__wbwide_xbar__DOT__s_err),4);
    bufp->fullCData(oldp+4810,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant),4);
    bufp->fullBit(oldp+4811,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__requested_channel_is_available));
    bufp->fullCData(oldp+4812,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex),2);
    bufp->fullCData(oldp+4813,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant),4);
    bufp->fullBit(oldp+4814,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__requested_channel_is_available));
    bufp->fullCData(oldp+4815,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex),2);
    bufp->fullCData(oldp+4816,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant),4);
    bufp->fullBit(oldp+4817,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__requested_channel_is_available));
    bufp->fullCData(oldp+4818,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex),2);
    bufp->fullCData(oldp+4819,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_regrant),4);
    bufp->fullBit(oldp+4820,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__requested_channel_is_available));
    bufp->fullCData(oldp+4821,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_mindex),2);
    bufp->fullCData(oldp+4822,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant),4);
    bufp->fullCData(oldp+4823,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__0__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex),2);
    bufp->fullCData(oldp+4824,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant),4);
    bufp->fullCData(oldp+4825,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__1__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex),2);
    bufp->fullCData(oldp+4826,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__regrant),4);
    bufp->fullCData(oldp+4827,(vlSelf->main__DOT__wbwide_xbar__DOT__GEN_SINDEX__BRA__2__KET____DOT__SINDEX_MORE_THAN_ONE_MASTER__DOT__reindex),2);
    bufp->fullBit(oldp+4828,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage2_stall));
    bufp->fullBit(oldp+4829,(vlSelf->main__DOT__ddr3_controller_inst__DOT__stage1_stall));
    bufp->fullCData(oldp+4830,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_status_d),8);
    bufp->fullSData(oldp+4831,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[0]),14);
    bufp->fullSData(oldp+4832,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[1]),14);
    bufp->fullSData(oldp+4833,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[2]),14);
    bufp->fullSData(oldp+4834,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[3]),14);
    bufp->fullSData(oldp+4835,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[4]),14);
    bufp->fullSData(oldp+4836,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[5]),14);
    bufp->fullSData(oldp+4837,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[6]),14);
    bufp->fullSData(oldp+4838,(vlSelf->main__DOT__ddr3_controller_inst__DOT__bank_active_row_d[7]),14);
    bufp->fullCData(oldp+4839,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[0]),4);
    bufp->fullCData(oldp+4840,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[1]),4);
    bufp->fullCData(oldp+4841,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[2]),4);
    bufp->fullCData(oldp+4842,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[3]),4);
    bufp->fullCData(oldp+4843,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[4]),4);
    bufp->fullCData(oldp+4844,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[5]),4);
    bufp->fullCData(oldp+4845,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[6]),4);
    bufp->fullCData(oldp+4846,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_precharge_counter_d[7]),4);
    bufp->fullCData(oldp+4847,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[0]),4);
    bufp->fullCData(oldp+4848,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[1]),4);
    bufp->fullCData(oldp+4849,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[2]),4);
    bufp->fullCData(oldp+4850,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[3]),4);
    bufp->fullCData(oldp+4851,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[4]),4);
    bufp->fullCData(oldp+4852,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[5]),4);
    bufp->fullCData(oldp+4853,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[6]),4);
    bufp->fullCData(oldp+4854,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_activate_counter_d[7]),4);
    bufp->fullCData(oldp+4855,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[0]),4);
    bufp->fullCData(oldp+4856,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[1]),4);
    bufp->fullCData(oldp+4857,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[2]),4);
    bufp->fullCData(oldp+4858,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[3]),4);
    bufp->fullCData(oldp+4859,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[4]),4);
    bufp->fullCData(oldp+4860,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[5]),4);
    bufp->fullCData(oldp+4861,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[6]),4);
    bufp->fullCData(oldp+4862,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_write_counter_d[7]),4);
    bufp->fullCData(oldp+4863,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[0]),4);
    bufp->fullCData(oldp+4864,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[1]),4);
    bufp->fullCData(oldp+4865,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[2]),4);
    bufp->fullCData(oldp+4866,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[3]),4);
    bufp->fullCData(oldp+4867,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[4]),4);
    bufp->fullCData(oldp+4868,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[5]),4);
    bufp->fullCData(oldp+4869,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[6]),4);
    bufp->fullCData(oldp+4870,(vlSelf->main__DOT__ddr3_controller_inst__DOT__delay_before_read_counter_d[7]),4);
    bufp->fullIData(oldp+4871,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[0]),24);
    bufp->fullIData(oldp+4872,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[1]),24);
    bufp->fullIData(oldp+4873,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[2]),24);
    bufp->fullIData(oldp+4874,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_d[3]),24);
    bufp->fullBit(oldp+4875,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_odt));
    bufp->fullBit(oldp+4876,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_ck_en));
    bufp->fullBit(oldp+4877,(vlSelf->main__DOT__ddr3_controller_inst__DOT__cmd_reset_n));
    bufp->fullBit(oldp+4878,(vlSelf->main__DOT__ddr3_controller_inst__DOT__o_wb_stall_d));
    bufp->fullBit(oldp+4879,(vlSelf->main__DOT__ddr3_controller_inst__DOT__precharge_slot_busy));
    bufp->fullBit(oldp+4880,(vlSelf->main__DOT__ddr3_controller_inst__DOT__activate_slot_busy));
    bufp->fullBit(oldp+4881,(vlSelf->main__DOT__wb32_xbar__DOT__m_stall));
    bufp->fullSData(oldp+4882,(vlSelf->main__DOT__wb32_xbar__DOT__s_stall),16);
    bufp->fullBit(oldp+4883,(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall));
    bufp->fullBit(oldp+4884,(vlSelf->main__DOT__wb32_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall));
    bufp->fullBit(oldp+4885,((1U & (~ (IData)(vlSelf->main__DOT__wb32_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall)))));
    bufp->fullCData(oldp+4886,(vlSelf->main__DOT__wbwide_xbar__DOT__m_stall),4);
    bufp->fullCData(oldp+4887,(vlSelf->main__DOT__wbwide_xbar__DOT__s_stall),4);
    bufp->fullCData(oldp+4888,(vlSelf->main__DOT__wbwide_xbar__DOT__s_ack),4);
    bufp->fullBit(oldp+4889,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall));
    bufp->fullBit(oldp+4890,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__0__KET____DOT__adcd__i_stall));
    bufp->fullBit(oldp+4891,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__0__KET____DOT__skd_stall)))));
    bufp->fullBit(oldp+4892,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stall));
    bufp->fullBit(oldp+4893,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__1__KET____DOT__adcd__i_stall));
    bufp->fullBit(oldp+4894,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__1__KET____DOT__skd_stall)))));
    bufp->fullBit(oldp+4895,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stall));
    bufp->fullBit(oldp+4896,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__2__KET____DOT__adcd__i_stall));
    bufp->fullBit(oldp+4897,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__2__KET____DOT__skd_stall)))));
    bufp->fullBit(oldp+4898,(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stall));
    bufp->fullBit(oldp+4899,(vlSelf->main__DOT__wbwide_xbar__DOT____Vcellinp__DECODE_REQUEST__BRA__3__KET____DOT__adcd__i_stall));
    bufp->fullBit(oldp+4900,((1U & (~ (IData)(vlSelf->main__DOT__wbwide_xbar__DOT__DECODE_REQUEST__BRA__3__KET____DOT__skd_stall)))));
    bufp->fullBit(oldp+4901,(vlSelf->i_clk));
    bufp->fullBit(oldp+4902,(vlSelf->i_reset));
    bufp->fullWData(oldp+4903,(vlSelf->i_ddr3_controller_iserdes_data),512);
    bufp->fullQData(oldp+4919,(vlSelf->i_ddr3_controller_iserdes_dqs),64);
    bufp->fullQData(oldp+4921,(vlSelf->i_ddr3_controller_iserdes_bitslip_reference),64);
    bufp->fullBit(oldp+4923,(vlSelf->i_ddr3_controller_idelayctrl_rdy));
    bufp->fullWData(oldp+4924,(vlSelf->o_ddr3_controller_cmd),96);
    bufp->fullBit(oldp+4927,(vlSelf->o_ddr3_controller_dqs_tri_control));
    bufp->fullBit(oldp+4928,(vlSelf->o_ddr3_controller_dq_tri_control));
    bufp->fullBit(oldp+4929,(vlSelf->o_ddr3_controller_toggle_dqs));
    bufp->fullWData(oldp+4930,(vlSelf->o_ddr3_controller_data),512);
    bufp->fullQData(oldp+4946,(vlSelf->o_ddr3_controller_dm),64);
    bufp->fullCData(oldp+4948,(vlSelf->o_ddr3_controller_odelay_data_cntvaluein),5);
    bufp->fullCData(oldp+4949,(vlSelf->o_ddr3_controller_odelay_dqs_cntvaluein),5);
    bufp->fullCData(oldp+4950,(vlSelf->o_ddr3_controller_idelay_data_cntvaluein),5);
    bufp->fullCData(oldp+4951,(vlSelf->o_ddr3_controller_idelay_dqs_cntvaluein),5);
    bufp->fullCData(oldp+4952,(vlSelf->o_ddr3_controller_odelay_data_ld),8);
    bufp->fullCData(oldp+4953,(vlSelf->o_ddr3_controller_odelay_dqs_ld),8);
    bufp->fullCData(oldp+4954,(vlSelf->o_ddr3_controller_idelay_data_ld),8);
    bufp->fullCData(oldp+4955,(vlSelf->o_ddr3_controller_idelay_dqs_ld),8);
    bufp->fullCData(oldp+4956,(vlSelf->o_ddr3_controller_bitslip),8);
    bufp->fullCData(oldp+4957,(vlSelf->o_sirefclk_word),8);
    bufp->fullBit(oldp+4958,(vlSelf->o_sirefclk_ce));
    bufp->fullBit(oldp+4959,(vlSelf->i_fan_sda));
    bufp->fullBit(oldp+4960,(vlSelf->i_fan_scl));
    bufp->fullBit(oldp+4961,(vlSelf->o_fan_sda));
    bufp->fullBit(oldp+4962,(vlSelf->o_fan_scl));
    bufp->fullBit(oldp+4963,(vlSelf->o_fpga_pwm));
    bufp->fullBit(oldp+4964,(vlSelf->o_sys_pwm));
    bufp->fullBit(oldp+4965,(vlSelf->i_fan_tach));
    bufp->fullBit(oldp+4966,(vlSelf->o_emmc_clk));
    bufp->fullBit(oldp+4967,(vlSelf->i_emmc_ds));
    bufp->fullBit(oldp+4968,(vlSelf->io_emmc_cmd_tristate));
    bufp->fullBit(oldp+4969,(vlSelf->o_emmc_cmd));
    bufp->fullBit(oldp+4970,(vlSelf->i_emmc_cmd));
    bufp->fullCData(oldp+4971,(vlSelf->io_emmc_dat_tristate),8);
    bufp->fullCData(oldp+4972,(vlSelf->o_emmc_dat),8);
    bufp->fullCData(oldp+4973,(vlSelf->i_emmc_dat),8);
    bufp->fullBit(oldp+4974,(vlSelf->i_emmc_detect));
    bufp->fullBit(oldp+4975,(vlSelf->i_i2c_sda));
    bufp->fullBit(oldp+4976,(vlSelf->i_i2c_scl));
    bufp->fullBit(oldp+4977,(vlSelf->o_i2c_sda));
    bufp->fullBit(oldp+4978,(vlSelf->o_i2c_scl));
    bufp->fullBit(oldp+4979,(vlSelf->o_sdcard_clk));
    bufp->fullBit(oldp+4980,(vlSelf->i_sdcard_ds));
    bufp->fullBit(oldp+4981,(vlSelf->io_sdcard_cmd_tristate));
    bufp->fullBit(oldp+4982,(vlSelf->o_sdcard_cmd));
    bufp->fullBit(oldp+4983,(vlSelf->i_sdcard_cmd));
    bufp->fullCData(oldp+4984,(vlSelf->io_sdcard_dat_tristate),4);
    bufp->fullCData(oldp+4985,(vlSelf->o_sdcard_dat),4);
    bufp->fullCData(oldp+4986,(vlSelf->i_sdcard_dat),4);
    bufp->fullBit(oldp+4987,(vlSelf->i_sdcard_detect));
    bufp->fullBit(oldp+4988,(vlSelf->cpu_sim_cyc));
    bufp->fullBit(oldp+4989,(vlSelf->cpu_sim_stb));
    bufp->fullBit(oldp+4990,(vlSelf->cpu_sim_we));
    bufp->fullCData(oldp+4991,(vlSelf->cpu_sim_addr),7);
    bufp->fullIData(oldp+4992,(vlSelf->cpu_sim_data),32);
    bufp->fullBit(oldp+4993,(vlSelf->cpu_sim_stall));
    bufp->fullBit(oldp+4994,(vlSelf->cpu_sim_ack));
    bufp->fullIData(oldp+4995,(vlSelf->cpu_sim_idata),32);
    bufp->fullBit(oldp+4996,(vlSelf->cpu_prof_stb));
    bufp->fullIData(oldp+4997,(vlSelf->cpu_prof_addr),28);
    bufp->fullIData(oldp+4998,(vlSelf->cpu_prof_ticks),32);
    bufp->fullBit(oldp+4999,(vlSelf->i_cpu_reset));
    bufp->fullBit(oldp+5000,(vlSelf->i_wbu_uart_rx));
    bufp->fullBit(oldp+5001,(vlSelf->o_wbu_uart_tx));
    bufp->fullBit(oldp+5002,(vlSelf->o_wbu_uart_cts_n));
    bufp->fullSData(oldp+5003,(vlSelf->i_gpio),16);
    bufp->fullCData(oldp+5004,(vlSelf->o_gpio),8);
    bufp->fullCData(oldp+5005,(vlSelf->i_sw),8);
    bufp->fullCData(oldp+5006,(vlSelf->i_btn),5);
    bufp->fullCData(oldp+5007,(vlSelf->o_led),8);
    bufp->fullBit(oldp+5008,(vlSelf->i_clk200));
    bufp->fullIData(oldp+5009,((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted) 
                                 << 0x1fU) | ((0x40000000U 
                                               & ((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__ovw_data) 
                                                  << 0x15U)) 
                                              | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_abort) 
                                                  << 0x1dU) 
                                                 | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__i2c_stretch) 
                                                     << 0x1cU) 
                                                    | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn) 
                                                        << 0x18U) 
                                                       | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait) 
                                                           << 0x17U) 
                                                          | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request) 
                                                              << 0x16U) 
                                                             | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted) 
                                                                 << 0x15U) 
                                                                | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err) 
                                                                    << 0x14U) 
                                                                   | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted) 
                                                                       << 0x13U) 
                                                                      | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
                                                                          << 0x12U) 
                                                                         | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid) 
                                                                             << 0x11U) 
                                                                            | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle) 
                                                                                << 0x10U) 
                                                                               | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl) 
                                                                                << 0xfU) 
                                                                                | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda) 
                                                                                << 0xeU) 
                                                                                | (((IData)(vlSelf->i_fan_scl) 
                                                                                << 0xdU) 
                                                                                | (((IData)(vlSelf->i_fan_sda) 
                                                                                << 0xcU) 
                                                                                | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn))))))))))))))))))),32);
    bufp->fullIData(oldp+5010,((((IData)(vlSelf->main__DOT__gpioi__DOT__r_gpio) 
                                 << 0x10U) | (IData)(vlSelf->o_gpio))),32);
    bufp->fullBit(oldp+5011,(((IData)(vlSelf->cpu_sim_cyc) 
                              | (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb))));
    bufp->fullBit(oldp+5012,(((~ (IData)(vlSelf->cpu_sim_cyc)) 
                              & (IData)(vlSelf->main__DOT__raw_cpu_dbg_ack))));
    bufp->fullBit(oldp+5013,(vlSelf->main__DOT____Vcellinp__ddr3_controller_inst__i_rst_n));
    bufp->fullSData(oldp+5014,(vlSelf->o_gpio),16);
    bufp->fullBit(oldp+5015,(vlSelf->main__DOT____Vcellinp__swic__i_reset));
    bufp->fullCData(oldp+5016,(((IData)(vlSelf->cpu_sim_cyc)
                                 ? 0xfU : (0xfU & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_ssel) 
                                                   >> 4U)))),4);
    bufp->fullIData(oldp+5017,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_pc),28);
    bufp->fullBit(oldp+5018,((((~ ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__dcd_F) 
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
                                     & (IData)(((0xeU 
                                                 == 
                                                 (0xeU 
                                                  & (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R))) 
                                                & ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__OP_REG_ADVANEC__DOT__r_op_R) 
                                                   != 
                                                   (0xfU 
                                                    | ((IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__SET_GIE__DOT__r_gie) 
                                                       << 4U))))))) 
                                 | (IData)(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__GEN_OP_STALL__DOT__r_pending_sreg_write)))));
    bufp->fullBit(oldp+5019,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim));
    bufp->fullIData(oldp+5020,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__instruction_decoder__DOT__o_sim_immv),23);
    bufp->fullBit(oldp+5021,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_valid));
    bufp->fullBit(oldp+5022,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim));
    bufp->fullIData(oldp+5023,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__op_sim_immv),23);
    bufp->fullBit(oldp+5024,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim));
    bufp->fullIData(oldp+5025,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_sim_immv),23);
    bufp->fullBit(oldp+5026,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__core__DOT__alu_ce));
    bufp->fullIData(oldp+5027,((((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_insn) 
                                 << 0x1cU) | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__manual) 
                                               << 0x18U) 
                                              | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_wait) 
                                                  << 0x17U) 
                                                 | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__soft_halt_request) 
                                                     << 0x16U) 
                                                    | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_aborted) 
                                                        << 0x15U) 
                                                       | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_err) 
                                                           << 0x14U) 
                                                          | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__r_halted) 
                                                              << 0x13U) 
                                                             | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn_valid) 
                                                                 << 0x12U) 
                                                                | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__half_valid) 
                                                                    << 0x11U) 
                                                                   | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__imm_cycle) 
                                                                       << 0x10U) 
                                                                      | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_scl) 
                                                                          << 0xfU) 
                                                                         | (((IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__GEN_MANUAL__DOT__o_sda) 
                                                                             << 0xeU) 
                                                                            | (((IData)(vlSelf->i_fan_scl) 
                                                                                << 0xdU) 
                                                                               | (((IData)(vlSelf->i_fan_sda) 
                                                                                << 0xcU) 
                                                                                | (IData)(vlSelf->main__DOT__u_fan__DOT__u_i2ccpu__DOT__insn)))))))))))))))),32);
    bufp->fullBit(oldp+5028,(((IData)(vlSelf->i_reset) 
                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                 & ((~ (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                        >> 0x18U)) 
                                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_data))))));
    bufp->fullCData(oldp+5029,((3U & (- (IData)((1U 
                                                 & ((IData)(vlSelf->i_reset) 
                                                    | (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                       >> 0x18U))))))),2);
    bufp->fullBit(oldp+5030,((1U & (IData)(vlSelf->i_sdcard_dat))));
    bufp->fullBit(oldp+5031,(((IData)(vlSelf->i_reset) 
                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                 & ((~ (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                        >> 0x19U)) 
                                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_data))))));
    bufp->fullCData(oldp+5032,((3U & (- (IData)((1U 
                                                 & ((IData)(vlSelf->i_reset) 
                                                    | (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                       >> 0x19U))))))),2);
    bufp->fullBit(oldp+5033,((1U & ((IData)(vlSelf->i_sdcard_dat) 
                                    >> 1U))));
    bufp->fullBit(oldp+5034,(((IData)(vlSelf->i_reset) 
                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                 & ((~ (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                        >> 0x1aU)) 
                                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_data))))));
    bufp->fullCData(oldp+5035,((3U & (- (IData)((1U 
                                                 & ((IData)(vlSelf->i_reset) 
                                                    | (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                       >> 0x1aU))))))),2);
    bufp->fullBit(oldp+5036,((1U & ((IData)(vlSelf->i_sdcard_dat) 
                                    >> 2U))));
    bufp->fullBit(oldp+5037,(((IData)(vlSelf->i_reset) 
                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_valid) 
                                 & ((~ (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                        >> 0x1bU)) 
                                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_data))))));
    bufp->fullCData(oldp+5038,((3U & (- (IData)((1U 
                                                 & ((IData)(vlSelf->i_reset) 
                                                    | (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_txframe__DOT__ck_data 
                                                       >> 0x1bU))))))),2);
    bufp->fullBit(oldp+5039,((1U & ((IData)(vlSelf->i_sdcard_dat) 
                                    >> 3U))));
    bufp->fullBit(oldp+5040,(((IData)(vlSelf->i_reset) 
                              | ((IData)(vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__active) 
                                 & ((~ (IData)((vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                                >> 0x2fU))) 
                                    | (IData)(vlSelf->main__DOT__u_sdcard__DOT__pp_cmd))))));
    bufp->fullCData(oldp+5041,((3U & (- (IData)(((IData)(vlSelf->i_reset) 
                                                 | (vlSelf->main__DOT__u_sdcard__DOT__u_sdio__DOT__u_sdcmd__DOT__tx_sreg 
                                                    >> 0x2fU)))))),2);
    bufp->fullSData(oldp+5042,(((0xfffff800U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
                                                & ((IData)(vlSelf->main__DOT__wb32_ddr3_phy_ack) 
                                                   << 0xbU))) 
                                | ((0xfffffc00U & ((IData)(vlSelf->main__DOT____Vcellout__wb32_xbar__o_scyc) 
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
                                                                 & (IData)(vlSelf->main__DOT__emmcscopei__DOT__br_wb_ack)))))))))))))),16);
    bufp->fullIData(oldp+5043,(vlSelf->main__DOT__wb32_xbar__DOT__iM),32);
    bufp->fullCData(oldp+5044,(vlSelf->main__DOT__wb32_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex),4);
    bufp->fullCData(oldp+5045,(((((IData)(vlSelf->cpu_sim_cyc) 
                                  | (IData)(vlSelf->main__DOT__swic__DOT__DELAY_THE_DEBUG_BUS__DOT__wbdelay__DOT__SKIDBUFFER__DOT__r_stb)) 
                                 << 1U) | (IData)(vlSelf->main__DOT__wbu_wbu_arbiter_stall))),2);
    bufp->fullCData(oldp+5046,(((((~ (IData)(vlSelf->cpu_sim_cyc)) 
                                  & (IData)(vlSelf->main__DOT__raw_cpu_dbg_ack)) 
                                 << 1U) | (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_ack))),2);
    bufp->fullCData(oldp+5047,(((0xfffffffeU & ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                                                & (((~ (IData)(vlSelf->cpu_sim_cyc)) 
                                                    & (IData)(vlSelf->main__DOT__raw_cpu_dbg_ack)) 
                                                   << 1U))) 
                                | ((IData)(vlSelf->main__DOT____Vcellout__wbu_xbar__o_scyc) 
                                   & (IData)(vlSelf->main__DOT__wbu_arbiter_upsz__DOT__UPSIZE__DOT__r_ack)))),4);
    bufp->fullIData(oldp+5048,(vlSelf->main__DOT__wbu_xbar__DOT__iM),32);
    bufp->fullCData(oldp+5049,(vlSelf->main__DOT__wbu_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex),2);
    bufp->fullIData(oldp+5050,(vlSelf->main__DOT__wbwide_xbar__DOT__iN),32);
    bufp->fullIData(oldp+5051,(vlSelf->main__DOT__wbwide_xbar__DOT__iM),32);
    bufp->fullCData(oldp+5052,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__0__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex),2);
    bufp->fullCData(oldp+5053,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__1__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex),2);
    bufp->fullCData(oldp+5054,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__2__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex),2);
    bufp->fullCData(oldp+5055,(vlSelf->main__DOT__wbwide_xbar__DOT__ARBITRATE_REQUESTS__BRA__3__KET____DOT__MINDEX_MULTIPLE_SLAVES__DOT__r_reindex),2);
    bufp->fullDouble(oldp+5056,(10.0));
    bufp->fullDouble(oldp+5058,(2.50000000000000000e+00));
    bufp->fullIData(oldp+5060,(0xeU),32);
    bufp->fullIData(oldp+5061,(0xaU),32);
    bufp->fullIData(oldp+5062,(3U),32);
    bufp->fullIData(oldp+5063,(8U),32);
    bufp->fullIData(oldp+5064,(1U),32);
    bufp->fullIData(oldp+5065,(4U),32);
    bufp->fullIData(oldp+5066,(0x18U),32);
    bufp->fullIData(oldp+5067,(0x4000000U),32);
    bufp->fullIData(oldp+5068,(0x16U),32);
    bufp->fullIData(oldp+5069,(0x10U),32);
    bufp->fullBit(oldp+5070,(1U));
    bufp->fullIData(oldp+5071,(0x64U),24);
    bufp->fullIData(oldp+5072,(7U),32);
    bufp->fullIData(oldp+5073,(0x13U),32);
    bufp->fullBit(oldp+5074,(0U));
    bufp->fullIData(oldp+5075,(2U),32);
    bufp->fullIData(oldp+5076,(0U),32);
    bufp->fullBit(oldp+5077,(1U));
    bufp->fullWData(oldp+5078,(Vmain__ConstPool__CONST_h93e1b771_0),512);
    bufp->fullQData(oldp+5094,(0xffffffffffffffffULL),64);
    bufp->fullCData(oldp+5096,(vlSelf->main__DOT__wb32_buildtime_addr),8);
    bufp->fullBit(oldp+5097,(vlSelf->main__DOT__wb32_buildtime_err));
    bufp->fullIData(oldp+5098,(0x82055U),32);
    bufp->fullCData(oldp+5099,(vlSelf->main__DOT__wb32_gpio_addr),8);
    bufp->fullBit(oldp+5100,(vlSelf->main__DOT__wb32_gpio_err));
    bufp->fullCData(oldp+5101,(vlSelf->main__DOT__wb32_sirefclk_addr),8);
    bufp->fullBit(oldp+5102,(vlSelf->main__DOT__wb32_sirefclk_err));
    bufp->fullCData(oldp+5103,(vlSelf->main__DOT__wb32_spio_addr),8);
    bufp->fullBit(oldp+5104,(vlSelf->main__DOT__wb32_spio_err));
    bufp->fullCData(oldp+5105,(vlSelf->main__DOT__wb32_version_addr),8);
    bufp->fullBit(oldp+5106,(vlSelf->main__DOT__wb32_version_err));
    bufp->fullIData(oldp+5107,(0x20230723U),32);
    bufp->fullCData(oldp+5108,(0xfU),4);
    bufp->fullCData(oldp+5109,(0x20U),8);
    bufp->fullIData(oldp+5110,(0x14U),32);
    bufp->fullIData(oldp+5111,(0x200U),32);
    bufp->fullCData(oldp+5112,(0U),8);
    bufp->fullBit(oldp+5113,(0U));
    bufp->fullIData(oldp+5114,(0x20U),32);
    bufp->fullCData(oldp+5115,(6U),4);
    bufp->fullCData(oldp+5116,(0U),2);
    bufp->fullCData(oldp+5117,(1U),2);
    bufp->fullCData(oldp+5118,(2U),2);
    bufp->fullCData(oldp+5119,(3U),2);
    bufp->fullIData(oldp+5120,(0x40U),32);
    bufp->fullIData(oldp+5121,(0x15U),32);
    bufp->fullCData(oldp+5122,(0U),4);
    bufp->fullCData(oldp+5123,(1U),4);
    bufp->fullCData(oldp+5124,(2U),4);
    bufp->fullCData(oldp+5125,(3U),4);
    bufp->fullCData(oldp+5126,(4U),4);
    bufp->fullCData(oldp+5127,(5U),4);
    bufp->fullCData(oldp+5128,(7U),4);
    bufp->fullCData(oldp+5129,(8U),4);
    bufp->fullIData(oldp+5130,(0x1bU),32);
    bufp->fullIData(oldp+5131,(0x1aU),32);
    bufp->fullIData(oldp+5132,(0x19U),32);
    bufp->fullIData(oldp+5133,(0x17U),32);
    bufp->fullIData(oldp+5134,(0x12U),32);
    bufp->fullIData(oldp+5135,(0x11U),32);
    bufp->fullIData(oldp+5136,(0xdU),32);
    bufp->fullIData(oldp+5137,(0x30d40U),32);
    bufp->fullIData(oldp+5138,(0x7a120U),32);
    bufp->fullDouble(oldp+5139,(1.37500000000000000e+01));
    bufp->fullIData(oldp+5141,(0x23U),32);
    bufp->fullDouble(oldp+5142,(350.0));
    bufp->fullIData(oldp+5144,(0x1e78U),32);
    bufp->fullDouble(oldp+5145,(360.0));
    bufp->fullDouble(oldp+5147,(15.0));
    bufp->fullIData(oldp+5149,(0xaU),19);
    bufp->fullDouble(oldp+5150,(7.50000000000000000e+00));
    bufp->fullIData(oldp+5152,(0x80U),32);
    bufp->fullIData(oldp+5153,(6U),32);
    bufp->fullIData(oldp+5154,(5U),32);
    bufp->fullIData(oldp+5155,(0xc350U),19);
    bufp->fullIData(oldp+5156,(9U),32);
    bufp->fullIData(oldp+5157,(0xbU),32);
    bufp->fullIData(oldp+5158,(0xcU),32);
    bufp->fullCData(oldp+5159,(0U),3);
    bufp->fullCData(oldp+5160,(2U),3);
    bufp->fullIData(oldp+5161,(0x20040U),19);
    bufp->fullCData(oldp+5162,(3U),3);
    bufp->fullIData(oldp+5163,(0x30004U),19);
    bufp->fullIData(oldp+5164,(0x30000U),19);
    bufp->fullIData(oldp+5165,(0U),17);
    bufp->fullCData(oldp+5166,(1U),3);
    bufp->fullIData(oldp+5167,(0x108c4U),19);
    bufp->fullIData(oldp+5168,(0x10844U),19);
    bufp->fullIData(oldp+5169,(0x720U),19);
    bufp->fullIData(oldp+5170,(0x4380005U),28);
    bufp->fullIData(oldp+5171,(vlSelf->main__DOT__ddr3_controller_inst__DOT__aligned_cmd),24);
    bufp->fullCData(oldp+5172,(vlSelf->main__DOT__ddr3_controller_inst__DOT__serial_index),2);
    bufp->fullCData(oldp+5173,(vlSelf->main__DOT__ddr3_controller_inst__DOT__serial_index_q),2);
    bufp->fullCData(oldp+5174,(vlSelf->main__DOT__ddr3_controller_inst__DOT__test_OFB),8);
    bufp->fullCData(oldp+5175,(vlSelf->main__DOT__ddr3_controller_inst__DOT__wb2_read_lane),3);
    bufp->fullIData(oldp+5176,(vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__delay),32);
    bufp->fullCData(oldp+5177,(vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__slot_number),2);
    bufp->fullCData(oldp+5178,(vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__read_slot),2);
    bufp->fullCData(oldp+5179,(vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__write_slot),2);
    bufp->fullCData(oldp+5180,(vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__anticipate_activate_slot),2);
    bufp->fullCData(oldp+5181,(vlSelf->main__DOT__ddr3_controller_inst__DOT__get_slot__Vstatic__anticipate_precharge_slot),2);
    bufp->fullIData(oldp+5182,(vlSelf->main__DOT__ddr3_controller_inst__DOT__find_delay__Vstatic__k),32);
    bufp->fullCData(oldp+5183,(0xcU),5);
    bufp->fullIData(oldp+5184,(0x1fU),32);
    bufp->fullIData(oldp+5185,(0x7fcU),20);
    bufp->fullIData(oldp+5186,(0x7fffffffU),31);
    bufp->fullIData(oldp+5187,(0x1eU),32);
    bufp->fullIData(oldp+5188,(0x24U),32);
    bufp->fullIData(oldp+5189,(0x400U),32);
    bufp->fullCData(oldp+5190,(0U),5);
    bufp->fullQData(oldp+5191,(0x100000000ULL),36);
    bufp->fullQData(oldp+5193,(0x40000000ULL),36);
    bufp->fullQData(oldp+5195,(0ULL),36);
    bufp->fullCData(oldp+5197,(0x4fU),7);
    bufp->fullCData(oldp+5198,(0x49U),7);
    bufp->fullIData(oldp+5199,(0x1cU),32);
    bufp->fullIData(oldp+5200,(0U),28);
    bufp->fullSData(oldp+5201,(0xfffU),12);
    bufp->fullCData(oldp+5202,(9U),4);
    bufp->fullCData(oldp+5203,(0xaU),4);
    bufp->fullCData(oldp+5204,(0xbU),4);
    bufp->fullCData(oldp+5205,(0xcU),4);
    bufp->fullCData(oldp+5206,(0xdU),4);
    bufp->fullCData(oldp+5207,(4U),3);
    bufp->fullCData(oldp+5208,(5U),3);
    bufp->fullCData(oldp+5209,(6U),3);
    bufp->fullCData(oldp+5210,(7U),3);
    bufp->fullCData(oldp+5211,(0xaU),5);
    bufp->fullIData(oldp+5212,(0x1fcU),20);
    bufp->fullCData(oldp+5213,(0x64U),7);
    bufp->fullCData(oldp+5214,(0x32U),7);
    bufp->fullIData(oldp+5215,(0xc0000000U),32);
    bufp->fullCData(oldp+5216,(1U),8);
    bufp->fullCData(oldp+5217,(2U),8);
    bufp->fullCData(oldp+5218,(3U),8);
    bufp->fullCData(oldp+5219,(4U),8);
    bufp->fullCData(oldp+5220,(5U),8);
    bufp->fullCData(oldp+5221,(6U),8);
    bufp->fullCData(oldp+5222,(7U),8);
    bufp->fullCData(oldp+5223,(8U),8);
    bufp->fullCData(oldp+5224,(9U),8);
    bufp->fullCData(oldp+5225,(0xaU),8);
    bufp->fullCData(oldp+5226,(0xbU),8);
    bufp->fullCData(oldp+5227,(0xcU),8);
    bufp->fullCData(oldp+5228,(0xdU),8);
    bufp->fullCData(oldp+5229,(0xeU),8);
    bufp->fullCData(oldp+5230,(0xfU),8);
    bufp->fullCData(oldp+5231,(0x80U),8);
    bufp->fullCData(oldp+5232,(0x10U),8);
    bufp->fullIData(oldp+5233,(0U),20);
    bufp->fullIData(oldp+5234,(0x208U),32);
    __Vtemp_hf465e4c8__0[0U] = 0x54494e47U;
    __Vtemp_hf465e4c8__0[1U] = 0x45524e41U;
    __Vtemp_hf465e4c8__0[2U] = 0x414c54U;
    bufp->fullWData(oldp+5235,(__Vtemp_hf465e4c8__0),88);
    bufp->fullIData(oldp+5238,(0x41425254U),32);
    bufp->fullIData(oldp+5239,(0x40U),32);
    bufp->fullIData(oldp+5240,(0xfU),32);
    bufp->fullBit(oldp+5241,(vlSelf->main__DOT__swic__DOT__thecpu__DOT__DATA_CACHE__DOT__mem__DOT__UNUSED_BITS__DOT__unused_aw));
    bufp->fullIData(oldp+5242,(0x1000000U),26);
    bufp->fullCData(oldp+5243,(0xeU),4);
    bufp->fullSData(oldp+5244,(0x1d7U),9);
    bufp->fullSData(oldp+5245,(0x2000U),14);
    bufp->fullIData(oldp+5246,(0U),31);
    bufp->fullCData(oldp+5247,(7U),5);
    bufp->fullSData(oldp+5248,(0x1021U),16);
    bufp->fullCData(oldp+5249,(9U),7);
    bufp->fullIData(oldp+5250,(0x10U),32);
    bufp->fullIData(oldp+5251,(0x5f5e100U),32);
    bufp->fullIData(oldp+5252,(0x186a0U),32);
    bufp->fullIData(oldp+5253,(0x4e20U),32);
    bufp->fullIData(oldp+5254,(0x1387U),32);
    bufp->fullSData(oldp+5255,(0xc8U),12);
    __Vtemp_hba125475__0[0U] = 0x18100800U;
    __Vtemp_hba125475__0[1U] = 0x38302820U;
    __Vtemp_hba125475__0[2U] = 0x80604840U;
    bufp->fullWData(oldp+5256,(__Vtemp_hba125475__0),96);
    __Vtemp_hca679e21__0[0U] = 0xf8f8f8f8U;
    __Vtemp_hca679e21__0[1U] = 0xf8f8f8f8U;
    __Vtemp_hca679e21__0[2U] = 0x80e0f8f8U;
    bufp->fullWData(oldp+5259,(__Vtemp_hca679e21__0),96);
    bufp->fullSData(oldp+5262,(0U),12);
    bufp->fullSData(oldp+5263,(0xf000U),16);
    bufp->fullIData(oldp+5264,(0x25U),32);
    bufp->fullIData(oldp+5265,(0x2dU),32);
    bufp->fullQData(oldp+5266,(0x20000000000000ULL),54);
    bufp->fullQData(oldp+5268,(0x20000004000000ULL),54);
    __Vtemp_h0730ce07__0[0U] = 0x80000U;
    __Vtemp_h0730ce07__0[1U] = 0x400U;
    __Vtemp_h0730ce07__0[2U] = 2U;
    bufp->fullWData(oldp+5270,(__Vtemp_h0730ce07__0),66);
    __Vtemp_h754c1427__0[0U] = 0x380000U;
    __Vtemp_h754c1427__0[1U] = 0xe00U;
    __Vtemp_h754c1427__0[2U] = 2U;
    bufp->fullWData(oldp+5273,(__Vtemp_h754c1427__0),66);
    bufp->fullIData(oldp+5276,(0x241U),32);
    bufp->fullIData(oldp+5277,(0x257U),32);
}
