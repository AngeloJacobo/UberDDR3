// diamond 3.7 accepts this PLL
// diamond 3.8-3.9 is untested
// diamond 3.10 or higher is likely to abort with error about unable to use feedback signal
// cause of this could be from wrong CPHASE/FPHASE parameters
module clk_wiz
(
    input reset, // 0:inactive, 1:reset
    input CLKI, // 48 MHz, 0 deg
    output CLKOP, // 160 MHz, 0 deg
    output CLKOS, // 160 MHz, 90 deg
    output CLKOS2, // 40 MHz, 0 deg
    output locked
);
(* FREQUENCY_PIN_CLKI="48" *)
(* FREQUENCY_PIN_CLKOP="160" *)
(* FREQUENCY_PIN_CLKOS="160" *)
(* FREQUENCY_PIN_CLKOS2="40" *)
(* ICP_CURRENT="12" *) (* LPF_RESISTOR="8" *) (* MFG_ENABLE_FILTEROPAMP="1" *) (* MFG_GMCREF_SEL="2" *)
EHXPLLL #(
        .PLLRST_ENA("ENABLED"),
        .INTFB_WAKE("DISABLED"),
        .STDBY_ENABLE("DISABLED"),
        .DPHASE_SOURCE("DISABLED"),
        .OUTDIVIDER_MUXA("DIVA"),
        .OUTDIVIDER_MUXB("DIVB"),
        .OUTDIVIDER_MUXC("DIVC"),
        .OUTDIVIDER_MUXD("DIVD"),
        .CLKI_DIV(3),
        .CLKOP_ENABLE("ENABLED"),
        .CLKOP_DIV(4),
        .CLKOP_CPHASE(2),
        .CLKOP_FPHASE(0),
        .CLKOS_ENABLE("ENABLED"),
        .CLKOS_DIV(4),
        .CLKOS_CPHASE(3),
        .CLKOS_FPHASE(0),
        .CLKOS2_ENABLE("ENABLED"),
        .CLKOS2_DIV(16),
        .CLKOS2_CPHASE(2),
        .CLKOS2_FPHASE(0),
        .FEEDBK_PATH("CLKOP"),
        .CLKFB_DIV(10)
    ) pll_i (
        .RST(reset),
        .STDBY(1'b0),
        .CLKI(CLKI),
        .CLKOP(CLKOP),
        .CLKOS(CLKOS),
        .CLKOS2(CLKOS2),
        .CLKFB(CLKOP),
        .CLKINTFB(),
        .PHASESEL0(1'b0),
        .PHASESEL1(1'b0),
        .PHASEDIR(1'b1),
        .PHASESTEP(1'b1),
        .PHASELOADREG(1'b1),
        .PLLWAKESYNC(1'b0),
        .ENCLKOP(1'b0),
        .LOCK(locked)
	);
endmodule
