PROJ=orangecrab_ecp5_ddr3
EXTRA_VERILOG_FILES= uart_rx.v  uart_tx.v clk_wiz_ecppll.v ../../rtl/ddr3_top.v ../../rtl/ddr3_controller.v  ../../rtl/ecp5_phy/ddr3_phy_ecp5.v  ../../rtl/ecp5_phy/iserdes_soft.v ../../rtl/ecp5_phy/oserdes_soft.v   
# `r0.1` or `r0.2` or `r0.2.1`
VERSION:=r0.2.1
# `25F` or `85F`
DENSITY=85F

ifneq (,$(findstring 85,$(DENSITY)))
	NEXTPNR_DENSITY:=--85k
else
	NEXTPNR_DENSITY:=--25k
endif

# Add Windows and Unix support
RM         = rm -rf
COPY       = cp -a
PATH_SEP   = /
ifeq ($(OS),Windows_NT)
# When SHELL=sh.exe and this actually exists, make will silently
# switch to using that instead of cmd.exe.  Unfortunately, there's
# no way to tell which environment we're running under without either
# (1) printing out an error message, or (2) finding something that
# works everywhere.
# As a result, we force the shell to be cmd.exe, so it works both
# under cygwin and normal Windows.
SHELL      = cmd.exe
COPY       = copy
RM         = del
PATH_SEP   = \\
endif


all: ${PROJ}.dfu

dfu: ${PROJ}.dfu
	dfu-util --alt 0 -D $<


%.json: %.v
	yosys -p "read_verilog -D LATTICE_ECP5_PHY $< ${EXTRA_VERILOG_FILES} ; synth_ecp5 -json $@ -top ${PROJ}"

%_out.config: %.json
	nextpnr-ecp5 --json $< --textcfg $@ $(NEXTPNR_DENSITY) --package CSFBGA285 --lpf ${PROJ}.pcf

%.bit: %_out.config
	ecppack --compress --freq 38.8 --input $< --bit $@

%.dfu : %.bit
	$(COPY) $< $@
	dfu-suffix -v 1209 -p 5af0 -a $@

clean:
	$(RM) -f ${PROJ}.bit ${PROJ}_out.config ${PROJ}.json ${PROJ}.dfu

.PHONY: prog clean
