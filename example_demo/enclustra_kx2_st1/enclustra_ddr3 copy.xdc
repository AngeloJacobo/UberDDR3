################################################################################
################################################################################
set_property CFGBVS GND [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 22 [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPPOWERDOWN ENABLE [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLNONE [current_design]

# set_property -dict {PACKAGE_PIN AD24 IOSTANDARD LVCMOS18 } [get_ports {CLK_100_CAL}]
# set_property DCI_CASCADE {32 33} [get_iobanks 34]
## For a 1.5V memory, the appropriate VREF voltage is half of 1.5, or 0.75 Volts
## Of the DDR3 bank(s), only bank 33 needs the INTERNAL_VREF. The other DDR3
## banks are explicitly connected to an external VREF signal. However, bank
## 33s IOs are overloaded--there was no room for the VREF. Hence, to spare
## two pins, bank 33 uses an internal voltage reference. Sadly, the same
## problem plays out in banks 12-16 as well.
# set_property INTERNAL_VREF 0.750 [get_iobanks 33]
# ## Other IO banks have internal VREFs as well, those these aren't as critical
# set_property INTERNAL_VREF 0.90 [get_iobanks 12]
# set_property INTERNAL_VREF 0.60 [get_iobanks 13]
# set_property INTERNAL_VREF 0.90 [get_iobanks 14]
# set_property INTERNAL_VREF 0.90 [get_iobanks 15]
# set_property INTERNAL_VREF 0.90 [get_iobanks 16]

## Clocks
# 100MHz single ended input clock
set_property -dict {PACKAGE_PIN AA4 IOSTANDARD SSTL15} [get_ports i_clk]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports i_clk]

# Baseboard LEDs
# set_property -dict {SLEW SLOW PACKAGE_PIN F22 IOSTANDARD LVCMOS18 } [get_ports { o_led_status[4] }] # GPIO0_LED0_N
set_property -dict {PACKAGE_PIN E23 IOSTANDARD LVCMOS18} [get_ports {led[0]}] 
set_property -dict {PACKAGE_PIN K25 IOSTANDARD LVCMOS12} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN K26 IOSTANDARD LVCMOS12} [get_ports {led[2]}]

## UART
## {{{
set_property -dict {PACKAGE_PIN B20 IOSTANDARD LVCMOS18 } [get_ports {rx}]
set_property -dict {PACKAGE_PIN A20 IOSTANDARD LVCMOS18 } [get_ports {tx}]
## }}}

## Buttons
## {{{
 set_property -dict {PACKAGE_PIN C22 IOSTANDARD LVCMOS18 } [get_ports {i_rst_n}]

## DDR3 MEMORY
set_property -dict {PACKAGE_PIN AB7 IOSTANDARD LVCMOS15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_reset_n}]

set_property -dict {PACKAGE_PIN AB12 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_clk_p}]
set_property -dict {PACKAGE_PIN AC12 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_clk_n}]
set_property -dict {PACKAGE_PIN AA13 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_cke}]
## set_property -dict {SLEW SLOW PACKAGE_PIN AA3 IOSTANDARD LVCMOS15 } [get_ports {o_ddr3_vsel}]
set_property -dict {PACKAGE_PIN Y12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_cs_n}]
set_property -dict {PACKAGE_PIN AE13 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_ras_n}]
set_property -dict {PACKAGE_PIN AE12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_cas_n}]
set_property -dict {PACKAGE_PIN AA12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_we_n}]
set_property -dict {PACKAGE_PIN AD13 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_odt}]


## Address lines
set_property -dict {PACKAGE_PIN AE11 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[0]}]
set_property -dict {PACKAGE_PIN AF9 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[1]}]
set_property -dict {PACKAGE_PIN AD10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[2]}]
set_property -dict {PACKAGE_PIN AB10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[3]}]
set_property -dict {PACKAGE_PIN AA9 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[4]}]
set_property -dict {PACKAGE_PIN AB9 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[5]}]
set_property -dict {PACKAGE_PIN AA8 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[6]}]
set_property -dict {PACKAGE_PIN AC8 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[7]}]
set_property -dict {PACKAGE_PIN AA7 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[8]}]
set_property -dict {PACKAGE_PIN AE8 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[9]}]

set_property -dict {PACKAGE_PIN AF10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[10]}]
set_property -dict {PACKAGE_PIN AD8 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[11]}]
set_property -dict {PACKAGE_PIN AE10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[12]}]
set_property -dict {PACKAGE_PIN AF8 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[13]}]
set_property -dict {PACKAGE_PIN AC7 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_addr[14]}]

set_property -dict {PACKAGE_PIN AD11 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_ba[0]}]
set_property -dict {PACKAGE_PIN AA10 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_ba[1]}]
set_property -dict {PACKAGE_PIN AF12 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_ba[2]}]


## Byte lane #0
set_property -dict {PACKAGE_PIN AA2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[0]}]
set_property -dict {PACKAGE_PIN Y2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[1]}]
set_property -dict {PACKAGE_PIN AB2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[2]}]
set_property -dict {PACKAGE_PIN V1 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[3]}]
set_property -dict {PACKAGE_PIN Y1 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[4]}]
set_property -dict {PACKAGE_PIN W1 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[5]}]
set_property -dict {PACKAGE_PIN AC2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[6]}]
set_property -dict {PACKAGE_PIN V2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[7]}]

set_property -dict {PACKAGE_PIN Y3 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[0]}]

set_property -dict {PACKAGE_PIN AB1 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[0]}]
set_property -dict {PACKAGE_PIN AC1 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[0]}]


## Byte lane #1
set_property -dict {PACKAGE_PIN W3 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[8]}]
set_property -dict {PACKAGE_PIN V3 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[9]}]
set_property -dict {PACKAGE_PIN U1 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[10]}]
set_property -dict {PACKAGE_PIN U7 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[11]}]
set_property -dict {PACKAGE_PIN U6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[12]}]
set_property -dict {PACKAGE_PIN V4 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[13]}]
set_property -dict {PACKAGE_PIN V6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[14]}]
set_property -dict {PACKAGE_PIN U2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[15]}]

set_property -dict {PACKAGE_PIN U5 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[1]}]

set_property -dict {PACKAGE_PIN W6 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[1]}]
set_property -dict {PACKAGE_PIN W5 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[1]}]


## Byte lane #2
set_property -dict {PACKAGE_PIN AE3 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[16]}]
set_property -dict {PACKAGE_PIN AE6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[17]}]
set_property -dict {PACKAGE_PIN AF3 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[18]}]
set_property -dict {PACKAGE_PIN AD1 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[19]}]
set_property -dict {PACKAGE_PIN AE1 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[20]}]
set_property -dict {PACKAGE_PIN AE2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[21]}]
set_property -dict {PACKAGE_PIN AF2 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[22]}]
set_property -dict {PACKAGE_PIN AE5 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[23]}]

set_property -dict {PACKAGE_PIN AD4 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[2]}]

set_property -dict {PACKAGE_PIN AF5 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[2]}]
set_property -dict {PACKAGE_PIN AF4 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[2]}]


## Byte lane #3
set_property -dict {PACKAGE_PIN AD5 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[24]}]
set_property -dict {PACKAGE_PIN Y5 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[25]}]
set_property -dict {PACKAGE_PIN AC6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[26]}]
set_property -dict {PACKAGE_PIN Y6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[27]}]
set_property -dict {PACKAGE_PIN AB4 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[28]}]
set_property -dict {PACKAGE_PIN AD6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[29]}]
set_property -dict {PACKAGE_PIN AB6 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[30]}]
set_property -dict {PACKAGE_PIN AC3 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[31]}]

set_property -dict {PACKAGE_PIN AC4 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[3]}]

set_property -dict {PACKAGE_PIN AA5 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[3]}]
set_property -dict {PACKAGE_PIN AB5 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[3]}]


## Byte lane #4
set_property -dict {PACKAGE_PIN AD16 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[32]}]
set_property -dict {PACKAGE_PIN AE17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[33]}]
set_property -dict {PACKAGE_PIN AF15 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[34]}]
set_property -dict {PACKAGE_PIN AF20 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[35]}]
set_property -dict {PACKAGE_PIN AD15 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[36]}]
set_property -dict {PACKAGE_PIN AF14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[37]}]
set_property -dict {PACKAGE_PIN AE15 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[38]}]
set_property -dict {PACKAGE_PIN AF17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[39]}]

set_property -dict {PACKAGE_PIN AF19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[4]}]

set_property -dict {PACKAGE_PIN AE18 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[4]}]
set_property -dict {PACKAGE_PIN AF18 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[4]}]


## Byte lane #5
set_property -dict {PACKAGE_PIN AA14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[40]}]
set_property -dict {PACKAGE_PIN AA15 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[41]}]
set_property -dict {PACKAGE_PIN AC14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[42]}]
set_property -dict {PACKAGE_PIN AD14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[43]}]
set_property -dict {PACKAGE_PIN AB14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[44]}]
set_property -dict {PACKAGE_PIN AB15 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[45]}]
set_property -dict {PACKAGE_PIN AA17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[46]}]
set_property -dict {PACKAGE_PIN AA18 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[47]}]

set_property -dict {PACKAGE_PIN AC16 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[5]}]

set_property -dict {PACKAGE_PIN Y15 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[5]}]
set_property -dict {PACKAGE_PIN Y16 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[5]}]


## Byte lane #6
set_property -dict {PACKAGE_PIN AB20 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[48]}]
set_property -dict {PACKAGE_PIN AD19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[49]}]
set_property -dict {PACKAGE_PIN AC19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[50]}]
set_property -dict {PACKAGE_PIN AA20 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[51]}]
set_property -dict {PACKAGE_PIN AA19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[52]}]
set_property -dict {PACKAGE_PIN AC17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[53]}]
set_property -dict {PACKAGE_PIN AD18 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[54]}]
set_property -dict {PACKAGE_PIN AB17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[55]}]
set_property -dict {PACKAGE_PIN AB19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[6]}]
set_property -dict {PACKAGE_PIN AD20 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[6]}]
set_property -dict {PACKAGE_PIN AE20 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[6]}]


## Byte lane #7
set_property -dict {PACKAGE_PIN W15 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[56]}]
set_property -dict {PACKAGE_PIN W16 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[57]}]
set_property -dict {PACKAGE_PIN W14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[58]}]
set_property -dict {PACKAGE_PIN V16 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[59]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[60]}]
set_property -dict {PACKAGE_PIN V17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[61]}]
set_property -dict {PACKAGE_PIN V18 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[62]}]
set_property -dict {PACKAGE_PIN Y17 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dq[63]}]

set_property -dict {PACKAGE_PIN V14 IOSTANDARD SSTL15 SLEW FAST VCCAUX_IO HIGH } [get_ports {ddr3_dm[7]}]

set_property -dict {PACKAGE_PIN W18 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_p[7]}]
set_property -dict {PACKAGE_PIN W19 IOSTANDARD DIFF_SSTL15 SLEW FAST VCCAUX_IO HIGH} [get_ports {ddr3_dqs_n[7]}]



set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
