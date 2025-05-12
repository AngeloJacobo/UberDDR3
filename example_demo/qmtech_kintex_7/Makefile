PROJECT = qmtech_kintex7_ddr3
FAMILY = kintex7
PART = xc7k325tffg676-1
CHIPDB  = ${KINTEX7_CHIPDB}
ADDITIONAL_SOURCES = ../../rtl/ddr3_controller.v  ../../rtl/ddr3_phy.v  ../../rtl/ddr3_top.v  uart_rx.v  uart_tx.v clk_wiz.v 


#############################################################################################
NEXTPNR_XILINX_DIR ?= /snap/openxc7/current/opt/nextpnr-xilinx
NEXTPNR_XILINX_PYTHON_DIR ?= ${NEXTPNR_XILINX_DIR}/python
PRJXRAY_DB_DIR ?= ${NEXTPNR_XILINX_DIR}/external/prjxray-db

DBPART = $(shell echo ${PART} | sed -e 's/-[0-9]//g')
SPEEDGRADE = $(shell echo ${PART} | sed -e 's/.*\-\([0-9]\)/\1/g')

CHIPDB ?= ./
ifeq ($(CHIPDB),)
CHIPDB = ./
endif

PYPY3 ?= pypy3

TOP ?= ${PROJECT}
TOP_MODULE ?= ${TOP}
TOP_VERILOG ?= ${TOP}.v

PNR_DEBUG ?= # --verbose --debug

JTAG_LINK ?= -c digilent_hs2

XDC ?= ${PROJECT}.xdc

.PHONY: openxc7
openxc7: ${PROJECT}_openxc7.bit

.PHONY: program
program: ${PROJECT}_openxc7.bit
	openFPGALoader ${JTAG_LINK} --bitstream $<

${PROJECT}.json: ${TOP_VERILOG} ${ADDITIONAL_SOURCES}
	yosys -p "synth_xilinx -flatten -abc9 ${SYNTH_OPTS} -arch xc7 -top ${TOP_MODULE}; write_json ${PROJECT}.json" $< ${ADDITIONAL_SOURCES}

# The chip database only needs to be generated once
# that is why we don't clean it with make clean
${CHIPDB}/${DBPART}.bin:
	${PYPY3} ${NEXTPNR_XILINX_PYTHON_DIR}/bbaexport.py --device ${PART} --bba ${DBPART}.bba
	bbasm -l ${DBPART}.bba ${CHIPDB}/${DBPART}.bin
	rm -f ${DBPART}.bba

${PROJECT}.fasm: ${PROJECT}.json ${CHIPDB}/${DBPART}.bin ${XDC}
	nextpnr-xilinx --chipdb ${CHIPDB}/${DBPART}.bin --xdc ${XDC} --json ${PROJECT}.json --fasm $@ ${PNR_ARGS} ${PNR_DEBUG}
	
${PROJECT}.frames: ${PROJECT}.fasm
	fasm2frames --part ${PART} --db-root ${PRJXRAY_DB_DIR}/${FAMILY} $< > $@

${PROJECT}_openxc7.bit: ${PROJECT}.frames
	xc7frames2bit --part_file ${PRJXRAY_DB_DIR}/${FAMILY}/${PART}/part.yaml --part_name ${PART} --frm_file $< --output_file $@


#############################################################################################
# SPDX-License-Identifier: MIT
# Generated from https://github.com/FPGAOL-CE/caas-wizard
#
BUILDDIR := ${CURDIR}/build

LOGFILE := ${BUILDDIR}/top.log

# Build design
.PHONY: vivado
vivado: ${BUILDDIR}/${PROJECT}_vivado.bit

${BUILDDIR}:
	mkdir -m 777 -p ${BUILDDIR} && chown -R nobody ${BUILDDIR} | true

.ONESHELL: 
${BUILDDIR}/vivado.tcl: ${BUILDDIR}
	cat << EOF > $@
	# vivado.tcl generated for FPGAOL-CE/caas-wizard
	# can be launched from any directory
	cd ${BUILDDIR}
	create_project -part ${PART} -force v_proj
	set_property target_language Verilog [current_project]
	cd ..
	read_verilog [glob ${PROJECT}.v ${ADDITIONAL_SOURCES}]
	read_xdc [glob  $(wildcard ${PROJECT}.xdc) ]
	cd build
	synth_design -top ${PROJECT}
	opt_design
	place_design
	phys_opt_design
	route_design
	write_bitstream -verbose -force ${PROJECT}_vivado.bit
	# report_utilization -file util.rpt
	# report_timing_summary -file timing.rpt
	EOF

${BUILDDIR}/${PROJECT}_vivado.bit: ${BUILDDIR}/vivado.tcl
	cd ${BUILDDIR} && vivado -mode batch -source $< > ${LOGFILE} 2>&1

.PHONY: program_vivado
program_vivado: 
	openFPGALoader ${JTAG_LINK} --bitstream ${BUILDDIR}/${PROJECT}_vivado.bit

#############################################################################################

.PHONY: clean
clean:
	rm -f *.bit
	rm -f *.frames
	rm -f *.fasm
	rm -f *.json
	rm -f *.bin
	rm -f *.bba
	rm -rf ${BUILDDIR}
