PROJECT = ypcb_00338_1p1_ddr3
FAMILY = kintex7
PART = xc7k480tffg1156-2
CHIPDB = ${KINTEX7_CHIPDB}
ADDITIONAL_SOURCES = ../../rtl/ddr3_controller.v ../../rtl/ddr3_phy.v ../../rtl/ddr3_top.v clk_wiz_ypcb.v

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
PNR_ARGS ?=

JTAG_LINK ?= -c digilent_hs3

XDC ?= ${PROJECT}.xdc

.PHONY: openxc7
openxc7: ${PROJECT}_openxc7.bit

.PHONY: program
program: ${PROJECT}_openxc7.bit
	openFPGALoader ${JTAG_LINK} --bitstream $<

${PROJECT}.json: ${TOP_VERILOG} ${ADDITIONAL_SOURCES}
	yosys -p "synth_xilinx -flatten -abc9 ${SYNTH_OPTS} -arch xc7 -top ${TOP_MODULE}; write_json ${PROJECT}.json" $< ${ADDITIONAL_SOURCES}

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

.PHONY: clean
clean:
	rm -f *.bit
	rm -f *.frames
	rm -f *.fasm
	rm -f *.json
	rm -f *.bin
	rm -f *.bba
