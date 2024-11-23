PROJECT = nexysvideo_ddr3
FAMILY = artix7
PART = xc7a200tsbg484-1
CHIPDB  = ${ARTIX7_CHIPDB}
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

BOARD ?= UNKNOWN
JTAG_LINK ?= --board ${BOARD}

XDC ?= ${PROJECT}.xdc

.PHONY: all
all: ${PROJECT}.bit

.PHONY: program
program: ${PROJECT}.bit
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

${PROJECT}.bit: ${PROJECT}.frames
	xc7frames2bit --part_file ${PRJXRAY_DB_DIR}/${FAMILY}/${PART}/part.yaml --part_name ${PART} --frm_file $< --output_file $@

.PHONY: clean
clean:
	@rm -f *.bit
	@rm -f *.frames
	@rm -f *.fasm
	@rm -f *.json
	@rm -f *.bin
	@rm -f *.bba
	
.PHONY: pnrclean
pnrclean:
	rm *.fasm *.frames *.bit 