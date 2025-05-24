rm -rf ./uberddr3_sim ./sim.log
iverilog -o uberddr3_sim -g2012 \
    -DNO_TEST_MODEL \
    -s ddr3_dimm_micron_sim \
    -I ../ \
    ../ddr3_dimm_micron_sim.sv \
    ../ddr3.sv \
    ../models/IDELAYCTRL_model.v \
    ../models/IDELAYE2_model.v \
    ../models/IOBUF_DCIEN.v \
    ../models/IOBUF_model.v \
    ../models/IOBUFDS_DCIEN_model.v \
    ../models/IOBUFDS_model.v \
    ../models/ISERDESE2_model.v \
    ../models/OBUFDS_model.v \
    ../models/ODELAYE2_model.v \
    ../models/OSERDESE2_model.v \
    ../models/OBUF_model.v \
    ../../rtl/ddr3_top.v \
    ../../rtl/ddr3_controller.v \
    ../../rtl/ddr3_phy.v \
    ../ddr3_module.sv

vvp -n ./uberddr3_sim 




