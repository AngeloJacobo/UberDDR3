rm -rf ./uberddr3_sim 
iverilog -o uberddr3_sim -g2012 \
    -DNO_TEST_MODEL \
    -s ddr3_dimm_micron_sim \
    -I ./ \
    ./ddr3_dimm_micron_sim.sv \
    ./ddr3.sv \
    ./IDELAYCTRL_model.v \
    ./IDELAYE2_model.v \
    ./IOBUF_DCIEN.v \
    ./IOBUF_model.v \
    ./IOBUFDS_DCIEN_model.v \
    ./IOBUFDS_model.v \
    ./ISERDESE2_model.v \
    ./OBUFDS_model.v \
    ./ODELAYE2_model.v \
    ./OSERDESE2_model.v \
    ./OBUF_model.v \
    ../rtl/ddr3_top.v \
    ../rtl/ddr3_controller.v \
    ../rtl/ddr3_phy.v 

vvp ./uberddr3_sim

