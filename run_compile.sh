# Clean files
rm -rf formal/ddr3*prf*
rm -rf formal/ddr3_singleconfig

# run verilator lint
echo -e "\e[32mRun Verilator Lint:\e[0m"
verilator --lint-only rtl/ddr3_controller.v rtl/ecc/ecc_dec.sv rtl/ecc/ecc_enc.sv -Irtl/ -Wall
echo "DONE!"
    

# run yosys compile
echo ""
echo ""
echo -e "\e[32mRun Yosys Compile:\e[0m"
yosys -q -p "
    read_verilog -sv ./rtl/ddr3_controller.v rtl/ecc/ecc_dec.sv rtl/ecc/ecc_enc.sv;
    synth -top ddr3_controller"

# run iverilog compile
echo ""
echo ""
echo -e "\e[32mRun IVerilog Compile:\e[0m"
iverilog rtl/ddr3_controller.v -o out
vvp out
rm out
echo

# run symbiyosys 
echo ""
echo -e "\e[32mRun Symbiyosys Formal Verification: Single Configuration\e[0m"
echo "---------------------------------------"
sby -f formal/ddr3_singleconfig.sby

echo ""
echo -e "\e[32mRun Symbiyosys Formal Verification: Multiple Configurations\e[0m"
echo "---------------------------------------"
sby -f formal/ddr3_multiconfig.sby


# ANSI color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

echo ""
echo ""
echo "Summary:"
# Iterate over folders starting with 'ddr3*'
for folder in formal/ddr3*/ ; do
    # Check if the 'PASS' file exists in the folder
    if [[ -e "${folder}PASS" ]]; then
        # Print the folder name and 'PASS' in green
        echo -e "${folder}: ${GREEN}PASS${NC}"
    else
        # Print the folder name and 'FAIL' in red
        echo -e "${folder}: ${RED}FAIL${NC}"
    fi
done

