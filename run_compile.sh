#!/bin/bash

# Function to run Verilator lint
run_lint() {
    echo -e "\e[32mRun Verilator Lint:\e[0m"
    verilator --lint-only rtl/ddr3_controller.v rtl/ecc/ecc_dec.sv rtl/ecc/ecc_enc.sv -Irtl/ -Wall
    echo "DONE!"
}

# If the script is called with "lint", run only linting and exit
if [[ "$1" == "lint" ]]; then
    run_lint
    exit 0
fi

# Clean files
rm -rf formal/ddr3*prf*
rm -rf formal/ddr3_singleconfig

# Run Verilator lint
run_lint    

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
echo -e "\e[32mRun Symbiyosys Formal Verification: ECC\e[0m"
echo "---------------------------------------"
sby -f formal/ecc.sby

echo ""
echo -e "\e[32mRun Symbiyosys Formal Verification: Single Configuration\e[0m"
echo "---------------------------------------"
sby -f formal/ddr3_singleconfig.sby

echo ""
echo -e "\e[32mRun Symbiyosys Formal Verification: Multiple Configurations (DEFAULT)\e[0m"
echo "---------------------------------------"
sby -f formal/ddr3_multiconfig_default.sby

echo ""
echo -e "\e[32mRun Symbiyosys Formal Verification: Multiple Configurations (ECC)\e[0m"
echo "---------------------------------------"
sby -f formal/ddr3_multiconfig_ecc.sby


# ANSI color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

echo ""
echo ""
echo "Summary:"

# Excluded folders
excluded_folders=("formal/ddr3_multiconfig_default/" "formal/ddr3_multiconfig_ecc/")

# Iterate over folders starting with 'ddr3*'
for folder in formal/ddr3*/ ; do
    # Skip excluded folders
    [[ " ${excluded_folders[*]} " =~ " ${folder} " ]] && continue

    # Check for 'PASS' file
    if [[ -e "${folder}PASS" ]]; then
        echo -e "${folder}: ${GREEN}PASS${NC}"
    else
        echo -e "${folder}: ${RED}FAIL${NC}"
    fi
done

# Iterate over folders inside 'ecc/'
for folder in formal/ecc/ ; do
    [[ " ${excluded_folders[*]} " =~ " ${folder} " ]] && continue

    if [[ -e "${folder}PASS" ]]; then
        echo -e "${folder}: ${GREEN}PASS${NC}"
    else
        echo -e "${folder}: ${RED}FAIL${NC}"
    fi
done
