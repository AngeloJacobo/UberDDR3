

import fileinput
import subprocess

# Define the path to the .vh file
vh_file = "../testbench/8192Mb_ddr3_parameters.vh"

# Modify BUS_DELAY and execute the simulation command
def run_simulation(delay, log_file):
    with fileinput.FileInput(vh_file, inplace=True) as file:
        for line in file:
            if line.startswith("    parameter BUS_DELAY"):
                line = f"    parameter BUS_DELAY        =     {delay}; // delay in nanoseconds\n"
            print(line, end="")
    
    # Print BUS_DELAY and log file name
    print(f"BUS_DELAY: {delay} ps")
    print(f"Log File: {log_file}")

    with open(log_file, "a") as log:
        print("")
        subprocess.call(["./ddr3_dimm_micron_sim.sh"], stdout=log, shell=True)
    
    # Print log contents starting from "------- SUMMARY -------"
    print_log_summary(log_file)
    print("")

# Function to print log contents from "------- SUMMARY -------" section
def print_log_summary(log_file):
    with open(log_file, "r") as log:
        summary_reached = False
        for line in log:
            if line.startswith("------- SUMMARY -------"):
                summary_reached = True
            if summary_reached:
                print(line.strip())

# Run simulations with different BUS_DELAY values
run_simulation(0, "sim_test_busdelay0ps.log")
run_simulation(1000, "sim_busdelay1000ps.log")
run_simulation(5000, "sim_busdelay5000ps.log")
run_simulation(10000, "sim_busdelay10000ps.log")
