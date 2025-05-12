#!/bin/bash

# Create a logs directory to store all log files
rm -rf build_logs
mkdir -p build_logs

# Loop through each item in the current directory
for dir in */; do
    # Check if it's a directory and contains a Makefile
    if [ -d "$dir" ] && [ -f "$dir/Makefile" ]; then
        log_file="build_logs/${dir%/}.log"
        echo "Building $dir... Logging to $log_file"
        {
            echo "===== $(date) - Building $dir ====="
            cd "$dir"
            make clean
            make
            echo ""
            echo "DONE OPENXC7"
            echo ""
            echo ""
            make vivado
            echo ""
            echo "DONE VIVADO"
            echo ""
            echo ""
            cd ..
            echo "===== Finished $dir ====="
        } &> "$log_file"
    else
        echo "Skipping $dir (no Makefile found)"
    fi
done
