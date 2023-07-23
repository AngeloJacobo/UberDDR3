# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Make include file with class lists
#
# This file lists generated Verilated files, for including in higher level makefiles.
# See Vmain.mk for the caller.

### Switches...
# C11 constructs required?  0/1 (always on now)
VM_C11 = 1
# Timing enabled?  0/1
VM_TIMING = 0
# Coverage output mode?  0/1 (from --coverage)
VM_COVERAGE = 0
# Parallel builds?  0/1 (from --output-split)
VM_PARALLEL_BUILDS = 1
# Tracing output mode?  0/1 (from --trace/--trace-fst)
VM_TRACE = 1
# Tracing output mode in VCD format?  0/1 (from --trace)
VM_TRACE_VCD = 1
# Tracing output mode in FST format?  0/1 (from --trace-fst)
VM_TRACE_FST = 0

### Object file lists...
# Generated module classes, fast-path, compile with highest optimization
VM_CLASSES_FAST += \
	Vmain \
	Vmain___024root__DepSet_h8b02a3a0__0 \
	Vmain___024root__DepSet_h3334316c__0 \
	Vmain___024root__DepSet_h3334316c__1 \
	Vmain___024root__DepSet_h3334316c__2 \
	Vmain___024root__DepSet_h3334316c__3 \
	Vmain___024root__DepSet_h3334316c__4 \
	Vmain___024root__DepSet_h3334316c__5 \

# Generated module classes, non-fast-path, compile with low/medium optimization
VM_CLASSES_SLOW += \
	Vmain__ConstPool_0 \
	Vmain___024root__Slow \
	Vmain___024root__DepSet_h8b02a3a0__0__Slow \
	Vmain___024root__DepSet_h3334316c__0__Slow \
	Vmain___024root__DepSet_h3334316c__1__Slow \
	Vmain___024root__DepSet_h3334316c__2__Slow \

# Generated support classes, fast-path, compile with highest optimization
VM_SUPPORT_FAST += \
	Vmain__Dpi \
	Vmain__Trace__0 \

# Generated support classes, non-fast-path, compile with low/medium optimization
VM_SUPPORT_SLOW += \
	Vmain__Syms \
	Vmain__Trace__0__Slow \

# Global classes, need linked once per executable, fast-path, compile with highest optimization
VM_GLOBAL_FAST += \
	verilated \
	verilated_dpi \
	verilated_vcd_c \
	verilated_threads \

# Global classes, need linked once per executable, non-fast-path, compile with low/medium optimization
VM_GLOBAL_SLOW += \


# Verilated -*- Makefile -*-
