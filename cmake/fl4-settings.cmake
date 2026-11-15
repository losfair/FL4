#
# FL4's configuration rules (DESIGN.md §3), applied before upstream's
# config.cmake declares the options. Options FL4 detects at boot or fixes
# at one value are forced, so whatever a project asks for, the generated
# configuration that libsel4 and user code see matches the kernel.
#
# SPDX-License-Identifier: GPL-2.0-only
#

function(fl4_force var value)
  set(${var} "${value}" CACHE STRING "Fixed by FL4 (DESIGN.md section 3)" FORCE)
endfunction()

function(fl4_require var value why)
  if(DEFINED ${var} AND NOT "${${var}}" STREQUAL "${value}")
    message(FATAL_ERROR "FL4: ${var}=${${var}} is not supported (${why}). FL4 builds only with ${var}=${value}.")
  endif()
  fl4_force(${var} "${value}")
endfunction()

if(DEFINED KernelPlatform AND NOT KernelPlatform STREQUAL "pc99")
  message(FATAL_ERROR "FL4: only the x86_64 pc99 platform is supported for now")
endif()
fl4_require(KernelIsMCS ON "FL4 implements only the MCS API")
fl4_require(KernelSel4Arch x86_64 "x86_64 is the only architecture for now")
fl4_force(KernelVTX ON)
fl4_force(KernelX86_64VTX64BitGuests ON)
fl4_require(KernelNumDomains 1 "FL4 supports one scheduling domain")

# API shape.
fl4_force(KernelIOMMU OFF)
fl4_force(KernelHugePage ON)
fl4_force(KernelSyscall syscall)
# Fastpaths and dangerous options are always off.
fl4_force(KernelFastpath OFF)
fl4_force(KernelExceptionFastpath OFF)
fl4_force(KernelSignalFastpath OFF)
fl4_force(KernelDangerousCodeInjection OFF)
fl4_force(KernelBenchmarks none)
# The bench profile (DESIGN.md section 3): a project that asks for user
# access to the performance counters or for the MSR syscalls, as sel4bench
# does, gets both; every other build gets neither.
if(KernelX86DangerousMSR OR KernelExportPMCUser)
  fl4_force(KernelX86DangerousMSR ON)
  fl4_force(KernelExportPMCUser ON)
else()
  fl4_force(KernelX86DangerousMSR OFF)
  fl4_force(KernelExportPMCUser OFF)
endif()
# Untyped resets clear 64 KiB per preemption point (l4h 0030).
fl4_force(KernelResetChunkBits 16)
# Kernel limits FL4 builds in at seL4's defaults (DESIGN.md section 3). A
# project that asks for another value would see it in libsel4's generated
# configuration while the kernel enforces its own, so refuse it.
fl4_require(KernelRetypeFanOutLimit 256 "the kernel's retype fan-out limit is 256")
fl4_require(KernelNumPriorities 256 "the kernel has 256 priorities")
fl4_require(KernelMaxNumWorkUnitsPerPreemption 100 "the kernel's preemption work-unit limit is 100")
fl4_require(KernelMaxNumBootinfoUntypedCaps 230 "BootInfo holds 230 untyped caps")
fl4_require(KernelBootThreadTimeSlice 5 "the boot thread's time slice is 5 ms")
fl4_require(KernelWcetScale 1 "the kernel WCET estimate is unscaled")
fl4_require(KernelStaticMaxPeriodUs 0 "the maximum period is seL4's default")
# Detected at boot: the values here only decide what CONFIG_* user code
# sees, and FL4 makes them say "the general case".
fl4_force(KernelLAPICMode XAPIC)
fl4_force(KernelIRQController IOAPIC)
fl4_force(KernelSupportPCID OFF)
fl4_force(KernelFSGSBase msr)
fl4_force(KernelFPU XSAVE)
fl4_force(KernelXSave XSAVE)
fl4_force(KernelSkimWindow OFF)
fl4_force(KernelX86IBRSMode ibrs_none)
fl4_force(KernelX86IBPBOnContextSwitch OFF)
fl4_force(KernelX86RSBOnContextSwitch OFF)
fl4_force(KernelMultiboot1Header ON)
fl4_force(KernelMultiboot2Header ON)

# The build profile decides the debug features together.
if(NOT DEFINED KernelDebugBuild)
  set(KernelDebugBuild ON)
endif()
# -DReleasePrinting=ON keeps seL4_DebugPutChar in a release build, for
# benchmarks whose user-space output must reach the serial port.
if(ReleasePrinting)
  fl4_force(KernelPrinting ON)
else()
  fl4_force(KernelPrinting ${KernelDebugBuild})
endif()
fl4_force(HardwareDebugAPI ${KernelDebugBuild})
fl4_force(KernelInvocationReportErrorIPC ${KernelDebugBuild})
fl4_force(KernelIRQReporting ${KernelDebugBuild})
