#
# FL4's kernel CMake project: a drop-in for seL4's top-level CMakeLists.txt
# (DESIGN.md §12). Configuration and the flags exported to user space follow
# upstream seL4; kernel.elf is linked from the fl4-kernel staticlib that
# cargo builds.
#
# SPDX-License-Identifier: GPL-2.0-only
#

cmake_minimum_required(VERSION 3.16.0)
include(CheckCCompilerFlag)

include(${CMAKE_CURRENT_LIST_DIR}/fl4-settings.cmake)
include(${CMAKE_CURRENT_LIST_DIR}/configs/seL4Config.cmake)
project(seL4 C ASM)

find_file(KERNEL_HELPERS_PATH helpers.cmake PATHS tools CMAKE_FIND_ROOT_PATH_BOTH)
mark_as_advanced(FORCE KERNEL_HELPERS_PATH)
include(${KERNEL_HELPERS_PATH})

function(RequireTool config file)
  RequireFile("${config}" "${file}" PATHS tools)
endfunction(RequireTool)

include(tools/internal.cmake)
set(PYTHON3 "python3" CACHE INTERNAL "")
RequireTool(KERNEL_FLAGS_PATH flags.cmake)
RequireTool(CONFIG_GEN_PATH config_gen.py)
RequireTool(BF_GEN_PATH bitfield_gen.py)
RequireTool(HARDWARE_GEN_PATH hardware_gen.py)
RequireTool(INVOCATION_ID_GEN_PATH invocation_header_gen.py)
RequireTool(SYSCALL_ID_GEN_PATH syscall_header_gen.py)
RequireTool(XMLLINT_PATH xmllint.sh)

include(config.cmake)

if(FL4_AARCH64)
  if(NOT KernelIsMCS OR KernelArmHypervisorSupport OR KernelFastpath OR HardwareDebugAPI)
    message(FATAL_ERROR "FL4: configuration rules were not applied")
  endif()
elseif(NOT KernelIsMCS OR NOT KernelVTX OR KernelIOMMU OR KernelFastpath)
  message(FATAL_ERROR "FL4: configuration rules were not applied")
endif()

# Flags user code compiles with, as upstream sets them.
string(APPEND common_flags " -D__KERNEL_${KernelWordSize}__")
if(FL4_AARCH64)
  set(arm_march "${KernelArmArmV}${KernelArmMachFeatureModifiers}")
  string(APPEND c_common_flags " -march=${arm_march}")
  string(APPEND asm_common_flags " -march=${arm_march}")
else()
  if(${KernelX86MicroArch} STREQUAL "generic")
    string(APPEND common_flags " -mtune=generic")
  else()
    string(APPEND common_flags " -march=${KernelX86MicroArch}")
  endif()
  string(APPEND common_exe_flags " -Wl,-m,elf_x86_64")
  string(APPEND c_common_flags " -m${KernelWordSize}")
  if(NOT LLVM_TOOLCHAIN)
    string(APPEND asm_common_flags " -Wa,--${KernelWordSize}")
  endif()
endif()
set(BASE_ASM_FLAGS "${asm_common_flags} ${common_flags}" CACHE INTERNAL "")
set(BASE_C_FLAGS "${c_common_flags} ${common_flags}" CACHE INTERNAL "")
set(BASE_CXX_FLAGS "${cxx_common_flags} ${c_common_flags} ${common_flags}" CACHE INTERNAL "")
set(BASE_EXE_LINKER_FLAGS "${common_flags} ${common_exe_flags} " CACHE INTERNAL "")

generate_autoconf(kernel_autoconf "kernel")
add_custom_target(kernel_config_headers DEPENDS kernel_autoconf_Gen kernel_autoconf kernel_Config
                                                kernel_Gen)
add_custom_target(kernel_headers DEPENDS kernel_config_headers)

# The kernel itself.
set(fl4_cargo_dir "${CMAKE_CURRENT_BINARY_DIR}/cargo")
if(FL4_AARCH64)
  set(fl4_target aarch64-unknown-none-softfloat)
  set(fl4_package fl4-kernel-aarch64)
  set(fl4_lib "${fl4_cargo_dir}/${fl4_target}/release/libfl4_kernel_aarch64.a")
  set(fl4_linker_script "${FL4_ROOT}/crates/fl4-kernel-aarch64/linker.ld")
  set(fl4_emulation "")
else()
  set(fl4_target x86_64-unknown-none)
  set(fl4_package fl4-kernel)
  set(fl4_lib "${fl4_cargo_dir}/${fl4_target}/release/libfl4_kernel.a")
  set(fl4_linker_script "${FL4_ROOT}/crates/fl4-kernel/linker.ld")
  set(fl4_emulation "-Wl,-m,elf_x86_64")
  # Safe RET must cover compiler-built library code as well.
  set(fl4_cargo_env RUSTC_BOOTSTRAP=1)
  # Newer Cargo filters inherited variables in rustc's target probe.
  set(fl4_cargo_flags -Zbuild-std=core,alloc --config "env.RUSTC_BOOTSTRAP='1'")
endif()
set(fl4_gen_config "${CMAKE_CURRENT_BINARY_DIR}/gen_config/kernel/gen_config.json")
set(fl4_feature_list "")
if(NOT KernelDebugBuild)
  list(APPEND fl4_feature_list "release-profile")
endif()
# Test only: every kernel entry takes the serial gate (DESIGN.md §13, M4).
option(FL4_SERIAL_GATE "Run every kernel entry under the serial gate" OFF)
if(FL4_SERIAL_GATE)
  list(APPEND fl4_feature_list "serial-gate")
endif()
if(fl4_feature_list)
  list(JOIN fl4_feature_list "," fl4_feature_csv)
  set(fl4_features "--features=${fl4_feature_csv}")
else()
  set(fl4_features "")
endif()
find_program(CARGO cargo HINTS "$ENV{HOME}/.cargo/bin" REQUIRED)
add_custom_target(
  fl4_cargo_build
  COMMAND ${CMAKE_COMMAND} -E env FL4_GEN_CONFIG=${fl4_gen_config} CARGO_TARGET_DIR=${fl4_cargo_dir} ${fl4_cargo_env}
          ${CARGO} build ${fl4_cargo_flags} --quiet --release -p ${fl4_package} --target ${fl4_target} ${fl4_features}
  WORKING_DIRECTORY ${FL4_ROOT}
  BYPRODUCTS ${fl4_lib}
  DEPENDS kernel_config_headers
  COMMENT "Building the FL4 kernel with cargo"
  USES_TERMINAL VERBATIM)

file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/fl4_empty.S" "")
add_executable(kernel.elf EXCLUDE_FROM_ALL "${CMAKE_CURRENT_BINARY_DIR}/fl4_empty.S")
add_dependencies(kernel.elf fl4_cargo_build)
set_target_properties(kernel.elf PROPERTIES LINKER_LANGUAGE C LINK_DEPENDS "${fl4_lib};${fl4_linker_script}")
target_link_options(kernel.elf PRIVATE -nostdlib -static -Wl,--build-id=none -Wl,-n
                    -Wl,-T,${fl4_linker_script} ${fl4_emulation} -Wl,--gc-sections -Wl,-u,fl4_boot)
target_link_libraries(kernel.elf PRIVATE -Wl,--whole-archive ${fl4_lib} -Wl,--no-whole-archive)
if(NOT FL4_AARCH64)
  find_package(Python3 REQUIRED COMPONENTS Interpreter)
  set(fl4_asm_check "${FL4_ROOT}/xtask/scripts/check_vm_asm.py")
  set_property(TARGET kernel.elf APPEND PROPERTY LINK_DEPENDS "${fl4_asm_check}")
  add_custom_command(TARGET kernel.elf POST_BUILD
      COMMAND "${Python3_EXECUTABLE}" "${fl4_asm_check}" "$<TARGET_FILE:kernel.elf>" "${CMAKE_OBJDUMP}"
      VERBATIM)
endif()


if(FL4_AARCH64)
  # AArch64 boots through FL4's UEFI loader with the kernel built in
  # (DESIGN.md section 11). A root server image is the loader with the
  # root task built in too; the seL4 tools' DeclareRootserver calls this
  # instead of building an elfloader image (xtask patches it in).
  find_program(CARGO_FOR_EFI cargo HINTS "$ENV{HOME}/.cargo/bin" REQUIRED)
  macro(fl4_declare_rootserver rootservername)
    set(IMAGE_NAME "${CMAKE_BINARY_DIR}/images/${rootservername}-image-${KernelArch}-${KernelPlatform}")
    set(fl4_kernel_stripped "${CMAKE_BINARY_DIR}/kernel/kernel-stripped.elf")
    add_custom_command(
      OUTPUT "${IMAGE_NAME}"
      COMMAND ${CMAKE_OBJCOPY} --strip-debug $<TARGET_FILE:kernel.elf> ${fl4_kernel_stripped}
      COMMAND ${CMAKE_COMMAND} -E env FL4_KERNEL_ELF=${fl4_kernel_stripped}
              FL4_ROOTSERVER_ELF=$<TARGET_FILE:${rootservername}>
              CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/kernel/cargo-efi ${CARGO_FOR_EFI} build --quiet
              --release -p fl4-efi --target aarch64-unknown-uefi
      COMMAND ${CMAKE_COMMAND} -E copy
              ${CMAKE_BINARY_DIR}/kernel/cargo-efi/aarch64-unknown-uefi/release/fl4-efi.efi "${IMAGE_NAME}"
      WORKING_DIRECTORY ${FL4_ROOT}
      DEPENDS kernel.elf ${rootservername}
      COMMENT "Building the FL4 UEFI image"
      VERBATIM)
    add_custom_target(rootserver_image ALL DEPENDS "${IMAGE_NAME}" kernel.elf ${rootservername})
    set_property(TARGET "${rootservername}" PROPERTY OUTPUT_NAME "${rootservername}")
    get_property(rootimage TARGET "${rootservername}" PROPERTY OUTPUT_NAME)
    get_property(dir TARGET "${rootservername}" PROPERTY BINARY_DIR)
    set_property(TARGET rootserver_image PROPERTY ROOTSERVER_IMAGE "${dir}/${rootimage}")
  endmacro()
endif()
