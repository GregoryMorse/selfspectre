# Assemble the MASM sources with UASM (https://github.com/Terraspace/UASM, a MASM-compatible assembler) on
# Linux and macOS. UASM is built from a pinned source revision at build time.
include(ExternalProject)

set(UASM_REVISION 97f643891c19ef257e45f1bf67cb47244ae72784) # v2.57r
set(UASM_MAKEFILE Makefile-Linux-GCC-64.mak) # the GCC/Clang makefile also serves macOS
set(UASM_PREFIX ${CMAKE_BINARY_DIR}/uasm)
set(UASM_EXE ${UASM_PREFIX}/src/uasm_build/GccUnixR/uasm)

find_program(UASM_HOST_CC NAMES clang cc gcc REQUIRED)
find_program(UASM_MAKE NAMES gmake make REQUIRED)

ExternalProject_Add(uasm_build
  PREFIX ${UASM_PREFIX}
  GIT_REPOSITORY https://github.com/Terraspace/UASM.git
  GIT_TAG ${UASM_REVISION}
  CONFIGURE_COMMAND ""
  PATCH_COMMAND sed -i.bak "s/-Wl,-Map,[^ ]*//" ${UASM_MAKEFILE}
  BUILD_IN_SOURCE TRUE
  BUILD_COMMAND ${UASM_MAKE} -k -f ${UASM_MAKEFILE} CC=${UASM_HOST_CC} "CFLAGS=-std=gnu89 -fcommon -w -Wno-int-conversion -Wno-incompatible-pointer-types -Wno-implicit-function-declaration"
  INSTALL_COMMAND ""
  BUILD_BYPRODUCTS ${UASM_EXE})

if(APPLE)
  # UASM's Mach-O writer cannot express the relocations of this code, so the ELF object is converted to a
  # position-independent blob (cmake/elf2blob.py) that the system assembler places in __TEXT,__text.
  set(UASM_FORMAT -elf64)
elseif(WE_X64)
  set(UASM_FORMAT -elf64)
else()
  set(UASM_FORMAT -elf -6 -zcw) # -zcw: no leading underscore on C symbols, as GCC on ELF
endif()
if(APPLE OR WE_X64)
  find_package(Python3 REQUIRED COMPONENTS Interpreter)
endif()
if(WE_X64)
  # UASM duplicates ELF64 RELA PC32 addends in the encoded displacement.
  # GNU ld would apply both and misdirect self-modifying code stores.
  set(UASM_NORMALIZE_DEPENDENCY ${CMAKE_SOURCE_DIR}/cmake/normalize_uasm_elf64.py)
else()
  set(UASM_NORMALIZE_DEPENDENCY "")
endif()
if(WE_X64)
  set(UASM_DEFS -DX64)
else()
  set(UASM_DEFS "")
endif()

# we_uasm_object(<variable> <source.asm> <name>) sets <variable> to the object file produced from the source.
function(we_uasm_object var source name)
  set(obj ${CMAKE_BINARY_DIR}/${name}.o)
  set(patched ${CMAKE_BINARY_DIR}/${name}_uasm.asm)
  if(APPLE)
    set(elf ${CMAKE_BINARY_DIR}/${name}_elf.o)
    set(normalize_command)
    if(WE_X64)
      set(normalize_command COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/cmake/normalize_uasm_elf64.py ${elf})
    endif()
    add_custom_command(OUTPUT ${obj}
      COMMAND ${CMAKE_COMMAND} -DIN=${source} -DOUT=${patched} -DWE_X64=${WE_X64} -P ${CMAKE_SOURCE_DIR}/cmake/UasmPatch.cmake
      COMMAND ${UASM_EXE} ${UASM_FORMAT} ${UASM_DEFS} -Fo${elf} ${patched}
      ${normalize_command}
      COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/cmake/elf2blob.py ${elf} ${CMAKE_BINARY_DIR}/${name}.bin ${CMAKE_BINARY_DIR}/${name}_blob.s
      COMMAND ${CMAKE_C_COMPILER} -c -x assembler ${CMAKE_BINARY_DIR}/${name}_blob.s -o ${obj}
      DEPENDS ${source} uasm_build ${CMAKE_SOURCE_DIR}/cmake/UasmPatch.cmake ${CMAKE_SOURCE_DIR}/cmake/elf2blob.py ${UASM_NORMALIZE_DEPENDENCY}
      COMMENT "UASM ${source} (via ELF)"
      VERBATIM)
  else()
    set(normalize_command)
    if(WE_X64)
      set(normalize_command COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/cmake/normalize_uasm_elf64.py ${obj})
    endif()
    add_custom_command(OUTPUT ${obj}
      COMMAND ${CMAKE_COMMAND} -DIN=${source} -DOUT=${patched} -DWE_X64=${WE_X64} -P ${CMAKE_SOURCE_DIR}/cmake/UasmPatch.cmake
      COMMAND ${UASM_EXE} ${UASM_FORMAT} ${UASM_DEFS} -Fo${obj} ${patched}
      ${normalize_command}
      DEPENDS ${source} uasm_build ${CMAKE_SOURCE_DIR}/cmake/UasmPatch.cmake ${UASM_NORMALIZE_DEPENDENCY}
      COMMENT "UASM ${source}"
      VERBATIM)
  endif()
  set(${var} ${obj} PARENT_SCOPE)
endfunction()
