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
  BUILD_IN_SOURCE TRUE
  BUILD_COMMAND ${UASM_MAKE} -k -f ${UASM_MAKEFILE} CC=${UASM_HOST_CC} "CFLAGS=-std=gnu89 -fcommon -w -Wno-int-conversion -Wno-incompatible-pointer-types -Wno-implicit-function-declaration"
  INSTALL_COMMAND ""
  BUILD_BYPRODUCTS ${UASM_EXE})

if(APPLE)
  set(UASM_FORMAT -macho64)
elseif(WE_X64)
  set(UASM_FORMAT -elf64)
else()
  set(UASM_FORMAT -elf)
endif()
if(WE_X64)
  set(UASM_DEFS -DX64)
else()
  set(UASM_DEFS "")
endif()

# we_uasm_object(<variable> <source.asm> <name>) sets <variable> to the object file produced from the source.
function(we_uasm_object var source name)
  set(obj ${CMAKE_BINARY_DIR}/${name}.o)
  add_custom_command(OUTPUT ${obj}
    COMMAND ${UASM_EXE} ${UASM_FORMAT} ${UASM_DEFS} -Fo${obj} ${source}
    DEPENDS ${source} uasm_build
    COMMENT "UASM ${source}"
    VERBATIM)
  set(${var} ${obj} PARENT_SCOPE)
endfunction()
