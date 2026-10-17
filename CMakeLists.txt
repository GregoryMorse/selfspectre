cmake_minimum_required(VERSION 3.20)
project(selfspectre C)

# Native sources of Gregory Morse, "Self-Spectre, Write-Execute and the Hidden State": the Write-Execute
# procedures (src/writeexc.asm, MASM syntax), their test harnesses and the Spectre proof-of-concept programs.
# Builds on Windows (MSVC, x86 and x64), Linux (x86 and x64) and macOS (x64). The MASM source is assembled by
# ml/ml64 with MSVC and by UASM (a MASM-compatible assembler, built from a pinned source revision) elsewhere.
# This is evidence for the Lean development, not part of it; see validation/README.md.

option(SELFSPECTRE_BUILD_SPECTRE "Build the Spectre proof-of-concept programs (built, never run by the tests)" ON)

enable_testing()

if(CMAKE_SIZEOF_VOID_P EQUAL 8)
  set(WE_X64 TRUE)
else()
  set(WE_X64 FALSE)
endif()
if(NOT CMAKE_SYSTEM_PROCESSOR MATCHES "([Xx]86|AMD64|amd64|i[3-6]86|x64)")
  message(FATAL_ERROR "The Write-Execute procedures are x86/x86-64 machine code (processor: ${CMAKE_SYSTEM_PROCESSOR})")
endif()

set(WE_ASM ${CMAKE_SOURCE_DIR}/src/writeexc.asm)
set(RSA_ASM ${CMAKE_SOURCE_DIR}/src/spectrecode.asm)

# ---- assembling ------------------------------------------------------------------------------------------
if(MSVC)
  enable_language(ASM_MASM)
  if(WE_X64)
    set_source_files_properties(${WE_ASM} ${RSA_ASM} PROPERTIES COMPILE_DEFINITIONS X64)
  endif()
  add_library(we_asm OBJECT ${WE_ASM})
  add_library(rsa_asm OBJECT ${RSA_ASM})
  set(WE_OBJECTS $<TARGET_OBJECTS:we_asm>)
  set(RSA_OBJECTS $<TARGET_OBJECTS:rsa_asm>)
else()
  include(cmake/UASM.cmake)
  we_uasm_object(we_asm_obj ${WE_ASM} we)
  we_uasm_object(rsa_asm_obj ${RSA_ASM} rsa)
  set(WE_OBJECTS ${we_asm_obj})
  set(RSA_OBJECTS ${rsa_asm_obj})
endif()

# ---- compiler and linker settings shared by every program -------------------------------------------------
function(we_configure target)
  target_include_directories(${target} PRIVATE ${CMAKE_SOURCE_DIR}/src)
  if(MSVC)
    # The Write-Execute procedures rewrite their own code: the text section must be writable.
    # /Qspectre- : no compiler Spectre mitigation (it would insert lfence barriers into the victim code).
    target_compile_options(${target} PRIVATE /Qspectre-)
    target_link_options(${target} PRIVATE /SECTION:.text,ERW /INCREMENTAL:NO)
    if(NOT WE_X64)
      target_link_options(${target} PRIVATE /SAFESEH:NO)
    endif()
  else()
    # -fno-strict-aliasing: the legacy sources reinterpret integers through pointers; -fcommon: they define
    # some globals (e.g. key) in more than one file.
    target_compile_definitions(${target} PRIVATE _GNU_SOURCE)
    target_compile_options(${target} PRIVATE -O2 -fno-strict-aliasing -fcommon -maes -msse4.2 -w)
    if(APPLE)
      target_link_options(${target} PRIVATE -Wl,-segprot,__TEXT,rwx,rwx)
    else()
      # Non-PIE so that the 32-bit absolute references of the x86 code resolve at link time; the harnesses
      # make the text writable at run time (we_make_code_writable).
      target_compile_options(${target} PRIVATE -fno-pie)
      target_link_options(${target} PRIVATE -no-pie)
    endif()
  endif()
endfunction()

# ---- harnesses ---------------------------------------------------------------------------------------------
add_executable(code_vectors validation/native/code_vectors.c) # includes spectreopt.c itself
we_configure(code_vectors)

add_executable(edge_vectors validation/native/edge_vectors.c src/spectreopt.c ${WE_OBJECTS})
we_configure(edge_vectors)

add_executable(writeexec src/writeexec.c src/spectreopt.c ${WE_OBJECTS})
we_configure(writeexec)

# Pass criteria (validation/README.md): the exit code is 0 and no mismatch line "GOT[WANT]" is printed.
add_test(NAME code_vectors COMMAND code_vectors)
add_test(NAME edge_vectors COMMAND edge_vectors)
set_tests_properties(edge_vectors PROPERTIES PASS_REGULAR_EXPRESSION "edge vectors ok")
add_test(NAME writeexec_harness COMMAND writeexec)
set_tests_properties(writeexec_harness PROPERTIES FAIL_REGULAR_EXPRESSION "[0-9A-Fa-f]\\[[0-9A-Fa-f]+\\]" TIMEOUT 1800)

# ---- Spectre programs (built only) -------------------------------------------------------------------------
if(SELFSPECTRE_BUILD_SPECTRE)
  add_executable(spectrepoc src/spectre.c)
  we_configure(spectrepoc)
  add_executable(selfspectre_aes src/spectreaes.c src/spectreopt.c)
  we_configure(selfspectre_aes)
  # spectrecode.asm refers to C globals; the macOS ELF bridge (cmake/elf2blob.py) cannot express those references
  # (Mach-O has no pc-relative relocation to an undefined symbol in an assembler expression), so this program is not built there.
  if(NOT APPLE)
    add_executable(selfspectre_rsa src/spectrersa.c src/spectreopt.c ${RSA_OBJECTS})
    we_configure(selfspectre_rsa)
  endif()
endif()
