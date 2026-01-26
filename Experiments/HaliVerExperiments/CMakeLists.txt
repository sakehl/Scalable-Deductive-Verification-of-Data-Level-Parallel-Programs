cmake_minimum_required(VERSION 3.16)
project(HaliVerExperiments)

include(CTest)

set(CMAKE_CXX_STANDARD 11)  # or newer
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)
list(APPEND CMAKE_PREFIX_PATH ../Halide/install)

find_package(Halide REQUIRED)

set(OUTFILE halide.out)
set(VCT "/haliver/vercors/bin/vct" CACHE STRING "Default value for VCT")
set(VERCORS ${VCT} --silicon-quiet --no-infer-heap-context-into-frame --dev-total-timeout=1200 --dev-assert-timeout 60)
set(VERCORS_PADRE ${VCT} --silicon-quiet --no-infer-heap-context-into-frame --dev-total-timeout=3600 --dev-assert-timeout 60)

function(build_experiment_test)
  set(options NO_TEST NOT_FRONT)
  set(oneValueArgs TARGET DIR)
  set(multiValueArgs LABELS SCHEDULES)
  cmake_parse_arguments(UT "${options}" "${oneValueArgs}"
                          "${multiValueArgs}" ${ARGN} )

  
  if(NOT TARGET ${UT_TARGET})
    add_executable(${UT_TARGET} tests/${UT_DIR}/${UT_TARGET}.cpp)
  endif()

  target_link_libraries(${UT_TARGET} PRIVATE Halide::Halide)

  if(NOT UT_SCHEDULES)
    set(UT_SCHEDULES "0" "1" "2" "3")
  endif()

  if(NOT TARGET ${UT_TARGET}_pvl)
    add_custom_command(
      OUTPUT ${UT_TARGET}_front.pvl
      COMMAND ./${UT_TARGET} ${UT_TARGET}_front front
      DEPENDS ${UT_TARGET}
      VERBATIM
    )
    if(NOT ${UT_NO_TEST} AND NOT ${UT_NOT_FRONT})
      add_test(NAME ${UT_TARGET}_front.pvl
        COMMAND ${VERCORS} ${CMAKE_BINARY_DIR}/${UT_TARGET}_front.pvl
      )
      set_tests_properties(${UT_TARGET}_front.pvl PROPERTIES
        LABELS experiment:${UT_DIR}:front:${UT_LABELS}
      )
    endif()

    add_custom_target(
      ${UT_TARGET}_pvl ALL
      DEPENDS ${UT_TARGET}_front.pvl
    )
  endif()

  foreach(V IN LISTS UT_SCHEDULES)
    add_custom_command(
      OUTPUT ${UT_TARGET}_${V}.c
      COMMAND ./${UT_TARGET} ${UT_TARGET}_${V} schedule ${V}
      DEPENDS ${UT_TARGET}
      VERBATIM
    )

    add_custom_command(
      OUTPUT ${UT_TARGET}_${V}_non_unique.c
      COMMAND ./${UT_TARGET} ${UT_TARGET}_${V}_non_unique schedule ${V} non_unique
      DEPENDS ${UT_TARGET}
      VERBATIM
    )

    if(NOT ${UT_NO_TEST})
      add_test(NAME ${UT_TARGET}_${V}.c
        COMMAND ${VERCORS} ${CMAKE_BINARY_DIR}/${UT_TARGET}_${V}.c
      )
      set_tests_properties(${UT_TARGET}_${V}.c PROPERTIES
        LABELS experiment:${UT_DIR}:back:${UT_LABELS}
      )
    endif()

  endforeach()

  foreach(V IN LISTS UT_SCHEDULES)
    add_custom_command(
      OUTPUT ${UT_TARGET}_${V}_mem.c
      COMMAND ./${UT_TARGET} ${UT_TARGET}_${V}_mem schedule ${V} mem
      DEPENDS ${UT_TARGET}
      VERBATIM
    )

    add_custom_command(
      OUTPUT ${UT_TARGET}_${V}_mem_non_unique.c
      COMMAND ./${UT_TARGET} ${UT_TARGET}_${V}_mem_non_unique schedule ${V} mem non_unique
      DEPENDS ${UT_TARGET}
      VERBATIM
    )

    if(NOT ${UT_NO_TEST})
      add_test(NAME ${UT_TARGET}_${V}_mem.c
        COMMAND ${VERCORS} ${CMAKE_BINARY_DIR}/${UT_TARGET}_${V}_mem.c
      )
      set_tests_properties(${UT_TARGET}_${V}_mem.c PROPERTIES
        LABELS experiment:${UT_DIR}:back:${UT_LABELS}:mem
      )
    endif()

    add_custom_target(
      ${UT_TARGET}_${V} ALL
      DEPENDS ${UT_TARGET}_${V}.c ${UT_TARGET}_${V}_mem.c
        ${UT_TARGET}_${V}_non_unique.c ${UT_TARGET}_${V}_mem_non_unique.c
    )

  endforeach()
endfunction()

function(build_single_experiment_test)
  set(options)
  set(oneValueArgs TARGET DIR)
  set(multiValueArgs LABELS)
  cmake_parse_arguments(UT "${options}" "${oneValueArgs}"
                          "${multiValueArgs}" ${ARGN} )

  add_executable(${UT_TARGET} tests/${UT_DIR}/${UT_TARGET}.cpp)

  target_link_libraries(${UT_TARGET} PRIVATE Halide::Halide)

  add_custom_command(
    OUTPUT ${UT_TARGET}_mem.c
    COMMAND ./${UT_TARGET} ${UT_TARGET}_mem
    DEPENDS ${UT_TARGET}
    VERBATIM
  )

  add_custom_target(
    ${UT_TARGET}_pvl ALL
    DEPENDS ${UT_TARGET}_mem.c
  )

  add_test(NAME ${UT_TARGET}_mem.c
    COMMAND ${VERCORS} ${CMAKE_BINARY_DIR}/${UT_TARGET}_mem.c
  )
  set_tests_properties(${UT_TARGET}_mem.c PROPERTIES
    LABELS ${UT_DIR}:back:${UT_LABELS}
  )
endfunction()

function(build_padre)
  set(options CONCRETE_BOUNDS)
  cmake_parse_arguments(UT "${options}" "${oneValueArgs}"
                          "${multiValueArgs}" ${ARGN} )

  set(CB "")
  if(${UT_CONCRETE_BOUNDS})
    set(CB "CB")
  endif()

  add_executable(GenerateHalideDiagonal${CB} tests/padre/GenerateHalideDiagonal.cpp)
  add_executable(GenerateHalideFull${CB} tests/padre/GenerateHalideFull.cpp)
  target_link_libraries(GenerateHalideDiagonal${CB} PRIVATE Halide::Halide)
  target_link_libraries(GenerateHalideFull${CB} PRIVATE Halide::Halide)
  if(${UT_CONCRETE_BOUNDS})
    target_compile_definitions(GenerateHalideDiagonal${CB} PUBLIC CONCRETE_BOUNDS)
    target_compile_definitions(GenerateHalideFull${CB} PUBLIC CONCRETE_BOUNDS)
  endif()
  
  add_custom_command(
    OUTPUT SubDirectionHalide${CB}.c SolveDirectionHalide${CB}.c StepHalide${CB}.c
    COMMAND ./GenerateHalideDiagonal${CB}
    DEPENDS GenerateHalideDiagonal${CB}
  )
  
  add_custom_target(
    GenerateHalideDiagonal${CB}_output ALL
    DEPENDS SubDirectionHalide${CB}.c SolveDirectionHalide${CB}.c StepHalide${CB}.c
  )
  
  add_custom_command(
    OUTPUT PerformIterationHalide${CB}.c
    COMMAND ./GenerateHalideFull${CB}
    DEPENDS GenerateHalideFull${CB}
  )
  
  add_custom_target(GenerateHalideFull${CB}_output ALL
    DEPENDS PerformIterationHalide${CB}.c
    GenerateHalideDiagonal${CB}_output
  )
  
  foreach(FILE SubDirectionHalide${CB}.c SolveDirectionHalide${CB}.c StepHalide${CB}.c PerformIterationHalide${CB}.c)
    add_test(NAME ${FILE}
      COMMAND ${VERCORS_PADRE} ${CMAKE_BINARY_DIR}/${FILE}
    )
    set_tests_properties(${FILE} PROPERTIES
      LABELS padre:back:${CB}
      TIMEOUT 3600
    )
  endforeach()
endfunction()

# Experiments: involved Halide programs
build_experiment_test(TARGET blur DIR experiment)
build_experiment_test(TARGET hist DIR experiment)
build_experiment_test(TARGET conv_layer DIR experiment)
build_experiment_test(TARGET auto_viz DIR experiment SCHEDULES 1 2 NOT_FRONT)
build_experiment_test(TARGET auto_viz DIR experiment SCHEDULES 0 3 NO_TEST)

build_experiment_test(TARGET gemm DIR experiment SCHEDULES 0 1 2 )
build_experiment_test(TARGET gemm DIR experiment SCHEDULES 3 NO_TEST)

# build_single_experiment_test(TARGET bgu DIR bgu)
build_single_experiment_test(TARGET bilateral_grid DIR experiment)
build_single_experiment_test(TARGET camera_pipe DIR experiment)
build_single_experiment_test(TARGET depthwise_separable_conv DIR experiment)

## Build padre files
build_padre()
build_padre(CONCRETE_BOUNDS)

# Tutorial
function(build_lesson)
  set(options)
  set(oneValueArgs TARGET DIR)
  set(multiValueArgs)
  cmake_parse_arguments(UT "${options}" "${oneValueArgs}"
                          "${multiValueArgs}" ${ARGN} )

  add_executable(${UT_TARGET} ${UT_DIR}/${UT_TARGET}.cpp)

  target_link_libraries(${UT_TARGET} PRIVATE Halide::Halide)

  add_custom_command(
    OUTPUT tutorial
    COMMAND mkdir -p tutorial
    VERBATIM
  )

  add_custom_command(
    OUTPUT ${UT_TARGET}_all_files
    COMMAND ./${UT_TARGET}
    DEPENDS ${UT_TARGET}
    VERBATIM
  )

  add_custom_target(
    ${UT_TARGET}_all ALL
    DEPENDS ${UT_TARGET}_all_files tutorial
  )
endfunction()


build_lesson(TARGET lesson1 DIR tutorial)
build_lesson(TARGET lesson2 DIR tutorial)
build_lesson(TARGET lesson3 DIR tutorial)