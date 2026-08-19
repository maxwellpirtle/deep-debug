set(BENCH_PROGRAMS
  mutex-bug
  mutex-clean
  sem-bug
  sem-clean
)

# Benchmark binaries land next to `libmcmini.so` at the top of the build tree.
# `target::set_preload_libmcmini()` derives LD_PRELOAD from the directory of
# the target program, so a benchmark placed anywhere else names a preload path
# that does not exist and dies before model checking begins.
foreach(bench_program ${BENCH_PROGRAMS})
  add_executable(${bench_program} ${bench_program}.c)
  target_link_libraries(${bench_program} PUBLIC -pthread)
  target_compile_options(${bench_program} PRIVATE -Wall)
  set_target_properties(${bench_program} PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
endforeach()
