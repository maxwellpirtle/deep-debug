if(BUILD_TESTS)
  add_executable(relations_test relations_test.cpp $<TARGET_OBJECTS:mcmini_core>)
  target_include_directories(relations_test PUBLIC "${MCMINI_INCLUDE_DIR}")
  target_compile_definitions(relations_test
    PUBLIC
      "${MCMINI_EXTRA_COMPILER_DEFINITIONS}")
  target_compile_options(relations_test
    PRIVATE
      "${MCMINI_EXTRA_COMPILER_FLAGS}")
  target_link_libraries(relations_test
    PUBLIC
      "${MCMINI_EXTRA_LINK_FLAGS}")
  # `$<TARGET_OBJECTS:>` carries objects, not link dependencies, so a
  # SCIP-enabled `mcmini_core` leaves SCIP to be linked here as well.
  if (MCMINI_USE_SCIP)
    target_link_libraries(relations_test PUBLIC scip)
  endif()
  add_test(NAME relations COMMAND relations_test)

  add_executable(logging_test logging_test.cpp $<TARGET_OBJECTS:mcmini_core>)
  target_include_directories(logging_test PUBLIC "${MCMINI_INCLUDE_DIR}")
  target_compile_definitions(logging_test
    PUBLIC
      "${MCMINI_EXTRA_COMPILER_DEFINITIONS}")
  target_compile_options(logging_test
    PRIVATE
      "${MCMINI_EXTRA_COMPILER_FLAGS}")
  target_link_libraries(logging_test
    PUBLIC
      "${MCMINI_EXTRA_LINK_FLAGS}")
  # `$<TARGET_OBJECTS:>` carries objects, not link dependencies, so a
  # SCIP-enabled `mcmini_core` leaves SCIP to be linked here as well.
  if (MCMINI_USE_SCIP)
    target_link_libraries(logging_test PUBLIC scip)
  endif()
  add_test(NAME logging COMMAND logging_test)
endif()
