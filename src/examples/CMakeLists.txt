add_executable(hello-world hello-world.c)
add_executable(cv-hello-world cv-hello-world.c)
add_executable(cv-test cv-test.c)
add_executable(deadly-embrace deadly-embrace.c)
add_executable(fifo-example fifo.cpp)
add_executable(producer-consumer producer-consumer.c)
add_executable(recycled-thread recycled-thread.c)
# CTest reserves the target name `test`, so this example is named for what it
# actually demonstrates.
add_executable(dining-philosophers test.cpp)
target_link_libraries(hello-world PUBLIC -pthread libmcmini)
target_link_libraries(cv-hello-world PUBLIC -pthread)
target_link_libraries(cv-test PUBLIC -pthread)
target_link_libraries(deadly-embrace PUBLIC -pthread)
target_link_libraries(producer-consumer PUBLIC -pthread)
target_link_libraries(recycled-thread PUBLIC -pthread libmcmini)

# The two `sem_destroy` controls land next to `libmcmini.so` at the top of the
# build tree, unlike every other example here.
# `target::set_preload_libmcmini()` derives LD_PRELOAD from the directory of
# the target program, so a program placed anywhere else names a preload path
# that does not exist and dies before model checking begins. `bench/` carries
# the same property for the same reason.
foreach(sem_destroy_example sem-destroy-clean sem-destroy-uaf)
  add_executable(${sem_destroy_example} ${sem_destroy_example}.c)
  target_link_libraries(${sem_destroy_example} PUBLIC -pthread)
  target_compile_options(${sem_destroy_example} PRIVATE -Wall)
  set_target_properties(${sem_destroy_example} PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
endforeach()
