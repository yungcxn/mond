cmake_minimum_required(VERSION 3.20)

execute_process(
        COMMAND python3 generatestandard.py
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tools
)

add_executable(mondc mondc.c)

add_test(
        NAME example_comp
        COMMAND "$<TARGET_FILE:mondc> examples/example.mon"
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)