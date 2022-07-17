cmake_minimum_required(VERSION 3.20)
project(mondc C)

set(CMAKE_C_STANDARD 99)

enable_testing()

add_subdirectory (${PROJECT_SOURCE_DIR}/test)

add_executable(mondc mondc.c)

execute_process(
        COMMAND python generatestandard.py
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tools
)