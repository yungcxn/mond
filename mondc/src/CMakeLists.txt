cmake_minimum_required(VERSION 3.20)

add_executable(mondc mondc.c)

execute_process(
        COMMAND python generatestandard.py
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tools
)