cmake_minimum_required(VERSION 3.20)

project(mondc C)

set(CMAKE_C_STANDARD 99)

find_package(Python REQUIRED)

add_subdirectory (${CMAKE_SOURCE_DIR}/src)
add_subdirectory (${CMAKE_SOURCE_DIR}/try)
add_subdirectory (${CMAKE_SOURCE_DIR}/test)