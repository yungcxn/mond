cmake_minimum_required(VERSION 3.20)

project(mondc C)

set(CMAKE_C_STANDARD 99)

find_package(Python REQUIRED)


enable_testing()

set(binpath "${CMAKE_SOURCE_DIR}/bin")

add_subdirectory (${CMAKE_SOURCE_DIR}/src)
add_subdirectory (${CMAKE_SOURCE_DIR}/test)
add_subdirectory (${CMAKE_SOURCE_DIR}/try)