cmake_minimum_required(VERSION 3.20)
project(mondc C)

set(CMAKE_C_STANDARD 99)

enable_testing()

add_subdirectory (${PROJECT_SOURCE_DIR}/test)


add_executable(mondc main.c)
