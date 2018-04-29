cmake_minimum_required(VERSION 2.8)
add_definitions("-O3 -std=c++11")
add_executable(st-exact
  main.cpp
  CBGfinder.cpp
)
