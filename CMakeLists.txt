# Specify the minimum version for CMake
cmake_minimum_required(VERSION 3.2)

# Project's name 
project(libZKPPHE)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -pthread -O0 -g")
find_package(OpenSSL REQUIRED)

include_directories(${OPENSSL_INCLUDE_DIR})

  
add_executable(test_range_proof test/test_range_proof.cpp)

target_link_libraries(test_range_proof ${OPENSSL_LIBRARIES})

