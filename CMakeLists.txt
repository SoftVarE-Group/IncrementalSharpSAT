cmake_minimum_required (VERSION 2.8)
project (SHARPSAT) 

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -std=c++11 -Wall -fPIC")

set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -std=c++11 -O3 -DNDEBUG -Wall -fPIC")

set(CMAKE_CXX_FLAGS_PROFILING "${CMAKE_CXX_FLAGS_PROFILING} -std=c++11 -O3 -g -DNDEBUG -Wall -fPIC")

IF(UNIX)
  IF(APPLE)
    include_directories(/opt/local/include)
  ELSE(APPLE)
    
    
  ENDIF(APPLE)
ELSE(UNIX)

ENDIF(UNIX)


find_library(GMP_LIB gmp)
find_library(GMPXX_LIB gmpxx)


add_subdirectory(src)

add_executable (incSharpSAT src/main.cpp)
target_link_libraries (incSharpSAT libsharpSAT ${GMP_LIB} ${GMPXX_LIB})

# Tests
add_subdirectory(tests)

enable_testing()

find_package(GTest REQUIRED)

add_executable(solver_tests tests/solver_tests.cpp)
target_link_libraries(solver_tests GTest::gtest_main libsharpSAT ${GMP_LIB} ${GMPXX_LIB})

include(GoogleTest)
gtest_discover_tests(solver_tests)

# Benchmarks
add_subdirectory(benchmarks/src)

add_library(incSharpSAT_benchmark_interface SHARED benchmarks/src/incSharpSATBenchmarkInterface.cpp)
target_link_libraries(incSharpSAT_benchmark_interface libsharpSAT ${GMP_LIB} ${GMPXX_LIB})
