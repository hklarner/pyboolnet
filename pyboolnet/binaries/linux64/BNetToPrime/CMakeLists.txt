cmake_minimum_required (VERSION 2.4)
PROJECT(BNetToPrime)

# Target
FILE(GLOB MY_HEADERS ${BNetToPrime_SOURCE_DIR}/source/*.h)
ADD_EXECUTABLE(BNetToPrime main.cpp ${MY_HEADERS})


