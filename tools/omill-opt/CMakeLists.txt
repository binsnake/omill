add_executable(omill-opt main.cpp)

target_link_libraries(omill-opt
  PRIVATE
    omill
    ${OMILL_LLVM_LIBS}
)

if(NOT MSVC)
  target_compile_options(omill-opt PRIVATE -fno-rtti)
endif()
