add_executable(omill-lift main.cpp)

target_link_libraries(omill-lift
  PRIVATE
    omill
    remill
    LLVMObject
    ${OMILL_LLVM_LIBS}
)

if(NOT MSVC)
  target_compile_options(omill-lift PRIVATE -fno-rtti)
endif()
