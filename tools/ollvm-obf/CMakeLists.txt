add_executable(ollvm-obf
  main.cpp
  Flattening.cpp
  Substitution.cpp
  StringEncryption.cpp
  ConstantUnfolding.cpp
  Vectorize.cpp
)

target_link_libraries(ollvm-obf PRIVATE ${OMILL_LLVM_LIBS})

if(NOT MSVC)
  target_compile_options(ollvm-obf PRIVATE -fno-rtti)
endif()
