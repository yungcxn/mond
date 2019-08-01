The Compiler
=======================
Merger
  reading .limp and .fimp and then copy content of one file into another
  from multiple .mon to .monm

Lexer
  lexical analysis with extra information to tokens of that .monm

Parser with semantic analysis
  from tokens to abstract syntax tree

Code-Generator
  from abstract syntax tree to LLVM-IR

llvm-link
  LLVM tool to link declared functions with foreign

llvm-opt
  LLVM tool to optimize linked .ll file

llvm-llc
  LLVM tool to compile .ll to an executable
