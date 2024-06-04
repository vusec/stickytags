#!/bin/bash

# Compile with Sticky Tags (compiler and allocator)
/root/tagpool/llvm-rel/bin/clang test.c -march=armv8.5-a+memtag -fsanitize=safe-stack -O2 -g -o test -flto=full -fuse-ld=lld -fno-builtin-malloc -L/root/tagpool/gperftools/install/lib/ -Wl,-rpath -Wl,/root/tagpool/gperftools/install/lib/ -ltcmalloc -lpthread

# Run the test program
./test 1 2 3 4
