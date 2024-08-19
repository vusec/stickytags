# Sticky Tags
**StickyTags** is an efficient Arm MTE-based solution that mitigates bounded spatial memory errors 

**Paper**: https://www.vusec.net/projects/stickytags/ 

## Installing LLVM
```
mkdir llvm-rel
cd llvm-rel
cmake -DLLVM_ENABLE_PROJECTS="clang;lld" -DLLVM_ENABLE_RUNTIMES="compiler-rt" -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_ASSERTIONS=On -GNinja -DLLVM_PARALLEL_LINK_JOBS=1 -DLLVM_TARGETS_TO_BUILD="AArch64" -DCLANG_ENABLE_STATIC_ANALYZER=OFF -DCLANG_ENABLE_ARCMT=OFF ../llvm-project/llvm
ninja
```

## Installing TCMalloc
```
./configure --prefix=/root/stickytags-reproduce/gperftools/install --enable-emergency-malloc CC=/root/stickytags-reproduce/llvm-rel/bin/clang CFLAGS=-march=armv8.5-a+memtag CPPFLAGS=-march=armv8.5-a+memtag LDFLAGS=-march=armv8.5-a+memtag CXX=/root/stickytags-reproduce/llvm-rel/bin/clang++
make -j8
make install
```

## Testing
Make sure the system allows userfaultfd capability
```
sudo /sbin/sysctl -w vm.unprivileged_userfaultfd=1
```

Then run a test program:
```
cd test
./run.sh
./test 1 2 3 4
```
The `./test 1 2 3 4` command should cause a segmentation fault due to a buffer overflow
