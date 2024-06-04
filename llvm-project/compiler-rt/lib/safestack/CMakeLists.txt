add_compiler_rt_component(safestack)

set(SAFESTACK_SOURCES
  safestack.cpp
  )

include_directories(..)

set(SAFESTACK_CFLAGS ${SANITIZER_COMMON_CFLAGS})

foreach(arch ${SAFESTACK_SUPPORTED_ARCH})
  add_compiler_rt_runtime(clang_rt.safestack
    STATIC
    ARCHS ${arch}
    SOURCES ${SAFESTACK_SOURCES}
            $<TARGET_OBJECTS:RTInterception.${arch}>
    CFLAGS ${SAFESTACK_CFLAGS}
    PARENT_TARGET safestack)
    add_sanitizer_rt_symbols(clang_rt.safestack
      ARCHS ${arch}
      EXTRA safestack.syms.extra)
    add_dependencies(safestack
      clang_rt.safestack-${arch}-symbols)
endforeach()
