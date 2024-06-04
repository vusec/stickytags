// ---
// Author: Taddeus Kroes <t.kroes@vu.nl>

#ifdef MTE_ENABLED

#include <sys/mman.h>             // for mmap, mprotect, etc
#include <string.h>               // for strerror
#include <errno.h>                // for errno
#include <limits>                 // for numeric_limits
#include "config.h"
#include "base/basictypes.h"      // for PREDICT_FALSE
#include "internal_logging.h"     // for Log, kLog, kCrash, ASSERT
#include "span.h"                 // for Span
#include "static_vars.h"          // for Static
#include "thread_cache.h"         // for ThreadCache
#include "heap-redzone-check.h"   // for tcmalloc_*
#include "libredzones-helpers.h"  // for register_uffd_pages

// Uncomment to log slow path redzone checks on the heap.
//#define RZ_DEBUG_VERBOSE

using tcmalloc::kLog;
using tcmalloc::kCrash;
using tcmalloc::Span;
using tcmalloc::Static;
using tcmalloc::ThreadCache;

#define llog(level, ...) Log((level), __FILE__, __LINE__, __VA_ARGS__)
#define lperror(msg) llog(kCrash, msg ":", strerror(errno))

#ifdef RZ_DEBUG
# define ldbg(...) llog(kLog, __VA_ARGS__)
#else
# define ldbg(...)
#endif

static inline Span *get_span(void *ptr) {
  const uintptr_t addr = reinterpret_cast<uintptr_t>(ptr);
  const PageID p = addr >> kPageShift;
  return Static::pageheap()->GetDescriptor(p);
}

__attribute__((always_inline))
static bool contains_redzone(void *ptr, const Span *span, size_t naccess) {
#ifdef RZ_DEBUG_VERBOSE
  ldbg("check", naccess, "bytes for redzones at", ptr);
#endif

  ASSERT(span);
  const uintptr_t span_start = span->start << kPageShift;
  const size_t span_offset = reinterpret_cast<uintptr_t>(ptr) - span_start;

  // Large objects have the redzone at the end of the last page.
  if (PREDICT_FALSE(span->sizeclass == 0)) {
    const size_t span_size = span->length << kPageShift;
    return span_offset < kLargeRedzoneSize || span_offset + naccess > span_size - kLargeRedzoneSize;
  }

  if (span->is_stack) {
    // Note: this computation does not work for guard pages, but we don't care
    // about redzone checks there because accesses will segfault anyway.
    const intptr_t span_end = (span->start + span->length) << kPageShift;
    const intptr_t stack_end = span_end - span->stack_guard;
    const ptrdiff_t stack_offset = stack_end - (intptr_t)ptr;
    const size_t objsize = span->stack_objsize;
    const size_t object_offset = stack_offset % objsize;
    return object_offset - naccess <= 0 || object_offset > objsize + kRedzoneSize;
  }

  // Small objects have a redzone at the start of each allocation unit.
  const size_t objsize = Static::sizemap()->class_to_size(span->sizeclass);
  const size_t object_offset = span_offset % objsize;
  return object_offset < kRedzoneSize || object_offset + naccess > objsize;
}

extern "C" {
  // Slow path check for heap.
  enum redzone_result tcmalloc_is_redzone(void *ptr, size_t naccess) {
    const Span *span = get_span(ptr);
    if (span == NULL)
      return redzone_unknown;
    return contains_redzone(ptr, span, naccess) ? redzone_yes : redzone_no;
  }

  // Expose emergency malloc to runtime library.
  void tcmalloc_set_emergency_malloc(bool enable) {
        fprintf(stderr, "WOOOOOOOOOOOOOOOOO we are in tcmalloc!\n");
/*
    if (enable) {
      ldbg("uffd: enabling emergency malloc");
      ThreadCache::SetUseEmergencyMalloc();
    } else {
      ldbg("uffd: disabling emergency malloc");
      ThreadCache::ResetUseEmergencyMalloc();
    }
*/
  }
}

#ifdef RZ_REUSE
static inline void register_uffd_span(const Span *span) {
  register_uffd_pages(reinterpret_cast<void*>(span->start << kPageShift),
                      span->length << kPageShift);
}

static inline void unregister_uffd_span(const Span *span) {
  unregister_uffd_pages(reinterpret_cast<void*>(span->start << kPageShift),
                        span->length << kPageShift);
}
#endif // RZ_REUSE

extern "C" void *tcmalloc_alloc_stack(size_t size, size_t guard, size_t sizeclass) {
  ldbg("allocate stack of", size, "bytes with size class", sizeclass);
  ASSERT(size > 0);
  ASSERT(sizeclass > kRedzoneSize);

  // Make sure the page heap is initialized.
  if (PREDICT_FALSE(!Static::IsInited()))
      ThreadCache::InitModule();

  // Allocate stack span.
  Span *span;
  {
    SpinLockHolder h(Static::pageheap_lock());
    span = Static::pageheap()->New(tcmalloc::pages(size + 2 * guard));
    ASSERT(span->location == Span::IN_USE);
    span->is_stack = 1;

    // Set nonzero sizeclass, we reserve zero for large heap allocations.
    span->sizeclass = 1;

    // Stack size classes may differ from the dynamically computed tcmalloc
    // sizeclasses so we cannot use the sizeclass ID's used by from
    // Static::sizemap. Instead we store the size class directly.
    if (sizeclass > std::numeric_limits<uint32_t>::max())
      llog(kCrash, "stack sizeclass too big for 32 bits:", sizeclass);
    span->stack_objsize = static_cast<uint32_t>(sizeclass);

    if (guard > std::numeric_limits<uint16_t>::max())
      llog(kCrash, "stack guard too big for 16 bits:", guard);
    span->stack_guard = static_cast<uint16_t>(guard);

    ASSERT(span->stack_objsize == sizeclass);
    ASSERT(span->stack_guard == guard);
  }

#if defined(RZ_REUSE_STACK) && !defined(RZ_REUSE_HEAP)
  // If reuse is enabled for stack but not for heap, the pages are not
  // registered automatically by the page heap so we register them here.
  register_uffd_span(span);
#elif !defined(RZ_REUSE_STACK) && defined(RZ_REUSE_HEAP)
  // If reuse is enabled for heap but not for stack, the stack pages are
  // registered automatically by the page heap so we unregister them here.
  unregister_uffd_span(span);
#endif

  // Protect guard zones. It is up to the caller to make sure that the guard
  // zone size is a multiple of the system page size.
  char *start = reinterpret_cast<char*>(span->start << kPageShift);
  char *end = start + (span->length << kPageShift);
  if (guard > 0) {
    mprotect(start, guard, PROT_NONE);
    mprotect(end - guard, guard, PROT_NONE);
  }

  // Return the end of the valid memory region because the stack grow down.
  return end - guard;
}

extern "C" void tcmalloc_free_stack(void *stack) {
  // Find stack span.
  Span *span = get_span(stack);
  ASSERT(span->is_stack);
  ASSERT(span->sizeclass == 1);

  ldbg("free stack at", (void*)((span->start << kPageShift) + span->stack_guard),
       "with size class", span->stack_objsize);

  // Unprotect guard zones to allow span reuse.
  size_t guard = span->stack_guard;
  if (guard > 0) {
    char *start = reinterpret_cast<char*>(span->start << kPageShift);
    char *end = start + (span->length << kPageShift);
    mprotect(start, guard, PROT_READ | PROT_WRITE);
    mprotect(end - guard, guard, PROT_READ | PROT_WRITE);
  }

  // Reverse registration operations by tcmalloc_alloc_stack.
#if defined(RZ_REUSE_STACK) && !defined(RZ_REUSE_HEAP)
  unregister_uffd_span(span);
#elif !defined(RZ_REUSE_STACK) && defined(RZ_REUSE_HEAP)
  register_uffd_span(span);
#endif

  // Return span to page heap.
  {
    SpinLockHolder h(Static::pageheap_lock());
    DeleteAndUnmapSpan(span);
  }
}

#ifdef RZ_REUSE
#ifdef RZ_FILL

static char *mmapx(size_t size) {
  char *page = (char*)mmap(NULL, size, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS | MAP_POPULATE, -1, 0);
  if (PREDICT_FALSE(page == MAP_FAILED))
    lperror("mmap of zeropage failed");
  return page;
}

extern "C" void *tcmalloc_fill_redzones(void *start, size_t sysPageSize) {
  const Span *span = get_span(start);
  if (span == NULL)
    return NULL;

  const uintptr_t istart = reinterpret_cast<uintptr_t>(start);

  ASSERT((istart & (sysPageSize - 1)) == 0);
  ASSERT(sysPageSize > 0);
  ASSERT(span->location == Span::IN_USE);

  ldbg("uffd:   span at", (void*)(span->start << kPageShift),
       "with length", span->length);

  static char *buf = mmapx(sysPageSize);
  memset(buf, 0, sysPageSize);

  if (span->sizeclass == 0) {
    // For large allocations, put the redzones at the start of the first page
    // and the end of the last page.
    // XXX: surround large allocations with guard pages instead?
    ASSERT(kLargeRedzoneSize <= sysPageSize);
    const uintptr_t span_start = span->start << kPageShift;
    const uintptr_t span_end = (span->start + span->length) << kPageShift;
    if (istart == span_start) {
      // lower bound redzone
      ldbg("uffd: initialize large redzone at start of large allocation at", start);
      memset(buf, kRedzoneValue, kLargeRedzoneSize);
    }
    else if (istart == span_end - sysPageSize) {
      // upper bound redzone
      ldbg("uffd: initialize large redzone at end of large allocation at", start);
      memset(buf + sysPageSize - kLargeRedzoneSize, kRedzoneValue, kLargeRedzoneSize);
    }
  } else {
    // For small allocations, fill all redzones of objects that are either fully
    // or partially in this page. Each slot starts with a redzone.
    size_t objsize;
    ssize_t lead_obj;

    ldbg("uffd: initialize redzones for page at", start);

    if (span->is_stack) {
      ASSERT(span->sizeclass == 1);
      objsize = static_cast<size_t>(span->stack_objsize);
      const uintptr_t span_end = (span->start + span->length) << kPageShift;
      const uintptr_t stack_start = span_end - span->stack_guard - kRedzoneSize;
      const ptrdiff_t stack_offset = stack_start - istart;
      lead_obj = stack_offset % objsize;
      ldbg("uffd:   stack page with object size", objsize, "lead", lead_obj);
    } else {
      objsize = Static::sizemap()->class_to_size(span->sizeclass);
      const uintptr_t span_start = span->start << kPageShift;
      const ptrdiff_t span_offset = istart - span_start;
      const size_t obj_before_pfpage = span_offset % objsize;
      lead_obj = objsize - obj_before_pfpage;
      ldbg("uffd:   heap page with object size", objsize, "lead", lead_obj);
    }

    const ssize_t lead_rz = lead_obj - (objsize - kRedzoneSize);
    const char *end = buf + sysPageSize;
    char *next_rz = buf + lead_obj;

    if (lead_rz > 0) {
#ifdef RZ_DEBUG_VERBOSE
      ldbg("uffd:   fill", lead_rz, "redzone bytes at offset 0");
#endif
      memset(buf, kRedzoneValue, lead_rz);
    }

    while (next_rz <= end - kRedzoneSize) {
#ifdef RZ_DEBUG_VERBOSE
      ldbg("uffd:   fill", kRedzoneSize, "redzone bytes at offset", next_rz - buf);
#endif
      memset(next_rz, kRedzoneValue, kRedzoneSize);
      next_rz += objsize;
    }

    const ptrdiff_t tail_rz = end - next_rz;
    if (tail_rz > 0) {
#ifdef RZ_DEBUG_VERBOSE
      ldbg("uffd:   fill", tail_rz, "redzone bytes at offset", next_rz - buf);
#endif
      memset(next_rz, kRedzoneValue, tail_rz);
    }
  }

  return buf;
}

#endif // RZ_FILL
#endif // RZ_REUSE

#endif
