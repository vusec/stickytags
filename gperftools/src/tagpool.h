#ifndef TCMALLOC_HEAP_REDZONE_CHECK_H_
#define TCMALLOC_HEAP_REDZONE_CHECK_H_

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

enum redzone_result { redzone_unknown = 0, redzone_yes, redzone_no };

// Slow path for single-byte redzone checks, implemented in system-alloc.c.
 __attribute__((noinline))
enum redzone_result tcmalloc_is_redzone(void *ptr, size_t naccess);

void tcmalloc_set_emergency_malloc(bool enable);

void *tcmalloc_alloc_stack(size_t size, size_t guard, size_t sizeclass);

void tcmalloc_free_stack(void *stack);

#if defined(RZ_REUSE) && defined(RZ_FILL)
void *tcmalloc_fill_redzones(void *start, size_t page_size);
#endif

#ifdef __cplusplus
}
#endif

#endif // TCMALLOC_HEAP_REDZONE_CHECK_H_
