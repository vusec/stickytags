//===-- safestack.cpp -----------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the runtime support for the safe stack protection
// mechanism. The runtime manages allocation/deallocation of the unsafe stack
// for the main thread, as well as all pthreads that are created/destroyed
// during program execution.
//
//===----------------------------------------------------------------------===//

#include "safestack_platform.h"
#include "safestack_util.h"
#include <errno.h>
#include <sys/resource.h>
#include <assert.h>
#include <stdlib.h>
#include <linux/userfaultfd.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <pthread.h>
#include <poll.h>
#include <fcntl.h>
#include <malloc.h> // memalign
#include <sys/prctl.h>
#include <dlfcn.h>
#include "interception/interception.h"

// #include "/home/debian/tagpool/gperftools/src/tagpool.h"

#define ALLOK(x) malloc(x)

typedef void* (*proto_tagpool_get_handler)();
// void* tagpool_get_handler()
proto_tagpool_get_handler tagpool_get_handler;
void* tagpool_handler = NULL;

typedef void* (*proto_tagpool_alloc_stack)(size_t size, size_t sizeclass);
// void* tagpool_alloc_stack(size_t size, size_t sizeclass);
proto_tagpool_alloc_stack tagpool_alloc_stack = NULL;;

typedef void (*proto_tagpool_enable_uffd)(void);
proto_tagpool_enable_uffd tagpool_enable_uffd = NULL;

#define NOINSTRUMENT(name) __noinstrument_##name
#define NOINSTRUMENT_PREFIX "__noinstrument_"

#define create_unsafe_stacks    NOINSTRUMENT(create_unsafe_stacks)
#define destroy_unsafe_stacks   NOINSTRUMENT(destroy_unsafe_stacks)
#define thread_start            NOINSTRUMENT(thread_start)
#define thread_cleanup_key      NOINSTRUMENT(thread_cleanup_key)
#define thread_cleanup_handler  NOINSTRUMENT(thread_cleanup_handler)

#define dyn_alloc         NOINSTRUMENT(dyn_alloc)
#define dyn_free          NOINSTRUMENT(dyn_free)
#define dyn_free_optional NOINSTRUMENT(dyn_free_optional)

#define MTE_SET_TAG_INLINE(ptr, size)     asm volatile ( \
        "mov x2, %0\n" \
        "mov x3, %1\n" \
        "mov x17, %0\n" \
        "cbz %1, 2f\n" \
   "1:\n" \
        "mov x16, %0\n" \
        "lsr x16, x16, #56\n" \
        "and x16, x16, #0xFUL\n" \
        "strb w16, [x17, #0x0]\n" \
        "add %0, %0, #16\n" \
        "sub %1, %1, #16\n" \
        "add x17, x17, 1\n" \
        "cbnz    %1, 1b\n" \
   "2:\n" \
       "mov %0, x2\n" \
       "mov %1, x3\n" \
    ::"r"(ptr), "r"(size):"x16","x17","x2","x3","memory")

#define MT_TAG_SHIFT        56
#define MT_SET_TAG(x, y)    ( (void*)((uintptr_t)(x) | ((y) << MT_TAG_SHIFT)) )

using namespace safestack;

// TODO: To make accessing the unsafe stack pointer faster, we plan to
// eventually store it directly in the thread control block data structure on
// platforms where this structure is pointed to by %fs or %gs. This is exactly
// the same mechanism as currently being used by the traditional stack
// protector pass to store the stack guard (see getStackCookieLocation()
// function above). Doing so requires changing the tcbhead_t struct in glibc
// on Linux and tcb struct in libc on FreeBSD.
//
// For now, store it in a thread-local variable.
// extern "C" {
// __attribute__((visibility("default"))) __thread void *__safestack_unsafe_stack_ptr = nullptr;
// }

extern __thread void *__sizedstack_ptrs[0];
extern size_t __sizedstack_sizeclasses[0];
extern size_t __sizedstack_count;

// stack spans
typedef struct sized_stack {
  uintptr_t stack_bottom;
  size_t stack_size;
  size_t stack_size_class;
  struct sized_stack* next;
} sized_stack_t;

sized_stack_t* stack_head = NULL;

// extern int test_function_tagpool(int);

namespace {

// TODO: The runtime library does not currently protect the safe stack beyond
// relying on the system-enforced ASLR. The protection of the (safe) stack can
// be provided by three alternative features:
//
// 1) Protection via hardware segmentation on x86-32 and some x86-64
// architectures: the (safe) stack segment (implicitly accessed via the %ss
// segment register) can be separated from the data segment (implicitly
// accessed via the %ds segment register). Dereferencing a pointer to the safe
// segment would result in a segmentation fault.
//
// 2) Protection via software fault isolation: memory writes that are not meant
// to access the safe stack can be prevented from doing so through runtime
// instrumentation. One way to do it is to allocate the safe stack(s) in the
// upper half of the userspace and bitmask the corresponding upper bit of the
// memory addresses of memory writes that are not meant to access the safe
// stack.
//
// 3) Protection via information hiding on 64 bit architectures: the location
// of the safe stack(s) can be randomized through secure mechanisms, and the
// leakage of the stack pointer can be prevented. Currently, libc can leak the
// stack pointer in several ways (e.g. in longjmp, signal handling, user-level
// context switching related functions, etc.). These can be fixed in libc and
// in other low-level libraries, by either eliminating the escaping/dumping of
// the stack pointer (i.e., %rsp) when that's possible, or by using
// encryption/PTR_MANGLE (XOR-ing the dumped stack pointer with another secret
// we control and protect better, as is already done for setjmp in glibc.)
// Furthermore, a static machine code level verifier can be ran after code
// generation to make sure that the stack pointer is never written to memory,
// or if it is, its written on the safe stack.
//
// Finally, while the Unsafe Stack pointer is currently stored in a thread
// local variable, with libc support it could be stored in the TCB (thread
// control block) as well, eliminating another level of indirection and making
// such accesses faster. Alternatively, dedicating a separate register for
// storing it would also be possible.

/// Minimum stack alignment for the unsafe stack.
const unsigned kStackAlign = 16;

/// Default size of the unsafe stack. This value is only used if the stack
/// size rlimit is set to infinity.
const unsigned kDefaultUnsafeStackSize = 0x2800000;
static const unsigned kMaxUnsafeStackSize = 0x10000000;
static const unsigned kMaxUnsafeGuardSize = 0x10000000;

long page_size = 0;
int uffd = -1;
struct uffdio_register uffdio_register;
pthread_t uffd_thread;

struct params {
    int uffd;
    long page_size;
};

/// Thread data for the cleanup handler
pthread_key_t thread_cleanup_key;

// Per-thread unsafe stack information. It's not frequently accessed, so there
// it can be kept out of the tcb in normal thread-local variables.
// __thread void *unsafe_stack_start = nullptr;
// __thread size_t unsafe_stack_size = 0;
// __thread size_t unsafe_stack_guard = 0;

static long get_page_size(void)
{
    long ret = sysconf(_SC_PAGESIZE);
    if (ret == -1) {
        perror("sysconf/pagesize");
        exit(1);
    }
    assert(ret > 0);
    return ret;
}

void add_stack_span(uintptr_t stack_bottom, uintptr_t size, uintptr_t size_class)
{
    if(stack_head == NULL){
        stack_head = (sized_stack_t*) ALLOK(sizeof(sized_stack_t));
        stack_head->stack_bottom = stack_bottom;
        stack_head->stack_size_class = size_class;
        stack_head->stack_size = size;
        stack_head->next = NULL;
        return;
    }

    sized_stack_t* curr = stack_head;
    while(curr->next != NULL){
        curr = curr->next;
    }
    
    curr->next = (sized_stack_t*) ALLOK(sizeof(sized_stack_t));
    curr = curr->next;
    curr->stack_bottom = stack_bottom;
    curr->stack_size_class = size_class;
    curr->stack_size = size;
    curr->next = NULL;
}

int get_fault_addr_size_class(uintptr_t fault_addr)
{
    sized_stack_t* curr = stack_head;
    while(curr != NULL){
        if(fault_addr >= curr->stack_bottom && fault_addr < curr->stack_bottom + curr->stack_size){
            return curr->stack_size_class;
        }
        curr = curr->next;
    }
    return -1;
}

void apply_tags_to_page(uintptr_t addr)
{
    int sc = get_fault_addr_size_class(addr);
    // fprintf(stderr, "fault addr %p has size class: %d\n", addr, sc);

    uint8_t tag = rand() % 0x0F + 1;

    // e.g. size class 18432
    if(sc > page_size){
        // the whole page gets one tag
        // TODO: since the object spans multiple pages, they need to share the same tag
        addr = (uintptr_t) MT_SET_TAG(addr, (uintptr_t)tag);
        MTE_SET_TAG_INLINE(addr, (uint64_t)page_size);
        return;
    }

    // for the size classes that are not a power of two, we have to incorporate
    // the shift of the objects. 
    // e.g. size class 80 will start from the top of the stack and go down in jumps of 80 bytes
    // the bottom of this will not align at the page.

    uint64_t fit = page_size / sc; // e.g.: 16384 / 80 = 204.8 = 204
    uint64_t shift = page_size - (fit * sc); // e.g.: 16384 - (204 * 80) = 16384 - 16320 = 64
    
    uint64_t base = addr;
    for(long offset = shift; offset < page_size; offset += sc){
        // fprintf(stderr, "offset %ld, page_size %ld\n", offset, page_size);
        addr = (uintptr_t) MT_SET_TAG(base+offset, (uintptr_t)tag);
        MTE_SET_TAG_INLINE(addr, (uint64_t)sc); // tag in blocks of size class
        // fprintf(stderr, "tagging addr %p with tag %x (size class %d)\n", addr, tag, sc);
        tag = (tag + 1) & 0x0F;
    }

    // for(int i = 0; i < 10; i++){
    //      fprintf(stderr, "checking pre-init: %d %lx\n", i, ((uintptr_t*)(addr))[i]);
    //  }
}

#define TIMEOUT (-1)
static void *handler(void *arg)
{
    struct params *p = (struct params*)arg;
    unsigned long long page_size = p->page_size;
    int fd = p->uffd;

    // debug test
    // FILE* fp = fopen("/tmp/userfaults.txt", "a");

    for (;;) {
        struct uffd_msg msg;

        struct pollfd pollfd = { .fd = p->uffd, .events = POLLIN };

        // fprintf(stderr, "polling on fd: %d\n", p->uffd);

        // wait for a userfaultfd event to occur
        int pollres = poll(&pollfd, 1, TIMEOUT); // timeout -1

        if(pollres < 0)
            exit(1);

        int readres = read(fd, &msg, sizeof(msg));
        if (readres == -1) {
            //fprintf(stderr, "read error: fd %d readres %d msg %p\n", p->uffd, readres, &msg);
            if (errno == EAGAIN)
                continue;
            perror("read/userfaultfd");
            exit(1);
        }

      //  fprintf(stderr, "********************* Stack Faulting Page: %p\n", (void*)msg.arg.pagefault.address);
        // fprintf(fp, "Faulting Page: %p\n", (void*)msg.arg.pagefault.address);

        // handle the page fault by getting a zero page and setting the tags
        if (msg.event & UFFD_EVENT_PAGEFAULT) {
          
            uintptr_t addr = msg.arg.pagefault.address;
            struct uffdio_zeropage zero = {
                .range = { .start = addr, .len = page_size },
                .mode = UFFDIO_ZEROPAGE_MODE_DONTWAKE // dont wake up the thread yet, we need to apply tags.
            };

            if (ioctl(fd, UFFDIO_ZEROPAGE, &zero) == -1){
                perror("ioctl/zero");
                exit(1);
            }

            // here we apply MTE tags to the whole page in size class pattern
            apply_tags_to_page(addr);

            struct uffdio_range wake = {
               .start = addr,
               .len = page_size
           };

            // now wake up the thread
            if (ioctl(fd, UFFDIO_WAKE, &wake) == -1){
                perror("ioctl/wake");
                exit(1);
            }
        }
    }
    return NULL;
}

static void create_unsafe_stacks(size_t size, size_t guard) { 

  // if(uffd == -1){
  //     page_size = 16384; //get_page_size();

  //     // enable tagged pointers
  //     if (prctl(PR_SET_TAGGED_ADDR_CTRL, PR_TAGGED_ADDR_ENABLE, 0, 0, 0)) {
  //         perror("prctl() failed");
  //         abort();
  //     }

  //     // open the userfault fd
  //     uffd = syscall(__NR_userfaultfd, O_CLOEXEC | O_NONBLOCK);
  //     if (uffd == -1) {
  //         perror("syscall/userfaultfd");
  //         exit(1);
  //     }

  //     // fprintf(stderr, "Stack uffd syscall is %d\n", uffd);
  //     // fprintf(stderr, "Gotta call malloc..\n");
  //     struct params *p = (struct params*)ALLOK(sizeof(struct params));
  //     // fprintf(stderr, " DID I RETURN?\n");
  //     p->uffd = uffd;
  //     p->page_size = page_size;
  //     // fprintf(stderr, "Before Stack Thread 1\n");
  //     pthread_create(&uffd_thread, NULL, handler, p);
  //     // fprintf(stderr, "After Stack Thread 2\n");

  //     // enable for api version and check features
  //     struct uffdio_api uffdio_api;
  //     uffdio_api.api = UFFD_API;
  //     uffdio_api.features = 0;
  //     if (ioctl(uffd, UFFDIO_API, &uffdio_api) == -1) {
  //         perror("ioctl/uffdio_api");
  //         exit(1);
  //     }

  //     if (uffdio_api.api != UFFD_API) {
  //         fprintf(stderr, "unsupported userfaultfd api\n");
  //         exit(1);
  //     }
  // }

  for (size_t i = 0; i < __sizedstack_count; i++) {
      // keep this print in when testing security guarantees with MTE lol
      // fprintf(stderr, "TP: Creating Unsafe Stacks #%d (Size Class %lu, size %lu each)\n", i, __sizedstack_sizeclasses[i], size);
      // Allocate a stack, this returns a single span.
      // char *stack_ptr = tcmalloc_alloc_stack(size, guard, __sizedstack_sizeclasses[i]);

      // TODO: use guard areas?

      // The Problem is that TCMalloc is registering the heap address of our SafeStack allocations.

      // char *stack_ptr;
      // posix_memalign((void**)&stack_ptr, 16384, size);
      void* stack_ptr = tagpool_alloc_stack(size, __sizedstack_sizeclasses[i]);
      __sizedstack_ptrs[i] = stack_ptr;
      //fprintf(stderr, "Registered SizedStack via heap: %p sizeclass %lu size %lu\n", stack_ptr, __sizedstack_sizeclasses[i], size);

      // stack_ptr = (char*)ALLOK(size);
      
      //char *stack_ptr = (char*)malloc(size+guard);

      // printf("stack_ptr %d %p to %p (size class %lu)\n", i, stack_ptr, stack_ptr + (size+guard), __sizedstack_sizeclasses[i]);

      // Point the current stack pointer to the end of the allocated region to
      // make it grow down.
      // assert(((uintptr_t)stack_ptr & (kStackAlign - 1)) == 0);
      // assert(__sizedstack_ptrs[i] == NULL);

      // char *stack_top = stack_ptr + size;
      // __sizedstack_ptrs[i] = stack_top;

      // add_stack_span((uintptr_t)stack_ptr, size, __sizedstack_sizeclasses[i]);

      // // register the pages in the region for missing callbacks
      // uffdio_register.range.start = (__u64) stack_ptr;
      // uffdio_register.range.len = size;
      // // fprintf(stderr, "Stack Register Range: %llx to %llx\n", uffdio_register.range.start, uffdio_register.range.start+uffdio_register.range.len);

      // // test_function_tagpool(i);
      // uffdio_register.mode = UFFDIO_REGISTER_MODE_MISSING;
      // if (ioctl(uffd, UFFDIO_REGISTER, &uffdio_register) == -1) {
      //     fprintf(stderr, "uffd %d start %p len %d\n", uffd, uffdio_register.range.start, uffdio_register.range.len);
      //     perror("ioctl/uffdio_register");
      //     exit(1);
      // }

      // apply_tags_to_page((uintptr_t)(stack_top-page_size));

      // Apply tags to the first page of the stack allocation (the top page)
      // fprintf(stderr, "[SizedStack] tagging at stack_ptr = %p\n", stack_top-page_size);
      // stack_ptr = (char*) MT_SET_TAG(stack_top-page_size, (uintptr_t)0x8);
      // MTE_SET_TAG_INLINE(stack_ptr, (uint64_t)page_size);
    }
}

static void destroy_unsafe_stacks() {
  for (size_t i = 0; i < __sizedstack_count; i++) {
    // The stack pointer has probably changed but that's OK, tcmalloc_free_stack
    // accepts any pointer within the stack because it has a reverse mapping of
    // pages to spans.
    if (__sizedstack_ptrs[i] != NULL) {
      // tcmalloc_free_stack(__sizedstack_ptrs[i]);
      // TODO: this is not freeing the right address since its the top.
      // fprintf(stderr, "TagPool destroy at %p\n", __sizedstack_ptrs[i]);
      // free(__sizedstack_ptrs[i]);
      __sizedstack_ptrs[i] = NULL;
    }
  }
}

// inline void *unsafe_stack_alloc(size_t size, size_t guard) {
//   SFS_CHECK(size + guard >= size);
//   void *addr = Mmap(nullptr, size + guard, PROT_READ | PROT_WRITE,
//                     MAP_PRIVATE | MAP_ANON, -1, 0);
//   SFS_CHECK(MAP_FAILED != addr);
//   Mprotect(addr, guard, PROT_NONE);
//   return (char *)addr + guard;
// }

// inline void unsafe_stack_setup(void *start, size_t size, size_t guard) {
//   SFS_CHECK((char *)start + size >= (char *)start);
//   SFS_CHECK((char *)start + guard >= (char *)start);
//   void *stack_ptr = (char *)start + size;
//   SFS_CHECK((((size_t)stack_ptr) & (kStackAlign - 1)) == 0);

//   __safestack_unsafe_stack_ptr = stack_ptr;
//   unsafe_stack_start = start;
//   unsafe_stack_size = size;
//   unsafe_stack_guard = guard;
// }



/// Safe stack per-thread information passed to the thread_start function
struct tinfo {
  void *(*start_routine)(void *);
  void *start_routine_arg;

  void *unsafe_stack_start;
  size_t unsafe_stack_size;
  size_t unsafe_stack_guard;
};

/// Wrap the thread function in order to deallocate the unsafe stack when the
/// thread terminates by returning from its main function.
void *thread_start(void *arg) {
  struct tinfo *tinfo = (struct tinfo *)arg;

  void *(*start_routine)(void *) = tinfo->start_routine;
  void *start_routine_arg = tinfo->start_routine_arg;
  size_t size = tinfo->unsafe_stack_size;
  size_t guard = tinfo->unsafe_stack_guard;
  free(tinfo);
  //munmap(tinfo, sizeof (struct tinfo));

  //fprintf(stderr, "Thread is start: Routine %p, tagpool_handler: %p\n", (void*)start_routine, (void*)tagpool_handler);

  // Set up unsafe stacks for the new thread, but not if its the handler thread in TCMalloc
  if (start_routine != tagpool_handler){
    // fprintf(stderr,  "thread_start %p %p\n", start_routine, handler);
    create_unsafe_stacks(size, guard);
  }
  else{
    // fprintf(stderr, "[TagPool] skip safe stack for uffd thread\n");
  }

  // Setup the unsafe stack; this will destroy tinfo content
  // unsafe_stack_setup(tinfo->unsafe_stack_start, tinfo->unsafe_stack_size,
  //                    tinfo->unsafe_stack_guard);

  // Make sure out thread-specific destructor will be called
  pthread_setspecific(thread_cleanup_key, (void *)1);

  return start_routine(start_routine_arg);
}

// /// Linked list used to store exiting threads stack/thread information.
// struct thread_stack_ll {
//   struct thread_stack_ll *next;
//   void *stack_base;
//   size_t size;
//   pid_t pid;
//   ThreadId tid;
// };

// /// Linked list of unsafe stacks for threads that are exiting. We delay
// /// unmapping them until the thread exits.
// thread_stack_ll *thread_stacks = nullptr;
// pthread_mutex_t thread_stacks_mutex = PTHREAD_MUTEX_INITIALIZER;

/// Thread-specific data destructor. We want to free the unsafe stack only after
/// this thread is terminated. libc can call functions in safestack-instrumented
/// code (like free) after thread-specific data destructors have run.
void thread_cleanup_handler(void *_iter) {
  // SFS_CHECK(unsafe_stack_start != nullptr);
  // pthread_setspecific(thread_cleanup_key, NULL);

  // pthread_mutex_lock(&thread_stacks_mutex);
  // // Temporary list to hold the previous threads stacks so we don't hold the
  // // thread_stacks_mutex for long.
  // thread_stack_ll *temp_stacks = thread_stacks;
  // thread_stacks = nullptr;
  // pthread_mutex_unlock(&thread_stacks_mutex);

  // pid_t pid = getpid();
  // ThreadId tid = GetTid();

  // // Free stacks for dead threads
  // thread_stack_ll **stackp = &temp_stacks;
  // while (*stackp) {
  //   thread_stack_ll *stack = *stackp;
  //   if (stack->pid != pid ||
  //       (-1 == TgKill(stack->pid, stack->tid, 0) && errno == ESRCH)) {
  //     Munmap(stack->stack_base, stack->size);
  //     *stackp = stack->next;
  //     free(stack);
  //   } else
  //     stackp = &stack->next;
  // }

  // thread_stack_ll *cur_stack =
  //     (thread_stack_ll *)malloc(sizeof(thread_stack_ll));
  // cur_stack->stack_base = (char *)unsafe_stack_start - unsafe_stack_guard;
  // cur_stack->size = unsafe_stack_size + unsafe_stack_guard;
  // cur_stack->pid = pid;
  // cur_stack->tid = tid;

  // pthread_mutex_lock(&thread_stacks_mutex);
  // // Merge thread_stacks with the current thread's stack and any remaining
  // // temp_stacks
  // *stackp = thread_stacks;
  // cur_stack->next = temp_stacks;
  // thread_stacks = cur_stack;
  // pthread_mutex_unlock(&thread_stacks_mutex);

  // unsafe_stack_start = nullptr;
  size_t iter = (size_t)_iter;
  // fprintf(stderr, "[TagPool] in thread clean up handler iter %lu\n", iter);
  // TODO: this is never reached, usually, iter < 73
  if (iter < _SC_THREAD_DESTRUCTOR_ITERATIONS) { // PTHREAD_DESTRUCTOR_ITERATIONS
    pthread_setspecific(thread_cleanup_key, (void*)(iter + 1));
  } else {
    // This is the last iteration
    destroy_unsafe_stacks();
  }
}

void EnsureInterceptorsInitialized();

/// Intercept thread creation operation to allocate and setup the unsafe stack
INTERCEPTOR(int, pthread_create, pthread_t *thread,
            const pthread_attr_t *attr,
            void *(*start_routine)(void*), void *arg) {
  EnsureInterceptorsInitialized();
  size_t size = 0;
  size_t guard = 0;

  if (attr) {
    pthread_attr_getstacksize(attr, &size);
    pthread_attr_getguardsize(attr, &guard);
  } else {
    // get pthread default stack size
    pthread_attr_t tmpattr;
    pthread_attr_init(&tmpattr);
    pthread_attr_getstacksize(&tmpattr, &size);
    pthread_attr_getguardsize(&tmpattr, &guard);
    pthread_attr_destroy(&tmpattr);
  }

  SFS_CHECK(size);
  // size = RoundUpTo(size, kStackAlign);
  size = RoundUpTo(size, get_page_size());

  if (size > kMaxUnsafeStackSize)
    size = kMaxUnsafeStackSize;
  if (guard > kMaxUnsafeGuardSize)
    guard = kMaxUnsafeGuardSize;

  // Put tinfo at the end of the buffer. guard may be not page aligned.
  // If that is so then some bytes after addr can be mprotected.
  struct tinfo *tinfo = (struct tinfo*)ALLOK(sizeof (struct tinfo));
  tinfo->start_routine = start_routine;
  tinfo->start_routine_arg = arg;
  tinfo->unsafe_stack_size = size;
  tinfo->unsafe_stack_guard = guard;

  return REAL(pthread_create)(thread, attr, thread_start, tinfo);
}

pthread_mutex_t interceptor_init_mutex = PTHREAD_MUTEX_INITIALIZER;
bool interceptors_inited = false;

void EnsureInterceptorsInitialized() {
  MutexLock lock(interceptor_init_mutex);
  if (interceptors_inited)
    return;

  // Initialize pthread interceptors for thread allocation
  INTERCEPT_FUNCTION(pthread_create);

  interceptors_inited = true;
}

}  // namespace

/*
 * Helpers for turning dynamic allocas into heap allocations in LLVM pass.
 */

#define USED        __attribute__((used))
#define UNUSED      __attribute__((unused))

#define INLINE      __attribute__((always_inline))
#define NOINLINE    __attribute__((noinline))

#define likely(x)   __builtin_expect((x), 1)
#define unlikely(x) __builtin_expect((x), 0)

extern "C" __attribute__((malloc, alloc_size(1), alloc_align(2)))
INLINE USED void *dyn_alloc(size_t size, size_t alignment) {
    void *p = alignment ? aligned_alloc(alignment, size) : malloc(size);
    if (unlikely(p == NULL)) {
        perror("dyn_alloc: allocation failed");
        exit(1);
    }
    return p;
}

extern "C" __attribute__((nonnull))
INLINE USED void dyn_free(void *p) {
    free(p);
}

extern "C" INLINE USED void dyn_free_optional(void *p) {
    if (p != NULL)
        dyn_free(p);
}

extern "C" __attribute__((visibility("default")))
#if !SANITIZER_CAN_USE_PREINIT_ARRAY
// On ELF platforms, the constructor is invoked using .preinit_array (see below)
__attribute__((constructor(0)))
#endif
void __safestack_init() {
  // Determine the stack size for the main thread.
  size_t size = kDefaultUnsafeStackSize;
  size_t guard = 4096*4;

//  fprintf(stderr, "__safestack_init() entry\n");

  struct rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY)
    size = limit.rlim_cur;

  if (size > kMaxUnsafeStackSize)
    size = kMaxUnsafeStackSize;


  //fprintf(stderr, "right before dlsym\n");
  //fflush(stderr);

  tagpool_get_handler = (proto_tagpool_get_handler) dlsym(RTLD_NEXT, "tagpool_get_handler");

  //fprintf(stderr, "tagpool_get_handler @ %p\n", tagpool_get_handler);
  //fflush(stderr);
  tagpool_handler = tagpool_get_handler();

  tagpool_alloc_stack = (proto_tagpool_alloc_stack) dlsym(RTLD_NEXT, "tagpool_alloc_stack");
  //fprintf(stderr, "tagpool_alloc_stack @ %p\n", tagpool_alloc_stack);

  tagpool_enable_uffd = (proto_tagpool_enable_uffd) dlsym(RTLD_NEXT, "tagpool_enable_uffd");
  //fprintf(stderr, "tagpool_enable_uffd @ %p\n", tagpool_enable_uffd);


  if(tagpool_get_handler == NULL || tagpool_alloc_stack == NULL){
    fprintf(stderr, "[TagPool] ERROR: TCMalloc symbols not found!\n");
    abort();
  }

  // Allocate unsafe stack for main thread
  create_unsafe_stacks(size, guard);

  // Setup the cleanup handler
  pthread_key_create(&thread_cleanup_key, thread_cleanup_handler);

  // now call uffd enable
  tagpool_enable_uffd();
}

#if SANITIZER_CAN_USE_PREINIT_ARRAY
// On ELF platforms, run safestack initialization before any other constructors.
// On other platforms we use the constructor attribute to arrange to run our
// initialization early.
extern "C" {
__attribute__((section(".preinit_array"),
               used)) void (*__safestack_preinit)(void) = __safestack_init;
}
#endif

extern "C"
    __attribute__((visibility("default"))) void *__get_unsafe_stack_bottom() {
  return NULL;
}

extern "C"
    __attribute__((visibility("default"))) void *__get_unsafe_stack_top() {
  return NULL;
}

extern "C"
    __attribute__((visibility("default"))) void *__get_unsafe_stack_start() {
  return NULL;
}

extern "C"
    __attribute__((visibility("default"))) void *__get_unsafe_stack_ptr() {
  return NULL;
}

// get Sized Stack variables

extern "C"
    __attribute__((visibility("default"))) size_t __get_sized_stack_count() {
  return __sizedstack_count;
}

extern "C"
    __attribute__((visibility("default"))) size_t __get_sized_stack_class(size_t i) {
  return __sizedstack_sizeclasses[i];
}

extern "C"
    __attribute__((visibility("default"))) void* __get_sized_stack_ptr(size_t i) {
  return __sizedstack_ptrs[i];
}
