// -*- Mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*-
// Copyright (c) 2008, Google Inc.
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
//     * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above
// copyright notice, this list of conditions and the following disclaimer
// in the documentation and/or other materials provided with the
// distribution.
//     * Neither the name of Google Inc. nor the names of its
// contributors may be used to endorse or promote products derived from
// this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// ---
// Author: Sanjay Ghemawat <opensource@google.com>

#include <config.h>
#ifdef HAVE_INTTYPES_H
#include <inttypes.h>                   // for PRIuPTR
#endif
#include <errno.h>                      // for ENOMEM, errno
#include <gperftools/malloc_extension.h>      // for MallocRange, etc
#include "base/basictypes.h"
#include "base/commandlineflags.h"
#include "internal_logging.h"  // for ASSERT, TCMalloc_Printer, etc
#include "page_heap_allocator.h"  // for PageHeapAllocator
#include "static_vars.h"       // for Static
#include "system-alloc.h"      // for TCMalloc_SystemAlloc, etc

// Uffd
#include <linux/userfaultfd.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <pthread.h>
#include <poll.h>
#include <fcntl.h>
#include "thread_cache.h"
#include <math.h>
#include <sys/mman.h>

DEFINE_double(tcmalloc_release_rate,
              EnvToDouble("TCMALLOC_RELEASE_RATE", 1.0),
              "Rate at which we release unused memory to the system.  "
              "Zero means we never release memory back to the system.  "
              "Increase this flag to return memory faster; decrease it "
              "to return memory slower.  Reasonable rates are in the "
              "range [0,10]");

DEFINE_int64(tcmalloc_heap_limit_mb,
              EnvToInt("TCMALLOC_HEAP_LIMIT_MB", 0),
              "Limit total size of the process heap to the "
              "specified number of MiB. "
              "When we approach the limit the memory is released "
              "to the system more aggressively (more minor page faults). "
              "Zero means to allocate as long as system allows.");

namespace tcmalloc {

PageHeap::PageHeap()
    : pagemap_(MetaDataAlloc),
      scavenge_counter_(0),
      // Start scavenging at kMaxPages list
      release_index_(kMaxPages),
      aggressive_decommit_(false) {
  COMPILE_ASSERT(kClassSizesMax <= (1 << PageMapCache::kValuebits), valuebits);
  for (int i = 0; i < kMaxPages; i++) {
    DLL_Init(&free_[i].normal);
    DLL_Init(&free_[i].returned);
  }
}

#ifdef LARGE_OBJ_MAP
Span* PageHeap::SearchFreeAndLargeLists(Length n, bool is_large) {
#else
Span* PageHeap::SearchFreeAndLargeLists(Length n) {
#endif
  ASSERT(Check());
  ASSERT(n > 0);

#ifdef LARGE_OBJ_OPT //LARGE_OBJ_MAP
  if(!is_large)
#endif
    {
  // Find first size >= n that has a non-empty list
  for (Length s = n; s <= kMaxPages; s++) {
    Span* ll = &free_[s - 1].normal;
    // If we're lucky, ll is non-empty, meaning it has a suitable span.
    if (!DLL_IsEmpty(ll)) {
      ASSERT(ll->next->location == Span::ON_NORMAL_FREELIST);
      return Carve(ll->next, n);
    }
    // Alternatively, maybe there's a usable returned span.
    ll = &free_[s - 1].returned;
    if (!DLL_IsEmpty(ll)) {
      // We did not call EnsureLimit before, to avoid releasing the span
      // that will be taken immediately back.
      // Calling EnsureLimit here is not very expensive, as it fails only if
      // there is no more normal spans (and it fails efficiently)
      // or SystemRelease does not work (there is probably no returned spans).
      if (EnsureLimit(n)) {
        // ll may have became empty due to coalescing
        if (!DLL_IsEmpty(ll)) {
          ASSERT(ll->next->location == Span::ON_RETURNED_FREELIST);
          return Carve(ll->next, n);
        }
      }
    }
  }
    }

#ifdef LARGE_OBJ_MAP
  if(is_large){
    // No luck in free lists, our last chance is in a larger class.
    return AllocLarge(n);  // May be NULL
  }
  return NULL;
#else
  // No luck in free lists, our last chance is in a larger class.
  return AllocLarge(n);  // May be NULL
#endif
}

static const size_t kForcedCoalesceInterval = 128*1024*1024;
#ifdef POOL_USERFAULT
#ifdef LARGE_OBJ_MAP
Span* PageHeap::New(Length n, bool is_stack, bool is_large) {
#else
Span* PageHeap::New(Length n, bool is_stack) {
#endif
#else
Span* PageHeap::New(Length n) {
#endif
  ASSERT(Check());
  ASSERT(n > 0);
#ifdef LARGE_OBJ_MAP
  Span* result = SearchFreeAndLargeLists(n, is_large);
#else
  Span* result = SearchFreeAndLargeLists(n);
#endif

  //fprintf(stderr, "New(): is_large %d first result is %p\n", is_large, result);

  if (result != NULL) {
#ifdef LARGE_OBJ_MAP
    result->is_origin_large = is_large;
#endif
    return result;
  }

  if (stats_.free_bytes != 0 && stats_.unmapped_bytes != 0
      && stats_.free_bytes + stats_.unmapped_bytes >= stats_.system_bytes / 4
      && (stats_.system_bytes / kForcedCoalesceInterval
          != (stats_.system_bytes + (n << kPageShift)) / kForcedCoalesceInterval)) {
    // We're about to grow heap, but there are lots of free pages.
    // tcmalloc's design decision to keep unmapped and free spans
    // separately and never coalesce them means that sometimes there
    // can be free pages span of sufficient size, but it consists of
    // "segments" of different type so page heap search cannot find
    // it. In order to prevent growing heap and wasting memory in such
    // case we're going to unmap all free pages. So that all free
    // spans are maximally coalesced.
    //
    // We're also limiting 'rate' of going into this path to be at
    // most once per 128 megs of heap growth. Otherwise programs that
    // grow heap frequently (and that means by small amount) could be
    // penalized with higher count of minor page faults.
    //
    // See also large_heap_fragmentation_unittest.cc and
    // https://code.google.com/p/gperftools/issues/detail?id=368
    ReleaseAtLeastNPages(static_cast<Length>(0x7fffffff));

    // then try again. If we are forced to grow heap because of large
    // spans fragmentation and not because of problem described above,
    // then at the very least we've just unmapped free but
    // insufficiently big large spans back to OS. So in case of really
    // unlucky memory fragmentation we'll be consuming virtual address
    // space, but not real memory
#ifdef LARGE_OBJ_MAP
    result = SearchFreeAndLargeLists(n, is_large);
#else
    result = SearchFreeAndLargeLists(n);
#endif
    if (result != NULL) {
#ifdef LARGE_OBJ_MAP
        result->is_origin_large = is_large;
#endif
        return result;
    }
  }

  // Grow the heap and try again.
#ifdef POOL_USERFAULT
#ifdef LARGE_OBJ_MAP
  if (!GrowHeap(n, is_stack, is_large)) {
#else
  if (!GrowHeap(n, is_stack)) {
#endif
#else
  if (!GrowHeap(n)) {
#endif
    ASSERT(stats_.unmapped_bytes+ stats_.committed_bytes==stats_.system_bytes);
    ASSERT(Check());
    // underlying SysAllocator likely set ENOMEM but we can get here
    // due to EnsureLimit so we set it here too.
    //
    // Setting errno to ENOMEM here allows us to avoid dealing with it
    // in fast-path.
    errno = ENOMEM;
    return NULL;
  }

#ifdef LARGE_OBJ_MAP
  result = SearchFreeAndLargeLists(n, is_large);
  result->is_origin_large = is_large;
  //fprintf(stderr, "Found Result after GrowHeap: %p\n", result);
  return result;
#else
  return SearchFreeAndLargeLists(n);
#endif
}

Span* PageHeap::AllocLarge(Length n) {
  Span *best = NULL;
  Span *best_normal = NULL;

  // Create a Span to use as an upper bound.
  Span bound;
  bound.start = 0;
  bound.length = n;

  // First search the NORMAL spans..
  SpanSet::iterator place = large_normal_.upper_bound(SpanPtrWithLength(&bound));
  if (place != large_normal_.end()) {
    best = place->span;
    best_normal = best;
    ASSERT(best->location == Span::ON_NORMAL_FREELIST);
  }

  // Try to find better fit from RETURNED spans.
  place = large_returned_.upper_bound(SpanPtrWithLength(&bound));
  if (place != large_returned_.end()) {
    Span *c = place->span;
    ASSERT(c->location == Span::ON_RETURNED_FREELIST);
    if (best_normal == NULL
        || c->length < best->length
        || (c->length == best->length && c->start < best->start))
      best = place->span;
  }

  if (best == best_normal) {
    return best == NULL ? NULL : Carve(best, n);
  }

  // best comes from RETURNED set.

  if (EnsureLimit(n, false)) {
    return Carve(best, n);
  }

  if (EnsureLimit(n, true)) {
    // best could have been destroyed by coalescing.
    // best_normal is not a best-fit, and it could be destroyed as well.
    // We retry, the limit is already ensured:
    return AllocLarge(n);
  }

  // If best_normal existed, EnsureLimit would succeeded:
  ASSERT(best_normal == NULL);
  // We are not allowed to take best from returned list.
  return NULL;
}

Span* PageHeap::Split(Span* span, Length n) {
  ASSERT(0 < n);
  ASSERT(n < span->length);
  ASSERT(span->location == Span::IN_USE);
  ASSERT(span->sizeclass == 0);

  const int extra = span->length - n;
  Span* leftover = NewSpan(span->start + n, extra);
#ifdef LARGE_OBJ_MAP
  leftover->is_origin_large = span->is_origin_large;
#endif

  ASSERT(leftover->location == Span::IN_USE);
  RecordSpan(leftover);
#ifndef POOL_USERFAULT
  pagemap_.set(span->start + n - 1, span); // Update map from pageid to span
#endif
  span->length = n;

  return leftover;
}

void PageHeap::CommitSpan(Span* span) {
  ++stats_.commit_count;

  TCMalloc_SystemCommit(reinterpret_cast<void*>(span->start << kPageShift),
                        static_cast<size_t>(span->length << kPageShift));
  stats_.committed_bytes += span->length << kPageShift;
  stats_.total_commit_bytes += (span->length << kPageShift);
}

bool PageHeap::DecommitSpan(Span* span) {
  ++stats_.decommit_count;

  bool rv = TCMalloc_SystemRelease(reinterpret_cast<void*>(span->start << kPageShift),
                                   static_cast<size_t>(span->length << kPageShift));
  if (rv) {
    stats_.committed_bytes -= span->length << kPageShift;
    stats_.total_decommit_bytes += (span->length << kPageShift);
  }

  return rv;
}

Span* PageHeap::Carve(Span* span, Length n) {
  ASSERT(n > 0);
  ASSERT(span->location != Span::IN_USE);
  const int old_location = span->location;
  RemoveFromFreeList(span);
  span->location = Span::IN_USE;

  const int extra = span->length - n;
  ASSERT(extra >= 0);
  if (extra > 0) {
    Span* leftover = NewSpan(span->start + n, extra);
    leftover->location = old_location;
#ifdef LARGE_OBJ_MAP
    leftover->is_origin_large = span->is_origin_large;
#endif

    RecordSpan(leftover);

    // The previous span of |leftover| was just splitted -- no need to
    // coalesce them. The next span of |leftover| was not previously coalesced
    // with |span|, i.e. is NULL or has got location other than |old_location|.
#ifndef NDEBUG
    const PageID p = leftover->start;
    const Length len = leftover->length;
    Span* next = GetDescriptor(p+len);
    ASSERT (next == NULL ||
            next->location == Span::IN_USE ||
            next->location != leftover->location);
#endif

    PrependToFreeList(leftover);  // Skip coalescing - no candidates possible
    span->length = n;
#ifndef POOL_USERFAULT
    pagemap_.set(span->start + n - 1, span);
#endif
  }
  ASSERT(Check());
  if (old_location == Span::ON_RETURNED_FREELIST) {
    // We need to recommit this address space.
    CommitSpan(span);
  }
  ASSERT(span->location == Span::IN_USE);
  ASSERT(span->length == n);
  ASSERT(stats_.unmapped_bytes+ stats_.committed_bytes==stats_.system_bytes);
  return span;
}
#ifdef LARGE_OBJ_MAP
void PageHeap::Delete(Span* span, bool skip) {
#else
void PageHeap::Delete(Span* span) {
#endif
  ASSERT(Check());
  ASSERT(span->location == Span::IN_USE);
  ASSERT(span->length > 0);
  ASSERT(GetDescriptor(span->start) == span);
  ASSERT(GetDescriptor(span->start + span->length - 1) == span);
  const Length n = span->length;
  span->sizeclass = 0;
  span->sample = 0;
#ifdef POOL_USERFAULT
  if (span->is_stack) {
    span->is_stack = 0;
    span->stack_objsize = 0;
  }
#endif
  span->location = Span::ON_NORMAL_FREELIST;
#ifdef LARGE_OBJ_MAP
  MergeIntoFreeList(span, skip);  // Coalesces if possible
#else
  MergeIntoFreeList(span);  // Coalesces if possible
#endif
  IncrementalScavenge(n);
  ASSERT(stats_.unmapped_bytes+ stats_.committed_bytes==stats_.system_bytes);
  ASSERT(Check());
}

// Given span we're about to free and other span (still on free list),
// checks if 'other' span is mergable with 'span'. If it is, removes
// other span from free list, performs aggressive decommit if
// necessary and returns 'other' span. Otherwise 'other' span cannot
// be merged and is left untouched. In that case NULL is returned.
Span* PageHeap::CheckAndHandlePreMerge(Span* span, Span* other) {
  if (other == NULL) {
    return other;
  }
#ifdef LARGE_OBJ_MAP
  // dont merge regular size classes with large objs
  if(span->is_origin_large != other->is_origin_large){
    return NULL;
  }
#endif
  // if we're in aggressive decommit mode and span is decommitted,
  // then we try to decommit adjacent span.
  if (aggressive_decommit_ && other->location == Span::ON_NORMAL_FREELIST
      && span->location == Span::ON_RETURNED_FREELIST) {
    bool worked = DecommitSpan(other);
    if (!worked) {
      return NULL;
    }
  } else if (other->location != span->location) {
    return NULL;
  }

  RemoveFromFreeList(other);
  return other;
}
#ifdef LARGE_OBJ_MAP
void PageHeap::MergeIntoFreeList(Span* span, bool skip) {
#else
void PageHeap::MergeIntoFreeList(Span* span) {
#endif
  ASSERT(span->location != Span::IN_USE);

  // Coalesce -- we guarantee that "p" != 0, so no bounds checking
  // necessary.  We do not bother resetting the stale pagemap
  // entries for the pieces we are merging together because we only
  // care about the pagemap entries for the boundaries.
  //
  // Note: depending on aggressive_decommit_ mode we allow only
  // similar spans to be coalesced.
  //
  // The following applies if aggressive_decommit_ is enabled:
  //
  // TODO(jar): "Always decommit" causes some extra calls to commit when we are
  // called in GrowHeap() during an allocation :-/.  We need to eval the cost of
  // that oscillation, and possibly do something to reduce it.

  // TODO(jar): We need a better strategy for deciding to commit, or decommit,
  // based on memory usage and free heap sizes.

  const PageID p = span->start;
  const Length n = span->length;

  if (aggressive_decommit_ && span->location == Span::ON_NORMAL_FREELIST) {
    if (DecommitSpan(span)) {
      span->location = Span::ON_RETURNED_FREELIST;
    }
  }
#ifdef LARGE_OBJ_MAP
  if(!skip)
#endif
    {
      Span* prev = CheckAndHandlePreMerge(span, GetDescriptor(p-1));
      if (prev != NULL) {
        // Merge preceding span into this span
        ASSERT(prev->start + prev->length == p);
        const Length len = prev->length;
        DeleteSpan(prev);
        span->start -= len;
        span->length += len;
    #ifdef POOL_USERFAULT
        for (Length i = 0; i < len; i++) {
          pagemap_.set(span->start + i, span);
        }
    #else
        pagemap_.set(span->start, span);
    #endif
      }
      Span* next = CheckAndHandlePreMerge(span, GetDescriptor(p+n));
      if (next != NULL) {
        // Merge next span into this span
        ASSERT(next->start == p+n);
        const Length len = next->length;
        DeleteSpan(next);
        span->length += len;
    #ifdef POOL_USERFAULT
        for (Length i = span->length - len; i < span->length; i++) {
          pagemap_.set(span->start + i, span);
        }
    #else
        pagemap_.set(span->start + span->length - 1, span);
    #endif
      }
  }

  PrependToFreeList(span);
}

void PageHeap::PrependToFreeList(Span* span) {
  ASSERT(span->location != Span::IN_USE);
  if (span->location == Span::ON_NORMAL_FREELIST)
    stats_.free_bytes += (span->length << kPageShift);
  else
    stats_.unmapped_bytes += (span->length << kPageShift);

#ifdef LARGE_OBJ_MAP
  if (span->length > kMaxPages || span->is_origin_large) {
#else
  if (span->length > kMaxPages) {
#endif
    SpanSet *set = &large_normal_;
    if (span->location == Span::ON_RETURNED_FREELIST)
      set = &large_returned_;
    std::pair<SpanSet::iterator, bool> p =
        set->insert(SpanPtrWithLength(span));
    ASSERT(p.second); // We never have duplicates since span->start is unique.
    span->SetSpanSetIterator(p.first);
    return;
  }

  SpanList* list = &free_[span->length - 1];
  if (span->location == Span::ON_NORMAL_FREELIST) {
    DLL_Prepend(&list->normal, span);
  } else {
    DLL_Prepend(&list->returned, span);
  }
}

void PageHeap::RemoveFromFreeList(Span* span) {
  ASSERT(span->location != Span::IN_USE);
  if (span->location == Span::ON_NORMAL_FREELIST) {
    stats_.free_bytes -= (span->length << kPageShift);
  } else {
    stats_.unmapped_bytes -= (span->length << kPageShift);
  }
#ifdef LARGE_OBJ_MAP
  if (span->length > kMaxPages || span->is_origin_large) {
#else
  if (span->length > kMaxPages) {
#endif
    SpanSet *set = &large_normal_;
    if (span->location == Span::ON_RETURNED_FREELIST)
      set = &large_returned_;
    SpanSet::iterator iter = span->ExtractSpanSetIterator();
    ASSERT(iter->span == span);
    ASSERT(set->find(SpanPtrWithLength(span)) == iter);
    set->erase(iter);
  } else {
    DLL_Remove(span);
  }
}

void PageHeap::IncrementalScavenge(Length n) {
  // Fast path; not yet time to release memory
  scavenge_counter_ -= n;
  if (scavenge_counter_ >= 0) return;  // Not yet time to scavenge

  const double rate = FLAGS_tcmalloc_release_rate;
  if (rate <= 1e-6) {
    // Tiny release rate means that releasing is disabled.
    scavenge_counter_ = kDefaultReleaseDelay;
    return;
  }

  ++stats_.scavenge_count;

  Length released_pages = ReleaseAtLeastNPages(1);

  if (released_pages == 0) {
    // Nothing to scavenge, delay for a while.
    scavenge_counter_ = kDefaultReleaseDelay;
  } else {
    // Compute how long to wait until we return memory.
    // FLAGS_tcmalloc_release_rate==1 means wait for 1000 pages
    // after releasing one page.
    const double mult = 1000.0 / rate;
    double wait = mult * static_cast<double>(released_pages);
    if (wait > kMaxReleaseDelay) {
      // Avoid overflow and bound to reasonable range.
      wait = kMaxReleaseDelay;
    }
    scavenge_counter_ = static_cast<int64_t>(wait);
  }
}

Length PageHeap::ReleaseSpan(Span* s) {
  ASSERT(s->location == Span::ON_NORMAL_FREELIST);

  if (DecommitSpan(s)) {
    RemoveFromFreeList(s);
    const Length n = s->length;
    s->location = Span::ON_RETURNED_FREELIST;
    MergeIntoFreeList(s);  // Coalesces if possible.
    return n;
  }

  return 0;
}

Length PageHeap::ReleaseAtLeastNPages(Length num_pages) {
  Length released_pages = 0;

  // Round robin through the lists of free spans, releasing a
  // span from each list.  Stop after releasing at least num_pages
  // or when there is nothing more to release.
  while (released_pages < num_pages && stats_.free_bytes > 0) {
    for (int i = 0; i < kMaxPages+1 && released_pages < num_pages;
         i++, release_index_++) {
      Span *s;
      if (release_index_ > kMaxPages) release_index_ = 0;

      if (release_index_ == kMaxPages) {
        if (large_normal_.empty()) {
          continue;
        }
        s = (large_normal_.begin())->span;
      } else {
        SpanList* slist = &free_[release_index_];
        if (DLL_IsEmpty(&slist->normal)) {
          continue;
        }
        s = slist->normal.prev;
      }
      // TODO(todd) if the remaining number of pages to release
      // is significantly smaller than s->length, and s is on the
      // large freelist, should we carve s instead of releasing?
      // the whole thing?
      Length released_len = ReleaseSpan(s);
      // Some systems do not support release
      if (released_len == 0) return released_pages;
      released_pages += released_len;
    }
  }
  return released_pages;
}

bool PageHeap::EnsureLimit(Length n, bool withRelease)
{
  Length limit = (FLAGS_tcmalloc_heap_limit_mb*1024*1024) >> kPageShift;
  if (limit == 0) return true; //there is no limit

  // We do not use stats_.system_bytes because it does not take
  // MetaDataAllocs into account.
  Length takenPages = TCMalloc_SystemTaken >> kPageShift;
  //XXX takenPages may be slightly bigger than limit for two reasons:
  // MetaDataAllocs ignore the limit (it is not easy to handle
  //  out of memory there)
  // sys_alloc may round allocation up to huge page size,
  //  although smaller limit was ensured

  ASSERT(takenPages >= stats_.unmapped_bytes >> kPageShift);
  takenPages -= stats_.unmapped_bytes >> kPageShift;

  if (takenPages + n > limit && withRelease) {
    takenPages -= ReleaseAtLeastNPages(takenPages + n - limit);
  }

  return takenPages + n <= limit;
}

void PageHeap::RegisterSizeClass(Span* span, uint32 sc) {
  // Associate span object with all interior pages as well
  ASSERT(span->location == Span::IN_USE);
  ASSERT(GetDescriptor(span->start) == span);
  ASSERT(GetDescriptor(span->start+span->length-1) == span);
  span->sizeclass = sc;
  //fprintf(stderr, "Registered Class: span->start %p sizeclass %lu\n", span->start << kPageShift, sc);
#ifndef POOL_USERFAULT
  // This is already done in RecordSpan.
  for (Length i = 1; i < span->length-1; i++) {
    pagemap_.set(span->start+i, span);
  }
#endif
}

void PageHeap::GetSmallSpanStats(SmallSpanStats* result) {
  for (int i = 0; i < kMaxPages; i++) {
    result->normal_length[i] = DLL_Length(&free_[i].normal);
    result->returned_length[i] = DLL_Length(&free_[i].returned);
  }
}

void PageHeap::GetLargeSpanStats(LargeSpanStats* result) {
  result->spans = 0;
  result->normal_pages = 0;
  result->returned_pages = 0;
  for (SpanSet::iterator it = large_normal_.begin(); it != large_normal_.end(); ++it) {
    result->normal_pages += it->length;
    result->spans++;
  }
  for (SpanSet::iterator it = large_returned_.begin(); it != large_returned_.end(); ++it) {
    result->returned_pages += it->length;
    result->spans++;
  }
}

bool PageHeap::GetNextRange(PageID start, base::MallocRange* r) {
  Span* span = reinterpret_cast<Span*>(pagemap_.Next(start));
  if (span == NULL) {
    return false;
  }
  r->address = span->start << kPageShift;
  r->length = span->length << kPageShift;
  r->fraction = 0;
  switch (span->location) {
    case Span::IN_USE:
      r->type = base::MallocRange::INUSE;
      r->fraction = 1;
      if (span->sizeclass > 0) {
        // Only some of the objects in this span may be in use.
        const size_t osize = Static::sizemap()->class_to_size(span->sizeclass);
        r->fraction = (1.0 * osize * span->refcount) / r->length;
      }
      break;
    case Span::ON_NORMAL_FREELIST:
      r->type = base::MallocRange::FREE;
      break;
    case Span::ON_RETURNED_FREELIST:
      r->type = base::MallocRange::UNMAPPED;
      break;
    default:
      r->type = base::MallocRange::UNKNOWN;
      break;
  }
  return true;
}

static void RecordGrowth(size_t growth) {
  StackTrace* t = Static::stacktrace_allocator()->New();
  t->depth = GetStackTrace(t->stack, kMaxStackDepth-1, 3);
  t->size = growth;
  t->stack[kMaxStackDepth-1] = reinterpret_cast<void*>(Static::growth_stacks());
  Static::set_growth_stacks(t);
}

#ifdef POOL_USERFAULT
// MTE userfaultfd
long page_size = 0;
int uffd = -1;
struct uffdio_register uffdio_register;
pthread_t uffd_thread;
struct params {
    int uffd;
    long page_size;
};
#define TIMEOUT (-1)
#ifdef TAGPOOL_HEAP_ONLY
int tagpool_enable = 1;
#else
int tagpool_enable = 0;
#endif

// temporarily store targets to
// avoid really early alloc freeze
#define MAX_CNT_STORE 50
uint64_t store_start[MAX_CNT_STORE];
uint64_t store_size[MAX_CNT_STORE];
uint64_t store_cnt = 0;


#ifdef COUNT_PAGEFAULTS
uint64_t heap_pf = 0;
uint64_t stack_pf = 0;

static char *program_path() {
    char *path = (char*) malloc(256);
    if (path != NULL) {
        if (readlink("/proc/self/exe", path, 256) == -1) {
            free(path);
            path = NULL;
        }
    }
    return path;
}

__attribute__((destructor)) static void on_destroy_dump_pf() {
    FILE* pf = fopen("/tmp/pagefaults.txt", "a");
    if(pf != NULL){
        //char *ppath = program_path();
        fprintf(pf, "%lu,%lu\n", stack_pf, heap_pf);
        fflush(pf);
        fclose(pf);
    }
}
#endif

static inline Span *get_span(uintptr_t addr) {
  const PageID p = addr >> kPageShift;
  return Static::pageheap()->GetDescriptor(p);
}

void apply_tags_to_page(uintptr_t addr) {
    Span* span = get_span(addr);
    if(span == NULL) {
      //fprintf(stderr, "Span Not Found! addr %p\n", (void*)addr);
      return;
    }

    // get the span start address. for the stack, span->start is the bottom (which is 16MB aligned)
    char *start = reinterpret_cast<char*>(span->start << kPageShift);
    uint64_t addr_delta = addr - (uintptr_t)start;
    //fprintf(stderr, "PageFault at %p from span %p has distance %lu is_stack: %d\n", addr, start, addr_delta, span->is_stack);

    // for the stack, we can assume the size classes are multiples of 2
    if(span->is_stack){
        size_t obj_size = span->stack_objsize;
        // i.e., we can perform N obj jumps from the start of the span to this faulting addr.
        // Optimize: this is equivalent to addr_delta >> bits(obj_size)
        size_t jumps = addr_delta / obj_size; // this is a valid integer division (N*page_size / (multiple-of-2))
        // if page_size / obj_size >= 16 then this tag result is always zero. could optimize.
        uint8_t tag = jumps % 16;

        //fprintf(stderr, "Stack PageFault at %p from span %p distance %lu obj_size %lu jumps %lu tag %lu\n", addr, start, addr_delta, obj_size, jumps, tag);
        //fflush(stderr);

        uint64_t base = addr;

        for(size_t offset = 0; offset < page_size; offset += obj_size){
            // fprintf(stderr, "offset %ld, page_size %ld\n", offset, page_size);
            addr = (uintptr_t) MT_SET_TAG(base+offset, (uintptr_t)tag);

#ifdef MTE_HARDWARE
            if(obj_size > page_size){
                // if the object is bigger than a page, we just fill the entire page
                // this will also end the loop because offset > page_size next iter.
                mte_set_tag_address_range((void*)addr, page_size);
            }
            else{
                mte_set_tag_address_range((void*)addr, obj_size);
            }
#else
            if(obj_size > page_size){
                MTE_SET_TAG_INLINE(addr, (uint64_t)page_size); // tag in blocks of size class
            } else {
                MTE_SET_TAG_INLINE(addr, (uint64_t)obj_size); // tag in blocks of size class
            }
#endif


            //fprintf(stderr, "tagging addr %p with tag %x (size class %d)\n", addr, tag, obj_size);
            tag = ((tag+1) & 15); // == (tag+1) % 16
        }

#ifdef COUNT_PAGEFAULTS
        stack_pf++;
#endif
    }

    // for the heap, we do not
#ifndef TAGPOOL_STACK_ONLY
    else{
        if (span->sizeclass > 0){
          size_t obj_size = Static::sizemap()->class_to_size(span->sizeclass);

          size_t jumps = addr_delta / obj_size; // potentially does not divide well
          //fprintf(stderr, "heap addr %p addr_delta %lu obj_size %lu jumps %lu div %lu\n", addr, addr_delta, obj_size, jumps, addr_delta/obj_size);
          //  fflush(stderr);

          // e.g. 16384 / 80 = 204.8 jumps
          // meaning we have distance 204 + an offset

          // Calculate the remaining bytes that need to be tagged in this page
          size_t part_of_obj = (addr_delta % obj_size);// % page_size; // e.g. (16384 % 80) = 64, and (4096 % 73728) = 4096

          uint8_t tag = jumps % 16;
          uint64_t base = addr;
          size_t offset = 0;

          //fprintf(stderr, "PF %p start %p obj_size %lu jumps %lu part_of_obj %lu tag %lu\n", addr, start, obj_size, jumps, part_of_obj, tag);
          //fflush(stderr);

          if(part_of_obj != 0){ // size class not a multiple-of-2, a part of the object was already filled
              offset = obj_size - part_of_obj; // e.g. 80 - 64 = 16
              //fprintf(stderr, "offset %lu starting from PF addr %p\n", offset, addr);
              //fflush(stderr);
              addr = (uintptr_t) MT_SET_TAG(base, (uintptr_t)tag);
              if(offset > page_size) offset = page_size;
#ifdef MTE_HARDWARE
              mte_set_tag_address_range((void*)addr, offset);
#else
              MTE_SET_TAG_INLINE(addr, (uint64_t)offset); // offset = remainder to fill
#endif
              //fprintf(stderr, "1 tagging addr %p with tag %x (part_of_obj offset %lu)\n", addr, tag, offset);
              tag = ((tag+1) & 15); // == (tag+1) % 16  -- only move tag to the next _after_ tagging the old remaining part_of_obj from prev page
          }

          // now we can start filling the page with multiples of obj_size
          for(; offset < page_size; offset += obj_size){
              // fprintf(stderr, "offset %ld, page_size %ld\n", offset, page_size);
              addr = (uintptr_t) MT_SET_TAG(base+offset, (uintptr_t)tag);
              if(offset + obj_size > page_size){
                  size_t rem_size = (uint64_t)obj_size - ((offset + obj_size) - page_size);
#ifdef MTE_HARDWARE
                  mte_set_tag_address_range((void*)addr, rem_size);
#else
                  MTE_SET_TAG_INLINE(addr, rem_size);
#endif
                  //fprintf(stderr, "2 tagging addr %p with tag %x (REM SIZE %lu)\n", addr, tag, rem_size);
              }
              else
              {
//                  fprintf(stderr, "PF %p start %p obj_size %lu jumps %lu part_of_obj %lu tag %lu pagesize %lu pageshift %lu\n", MT_CLEAR_TAG(addr), start, obj_size, jumps, part_of_obj, tag, kPageSize, kPageShift);
//                  fflush(stderr);
#ifdef MTE_HARDWARE
                  mte_set_tag_address_range((void*)addr, obj_size);
#else
                  MTE_SET_TAG_INLINE(addr, (uint64_t)obj_size); // tag in blocks of size class
#endif
                  //fprintf(stderr, "3 tagging addr %p with tag %x (size class %d)\n", addr, tag, obj_size);
              }
              tag = ((tag+1) & 15); // == (tag+1) % 16
          }
        }
        else{
            // sizeclass == 0, meaning its a large heap allocation
            // size is bigger than kMaxSize (262144 bytes (262kB))
            // the size of the object is equal to the size of the span
            // have overhead tagging the entire page with a static tag
            // needs guard pages
            addr = (uintptr_t) MT_SET_TAG(addr, (uintptr_t)LARGE_TAG);
#ifdef MTE_HARDWARE
            mte_set_tag_address_range((void*)addr, page_size);
#else
            MTE_SET_TAG_INLINE(addr, page_size);
#endif
        }
#ifdef COUNT_PAGEFAULTS
        heap_pf++;
#endif
    }
#endif
}


static void *tagpool_uffd_handler(void *arg) {
    struct params *p = (struct params*)arg;
    unsigned long long page_size = p->page_size;
    int fd = p->uffd;

    //fprintf(stderr, "Handler thread launched: fd %d page %llu\n", fd, page_size);

    for (;;) {
        struct uffd_msg msg;

        struct pollfd pollfd = { .fd = p->uffd, .events = POLLIN };

        //fprintf(stderr, "polling on fd: %d\n", p->uffd);

        // wait for a userfaultfd event to occur
        int pollres = poll(&pollfd, 1, TIMEOUT);

        if(pollres < 0)
            exit(1);

        int readres = read(fd, &msg, sizeof(msg));
        if (readres == -1) {
            fprintf(stderr, "read error: fd %d readres %d msg %p size %lu\n", p->uffd, readres, &msg, sizeof(msg));
            fflush(stderr);
            if (errno == EAGAIN)
                continue;
            perror("read/userfaultfd");
            //exit(1);
            continue;
        }

        //fprintf(stderr, "********************* TC Faulting Page: %p\n", (void*)msg.arg.pagefault.address);

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

void init_uffd(){
    page_size = 4096; //16384; //get_page_size();
    // open the userfault fd
    uffd = syscall(__NR_userfaultfd, O_CLOEXEC | O_NONBLOCK);
    if (uffd == -1) {
        perror("syscall/userfaultfd");
        exit(1);
    }

    //fprintf(stderr, "TcMalloc set up userfaultfd: %d\n", uffd);
    // ENABLE_EMERGENCY_MALLOC
    ThreadCache::SetUseEmergencyMalloc();
    struct params *p = (struct params*)malloc(sizeof(struct params));
    //fprintf(stderr, "Allocated: %p\n", &p);
    p->uffd = uffd;
    p->page_size = page_size;
    pthread_create(&uffd_thread, NULL, tagpool_uffd_handler, p);
    ThreadCache::ResetUseEmergencyMalloc();

    // enable for api version and check features
    struct uffdio_api uffdio_api;
    uffdio_api.api = UFFD_API;
    uffdio_api.features = 0;
    if (ioctl(uffd, UFFDIO_API, &uffdio_api) == -1) {
        perror("ioctl/uffdio_api");
        exit(1);
    }

    if (uffdio_api.api != UFFD_API) {
        fprintf(stderr, "unsupported userfaultfd api\n");
        exit(1);
    }
}

void register_uffd_pages(uintptr_t start, size_t len) {
    if (uffd == -1 && tagpool_enable){
        init_uffd();
#ifdef S22_BUG_WORKAROUND
#ifndef TAGPOOL_STACK_ONLY
        // do not register the first allocation, its dlsym() from SafeStack using malloc
        return;
#endif
#endif
    }

    if(!tagpool_enable) {
        store_start[store_cnt] = start;
        store_size[store_cnt] = len;
        store_cnt++;
        if(store_cnt >= MAX_CNT_STORE){
            perror("max store count exceeded!!");
            exit(1);
        }
        return;
    }

    // register the pages in the region for missing callbacks
    size_t div = len % page_size;
    // if the length is not 16K page aligned (or 4K), cut down back to alignment
    if(div != 0){
        if(len > div){
            len -= div;
        }
        else{
            return;
        }
    }
    div = start % page_size;
    if(div != 0){
      if(start > div){
        start -= div;
      }
      else{
        return;
      }
    }

    uffdio_register.range.start = start;
    uffdio_register.range.len = len;
    // fprintf(stderr, "len %lu div %lu\n", len, len % page_size);
    //fprintf(stderr, "Heap Register Range: %llx to %llx\n", uffdio_register.range.start, uffdio_register.range.start+uffdio_register.range.len);
    //fflush(stderr);
    uffdio_register.mode = UFFDIO_REGISTER_MODE_MISSING;
    if (ioctl(uffd, UFFDIO_REGISTER, &uffdio_register) == -1) {
        fprintf(stderr, "uffd %d start %p len %d\n", uffd, (void*)uffdio_register.range.start, (int)uffdio_register.range.len);
        perror("ioctl/uffdio_register");
        exit(1);
    }
}

extern "C" void *tagpool_get_handler() {
    return (void*)tagpool_uffd_handler;
}

extern "C" void tagpool_enable_uffd() {
    tagpool_enable = 1;
#ifndef TAGPOOL_DISABLE_UFFD
    for(uint64_t i = 0; i < store_cnt; i++){
        register_uffd_pages(store_start[i], store_size[i]);
    }
#endif
}

extern "C" void *tagpool_alloc_stack(size_t size, size_t sizeclass) {
  // Make sure the page heap is initialized.
  if (PREDICT_FALSE(!Static::IsInited())){
      ThreadCache::InitModule();
    }
  // Allocate stack span.
  Span *span;
  {
    SpinLockHolder h(Static::pageheap_lock());
#ifdef LARGE_OBJ_MAP
    span = Static::pageheap()->New(tcmalloc::pages(size), true, true); // is_stack = true! is_large = true!
#else
    span = Static::pageheap()->New(tcmalloc::pages(size), true); // is_stack = true!
#endif
    ASSERT(span->location == Span::IN_USE);
    span->is_stack = 1;

    // Set nonzero sizeclass, we reserve zero for large heap allocations.
    span->sizeclass = 1;

    // Stack size classes may differ from the dynamically computed tcmalloc
    // sizeclasses so we cannot use the sizeclass ID's used by from
    // Static::sizemap. Instead we store the size class directly.
    span->stack_objsize = static_cast<uint32_t>(sizeclass);

    ASSERT(span->stack_objsize == sizeclass);
  }

  size_t span_len = span->length << kPageShift;
  char *start = reinterpret_cast<char*>(span->start << kPageShift);
  char *end = start + (span_len);

#if defined(LARGE_OBJ_OPT) || defined(TAGPOOL_STACK_ONLY)
  // by default, span gets registered to uffd by GrowHeap()
  // but now, since the large stack allocation gets carved to fit the stack,
  // we only mark the exact stack area as uffd to avoid large objs faulting
#ifndef TAGPOOL_DISABLE_UFFD
  register_uffd_pages((uintptr_t)start, span_len);
  if (mprotect((void*)start, span_len, PROT_READ | PROT_WRITE | PROT_MTE)) {
    perror("mprotect() failed");
  }
#endif
#endif

  //fprintf(stderr, "tagpool_alloc_stack result: %p to %p\n", (void*)start, (void*)end );
  return end;
}
#endif

#ifdef POOL_USERFAULT
#ifdef LARGE_OBJ_MAP
bool PageHeap::GrowHeap(Length n, bool is_stack, bool is_large) {
#else
bool PageHeap::GrowHeap(Length n, bool is_stack) {
#endif
#else
bool PageHeap::GrowHeap(Length n) {
#endif
  ASSERT(kMaxPages >= kMinSystemAlloc);
  if (n > kMaxValidPages) return false;
  Length ask = (n>kMinSystemAlloc) ? n : static_cast<Length>(kMinSystemAlloc);
  size_t actual_size;
  void* ptr = NULL;

  size_t align = kPageSize;
#ifdef POOL_USERFAULT
  if(is_stack){
    // 16 MB alignment for size-classed stacks 
    // so that we can make assumptions about the distance to the stack top
    align = 1 << 24;
  }
#endif

  if (EnsureLimit(ask)) {
      ptr = TCMalloc_SystemAlloc(ask << kPageShift, &actual_size, align);
#if defined(POOL_USERFAULT) && !defined(TAGPOOL_STACK_ONLY)
#ifdef LARGE_OBJ_OPT
        // stacks are large, but they are registered in tagpool_alloc_stack
        if(!is_large)
#endif
        {
#ifndef TAGPOOL_DISABLE_UFFD
            register_uffd_pages((uintptr_t)ptr, actual_size);
#endif
        }
#endif
  }
  if (ptr == NULL) {
    if (n < ask) {
      // Try growing just "n" pages
      ask = n;
      if (EnsureLimit(ask)) {
        ptr = TCMalloc_SystemAlloc(ask << kPageShift, &actual_size, align);
#if defined(POOL_USERFAULT) && !defined(TAGPOOL_STACK_ONLY)
#ifdef LARGE_OBJ_OPT
        if(!is_large)
#endif
        {
#ifndef TAGPOOL_DISABLE_UFFD
            register_uffd_pages((uintptr_t)ptr, actual_size);
#endif
        }
#endif
      }
    }
    if (ptr == NULL) return false;
  }

#if defined(MTE_ENABLED) && defined(RANDOM_HEAP_TAGS)
    if (mprotect(ptr, actual_size, PROT_READ | PROT_WRITE | PROT_MTE)) {
        perror("mprotect() failed");
    }
#endif

#if defined(MTE_ENABLED) && defined(MTE_HARDWARE) && !defined(TAGPOOL_STACK_ONLY)
#ifdef LARGE_OBJ_OPT
    // stack is mprot in alloc_stack
    if(!is_large)
#endif
    {
        if (mprotect(ptr, actual_size, PROT_READ | PROT_WRITE | PROT_MTE)) {
            perror("mprotect() failed");
        }
    }
#endif

  ask = actual_size >> kPageShift;
  RecordGrowth(ask << kPageShift);

  ++stats_.reserve_count;
  ++stats_.commit_count;

  uint64_t old_system_bytes = stats_.system_bytes;
  stats_.system_bytes += (ask << kPageShift);
  stats_.committed_bytes += (ask << kPageShift);

  stats_.total_commit_bytes += (ask << kPageShift);
  stats_.total_reserve_bytes += (ask << kPageShift);

  const PageID p = reinterpret_cast<uintptr_t>(ptr) >> kPageShift;
  ASSERT(p > 0);

  // If we have already a lot of pages allocated, just pre allocate a bunch of
  // memory for the page map. This prevents fragmentation by pagemap metadata
  // when a program keeps allocating and freeing large blocks.

  if (old_system_bytes < kPageMapBigAllocationThreshold
      && stats_.system_bytes >= kPageMapBigAllocationThreshold) {
    pagemap_.PreallocateMoreMemory();
  }

  // Make sure pagemap_ has entries for all of the new pages.
  // Plus ensure one before and one after so coalescing code
  // does not need bounds-checking.
  if (pagemap_.Ensure(p-1, ask+2)) {
    // Pretend the new area is allocated and then Delete() it to cause
    // any necessary coalescing to occur.
    Span* span = NewSpan(p, ask);
    RecordSpan(span);
#ifdef LARGE_OBJ_MAP
    span->is_origin_large = is_large;
    Delete(span, true);
#else
    Delete(span);
#endif
    ASSERT(stats_.unmapped_bytes+ stats_.committed_bytes==stats_.system_bytes);
    ASSERT(Check());
    return true;
  } else {
    // We could not allocate memory within "pagemap_"
    // TODO: Once we can return memory to the system, return the new span
    return false;
  }
}

bool PageHeap::Check() {
  return true;
}

bool PageHeap::CheckExpensive() {
  bool result = Check();
  CheckSet(&large_normal_, kMaxPages + 1, Span::ON_NORMAL_FREELIST);
  CheckSet(&large_returned_, kMaxPages + 1, Span::ON_RETURNED_FREELIST);
  for (int s = 1; s <= kMaxPages; s++) {
    CheckList(&free_[s - 1].normal, s, s, Span::ON_NORMAL_FREELIST);
    CheckList(&free_[s - 1].returned, s, s, Span::ON_RETURNED_FREELIST);
  }
  return result;
}

bool PageHeap::CheckList(Span* list, Length min_pages, Length max_pages,
                         int freelist) {
  for (Span* s = list->next; s != list; s = s->next) {
    CHECK_CONDITION(s->location == freelist);  // NORMAL or RETURNED
    CHECK_CONDITION(s->length >= min_pages);
    CHECK_CONDITION(s->length <= max_pages);
    CHECK_CONDITION(GetDescriptor(s->start) == s);
    CHECK_CONDITION(GetDescriptor(s->start+s->length-1) == s);
  }
  return true;
}

bool PageHeap::CheckSet(SpanSet* spanset, Length min_pages,int freelist) {
  for (SpanSet::iterator it = spanset->begin(); it != spanset->end(); ++it) {
    Span* s = it->span;
    CHECK_CONDITION(s->length == it->length);
    CHECK_CONDITION(s->location == freelist);  // NORMAL or RETURNED
    CHECK_CONDITION(s->length >= min_pages);
    CHECK_CONDITION(GetDescriptor(s->start) == s);
    CHECK_CONDITION(GetDescriptor(s->start+s->length-1) == s);
  }
  return true;
}

}  // namespace tcmalloc
