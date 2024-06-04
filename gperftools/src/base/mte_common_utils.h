/* https://elixir.bootlin.com/linux/latest/source/tools/testing/selftests/arm64/mte/mte_common_util.h */
/* SPDX-License-Identifier: GPL-2.0 */
/* Copyright (C) 2020 ARM Limited */

#ifndef _MTE_COMMON_UTIL_H
#define _MTE_COMMON_UTIL_H

#include "arm_instruction_set_select.h"
#if defined(MTE_ENABLED)

#include "mte_def.h"

namespace tcmalloc {

enum mte_mode {
	MTE_NONE_ERR,
	MTE_SYNC_ERR,
	MTE_ASYNC_ERR,
    MTE_ASYMM_ERR,
};

/* MTE utility functions */
void mte_switch_mode(enum mte_mode mte_option, unsigned long incl_mask);

}  // namespace tcmalloc

/* Assembly MTE utility functions */
#ifdef __cplusplus
extern "C" {
#endif

void *mte_insert_random_tag(void *ptr);
void *mte_insert_new_tag(void *ptr);
void *mte_get_tag_address(void *ptr);
void mte_set_tag_address_range(void *ptr, int range);	//stg
void mte_clear_tag_address_range(void *ptr, int range);	//stzg

// TagPool: x2 and x3 store the ptr and size arguments to save them from being destroyed
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

void mte_disable_pstate_tco(void);
void mte_enable_pstate_tco(void);
unsigned int mte_get_pstate_tco(void);
#ifdef __cplusplus
}
#endif

#else

/* On architectures that are not MTE_ENABLED, make these operations a no-op */
#define mte_get_tag_address(x)      (x)

#endif /* MTE_ENABLED */

#endif /* _MTE_COMMON_UTIL_H */
