// https://elixir.bootlin.com/linux/latest/source/tools/testing/selftests/arm64/mte/mte_common_util.c
// SPDX-License-Identifier: GPL-2.0
// Copyright (C) 2020 ARM Limited

#include "arm_instruction_set_select.h"
#include "mte_common_utils.h"

#if defined(MTE_ENABLED) && defined(MTE_HARDWARE)

#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

#include <linux/auxvec.h>
#include <sys/auxv.h>
#include <sys/mman.h>
#include <sys/prctl.h>

#include <asm/hwcap.h>
#include "internal_logging.h"

namespace tcmalloc {

void mte_switch_mode(mte_mode mte_option, unsigned long incl_mask)
{
	unsigned long en = 0;
	ASSERT(getauxval(AT_HWCAP2) & HWCAP2_MTE);	//MTE features unavailable otherwise

	switch (mte_option) {
	case MTE_NONE_ERR:
	case MTE_SYNC_ERR:
	case MTE_ASYNC_ERR:
    case MTE_ASYMM_ERR:
		break;
	default:
	    ASSERT(false);
	}
	ASSERT((incl_mask & ~MT_INCLUDE_TAG_MASK) == 0); //invalid mask otherwise

	en = PR_TAGGED_ADDR_ENABLE;
	switch (mte_option) {
	case MTE_SYNC_ERR:
		en |= PR_MTE_TCF_SYNC;
		break;
	case MTE_ASYNC_ERR:
		en |= PR_MTE_TCF_ASYNC;
		break;
    case MTE_ASYMM_ERR:
        en |= PR_MTE_TCF_SYNC | PR_MTE_TCF_ASYNC;
		break;
	case MTE_NONE_ERR:
		en |= PR_MTE_TCF_NONE;
		break;
	default:
	    ASSERT(false);
	}

	/* en structure:
	 * 3 LSBits indicate the mode
	 * Next, 16 bits indicate which tags are allowed?
	*/
	en |= (incl_mask << PR_MTE_TAG_SHIFT);

	//For some reason, the Samsung S22 does not like at all when we tell it what mode to use.
	//So we explicitly ignore this value
	en = PR_TAGGED_ADDR_ENABLE | (incl_mask << PR_MTE_TAG_SHIFT);

	/* Enable address tagging ABI, mte error reporting mode and tag inclusion mask. */
	if (prctl(PR_SET_TAGGED_ADDR_CTRL, en, 0, 0, 0) != 0) {
    	Log(kCrash, __FILE__, __LINE__, "FAIL:prctl PR_SET_TAGGED_ADDR_CTRL for mte mode");
	} else {
#ifndef NDEBUG
		Log(kLog, __FILE__, __LINE__, "Successfully enabled MTE");
#endif
	}
}

}  // namespace tcmalloc

#elif defined(MTE_ENABLED)

void tcmalloc::mte_switch_mode(enum tcmalloc::mte_mode mte_option, unsigned long incl_mask) { }

#else

#define mte_switch_mode(mte_option, incl_mask)

#endif
