/* https://elixir.bootlin.com/linux/latest/source/tools/testing/selftests/arm64/mte/mte_helper.S */
/* SPDX-License-Identifier: GPL-2.0 */
/* Copyright (C) 2020 ARM Limited */

#include "arm_instruction_set_select.h"
#if defined(MTE_ENABLED)

/* Consult mte_def.h for the defines */
#define MT_GRANULE_SIZE     16
#define MT_PSTATE_TCO_SHIFT	25
#define MT_PSTATE_TCO_EN	1
#define MT_PSTATE_TCO_DIS	0
#define MT_TAG_SHIFT		56
#define MT_FREE_TAG			0x00
#define MT_TAG_MASK			0xF

#define ENTRY(name) \
	.globl name ;\
	.p2align 2;\
	.type name, %function ;\
name:

#define ENDPROC(name) \
	.size name, .-name ;

	.text

#if defined(MTE_HARDWARE)

/*
 * mte_insert_random_tag: Insert random tag and might be same as the source tag if
 *			  the source pointer has it.
 * Input:
 *		x0 - source pointer with a tag/no-tag
 * Return:
 *		x0 - pointer with random tag
 */
ENTRY(mte_insert_random_tag)
	irg	x0, x0, xzr
	ret
ENDPROC(mte_insert_random_tag)

/*
 * mte_insert_new_tag: Insert new tag and different from the source tag if
 *		       source pointer has it.
 * Input:
 *		x0 - source pointer with a tag/no-tag
 * Return:
 *		x0 - pointer with random tag
 */
ENTRY(mte_insert_new_tag)
	gmi	x1, x0, xzr
	irg	x0, x0, x1
	ret
ENDPROC(mte_insert_new_tag)

/*
 * mte_get_tag_address: Get the tag from given address.
 * Input:
 *		x0 - source pointer
 * Return:
 *		x0 - pointer with appended tag
 */
ENTRY(mte_get_tag_address)
	ldg	x0, [x0]
	ret
ENDPROC(mte_get_tag_address)

/*
 * mte_set_tag_address_range: Set the tag range from the given address
 * Input:
 *		x0 - source pointer with tag data
 *		x1 - range
 * Return:
 *		none
 */
ENTRY(mte_set_tag_address_range)
	cbz	x1, 2f
1:
	stg	x0, [x0, #0x0]
	add	x0, x0, #MT_GRANULE_SIZE
	sub	x1, x1, #MT_GRANULE_SIZE
	cbnz	x1, 1b
2:
	ret
ENDPROC(mte_set_tag_address_range)

/*
 * mt_clear_tag_address_range: Clear the tag range from the given address
 * Input:
 *		x0 - source pointer with tag data
 *		x1 - range
 * Return:
 *		none
 */
ENTRY(mte_clear_tag_address_range)
	cbz	x1, 2f
1:
	stzg	x0, [x0, #0x0]
	add	x0, x0, #MT_GRANULE_SIZE
	sub	x1, x1, #MT_GRANULE_SIZE
	cbnz	x1, 1b
2:
	ret
ENDPROC(mte_clear_tag_address_range)

/*
 * mte_enable_pstate_tco: Enable PSTATE.TCO (tag check override) field
 * Input:
 *		none
 * Return:
 *		none
 */
ENTRY(mte_enable_pstate_tco)
	msr	tco, #MT_PSTATE_TCO_EN
	ret
ENDPROC(mte_enable_pstate_tco)

/*
 * mte_disable_pstate_tco: Disable PSTATE.TCO (tag check override) field
 * Input:
 *		none
 * Return:
 *		none
 */
ENTRY(mte_disable_pstate_tco)
	msr	tco, #MT_PSTATE_TCO_DIS
	ret
ENDPROC(mte_disable_pstate_tco)

/*
 * mte_get_pstate_tco: Get PSTATE.TCO (tag check override) field
 * Input:
 *		none
 * Return:
 *		x0
 */
ENTRY(mte_get_pstate_tco)
	mrs	x0, tco
	ubfx	x0, x0, #MT_PSTATE_TCO_SHIFT, #1
	ret
ENDPROC(mte_get_pstate_tco)

#else

ENTRY(mte_insert_random_tag)
	ret
ENDPROC(mte_insert_random_tag)

ENTRY(mte_insert_new_tag)
	ret
ENDPROC(mte_insert_new_tag)

ENTRY(mte_get_tag_address)
	/* ldg	x0, [x0]
	Here is what happens with the above instruction.
	Given a pointer in x0, (can be either tagged or untagged - doesn't matter),
	you go to the "tag memory". You fetch the tag and you store it in the pointer itself.
	```
	address = calc_tag_memory_address(x0)
	tag = *(byte*)(address)
	x0  = x0 | (tag << MT_TAG_SHIFT)
	```

	Since we do not know how address is computed (It would make sense to use the physical address to compute this),
	as `address` we are going to use the pointer itself.
	To simulate the tag, we will use tag 0, which does not affect the execution.
	*/

	/* X16 and X17 are IP0 and IP1, intra-procedure-call temporary registers */
#ifdef MTE_ANALOGUES
	ldrb w16, [x0]
	mov x17, #MT_FREE_TAG
	lsl x17, x17, #MT_TAG_SHIFT
	orr x0,  x0,  x17
#endif
	ret
ENDPROC(mte_get_tag_address)

ENTRY(mte_set_tag_address_range)
lab_mte_set_tag_address_range:
#ifdef MTE_ANALOGUES
	mov x17, x0
	cbz	x1, 2f
1:
	/* stg	x0, [x0, #0x0]
	Here is what happens with the above instruction.
	You have your tagged pointer x0 (logical tag).
	That tag has to be stored in the "tag memory". So, you index the tag memory using
	the (untagged?) x0 to find the address where you are going to store the tag.
	Then you store the tag in that location.
	address  = calc_tag_memory_address(x0)	//address inside "tag_memory"
	tag      = (x0 >> MT_TAG_SHIFT) & 0x0F
	*(byte*)(address) = tag

	Since we do not know how address is computed (It would make sense to use the physical address to compute this),
	as `address` we are going to use the pointer itself.
	Also to better simulate the "tag_memory", we will write in conesquetive addresses
	*/
	mov x16, x0
	lsr x16, x16, #MT_TAG_SHIFT
	and x16, x16, #MT_TAG_MASK
	strb w16, [x17, #0x0]

	add	x0, x0, #MT_GRANULE_SIZE
	sub	x1, x1, #MT_GRANULE_SIZE
	add x17, x17, 1
	cbnz	x1, 1b
2:
#endif
	ret
ENDPROC(mte_set_tag_address_range)

ENTRY(mte_clear_tag_address_range)
	/* Same performance overhead as stg. Clearing the memory with stzg has no performance cost */
	b lab_mte_set_tag_address_range
ENDPROC(mte_clear_tag_address_range)

ENTRY(mte_enable_pstate_tco)
	ret
ENDPROC(mte_enable_pstate_tco)

ENTRY(mte_disable_pstate_tco)
	ret
ENDPROC(mte_disable_pstate_tco)

ENTRY(mte_get_pstate_tco)
	ret
ENDPROC(mte_get_pstate_tco)


#endif /* MTE_HARDWARE */

#endif /* MTE_ENABLED */
