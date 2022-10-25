// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */

/* CP: originally at linux/arch/arm64/kvm/hyp/nvhe/early_alloc.c */


/* CP: originally: #include <asm/kvm_pgtable.h> */

/* CP: originally: #include <nvhe/memory.h> */
#include "memory.h"

/* CP: adding */
#include "include/page-def.h"
#include "include/stddef.h"
#include "include/kvm_pgtable.h"

/* CP: originally: s64 hyp_physvirt_offset; */
unsigned long long hyp_physvirt_offset;
struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;

static unsigned long base;
static unsigned long end;
static unsigned long cur;

unsigned long hyp_early_alloc_nr_pages(void)
{
	return (cur - base) >> PAGE_SHIFT;
}

/* CP: originally: extern void clear_page(void *to); */
/* CP: instead, making up a definition of this */
void clear_page(void *to)
{                                                           /*RCIGNORE*/
  int i = 0;                                                /*RCIGNORE*/
  while(i < 4096)                                           /*RCIGNORE*/
  {                                                         /*RCIGNORE*/
    *((char *) to+i) = 0;                                   /*RCIGNORE*/
    i++;                                                    /*RCIGNORE*/
  };                                                        /*RCIGNORE*/
}                                                           /*RCIGNORE*/

void * hyp_early_alloc_page(void *arg)
{
	unsigned long ret = cur;

	cur += PAGE_SIZE;
	if (cur > end) {
		cur = ret;
		return NULL;
	}
	clear_page((void*)ret);

	return (void *)ret;
}

/* CP: We also include this variant of hyp_early_alloc_page that
   allocates a number of pages, as found in newer versions of
   early_alloc.c */
void *hyp_early_alloc_contig(unsigned int nr_pages)
{
	unsigned long ret = cur, i, p;

	if (!nr_pages)
		return NULL;

	cur += nr_pages << PAGE_SHIFT;
	if (cur > end) {
		cur = ret;
		return NULL;
	}

	for (i = 0; i < nr_pages; i++) {                    /*RCIGNORE*/
		p = ret + (i << PAGE_SHIFT);                /*RCIGNORE*/
		clear_page((void *)(p));                    /*RCIGNORE*/
	}                                                   /*RCIGNORE*/

	return (void *)ret;
}

void hyp_early_alloc_init(unsigned long virt, unsigned long size)
{
	base = virt;
	end = virt + size;
	cur = virt;

	hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
	hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
	hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;
}
