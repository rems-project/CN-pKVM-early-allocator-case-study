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

/*@ requires base <= cur;
  @ assigns \nothing;
  @ ensures \result == (cur-base) >> 4096; @*/
unsigned long hyp_early_alloc_nr_pages(void)
{
	return (cur - base) >> PAGE_SHIFT;
}

/* CP: originally: extern void clear_page(void *to); */
/* CP: instead, making up a definition of this */
/*@ requires \valid(((char*)to)+(0..4095));
  @ assigns ((char*)to)[0..4095];
  @ ensures \forall integer k; 0 <= k && k < PAGE_SIZE ==> ((char*)to)[k] == 0; @*/
void clear_page(void *to) 
{
  int i = 0;
  /*@ loop assigns i, ((char*)to)[0..4095];
    @ loop invariant 0 <= i <= PAGE_SIZE;
    @ loop invariant \forall integer j; 0 <= j < i ==> ((char*)to)[j] == 0; @*/
  while(i < 4096) 
  {
    *((char *) to+i) = 0;
    i++;
  };
}

/*@ requires cur + 4096 <= end && \valid(((char*)0)+(cur..(end-1)));
  @ assigns cur, ((char*)cur)[0..4095], \result \from ((char*)cur)[0..4095];
  @ ensures cur == \old(cur) + 4096;
  @ ensures \forall integer k; 0 <= k && k < PAGE_SIZE ==> ((char*)\result)[k] == 0; @*/
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
/*@ requires nr_pages > 0 && (nr_pages*4096) < UINT_MAX;
  @ requires cur + 4096*nr_pages <= end;
  @ requires \valid(((char*)0)+(cur..(end-1)));
  @ assigns cur, ((char*)cur)[0..(4096*nr_pages-1)];
  @ assigns \result \from ((char*)cur)[0..(4096*nr_pages-1)];
  @ ensures cur <= end && cur == \old(cur) + 4096*nr_pages; 
  @ ensures \forall integer k; 0 <= k && k < nr_pages*4096 ==> ((char*)\result)[k] == 0; 
  @*/
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

        /*@ loop invariant nr_pages == \at(nr_pages, Pre);
            loop invariant cur == \at(cur, Pre) + nr_pages*4096;
            loop invariant end == \at(end, Pre) && ret == \at(cur, Pre);
            loop invariant 0 <= i <= nr_pages;
            loop invariant \forall integer k; 0 <= k && k < nr_pages*i ==> ((char*) ret)[k] == 0;
            loop assigns p, (((char*)ret)+i*4096)[0..4095]; @*/
	for (i = 0; i < nr_pages; i++) {
		p = ret + (i << PAGE_SHIFT);
		clear_page((void *)(p));
	}

	return (void *)ret;
}

/*@ requires virt + size < UINT_MAX;
    requires \valid(((char*)0)+(base..(end-1)));
    assigns base, cur, end, hyp_early_alloc_mm_ops;
    ensures base == virt && end == virt + size && cur == virt && cur <= end; @*/
void hyp_early_alloc_init(unsigned long virt, unsigned long size)
{
	base = virt;
	end = virt + size;
	cur = virt;

	hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
	hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
	hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;
}
