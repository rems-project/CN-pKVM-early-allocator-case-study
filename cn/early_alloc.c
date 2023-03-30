// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */

/* CP: originally at linux/arch/arm64/kvm/hyp/nvhe/early_alloc.c */


/* CP: originally: #include <asm/kvm_pgtable.h> */

/* CP: originally: #include <nvhe/memory.h> */
#include "memory.h"
#include "cn_predicates.h"

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
/*@ accesses cur; base @*/
/*@ requires base <= cur @*/
/*@ ensures {cur}unchanged; {base}unchanged @*/
/*@ ensures return == (cur-base) / (power(2, 12)) @*/
{
	return (cur - base) >> PAGE_SHIFT;
}

/* CP: originally: extern void clear_page(void *to); */
/* CP: instead, making up a definition of this */
void clear_page(void *to) 
/*@ requires let to_i = (integer) to @*/
/*@ requires take B = each(integer j; to_i <= j && j < (to_i + 4096)){ Byte(((pointer) 0)+(j*1)) } @*/
/*@ ensures take B2 = each(integer j; to_i <= j && j < (to_i + 4096)){ ByteV(((pointer) 0)+(j*1), 0) } @*/
{
  int i = 0;
  while(i < 4096)
  /*@ inv 0 <= i; i <= 4096 @*/
  /*@ inv take Z = each(integer j; to_i <= j && j < (to_i + i)){ ByteV(((pointer) 0)+(j*1), 0) } @*/
  /*@ inv take BI = each(integer j; (to_i + i) <= j && j < (to_i + 4096)){ Byte(((pointer) 0)+(j*1)) } @*/
  /*@ inv {to}unchanged @*/
  {
    /*CN*/ /*@ unpack Byte ((pointer) ((integer) to+i)); @*/
    *((char *) to+i) = 0;
    /*CN*/ /*@ pack ByteV ((pointer) ((integer) to + i), 0); @*/
    i++;
  };
}

void * hyp_early_alloc_page(void *arg)
/*@ accesses cur; end @*/
/*@ requires cur + 4096 <= end @*/
/*@ requires take E = EarlyAlloc((pointer) cur, end) @*/
/*@ ensures take E2 = EarlyAlloc((pointer) cur, end) @*/
/*@ ensures take Z = each(integer j; ((integer) return) <= j && j < ((integer) return) + 4096){ Byte(((pointer) 0)+(j*1)) } @*/
/*@ ensures cur == {cur}@start + 4096; {end}unchanged @*/
{
        /*CN*/ /*@ unpack EarlyAlloc((pointer) cur, end); @*/
	unsigned long ret = cur;

	cur += PAGE_SIZE;
	if (cur > end) {
		cur = ret;
		return NULL;
	}
	/* clear_page((void*)ret); */

        /*CN*/ /*@ pack EarlyAlloc((pointer) cur, end); @*/
	return (void *)ret;
}

/* CP: We also include this variant of hyp_early_alloc_page that
   allocates a number of pages, as found in newer versions of
   early_alloc.c */
void *hyp_early_alloc_contig(unsigned int nr_pages)
/*@ accesses cur; end @*/
/*@ requires nr_pages > 0; (nr_pages*4096) < (power(2,32)) @*/
/*@ requires cur + (nr_pages*4096) <= end @*/
/*@ requires take E = EarlyAlloc((pointer) cur, end) @*/
/*@ ensures take E2 = EarlyAlloc((pointer) cur, end) @*/
/*@ ensures take Z = each(integer j; ((integer) return) <= j && j < ((integer) return) + (nr_pages*4096)){ ByteV(((pointer) 0)+(j*1), 0) } @*/
/*@ ensures cur == {cur}@start + (nr_pages*4096); {end}unchanged @*/
{
        /*CN*/ /*@ unpack EarlyAlloc((pointer) cur, end); @*/

        /* cp: originally */
	/* unsigned long ret = cur, i, p; */
	unsigned long ret = cur;
        unsigned long i = 0;
        unsigned long p = 0;

	if (!nr_pages)
		return NULL;

	cur += nr_pages << PAGE_SHIFT;
	if (cur > end) {
		cur = ret;
		return NULL;
	}


        /*CN*/ /*@ pack EarlyAlloc((pointer) cur, end); @*/
	for (i = 0; i < nr_pages; i++)
          /*@ inv {nr_pages} unchanged @*/
          /*@ inv cur == {cur}@start + (nr_pages*4096) @*/
          /*@ inv {end} unchanged; ret == {cur}@start @*/
          /*@ inv 0 <= i && i <= nr_pages @*/
          /*@ inv take E3 = EarlyAlloc((pointer) cur, end) @*/
          /*@ inv take Z = each(integer j; ret <= j && j < ret + (i*4096)){ ByteV(((pointer) 0)+(j*1), 0) } @*/
          /*@ inv take Z2 = each(integer j; ret + (i*4096) <= j && j < ret + (nr_pages*4096)){ Byte(((pointer) 0)+(j*1)) } @*/
        {
		p = ret + (i << PAGE_SHIFT);
		clear_page((void *)(p));
	}

	return (void *)ret;
}

void hyp_early_alloc_init(unsigned long virt, unsigned long size)
/*@ accesses base; cur; end; hyp_early_alloc_mm_ops @*/
/*@ requires virt + size < (power(2,64)) @*/
/*@ requires take B = each(integer j; virt <= j && j < virt + size){ Byte(((pointer) 0)+(j*1)) } @*/
/*@ ensures base == virt; end == virt + size; cur == virt @*/
/*@ ensures take E = EarlyAlloc((pointer) cur, end) @*/
{
	base = virt;
	end = virt + size;
	cur = virt;

	hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
	hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
	hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;

        /*CN*/ /*@ pack EarlyAlloc((pointer) cur, end); @*/
}
