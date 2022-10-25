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
/* adding */
#include "definitions.h"
#include "proofs.h"
#include "refinedc.h"

/* CP: originally: s64 hyp_physvirt_offset; */
unsigned long long hyp_physvirt_offset;
struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;

/* originally: */
/* static unsigned long base; */
/* static unsigned long end; */
/* static unsigned long cur; */

/* Specifications and RefinedC intra-function instrumentation are copied over from https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/linux/pkvm/early_alloc.c and sometimes tweaked and/or cut-down. These are marked with BEGIN and END comments */


/* BEGIN A */
struct
[[rc::refined_by("base : loc", "given : Z", "remaining : Z")]]
[[rc::let("z_cur : Z = {(base.2 + given * PAGE_SIZE)%Z}")]]
[[rc::let("z_end : Z = {(base.2 + (given + remaining) * PAGE_SIZE)%Z}")]]
[[rc::constraints("{0 ≤ given}", "{0 ≤ remaining}", "[alloc_global base]")]]
[[rc::constraints("{base.2 + (given + remaining) * PAGE_SIZE ≤ max_int u64}")]]
region {
  [[rc::field("z_end @ int<u64>")]]
  unsigned long end;
  [[rc::field("z_cur @ int<u64>")]]
  unsigned long cur;
  [[rc::field("own_constrained<nonshr_constraint<"
                 "{(base.1, z_cur) ◁ₗ uninit (PAGES (Z.to_nat remaining))}>, "
                 "base @ intptr<u64>>")]]
  unsigned long base;
};

static struct region mem;



#define base (mem.base)
#define end (mem.end)
#define cur (mem.cur)
/* END A */


/* BEGIN B */
[[rc::parameters("base : loc", "given : Z", "remaining : Z")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::returns("given @ int<size_t>")]]
[[rc::ensures("global mem : {(base, given, remaining)} @ region")]]
[[rc::tactics("all: rewrite Z.add_simpl_l; try solve_goal.")]]
[[rc::tactics("all: rewrite Z.shiftr_div_pow2 //= Z.div_mul //=.")]] /* END B */
unsigned long hyp_early_alloc_nr_pages(void)
{
	return (cur - base) >> PAGE_SHIFT;
}


/* CP: We don't implement clear_page here: RefinedC currently does not
   have the typing rules in place for 'zeroed'. Those could be added,
   but skipping this here. */
/* BEGIN C */
[[rc::parameters("p : loc")]]
[[rc::args("&own<place<p>>")]]
[[rc::requires("own p : uninit<{ly_with_align (Z.to_nat PAGE_SIZE) 1}>")]]
[[rc::ensures("own p : zeroed<{ly_with_align (Z.to_nat PAGE_SIZE) 1}>")]] /* END C */
extern void clear_page(void *to);

/* copied from https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/linux/pkvm/early_alloc.c and tweaked
BEGIN D */
[[rc::parameters("p : loc", "n : Z")]]                               /*RCSPECIGNORE*/
[[rc::args("&own<place<p>>", "{0} @ int<u8>", "n @ int<u64>")]]      /*RCSPECIGNORE*/
[[rc::requires("own p : uninit<{ly_with_align (Z.to_nat n) 1}>")]]   /*RCSPECIGNORE*/
[[rc::ensures("own p : zeroed<{ly_with_align (Z.to_nat n) 1}>")]]    /*RCSPECIGNORE*/
extern void memset(void *to, unsigned char c, unsigned long size);   


[[rc::parameters("base : loc", "given : Z", "remaining : Z")]]
[[rc::args("uninit<void*>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::requires("{1 ≤ remaining}")]]
[[rc::returns("&own<zeroed<PAGES<{Z.to_nat 1}>>>")]]
[[rc::ensures("global mem : {(base, given + 1, remaining - 1)%Z} @ region")]]
void *hyp_early_alloc_page(void *arg)
{
        /* originally "unsigned long ret = cur;" instead: */
	/*REFINEDC*/ void *ret = copy_alloc_id(cur, (void*) base);

	cur += PAGE_SIZE;
	if (cur > end) {
                /* originally "cur = ret;" instead: */
		cur = (unsigned long) ret;
		return NULL;
	}
	clear_page((void*)ret);

	/* originally: "return (void *)ret;" instead: */
	return ret;
}


[[rc::parameters("base : loc", "given : Z", "remaining : Z", "n : Z")]]
[[rc::args("n @ int<u32>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::requires("{0 < n ≤ remaining}", "{n ≪ PAGE_SHIFT ≤ max_int u32}")]]
[[rc::returns("&own<zeroed<PAGES<{Z.to_nat n}>>>")]]
[[rc::ensures("global mem : {(base, given + n, remaining - n)%Z} @ region")]]
void *hyp_early_alloc_contig(unsigned int nr_pages)
{
	/* originally: "unsigned long ret = cur, i, p;"; instead: */
	/*REFINEDC*/ void *ret = copy_alloc_id(cur, (void*) base);

	if (!nr_pages)
		return NULL;

	cur += nr_pages << PAGE_SHIFT;
	if (cur > end) {
		/* originally: "cur = ret;"; instead: */
		cur = (unsigned long) ret;
		return NULL;
	}

        /* originally: */
	/* for (i = 0; i < nr_pages; i++) { */
	/* 	p = ret + (i << PAGE_SHIFT); */
	/* 	clear_page((void *)(p)); */
	/* } */
        /* instead: */
	memset(ret, 0, nr_pages << PAGE_SHIFT);

        /* originally: "return (void *)ret;" instead: */
	return ret;
}
/* END D */


/* BEGIN I */
[[rc::parameters("l : loc", "n : Z", "s : Z")]]
[[rc::args("l @ &own<uninit<PAGES<{Z.to_nat n}>>>", "s @ int<u64>")]]
[[rc::requires("{s = (n * PAGE_SIZE)%Z}", "[alloc_global l]")]]
[[rc::requires("global mem : uninit<struct_region>")]]
[[rc::ensures("global mem : {(l, 0, n)} @ region")]] /* END I */
/* originally: */
/* void hyp_early_alloc_init(unsigned long virt, unsigned long size) */
/* instead: BEGIN K */
void hyp_early_alloc_init(void *virt, unsigned long size) /* END K */
{
        /* originally: */
	/* base = virt; */
	/* end = virt + size; */
	/* cur = virt; */

        /* instead: BEGIN J */
        base = (unsigned long)virt;
        end = base + size;
        cur = base;
        /* END J */

        /* originally: */
	/* hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page; */
	/* hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt; */
	/* hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys; */
}
