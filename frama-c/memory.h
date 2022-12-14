// SPDX-License-Identifier: GPL-2.0-only
/* CP: originally at linux/arch/arm64/kvm/hyp/include/nvhe/memory.h */
#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* CP: originally #include <asm/page.h> */

/* CP: originally #include <linux/types.h> */

/* CP: adding */ 
#include "include/kernel.h"

/* CP: originally: extern s64 hyp_physvirt_offset; */
extern unsigned long long hyp_physvirt_offset;

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(virt)	(void*)((phys_addr_t)(virt) - hyp_physvirt_offset)

/*@ requires 0 <= phys - hyp_physvirt_offset < UINT_MAX;
    assigns \result \from hyp_physvirt_offset;
    ensures \separated((unsigned long long*)\result, &hyp_physvirt_offset); 
    ensures (phys_addr_t) \result == (\old(phys) - \old(hyp_physvirt_offset)); @*/
static inline void *hyp_phys_to_virt(phys_addr_t phys)
{
	return __hyp_va(phys);
}

/*@ requires 0 <= ((phys_addr_t)addr + hyp_physvirt_offset) < UINT_MAX;
    requires \separated((unsigned long long*)((phys_addr_t)addr + hyp_physvirt_offset), &hyp_physvirt_offset);
    assigns \result \from hyp_physvirt_offset; 
    ensures \result == ((phys_addr_t)addr + hyp_physvirt_offset); @*/
static inline phys_addr_t hyp_virt_to_phys(void* addr)
{
	return __hyp_pa(addr);
}

#endif /* __KVM_HYP_MEMORY_H */
