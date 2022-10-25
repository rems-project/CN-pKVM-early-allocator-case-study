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



[[rc::parameters("phys_v : Z", "offset : Z")]]
[[rc::requires("global hyp_physvirt_offset : offset @ int<u64>")]]
[[rc::args("phys_v @ int<u64>")]]
[[rc::requires("{0 <= phys_v - offset}", "{phys_v - offset < max_int u64}")]]
[[rc::exists("virt : loc")]]
[[rc::returns("&own<place<virt>>")]]
[[rc::ensures("global hyp_physvirt_offset : offset @ int<u64>")]]
[[rc::ensures("{virt.2 = phys_v - offset}")]]
static inline void *hyp_phys_to_virt(phys_addr_t phys)
{
	return __hyp_va(phys);
}

[[rc::parameters("addr_v : loc", "offset : Z")]]
[[rc::args("&own<place<addr_v>>")]]
[[rc::requires("global hyp_physvirt_offset : offset @ int<u64>")]]
[[rc::requires("{0 <= addr_v.2 + offset}", "{addr_v.2 + offset < max_int u64}")]]
[[rc::requires("[alloc_alive_loc addr_v]", "[loc_in_bounds addr_v 1]")]]
[[rc::ensures("global hyp_physvirt_offset : offset @ int<u64>")]]
[[rc::returns("{addr_v.2 + offset} @ int<u64>")]]
static inline phys_addr_t hyp_virt_to_phys(void* addr)
{
	return __hyp_pa(addr);
}

#endif /* __KVM_HYP_MEMORY_H */
