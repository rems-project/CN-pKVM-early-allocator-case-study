/*@ predicate kvm_pgtable_mm_ops(struct kvm_pgtable_mm_ops *p;) =
      kvm_pgtable_mm_ops_zalloc_page(p, _) &*&
      kvm_pgtable_mm_ops_zalloc_pages_exact(p, _) &*&
      kvm_pgtable_mm_ops_free_pages_exact(p, _) &*&
      kvm_pgtable_mm_ops_get_page(p, _) &*&
      kvm_pgtable_mm_ops_put_page(p, _) &*&
      kvm_pgtable_mm_ops_page_count(p, _) &*&
      kvm_pgtable_mm_ops_phys_to_virt(p, _) &*&
      kvm_pgtable_mm_ops_virt_to_phys(p, _);
@*/             

/*@ predicate earlyAlloc(char* cur_val, unsigned long end_val) =
       chars((char*) cur_val, end_val-(unsigned long) cur_val, _) &*& (unsigned long) cur_val <= end_val; @*/

/*@ predicate characters_zeroed(char* to, int count;) =
       count == 0 ? true : character(to, 0) &*& characters_zeroed(to + 1, count - 1); @*/
