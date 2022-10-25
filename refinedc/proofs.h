/* copied over from https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/linux/pkvm/proofs/early_alloc/instances.v, cut-down and turned into an inlined_prelude  */


//@rc::inlined_prelude
//@ Lemma shift_12_eq_mul_4096 n :
//@   (n ≪ 12) = n * 4096.
//@ Proof. by rewrite Z.shiftl_mul_pow2. Qed.
//@ #[export] Hint Rewrite shift_12_eq_mul_4096 : lithium_rewrite.
//@ Lemma ly_size_ly_offset ly m:
//@   (ly_size (ly_offset ly m) = ly_size ly - m)%nat.
//@ Proof. done. Qed.
//@ #[export] Hint Rewrite ly_size_ly_offset : lithium_rewrite.
//@rc::end
