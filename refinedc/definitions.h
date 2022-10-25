/* copied over from https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/linux/pkvm/include/asm/page-def.h, cut-down and tweaked */

//@rc::inlined_prelude
//@ Notation PAGE_SHIFT := (12).
//@ Notation PAGE_SIZE := (4096).
//@ Definition PAGES (n : nat) : layout :=
//@   ly_with_align (n * Z.to_nat PAGE_SIZE) 1.
//@ Notation PAGE := (PAGES 1).
//@rc::end
