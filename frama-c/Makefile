.PHONY: default check clean

default: check

clean: 
	rm -rf .frama-c
	rm -f generated.c

generated.c: macros.h early_alloc.c ../original/include/*.h
	cat macros.h > generated.c
	clang -I ../original -E -CC -P early_alloc.c >> generated.c

check: generated.c
	frama-c -wp -wp-rte generated.c

