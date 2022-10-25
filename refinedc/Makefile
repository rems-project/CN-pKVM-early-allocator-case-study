.PHONY: default check clean

default: check

clean:
	rm -rf _build
	rm -rf _CoqProject
	rm -f dune-project
	rm -f rc-project.toml
	rm -rf proofs

rc-project.toml:
	refinedc init

check: rc-project.toml
	refinedc check -I ../original early_alloc.c

