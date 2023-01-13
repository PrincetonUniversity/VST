clightgen -normalize progs64/input.c
make progs64/input.vo
rm progs64/proofgen.vo
make ANNOTATE=false progs64/proofgen.vo > progs64/verif_input.v
