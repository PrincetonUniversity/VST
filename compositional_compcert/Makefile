COQFLAGS= -I . -as compositional_compcert
DEPFLAGS= -I ../msl -as msl -R ../compcert -as compcert
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc

FILES= \
  step_lemmas.v \
  extspec.v \
  mem_lemmas.v \
  core_semantics.v forward_simulations.v rg_forward_simulations.v \
  sim.v extension_sim.v rg_sim.v MemEvolve.v \
  forward_simulations_lemmas.v \
  extension.v extension_simulations.v extension_proof.v \
  null_extension.v fs_extension.v linking_extension.v trace_extension.v \
  mem_interpolants.v compiler_correctness_trans.v \
  compcert_compiler_correctness.v
#  sim_step_lemmas.v bigstep_extensions.v
#  Address.v 

target: proof

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) $(COQFLAGS) $*.v

depend:
	$(COQDEP) $(COQFLAGS) $(DEPFLAGS) $(FILES) > .depend

clean:
	rm -f *.vo *.glob $(FILES:%.v=%.html) *~

count:
	wc $(FILES)

include .depend
