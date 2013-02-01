# SEE ../BUILD_ORGANIZATION for explanations of why this is the way it is
COQFLAGS= -I . -as veric
DEPFLAGS= -I ../msl -as msl -R ../compcert -as compcert
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc

FILES= \
  Coqlib2.v  base.v Address.v rmaps.v rmaps_lemmas.v compcert_rmaps.v \
  expr.v environ_lemmas.v binop_lemmas.v binop_lemmas2.v expr_lemmas.v \
  extspec.v step_lemmas.v \
  Clight_lemmas.v Clight_new.v Clight_sim.v \
  slice.v res_predicates.v seplog.v assert_lemmas.v  \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v \
  initial_world.v initialize.v semax_prog.v SeparationLogic.v SeparationLogicSoundness.v \
  NullExtension.v SequentialClight.v \
#  sim.v Sim_starplus.v 
#  MemEvolve.v linking_extension.v trace_extension.v \
#  rg_sim.v extension_sim.v
#  extension.v extension_proof.v seplog_extension.v null_extension.v fs_extension.v 


target: proof

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

../%.vo: ../%.v
	echo "ERROR: $@ not built!"
.v.vo:
	$(COQC) $(COQFLAGS) $*.v

depend:
	$(COQDEP) $(COQFLAGS) $(DEPFLAGS) $(FILES) > .depend

clean:
	rm -f *.vo *.glob $(FILES:%.v=%.html) *~

count:
	wc $(FILES)

include .depend
