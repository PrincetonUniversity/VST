COQFLAGS= -dont-load-proofs -I . -I ..  -R . veric
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc

FILES= \
  Coqlib2.v  base.v Address.v rmaps.v rmaps_lemmas.v compcert_rmaps.v \
  expr.v expr_lemmas.v \
  extspec.v forward_simulations.v forward_simulations_proofs.v step_lemmas.v \
  sim.v \
  Clight_lemmas.v Clight_new.v Clight_sim.v \
  slice.v res_predicates.v seplog.v assert_lemmas.v  \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v \
  initial_world.v semax_prog.v SeparationLogic.v SeparationLogicSoundness.v \
  NullExtension.v SequentialClight.v


target: proof

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) $(COQFLAGS) $*.v

depend:
	$(COQDEP) $(COQFLAGS) $(FILES) > .depend

clean:
	rm -f *.vo *.glob $(FILES:%.v=%.html) *~

count:
	wc $(FILES)

include .depend

