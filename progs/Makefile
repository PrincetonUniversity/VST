COQFLAGS= -dont-load-proofs -R . progs
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc
CLIGHTGENFLAGS = -I ../compcert/lib -I ../compcert/common -I ../compcert/cfrontend \
    -I ../compcert/flocq/Appli   -I ../compcert/flocq/Calc  -I ../compcert/flocq/Core  -I ../compcert/flocq/Prop

FILES= \
  loadpath.v list.v client_lemmas.v assert_lemmas.v field_mapsto.v forward.v \
  test1.v ilseg.v entailment_tests.v verif1.v


target: proof

proof: $(FILES:.v=.vo)


test1.vo: test1.v
	$(COQC) $(COQFLAGS)  $(CLIGHTGENFLAGS) $*.v

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

