# SEE ../BUILD_ORGANIZATION for explanations of why this is the way it is

COQFLAGS= -I . -as progs 
DEPFLAGS= -I ../msl -as msl -I ../veric -as veric -I ../compositional_compcert -as compositional_compcert  -R ../compcert -as compcert
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc
CLIGHTGENFLAGS = -l loadpath

FILES= \
   list.v list_dt.v \
   client_lemmas.v assert_lemmas.v field_mapsto.v forward_lemmas.v forward.v \
  test1.v verif1.v \
  queue.v verif_queue.v


target: proof

proof: $(FILES:.v=.vo)


test1.vo: test1.v
	$(COQC) $(COQFLAGS) $(CLIGHTGENFLAGS) $*.v

queue.vo: queue.v
	$(COQC) $(COQFLAGS) $(CLIGHTGENFLAGS) $*.v

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

