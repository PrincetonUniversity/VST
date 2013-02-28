# SEE ../BUILD_ORGANIZATION for explanations of why this is the way it is

COQFLAGS= -I . -as progs 
DEPFLAGS= -I ../msl -as msl -I ../veric -as veric -I ../compositional_compcert -as compositional_compcert  -R ../compcert -as compcert
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc
CLIGHTGENFLAGS = -l loadpath

FILES= \
   base.v proofauto.v list.v list_dt.v malloc_lemmas.v \
   client_lemmas.v canonicalize.v assert_lemmas.v field_mapsto.v \
   call_lemmas.v forward_lemmas.v forward.v \
  test1.v verif1.v \
  queue.v verif_queue.v \
  sumarray.v verif_sumarray.v \
  message.v verif_message.v \


target: proof

proof: $(FILES:.v=.vo)


test1.vo: test1.v
	$(COQC) $(COQFLAGS) $(CLIGHTGENFLAGS) $*.v

queue.vo: queue.v
	$(COQC) $(COQFLAGS) $(CLIGHTGENFLAGS) $*.v

sumarray.vo: sumarray.v
	$(COQC) $(COQFLAGS) $(CLIGHTGENFLAGS) $*.v

message.vo: message.v
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

