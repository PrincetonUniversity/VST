# SEE ../BUILD_ORGANIZATION for explanations of why this is the way it is

COQFLAGS= -I . -as progs 
DEPFLAGS= -I ../msl -as msl -I ../veric -as veric -I ../floyd -as floyd -I ../sepcomp -as sepcomp  -R ../compcert -as compcert
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
COQDOC=coqdoc
CLIGHTGENFLAGS = -l loadpath

FILES= \
   list.v list_dt.v \
  reverse.v verif_reverse.v \
  queue.v verif_queue.v \
  sumarray.v verif_sumarray.v \
  message.v verif_message.v \


target: proof

proof: $(FILES:.v=.vo)

reverse.v: reverse.c
	clightgen reverse.c
queue.v: queue.c
	clightgen queue.c
sumarray.v: sumarray.c
	clightgen sumarray.c
message.v: message.c
	clightgen message.c

reverse.vo: reverse.v
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

