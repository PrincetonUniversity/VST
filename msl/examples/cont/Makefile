# NOTE: This Makefile is low-tech, but at least it's portable to cygwin.
# We have the .depend file checked into the repository so that 
# this file works even if coqdep cannot be run.  Do "make depend"
# to rebuild the .depend file.

COQC=coqc -dont-load-proofs -I ../../.. -R . msl.examples.cont
COQDEP=coqdep -I ../../..
COQDOC=coqdoc

FILES = \
  language.v seplog.v model.v lseg.v client_lemmas.v sample_prog.v

.PHONY : clean  all lib docs

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

depend:
	$(COQDEP) $(FILES) > .depend
include .depend
