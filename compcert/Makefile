# NOTE: This Makefile is low-tech, but at least it's portable to cygwin.
# We have the .depend file checked into the repository so that 
# this file works even if coqdep cannot be run.  Do "make depend"
# to rebuild the .depend file.

COQFLAGS= -dont-load-proofs -I . -I ..  -R . compcert
COQC=coqc
COQDEP=coqdep -I .
COQDOC=coqdoc

FILES = \
  AST.v Determinism.v Events.v Memdata.v Memtype.v Switch.v \
  Behaviors.v Errors.v Globalenvs.v Memory.v Smallstep.v Values.v \
  Integers.v Floats.v Coqlib.v Intv.v Ordered.v Axioms.v Maps.v \
  Ctypes.v Csyntax.v Csem.v Clight.v Clight_sem.v

.PHONY : clean  all lib docs

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $(COQFLAGS) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

depend:
	$(COQDEP) $(FILES) > .depend
include .depend
