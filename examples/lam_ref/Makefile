# We have the .depend file checked into the repository so that
# this file works even if coqdep cannot be run.  Do "make depend"
# to rebuild the .depend file.

COQFLAGS= -I . -I ../../msl -as msl
COQC=coqc
COQDEP=coqdep
COQDOC=coqdoc

FILES = \
  lam_ref_tcb.v \
  lam_ref_eval.v \
  lam_ref_mach_defs.v \
  lam_ref_mach_lemmas.v \
  lam_ref_type_prelim.v \
  lam_ref_type_defs.v \
  lam_ref_type_safety.v \
  lam_ref_type_lemmas.v \
  lam_ref_type_rules.v \
  programs.v crash.v

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
	$(COQDEP) $(COQFLAGS) $(FILES) > .depend
include .depend

