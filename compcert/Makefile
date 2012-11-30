# NOTE: This Makefile is low-tech, but at least it's portable to cygwin.
# We have the .depend file checked into the repository so that 
# this file works even if coqdep cannot be run.  Do "make depend"
# to rebuild the .depend file.

COQFLAGS= -dont-load-proofs -I . -I ..  -R . compcert
COQC=coqc
COQDEP=coqdep -I .
COQDOC=coqdoc

FILES = \
  AST.v Determinism.v Events.v Events2.v Memdata.v Memtype.v Switch.v \
  Behaviors.v Errors.v Globalenvs.v Memory.v Smallstep.v Values.v \
  Integers.v Floats.v Fappli_IEEE.v Fappli_IEEE_bits.v  \
  Fcore.v Fcore_defs.v Fcore_digits.v Fcore_FIX.v Fcore_float_prop.v \
  Fcore_FLT.v Fcore_FLX.v Fcore_FTZ.v Fcore_generic_fmt.v Fcore_Raux.v \
  Fcore_rnd.v Fcore_rnd_ne.v Fcore_ulp.v Fcore_Zaux.v \
  Fcalc_bracket.v  Fcalc_div.v  Fcalc_round.v \
  Fcalc_digits.v   Fcalc_ops.v  Fcalc_sqrt.v \
  Fprop_div_sqrt_error.v  Fprop_plus_error.v  Fprop_Sterbenz.v \
  Fprop_mult_error.v      Fprop_relative.v \
  Coqlib.v Intv.v Ordered.v Axioms.v Maps.v \
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
