# SEE ../BUILD_ORGANIZATION for explanations of why this is the way it is

COQFLAGS= -I . -as msl
COQC=coqc
COQDEP=coqdep
COQDOC=coqdoc

FILES = \
  Axioms.v Extensionality.v base.v eq_dec.v \
  ageable.v sepalg.v psepalg.v age_sepalg.v \
  sepalg_generators.v functors.v sepalg_functors.v combiner_sa.v \
  cross_split.v join_hom_lemmas.v cjoins.v \
  boolean_alg.v tree_shares.v shares.v pshares.v \
  knot.v knot_sa.v knot_prop.v \
  knot_lemmas.v knot_unique.v \
  knot_hered.v knot_hered_sa.v \
  knot_full.v knot_shims.v \
  knot_sa_trivial.v \
  predicates_hered.v predicates_sl.v subtypes.v subtypes_sl.v \
  contractive.v predicates_rec.v \
  msl_direct.v msl_standard.v msl_classical.v \
  predicates_sa.v \
  normalize.v \
  env.v corec.v Coqlib2.v sepalg_list.v rmaps.v rmaps_lemmas.v op_classes.v \
  seplog.v alg_seplog.v log_normalize.v
#  knot_setoid.v \  takes forever to compile, nobody uses it

.PHONY : clean  all lib docs examples extract

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $(COQFLAGS) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

extract:
	coqc -R . msl extract.v

depend:
	$(COQDEP) $(COQFLAGS) $(FILES) > .depend
include .depend

