# See the file BUILD_ORGANIZATION for 
# explanations of why this is the way it is

COMPCERT=compcert
-include CONFIGURE
#Note:  You can make a CONFIGURE file with the definition
#   COMPCERT=../compcert
# if, for example, you want to build from a compcert distribution
# that is sitting in a sister directory to vst.
# One might think that one could change this to  COMPCERT=/home/appel/compcert
# if there is a compcert build at that pathname, but in cygwin
# at least, coqdep is confused by the absolute pathname while
# it works fine with the relative pathname

#Note2:  By default, the rules for converting .c files to .v files
# are inactive.  To activate them, do something like
#  make CLIGHTGEN=clightgen

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
DIRS= msl sepcomp veric floyd progs
INCLUDE= $(foreach a,$(DIRS), -I $(a) -as $(a)) -R $(COMPCERT) -as compcert
# $(foreach a,$(CC_DIRS), -R $(COMPCERT)/$(a) -as compcert.$(a)) -I $(COMPCERT)/flocq -as compcert.flocq

CV1=$(shell cat compcert/VERSION)
CV2=$(shell cat $(COMPCERT)/VERSION)

ifneq ($(CV1), $(CV2))
$(error COMPCERT_VERSION=$(CV1) but $(COMPCERT)/VERSION=$(CV2))
endif

ifeq ($(wildcard $(COMPCERT)/*/Clight.vo), )
ifeq ($(COMPCERT), compcert)
 $(warning FIRST BUILD COMPCERT, by:  cd compcert; ./make   (use ./make and not just make))
 $(warning "or, link to an external compcert directory by creating a CONFIGURE file;")
 $(error " see the note in vst/Makefile.")
else
 $(error FIRST BUILD COMPCERT, by:  cd $(COMPCERT); make clightgen)
endif
endif


COQFLAGS= $(INCLUDE)
DEPFLAGS= $(INCLUDE)
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep -slash
COQDOC=coqdoc

MSL_FILES = \
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

SEPCOMP_FILES= \
  Address.v step_lemmas.v Coqlib2.v extspec.v FiniteMaps.v \
  mem_lemmas.v mem_interpolants.v mem_interpolation_defs.v \
  mem_interpolation_EE.v mem_interpolation_EI.v mem_interpolation_IE.v mem_interpolation_II.v \
  mem_interpolation_proofs.v compiler_correctness.v \
  core_semantics.v forward_simulations.v forward_simulations_trans.v \
  forward_simulations_lemmas.v rg_forward_simulations.v rg_semantics.v rg_forward_simulations_lemmas.v \
  compiler_correctness_trans.v compiler_correctness_progless_trans.v \
  safety_preservation.v \
  StructuredInjections.v effect_semantics.v effect_simulations.v \
  effect_simulations_lemmas.v effect_corediagram_trans.v \
  effect_properties.v effect_interpolants.v effect_simulations_trans.v \
  effect_interpolation_II.v effect_interpolation_proofs.v \
  arguments.v closed_safety.v compcert.v open_semantics_preservation.v \
  trace_semantics.v \
  wf_lemmas_old.v linking_old.v linking_simulations_old.v linking_proof_old.v 

LINKING_FILES= \
  pos.v \
  stack.v \
  cast.v \
  wf_lemmas.v \
  core_semantics_lemmas.v \
  pred_lemmas.v \
  sminj_lemmas.v \
  domain_inv.v \
  linking.v \
  linking_lemmas.v \
  linking_sim.v

COMPCOMP_FILES= \
  Ordered.v Switch.v Cminor.v Cminor_coop.v Cminor_eff.v \
  Csharpminor.v Csharpminor_coop.v Csharpminor_eff.v \
  Cshmgen.v \
  Cminorgen.v CminorgenproofRestructured.v CminorgenproofSIM.v CminorgenproofEFF.v \
  Op.v CminorSel.v CminorSel_coop.v CminorSel_eff.v \
  SelectOp.v SelectDiv.v SelectLong.v \
  SelectOpproof.v SelectDivproof.v SelectLongproof.v \
  Selection.v SelectionproofEFF.v Registers.v RTL.v \
  RTL_coop.v RTL_eff.v RTLgen.v RTLgenspec.v RTLgenproofEFF.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Subtyping.v RTLtyping.v LTL_coop.v LTL_eff.v \
  Lattice.v Wfsimpl.v Iteration.v Heaps.v Kildall.v \
  FSetAVLplus.v Allocation.v AllocproofEFF.v \
  Inlining.v Inliningspec.v Inliningproof.v
#Selectionproof.v

VERIC_FILES= \
  base.v rmaps.v rmaps_lemmas.v compcert_rmaps.v Cop2.v\
  lift.v expr.v environ_lemmas.v binop_lemmas.v expr_lemmas.v \
  Clight_lemmas.v Clight_new.v Clightnew_coop.v Clight_sim.v \
  slice.v res_predicates.v seplog.v assert_lemmas.v  ghost.v \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v \
  initial_world.v initialize.v semax_prog.v SeparationLogic.v SeparationLogicSoundness.v  \
  NullExtension.v SequentialClight.v

FLOYD_FILES= \
   base.v proofauto.v malloc_lemmas.v \
   client_lemmas.v canonicalize.v assert_lemmas.v field_mapsto.v \
   compare_lemmas.v array_lemmas.v \
   call_lemmas.v loadstore_lemmas.v forward_lemmas.v forward.v \
   entailer.v globals_lemmas.v

PROGS_FILES= \
  list_dt.v verif_reverse.v verif_queue.v verif_sumarray.v verif_message.v \
  insertionsort.v reverse.v queue.v sumarray.v message.v \
  SHA256.v sha_lemmas.v sha.v spec_sha.v verif_sha_update.v verif_sha_init.v \
  verif_sha_bdo.v verif_sha_bdo2.v verif_sha_bdo3.v verif_sha_bdo4.v verif_sha_final2.v verif_sha_final.v \
   entail_examples.v entail_examples2.v \
  revarray.v verif_revarray.v insertionsort.v verif_insertion_sort.v \
  verif_float.v

C_FILES = reverse.c queue.c sumarray.c message.c sha.c insertionsort.c float.c

FILES = \
 $(MSL_FILES:%=msl/%) \
 $(SEPCOMP_FILES:%=sepcomp/%) \
 $(VERIC_FILES:%=veric/%) \
 $(FLOYD_FILES:%=floyd/%) \
 $(PROGS_FILES:%=progs/%) 

%_stripped.v: %.v
# e.g., 'make progs/verif_reverse_stripped.v will remove the tutorial comments
# from progs/verif_reverse.v
	grep -v '^.[*][*][ )]' $*.v >$@

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQFLAGS) $*.v
#  to collect wall-clock timings, use the following in place of the one above
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQFLAGS) $*.v; date +'%s.%N after' >>timings" 2>>timings

#compcert/%.vo: compcert/%.v
#	()

all:     .loadpath $(FILES:.v=.vo) version.vo

msl:     .loadpath $(MSL_FILES:%.v=msl/%.vo)
sepcomp: .loadpath $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo)
linking: .loadpath $(CC_TARGET) $(LINKING_FILES:%.v=sepcomp/%.vo)
veric:   .loadpath $(VERIC_FILES:%.v=veric/%.vo)
floyd:   .loadpath $(FLOYD_FILES:%.v=floyd/%.vo) floyd/floyd.coq
progs:   .loadpath $(PROGS_FILES:%.v=progs/%.vo)
compcomp: .loadpath $(COMPCOMP_FILES:%.v=sepcomp/%.vo)


ifdef CLIGHTGEN
# Is there a way to generate the next 5 rules automatically from C_FILES? 
progs/revarray.v: progs/revarray.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/reverse.v: progs/reverse.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/queue.v: progs/queue.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/sumarray.v: progs/sumarray.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/message.v: progs/message.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/sha.v: progs/sha.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/insertionsort.v: progs/insertionsort.c
	$(CLIGHTGEN) -DCOMPCERT $<
progs/float.v: progs/float.c
	$(CLIGHTGEN) -DCOMPCERT $<
endif

version.v: $(FILES) util/make_version
	sh util/make_version

.loadpath: Makefile
	echo $(INCLUDE) >.loadpath

floyd/floyd.coq: floyd/proofauto.vo
	coqtop -load-vernac-source floyd/proofauto -outputstate floyd/floyd -batch

.depend:
	$(COQDEP) $(DEPFLAGS) $(FILES) > .depend

depend:
	$(COQDEP) $(DEPFLAGS) $(FILES) > .depend

depend-linking:
	$(COQDEP) $(DEPFLAGS) $(FILES) $(LINKING_FILES) > .depend

clean:
	rm -f $(FILES:%.v=%.vo) $(FILES:%.v=%.glob) floyd/floyd.coq .loadpath .depend

clean-linking:
	rm -f $(LINKING_FILES:%.v=sepcomp/%.vo) $(LINKING_FILES:%.v=sepcomp/%.glob) 

count:
	wc $(FILES)

$(CC_TARGET): compcert/make
	(cd compcert; ./make)

include .depend
