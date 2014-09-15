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
DIRS= msl sepcomp veric floyd progs sha linking
INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -I $(a) -as $(a))) -R $(COMPCERT) -as compcert
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
  is_prop_lemma.v \
  predicates_hered.v predicates_sl.v subtypes.v subtypes_sl.v \
  contractive.v predicates_rec.v \
  msl_direct.v msl_standard.v msl_classical.v \
  predicates_sa.v \
  normalize.v \
  env.v corec.v Coqlib2.v sepalg_list.v rmaps.v rmaps_lemmas.v op_classes.v \
  seplog.v alg_seplog.v log_normalize.v

SEPCOMP_FILES= \
  Address.v step_lemmas.v extspec.v FiniteMaps.v \
  mem_lemmas.v mem_wd.v mem_interpolants.v mem_interpolation_defs.v \
  mem_interpolation_EE.v mem_interpolation_EI.v mem_interpolation_IE.v mem_interpolation_II.v \
  mem_interpolation_proofs.v compiler_correctness.v \
  core_semantics.v core_semantics_lemmas.v \
  forward_simulations.v forward_simulations_trans.v \
  forward_simulations_lemmas.v \
  compiler_correctness_trans.v compiler_correctness_progless_trans.v \
  safety_preservation.v \
  StructuredInjections.v effect_semantics.v effect_simulations.v rg_lemmas.v \
  effect_simulations_lemmas.v effect_corediagram_trans.v \
  effect_properties.v effect_interpolants.v effect_simulations_trans.v \
  effect_interpolation_II.v effect_interpolation_proofs.v \
  arguments.v closed_safety.v compcert.v \
  val_casted.v \
  reach.v \
  trace_semantics.v \
  arguments.v \
  nucular_semantics.v \
  effect_simulationsEXP.v \
  wholeprog_simulations.v \
  wholeprog_lemmas.v \
  barebones_simulations.v \
  dep_effect_simulationsEXP.v \
  dep_wholeprog_simulations.v 

LINKING_FILES= \
  sepcomp.v \
  pos.v \
  stack.v \
  cast.v \
  seq_lemmas.v \
  wf_lemmas.v \
  reestablish.v \
  pred_lemmas.v \
  inj_lemmas.v \
  join_sm.v \
  disjointness.v \
  rc_semantics.v \
  rc_semantics_lemmas.v \
  reach_lemmas.v \
  linking.v \
  compcert_linking.v \
  compcert_linking_lemmas.v \
  core_semantics_tcs.v \
  linking_inv.v \
  call_lemmas.v \
  ret_lemmas.v \
  linking_spec.v \
  linking_proof.v \
  stacking.v \
  context_equiv.v \
  erase_juice.v \
  safety.v

VERIC_FILES= \
  base.v rmaps.v rmaps_lemmas.v compcert_rmaps.v Cop2.v\
  lift.v expr.v environ_lemmas.v binop_lemmas.v expr_lemmas.v expr_lemmas2.v expr_rel.v \
  Clight_lemmas.v Clight_new.v Clightnew_coop.v Clight_sim.v \
  slice.v res_predicates.v seplog.v assert_lemmas.v  ghost.v \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_safety.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v \
  initial_world.v initialize.v semax_prog.v semax_ext.v SeparationLogic.v SeparationLogicSoundness.v  \
  NullExtension.v SequentialClight.v superprecise.v

FLOYD_FILES= \
   base.v proofauto.v \
   client_lemmas.v canonicalize.v assert_lemmas.v closed_lemmas.v \
   field_mapsto.v compare_lemmas.v array_lemmas.v \
   call_lemmas.v extcall_lemmas.v loadstore_lemmas.v type_id_env.v forward_lemmas.v forward.v \
   entailer.v globals_lemmas.v \
   nested_field_lemmas.v data_at_lemmas.v unfold_data_at.v nested_loadstore.v\
   expr_rel.v for_lemmas.v semax_tactics.v

PROGS_FILES= \
  list_dt.v verif_reverse.v verif_queue.v verif_sumarray.v verif_message.v \
  insertionsort.v reverse.v queue.v sumarray.v message.v string.v\
   entail_examples.v \
  revarray.v verif_revarray.v insertionsort.v verif_insertion_sort.v \
  verif_float.v verif_dotprod.v \
  verif_nest3.v verif_nest2.v \
  logical_compare.v verif_logical_compare.v \
  even.v verif_even.v odd.v verif_odd.v

SHA_FILES= \
  SHA256.v common_lemmas.v sha_lemmas.v functional_prog.v \
  sha.v spec_sha.v verif_sha_init.v \
  verif_sha_update.v verif_sha_update2.v verif_sha_update3.v verif_sha_update4.v \
  bdo_lemmas.v verif_sha_bdo.v verif_sha_bdo2.v \
  verif_sha_bdo4.v verif_sha_bdo7.v verif_sha_bdo8.v \
  verif_sha_final2.v verif_sha_final3.v verif_sha_final.v \
  verif_addlength.v verif_SHA256.v

HMAC_FILES= \
  HMAC_functional_prog.v \
  hmac091c.v spec_hmac.v verif_hmac_cleanup.v verif_hmac_simple.v \
  HMAC_refined_fp.v hmac_sha256.v HMAC_definitions.v HMAC_lemmas.v \
  HMAC_part2GT.v HMAC_part2LE.v \
  HMAC_LoopBodyGT.v HMAC_LoopBodyLE.v \
  HMAC_proofLE.v HMAC_proof.v

C_FILES = reverse.c queue.c sumarray.c message.c insertionsort.c float.c nest3.c nest2.c nest3.c dotprod.c string.v

FILES = \
 $(MSL_FILES:%=msl/%) \
 $(SEPCOMP_FILES:%=sepcomp/%) \
 $(VERIC_FILES:%=veric/%) \
 $(FLOYD_FILES:%=floyd/%) \
 $(PROGS_FILES:%=progs/%) \
 $(SHA_FILES:%=sha/%) \
 $(HMAC_FILES:%=sha/%) 

%_stripped.v: %.v
# e.g., 'make progs/verif_reverse_stripped.v will remove the tutorial comments
# from progs/verif_reverse.v
	grep -v '^.[*][*][ )]' $*.v >$@

%.vo: %.v
	@echo COQC $*.v
ifeq ($(TIMINGS), true)
	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQFLAGS) $*.v; date +'%s.%N after' >>timings" 2>>timings
else
	@$(COQC) $(COQFLAGS) $*.v
endif

#compcert/%.vo: compcert/%.v
#	()

default_target: msl veric floyd progs

all:     .loadpath $(FILES:.v=.vo) version.vo

msl:     .loadpath $(MSL_FILES:%.v=msl/%.vo)
sepcomp: .loadpath $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo)
linking: .loadpath linking/linking_proof.vo $(LINKING_FILES:%.v=linking/%.vo) 
veric:   .loadpath $(VERIC_FILES:%.v=veric/%.vo)
floyd:   .loadpath $(FLOYD_FILES:%.v=floyd/%.vo)
progs:   .loadpath $(PROGS_FILES:%.v=progs/%.vo)
sha:     .loadpath $(SHA_FILES:%.v=sha/%.vo)
hmac:    .loadpath $(HMAC_FILES:%.v=sha/%.vo)

CGFLAGS =  -DCOMPCERT

CVFILES = progs/revarray.v progs/reverse.v progs/queue.v progs/sumarray.v \
         progs/message.v progs/insertionsort.v progs/float.v progs/logical_compare.v \
         progs/nest2.v progs/nest3.v progs/dotprod.v

cvfiles: $(CVFILES)

clean_cvfiles: 
	rm $(CVFILES)

ifdef CLIGHTGEN
sha/sha.v: sha/sha.c
	$(CLIGHTGEN) ${CGFLAGS} $<
# Is there a way to generate the next 5 rules automatically from C_FILES? 
progs/revarray.v: progs/revarray.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/reverse.v: progs/reverse.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/queue.v: progs/queue.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/sumarray.v: progs/sumarray.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/message.v: progs/message.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/insertionsort.v: progs/insertionsort.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/float.v: progs/float.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/logical_compare.v: progs/logical_compare.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/nest2.v: progs/nest2.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/nest3.v: progs/nest3.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/dotprod.v: progs/dotprod.c
	$(CLIGHTGEN) ${CGFLAGS} $<
endif

version.v: $(FILES) util/make_version
	sh util/make_version

.loadpath: Makefile
	echo $(INCLUDE) >.loadpath

floyd/floyd.coq: floyd/proofauto.vo
	coqtop $(COQFLAGS) -load-vernac-object floyd/proofauto -outputstate floyd/floyd -batch

.depend:
	$(COQDEP) $(DEPFLAGS) $(FILES) > .depend

depend:
	$(COQDEP) $(DEPFLAGS) $(FILES) > .depend

depend-linking:
	$(COQDEP) $(DEPFLAGS) $(FILES) $(LINKING_FILES:%.v=linking/%.v) > .depend

clean:
	rm -f $(FILES:%.v=%.vo) $(FILES:%.v=%.glob) floyd/floyd.coq .loadpath .depend

clean-linking:
	rm -f $(LINKING_FILES:%.v=linking/%.vo) $(LINKING_FILES:%.v=linking/%.glob) 

count:
	wc $(FILES)

count-linking:
	wc $(LINKING_FILES:%.v=linking/%.v)

# $(CC_TARGET): compcert/make
#	(cd compcert; ./make)

include .depend
