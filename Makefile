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

#Configure a custom Ssreflect installation (used to build the linking/ subdirectory):
#SSREFLECT=""
#MATHCOMP=""

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
DIRS= msl sepcomp veric floyd progs sha linking fcf hmacfcf tweetnacl20140427
INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -I $(a) -as $(a))) -R $(COMPCERT) -as compcert 
#Replace the INCLUDE above with the following in order to build the linking target:
#INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -I $(a) -as $(a))) -R $(COMPCERT) -as compcert -I $(SSREFLECT)/src -R $(SSREFLECT)/theories -as Ssreflect \
#  -R $(MATHCOMP)/theories -as MathComp
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


#COQFLAGS= $(foreach d, $(DIRS), -R $(d) -as VST.$(d)) -R $(COMPCERT) -as compcert
COQFLAGS= $(foreach d, $(DIRS), -R $(d) -as $(d)) -R $(COMPCERT) -as compcert 
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
  corable.v \
  predicates_hered.v predicates_sl.v subtypes.v subtypes_sl.v \
  contractive.v predicates_rec.v \
  msl_direct.v msl_standard.v msl_classical.v \
  predicates_sa.v \
  normalize.v \
  env.v corec.v Coqlib2.v sepalg_list.v rmaps.v rmaps_lemmas.v op_classes.v \
  simple_CCC.v seplog.v alg_seplog.v log_normalize.v

SEPCOMP_FILES= \
  Address.v \
  step_lemmas.v \
  extspec.v \
  FiniteMaps.v \
  mem_lemmas.v mem_wd.v \
  compiler_correctness.v \
  core_semantics.v core_semantics_lemmas.v \
  forward_simulations.v \
  forward_simulations_lemmas.v \
  safety_preservation.v \
  StructuredInjections.v \
  effect_semantics.v effect_simulations.v effect_simulations_lemmas.v \
  rg_lemmas.v \
  effect_properties.v \
  arguments.v closed_safety.v compcert.v \
  val_casted.v \
  reach.v \
  trace_semantics.v \
  arguments.v \
  nucular_semantics.v \
  wholeprog_simulations.v \
  wholeprog_lemmas.v \
  barebones_simulations.v

LINKING_FILES= \
  sepcomp.v \
  pos.v \
  stack.v \
  pred_lemmas.v \
  rc_semantics.v \
  rc_semantics_lemmas.v \
  linking.v \
  compcert_linking.v \
  compcert_linking_lemmas.v \
  core_semantics_tcs.v \
  linking_spec.v \
  erase_juice.v \
  safety.v \
  semax_linking.v \
  cast.v \
  tuple.v \
  finfun.v

VERIC_FILES= \
  base.v shares.v rmaps.v rmaps_lemmas.v compcert_rmaps.v Cop2.v\
  tycontext.v lift.v expr.v expr2.v environ_lemmas.v binop_lemmas.v binop_lemmas2.v \
  expr_lemmas.v expr_lemmas2.v expr_lemmas3.v expr_rel.v  extend_tc.v \
  Clight_lemmas.v Clight_new.v Clightnew_coop.v Clight_sim.v \
  slice.v res_predicates.v seplog.v assert_lemmas.v  ghost.v \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_safety.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v semax_congruence.v \
  initial_world.v initialize.v semax_prog.v semax_ext.v SeparationLogic.v SeparationLogicSoundness.v  \
  NullExtension.v SequentialClight.v superprecise.v jstep.v address_conflict.v

FLOYD_FILES= \
   coqlib3.v base.v proofauto.v computable_theorems.v \
   type_induction.v reptype_lemmas.v aggregate_type.v aggregate_pred.v \
   nested_pred_lemmas.v compact_prod_sum.v zlist.v \
   sublist.v smt_test.v \
   client_lemmas.v canon.v canonicalize.v assert_lemmas.v closed_lemmas.v jmeq_lemmas.v \
   compare_lemmas.v sc_set_load_store.v \
   loadstore_mapsto.v loadstore_field_at.v nested_loadstore.v \
   call_lemmas.v extcall_lemmas.v forward_lemmas.v forward.v \
   entailer.v globals_lemmas.v local2ptree.v fieldlist.v mapsto_memory_block.v\
   nested_field_lemmas.v efield_lemmas.v proj_reptype_lemmas.v replace_refill_reptype_lemmas.v \
   data_at_lemmas.v field_at.v stronger.v \
   for_lemmas.v semax_tactics.v expr_lemmas.v real_forward.v diagnosis.v

PROGS_FILES= \
  list_dt.v verif_reverse.v verif_queue.v verif_sumarray.v \
  insertionsort.v reverse.v queue.v sumarray.v message.v string.v\
  revarray.v verif_revarray.v insertionsort.v \
  verif_float.v verif_ptr_compare.v \
  verif_nest3.v verif_nest2.v \
  logical_compare.v verif_logical_compare.v field_loadstore.v  verif_field_loadstore.v \
  even.v verif_even.v odd.v verif_odd.v \
  merge.v verif_merge.v
# verif_message.v verif_dotprod.v verif_insertion_sort.v 

SHA_FILES= \
  general_lemmas.v SHA256.v common_lemmas.v pure_lemmas.v sha_lemmas.v functional_prog.v \
  sha.v spec_sha.v verif_sha_init.v \
  verif_sha_update.v verif_sha_update2.v verif_sha_update3.v verif_sha_update4.v \
  bdo_lemmas.v verif_sha_bdo.v  \
  verif_sha_bdo4.v verif_sha_bdo7.v verif_sha_bdo8.v \
  verif_sha_final2.v verif_sha_final3.v verif_sha_final.v \
  verif_addlength.v verif_SHA256.v call_memcpy.v

HMAC_FILES= \
  HMAC_functional_prog.v HMAC256_functional_prog.v \
  vst_lemmas.v hmac_pure_lemmas.v hmac_common_lemmas.v \
  hmac091c.v spec_hmac.v verif_hmac_cleanup.v \
  verif_hmac_init_part1.v verif_hmac_init_part2.v verif_hmac_init.v \
  verif_hmac_update.v verif_hmac_final.v verif_hmac_simple.v \
  verif_hmac_double.v verif_hmac_crypto.v \
  hmac_NK.v spec_hmacNK.v verif_hmacNK_cleanup.v \
  verif_hmacNK_init_part1.v verif_hmacNK_init_part2.v verif_hmacNK_init.v\
  verif_hmacNK_update.v verif_hmacNK_final.v verif_hmacNK_simple.v \
  verif_hmacNK_double.v verif_hmacNK_crypto.v \
  spec_hmacADT.v verif_hmacADT_cleanup.v \
  verif_hmacADT_init_part1.v \
  verif_hmacADT_update.v verif_hmacADT_final.v verif_hmacADT_simple.v \
  verif_hmacADT_double.v  verif_hmacADT_init_part1_5.v \
  verif_hmacADT_init_part1.v  verif_hmacADT_init_part2.v verif_hmacADT_init.v 
#  HMAC_lemmas.v HMAC_refined_fp.v hmac_sha256.v HMAC_definitions.v \
#  HMAC_part2GT.v HMAC_part2LE.v \
#  HMAC_LoopBodyGT.v HMAC_LoopBodyLE.v \
#  HMAC_proofLE.v HMAC_proof.v

FCF_FILES= \
  Limit.v Blist.v StdNat.v Rat.v Fold.v Comp.v DetSem.v DistSem.v \
  DistRules.v DistTacs.v ProgTacs.v GenTacs.v Crypto.v SemEquiv.v \
  ProgramLogic.v RndNat.v Bernoulli.v FCF.v HasDups.v CompFold.v \
  RepeatCore.v PRF_Encryption_IND_CPA.v PRF.v Array.v Encryption.v \
  Asymptotic.v Admissibility.v RndInList.v OTP.v RndGrpElem.v \
  GroupTheory.v WC_PolyTime.v RndListElem.v RndPerm.v NoDup_gen.v \
  Hybrid.v OracleCompFold.v PRF_Convert.v

HMACFCF_FILES= \
  splitVector.v cAU.v hF.v HMAC_spec.v NMAC_to_HMAC.v \
  GNMAC_PRF.v GHMAC_PRF.v HMAC_PRF.v

HMACEQUIV_FILES= \
  HMAC256_functional_prog.v ShaInstantiation.v XorCorrespondence.v \
  sha_padding_lemmas.v Bruteforce.v ByteBitRelations.v \
  HMAC_common_defs.v HMAC_spec_pad.v HMAC256_spec_pad.v \
  HMAC_spec_concat.v HMAC256_spec_concat.v \
  HMAC_spec_list.v HMAC256_spec_list.v \
  HMAC_spec_abstract.v HMAC_equivalence.v HMAC256_equivalence.v \
  HMAC_isPRF.v HMAC256_isPRF.v

TWEETNACL_FILES = \
  Salsa20.v Snuffle.v \
  tweetNaclBase.v  verif_salsa_base.v tweetnaclVerifiableC.v spec_salsa.v \
  verif_ld_st.v  verif_fcore_epilogue_htrue.v verif_fcore_epilogue_hfalse.v \
  split_array_lemmas.v verif_fcore_loop1.v verif_fcore_loop2.v \
  verif_fcore_jbody.v verif_fcore_loop3.v verif_fcore.v \
  verif_crypto_core.v

C_FILES = reverse.c queue.c sumarray.c message.c insertionsort.c float.c nest3.c nest2.c nest3.c dotprod.c string.c field_loadstore.c ptr_compare.c merge.c

FILES = \
 $(MSL_FILES:%=msl/%) \
 $(SEPCOMP_FILES:%=sepcomp/%) \
 $(VERIC_FILES:%=veric/%) \
 $(FLOYD_FILES:%=floyd/%) \
 $(PROGS_FILES:%=progs/%) \
 $(SHA_FILES:%=sha/%) \
 $(HMAC_FILES:%=sha/%) \
 $(FCF_FILES:%=fcf/%) \
 $(HMACFCF_FILES:%=hmacfcf/%) \
 $(HMACEQUIV_FILES:%=sha/%) \
 $(TWEETNACL_FILES:%=tweetnacl20140427/%)

%_stripped.v: %.v
# e.g., 'make progs/verif_reverse_stripped.v will remove the tutorial comments
# from progs/verif_reverse.v
	grep -v '^.[*][*][ )]' $*.v >$@

%.vo: %.v
	@echo COQC $*.v
ifeq ($(TIMINGS), true)
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQFLAGS) $*.v; date +'%s.%N after' >>timings" 2>>timings
	echo -n $*.v " " >>TIMINGS; bash -c "/usr/bin/time -o TIMINGS -a $(COQC) $(COQFLAGS) $*.v"
else
	@$(COQC) $(COQFLAGS) $*.v
endif

COQVERSION=8.4pl5 or-else 8.4pl6 or-else 8.4pl4
COQV=$(shell $(COQC) -v)
ifeq ("$(filter $(COQVERSION),$(COQV))","")
$(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
endif

#compcert/%.vo: compcert/%.v
#	()

default_target: msl veric floyd progs

all:     .loadpath version.vo $(FILES:.v=.vo)

msl:     .loadpath version.vo $(MSL_FILES:%.v=msl/%.vo)
sepcomp: .loadpath $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo)
linking: .loadpath $(LINKING_FILES:%.v=linking/%.vo) 
veric:   .loadpath $(VERIC_FILES:%.v=veric/%.vo)
floyd:   .loadpath $(FLOYD_FILES:%.v=floyd/%.vo)
progs:   .loadpath $(PROGS_FILES:%.v=progs/%.vo)
sha:     .loadpath $(SHA_FILES:%.v=sha/%.vo)
hmac:    .loadpath $(HMAC_FILES:%.v=sha/%.vo)
hmacequiv:    .loadpath $(HMAC_FILES:%.v=sha/%.vo)
fcf:     .loadpath $(FCF_FILES:%.v=fcf/%.vo)
hmacfcf: .loadpath $(HMACFCF_FILES:%.v=hmacfcf/%.vo)
tweetnacl: .loadpath $(TWEETNACL_FILES:%.v=tweetnacl20140427/%.vo)
hmac0: .loadpath sha/verif_hmac_init.vo sha/verif_hmac_cleanup.vo sha/verif_hmac_final.vo sha/verif_hmac_simple.vo  sha/verif_hmac_double.vo sha/verif_hmac_update.vo sha/verif_hmac_crypto.vo

CGFLAGS =  -DCOMPCERT

CVFILES = progs/revarray.v progs/reverse.v progs/queue.v progs/sumarray.v \
         progs/message.v progs/insertionsort.v progs/float.v progs/logical_compare.v \
         progs/nest2.v progs/nest3.v progs/dotprod.v progs/string.v progs/even.v progs/odd.v \
         progs/merge.v

cvfiles: $(CVFILES)

clean_cvfiles: 
	rm $(CVFILES)

ifdef CLIGHTGEN
sha/hmac091c.v: sha/hmac091c.c
	$(CLIGHTGEN) ${CGFLAGS} $<
sha/hmac_NK.v: sha/hmac_NK.c
	$(CLIGHTGEN) ${CGFLAGS} $<
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
progs/ptr_compare.v: progs/ptr_compare.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/dotprod.v: progs/dotprod.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/string.v: progs/string.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/even.v: progs/even.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/odd.v: progs/odd.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/field_loadstore.v: progs/field_loadstore.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/merge.v: progs/merge.c
	$(CLIGHTGEN) ${CGFLAGS} $<
endif

version.v:  $(MSL_FILES:%=msl/%) $(SEPCOMP_FILES:%=sepcomp/%) $(VERIC_FILES:%=veric/%) $(FLOYD_FILES:%=floyd/%)
	sh util/make_version

.loadpath: Makefile
	echo $(INCLUDE) >.loadpath

floyd/floyd.coq: floyd/proofauto.vo
	coqtop $(COQFLAGS) -load-vernac-object floyd/proofauto -outputstate floyd/floyd -batch

.depend:
	$(COQDEP) $(DEPFLAGS) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend

depend:	
	$(COQDEP) $(DEPFLAGS) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend

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
