# See the file BUILD_ORGANIZATION for
# explanations of why this is the way it is

default_target: msl veric floyd progs

COMPCERT ?= compcert
-include CONFIGURE
#Note:  You can make a CONFIGURE file with the definition
#   COMPCERT=../compcert
# if, for example, you want to build from a compcert distribution
# that is sitting in a sister directory to vst.
# One might think that one could change this to  COMPCERT=/home/appel/compcert
# if there is a compcert build at that pathname, but in cygwin
# at least, coqdep is confused by the absolute pathname while
# it works fine with the relative pathname
#
# One can also add in CONFIGURE the line
#   COQBIN=/path/to/bin/
# to a directory containing the coqc/coqdep/... you wish to use, if it
# is not your path.

#Note2:  By default, the rules for converting .c files to .v files
# are inactive.  To activate them, do something like
CLIGHTGEN=$(COMPCERT)/clightgen 

#Note3: for SSReflect, one solution is to install MathComp 1.6
# somewhere add this line to a CONFIGURE file
# MATHCOMP=/my/path/to/mathcomp

CC_TARGET=compcert/cfrontend/Clight.vo
CC_DIRS= lib common cfrontend exportclight
DIRS= msl sepcomp veric concurrency floyd progs sha linking fcf hmacfcf tweetnacl20140427 ccc26x86 hmacdrbg
INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -Q $(a) $(a))) -Q $(COMPCERT) compcert $(if $(MATHCOMP), -Q mathcomp $(MATHCOMP))
#Replace the INCLUDE above with the following in order to build the linking target:
#INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -I $(a) -as $(a))) -R $(COMPCERT) -as compcert -I $(SSREFLECT)/src -R $(SSREFLECT)/theories -as Ssreflect \
#  -R $(MATHCOMP)/theories -as MathComp
# $(foreach a,$(CC_DIRS), -R $(COMPCERT)/$(a) -as compcert.$(a)) -I $(COMPCERT)/flocq -as compcert.flocq
CONCUR = concurrency

CV1=$(shell cat compcert/VERSION)
CV2=$(shell cat $(COMPCERT)/VERSION)

ifneq ($(CV1), $(CV2))
 $(error COMPCERT_VERSION=$(CV1) but $(COMPCERT)/VERSION=$(CV2))
endif

ifeq ($(wildcard $(COMPCERT)/*/Clight.vo), )
ifeq ($(COMPCERT), compcert)
else
 $(error FIRST BUILD COMPCERT, by:  cd $(COMPCERT); make clightgen)
endif
endif

EXTFLAGS= -R $(COMPCERT) compcert

# for SSReflect
ifdef MATHCOMP
 EXTFLAGS:=$(EXTFLAGS) -R $(MATHCOMP) mathcomp
endif

COQFLAGS=$(foreach d, $(DIRS), $(if $(wildcard $(d)), -Q $(d) $(d))) $(EXTFLAGS)
DEPFLAGS:=$(COQFLAGS)

ifdef LIBPREFIX
 COQFLAGS=$(foreach d, $(DIRS), $(if $(wildcard $(d)), -Q $(d) $(LIBPREFIX).$(d))) $(EXTFLAGS)
endif

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

MSL_FILES = \
  Axioms.v Extensionality.v base.v eq_dec.v sig_isomorphism.v \
  ageable.v sepalg.v psepalg.v age_sepalg.v \
  sepalg_generators.v functors.v sepalg_functors.v combiner_sa.v \
  cross_split.v join_hom_lemmas.v cjoins.v \
  boolean_alg.v tree_shares.v shares.v pshares.v \
  knot.v knot_prop.v \
  knot_lemmas.v knot_unique.v \
  knot_hered.v \
  knot_full.v knot_full_variant.v knot_shims.v knot_full_sa.v \
  corable.v corable_direct.v \
  predicates_hered.v predicates_sl.v subtypes.v subtypes_sl.v \
  contractive.v predicates_rec.v \
  msl_direct.v msl_standard.v msl_classical.v \
  predicates_sa.v \
  normalize.v \
  env.v corec.v Coqlib2.v sepalg_list.v op_classes.v \
  simple_CCC.v seplog.v alg_seplog.v alg_seplog_direct.v log_normalize.v ramification_lemmas.v

SEPCOMP_FILES = \
  Address.v \
  step_lemmas.v \
  extspec.v \
  rg_lemmas.v \
  FiniteMaps.v \
  mem_lemmas.v mem_wd.v \
  nucular_semantics.v \
  semantics.v semantics_lemmas.v \
  globalSep.v simulations.v \
  simulations_lemmas.v \
  structured_injections.v \
  effect_semantics.v effect_simulations.v effect_simulations_lemmas.v \
  effect_properties.v \
  event_semantics.v \
  full_composition.v \
  closed_safety.v compcert.v \
  val_casted.v \
  reach.v \
  arguments.v \
  internal_diagram_trans.v \
  wholeprog_simulations.v \
  wholeprog_lemmas.v

# what is:  erasure.v context.v context_equiv.v jstep.v 

CONCUR_FILES= \
  addressFiniteMap.v cast.v compcert_imports.v \
  compcert_linking.v compcert_linking_lemmas.v \
  compcert_threads_lemmas.v threadPool.v  \
  concurrent_machine.v disjointness.v dry_context.v dry_machine.v dry_machine_lemmas.v \
  ClightSemantincsForMachines.v JuicyMachineModule.v DryMachineSource.v \
  erased_machine.v erasure_proof.v erasure_safety.v erasure_signature.v \
  fineConc_safe.v inj_lemmas.v join_sm.v juicy_machine.v \
  lksize.v \
  main.v mem_obs_eq.v memory_lemmas.v permissions.v permjoin_def.v pos.v pred_lemmas.v \
  rc_semantics.v rc_semantics_lemmas.v \
  scheduler.v sepcomp.v seq_lemmas.v ssromega.v stack.v \
  threads_lemmas.v wf_lemmas.v \
  x86_inj.v x86_safe.v x86_context.v fineConc_x86.v executions.v SC_erasure.v \
  sync_preds_defs.v sync_preds.v \
  semax_conc_pred.v semax_conc.v semax_to_juicy_machine.v \
  semax_invariant.v semax_initial.v \
  semax_simlemmas.v cl_step_lemmas.v \
  semax_progress.v semax_preservation.v \
  semax_preservation_jspec.v \
  semax_preservation_local.v \
  semax_preservation_acquire.v \
  semax_preservation_release.v \
  semax_preservation_makelock.v \
  semax_preservation_freelock.v \
  semax_preservation_spawn.v \
  aging_lemmas.v resource_decay_lemmas.v \
  rmap_locking.v \
  permjoin.v \
  resource_decay_join.v join_lemmas.v coqlib5.v age_to.v \
  konig.v safety.v \
  reach_lemmas.v \
	reestablish.v ret_lemmas.v \
	lifting.v lifting_safety.v linking_inv.v linking_spec.v call_lemmas.v  \
  machine_semantics.v machine_semantics_lemmas.v machine_simulation.v \
  coinductive_safety.v

PACO_FILES= \
  hpattern.v\
  paco.v\
  paco0.v\
  paco1.v\
  paco2.v\
  paco3.v\
  paco4.v\
  paco5.v\
  paco6.v\
  paco7.v\
  pacodef.v\
  paconotation.v\
  pacotac.v\
  pacotacuser.v\
  tutorial.v

CCC26x86_FILES = \
  Archi.v Bounds.v Conventions1.v Conventions.v Separation.v \
  Decidableplus.v Locations.v Op.v Ordered.v Stacklayout.v Linear.v LTL.v \
  Machregs.v Asm.v \
  Switch.v Cminor.v \
  I64Helpers.v BuiltinEffects.v load_frame.v Asm_coop.v Asm_eff.v \
  Asm_nucular.v Asm_event.v \
  Clight_coop.v Clight_eff.v

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
  base.v Memory.v shares.v rmaps.v rmaps_lemmas.v compcert_rmaps.v Cop2.v juicy_base.v \
  tycontext.v lift.v expr.v expr2.v environ_lemmas.v binop_lemmas.v binop_lemmas2.v \
  expr_lemmas.v expr_lemmas2.v expr_lemmas3.v expr_rel.v xexpr_rel.v extend_tc.v \
  Clight_lemmas.v Clight_new.v Clightnew_coop.v Clight_sim.v \
  slice.v res_predicates.v seplog.v mapsto_memory_block.v assert_lemmas.v  ghost.v \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_safety.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v semax_congruence.v \
  initial_world.v initialize.v semax_prog.v semax_ext.v SeparationLogic.v SeparationLogicSoundness.v  \
  NullExtension.v SequentialClight.v superprecise.v jstep.v address_conflict.v valid_pointer.v coqlib4.v \
  semax_ext_oracle.v mem_lessdef.v

FLOYD_FILES= \
   coqlib3.v base.v library.v proofauto.v computable_theorems.v \
   type_induction.v reptype_lemmas.v aggregate_type.v aggregate_pred.v \
   nested_pred_lemmas.v compact_prod_sum.v zlist.v \
   sublist.v smt_test.v extract_smt.v \
   client_lemmas.v canon.v canonicalize.v assert_lemmas.v closed_lemmas.v jmeq_lemmas.v \
   compare_lemmas.v sc_set_load_store.v \
   loadstore_mapsto.v loadstore_field_at.v field_compat.v nested_loadstore.v \
   call_lemmas.v extcall_lemmas.v forward_lemmas.v forward.v \
   entailer.v globals_lemmas.v local2ptree.v fieldlist.v mapsto_memory_block.v\
   nested_field_lemmas.v efield_lemmas.v proj_reptype_lemmas.v replace_refill_reptype_lemmas.v \
   data_at_rec_lemmas.v field_at.v stronger.v \
   for_lemmas.v semax_tactics.v expr_lemmas.v diagnosis.v simple_reify.v simpl_reptype.v \
   freezer.v 
#real_forward.v


PROGS_FILES= \
  bin_search.v list_dt.v verif_reverse.v verif_queue.v verif_queue2.v verif_sumarray.v \
  insertionsort.v reverse.v queue.v sumarray.v message.v string.v\
  revarray.v verif_revarray.v insertionsort.v append.v \
  verif_float.v verif_global.v verif_ptr_compare.v \
  verif_nest3.v verif_nest2.v \
  logical_compare.v verif_logical_compare.v field_loadstore.v  verif_field_loadstore.v \
  even.v verif_even.v odd.v verif_odd.v \
  merge.v verif_merge.v verif_append.v verif_append2.v bst.v verif_bst.v \
  verif_bin_search.v incr.v verif_incr.v cond.v verif_cond.v conclib.v
# verif_message.v verif_dotprod.v verif_insertion_sort.v 

SHA_FILES= \
  general_lemmas.v SHA256.v common_lemmas.v pure_lemmas.v sha_lemmas.v functional_prog.v \
  sha.v spec_sha.v verif_sha_init.v \
  verif_sha_update.v verif_sha_update3.v verif_sha_update4.v \
  bdo_lemmas.v verif_sha_bdo.v  \
  verif_sha_bdo4.v verif_sha_bdo7.v verif_sha_bdo8.v \
  verif_sha_final2.v verif_sha_final3.v verif_sha_final.v \
  verif_addlength.v verif_SHA256.v call_memcpy.v

HMAC_FILES= \
  HMAC_functional_prog.v HMAC256_functional_prog.v \
  vst_lemmas.v hmac_pure_lemmas.v hmac_common_lemmas.v \
  hmac.v spec_hmac.v verif_hmac_cleanup.v \
  verif_hmac_init_part1.v verif_hmac_init_part2.v verif_hmac_init.v\
  verif_hmac_update.v verif_hmac_final.v verif_hmac_simple.v \
  verif_hmac_double.v verif_hmac_crypto.v protocol_spec_hmac.v

FCF_FILES= \
  Admissibility.v Encryption.v NotationV1.v RndDup.v \
  Array.v Encryption_2W.v NotationV2.v RndGrpElem.v \
  Asymptotic.v  Encryption_PK.v OracleCompFold.v RndInList.v \
  Bernoulli.v EqDec.v OracleHybrid.v RndListElem.v \
  Blist.v ExpectedPolyTime.v OTP.v RndNat.v \
  Class.v FCF.v PRF.v RndPerm.v \
  Comp.v Fold.v PRF_Convert.v SemEquiv.v \
  CompFold.v GenTacs.v PRG.v Sigma.v \
  ConstructedFunc.v GroupTheory.v Procedure.v State.v \
  Crypto.v HasDups.v ProgramLogic.v StdNat.v \
  DetSem.v Hybrid.v ProgTacs.v Tactics.v \
  DiffieHellman.v Limit.v PRP_PRF.v TwoWorldsEquiv.v \
  DistRules.v ListHybrid.v RandPermSwitching.v WC_PolyTime.v \
  DistSem.v Lognat.v Rat.v WC_PolyTime_old.v \
  DistTacs.v NoDup_gen.v RepeatCore.v


#FCF_FILES= \
#  Limit.v Blist.v StdNat.v Rat.v EqDec.v Fold.v Comp.v DetSem.v DistSem.v \
#  DistRules.v DistTacs.v ProgTacs.v GenTacs.v Crypto.v SemEquiv.v \
#  ProgramLogic.v RndNat.v Bernoulli.v FCF.v HasDups.v CompFold.v \
#  RepeatCore.v PRF_Encryption_IND_CPA.v PRF.v Array.v Encryption.v \
#  Asymptotic.v Admissibility.v RndInList.v OTP.v RndGrpElem.v \
#  GroupTheory.v WC_PolyTime.v RndListElem.v RndPerm.v NoDup_gen.v \
#  Hybrid.v OracleCompFold.v PRF_Convert.v

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
  split_array_lemmas.v Salsa20.v Snuffle.v tweetNaclBase.v \
  verif_salsa_base.v tweetnaclVerifiableC.v spec_salsa.v \
  verif_ld_st.v verif_fcore_loop1.v verif_fcore_loop2.v \
  verif_fcore_jbody.v verif_fcore_loop3.v \
  verif_fcore_epilogue_hfalse.v verif_fcore_epilogue_htrue.v \
  verif_fcore.v verif_crypto_core.v \
  verif_crypto_stream_salsa20_xor.v verif_crypto_stream.v

HMACDRBG_FILES = \
  entropy.v entropy_lemmas.v DRBG_functions.v HMAC_DRBG_algorithms.v \
  HMAC256_DRBG_functional_prog.v HMAC_DRBG_pure_lemmas.v \
  HMAC_DRBG_update.v \
  mocked_md.v mocked_md_compspecs.v hmac_drbg.v hmac_drbg_compspecs.v \
  spec_hmac_drbg.v spec_hmac_drbg_pure_lemmas.v \
  HMAC_DRBG_common_lemmas.v  HMAC_DRBG_pure_lemmas.v \
  verif_hmac_drbg_update.v verif_hmac_drbg_reseed.v \
  verif_hmac_drbg_generate.v verif_hmac_drbg_seed_buf.v verif_mocked_md.v \
  verif_hmac_drbg_seed.v verif_hmac_drbg_NISTseed.v verif_hmac_drbg_other.v

# DRBG_Files = \
#  hmac_drbg.v HMAC256_DRBG_functional_prog.v hmac_drbg_compspecs.v \
#  entropy.v DRBG_functions.v HMAC_DRBG_algorithms.v spec_hmac_drbg.v \
#  HMAC_DRBG_pure_lemmas.v HMAC_DRBG_common_lemmas.v verif_mocked_md.v \
#  verif_hmac_drbg_update.v verif_hmac_drbg_reseed.v verif_hmac_drbg_generate.v


C_FILES = reverse.c queue.c queue2.c sumarray.c sumarray2.c message.c insertionsort.c float.c global.c nest3.c nest2.c nest3.c dotprod.c string.c field_loadstore.c ptr_compare.c merge.c append.c bst.c

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
 $(CCC26x86_FILES:%=ccc26x86/%) \
 $(TWEETNACL_FILES:%=tweetnacl20140427/%) \
 $(HMACDRBG_Files:%=hmacdrbg/%)
#$(CONCUR_FILES:%=concurrency/%)
# $(DRBG_FILES:%=verifiedDrbg/spec/%)

%_stripped.v: %.v
# e.g., 'make progs/verif_reverse_stripped.v will remove the tutorial comments
# from progs/verif_reverse.v
	grep -v '^.[*][*][ )]' $*.v >$@

%.vo: %.v
	@echo COQC $*.v
ifeq ($(TIMINGS), true)
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQFLAGS) $*.v; date +'%s.%N after' >>timings" 2>>timings
	@bash -c "/bin/time --output=TIMINGS -a -f '%e real, %U user, %S sys, '\"$(shell wc $*.v)\" $(COQC) $(COQFLAGS) $*.v"
#	echo -n $*.v " " >>TIMINGS; bash -c "/usr/bin/time -o TIMINGS -a $(COQC) $(COQFLAGS) $*.v"
else
	@$(COQC) $(COQFLAGS) $*.v
endif

COQVERSION= 8.5pl1 or-else 8.5pl2 or-else 8.5pl3
COQV=$(shell $(COQC) -v)
ifeq ("$(filter $(COQVERSION),$(COQV))","")
$(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
endif


$(COMPCERT)/lib/%.vo: $(COMPCERT)/lib/%.v
	@
$(COMPCERT)/common/%.vo: $(COMPCERT)/common/%.v
	@
$(COMPCERT)/cfrontend/%.vo: $(COMPCERT)/cfrontend/%.v
	@
$(COMPCERT)/exportclight/%.vo: $(COMPCERT)/exportclight/%.v
	@
$(COMPCERT)/flocq/Appli/%.vo: $(COMPCERT)/flocq/Appli/%.v
	@
$(COMPCERT)/flocq/Calc/%.vo: $(COMPCERT)/flocq/Calc/%.v
	@
$(COMPCERT)/flocq/Core/%.vo: $(COMPCERT)/flocq/Core/%.v
	@
$(COMPCERT)/flocq/Prop/%.vo: $(COMPCERT)/flocq/Prop/%.v
	@
$(COMPCERT)/flocq/%.vo: $(COMPCERT)/flocq/%.v
	@

all:     .loadpath version.vo $(FILES:.v=.vo)


ifeq ($(COMPCERT), compcert)
compcert: $(COMPCERT)/exportclight/Clightdefs.vo
$(COMPCERT)/exportclight/Clightdefs.vo: 
	cd $(COMPCERT) && $(MAKE) exportclight/Clightdefs.vo
$(patsubst %.v,sepcomp/%.vo,$(SEPCOMP_FILES)): compcert
$(patsubst %.v,veric/%.vo,$(VERIC_FILES)): compcert
$(patsubst %.v,floyd/%.vo,$(FLOYD_FILES)): compcert
msl/Coqlib2.vo: compcert
endif

msl:     .loadpath version.vo $(MSL_FILES:%.v=msl/%.vo)
sepcomp: .loadpath $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo)
ccc26x86:   .loadpath $(CCC26x86_FILES:%.v=ccc26x86/%.vo)
concurrency: .loadpath $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo) $(CONCUR_FILES:%.v=concurrency/%.vo)
paco: .loadpath $(PACO_FILES:%.v=concurrency/paco/src/%.vo)
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
hmacdrbg:   .loadpath $(HMACDRBG_FILES:%.v=hmacdrbg/%.vo)
# drbg: .loadpath $(DRBG_FILES:%.v=verifiedDrbg/%.vo)

CGFLAGS =  -DCOMPCERT

$(patsubst %.c,progs/%.vo,$(C_FILES)): compcert

cvfiles: $(CVFILES)



clean_cvfiles: 
	rm $(CVFILES)

ifdef CLIGHTGEN
sha/sha.v sha/hmac.v hmacdrbg/hmac_drbg.v: sha/sha.c sha/hmac.c hmacdrbg/hmac_drbg.c
	$(CLIGHTGEN) ${CGFLAGS} sha/sha.c sha/hmac.c hmacdrbg/hmac_drbg.c
# Is there a way to generate the next 5 rules automatically from C_FILES? 
progs/revarray.v: progs/revarray.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/reverse.v: progs/reverse.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/queue.v: progs/queue.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/queue2.v: progs/queue2.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/sumarray.v: progs/sumarray.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/sumarray2.v: progs/sumarray2.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/message.v: progs/message.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/insertionsort.v: progs/insertionsort.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/float.v: progs/float.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/global.v: progs/global.c
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
progs/even.v: progs/even.c progs/odd.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/odd.v: progs/even.v
progs/field_loadstore.v: progs/field_loadstore.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/merge.v: progs/merge.c
	$(CLIGHTGEN) ${CGFLAGS} $<
progs/append.v: progs/append.c
	$(CLIGHTGEN) ${CGFLAGS} $<
endif

version.v:  VERSION $(MSL_FILES:%=msl/%) $(SEPCOMP_FILES:%=sepcomp/%) $(VERIC_FILES:%=veric/%) $(FLOYD_FILES:%=floyd/%)
	sh util/make_version

.loadpath: Makefile
	echo $(COQFLAGS) > .loadpath

floyd/floyd.coq: floyd/proofauto.vo
	coqtop $(COQFLAGS) -load-vernac-object floyd/proofauto -outputstate floyd/floyd -batch

dep:
	$(COQDEP) $(shell find . -name "*.v")  > .depend

.depend:
	$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend

depend:	
	$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend
dependx:	
	$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend
	$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(SEPCOMP_FILES:%=sepcomp/%) $(CONCUR_FILES:%=concurrency/%))  >> .depend

depend-linking:
	$(COQDEP) $(FILES) $(LINKING_FILES:%.v=linking/%.v) > .depend

depend-concur:
	$(COQDEP) > .depend-concur $(CONCUR_FILES:%.v=concurrency/%.v) $(PACO_FILES:%.v=concurrency/paco/src/%.v) $(CCC26x86_FILES:%.v=concurrency/%.v)

depend-paco:
	$(COQDEP) > .depend-paco $(PACO_FILES:%.v=concurrency/paco/src/%.v)

clean:
	rm -f $(FILES:%.v=%.vo) $(FILES:%.v=%.glob) floyd/floyd.coq .loadpath .depend

clean-concur:
	rm -f $(CONCUR_FILES:%.v=%.vo) $(CONCUR_FILES:%.v=%.glob)

clean-linking:
	rm -f $(LINKING_FILES:%.v=linking/%.vo) $(LINKING_FILES:%.v=linking/%.glob) 

count:
	wc $(FILES)

count-linking:
	wc $(LINKING_FILES:%.v=linking/%.v)

# $(CC_TARGET): compcert/make
#	(cd compcert; ./make)

# The .depend file is divided into two parts, .depend and .depend-concur,
# in order to work around a limitation in Cygwin about how long one
# command line can be.  (Or at least, it seems to be a solution to some
# such problem, not sure exactly.  -- Andrew)
include .depend
-include .depend-concur
