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

COQFLAGS= $(INCLUDE)
DEPFLAGS= $(INCLUDE)
COQC=coqc
COQTOP=coqtop
COQDEP=coqdep
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
  Address.v step_lemmas.v Coqlib2.v \
  extspec.v \
  wf_lemmas.v mem_lemmas.v mem_interpolants.v mem_interpolation_defs.v \
  mem_interpolation_EE.v mem_interpolation_EI.v \
  mem_interpolation_IE.v mem_interpolation_II.v \
  mem_interpolation_proofs.v \
  compile_safe.v \
  core_semantics.v forward_simulations.v rg_forward_simulations.v \
  forward_simulations_lemmas.v \
  extension.v extension_safety.v extension_simulations.v \
  extension_proof_safety.v extension_proof.v \
  null_extension.v fs_extension.v linking_extension.v trace_extension.v \
  mem_interpolants.v compiler_correctness_trans.v \
  compcert_compiler_correctness.v RG_interpolants.v rgsim.v

VERIC_FILES= \
  base.v rmaps.v rmaps_lemmas.v compcert_rmaps.v \
  lift.v expr.v environ_lemmas.v binop_lemmas.v expr_lemmas.v \
  Clight_lemmas.v Clight_new.v Clight_sim.v \
  slice.v res_predicates.v seplog.v assert_lemmas.v  ghost.v \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_mem_ops.v juicy_extspec.v \
  juicy_linking_extension.v \
  semax.v semax_lemmas.v semax_call.v semax_straight.v semax_loop.v \
  initial_world.v initialize.v semax_prog.v SeparationLogic.v SeparationLogicSoundness.v \
  NullExtension.v SequentialClight.v

FLOYD_FILES= \
   base.v proofauto.v malloc_lemmas.v \
   client_lemmas.v canonicalize.v assert_lemmas.v field_mapsto.v \
   call_lemmas.v forward_lemmas.v forward.v 

PROGS_FILES= \
  list_dt.v verif_reverse.v verif_queue.v verif_sumarray.v verif_message.v \
  reverse.v queue.v sumarray.v message.v

FILES = \
 $(MSL_FILES:%=msl/%) \
 $(SEPCOMP_FILES:%=sepcomp/%) \
 $(VERIC_FILES:%=veric/%) \
 $(FLOYD_FILES:%=floyd/%) \
 $(PROGS_FILES:%=progs/%) 

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQFLAGS) $*.v

compcert/%.vo: compcert/%.v
	()

all:     .loadpath $(FILES:.v=.vo)

msl:     .loadpath $(MSL_FILES:%.v=msl/%.vo)
sepcomp: .loadpath $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo)
veric:   .loadpath $(VERIC_FILES:%.v=veric/%.vo)
floyd:   .loadpath $(FLOYD_FILES:%.v=floyd/%.vo) floyd/floyd.coq
progs:   .loadpath $(PROGS_FILES:%.v=progs/%.vo)

.loadpath: Makefile
	echo $(INCLUDE) >.loadpath

floyd/floyd.coq: floyd/proofauto.vo
	coqtop -load-vernac-source floyd/proofauto -outputstate floyd/floyd -batch

depend:
	$(COQDEP) $(DEPFLAGS) $(FILES) > .depend

clean:
	rm -f $(FILES:%.v=%.vo) $(FILES:%.v=%.glob) floyd/floyd.coq .loadpath

count:
	wc $(FILES)

$(CC_TARGET): compcert/make
	(cd compcert; ./make)

include .depend
