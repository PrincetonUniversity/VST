# ########## Configuration ##########

# See the file BUILD_ORGANIZATION.md
# for explanations of why this is the way it is.

-include CONFIGURE

# ##### Configure Coq #####

# ANNOTATE=true   # label chatty output from coqc with file name
ANNOTATE=silent   # suppress chatty output from coqc
# ANNOTATE=false  # leave chatty output of coqc unchanged
# ANNOTATE=echo   # like false, but in addition echo commands

# DO NOT DISABLE coqc WARNINGS!  That would hinder the Coq team's continuous integration.
COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep -vos
COQDOC=$(COQBIN)coqdoc -d doc/html -g  $(DEPFLAGS)
COQLIB=$(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')

# Check Coq version

COQVERSION= 8.19.1 or-else 8.19.2 or-else 8.20.0 or-else 8.20.1

COQV=$(shell $(COQC) -v)
ifneq ($(IGNORECOQVERSION),true)
  ifeq ("$(filter $(COQVERSION),$(COQV))","")
    $(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
  endif
endif

# ##### Configure Compcert #####

# Note:  You can make a CONFIGURE file with the below definitions or give them
# on the make command line
#
# # Choosing compcert #
# COMPCERT=platform     (default, choose 32 or 64 bit platform supplied x86 variant, dependent on BITSIZE, ARCH can be left empty or must be x86)
# COMPCERT=bundled      (build and use bundled 32 or 64 x86 variant, dependent on BITSIZE, ARCH can be left empty or must be x86)
# COMPCERT=bundled_new  (build and use bundled compcert_new 32 or 64 x86 variant, dependent on BITSIZE, ARCH can be left empty or must be x86)
# COMPCERT=src_dir      (build and use in source folder COMPCERT_SRC_DIR the variant specified by ARCH and BITSIZE)
# COMPCERT=inst_dir     (use prebuilt CompCert in COMPCERT_INST_DIR - BITSIZE and ARCH can be left empty or must match)
#
# # Choosing VST zlist #
# ZLIST=platform     (use zlist from installed library)
# ZLIST=bundled      (default, build and use bundled zlist)
#
# # Choosing BITSIZE #
# BITSIZE=32 
# BITSIZE=64
#
# # Choosing ARCHITECTURE #
# ARCH=x86
# ARCH=aarch64
# ARCH=powerpc
#
# # Choosing Flocq #
# FLOCQ=platform (default, except for COMPCERT_BUNDLED_NEW)
# FLOCQ=bundled  (require for COMPCERT_BUNDLED_NEW, valid for COMPCERT_BUNDLED, COMPCERT_SRC_DIR)
#
# # Choosing Clightgen
# Note:  By default, the rules for converting .c files to .v files are inactive.
# To activate them, define
# CLIGHTGEN=$(my_local_bin_path)/clightgen

# # User settable variables #
COMPCERT ?= bundled
ZLIST ?= bundled
ARCH ?= 
BITSIZE ?= 64

# # Internal variables #
# Set to true if the bundled CompCert is used
COMPCERT_NEW = false
# Relative path to bundled compcert for version comparison
COMPCERT_INFO_PATH_REF = compcert
# Set to true if the Coq module path for compcert needs to be set explicitly
COMPCERT_EXPLICIT_PATH = true
# Set to true if building from sources
COMPCERT_BUILD_FROM_SRC = false

ifeq ($(COMPCERT),platform)
  # Platform supplied CompCert
  ifeq ($(BITSIZE),)
    COMPCERT_INST_DIR = $(COQLIB)/user-contrib/compcert
    COMPCERT_EXPLICIT_PATH = false
  else ifeq ($(BITSIZE),64)
    COMPCERT_INST_DIR = $(COQLIB)/user-contrib/compcert
    COMPCERT_EXPLICIT_PATH = false
  else ifeq ($(BITSIZE),32)
    COMPCERT_INST_DIR = $(COQLIB)/../coq-variant/compcert32/compcert
  else 
    $(error ILLEGAL BITSIZE $(BITSIZE))
  endif
  COMPCERT_SRC_DIR = __NONE__
else ifeq ($(COMPCERT),bundled)
  # Bundled CompCert
  COMPCERT_SRC_DIR = compcert
  COMPCERT_INST_DIR = compcert
  COMPCERT_BUILD_FROM_SRC = true
else ifeq ($(COMPCERT),bundled_new)
  # Bundled CompCert (new variant)
  COMPCERT_SRC_DIR = compcert_new
  COMPCERT_INST_DIR = compcert_new
  COMPCERT_NEW = true
  COMPCERT_INFO_PATH_REF = compcert_new
  COMPCERT_BUILD_FROM_SRC = true
else ifeq ($(COMPCERT),src_dir)
  # Compile CompCert from source dir
  ifeq ($(COMPCERT_SRC_DIR),)
    $(error COMPCERT_SRC_DIR must not be empty if COMPCERT=src_dir)
  endif
  COMPCERT_INST_DIR = $(COMPCERT_SRC_DIR)
  COMPCERT_BUILD_FROM_SRC = true
else ifeq ($(COMPCERT),inst_dir)
  # Find CompCert in install dir
  COMPCERT_SRC_DIR = __NONE__
  ifeq ($(COMPCERT_INST_DIR),)
    $(error COMPCERT_INST_DIR must not be empty if COMPCERT=inst_dir)
  endif
endif

# Verify that the version of the supplied compcert matches the version of the internal compcert

CV1=$(shell cat $(COMPCERT_INFO_PATH_REF)/VERSION | grep "version=")
CV2=$(shell cat $(COMPCERT_INST_DIR)/VERSION | grep "version=")

ifneq ($(IGNORECOMPCERTVERSION),true)
  ifneq ($(CV1), $(CV2))
    $(error COMPCERT VERSION MISMATCH: COMPCERT_VERSION=$(CV1) but $(COMPCERT_INST_DIR)/VERSION=$(CV2))
  endif
endif

# Verify that the version of the supplied clightgen matches the version of the internal compcert

COMPCERT_VERSION=$(subst version=,,$(shell grep version $(COMPCERT_INFO_PATH_REF)/VERSION))

ifdef CLIGHTGEN
  VERSION1= $(lastword $(shell $(CLIGHTGEN) --version))
  ifneq ($(VERSION1),$(COMPCERT_VERSION))
    $(warning clightgen version $(VERSION1) does not match VST/$(COMPCERT_INFO_PATH_REF)/VERSION $(COMPCERT_VERSION))
  endif
endif

# Verify that the supplied compcert folder is built (contains .vo files)

ifeq ($(COMPCERT_BUILD_FROM_SRC),false)
  ifeq ($(wildcard $(COMPCERT_INST_DIR)/*/Clight.vo), )
    $(error FIRST BUILD COMPCERT, by:  cd $(COMPCERT_INST_DIR); $(MAKE) clightgen)
  endif
endif

# ##### Configure Architecture #####

ifneq ($(COMPCERT_SRC_DIR),__NONE__)
  # We are building CompCert from source and can choose BITSIZE and ARCH

  ifeq ($(BITSIZE),)
    BITSIZE = 32
  endif

  ifeq ($(ARCH),)
    ARCH = x86
  endif

else
  # We are using a pre-built CompCert, so verify that BITSIZE and ARCH match
  # or extract them from the compcert settings if they are undefined

  ifeq ($(wildcard $(COMPCERT_INST_DIR)/compcert.config),)
    $(error Cannot find compcert.config in $(COMPCERT_INST_DIR))
  endif
  
  include $(COMPCERT_INST_DIR)/compcert.config

  ifneq ($(BITSIZE),)
    ifneq ($(BITSIZE),$(COMPCERT_BITSIZE))
      $(error The compcert found in $(COMPCERT_INST_DIR) has bitsize $(COMPCERT_BITSIZE) but you requested $(BITSIZE))
    endif
  else
    BITSIZE = $(COMPCERT_BITSIZE)
  endif

  ifneq ($(ARCH),)
    ifneq ($(ARCH),$(COMPCERT_ARCH))
      $(error The compcert found in $(COMPCERT_INST_DIR) has bitsize $(COMPCERT_ARCH) but you requested $(ARCH))
    endif
  else
    ARCH = $(COMPCERT_ARCH)
  endif
endif

# Choose CompCert architecture folder

ifeq ($(wildcard $(COMPCERT_INST_DIR)/$(ARCH)_$(BITSIZE)),)
  ARCHDIRS=$(ARCH)
else
  ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

# Add CompCert backend folder for COMPCERT_NEW

ifeq ($(COMPCERT_NEW),true)
  BACKEND=backend
endif

# Choose VST programs folder

ifeq ($(BITSIZE),64)
  PROGSDIR=progs64
else
  PROGSDIR=progs
endif


# ##### Configure ssreflect / mathcomp #####

# This makefile assumes, that ssreflect / mathcomp is provided by the coq platform,
# that is found in $(coqc -where)/user-contrib/mathcomp.
# In case it is not, define in file CONFIGURE e.g.:

# MATHCOMP=/my/path/to/mathcomp
# MATHCOMP=c:/Coq/lib/user-contrib/mathcomp

# ##### Configure Flocq #####


ifeq ($(FLOCQ),bundled)
 override FLOCQ= -R $(COMPCERT_INST_DIR)/flocq Flocq 
 COMPCERTFLOCQDIRS= compcert/flocq/*/*.v
 # this mode to use the flocq built into compcert
endif
ifeq ($(FLOCQ),platform)
 undefine FLOCQ
 # this mode to use the flocq packaged with Coq or opam
endif

# ##### Configure installation folder #####
#  1. (if present) the VST installation for reasoning about 64-bit C programs
#     on the host  architecture will be in $(COQLIB)/user-contrib/VST, 
#  2. (if present) the VST installation for reasoning about 32 C programs 
#    for the 32-bit analogue of the host architecture 
#    will be in $(COQLIB)/../coq-variant/VST32/VST
#  3. (if present) a VST installation for reasoning about C programs compiled
#     for a _different_ architecture will be in 
#     $(COQLIB)/../coq-variant/VST_otherarch_bitsize/VST
#  Not all of this logic is right here in this makefile; some of it is done
#  in the CompCert install, in choosing how to configure CompCert itself,
#  creating the values of $(ARCH) and $(BITSIZE)
MACHINE_ARCH=$(shell uname -m)
X86_ALIASES:=x86 x86_32 x86_64 i686
ARM_ALIASES:=arm64 aarch64
BOTH_X86=$(and $(filter $(ARCH),$(X86_ALIASES)),$(filter $(MACHINE_ARCH),$(X86_ALIASES)))
BOTH_ARM=$(and $(filter $(ARCH),$(ARM_ALIASES)),$(filter $(MACHINE_ARCH),$(ARM_ALIASES)))
THE_SAME=$(and $(findstring $(ARCH),$(MACHINE_ARCH)),$(findstring $(MACHINE_ARCH),$(ARCH)))

ifneq ($(or $(BOTH_X86),$(BOTH_ARM),$(THE_SAME)),)
  ifeq ($(BITSIZE),64)
    INSTALLDIR ?= $(COQLIB)/user-contrib/VST
  else
    INSTALLDIR ?= $(abspath $(COQLIB)/../coq-variant/VST32/VST)
  endif
else
  INSTALLDIR ?= $(abspath $(COQLIB)/../coq-variant/VST_$(ARCH)_$(BITSIZE)/VST)
endif

# ########## Flags ##########

ifeq ($(ZLIST),platform)
  VSTDIRS= shared msl sepcomp veric floyd $(PROGSDIR) concurrency ccc26x86 atomics
else
  VSTDIRS= shared msl sepcomp veric zlist floyd $(PROGSDIR) concurrency ccc26x86 atomics
endif
OTHERDIRS= wand_demo sha hmacfcf tweetnacl20140427 hmacdrbg aes mailbox boringssl_fips_20180730
DIRS = $(VSTDIRS) $(OTHERDIRS)

# ##### Compcert Flags #####

COMPCERTDIRS=lib common $(ARCHDIRS) cfrontend export $(BACKEND)

ifeq ($(COMPCERT_EXPLICIT_PATH),true)
  COMPCERT_R_FLAGS= $(foreach d, $(COMPCERTDIRS), -R $(COMPCERT_INST_DIR)/$(d) compcert.$(d)) $(FLOCQ)
  EXTFLAGS= $(foreach d, $(COMPCERTDIRS), -Q $(COMPCERT_INST_DIR)/$(d) compcert.$(d)) $(FLOCQ) -Q ora/theories iris_ora
else
  COMPCERT_R_FLAGS=
  EXTFLAGS=
endif

# Compcert Clightgen flags

CGFLAGS =  -DCOMPCERT -short-idents

#ifeq ($(COMPCERT_NEW),true)
#SHIM= -Q concurrency/shim VST.veric
#endif

# ##### ExtLib Flags #####

# ifneq ($(wildcard coq-ext-lib/theories),)
# EXTFLAGS:=$(EXTFLAGS) -Q coq-ext-lib/theories ExtLib
# endif

# ##### Interaction Trees Flags #####

ifneq ($(wildcard InteractionTrees/theories),)
EXTFLAGS:=$(EXTFLAGS) -Q InteractionTrees/theories ITree
endif

# ##### FCF (Foundational Cryptography Framework) Flags #####

ifneq ($(wildcard fcf/src/FCF),)
EXTFLAGS:=$(EXTFLAGS) -Q fcf/src/FCF FCF
endif#

# ##### PaCo (Parameterized Coinduction) Flags #####

ifneq ($(wildcard paco/src),)
EXTFLAGS:=$(EXTFLAGS) -Q paco/src Paco
endif

# ##### SSReflect Flags #####

ifdef MATHCOMP
EXTFLAGS:=$(EXTFLAGS) -R $(MATHCOMP) mathcomp
endif

# ##### ORA Flags #####

ifneq ($(wildcard ora/theories),)
EXTFLAGS:=$(EXTFLAGS) -Q ora/theories iris_ora
endif

# ##### refinedVST Flags #####
EXTFLAGS:=$(EXTFLAGS) -Q refinedVST/lithium VST.lithium -Q refinedVST/typing VST.typing

EXTFLAGS:=$(EXTFLAGS) $(REFINEDVSTFLAGS)

# ##### Flag summary #####

COQFLAGS=$(foreach d, $(VSTDIRS), $(if $(wildcard $(d)), -Q $(d) VST.$(d))) $(foreach d, $(OTHERDIRS), $(if $(wildcard $(d)), -Q $(d) $(d))) $(EXTFLAGS) $(SHIM) # -Q ../stdpp/theories stdpp -Q ../iris/iris iris -Q ../InteractionTrees/theories ITree -Q ../paco/src Paco -Q ../coq-ext-lib/theories ExtLib -Q ../fcf/src/fcf FCF


DEPFLAGS:=$(COQFLAGS)

COQFLAGS+=$(COQEXTRAFLAGS)

PROFILING?=

ifneq (,$(PROFILING))
  # does this coq version dupport -profile ? (Coq >= 8.19)
  ifeq (,$(shell "$(COQBIN)coqc" -profile /dev/null 2>&1))
    PROFILE_FLAGS+=-profile $<.prof.json
    PROFILE_ZIP = gzip -f $<.prof.json
  else
  endif
endif
PROFILE_FLAGS ?=
PROFILE_ZIP ?= true

TIMED?=

# Use command time on linux, gtime on Mac OS
TIMEFMT?="$(if $(findstring undefined, $(flavor 1)),$@,$(1)) (real: %e, user: %U, sys: %S, mem: %M ko)"
ifneq (,$(TIMED))
ifeq (0,$(shell command time -f "" true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=command time -f $(TIMEFMT)
else
ifeq (0,$(shell gtime -f "" true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=gtime -f $(TIMEFMT)
else
STDTIME?=command time
endif
endif
else
STDTIME?=command time -f $(TIMEFMT)
endif

# ##### Print configuration summary #####

$(info ===== CONFIGURATION SUMMARY =====)
$(info COMPCERT=$(COMPCERT))
$(info COMPCERT_SRC_DIR=$(COMPCERT_SRC_DIR))
$(info COMPCERT_INST_DIR=$(COMPCERT_INST_DIR))
$(info ZLIST=$(ZLIST))
$(info BITSIZE=$(BITSIZE))
$(info ARCH=$(ARCH))
$(info INSTALLDIR=$(INSTALLDIR))
$(info ===== DERIVED CONFIGURATION =====)
$(info COMPCERT_INFO_PATH_REF=$(COMPCERT_INFO_PATH_REF))
$(info COMPCERT_EXPLICIT_PATH=$(COMPCERT_EXPLICIT_PATH))
$(info COMPCERT_BUILD_FROM_SRC=$(COMPCERT_BUILD_FROM_SRC))
$(info COMPCERT_NEW=$(COMPCERT_NEW))
$(info COQFLAGS=$(COQFLAGS))
$(info COMPCERT_R_FLAGS=$(COMPCERT_R_FLAGS))
$(info FLOCQ=$(FLOCQ))
$(info =================================)

# ########## File Lists ##########

MSL_FILES = \
  Axioms.v Extensionality.v base.v eq_dec.v \
  sepalg.v sepalg_generators.v psepalg.v \
  boolean_alg.v tree_shares.v shares.v pshares.v \
  Coqlib2.v sepalg_list.v

ORA_FILES = \
  theories/algebra/ora.v theories/algebra/excl.v theories/algebra/osum.v \
  theories/algebra/agree.v theories/algebra/gmap.v theories/algebra/functions.v \
  theories/algebra/dfrac.v theories/algebra/ext_order.v theories/algebra/view.v \
  theories/algebra/auth.v theories/algebra/excl_auth.v theories/algebra/frac_auth.v \
  theories/algebra/gmap_view.v theories/logic/oupred.v theories/logic/algebra.v \
  theories/logic/iprop.v theories/logic/derived.v theories/logic/own.v \
  theories/logic/proofmode.v theories/logic/logic.v theories/logic/wsat.v \
  theories/logic/later_credits.v theories/logic/fancy_updates.v theories/logic/invariants.v \
  theories/logic/cancelable_invariants.v theories/logic/weakestpre.v theories/logic/ghost_map.v

SEPCOMP_FILES = \
  Address.v \
  effect_semantics.v \
  event_semantics.v \
  extspec.v \
  globalSep.v \
  mem_lemmas.v \
  reach.v \
  mem_wd.v \
  semantics.v semantics_lemmas.v \
  step_lemmas.v \
  structured_injections.v

# what is:  erasure.v context.v context_equiv.v jstep.v

CONCUR_JUICY_FILES= \
  cl_step_lemmas.v erasure_proof.v erasure_safety.v erasure_signature.v \
  join_lemmas.v juicy_machine.v JuicyMachineModule.v \
  resource_decay_lemmas.v resource_decay_join.v \
  rmap_locking.v \
  semax_conc_pred.v semax_conc.v semax_to_juicy_machine.v \
  semax_invariant.v semax_initial.v \
  semax_simlemmas.v \
  semax_progress.v semax_preservation.v \
  semax_preservation_jspec.v \
  semax_preservation_local.v \
  semax_preservation_acquire.v \
  semax_safety_release.v \
  semax_safety_makelock.v \
  semax_safety_freelock.v \
  semax_safety_spawn.v \
  sync_preds_defs.v sync_preds.v

CONCUR_COMMON_FILES= \
  addressFiniteMap.v \
  bounded_maps.v \
  Clight_bounds.v ClightSemantincsForMachines.v  \
  core_semantics.v \
  dry_context.v \
  dry_machine_lemmas.v dry_machine_step_lemmas.v \
  enums_equality.v \
  erased_machine.v \
  HybridMachine.v \
  konig.v \
  lksize.v \
  machine_semantics.v machine_semantics_lemmas.v \
  permissions.v permjoin_def.v pos.v permjoin.v \
  scheduler.v \
  semantics.v \
  sepcomp.v \
  ssromega.v \
  tactics.v \
  threadPool.v konig.v \
  threads_lemmas.v \

CONCUR_COMPILER_FILES= \
  safety.v CoreSemantics_sum.v concurrent_compiler_safety_proof.v \
#  self_simulation.v Clight_self_simulation.v Asm_self_simulation.v \
#  lifting.v lifting_safety.v \
#  compiler_correct.v

CONCUR_FILES= lksize.v semax_conc.v semax_conc_pred.v \
        memsem_lemmas.v main.v memory_lemmas.v  \

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
  base.v Clight_base.v val_lemmas.v Memory.v shares.v compspecs.v juicy_base.v type_induction.v composite_compute.v align_mem.v change_compspecs.v \
  tycontext.v lift.v expr.v expr2.v environ_lemmas.v \
  binop_lemmas.v binop_lemmas2.v binop_lemmas3.v binop_lemmas4.v binop_lemmas5.v binop_lemmas6.v \
  expr_lemmas.v expr_lemmas2.v expr_lemmas3.v expr_lemmas4.v \
  extend_tc.v \
  Clight_lemmas.v Clight_core.v  \
  slice.v res_predicates.v seplog.v Clight_seplog.v mapsto_memory_block.v Clight_mapsto_memory_block.v assert_lemmas.v Clight_assert_lemmas.v \
  juicy_mem.v juicy_mem_lemmas.v local.v juicy_extspec.v \
  semax.v semax_lemmas.v semax_conseq.v semax_call.v semax_straight.v semax_loop.v semax_switch.v \
  initial_world.v Clight_initial_world.v initialize.v semax_prog.v semax_ext.v SeparationLogic.v SeparationLogicSoundness.v  \
  NullExtension.v SequentialClight.v tcb.v jstep.v address_conflict.v valid_pointer.v coqlib4.v \
  mem_lessdef.v Clight_mem_lessdef.v mpred.v

ZLIST_FILES= \
  sublist.v Zlength_solver.v list_solver.v

FLOYD_FILES= \
   coqlib3.v base.v seplog_tactics.v typecheck_lemmas.v val_lemmas.v assert_lemmas.v find_nth_tactic.v const_only_eval.v \
   base2.v functional_base.v go_lower.v \
   library.v proofauto.v computable_theorems.v computable_functions.v \
   type_induction.v align_compatible_dec.v reptype_lemmas.v aggregate_type.v aggregate_pred.v \
   nested_pred_lemmas.v compact_prod_sum.v \
   client_lemmas.v canon.v canonicalize.v closed_lemmas.v jmeq_lemmas.v \
   compare_lemmas.v sc_set_load_store.v \
   loadstore_mapsto.v loadstore_field_at.v field_compat.v nested_loadstore.v \
   call_lemmas.v extcall_lemmas.v forward_lemmas.v forward.v \
   entailer.v globals_lemmas.v \
   local2ptree_denote.v local2ptree_eval.v local2ptree_typecheck.v \
   fieldlist.v mapsto_memory_block.v\
   nested_field_lemmas.v efield_lemmas.v proj_reptype_lemmas.v replace_refill_reptype_lemmas.v \
   data_at_rec_lemmas.v field_at.v field_at_wand.v stronger.v \
   for_lemmas.v semax_tactics.v diagnosis.v simple_reify.v simpl_reptype.v \
   freezer.v deadvars.v Clightnotations.v unfold_data_at.v hints.v reassoc_seq.v \
   SeparationLogicAsLogicSoundness.v SeparationLogicAsLogic.v SeparationLogicFacts.v \
   subsume_funspec.v linking.v data_at_lemmas.v Funspec_old_Notation.v assoclists.v VSU.v quickprogram.v PTops.v Component.v QPcomposite.v \
   data_at_list_solver.v step.v fastforward.v finish.v \
   compat.v
#  VSU_DrySafe.v \   # does not yet work in VST 3.x 
#real_forward.v


PROGS32_FILES= \
  incr.v verif_incr.v \
  bin_search.v list_dt.v verif_reverse.v verif_reverse2.v verif_reverse3.v verif_reverse_client.v verif_queue.v verif_queue2.v verif_sumarray.v \
  insertionsort.v reverse.v reverse_client.v queue.v sumarray.v message.v string.v object.v \
  revarray.v verif_revarray.v insertionsort.v append.v min.v min64.v int_or_ptr.v \
  dotprod.v strlib.v fib.v \
  verif_min.v verif_min64.v verif_float.v verif_global.v verif_ptr_compare.v\
  verif_nest3.v verif_nest2.v verif_load_demo.v verif_store_demo.v \
  logical_compare.v verif_logical_compare.v field_loadstore.v  verif_field_loadstore.v \
  even.v verif_even.v odd.v verif_odd.v verif_evenodd_spec.v  \
  merge.v verif_merge.v verif_append.v verif_append2.v bst.v bst_oo.v verif_bst.v verif_bst_oo.v \
  verif_bin_search.v verif_floyd_tests.v verif_structcopy.v \
  verif_sumarray2.v verif_switch.v verif_message.v verif_object.v \
  funcptr.v verif_funcptr.v tutorial1.v  \
  verif_int_or_ptr.v verif_union.v verif_cast_test.v verif_dotprod.v \
  verif_strlib.v verif_fib.v bug83.v \
  tree.v verif_tree.v loop_minus1.v verif_loop_minus1.v \
  libglob.v verif_libglob.v peel.v verif_peel.v \
  printf.v stackframe_demo.v verif_stackframe_demo.v \
	rotate.v verif_rotate.v \
  verif_objectSelf.v verif_objectSelfFancy.v verif_objectSelfFancyOverriding.v
# verif_insertion_sort.v

C64_ORDINARY = reverse.c revarray.c sumarray.c append.c bin_search.c \
    bst.c field_loadstore.c float.c object.c \
    global.c min.c min64.c nest2.c nest3.c \
    logical_compare.c fptr_cmp.c \
    strlib.c switch.c union.c message.c

V64_ORDINARY = verif_reverse2.v verif_revarray.v verif_sumarray.v \
    verif_append2.v verif_bin_search.v \
    verif_bst.v verif_field_loadstore.v verif_float.v verif_object.v \
    verif_global.v verif_min.v verif_min64.v verif_nest2.v verif_nest3.v \
    verif_logical_compare.v  verif_fptr_cmp.v\
    verif_strlib.v verif_switch.v verif_union.v verif_message.v verif_incr.v

SHA_FILES= \
  general_lemmas.v SHA256.v common_lemmas.v pure_lemmas.v sha_lemmas.v functional_prog.v \
  sha.v spec_sha.v verif_sha_init.v \
  verif_sha_update.v verif_sha_update3.v verif_sha_update4.v \
  bdo_lemmas.v verif_sha_bdo.v  \
  verif_sha_bdo4.v verif_sha_bdo7.v verif_sha_bdo8.v \
  verif_sha_final2.v verif_sha_final3.v verif_sha_final.v \
  verif_addlength.v verif_SHA256.v call_memcpy.v
SHA_C_FILES= sha/sha.c sha/hmac.c hmacdrbg/hmac_drbg.c sha/hkdf.c

HMAC_FILES= \
  HMAC_functional_prog.v HMAC256_functional_prog.v \
  vst_lemmas.v hmac_pure_lemmas.v hmac_common_lemmas.v \
  hmac.v spec_hmac.v verif_hmac_cleanup.v \
  verif_hmac_init_part1.v verif_hmac_init_part2.v verif_hmac_init.v\
  verif_hmac_update.v verif_hmac_final.v verif_hmac_simple.v \
  verif_hmac_double.v verif_hmac_crypto.v protocol_spec_hmac.v

HKDF_FILES= \
  hkdf_functional_prog.v hkdf.v spec_hkdf.v \
  verif_hkdf_extract.v verif_hkdf_expand.v verif_hkdf.v

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
  verif_crypto_stream_salsa20_xor1.v verif_crypto_stream_salsa20_xor.v \
  verif_crypto_stream.v verif_verify.v

HMACDRBG_FILES = \
  entropy.v entropy_lemmas.v DRBG_functions.v HMAC_DRBG_algorithms.v \
  HMAC256_DRBG_functional_prog.v HMAC_DRBG_pure_lemmas.v \
  map_swap.v PRF_DRBG.v HMAC_DRBG_nonadaptive.v \
  PRG_NA.v HMAC_DRBG_nonadaptive.v \
  HMAC_DRBG_update.v \
  hmac_drbg.v hmac_drbg_compspecs.v \
  spec_hmac_drbg.v HMAC256_DRBG_bridge_to_FCF.v spec_hmac_drbg_pure_lemmas.v \
  HMAC_DRBG_common_lemmas.v  HMAC_DRBG_pure_lemmas.v \
  drbg_protocol_specs.v \
  verif_hmac_drbg_update_common.v verif_hmac_drbg_update.v \
  verif_hmac_drbg_reseed_common.v verif_hmac_drbg_WF.v \
  verif_hmac_drbg_generate_common.v \
  verif_hmac_drbg_seed_common.v verif_hmac_drbg_reseed.v \
  verif_hmac_drbg_generate.v verif_hmac_drbg_seed_buf.v verif_mocked_md.v \
  verif_hmac_drbg_seed.v verif_hmac_drbg_NISTseed.v verif_hmac_drbg_other.v \
  drbg_protocol_proofs.v verif_hmac_drbg_generate_abs.v
#  mocked_md.v mocked_md_compspecs.v

# these are only the top-level AES files, but they depend on many other AES files, so first run "make depend"
AES_FILES = \
  verif_encryption_LL.v verif_gen_tables_LL.v verif_setkey_enc_LL.v equiv_encryption.v

# DRBG_Files = \
#  hmac_drbg.v HMAC256_DRBG_functional_prog.v hmac_drbg_compspecs.v \
#  entropy.v DRBG_functions.v HMAC_DRBG_algorithms.v spec_hmac_drbg.v \
#  HMAC_DRBG_pure_lemmas.v HMAC_DRBG_common_lemmas.v verif_mocked_md.v \
#  verif_hmac_drbg_update.v verif_hmac_drbg_reseed.v verif_hmac_drbg_generate.v


# SINGLE_C_FILES are those to be clightgen'd individually with -normalize flag
# LINKED_C_FILES are those that need to be clightgen'd in a batch with others

SINGLE_C_FILES = reverse.c reverse_client.c revarray.c queue.c queue2.c message.c object.c insertionsort.c float.c global.c logical_compare.c nest2.c nest3.c ptr_compare.c load_demo.c store_demo.c dotprod.c string.c field_loadstore.c merge.c append.c bin_search.c bst.c bst_oo.c min.c min64.c switch.c funcptr.c floyd_tests.c cond.c sumarray.c sumarray2.c int_or_ptr.c union.c cast_test.c strlib.c tree.c fib.c loop_minus1.c libglob.c peel.c structcopy.c printf.c stackframe_demo.c rotate.c \
  objectSelf.c objectSelfFancy.c objectSelfFancyOverriding.c io.c io_mem.c fptr_cmp.c


LINKED_C_FILES = even.c odd.c
C_FILES = $(SINGLE_C_FILES) $(LINKED_C_FILES)

FILES = \
 veric/version.v \
 $(MSL_FILES:%=msl/%) \
 $(ORA_FILES:%=ora/%) \
 $(SEPCOMP_FILES:%=sepcomp/%) \
 $(VERIC_FILES:%=veric/%) \
 $(FLOYD_FILES:%=floyd/%) \
 $(PROGS_FILES:%=$(PROGSDIR)/%) \
 $(WAND_DEMO_FILES:%=wand_demo/%) \
 $(SHA_FILES:%=sha/%) \
 $(HMAC_FILES:%=sha/%) \
 $(FIPSDIGEST_FILES:%=boringssl-fips20180730/%) \
# $(FCF_FILES:%=fcf/src/FCF/%) \
 $(HMACFCF_FILES:%=hmacfcf/%) \
 $(HMACEQUIV_FILES:%=sha/%) \
 $(TWEETNACL_FILES:%=tweetnacl20140427/%) \
 $(HMACDRBG_Files:%=hmacdrbg/%)
# $(CCC26x86_FILES:%=ccc26x86/%) \
# $(CONCUR_FILES:%=concurrency/%) \
# $(DRBG_FILES:%=verifiedDrbg/spec/%)

EXTRA_INSTALL_FILES = \
  LICENSE \
  HISTORY \
  CHANGES \
  README.md \
  VERSION \
  msl/CREDITS \
  msl/EXTRACTION \
  msl/README.html \
  msl/SUMMARY \
  doc/VC.pdf \
  VST.config

# ##### Derived file lists #####

CC_TARGET= $(COMPCERT_INST_DIR)/cfrontend/Clight.vo

CVFILES = $(patsubst %.c,$(PROGSDIR)/%.v,$(C_FILES))
CVOFILES = $(patsubst %.c,$(PROGSDIR)/%.vo,$(C_FILES))

PROGS64_FILES=$(V64_ORDINARY) incr.v

ifeq ($(BITSIZE),64)
PROGS_FILES=$(PROGS64_FILES)
else
PROGS_FILES=$(PROGS32_FILES)
endif

INSTALL_FILES_SRC=$(shell COMPCERT=$(COMPCERT) COMPCERT_INST_DIR=$(COMPCERT_INST_DIR) ZLIST=$(ZLIST) BITSIZE=$(BITSIZE) ARCH=$(ARCH) IGNORECOQVERSION=$(IGNORECOQVERSION) IGNORECOMPCERTVERSION=$(IGNORECOMPCERTVERSION) MAKE=$(MAKE) util/calc_install_files $(PROGSDIR))
INSTALL_FILES_VO=$(patsubst %.v,%.vo,$(INSTALL_FILES_SRC))
INSTALL_FILES=$(sort $(INSTALL_FILES_SRC) $(INSTALL_FILES_VO))

# ########## Rules ##########

%_stripped.v: %.v
# e.g., 'make progs/verif_reverse_stripped.v will remove the tutorial comments
# from progs/verif_reverse.v
	grep -v '^.[*][*][ )]' $*.v >$@

# This line sets COQF depending on the folder of the input file $<
# If the folder name contains compcert, $(COMPCERT_R_FLAGS) is added, otherwise not.
%.vo: COQF=$(if $(findstring $(COMPCERT_SRC_DIR), $(dir $<)), $(COMPCERT_R_FLAGS) $(COQEXTRAFLAGS), $(COQFLAGS) $(PROFILE_FLAGS))

# If CompCert changes, all .vo files need to be recompiled
%.vo: $(COMPCERT_CONFIG)

%.vo: %.v
	@echo COQC $*.v
ifneq (,$(TIMING))
	@$(if $(TIMED),$(STDTIME)) $(COQC) $(COQF) -time $*.v > $<.timing
else ifeq ($(TIMINGS), true)
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQF) $*.v; date +'%s.%N after' >>timings" 2>>timings
	@bash -c "/usr/bin/time --output=TIMINGS -a -f '%e real, %U user, %S sys %M mem, '\"$(shell wc $*.v)\" $(COQC) $(COQF) $*.v"
#	echo -n $*.v " " >>TIMINGS; bash -c "/usr/bin/time -o TIMINGS -a $(COQC) $(COQF) $*.v"
else ifeq ($(TIMINGS), simple)
	@/usr/bin/time -f 'TIMINGS %e real, %U user, %S sys %M kbytes: '"$*.v" $(COQC) $(COQF) $*.v
else ifeq ($(strip $(ANNOTATE)), true)
	@$(COQC) $(COQF) $*.v | awk '{printf "%s: %s\n", "'$*.v'", $$0}'
else ifeq ($(strip $(ANNOTATE)), silent)
	@$(COQC) $(COQF) $*.v >/dev/null
else ifeq ($(strip $(ANNOTATE)), echo)
	$(COQC) $(COQF) $*.v >/dev/null
else
	@$(COQC) $(COQF) $*.v
#	@util/annotate $(COQC) $(COQF) $*.v
endif
	@$(PROFILE_ZIP)


# ########## Targets ##########

default_target: vst $(PROGSDIR)
vst: _CoqProject msl veric ora floyd simpleconc

ifeq ($(BITSIZE),64)
test: vst progs64
	@# need this tab here to turn off special behavior of 'test' target
test2: io
test4: mailbox 
test5: VSUpile64
tests: test test2 test4 test5
all: tests
else
test: vst progs
	@# need this tab here to turn off special behavior of 'test' target
test2: io
test3: sha hmac 
test5: VSUpile
tests: test test2 test3 test5
all: vst files tests hmacdrbg tweetnacl aes
endif

files: _CoqProject $(FILES:.v=.vo)

# TODO:
#
# Add conclib_coqlib, conclib_sublist, and conclib_veric to the targets
#
simpleconc: concurrency/conclib.vo atomics/verif_lock.vo
msl:     _CoqProject $(MSL_FILES:%.v=msl/%.vo)
ora:     _CoqProject $(ORA_FILES:%.v=ora/%.vo)
sepcomp: _CoqProject $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo)
concurrency: _CoqProject $(CC_TARGET) $(SEPCOMP_FILES:%.v=sepcomp/%.vo) $(CONCUR_FILES:%.v=concurrency/%.vo)
linking: _CoqProject $(LINKING_FILES:%.v=linking/%.vo)
veric:   _CoqProject $(VERIC_FILES:%.v=veric/%.vo) veric/version.vo
zlist:   _CoqProject $(ZLIST_FILES:%.v=zlist/%.vo)
floyd:   _CoqProject $(FLOYD_FILES:%.v=floyd/%.vo)
progs:   _CoqProject $(PROGS_FILES:%.v=$(PROGSDIR)/%.vo)
progsdir: $(PROGSDIR)
wand_demo:   _CoqProject $(WAND_DEMO_FILES:%.v=wand_demo/%.vo)
sha:     _CoqProject $(SHA_FILES:%.v=sha/%.vo)
hmac:    _CoqProject $(HMAC_FILES:%.v=sha/%.vo)
sha-hmac: sha hmac
hmacequiv:    _CoqProject $(HMAC_FILES:%.v=sha/%.vo)
fipsdigest:    _CoqProject $(FIPSDIGEST_FILES:%.v=boringssl_fips_20180730/%.vo)
FCF:     _CoqProject $(FCF_FILES:%.v=FCF/%.vo)
hmacfcf: _CoqProject $(HMACFCF_FILES:%.v=hmacfcf/%.vo)
tweetnacl: _CoqProject $(TWEETNACL_FILES:%.v=tweetnacl20140427/%.vo)
hmac0: _CoqProject sha/verif_hmac_init.vo sha/verif_hmac_cleanup.vo sha/verif_hmac_final.vo sha/verif_hmac_simple.vo  sha/verif_hmac_double.vo sha/verif_hmac_update.vo sha/verif_hmac_crypto.vo
hmacdrbg:   _CoqProject $(HMACDRBG_FILES:%.v=hmacdrbg/%.vo)
aes: _CoqProject $(AES_FILES:%.v=aes/%.vo)
hkdf:    _CoqProject $(HKDF_FILES:%.v=sha/%.vo)
# drbg: _CoqProject $(DRBG_FILES:%.v=verifiedDrbg/%.vo)
mailbox: _CoqProject mailbox/verif_mailbox_all.vo
# atomics: _CoqProject atomics/verif_kvnode_atomic.vo atomics/verif_kvnode_atomic_ra.vo atomics/verif_hashtable_atomic.vo atomics/verif_hashtable_atomic_ra.vo
atomics: _CoqProject atomics/verif_hashtable_atomic.vo $(PROGSDIR)/verif_incr_atomic.vo atomics/verif_lock.vo atomics/verif_lock_atomic.vo
io: _CoqProject $(PROGSDIR)/os_combine.vo $(PROGSDIR)/verif_printf.vo $(PROGSDIR)/verif_io.vo $(PROGSDIR)/verif_io_mem.vo $(PROGSDIR)/io_specs.vo floyd/printf.vo

$(CVOFILES): compcert

cvfiles: $(CVFILES)

VST.config:
	(echo "# VST configuration"; \
	echo "VST_ARCH=$(ARCH)"; \
	echo "VST_BITSIZE=$(BITSIZE)"; \
	echo "VST_COMPCERT=$(COMPCERT)"; \
	echo "VST_COMPCERT_INST_DIR=$(COMPCERT_INST_DIR)"; \
	echo "VST_COMPCERT_EXPLICIT_PATH=$(COMPCERT_EXPLICIT_PATH)"; \
	echo "VST_INSTALLDIR=$(INSTALLDIR)"; \
	) > VST.config

# Note: doc files are installed into the coq destination folder.
# This is not ideal but otherwise it gets tricky to handle variants
install: VST.config
	install -d "$(INSTALLDIR)"
	install -d "$(INSTALLDIR)"
	for d in $(sort $(dir $(INSTALL_FILES) $(EXTRA_INSTALL_FILES))); do install -d "$(INSTALLDIR)/$$d"; done
	for f in $(INSTALL_FILES); do install -m 0644 $$f "$(INSTALLDIR)/$$(dirname $$f)"; done
	for f in $(EXTRA_INSTALL_FILES); do install -m 0644 $$f "$(INSTALLDIR)/$$(dirname $$f)"; done
	cd ora; $(MAKE) install

dochtml:
	mkdir -p doc/html
	$(COQDOC) $(MSL_FILES:%=msl/%) $(VERIC_FILES:%=veric/%) $(FLOYD_FILES:%=floyd/%) $(SEPCOMP_FILES:%=sepcomp/%)

dochtml-full:
	mkdir -p doc/html
	$(COQDOC) $(FILES)

clean_cvfiles:
	rm $(CVFILES)

# SPECIAL-CASE RULES FOR LINKED_C_FILES:
ifdef CLIGHTGEN
all-cv-files: $(patsubst %.c,$(PROGSDIR)/%.v, $(SINGLE_C_FILES) even.c odd.c) \
              $(patsubst %.c,%.v, $(SHA_C_FILES)) \
              aes/aes.v tweetnacl20140427/tweetnaclVerifiableC.v \
              mailbox/mailbox.v atomics/SC_atomics.v # concurrency/threads.v 
ifneq (, $(findstring -short-idents, $(CGFLAGS)))
$(patsubst %.c,%.v, $(SHA_C_FILES)) &: $(SHA_C_FILES)
	$(CLIGHTGEN) ${CGFLAGS} $^
$(PROGSDIR)/odd.v: $(PROGSDIR)/even.v
mailbox/mailbox.v: mailbox/atomic_exchange.c mailbox/mailbox.c
	$(CLIGHTGEN) -DCOMPCERT -normalize -canonical-idents $^
else
ifeq (, $(findstring -canonical-idents, $(CGFLAGS)))
  $(warning CGFLAGS contains neither -short-idents nor -canonical-idents, using default which is probably -canonical-idents)
endif
$(patsubst %.c,%.v, $(SHA_C_FILES)): %.v: %.c
	$(CLIGHTGEN) ${CGFLAGS} $^
endif
concurrency/threads.v: concurrency/threads.c
	$(CLIGHTGEN) -normalize $^
atomics/SC_atomics.v: atomics/SC_atomics.c
	$(CLIGHTGEN) -normalize $^
progs/incr.v: progs/incr.c
	$(CLIGHTGEN) -normalize $^
progs64/incr.v: progs64/incr.c
	$(CLIGHTGEN) -normalize $^
progs/incrN.v: progs/incrN.c
	$(CLIGHTGEN) -normalize $^
aes/aes.v: aes/mbedtls/library/aes.c aes/mbedtls/include/mbedtls/config.h \
              aes/mbedtls/include/mbedtls/check_config.h
	$(CLIGHTGEN) ${CGFLAGS} -Iaes/mbedtls/include $<; mv aes/mbedtls/library/aes.v aes/aes.v
$(PROGSDIR)/even.v: $(PROGSDIR)/even.c $(PROGSDIR)/odd.c
	$(CLIGHTGEN) ${CGFLAGS} $^
tweetnacl20140427/tweetnaclVerifiableC.v: tweetnacl20140427/tweetnaclVerifiableC.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $<
# GENERAL RULES FOR SINGLE_C_FILES and NORMAL_C_FILES
$(patsubst %.c,$(PROGSDIR)/%.v, $(SINGLE_C_FILES)): $(PROGSDIR)/%.v: $(PROGSDIR)/%.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $^
endif

veric/version.v:  VERSION $(MSL_FILES:%=msl/%) $(SEPCOMP_FILES:%=sepcomp/%) $(VERIC_FILES:%=veric/%) $(FLOYD_FILES:%=floyd/%)
	util/make_version ${BITSIZE} ${COMPCERT_VERSION}

_CoqProject _CoqProject-export: Makefile util/coqflags $(COMPCERT_CONFIG)
	echo $(COQFLAGS) > _CoqProject
	util/coqflags > _CoqProject-export

floyd/floyd.coq: floyd/proofauto.vo
	coqtop $(COQFLAGS) -load-vernac-object floyd/proofauto -outputstate floyd/floyd -batch

.depend depend:
	@echo 'coqdep ... >.depend'
ifeq ($(COMPCERT_NEW),true)
	# DEPENDENCIES VARIANT COMPCERT_NEW
	$(COQDEP) $(DEPFLAGS) 2>&1 >.depend `find $(filter $(wildcard *), $(DIRS) refinedVST concurrency/common concurrency/compiler concurrency/juicy concurrency/util paco concurrency/sc_drf) -name "*.v"` | grep -v 'Warning:.*found in the loadpath' || true
	@echo "" >>.depend
else
	# DEPENDENCIES DEFAULT
	$(COQDEP) $(DEPFLAGS) 2>&1 >.depend `find $(filter $(wildcard *), $(DIRS) refinedVST) -name "*.v"` | grep -v 'Warning:.*found in the loadpath' || true
endif
ifeq ($(COMPCERT_BUILD_FROM_SRC),true)
	# DEPENDENCIES TO BUILD COMPCERT FROM SOURCE
	$(COQDEP) $(COMPCERT_R_FLAGS) 2>&1 >>.depend `find $(addprefix $(COMPCERT_SRC_DIR)/,$(COMPCERTDIRS))  -name "*.v"` $(COMPCERTFLOCQDIRS) | grep -v 'Warning:.*found in the loadpath' || true
endif
# ifneq ($(wildcard coq-ext-lib/theories),)
# 	$(COQDEP) -Q coq-ext-lib/theories ExtLib coq-ext-lib/theories >>.depend
# endif
ifneq ($(wildcard InteractionTrees/theories),)
#	$(COQDEP) -Q coq-ext-lib/theories ExtLib -Q paco/src Paco -Q InteractionTrees/theories ITree InteractionTrees/theories >>.depend
	$(COQDEP) -Q paco/src Paco -Q InteractionTrees/theories ITree InteractionTrees/theories >>.depend
endif
ifneq ($(wildcard ora/theories),)
	$(COQDEP) -Q ora/theories iris_ora ora/theories >>.depend
endif
ifneq ($(wildcard fcf/src/FCF),)
	$(COQDEP) -Q fcf/src/FCF FCF fcf/src/FCF/*.v >>.depend
endif
ifneq ($(wildcard paco/src),)
	$(COQDEP) -Q paco/src Paco paco/src/*.v >>.depend
endif
	wc .depend

clean:
	rm -f $(addprefix veric/version., v vo vos vok glob) .lia.cache .nia.cache floyd/floyd.coq .depend _CoqProject _CoqProject-export $(wildcard */.*.aux)  $(wildcard */*.glob) $(wildcard */*.vo */*.vos */*.vok) compcert/*/*.{vo,vos,vok} compcert/*/*/*.{vo,vos,vok}  compcert_new/*/*.{vo,vos,vok} compcert_new/*/*/*.{vo,vos,vok}
	rm -f progs/VSUpile/{*,*/*}.{vo,vos,vok,glob}
	rm -f progs64/VSUpile/{*,*/*}.{vo,vos,vok,glob}
	rm -f progs/memmgr/*.{vo,vos,vok,glob}
	rm -f ora/theories/*/*.{vo,vos,vok,glob}
	rm -f coq-ext-lib/theories/*.{vo,vos,vok,glob} InteractionTrees/theories/{*,*/*}.{vo,vos,vok,glob}
	rm -f paco/src/*.{vo,vos,vok,glob}
	rm -f fcf/src/FCF/*.{vo,vos,vok,glob}
	rm -fr doc/html

clean-concur:
	rm -f $(CONCUR_FILES:%.v=concurrency/%.vo) $(CONCUR_FILES:%.v=concurrency/%.glob) $(CONCUR_COMPILER_FILES:%.v=concurrency/compiler/%.vo) $(CONCUR_COMPILER_FILES:%.v=concurrency/compiler/%.glob) $(CONCUR_COMMON_FILES:%.v=concurrency/common/%.vo) $(CONCUR_COMMON_FILES:%.v=concurrency/common/%.glob) $(CONCUR_JUICY_FILES:%.v=concurrency/juicy/%.vo) $(CONCUR_JUICY_FILES:%.v=concurrency/juicy/%.glob)

clean-linking:
	rm -f $(LINKING_FILES:%.v=linking/%.vo) $(LINKING_FILES:%.v=linking/%.glob)

clean-refinedVST-frontend:
	rm -fr refinedVST/typing/frontend_stuff/_build
	rm -fr refinedVST/typing/frontend_stuff/examples/proofs

count:
	wc $(FILES)

count-linking:
	wc $(LINKING_FILES:%.v=linking/%.v)

util/calibrate: util/calibrate.ml
	cd util; ocamlopt.opt calibrate.ml -o calibrate

calibrate: util/calibrate
	-/usr/bin/time -f 'TIMINGS %e real, %U user, %S sys %M kbytes: CALIBRATE' util/calibrate

progs64/%.c: progs/%.c
	$(if $(findstring $(@F), $(C64_ORDINARY)), cp $< $@)

FIX64= "BEGIN{print \"(* Do not edit this file, it was generated automatically *)\"} 1 {sub(/VST[.]progs[.]/,\"VST.progs64.\"); print}"
progs64/verif_%.v: progs/verif_%.v
	$(if $(findstring $(@F), $(V64_ORDINARY)), awk $(FIX64) < $< > $@)

progs64c: $(C64_ORDINARY:%.c=progs64/%.c)
progs64v: progs64c $(V64_ORDINARY:%.v=progs64/%.v) $(C64_ORDINARY:%.c=progs64/%.v) depend
progs64: _CoqProject  $(PROGS64_FILES:%.v=progs64/%.vo)

VSUpile: floyd/proofauto.vo floyd/library.vo floyd/VSU.vo
	cd progs/VSUpile; $(MAKE) VST_LOC=../..
VSUpile64: floyd/proofauto.vo floyd/library.vo floyd/VSU.vo
	cd progs64/VSUpile; $(MAKE) VST_LOC=../..
memmgr:  floyd/proofauto.vo floyd/library.vo floyd/VSU.vo
	cd progs/memmgr; $(MAKE) VST_LOC=../..

nothing: # need this target for the degenerate case of "make -tk */*.vo" in coq-action.yml

assumptions.txt: veric/tcb.vo
	$(COQC) $(COQFLAGS) veric/tcb.v > assumptions.txt
	bash util/check_assumptions.sh

# $(CC_TARGET): compcert/make
#	(cd compcert; ./make)

# The .depend file is divided into two parts, .depend and .depend-concur,
# in order to work around a limitation in Cygwin about how long one
# command line can be.  (Or at least, it seems to be a solution to some
# such problem, not sure exactly.  -- Andrew)
include .depend
-include .depend-concur

