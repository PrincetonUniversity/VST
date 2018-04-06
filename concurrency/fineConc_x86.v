(** Safety of the FineConc Machine initiliazed with X86 semantics *)

Require Import compcert.lib.Axioms.

Require Import VST.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.pos.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.mem_obs_eq.
Require Import VST.concurrency.x86_inj.
Require Import VST.concurrency.x86_context.
Require Import VST.concurrency.fineConc_safe.
Require Import Coqlib.
Require Import VST.msl.Coqlib2.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.

Module X86Initial : FineConcInitial X86SEM X86Machines X86Context X86Inj.
  Import Renamings MemObsEq ValObsEq ValueWD MemoryWD
         X86Inj X86Context event_semantics.

  (** The initial memory is well-defined*)
  Parameter init_mem_wd:
    forall m, init_mem = Some m -> valid_mem m.

  Lemma init_core_wd:
    forall v args m (ARGS:valid_val_list (id_ren m) args),
      init_mem = Some m ->
      match initial_core X86SEM.Sem 0 the_ge v args with
      | Some c => core_wd (id_ren m) c
      | None => True
      end.
  Proof.
    intros.
    unfold initial_core. unfold X86SEM.Sem. simpl. unfold Asm_coop.Asm_initial_core.
    destruct v; trivial.
    destruct (Int.eq_dec i Int.zero); trivial.
    remember (Genv.find_funct_ptr the_ge b ) as d.
    destruct d; trivial. destruct f; trivial.
    remember (val_casted.val_has_type_list_func args (sig_args (Asm.fn_sig f))) as t.
    destruct t; try solve [simpl; trivial].
    rewrite andb_true_l.
    remember (val_casted.vals_defined args ) as w.
    destruct w; try solve [simpl; trivial].
    rewrite andb_true_l.
    remember (proj_sumbool (zlt (4 * (2 * Zlength args)) Int.max_unsigned)) as r.
    destruct r; try solve [simpl; trivial]. simpl.
    unfold init_mem in H.
    split; trivial.
    unfold id_ren, is_left. symmetry in Heqd.
    specialize (Genv.find_funct_ptr_not_fresh _ _ H Heqd); intros.
    remember (valid_block_dec m b). destruct s; simpl; trivial. contradiction.
  Qed.

  (** The global env is well-defined *)
  Lemma the_ge_wd:
    forall m,
      init_mem = Some m ->
      ge_wd (id_ren m) the_ge.
  Proof.
    intros. unfold init_mem in H.
    unfold the_ge.
    constructor.
    - intros b Hfuns.
      destruct ((Genv.genv_defs (Genv.globalenv the_program)) ! b) eqn:Hget;
        try by exfalso.
      apply Genv.genv_defs_range in Hget.
      erewrite Genv.init_mem_genv_next in Hget by eauto.
      apply id_ren_validblock in Hget.
      rewrite Hget; auto.
    - intros.
      unfold Senv.symbol_address in H0.
      destruct (Senv.find_symbol (Genv.globalenv the_program) id) eqn:Hfind.
      apply Senv.find_symbol_below in Hfind.
      unfold Senv.nextblock in Hfind. simpl in Hfind.
      erewrite Genv.init_mem_genv_next in Hfind by eauto.
      unfold valid_val. rewrite <- H0.
      apply id_ren_validblock in Hfind. eexists; eauto.
      subst. simpl; auto.
  Qed.

End X86Initial.

(** Safety of the FineConc machine for the X86 architecture*)
Module FineConcX86Safe :=
  FineConcSafe X86SEM X86SEMAxioms X86Machines X86Context X86Inj X86Initial.
