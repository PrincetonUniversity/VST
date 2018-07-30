(** Safety of the FineConc Machine initiliazed with X86 semantics *)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.sc_drf.mem_obs_eq.
Require Import VST.concurrency.sc_drf.x86_inj.
Require Import VST.concurrency.sc_drf.fineConc_safe.
Require Import Coqlib.
Require Import VST.msl.Coqlib2.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.

Module X86FineSafe.
  Import FineConcSafe Renamings MemObsEq FineConcInitial
         ValObsEq ValueWD MemoryWD
         X86Inj X86Context event_semantics.
  Section FineConcSafe.
    Context {the_program : Asm.program}
            {Hsafe: Asm_core.safe_genv (@the_ge the_program)}.

    Instance X86Sem : Semantics := @X86Sem the_program Hsafe.
    Instance X86Inj : CoreInjections.CoreInj := X86Inj the_program Hsafe.

    (** The initial memory is well-defined*)
    Context {init_mem : option Memory.mem}
            {init_mem_wd: forall m, init_mem = Some m -> valid_mem m}.

    Lemma init_core_wd:
      forall (c : semC) (v : Values.val) (args : seq Values.val)
        (m : Memory.mem),
        valid_val_list (id_ren m) args ->
        init_mem = Some m ->
        initial_core semSem 0 m c v args -> CoreInjections.core_wd (id_ren m) c.
  Proof.
    intros.
    unfold initial_core in *.
    simpl in *.
    inv H1.
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
