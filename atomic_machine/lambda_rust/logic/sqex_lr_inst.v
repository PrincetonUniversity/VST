(** Lambda-Rust instances for generic EXWP rules and concrete adequacy. *)
From iris.algebra Require Import auth gmap frac.
From iris.proofmode Require Import proofmode coq_tactics reduction.
From lrust.lang Require Import tactics lifting.
Require Export VST.atomic_machine.ext_call_impl.
Require Export VST.atomic_machine.lambda_rust.logic.sq_heap.
Require Export VST.atomic_machine.lambda_rust.logic.lr_lemmas.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Class lrSqGS Σ := LrSqGS {
  lrSqGS_invGS : invGS Σ;
  lrSqGS_heapGS :: sq_heapGS Σ
}.

Class lrSqGpreS Σ := LrSqGpreS {
  lrSqGpreS_inv :: invGpreS Σ;
  lrSqGpreS_heap :: inG Σ (authR sq_heapUR);
  lrSqGpreS_heap_freeable :: inG Σ (authR sq_freeableUR)
}.

Definition lrSqΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR sq_heapUR));
    GFunctor (constRF (authR sq_freeableUR))].
Global Instance subG_lrSqGpreS {Σ} : subG lrSqΣ Σ -> lrSqGpreS Σ.
Proof. solve_inG. Qed.

Local Existing Instance lrSqGS_invGS.

#[global] Instance lr_sqHeap `{!sq_heapGS Σ} :
    sqHeap lr_language Σ.
Proof.
  refine {| sq_mem_inhabited := populate ∅;
            sqex_logic.sq_heap := sq_heap; sqex_logic.sq_pointsto := sq_pointsto |}.
  - intros l q1 q2 v1 v2. iIntros "H1 H2".
    iDestruct (sq_pointsto_valid_2 with "H1 H2") as %[Hq _]. done.
  - intros e m T e' m' l q v Hstep Halloc.
    destruct (lr_step_alloc_footprint Hstep Halloc) as [Hnone _].
    iIntros "Hm Hl". iDestruct (sq_heap_read with "Hm Hl") as %Hsome.
    congruence.
Defined.

#[global] Instance lr_sq_pointsto_mixin `{!sq_heapGS Σ} :
    sq_pointsto_mixin (L := lr_language) (Σ := Σ).
Proof.
  refine {| sq_compare := fun v v' b =>
      (∃ z z' : Z, ⌜v = LitV (LitInt z) /\ v' = LitV (LitInt z') /\
        b = bool_decide (z = z')⌝)%I |}.
  - intros m ly l q v. iIntros "Hm Hl".
    by iDestruct (sq_heap_read with "Hm Hl") as %Hl.
  - intros m ly l v v'. iIntros "Hm Hl".
    iDestruct (sq_heap_read with "Hm Hl") as %Hl.
    iPureIntro. eexists. by rewrite /= Hl.
  - intros m ly l v v' m' Hstore. iIntros "Hm Hl".
    iDestruct (sq_heap_read with "Hm Hl") as %Hl.
    simpl in Hstore. rewrite Hl in Hstore. injection Hstore as <-.
    by iApply (sq_heap_write with "Hm Hl").
  - intros ly l q v la Hla. apply list_elem_of_singleton in Hla as <-.
    rewrite /fp_own. iIntros "Hl". by iExists q, v.
  - intros ly l v la Hla. apply list_elem_of_singleton in Hla as <-.
    rewrite /fp_own. iIntros "Hl". by iExists v.
  - intros m v v' b. iIntros "_ Hcmp".
    iDestruct "Hcmp" as (z z') "%Hcmp".
    destruct Hcmp as (Hv & Hv' & Hb). subst v v' b. iPureIntro.
    change ((sq_mem.lit_eq m (LitInt z') (LitInt z) <-> bool_decide (z = z') = true) /\
      (lit_neq (LitInt z') (LitInt z) <-> bool_decide (z = z') = false)).
    destruct (decide (z = z')) as [-> | Hne].
    + rewrite bool_decide_true //. split.
      * split; [done | intros _; constructor].
      * split; [intros Hneq; apply lr_lit_neq_int in Hneq; congruence | discriminate].
    + rewrite bool_decide_false //. split.
      * split; [intros Heq; apply lr_lit_eq_int in Heq; congruence | discriminate].
      * split; [done | intros _; constructor; congruence].
Defined.

(** The generic rules infer lambda-Rust values, evaluation contexts, and
    exposed operations through these semantic instances. *)
#[global] Instance lr_sqOfVal : sqOfVal (L := lr_language) := {
  sq_of_val := of_val;
  sq_to_of_val := to_of_val;
  sq_of_to_val := of_to_val
}.

#[global] Instance lr_sqIntoVal e v `{Hval : !@IntoVal lrust_lang e v} :
    SqIntoVal (L := lr_language) e v.
Proof. change (to_val e = Some v). by rewrite -(@into_val lrust_lang e v Hval) to_of_val. Qed.

#[global] Instance lr_result_into_val v :
    SqIntoVal (L := lr_language) (lr_result_expr (Some v)) v.
Proof. apply to_of_val. Qed.

#[global] Instance lr_sqContext K : SqContext (L := lr_language) (fill K).
Proof.
  split; cbn [sqlang_is_final sqlang_step sqlang_at_external lr_language].
  - intros e Hv. by apply fill_not_val.
  - intros e m T e' m' Hs. destruct Hs. rewrite -!fill_app. by constructor.
  - intros e m T e' m' Hv Hs. by apply (lr_step_fill_inv K e m T e' m').
  - intros e op k He. by apply (lr_external_fill K e op k).
  - intros e op k Hv He. by apply (lr_external_fill_inv K e op k).
Qed.

#[global] Instance lr_read_sc_external l :
    SqAtExternal (L := lr_language) (Read ScOrd (Lit (LitLoc l)))
      (ALoad tt l) lr_result_expr.
Proof. apply (LREctxExternal []). constructor. Qed.

#[global] Instance lr_write_sc_external l e v `{Hval : !@IntoVal lrust_lang e v} :
    SqAtExternal (L := lr_language) (Write ScOrd (Lit (LitLoc l)) e)
      (AStore tt l v) (fun _ => Lit LitPoison).
Proof.
  apply (LREctxExternal []). constructor.
  by rewrite -(@into_val lrust_lang e v Hval) to_of_val.
Qed.

#[global] Instance lr_cas_external l e1 lit1 e2 lit2
    `{Hval1 : !@IntoVal lrust_lang e1 (LitV lit1),
      Hval2 : !@IntoVal lrust_lang e2 (LitV lit2)} :
    SqAtExternal (L := lr_language) (CAS (Lit (LitLoc l)) e1 e2)
      (ACAS tt l (LitV lit1) (LitV lit2)) lr_result_expr.
Proof.
  apply (LREctxExternal []). constructor.
  - by rewrite -(@into_val lrust_lang e1 (LitV lit1) Hval1) to_of_val.
  - by rewrite -(@into_val lrust_lang e2 (LitV lit2) Hval2) to_of_val.
Qed.

#[global] Instance lr_fork_external e :
    SqAtExternal (L := lr_language) (Fork e) (ASpawn e) (fun _ => Lit LitPoison).
Proof. apply (LREctxExternal []). constructor. Qed.

#[global] Hint Extern 0 (SqAtExternal (L := lr_language) ?e ?op ?k) =>
  let e' := eval cbn [sqlang_expr_to_thrd_st lr_language id] in e in
  progress change (SqAtExternal (L := lr_language) e' op k);
  typeclasses eauto : typeclass_instances.

(** Pure reductions are proved directly for the sequential semantics. *)
Local Lemma lr_head_pure_exec e1 e2 (φ : Prop) :
  (forall m, φ -> lr_head_step e1 m [] e2 m) ->
  (forall m T e' m', φ -> lr_head_step e1 m T e' m' ->
    T = [] /\ e' = e2 /\ m' = m) ->
  SqPureExec (L := lr_language) φ 1 e1 e2.
Proof.
  intros Hsafe Hdet Hφ. apply relations.nsteps_once. split.
  - intros m. apply (LREctxStep []). by apply Hsafe.
  - intros m T e' m' Hstep. apply lr_step_head in Hstep.
    + eapply Hdet; [exact Hφ | exact Hstep].
    + exact (lr_head_step_redex_shape _ _ _ _ _ (Hsafe m Hφ)).
Qed.

Local Ltac inv_lr_pure :=
  repeat match goal with
  | _ => progress simplify_map_eq/=
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : lr_head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); inversion H; subst; clear H
  | H : sq_mem.lit_eq _ _ _ |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq _ _ |- _ => inversion H; clear H; simplify_map_eq/=
  | H : sq_mem.bin_op_eval _ ?op _ _ _ |- _ =>
      is_constructor op; inversion H; clear H; simplify_eq/=
  end.

Local Hint Constructors lr_head_step sq_mem.bin_op_eval sq_mem.lit_eq lit_neq : core.
Local Ltac solve_lr_pure :=
  apply lr_head_pure_exec;
    [intros; destruct_and?; subst; econstructor; simpl; eauto with lia
    | simpl; intros; destruct_and?; inv_lr_pure; done].

#[global] Instance lr_pure_rec e f xl body body' el :
  AsRec e f xl body -> TCForall AsVal el ->
  Closed (f :b: xl +b+ []) body ->
  DoSubstL (f :: xl) (e :: el) body body' ->
  SqPureExec (L := lr_language) True 1 (App e el) body'.
Proof.
  rewrite /AsRec /DoSubstL => -> /TCForall_Forall Hel ??. solve_lr_pure.
  eapply Forall_impl; [exact Hel |]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

#[global] Instance lr_pure_eq_int z1 z2 :
  SqPureExec (L := lr_language) True 1
    (BinOp EqOp (Lit (LitInt z1)) (Lit (LitInt z2)))
    (Lit (lit_of_bool (bool_decide (z1 = z2)))).
Proof. case_bool_decide; solve_lr_pure. Qed.

#[global] Instance lr_pure_plus z1 z2 :
  SqPureExec (L := lr_language) True 1
    (BinOp PlusOp (Lit (LitInt z1)) (Lit (LitInt z2)))
    (Lit (LitInt (z1 + z2))).
Proof. solve_lr_pure. Qed.

#[global] Instance lr_pure_case i e el :
  SqPureExec (L := lr_language) (0 <= i /\ el !! Z.to_nat i = Some e) 1
    (Case (Lit (LitInt i)) el) e | 10.
Proof. solve_lr_pure. Qed.

#[global] Instance lr_pure_if b e1 e2 :
  SqPureExec (L := lr_language) True 1
    (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_lr_pure. Qed.

(** Expression reshaping is specific to lambda-Rust. *)
Tactic Notation "exwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; apply (tac_exwp_bind (@ectx_language.fill lrust_ectx_lang K));
    [tc_solve | simpl])
  end.

Tactic Notation "exwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; eapply (tac_exwp_pure (@ectx_language.fill lrust_ectx_lang K));
    [tc_solve | simpl; tc_solve | try done | tc_solve | simpl_subst])
  end.

(** Adequacy for lambda-Rust with any sound external-call contracts. *)
Section adequacy_gen.
  Context `{!lrSqGpreS Σ}.
  Context (ext_specs : forall `{!lrSqGS Σ},
    ExtSpecs lr_language Σ).
  Local Existing Instance ext_specs.
  Context (ext_specs_sound : forall `{!lrSqGS Σ}, ExtSpecsSound).
  Local Existing Instance ext_specs_sound.

  Theorem lr_sqex_adequacy_gen (e : expr) (φ : val -> Prop) (m : lr_mem) :
    (forall `{!lrSqGS Σ}, ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
    at_sem_adequate [e] [φ] m.
  Proof using Type*.
    intros Hwp. apply (sqex_adequacy_gen Σ e φ m).
    intros Hinv. iMod (sq_heap_init m) as (γh γf) "Hheap".
    pose (HGS := {| lrSqGS_invGS := Hinv;
      lrSqGS_heapGS := SqHeapGS Σ _ _ γh γf |}).
    iModIntro. iExists {| sqGS_heap := @lr_sqHeap Σ (SqHeapGS Σ _ _ γh γf);
      sqGS_extspecs := @ext_specs HGS;
      sqGS_extspecs_sound := @ext_specs_sound HGS |}.
    iFrame "Hheap". iApply (Hwp HGS).
  Qed.
End adequacy_gen.

Section standard_adequacy.

Theorem sqex_adequacy Σ `{!lrSqGpreS Σ} (e : expr) (φ : val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ}, ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hwp. eapply (lr_sqex_adequacy_gen (Σ := Σ) (fun _ => ext_call_impl.ext_specs)).
  - intros ?. apply _.
  - exact Hwp.
Qed.

End standard_adequacy.

