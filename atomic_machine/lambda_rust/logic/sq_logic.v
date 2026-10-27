(**
  A program logic for the sequential lambda-Rust semantics of [sq_sem.v],
  after lambda-Rust's [lrust.lang.lifting].

  [sq_lang] is that semantics as an Iris language with a single thread: its
  head steps are the [lr_head_step]s, whose memory events become the step's
  observations.  It has no atomic operations: a thread at a sequentially
  consistent access or CAS ([lr_external]) is stuck here, as is one at a
  [Fork], since the semantics of these exists only at the level of the
  atomic machine ([at_logic.v]).

  The logic has the shape of lambda-Rust's: the heap resources of
  [lrust.lang.heap] ([l ↦{q} v], [†l…n]), with the state interpretation
  [heap_ctx (sq_heap m)], in which every location is unlocked, and
  lambda-Rust's rules for the non-atomic fragment.

  The carrier types of [sq_lang] are aliases ([sq_expr], [sq_val], ...), so
  that its canonical structures do not take over lambda-Rust's [lrust_lang]:
  a [WP] about [sq_lang] is on an [sq_expr], with a postcondition on
  [sq_val] (hence the [RET (v : sq_val)] below).
*)

From iris.algebra Require Import auth.
From iris.program_logic Require Export weakestpre ectx_language ectxi_language
  lifting ectx_lifting.
From iris.proofmode Require Import proofmode.
From lrust.lang Require Export heap.
From lrust.lang Require Import lifting.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** * The language *)

Definition sq_expr : Type := expr.
Definition sq_val : Type := val.
Definition sq_ectx_item : Type := ectx_item.
Definition sq_obs : Type := mem_ev.

Inductive sq_base_step
    : sq_expr -> lr_mem -> list sq_obs -> sq_expr -> lr_mem -> list sq_expr -> Prop :=
| SqHeadStep e m T e' m' :
    lr_head_step e m T e' m' ->
    sq_base_step e m T e' m' [].

Lemma sq_val_stuck e m T e' m' efs : sq_base_step e m T e' m' efs -> to_val e = None.
Proof. destruct 1 as [????? H]; by destruct H. Qed.

Lemma sq_base_ctx_step_val Ki e m T e' m' efs :
  sq_base_step (fill_item Ki e) m T e' m' efs -> is_Some (to_val e).
Proof.
  inversion 1 as [????? Hh]; subst; revert Hh;
    destruct Ki; inversion_clear 1; decompose_Forall_hyps; simplify_option_eq; by eauto.
Qed.

Lemma sq_lang_mixin :
  @EctxiLanguageMixin sq_expr sq_val sq_ectx_item lr_mem sq_obs
    of_val to_val fill_item sq_base_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, sq_val_stuck, fill_item_val,
    fill_item_no_val_inj, sq_base_ctx_step_val.
Qed.

Canonical Structure sq_ectxi_lang := EctxiLanguage sq_lang_mixin.
Canonical Structure sq_ectx_lang := EctxLanguageOfEctxi sq_ectxi_lang.
(* lambda-rust language instance, but the semantics is restricted to the sequential lr_head_step. *)
Canonical Structure sq_lang := LanguageOfEctx sq_ectx_lang.

Global Instance sq_state_inhabited : Inhabited lr_mem := populate ∅.

(** * The heap

    The memory as a lambda-Rust heap with every location unlocked. *)

Definition sq_heap (m : lr_mem) : state := (fun v => (RSt 0, v)) <$> m.

Lemma lookup_sq_heap (m : lr_mem) (l : loc) : sq_heap m !! l = (fun v => (RSt 0, v)) <$> m !! l.
Proof. apply lookup_fmap. Qed.

Lemma lookup_sq_heap_None (m : lr_mem) (l : loc) : sq_heap m !! l = None <-> m !! l = None.
Proof. by rewrite lookup_sq_heap fmap_None. Qed.

Lemma lookup_sq_heap_Some (m : lr_mem) (l : loc) st v :
  sq_heap m !! l = Some (st, v) -> st = RSt 0 /\ m !! l = Some v.
Proof. rewrite lookup_sq_heap. intros (? & -> & [= <- <-])%fmap_Some. done. Qed.

Lemma sq_heap_insert (m : lr_mem) (l : loc) (v : val) : sq_heap (<[l := v]> m) = <[l := (RSt 0, v)]> (sq_heap m).
Proof. apply fmap_insert. Qed.

Lemma fmap_alloc_gmap {A B} (f : A -> B) (x : A) (l : loc) (n : nat) (m : gmap loc A) :
  f <$> alloc_gmap x l n m = alloc_gmap (f x) l n (f <$> m).
Proof. revert l. induction n as [ | n IH ]; intros l; [ done | ]. simpl. by rewrite fmap_insert IH. Qed.

Lemma fmap_free_gmap {A B} (f : A -> B) (l : loc) (n : nat) (m : gmap loc A) :
  f <$> free_gmap l n m = free_gmap l n (f <$> m).
Proof. revert l. induction n as [ | n IH ]; intros l; [ done | ]. simpl. by rewrite fmap_delete IH. Qed.

Lemma sq_heap_alloc (m : lr_mem) (l : loc) (n : nat) :
  sq_heap (alloc_gmap (LitV LitPoison) l n m) = init_mem l n (sq_heap m).
Proof. by rewrite /sq_heap fmap_alloc_gmap init_mem_equiv. Qed.

Lemma sq_heap_free (m : lr_mem) (l : loc) (n : nat) : sq_heap (free_gmap l n m) = free_mem l n (sq_heap m).
Proof. by rewrite /sq_heap fmap_free_gmap free_mem_equiv. Qed.

Lemma sq_alloc_fresh (m : lr_mem) : exists l, forall z, m !! (l +ₗ z)%L = None.
Proof.
  exists (fresh_block (sq_heap m), 0). intros z.
  apply lookup_sq_heap_None, (is_fresh_block (sq_heap m) (0 + z)).
Qed.

(** * The logic *)

Class lrSqGS Σ := LrSqGS {
  lrSqGS_invGS : invGS Σ;
  lrSqGS_heapGS :: heapGS Σ
}.

Global Instance lrSqGS_irisGS `{!lrSqGS Σ} : irisGS sq_lang Σ := {
  iris_invGS := lrSqGS_invGS;
  (* state_interp is the same as the one in lambda-rust. *)
  state_interp m _ _ _ := heap_ctx (sq_heap m);
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.


(** Inversion of sequential steps, after lambda-Rust's [inv_base_step]. *)
Ltac inv_sq_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/=
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : sq_base_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1); inversion H; subst; clear H
  | H : lr_head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); inversion H; subst; clear H
  end.

Ltac inv_sq_lit :=
  repeat match goal with
  | H : sq_mem.lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : sq_mem.bin_op_eval _ ?c _ _ _ |- _ =>
      is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Local Hint Constructors sq_base_step lr_head_step
  sq_mem.bin_op_eval sq_mem.lit_eq lit_neq : core.

Section lifting.
Context `{!lrSqGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : sq_expr.

(** Pure reductions *)
Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; do 3 eexists; apply SqHeadStep; econstructor; simpl;
    eauto with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_sq_step; inv_sq_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, (pure_base_step_pure_step (Λ := sq_ectx_lang));
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance sq_pure_rec e f xl erec erec' el :
  AsRec e f xl erec ->
  TCForall AsVal el ->
  Closed (f :b: xl +b+ []) erec ->
  DoSubstL (f :: xl) (e :: el) erec erec' ->
  PureExec True 1 (App e el : sq_expr) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  eapply Forall_impl; [exact Hel|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Global Instance sq_pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) : sq_expr)
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)) : sq_expr)
                  (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance sq_pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0)) : sq_expr) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l)) : sq_expr) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2) : sq_expr)
                  (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2) : sq_expr)
                  (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_offset l z :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z) : sq_expr)
                  (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1 (Case (Lit $ LitInt i) el : sq_expr) e | 10.
Proof. solve_pure_exec. Qed.

Global Instance sq_pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2 : sq_expr) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

(** Heap *)
Lemma sq_wp_alloc E (n : Z) :
  0 < n ->
  {{{ True }}} (Alloc (Lit $ LitInt n) : sq_expr) @ E
  {{{ l (sz: nat), RET (LitV $ LitLoc l : sq_val); ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (m ? κ κs n') "Hσ !>"; iSplit.
  { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
    eexists _, _, _, _. apply SqHeadStep. by apply LRAllocS. }
  iNext; iIntros (v2 m2 efs Hstep) "_"; inv_sq_step.
  iMod (heap_alloc with "Hσ") as "[Hσ Hl]"; [done | by intros z; apply lookup_sq_heap_None | ].
  iModIntro; iSplit=> //. rewrite sq_heap_alloc. iFrame.
  iApply ("HΦ" $! _ (Z.to_nat n)). iFrame. iPureIntro. rewrite Z2Nat.id; lia.
Qed.

Lemma sq_wp_free E (n:Z) l vl :
  n = length vl ->
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    (Free (Lit $ LitInt n) (Lit $ LitLoc l) : sq_expr) @ E
  {{{ RET (LitV LitPoison : sq_val); True }}}.
Proof.
  iIntros (? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (m ? κ κs n') "Hσ".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & %Hdom & Hσ)"=>//.
  assert (Hdom' : forall z, is_Some (m !! (l +ₗ z)) <-> 0 ≤ z < n).
  { intros z. rewrite -Hdom lookup_sq_heap fmap_is_Some. done. }
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. apply SqHeadStep. by apply LRFreeS. }
  iNext; iIntros (v2 m2 efs Hstep) "_"; inv_sq_step.
  iModIntro; iSplit=> //. rewrite sq_heap_free. iFrame. by iApply "HΦ".
Qed.

Lemma sq_wp_read_na E l q v :
  {{{ ▷ l ↦{q} v }}} (Read Na1Ord (Lit $ LitLoc l) : sq_expr) @ E
  {{{ RET (v : sq_val); l ↦{q} v }}}.
Proof.
  iIntros (?) ">Hv HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (m ? κ κs n) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[k Hl].
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. apply SqHeadStep. by apply LRReadNaS. }
  iNext; iIntros (v2 m2 efs Hstep) "_"; inv_sq_step.
  iModIntro; iSplit=> //. iFrame. rewrite to_of_val /=. by iApply "HΦ".
Qed.

Lemma sq_wp_write_na E l e v v' :
  IntoVal e v ->
  {{{ ▷ l ↦ v' }}} (Write Na1Ord (Lit $ LitLoc l) e : sq_expr) @ E
  {{{ RET (LitV LitPoison : sq_val); l ↦ v }}}.
Proof.
  iIntros (<- Φ) ">Hv HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (m ? κ κs n) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %Hl.
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iMod (heap_write _ _ _ v with "Hσ Hv") as "[Hσ Hv]".
  iModIntro; iSplit.
  { iPureIntro. do 4 eexists. apply SqHeadStep. econstructor; [ apply to_of_val | done ]. }
  iNext; iIntros (v2 m2 efs Hstep) "_"; inv_sq_step.
  iModIntro; iSplit=> //. rewrite sq_heap_insert. iFrame. by iApply "HΦ".
Qed.

Lemma sq_wp_eq_loc E (l1 : loc) (l2: loc) q1 q2 v1 v2 P (Φ : sq_val -> iProp Σ) :
  (P ⊢ ▷ l1 ↦{q1} v1) ->
  (P ⊢ ▷ l2 ↦{q2} v2) ->
  (P ⊢ ▷ Φ (LitV (bool_decide (l1 = l2)))) ->
  P ⊢ WP (BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) : sq_expr) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost) "HP".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply wp_lift_pure_det_base_step_no_fork'; [ done | | solve_exec_puredet | ].
    { intros m. eexists _, _, _, _. apply SqHeadStep, LRBinOpS, sq_mem.BinOpEqTrue. constructor. }
    iPoseProof (Hpost with "HP") as "?".
    iIntros "!> _". by iApply wp_value.
  - iApply wp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (m ? κ κs n') "Hσ1". iModIntro.
    iSplitR.
    { iPureIntro. eexists _, _, _, _. apply SqHeadStep, LRBinOpS, sq_mem.BinOpEqFalse. by constructor. }
    (* As in lambda-Rust: strip the later off the points-tos while keeping them. *)
    iAssert ((▷ ∃ q v, l1 ↦{q} v) ∧ (▷ ∃ q v, l2 ↦{q} v) ∧ ▷ Φ (LitV false))%I
      with "[HP]" as "HP".
    { iSplit; last iSplit.
      + iExists _, _. by iApply Hl1.
      + iExists _, _. by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 m2 efs Hs) "_ !>".
    inv_sq_step. iSplitR=>//. inv_sq_lit.
    + iExFalso. iDestruct "HP" as "[Hl1 _]".
      iDestruct "Hl1" as (??) "Hl1".
      iDestruct (heap_read with "Hσ1 Hl1") as %[? [_ Hl]%lookup_sq_heap_Some].
      match goal with H : _ = None |- _ => by rewrite H in Hl end.
    + iExFalso. iDestruct "HP" as "[_ [Hl2 _]]".
      iDestruct "Hl2" as (??) "Hl2".
      iDestruct (heap_read with "Hσ1 Hl2") as %[? [_ Hl]%lookup_sq_heap_Some].
      match goal with H : _ = None |- _ => by rewrite H in Hl end.
    + iDestruct "HP" as "[_ [_ $]]". done.
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma sq_wp_app_ind E f (el : list expr) (Ql : vec (sq_val -> iProp Σ) (length el)) vs
    (Φ : sq_val -> iProp Σ) :
  AsVal f ->
  ([∗ list] eQ ∈ zip el Ql, WP (eQ.1 : sq_expr) @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP (App f (of_val <$> vs ++ vl) : sq_expr) @ E {{ Φ }}) -∗
    WP (App f ((of_val <$> vs) ++ el) : sq_expr) @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el))
      with (@ectxi_language.fill_item sq_ectxi_lang (AppRCtx vf vs el) e).
    pose proof (ectxi_lang_ctx_item (Λ := sq_ectxi_lang) (AppRCtx vf vs el)).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "%vl Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma sq_wp_app_vec E f el (Ql : vec (sq_val -> iProp Σ) (length el)) (Φ : sq_val -> iProp Σ) :
  AsVal f ->
  ([∗ list] eQ ∈ zip el Ql, WP (eQ.1 : sq_expr) @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP (App f (of_val <$> (vl : list val)) : sq_expr) @ E {{ Φ }}) -∗
    WP (App f el : sq_expr) @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (sq_wp_app_ind _ _ _ _ []). Qed.

Lemma sq_wp_app (Ql : list (sq_val -> iProp Σ)) E f el (Φ : sq_val -> iProp Σ) :
  length Ql = length el -> AsVal f ->
  ([∗ list] eQ ∈ zip el Ql, WP (eQ.1 : sq_expr) @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP (App f (of_val <$> (vl : list val)) : sq_expr) @ E {{ Φ }}) -∗
    WP (App f el : sq_expr) @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (sq_wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.

End lifting.
