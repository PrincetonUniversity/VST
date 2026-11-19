(** Single-threaded lambda-Rust semantics for the atomic machine. *)

From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import base gmap list fin_map_dom.

Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.common.

Import ListNotations.
Open Scope Z_scope.
Open Scope loc_scope.

Set Default Proof Using "Type".

(** lambda-Rust's location type.  A hint rather than an [Instance], so that
    the inferred location type is [loc] itself, not a constant equal to it. *)
#[global] Hint Extern 0 Location => exact loc : typeclass_instances.

Definition lr_mem : Type := gmap loc val.
Definition lr_layout : Type := unit.

#[global] Instance lr_memory :
    @Memory loc val _ _ lr_mem lr_layout :=
  {| load := fun m l _ => m !! l;

     store := fun m l _ v =>
       match m !! l with
       | Some _ => Some (<[l := v]> m)
       | None => None
       end;

     layout_to_locs := fun l _ => [l] |}.

Local Notation lr_mem_ev := (@mem_ev loc).

Definition lr_read_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Read l.

Definition lr_write_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Write l.

Definition lr_alloc_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Alloc l.

Definition lr_free_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Free l.

(** The locations in the half-open range starting at [l] with length [n]. *)
Fixpoint lr_locs (l : loc) (n : nat) : list loc :=
  match n with
  | O => []
  | S n => l :: lr_locs (l +ₗ 1)%L n
  end.

Local Lemma lr_locs_elem l k n :
  k ∈ lr_locs l n <-> k.1 = l.1 /\ l.2 <= k.2 < l.2 + Z.of_nat n.
Proof.
  induction n as [|n IH] in l |- *.
  - rewrite /= elem_of_nil. destruct l, k; simpl. lia.
  - rewrite /= elem_of_cons IH Nat2Z.inj_succ.
    destruct l as [b o], k as [b' o']. rewrite /shift_loc /=.
    split.
    + intros [Heq | [Hb Hz]].
      * injection Heq as -> ->. split; [done | lia].
      * split; [done | lia].
    + intros [-> Hz]. destruct (decide (o' = o)) as [-> | Hne].
      * by left.
      * right. split; [done | lia].
Qed.

Definition lr_alloc_events (l : loc) (n : nat) : list lr_mem_ev :=
  map lr_alloc_event (lr_locs l n).

Definition lr_free_events (l : loc) (n : nat) : list lr_mem_ev :=
  map lr_free_event (lr_locs l n).

Definition lr_val_eq
    (m : lr_mem) (v_cur v_exp : val) : Prop :=
  match v_exp, v_cur with
  | LitV l_exp, LitV l_cur => sq_mem.lit_eq m l_exp l_cur
  | _, _ => False
  end.

Definition lr_val_neq
    (m : lr_mem) (v_cur v_exp : val) : Prop :=
  match v_exp, v_cur with
  | LitV l_exp, LitV l_cur => lit_neq l_exp l_cur
  | _, _ => False
  end.

(** Head steps that do not belong to the machine's SC atomic interface. *)
Inductive lr_head_step
    : expr -> lr_mem -> list lr_mem_ev -> expr -> lr_mem -> Prop :=
| LRBinOpS op l1 l2 l' m :
    sq_mem.bin_op_eval m op l1 l2 l' ->
    lr_head_step
      (BinOp op (Lit l1) (Lit l2)) m []
      (Lit l') m
| LRBetaS f xl e e' el m :
    Forall (fun ei => is_Some (to_val ei)) el ->
    Closed (cons_binder f (app_binder xl [])) e ->
    subst_l (f :: xl) (Rec f xl e :: el) e = Some e' ->
    lr_head_step
      (App (Rec f xl e) el) m []
      e' m
| LRReadNaS l v m :
    m !! l = Some v ->
    lr_head_step
      (Read Na1Ord (Lit (LitLoc l))) m [lr_read_event l]
      (of_val v) m
| LRWriteNaS l e v v' m :
    to_val e = Some v ->
    m !! l = Some v' ->
    lr_head_step
      (Write Na1Ord (Lit (LitLoc l)) e) m [lr_write_event l]
      (Lit LitPoison) (<[l := v]> m)
| LRAllocS n l m :
    0 < n ->
    (forall z, m !! (l +ₗ z)%L = None) ->
    lr_head_step
      (Alloc (Lit (LitInt n))) m
      (lr_alloc_events l (Z.to_nat n))
      (Lit (LitLoc l))
      (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m)
| LRFreeS n l m :
    0 < n ->
    (forall z,
        is_Some (m !! (l +ₗ z)%L) <-> 0 <= z < n) ->
    lr_head_step
      (Free (Lit (LitInt n)) (Lit (LitLoc l))) m
      (lr_free_events l (Z.to_nat n))
      (Lit LitPoison) (free_gmap l (Z.to_nat n) m)
| LRCaseS i el e m :
    0 <= i ->
    el !! Z.to_nat i = Some e ->
    lr_head_step
      (Case (Lit (LitInt i)) el) m []
      e m.

(** Evaluation-context closure of [lr_head_step]. *)
Inductive lr_step
    : expr -> lr_mem -> list lr_mem_ev -> expr -> lr_mem -> Prop :=
| LREctxStep K e1 m1 T e2 m2 :
    lr_head_step e1 m1 T e2 m2 ->
    lr_step
      (fill K e1) m1 T
      (fill K e2) m2.

(** The memory effect of a sequential step, independently of its expression.
    This is an invariant proved below, not an additional step premise. *)
Inductive lr_mem_effect : lr_mem -> list lr_mem_ev -> lr_mem -> Prop :=
| LREffectPure m : lr_mem_effect m [] m
| LREffectRead m l :
    is_Some (m !! l) -> lr_mem_effect m [lr_read_event l] m
| LREffectWrite m l v :
    is_Some (m !! l) -> lr_mem_effect m [lr_write_event l] (<[l := v]> m)
| LREffectAlloc m l n :
    (forall z, m !! (l +ₗ z) = None) ->
    lr_mem_effect m (lr_alloc_events l n) (alloc_gmap (LitV LitPoison) l n m)
| LREffectFree m l n :
    (forall z, 0 <= z < Z.of_nat n -> is_Some (m !! (l +ₗ z))) ->
    lr_mem_effect m (lr_free_events l n) (free_gmap l n m).

Lemma lr_step_mem_effect e m T e' m' :
  lr_step e m T e' m' -> lr_mem_effect m T m'.
Proof.
  intros [K e1 m1 T1 e2 m2 Hhead]. destruct Hhead.
  - constructor.
  - constructor.
  - constructor. by eexists.
  - constructor. by eexists.
  - by constructor.
  - constructor. intros z Hz. apply H0. rewrite Z2Nat.id in Hz; lia.
  - constructor.
Qed.

Local Lemma lr_alloc_gmap_lookup_in (m : lr_mem) l n k :
  k ∈ lr_locs l n ->
  alloc_gmap (LitV LitPoison) l n m !! k = Some (LitV LitPoison).
Proof.
  induction n as [|n IH] in l |- *; simpl; first by rewrite elem_of_nil.
  rewrite elem_of_cons. intros [-> | Hin]; first by rewrite lookup_insert_eq.
  destruct (decide (l = k)) as [-> | Hne]; first by rewrite lookup_insert_eq.
  rewrite lookup_insert_ne; last done. by apply IH.
Qed.

Lemma lr_step_alloc_footprint {e m T e' m' l} :
  lr_step e m T e' m' -> lr_alloc_event l ∈ T ->
  m !! l = None /\ m' !! l = Some (LitV LitPoison).
Proof.
  intros Hstep Halloc.
  destruct (lr_step_mem_effect _ _ _ _ _ Hstep)
    as [m0 | m0 l0 Hread | m0 l0 v Hwrite | m0 l0 n Hfresh | m0 l0 n Hfree].
  - inversion Halloc.
  - apply list_elem_of_singleton in Halloc. discriminate.
  - apply list_elem_of_singleton in Halloc. discriminate.
  - apply list_elem_of_fmap in Halloc as (k & Heq & Hin).
    injection Heq as <-. split.
    + destruct (proj1 (lr_locs_elem l0 l n) Hin) as [Hb _].
      specialize (Hfresh (l.2 - l0.2)).
      replace (l0 +ₗ (l.2 - l0.2)) with l in Hfresh;
        [exact Hfresh | destruct l0, l; simpl in *; simplify_eq; unfold shift_loc; simpl; f_equal; lia].
    + by apply lr_alloc_gmap_lookup_in.
  - apply list_elem_of_fmap in Halloc as (k & Heq & _). discriminate.
Qed.

Lemma lr_step_access_allocated e m T e' m' ev l w :
  lr_step e m T e' m' -> ev ∈ T -> mem_ev_need_full_loc ev = Some (l, w) ->
  is_Some (m !! l).
Proof.
  intros Hstep Hin Haccess.
  destruct (lr_step_mem_effect _ _ _ _ _ Hstep)
    as [m0 | m0 l0 Hread | m0 l0 v Hwrite | m0 l0 n Hfresh | m0 l0 n Hfree].
  - inversion Hin.
  - apply list_elem_of_singleton in Hin as ->. inversion Haccess; subst. exact Hread.
  - apply list_elem_of_singleton in Hin as ->. inversion Haccess; subst. exact Hwrite.
  - apply list_elem_of_fmap in Hin as (k & -> & _). discriminate.
  - apply list_elem_of_fmap in Hin as (k & -> & Hin).
    inversion Haccess; subst.
    destruct (proj1 (lr_locs_elem l0 l n) Hin) as [Hb Hz].
    specialize (Hfree (l.2 - l0.2)).
    replace (l0 +ₗ (l.2 - l0.2)) with l in Hfree;
      [apply Hfree; lia | destruct l0, l; simpl in *; simplify_eq; unfold shift_loc; simpl; f_equal; lia].
Qed.

(** An emitted access identifies the exact memory effect. These are purely
    operational facts; logical ownership is supplied separately by EXWP. *)
Lemma lr_step_write_footprint e m T e' m' l :
  lr_step e m T e' m' -> lr_write_event l ∈ T ->
  exists old new, m !! l = Some old /\
    T = [lr_write_event l] /\ m' = <[l := new]> m.
Proof.
  intros Hstep Hwrite.
  destruct (lr_step_mem_effect _ _ _ _ _ Hstep).
  - inversion Hwrite.
  - apply list_elem_of_singleton in Hwrite. discriminate.
  - apply list_elem_of_singleton in Hwrite. injection Hwrite as ->.
    destruct H as [old Hold]. exists old, v. done.
  - apply list_elem_of_fmap in Hwrite as (k & Hk & _). discriminate.
  - apply list_elem_of_fmap in Hwrite as (k & Hk & _). discriminate.
Qed.

Lemma lr_step_read_footprint e m T e' m' l :
  lr_step e m T e' m' -> lr_read_event l ∈ T ->
  is_Some (m !! l) /\ T = [lr_read_event l] /\ m' = m.
Proof.
  intros Hstep Hread.
  destruct (lr_step_mem_effect _ _ _ _ _ Hstep).
  - inversion Hread.
  - apply list_elem_of_singleton in Hread. injection Hread as ->. done.
  - apply list_elem_of_singleton in Hread. discriminate.
  - apply list_elem_of_fmap in Hread as (k & Hk & _). discriminate.
  - apply list_elem_of_fmap in Hread as (k & Hk & _). discriminate.
Qed.

Local Lemma lr_alloc_gmap_frame (m : lr_mem) l n k :
  k ∉ lr_locs l n -> alloc_gmap (LitV LitPoison) l n m !! k = m !! k.
Proof.
  revert l. induction n as [|n IH]=> l //= /not_elem_of_cons [Hne Htail].
  rewrite lookup_insert_ne; last congruence. by apply IH.
Qed.

Local Lemma lr_free_gmap_frame (m : lr_mem) l n k :
  k ∉ lr_locs l n -> free_gmap l n m !! k = m !! k.
Proof.
  revert l. induction n as [|n IH]=> l //= /not_elem_of_cons [Hne Htail].
  rewrite lookup_delete_ne; last congruence. by apply IH.
Qed.

(** Outside Write/Alloc/Free events the memory is unchanged. This is a
    modification footprint, not a claim that all step-enabling facts are read
    events: pointer equality can inspect allocation status while emitting []. *)
Lemma lr_step_frame e m T e' m' k :
  lr_step e m T e' m' ->
  lr_write_event k ∉ T -> lr_alloc_event k ∉ T -> lr_free_event k ∉ T ->
  m' !! k = m !! k.
Proof.
  intros Hstep. destruct (lr_step_mem_effect _ _ _ _ _ Hstep);
    intros Hwrite Halloc Hfree; try done.
  - apply lookup_insert_ne. intros ->. apply Hwrite. by left.
  - apply lr_alloc_gmap_frame. intros Hk. apply Halloc.
    by apply list_elem_of_fmap_2.
  - apply lr_free_gmap_frame. intros Hk. apply Hfree.
    by apply list_elem_of_fmap_2.
Qed.

Local Notation lr_atomic_op := (@atomic_op loc val lr_layout expr).

Definition lr_result_expr (ov : option val) : expr :=
  match ov with
  | Some v => of_val v
  | None => stuck_term
  end.

(** Identify valid external calls. *)
Inductive lr_head_external
    : expr -> lr_atomic_op -> (option val -> expr) -> Prop :=
| LRReadScE l :
    lr_head_external
      (Read ScOrd (Lit (LitLoc l)))
      (ALoad tt l) lr_result_expr
| LRWriteScE l e v :
    to_val e = Some v ->
    lr_head_external
      (Write ScOrd (Lit (LitLoc l)) e)
      (AStore tt l v) (fun _ => Lit LitPoison)
| LRCasE l e1 lit1 e2 lit2 :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    lr_head_external
      (CAS (Lit (LitLoc l)) e1 e2)
      (ACAS tt l (LitV lit1) (LitV lit2)) lr_result_expr
| LRSpawnE e :
    lr_head_external (Fork e) (ASpawn e) (fun _ => Lit LitPoison).

(** Evaluation-context closure of [lr_head_external]. *)
Inductive lr_external
    : expr -> lr_atomic_op -> (option val -> expr) -> Prop :=
| LREctxExternal K e op k :
    lr_head_external e op k ->
    lr_external
      (fill K e) op
      (fun ov => fill K (k ov)).

(** ** Evaluation contexts around a redex *)

Lemma fill_item_not_val Ki e : to_val (fill_item Ki e) = None.
Proof. by destruct Ki. Qed.

(** An expression has redex shape if it is not itself a strict context
    around a non-value.  Head redexes have this shape, so their evaluation
    context is unique. *)

Definition redex_shape (e : expr) : Prop :=
  forall Ki e', e = fill_item Ki e' -> is_Some (to_val e').

Lemma fill_redex_shape_inv K e e1 :
  redex_shape e1 -> to_val e = None -> fill K e = e1 -> K = [] /\ e = e1.
Proof.
  revert e. induction K as [ | Ki K IH ]; intros e Hshape He Hfill; simpl in Hfill; [ auto | ].
  destruct (IH _ Hshape (fill_item_not_val Ki e) Hfill) as (_ & Heq).
  destruct (Hshape Ki e (eq_sym Heq)) as [v Hv]. by rewrite He in Hv.
Qed.

Lemma fill_redex_unique K1 K2 e1 e2 :
  redex_shape e1 -> redex_shape e2 -> to_val e1 = None -> to_val e2 = None ->
  fill K1 e1 = fill K2 e2 -> K1 = K2 /\ e1 = e2.
Proof.
  intros Hs1 Hs2 Hv1 Hv2. revert K2.
  induction K1 as [ | Ki K1 IH ] using rev_ind; intros K2 Hfill.
  - by destruct (fill_redex_shape_inv K2 e2 e1 Hs1 Hv2 (eq_sym Hfill)) as (-> & ->).
  - destruct K2 as [ | Kj K2 _ ] using rev_ind.
    + destruct (fill_redex_shape_inv (K1 ++ [Ki]) e1 e2 Hs2 Hv1 Hfill) as (Hnil & _).
      by destruct K1.
    + rewrite !fill_app in Hfill. simpl in Hfill.
      pose proof (fill_item_no_val_inj Ki Kj (fill K1 e1) (fill K2 e2)
                    (fill_not_val K1 e1 Hv1) (fill_not_val K2 e2 Hv2) Hfill) as <-.
      apply (inj (fill_item Ki)) in Hfill as Hfill'.
      by destruct (IH K2 Hfill') as (-> & ->).
Qed.

Lemma lr_step_not_val e m T e' m' :
  lr_step e m T e' m' -> to_val e = None.
Proof.
  intros Hstep. inversion Hstep; subst. apply fill_not_val.
  by inversion H.
Qed.

Lemma lr_external_not_val e op k :
  lr_external e op k -> to_val e = None.
Proof.
  intros Hext. inversion Hext; subst. apply fill_not_val.
  by inversion H.
Qed.

(** The semantic separation laws needed to construct [lr_language]. *)

Lemma lr_head_step_not_val e m T e' m' : lr_head_step e m T e' m' -> to_val e = None.
Proof. by destruct 1. Qed.

Lemma lr_head_external_not_val e op k : lr_head_external e op k -> to_val e = None.
Proof. by destruct 1. Qed.

Lemma lr_head_step_redex_shape e m T e' m' : lr_head_step e m T e' m' -> redex_shape e.
Proof.
  intros Hh Ki e1 ->. revert Hh.
  destruct Ki; inversion_clear 1; decompose_Forall_hyps; simplify_option_eq; by eauto.
Qed.

Lemma lr_head_external_redex_shape e op k : lr_head_external e op k -> redex_shape e.
Proof. intros Hh Ki e1 ->. destruct Ki; inversion Hh; subst; rewrite ?to_of_val; eauto. Qed.

Lemma lr_head_step_external e m T e' m' op k :
  lr_head_step e m T e' m' -> lr_head_external e op k -> False.
Proof. destruct 1; inversion 1. Qed.

Lemma lr_step_external_disjoint e m T e' m' op k :
  lr_step e m T e' m' -> lr_external e op k -> False.
Proof.
  intros [K1 e1 ?? e2 ? Hh] Hext. inversion Hext as [K2 e3 ? k' Hh' Heq].
  destruct (fill_redex_unique K2 K1 e3 e1 (lr_head_external_redex_shape _ _ _ Hh')
              (lr_head_step_redex_shape _ _ _ _ _ Hh) (lr_head_external_not_val _ _ _ Hh')
              (lr_head_step_not_val _ _ _ _ _ Hh) Heq) as [_ ->].
  exact (lr_head_step_external _ _ _ _ _ _ _ Hh Hh').
Qed.

Lemma lr_external_det e op1 k1 op2 k2 :
  lr_external e op1 k1 -> lr_external e op2 k2 ->
  op2 = op1 /\ forall ov, k2 ov = k1 ov.
Proof.
  intros H1 H2. destruct H1 as [K1 e1 op1 k1 H1].
  inversion H2 as [K2 e2 op2x k2x Hh Heq]; subst.
  destruct (fill_redex_unique K2 K1 e2 e1
    (lr_head_external_redex_shape _ _ _ Hh)
    (lr_head_external_redex_shape _ _ _ H1)
    (lr_head_external_not_val _ _ _ Hh)
    (lr_head_external_not_val _ _ _ H1) Heq) as [-> ->].
  destruct H1; inversion Hh; subst; split; congruence.
Qed.

(** ** Constructive decisions for stepping and exposed calls *)

Section decisions.


(** Deciding the exact allocation range used by [LRFreeS] is a finite-set check. *)
Local Lemma lr_nat_range n z :
  0 <= z < Z.of_nat (Z.to_nat n) <-> 0 <= z < n.
Proof.
  destruct (decide (0 <= n)) as [Hn | Hn].
  - by rewrite Z2Nat.id.
  - rewrite Z2Nat.nonpos; lia.
Qed.

Local Lemma lr_free_range_iff (m : lr_mem) l n :
  (forall z, is_Some (m !! (l +ₗ z)%L) <-> 0 <= z < n) <->
  filter (fun k : loc => k.1 = l.1) (dom m : gset loc) =
    (list_to_set (lr_locs l (Z.to_nat n)) : gset loc).
Proof.
  split.
  - intros H. apply set_eq. intros [b o].
    rewrite elem_of_filter elem_of_dom elem_of_list_to_set lr_locs_elem.
    destruct l as [bl ol]. simpl.
    split.
    + intros [-> Hlookup]. split; first done.
      specialize (H (o - ol)). rewrite /shift_loc /= in H.
      replace (ol + (o - ol)) with o in H by lia.
      apply H in Hlookup. apply lr_nat_range in Hlookup. lia.
    + intros [-> Hz]. split; first done.
      specialize (H (o - ol)). rewrite /shift_loc /= in H.
      replace (ol + (o - ol)) with o in H by lia.
      apply H. apply lr_nat_range. lia.
  - intros Heq z.
    have H : (l +ₗ z)%L ∈ filter (fun k : loc => k.1 = l.1) (dom m : gset loc) <->
      (l +ₗ z)%L ∈ (list_to_set (lr_locs l (Z.to_nat n)) : gset loc) by rewrite Heq.
    rewrite elem_of_filter elem_of_dom elem_of_list_to_set lr_locs_elem in H.
    rewrite /shift_loc /= in H.
    rewrite /shift_loc /=. split.
    + intros Hlookup. destruct (proj1 H (conj eq_refl Hlookup)) as [_ Hz].
      apply lr_nat_range. lia.
    + intros Hz. have Hz' := proj2 (lr_nat_range n z) Hz.
      have Hb : l.2 <= l.2 + z < l.2 + Z.of_nat (Z.to_nat n) by lia.
      exact (proj2 (proj2 H (conj eq_refl Hb))).
Qed.

Local Instance lr_free_range_dec (m : lr_mem) l n :
    Decision (forall z, is_Some (m !! (l +ₗ z)%L) <-> 0 <= z < n).
Proof.
  destruct (decide (filter (fun k : loc => k.1 = l.1) (dom m : gset loc) =
    (list_to_set (lr_locs l (Z.to_nat n)) : gset loc))) as [H | H].
  - left. by apply lr_free_range_iff.
  - right. intros Hr. apply H. by apply lr_free_range_iff.
Defined.

(** Head-operation enabling conditions have constructive decisions. *)
Local Instance lr_bin_op_reducible_dec (m : lr_mem) op l1 l2 :
    Decision (exists l', sq_mem.bin_op_eval m op l1 l2 l').
Proof.
  destruct op, l1, l2;
    try solve [left; eexists; constructor];
    try solve [right; intros [l' H]; inversion H; subst;
      match goal with
      | H : sq_mem.lit_eq _ _ _ |- _ => inversion H
      | H : lit_neq _ _ |- _ => inversion H
      end].
  - destruct (decide (l = l0)) as [-> | Hne].
    + left. eexists. apply sq_mem.BinOpEqTrue. constructor.
    + left. eexists. apply sq_mem.BinOpEqFalse. by constructor.
  - destruct (decide (n = 0)) as [-> | Hne].
    + left. eexists. apply sq_mem.BinOpEqFalse. constructor.
    + right. intros [l' H]. inversion H; subst;
        match goal with
        | H : sq_mem.lit_eq _ _ _ |- _ => inversion H
        | H : lit_neq _ _ |- _ => inversion H; congruence
        end.
  - destruct (decide (n = 0)) as [-> | Hne].
    + left. eexists. apply sq_mem.BinOpEqFalse. constructor.
    + right. intros [l' H]. inversion H; subst;
        match goal with
        | H : sq_mem.lit_eq _ _ _ |- _ => inversion H
        | H : lit_neq _ _ |- _ => inversion H; congruence
        end.
  - destruct (decide (n = n0)) as [-> | Hne].
    + left. eexists. apply sq_mem.BinOpEqTrue. constructor.
    + left. eexists. apply sq_mem.BinOpEqFalse. by constructor.
Defined.

Local Definition lr_head_enabled (e : expr) (m : lr_mem) : Prop :=
  match e with
  | BinOp op e1 e2 =>
      match to_val e1, to_val e2 with
      | Some (LitV l1), Some (LitV l2) => exists l', sq_mem.bin_op_eval m op l1 l2 l'
      | _, _ => False
      end
  | App ef el =>
      match to_val ef with
      | Some (RecV f xl body) =>
          Forall (fun ei => is_Some (to_val ei)) el /\
          is_Some (subst_l (f :: xl) (Rec f xl body :: el) body)
      | _ => False
      end
  | Read Na1Ord e =>
      match to_val e with Some (LitV (LitLoc l)) => is_Some (m !! l) | _ => False end
  | Write Na1Ord e1 e2 =>
      match to_val e1 with
      | Some (LitV (LitLoc l)) => is_Some (to_val e2) /\ is_Some (m !! l)
      | _ => False
      end
  | Alloc e =>
      match to_val e with Some (LitV (LitInt n)) => 0 < n | _ => False end
  | Free e1 e2 =>
      match to_val e1, to_val e2 with
      | Some (LitV (LitInt n)), Some (LitV (LitLoc l)) =>
          0 < n /\ forall z, is_Some (m !! (l +ₗ z)%L) <-> 0 <= z < n
      | _, _ => False
      end
  | Case e el =>
      match to_val e with
      | Some (LitV (LitInt i)) => 0 <= i /\ is_Some (el !! Z.to_nat i)
      | _ => False
      end
  | _ => False
  end.

Local Instance lr_head_enabled_dec e m : Decision (lr_head_enabled e m).
Proof.
  unfold lr_head_enabled. repeat case_match; apply _.
Defined.

Local Lemma lr_head_enabled_complete e m T e' m' :
  lr_head_step e m T e' m' -> lr_head_enabled e m.
Proof.
  destruct 1; simpl; eauto.
  case_decide; last contradiction. simpl. split; eauto.
Qed.

Lemma lr_alloc_fresh (m : lr_mem) : exists l, forall z, m !! (l +ₗ z)%L = None.
Proof.
  set (σ := (fun v => (RSt 0, v)) <$> m).
  exists (fresh_block σ, 0). intros z.
  change (m !! (fresh_block σ, z) = None).
  have Hfresh := is_fresh_block σ z.
  by rewrite /σ lookup_fmap fmap_None in Hfresh.
Qed.

Local Lemma lr_head_enabled_sound e m :
  lr_head_enabled e m -> exists T e' m', lr_head_step e m T e' m'.
Proof.
  destruct e; unfold lr_head_enabled; try done;
    repeat case_match; try done;
    repeat match goal with
    | H : to_val ?e = Some ?v |- _ => apply of_to_val in H; subst e
    end; simpl.
  - intros [l' H]. do 3 eexists. by constructor.
  - intros [Hargs [e' Hsubst]]. do 3 eexists. by eapply LRBetaS.
  - intros [v_read Hread]. do 3 eexists. by constructor.
  - intros [[v_write Hv] [v_old Hv']]. do 3 eexists. by eapply LRWriteNaS.
  - intros Hn. destruct (lr_alloc_fresh m) as [l_fresh Hfresh]. do 3 eexists. by eapply LRAllocS.
  - intros [Hn Hl]. do 3 eexists. by eapply LRFreeS.
  - intros [Hi [e' He']]. do 3 eexists. by eapply LRCaseS.
Qed.

Local Instance lr_head_reducible_dec e m :
    Decision (exists T e' m', lr_head_step e m T e' m').
Proof.
  destruct (decide (lr_head_enabled e m)) as [H | H].
  - left. by apply lr_head_enabled_sound.
  - right. intros (T & e' & m' & Hstep). apply H. by eapply lr_head_enabled_complete.
Defined.

Local Definition lr_head_external_enabled (e : expr) : Prop :=
  match e with
  | Read ScOrd e =>
      match to_val e with Some (LitV (LitLoc _)) => True | _ => False end
  | Write ScOrd e1 e2 =>
      match to_val e1 with
      | Some (LitV (LitLoc _)) => is_Some (to_val e2)
      | _ => False
      end
  | CAS e0 e1 e2 =>
      match to_val e0, to_val e1, to_val e2 with
      | Some (LitV (LitLoc _)), Some (LitV _), Some (LitV _) => True
      | _, _, _ => False
      end
  | Fork _ => True
  | _ => False
  end.

Local Instance lr_head_external_enabled_dec e : Decision (lr_head_external_enabled e).
Proof. unfold lr_head_external_enabled. repeat case_match; apply _. Defined.

Local Lemma lr_head_external_enabled_complete e op k :
  lr_head_external e op k -> lr_head_external_enabled e.
Proof. destruct 1; simpl; try rewrite ?H ?H0; eauto. Qed.

Local Lemma lr_head_external_enabled_sound e :
  lr_head_external_enabled e -> exists op k, lr_head_external e op k.
Proof.
  destruct e; unfold lr_head_external_enabled; try done;
    repeat case_match; try done;
    repeat match goal with
    | H : to_val ?e = Some ?v |- _ => apply of_to_val in H; subst e
    end; simpl;
    try solve [intros _; do 2 eexists; constructor; done].
  intros [v_write Hv]. do 2 eexists. by econstructor.
Qed.

Local Instance lr_head_external_dec e : Decision (exists op k, lr_head_external e op k).
Proof.
  destruct (decide (lr_head_external_enabled e)) as [H | H].
  - left. by apply lr_head_external_enabled_sound.
  - right. intros (op & k & Hext). apply H. by eapply lr_head_external_enabled_complete.
Defined.

(** Enumerate the subexpressions obtainable by removing an evaluation context.
    Application arguments are visited only after the function and preceding
    arguments are values. *)
Local Definition lr_arg_redexes (go : expr -> list expr) : list expr -> list expr :=
  fix args (el : list expr) := match el with
  | [] => []
  | e :: el => go e ++ match to_val e with Some _ => args el | None => [] end
  end.

Local Fixpoint lr_redexes (e : expr) : list expr :=
  e :: match e with
  | BinOp _ e1 e2 | Write _ e1 e2 | Free e1 e2 =>
      lr_redexes e1 ++ match to_val e1 with Some _ => lr_redexes e2 | None => [] end
  | App ef el =>
      lr_redexes ef ++ match to_val ef with
      | Some _ =>
          (fix args (el : list expr) :=
            match el with
            | [] => []
            | ei :: el => lr_redexes ei ++
                match to_val ei with Some _ => args el | None => [] end
            end) el
      | None => []
      end
  | Read _ e1 | Alloc e1 | Case e1 _ => lr_redexes e1
  | CAS e0 e1 e2 =>
      lr_redexes e0 ++ match to_val e0 with
      | Some _ => lr_redexes e1 ++
          match to_val e1 with Some _ => lr_redexes e2 | None => [] end
      | None => []
      end
  | _ => []
  end.

Local Lemma lr_arg_redexes_prefix go vl e el r :
  r ∈ go e -> r ∈ lr_arg_redexes go ((of_val <$> vl) ++ e :: el).
Proof.
  intros Hin. induction vl; simpl; rewrite ?to_of_val; apply elem_of_app; auto.
Qed.

Local Lemma lr_redexes_fill_item Ki e r :
  r ∈ lr_redexes e -> r ∈ lr_redexes (fill_item Ki e).
Proof.
  intros Hin. destruct Ki; simpl; rewrite ?to_of_val;
    apply elem_of_cons; right;
    try solve [apply elem_of_app; auto | done].
  - apply elem_of_app. right. by apply lr_arg_redexes_prefix.
  - apply elem_of_app. right. apply elem_of_app. by left.
  - apply elem_of_app. right. apply elem_of_app. by right.
Qed.

Local Lemma lr_redexes_fill K e r : r ∈ lr_redexes e -> r ∈ lr_redexes (fill K e).
Proof.
  induction K as [|Ki K IH] in e |- *; simpl; first done.
  intros Hin. apply IH. by apply lr_redexes_fill_item.
Qed.

Local Lemma lr_redexes_sound e r :
  r ∈ lr_redexes e -> exists K, e = fill K r.
Proof.
  revert e r. fix IH 1. intros e r. destruct e;
    rewrite /= elem_of_cons; intros [-> | Hin]; try solve [by exists []];
    try solve [by apply elem_of_nil in Hin].
  - apply elem_of_app in Hin as [Hin | Hin].
    + destruct (IH e1 r Hin) as [K HK]. exists (K ++ [BinOpLCtx op e2]).
      by rewrite fill_app /= -HK.
    + destruct (to_val e1) as [v1|] eqn:Hv; last by apply elem_of_nil in Hin.
      destruct (IH e2 r Hin) as [K HK]. exists (K ++ [BinOpRCtx op v1]).
      by rewrite fill_app /= -HK (of_to_val _ _ Hv).
  - apply elem_of_app in Hin as [Hin | Hin].
    + destruct (IH e r Hin) as [K HK]. exists (K ++ [AppLCtx el]).
      by rewrite fill_app /= -HK.
    + destruct (to_val e) as [vf|] eqn:Hv; last by apply elem_of_nil in Hin.
      have Hargs : forall r, r ∈ lr_arg_redexes lr_redexes el ->
        exists vl ei er K, el = (of_val <$> vl) ++ ei :: er /\ ei = fill K r.
      { clear Hin. induction el as [|ei el IHel]; simpl; intros r0 Hr; first by apply elem_of_nil in Hr.
        apply elem_of_app in Hr as [Hr | Hr].
        - destruct (IH ei r0 Hr) as [K HK]. exists [], ei, el, K. done.
        - destruct (to_val ei) as [vi|] eqn:Hvi; last by apply elem_of_nil in Hr.
          destruct (IHel r0 Hr) as (vl & ei' & er & K & Hel & HK).
          exists (vi :: vl), ei', er, K. simpl. rewrite Hel (of_to_val _ _ Hvi). done. }
      destruct (Hargs r Hin) as (vl & ei & er & K & -> & HK).
      exists (K ++ [AppRCtx vf vl er]).
      by rewrite fill_app /= -HK (of_to_val _ _ Hv).
  - destruct (IH e r Hin) as [K HK]. exists (K ++ [ReadCtx o]).
    by rewrite fill_app /= -HK.
  - apply elem_of_app in Hin as [Hin | Hin].
    + destruct (IH e1 r Hin) as [K HK]. exists (K ++ [WriteLCtx o e2]).
      by rewrite fill_app /= -HK.
    + destruct (to_val e1) as [v1|] eqn:Hv; last by apply elem_of_nil in Hin.
      destruct (IH e2 r Hin) as [K HK]. exists (K ++ [WriteRCtx o v1]).
      by rewrite fill_app /= -HK (of_to_val _ _ Hv).
  - apply elem_of_app in Hin as [Hin | Hin].
    + destruct (IH e1 r Hin) as [K HK]. exists (K ++ [CasLCtx e2 e3]).
      by rewrite fill_app /= -HK.
    + destruct (to_val e1) as [v0|] eqn:Hv0; last by apply elem_of_nil in Hin.
      apply elem_of_app in Hin as [Hin | Hin].
      * destruct (IH e2 r Hin) as [K HK]. exists (K ++ [CasMCtx v0 e3]).
        by rewrite fill_app /= -HK (of_to_val _ _ Hv0).
      * destruct (to_val e2) as [v1|] eqn:Hv1; last by apply elem_of_nil in Hin.
        destruct (IH e3 r Hin) as [K HK]. exists (K ++ [CasRCtx v0 v1]).
        by rewrite fill_app /= -HK (of_to_val _ _ Hv0) (of_to_val _ _ Hv1).
  - destruct (IH e r Hin) as [K HK]. exists (K ++ [AllocCtx]).
    by rewrite fill_app /= -HK.
  - apply elem_of_app in Hin as [Hin | Hin].
    + destruct (IH e1 r Hin) as [K HK]. exists (K ++ [FreeLCtx e2]).
      by rewrite fill_app /= -HK.
    + destruct (to_val e1) as [v1|] eqn:Hv; last by apply elem_of_nil in Hin.
      destruct (IH e2 r Hin) as [K HK]. exists (K ++ [FreeRCtx v1]).
      by rewrite fill_app /= -HK (of_to_val _ _ Hv).
  - destruct (IH e r Hin) as [K HK]. exists (K ++ [CaseCtx el]).
    by rewrite fill_app /= -HK.
Qed.

Global Instance lr_step_dec e m : Decision (exists T e' m', lr_step e m T e' m').
Proof.
  destruct (decide (Exists (fun r => exists T e' m', lr_head_step r m T e' m')
    (lr_redexes e))) as [H | H].
  - left. apply Exists_exists in H as (r & Hin & T & e' & m' & Hstep).
    destruct (lr_redexes_sound e r Hin) as [K ->].
    do 3 eexists. by constructor.
  - right. intros (T & e' & m' & Hstep). apply H. apply Exists_exists.
    destruct Hstep as [K r m T r' m' Hhead]. exists r. split; last by do 3 eexists.
    apply lr_redexes_fill. destruct r; by left.
Defined.

Global Instance lr_external_dec e : Decision (exists op k, lr_external e op k).
Proof.
  destruct (decide (Exists (fun r => exists op k, lr_head_external r op k)
    (lr_redexes e))) as [H | H].
  - left. apply Exists_exists in H as (r & Hin & op & k & Hext).
    destruct (lr_redexes_sound e r Hin) as [K ->].
    do 2 eexists. by constructor.
  - right. intros (op & k & Hext). apply H. apply Exists_exists.
    destruct Hext as [K r op k Hhead]. exists r. split; last by do 2 eexists.
    apply lr_redexes_fill. destruct r; by left.
Defined.


End decisions.

(** The sequential semantics together with its classification and external-call laws. *)
#[global] Canonical Structure lr_language :
    @sqlang loc val _ _ lr_mem lr_layout expr.
Proof.
  refine {| sqlang_memory := lr_memory;
     sqlang_thrd_st := expr;
     sqlang_true_val := LitV (lit_of_bool true);
     sqlang_false_val := LitV (lit_of_bool false);
     sqlang_step := lr_step;
     sqlang_expr_to_thrd_st := id;
     sqlang_at_external := lr_external;
     sqlang_is_final := to_val;
     sqlang_ValEq := lr_val_eq;
     sqlang_ValNEq := lr_val_neq |}.
  - intros e m.
    destruct (to_val e) as [v|] eqn:Hfinal.
    + have Hnoext : ~ (exists op k, lr_external e op k).
      { intros (op & k & Hext). apply lr_external_not_val in Hext. congruence. }
      have Hnostep : ~ (exists T e' m', lr_step e m T e' m').
      { intros (T & e' & m' & Hstep). apply lr_step_not_val in Hstep. congruence. }
      exists SqValue. split; first by exists v.
      intros []; cbn; rewrite /is_Some; naive_solver.
    + destruct (decide (exists T e' m', lr_step e m T e' m')) as [Hstep | Hnostep].
      * have Hnoext : ~ (exists op k, lr_external e op k).
        { intros (op & k & Hext). destruct Hstep as (T & e' & m' & Hstep).
          by eapply lr_step_external_disjoint. }
        exists SqStep. split; first exact Hstep.
        intros []; cbn; rewrite /is_Some; naive_solver.
      * destruct (decide (exists op k, lr_external e op k)) as [Hext | Hnoext].
        -- exists SqExternal. split; first exact Hext.
           intros []; cbn; rewrite /is_Some; naive_solver.
        -- exists SqStuck. split.
           ++ split; first done. done.
           ++ intros []; cbn; rewrite /is_Some; naive_solver.
  - apply lr_external_det.
Defined.
#[global] Existing Instance lr_language.

(** Allocation events change an unallocated location into an allocated one;
    every data access is to a location present before this step. *)
#[global] Instance lr_alloc_laws : SqAllocLaws (L := lr_language).
Proof.
  refine {| sq_loc_allocated := fun m l => is_Some (m !! l) |}.
  - intros e m evs e' m' o l Hstep Halloc. destruct Hstep;
      try (apply list_elem_of_singleton in Halloc; discriminate); last by inversion Halloc.
    apply list_elem_of_fmap in Halloc as (ev & Heq & Hin). injection Heq as <-.
    destruct (lr_step_alloc_footprint Hstep Hin) as [Hnone Hsome].
    rewrite Hnone Hsome. split; [by intros [v Hv] | by eexists].
  - intros e m evs e' m' o ev l w Hstep Hin Haccess. destruct Hstep; last by inversion Hin.
    { apply list_elem_of_fmap in Hin as (ev0 & -> & Hin).
      left. by eapply lr_step_access_allocated. }
    all: apply list_elem_of_singleton in Hin as ->; destruct Haccess as [Hl _];
      apply list_elem_of_singleton in Hl as <-; left; try by eexists.
    simpl in Hstore. destruct (m !! l); [by eexists | discriminate].
Qed.
