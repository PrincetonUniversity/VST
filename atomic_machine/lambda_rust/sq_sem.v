(** Single-threaded lambda-Rust semantics for the atomic machine. *)

From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import base gmap list.

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

(** A thread has terminated once it is a value. *)
Definition lr_final (e : expr) : Prop := is_Some (to_val e).

#[global] Canonical Structure lr_language :
    @sqlang loc val _ _ lr_mem lr_layout expr :=
  {| sqlang_memory := lr_memory;
     sqlang_thrd_st := expr;
     sqlang_true_val := LitV (lit_of_bool true);
     sqlang_false_val := LitV (lit_of_bool false);
     sqlang_step := lr_step;
     sqlang_expr_to_thrd_st := id;
     sqlang_at_external := lr_external;
     sqlang_final := lr_final;
     sqlang_ValEq := lr_val_eq;
     sqlang_ValNEq := lr_val_neq |}.
#[global] Existing Instance lr_language.

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
