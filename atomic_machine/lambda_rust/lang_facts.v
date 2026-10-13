(** Facts about lambda-Rust syntax and heaps used by the correspondence
    between the reference semantics and the atomic machine: unique
    decomposition around a redex, freedom from the administrative
    [Na2Ord] accesses, heap ranges, and the heap-domain dependence of
    literal comparison. *)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.

Require Import VST.atomic_machine.lambda_rust.reference.

Import ListNotations.

Set Default Proof Using "Type".

(** * Syntactic infrastructure

    Ported from the upstream lambda-Rust [lang.v]: evaluation contexts
    decompose uniquely around a head redex. *)

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof. destruct e; simpl; try case_decide; intros; by simplify_eq. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros v1 v2 H%(f_equal to_val). rewrite !to_of_val in H. by simplify_eq. Qed.

Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. revert e. induction K1; simpl; auto. Qed.

Lemma fill_item_not_val Ki e : to_val (fill_item Ki e) = None.
Proof. by destruct Ki. Qed.

Lemma fill_not_val K e : to_val e = None -> to_val (fill K e) = None.
Proof. revert e. induction K; simpl; eauto using fill_item_not_val. Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None -> to_val e2 = None ->
  map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 ->
  vl1 = vl2 /\ e1 = e2 /\ el1 = el2.
Proof.
  revert vl2. induction vl1 as [ | v1 vl1 IH ]; intros [ | v2 vl2 ] He1 He2 H; injection H as H1 H2;
    [ by subst | by rewrite H1, to_of_val in He1 | by rewrite <- H1, to_of_val in He2 | ].
  apply (inj of_val) in H1 as ->. by destruct (IH vl2 He1 He2 H2) as (-> & -> & ->).
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None -> to_val e2 = None ->
  fill_item Ki1 e1 = fill_item Ki2 e2 -> Ki1 = Ki2 /\ e1 = e2.
Proof.
  intros He1 He2 H. destruct Ki1, Ki2; simplify_eq/=; auto;
    repeat match goal with H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H end.
  match goal with H : map of_val _ ++ _ :: _ = map of_val _ ++ _ :: _ |- _ =>
    by destruct (list_expr_val_eq_inv _ _ _ _ _ _ He1 He2 H) as (-> & -> & ->) end.
Qed.

(** An expression has redex shape if it is not itself a strict context
    around a non-value.  Head redexes and the administrative [Na2Ord]
    accesses have this shape, so their evaluation context is unique. *)

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
      destruct (fill_item_no_val_inj Ki Kj (fill K1 e1) (fill K2 e2)
                  (fill_not_val K1 e1 Hv1) (fill_not_val K2 e2 Hv2) Hfill) as (-> & Hfill').
      by destruct (IH K2 Hfill') as (-> & ->).
Qed.

Lemma head_step_not_val e1 sigma1 e2 sigma2 spawned :
  head_step e1 sigma1 e2 sigma2 spawned -> to_val e1 = None.
Proof. by destruct 1. Qed.

Lemma head_step_redex_shape e1 sigma1 e2 sigma2 spawned :
  head_step e1 sigma1 e2 sigma2 spawned -> redex_shape e1.
Proof.
  intros Hstep Ki e' Heq.
  destruct Hstep; destruct Ki; simplify_eq/=; rewrite ?to_of_val; eauto.
  - by case_decide.
  - by apply Forall_app, proj2, Forall_cons in H as [? _].
Qed.

Lemma na2_read_redex_shape l : redex_shape (Read Na2Ord (Lit (LitLoc l))).
Proof. intros Ki e' Heq. destruct Ki; simplify_eq/=; eauto. Qed.

Lemma na2_write_redex_shape l e v : to_val e = Some v -> redex_shape (Write Na2Ord (Lit (LitLoc l)) e).
Proof. intros He Ki e' Heq. destruct Ki; simplify_eq/=; eauto. Qed.

(** * Freedom from administrative accesses

    [Na2Ord] is an administrative state of the reference semantics, but it
    is also syntax, and a program that mentions it directly can decrement a
    reader count it never incremented.  Such a program is stuck on the
    machine (which has no rule for [Na2Ord]) yet may reach a "stable"
    reference configuration, so the correspondence excludes it. *)

Fixpoint na2_free (e : expr) : bool :=
  match e with
  | Var _ | Lit _ => true
  | Rec _ _ e | Alloc e | Fork e => na2_free e
  | BinOp _ e1 e2 | Free e1 e2 => na2_free e1 && na2_free e2
  | App e el | Case e el => na2_free e && forallb na2_free el
  | Read o e => match o with Na2Ord => false | _ => na2_free e end
  | Write o e1 e2 => match o with Na2Ord => false | _ => na2_free e1 && na2_free e2 end
  | CAS e0 e1 e2 => na2_free e0 && na2_free e1 && na2_free e2
  end.

Ltac na2_split :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | |- (_ && _) = true => apply andb_true_iff; split
  end.

Lemma na2_free_fill_item_inv Ki e :
  na2_free (fill_item Ki e) = true -> na2_free e = true.
Proof. destruct Ki; simpl; try destruct o; rewrite ?forallb_app; simpl; intros; na2_split; auto; discriminate. Qed.

Lemma na2_free_fill_item Ki e e' :
  na2_free (fill_item Ki e) = true -> na2_free e' = true -> na2_free (fill_item Ki e') = true.
Proof. destruct Ki; simpl; try destruct o; rewrite ?forallb_app; simpl; intros; na2_split; auto; discriminate. Qed.

Lemma na2_free_fill_inv K e :
  na2_free (fill K e) = true -> na2_free e = true.
Proof. revert e. induction K; simpl; eauto using na2_free_fill_item_inv. Qed.

Lemma na2_free_fill K e e' :
  na2_free (fill K e) = true -> na2_free e' = true -> na2_free (fill K e') = true.
Proof.
  revert e e'. induction K as [ | Ki K IH ]; simpl; intros e e' H He'; [ done | ].
  eapply IH; [ exact H | ]. eapply na2_free_fill_item; eauto using na2_free_fill_inv.
Qed.

Lemma na2_free_subst x es e :
  na2_free es = true -> na2_free e = true -> na2_free (subst x es e) = true.
Proof.
  intros Hes. revert e. fix IH 1. intros e He.
  destruct e; simpl in *; repeat case_match; na2_split; auto;
    match goal with el : list expr |- _ => induction el; simpl in *; na2_split; auto end.
Qed.

Lemma na2_free_subst' mx es e :
  na2_free es = true -> na2_free e = true -> na2_free (subst' mx es e) = true.
Proof. destruct mx; simpl; auto using na2_free_subst. Qed.

Lemma na2_free_subst_l xl esl e e' :
  forallb na2_free esl = true -> na2_free e = true ->
  subst_l xl esl e = Some e' -> na2_free e' = true.
Proof.
  revert esl e'. induction xl as [ | mx xl IH ]; intros [ | es esl ] e' Hesl He Hsubst;
    simpl in *; na2_split; simplify_eq; [ done | ].
  destruct (subst_l xl esl e) eqn:Hsub; simplify_eq/=. eauto using na2_free_subst'.
Qed.

Lemma stuck_term_redex_shape : redex_shape stuck_term.
Proof.
  intros Ki e' Heq. destruct Ki; unfold stuck_term in Heq; simplify_eq/=; eauto. by destruct vl.
Qed.

Lemma crashed_no_step K sigma1 e2 sigma2 spawned :
  ~ prim_step (fill K stuck_term) sigma1 e2 sigma2 spawned.
Proof.
  intros Hstep. inversion Hstep as [K' e1 ? ? ? ? Hhead HK]; subst.
  destruct (fill_redex_unique K' K e1 stuck_term
              (head_step_redex_shape _ _ _ _ _ Hhead) stuck_term_redex_shape
              (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (_ & ->).
  inversion Hhead.
Qed.

Lemma na2_free_read_na2 K l : na2_free (fill K (Read Na2Ord (Lit (LitLoc l)))) = false.
Proof. apply not_true_is_false. intros H%na2_free_fill_inv. discriminate. Qed.

Lemma na2_free_write_na2 K l e : na2_free (fill K (Write Na2Ord (Lit (LitLoc l)) e)) = false.
Proof. apply not_true_is_false. intros H%na2_free_fill_inv. discriminate. Qed.

(** * Heap ranges

    Allocation and deallocation act on a contiguous range of locations.
    [init_mem]/[free_mem] and the machine's event lists are all described
    through [loc_in_range]. *)

Definition loc_in_range (l : loc) (n : nat) (l' : loc) : Prop :=
  l'.1 = l.1 /\ (l.2 <= l'.2 < l.2 + Z.of_nat n)%Z.

Instance loc_in_range_dec l n l' : Decision (loc_in_range l n l').
Proof. unfold loc_in_range. apply _. Defined.

Lemma loc_in_range_shift l n l' :
  loc_in_range l n l' -> exists z, (0 <= z < Z.of_nat n)%Z /\ l' = (l +ₗ z)%L.
Proof.
  destruct l as [b o], l' as [b' o']. unfold loc_in_range, shift_loc. simpl.
  intros (-> & Hr). exists (o' - o)%Z. split; [ lia | ]. f_equal. lia.
Qed.

(** Shared proof of the two range lookups; [step] rewrites the head
    insertion/deletion at the looked-up location. *)

Ltac range_lookup_base :=
  case_decide; [ | done ]; unfold loc_in_range in *; simpl in *; lia.

Ltac range_lookup_step IH l l' :=
  destruct (decide (l = l')) as [-> | Hne];
  [ first [ rewrite lookup_insert_eq | rewrite lookup_delete_eq ];
    case_decide; [ done | ]; unfold loc_in_range in *; simpl in *; lia
  | first [ rewrite lookup_insert_ne | rewrite lookup_delete_ne ]; [ | done ]; rewrite IH;
    destruct l as [b o], l' as [b' o']; unfold loc_in_range, shift_loc in *; simpl in *;
    do 2 case_decide; try done; exfalso; [ lia | apply Hne; f_equal; lia ] ].

Lemma lookup_init_mem {A : Type} (x : A) (l : loc) (n : nat) (sigma : gmap loc A) (l' : loc) :
  init_mem x l n sigma !! l' =
    if decide (loc_in_range l n l') then Some x else sigma !! l'.
Proof.
  revert l. induction n as [ | n IH ]; intros l; simpl; [ range_lookup_base | range_lookup_step IH l l' ].
Qed.

Lemma lookup_free_mem {A : Type} (l : loc) (n : nat) (sigma : gmap loc A) (l' : loc) :
  free_mem l n sigma !! l' =
    if decide (loc_in_range l n l') then None else sigma !! l'.
Proof.
  revert l. induction n as [ | n IH ]; intros l; simpl; [ range_lookup_base | range_lookup_step IH l l' ].
Qed.

(** [bin_op_eval] only consults the heap through [lit_eq]'s dangling-pointer
    cases, and those only observe the domain. *)

Lemma lit_eq_dom {A B : Type} (sigma : gmap loc A) (m : gmap loc B) lit1 lit2 :
  (forall l, sigma !! l = None -> m !! l = None) ->
  lit_eq sigma lit1 lit2 -> lit_eq m lit1 lit2.
Proof. destruct 2; eauto using lit_eq. Qed.

Lemma lit_neq_dom {A B : Type} (sigma : gmap loc A) (m : gmap loc B) lit1 lit2 :
  lit_neq sigma lit1 lit2 -> lit_neq m lit1 lit2.
Proof. destruct 1; constructor; auto. Qed.

Lemma bin_op_eval_dom {A B : Type} (sigma : gmap loc A) (m : gmap loc B) op lit1 lit2 lit' :
  (forall l, sigma !! l = None -> m !! l = None) ->
  bin_op_eval sigma op lit1 lit2 lit' -> bin_op_eval m op lit1 lit2 lit'.
Proof. destruct 2; constructor; eauto using lit_eq_dom, lit_neq_dom. Qed.

