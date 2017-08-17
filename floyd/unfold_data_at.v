Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.array_lemmas.
Require Import Coq.Logic.JMeq.
Opaque alignof.

Local Open Scope logic.

(********************************************

The following part is for unfold_field_at tactic.

********************************************)

Lemma lower_sepcon_val:
  forall (P Q: val->environ->mpred) v,
  ((P*Q) v) = (P v * Q v).
Proof. reflexivity. Qed.

Definition opaque_sepcon := @sepcon (val->mpred) _ _.
Global Opaque opaque_sepcon.
Definition opaque_emp := @emp (val->mpred) _ _.
Global Opaque opaque_emp.

Lemma distribute_envtrans:
  forall A (P Q: A -> mpred) (J: environ -> A),
   @liftx (Tarrow A (LiftEnviron mpred))
   (@sepcon (A -> mpred) _ _ P Q) J =
   (@liftx (Tarrow A (LiftEnviron mpred)) P J
    * @liftx (Tarrow A (LiftEnviron mpred)) Q J ).
Proof. reflexivity. Qed.
Hint Rewrite distribute_envtrans: norm2.

Lemma distribute_envtrans0:
  forall (P Q: mpred),
   @liftx (LiftEnviron mpred)
   (@sepcon mpred _ _ P Q) =
   @liftx (LiftEnviron mpred) P *
   @liftx (LiftEnviron mpred) Q.
Proof. intros. reflexivity. Qed.
Hint Rewrite distribute_envtrans0: norm2.

Lemma distribute_lifted_sepcon:
 forall A F G v,
  (@sepcon (A -> mpred) _ _ F G v) = @sepcon mpred _ _ (F v) (G v).
Proof. reflexivity. Qed.

Lemma lift_at_offset_mapsto: forall pos sh t v p, `(at_offset pos (fun p0 : val => mapsto sh t p0 v)) p = `(mapsto sh t) (`(offset_val (Int.repr pos)) p) `v.
Proof. intros. reflexivity. Qed.

Lemma at_offset_mapsto: forall pos sh t v p, (at_offset pos (fun p0 : val => mapsto sh t p0 v)) p = (mapsto sh t) (offset_val (Int.repr pos) p) v.
Proof. intros. reflexivity. Qed.

Lemma lift_mapsto: forall sh t v p, `(fun p0 : val => mapsto sh t p0 v) p = `(mapsto sh t) p `v.
Proof. intros. reflexivity. Qed.

Lemma lift_at_offset_memory_block: forall pos sh len p, `(at_offset pos (memory_block sh len)) p = `(memory_block sh len) (`(offset_val (Int.repr pos)) p).
Proof. intros. reflexivity. Qed.

Lemma at_offset_memory_block: forall pos sh len p, (at_offset pos (memory_block sh len)) p = (memory_block sh len) (offset_val (Int.repr pos) p).
Proof. intros. reflexivity. Qed.

Lemma lift_at_offset_data_at: forall pos sh t v p, `(at_offset pos (data_at sh t v)) p = `(data_at sh t v) (`(offset_val (Int.repr pos)) p).
Proof. intros. reflexivity. Qed.

Lemma at_offset_data_at: forall pos sh t v p, (at_offset pos (data_at sh t v)) p = (data_at sh t v) (offset_val (Int.repr pos) p).
Proof. intros. reflexivity. Qed.

Ltac unfold_nested_field H :=
  unfold nested_field_type2, nested_field_offset2 in H;
  match type of H with
  | appcontext [nested_field_rec ?T ?IDS] =>
    simpl (match nested_field_rec T IDS with | Some _ => _ | None => _ end) in H
  end.

Ltac unfold_field_at' H :=
  first [
    erewrite field_at_Tarray in H; [| try unfold tarray; reflexivity  | reflexivity | eauto]
  |
    erewrite field_at_Tstruct in H; try reflexivity; try reflexivity;
   unfold nested_sfieldlist_at, withspacer in H].

Ltac floyd_simpl T H MA TAC :=
   try unfold T in H;  (* need "try" in case T is not just a simple identifier *)
   TAC H;
   replace (@sepcon (val -> mpred) (@LiftNatDed val mpred Nveric)
     (@LiftSepLog val mpred Nveric Sveric)) with opaque_sepcon in H by reflexivity;
   change (@emp (val->mpred) _ _) with opaque_emp in H;
   simpl in H;
   (* can't use "@sepcon (val->mpred) _ _" with implicit arguments in next two lines,
     otherwise trigger Coq bug 2997 if there are evars in context *)
   change @opaque_sepcon with (@sepcon (val -> mpred) (@LiftNatDed val mpred Nveric)
  (@LiftSepLog val mpred Nveric Sveric)) in H;
   change @opaque_emp with (@emp (val->mpred) (@LiftNatDed val mpred Nveric)
  (@LiftSepLog val mpred Nveric Sveric)) in H;
(*
   repeat
    match type of H with
    | appcontext [(field_at ?sh ?ids ?t Vundef)] =>
     change (field_at sh ids t Vundef) with (?????) in H
    end;
    fold tuint in H; fold tint in H;
*)
   try fold T in H,MA; (* need "try" in case T is not just a simple identifier *)
   repeat rewrite positive_nat_Z in H;
   repeat rewrite sepcon_emp in H || rewrite emp_sepcon in H;
   repeat rewrite distribute_lifted_sepcon in H;
   repeat rewrite distribute_envtrans in H;
   repeat rewrite distribute_envtrans0 in H;
   repeat rewrite lift_at_offset_mapsto in H;
   repeat rewrite lift_mapsto in H;
   repeat rewrite lift_at_offset_memory_block in H;
   repeat rewrite at_offset_mapsto in H;
   repeat rewrite at_offset_memory_block in H;
   subst MA;
   repeat rewrite distribute_lifted_sepcon;
   repeat rewrite distribute_envtrans;
   repeat rewrite distribute_envtrans0;
   repeat flatten_sepcon_in_SEP;
   simpl @fst; simpl @snd; simpl align; simpl Z.max.

Definition opaque_field_at := field_at.
Global Opaque opaque_field_at.

Definition opaque_data_at := data_at.
Global Opaque opaque_data_at.

Lemma opaque_nda1: field_at = opaque_field_at.
Proof. reflexivity. Qed.

Lemma opaque_nda2: data_at = opaque_data_at.
Proof. intros. reflexivity. Qed.

Ltac unfold_field_at N :=
  match N with
  | S O =>
    let H := fresh "H" in let MA := fresh "MA" in
    pattern field_at at 1;
    rewrite opaque_nda1;
    match goal with
    | |- appcontext [`(opaque_field_at ?SH ?T ?IDS ?v) ?p] =>
           remember (`(opaque_field_at SH T IDS v) p) as MA eqn:H in |-*;
           rewrite <- opaque_nda1 in H;
           try floyd_simpl T H MA unfold_field_at';
           try subst MA
    | |- appcontext [(opaque_field_at ?SH ?T ?IDS ?v) ?p] =>
           remember ((opaque_field_at SH T IDS v) p) as MA eqn:H in |-*;
           rewrite <- opaque_nda1 in H;
           try floyd_simpl T H MA unfold_field_at';
           try subst MA
    end
  | S ?n' =>
    let H := fresh "H" in let MA := fresh "MA" in
    pattern field_at at 1;
    rewrite opaque_nda1;
    remember opaque_field_at as MA eqn:H in |- * ;
    unfold_field_at n';
    rewrite <- opaque_nda1 in H;
    subst MA
  end.

Ltac unfold_data_at N :=
  match N with
  | S O =>
    let H := fresh "H" in let MA := fresh "MA" in
    pattern data_at at 1;
    rewrite opaque_nda2;
    match goal with
    | |- appcontext [`(opaque_data_at ?SH ?T ?v) ?p] =>
           remember (`(opaque_data_at SH T v) p) as MA eqn:H in |-*;
           rewrite <- opaque_nda2 in H;
           rewrite data_at_field_at in H;
           try floyd_simpl T H MA unfold_field_at';
           try subst MA
    | |- appcontext [(opaque_data_at ?SH ?T ?v) ?p] =>
           remember ((opaque_data_at SH T v) p) as MA eqn:H in |-*;
           rewrite <- opaque_nda2 in H;
           rewrite data_at_field_at in H;
           try floyd_simpl T H MA unfold_field_at';
           try subst MA
    end
  | S ?n' =>
    let H := fresh "H" in let MA := fresh "MA" in
    pattern data_at at 1;
    rewrite opaque_nda2;
    remember opaque_data_at as MA eqn:H in |- * ;
    unfold_data_at n';
    rewrite <- opaque_nda2 in H;
    subst MA
  end.

(********************************************

The following part is for simpl_data_at tactic

********************************************)
(*
Ltac simpl_data_at_rec H :=
  unfold data_at_, data_at, data_at_rec, withspacer, at_offset', at_offset2, align, Z.max in H.

Ltac simpl_data_at :=
  repeat (
    let H := fresh "H" in let MA := fresh "MA" in
    try unfold data_at_;
    match goal with
    | |- appcontext [`(field_at ?SH ?T ?IDS ?v) ?p] =>
           remember (`(field_at SH T IDS v) p) as MA eqn:H in |-*;
           rewrite field_at_data_at in H;
           floyd_simpl T H MA simpl_data_at_rec
    | |- appcontext [(field_at ?SH ?T ?IDS ?v) ?p] =>
           remember ((field_at SH T IDS v) p) as MA eqn:H in |-*;
           rewrite field_at_data_at in H;
           floyd_simpl T H MA simpl_data_at_rec
    | |- appcontext [field_at ?SH ?T ?IDS] =>
           remember (field_at SH T IDS) as MA eqn:H in |-*;
           rewrite field_at_data_at in H;
           floyd_simpl T H MA simpl_data_at_rec
    | |- appcontext [`(data_at ?SH ?T ?v) ?p] =>
           remember (`(data_at SH T v) p) as MA eqn:H in |-*;
           floyd_simpl T H MA simpl_data_at_rec
    | |- appcontext [(data_at ?SH ?T ?v) ?p] =>
           remember ((data_at SH T v) p) as MA eqn:H in |-*;
           floyd_simpl T H MA simpl_data_at_rec
    | |- appcontext [data_at ?SH ?T] =>
           remember (data_at SH T) as MA eqn:H in |-*;
           floyd_simpl T H MA simpl_data_at_rec
    end).

*)