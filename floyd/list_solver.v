(*Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.coqlib4.  (* just for prop_unext *)
*)
Require Import ZArith Znumtheory.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Export VST.floyd.sublist.
Import SublistInternalLib.
(*
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
*)
Require Export VST.floyd.Zlength_solver.

(** This file provides a almost-complete solver for list with concatenation.
  Its core symbols include:
    Zlength
    Znth
    Zrepeat
    app
    sublist
    map.
  And it also interprets these symbols by convernting to core symbols:
    nil
    cons
    upd_Znth. *)

(** * list_form *)
Lemma repeat_Zrepeat : forall (A : Type) (x : A) (n : Z),
  repeat x (Z.to_nat n) = Zrepeat x n.
Proof. intros *. auto. Qed.

Lemma cons_Zrepeat_1_app : forall (A : Type) (x : A) (al : list A),
  x :: al = Zrepeat x 1 ++ al.
Proof. auto. Qed.

Lemma upd_Znth_unfold : forall (A : Type) (n : Z) (al : list A) (x : A),
  0 <= n < Zlength al ->
  upd_Znth n al x = sublist 0 n al ++ [x] ++ sublist (n+1) (Zlength al) al.
Proof. intros. rewrite upd_Znth_old_upd_Znth; auto. Qed.

(** * Znth_solve *)
(** Znth_solve is a tactic that simplifies and solves proof goal related to terms headed by Znth. *)

(* Auxilary lemmas for Znth_solve. *)
Lemma Znth_Zrepeat : forall (A : Type) (d : Inhabitant A) (i n : Z) (x : A),
  0 <= i < n ->
  Znth i (Zrepeat x n) = x.
Proof. intros. unfold Zrepeat. apply Znth_repeat_inrange; auto. Qed.

Definition Znth_app1 := app_Znth1.
Definition Znth_app2 := app_Znth2.

Lemma Znth_upd_Znth_same : forall (A : Type) (d : Inhabitant A) (i j : Z) (l : list A) (x : A),
  0 <= i < Zlength l ->
  i = j ->
  Znth i (upd_Znth j l x) = x.
Proof.
  intros. subst. apply upd_Znth_same; auto.
Qed.

Lemma Znth_upd_Znth_diff : forall (A : Type) (d : Inhabitant A) (i j : Z) (l : list A) (x : A),
  i <> j ->
  Znth i (upd_Znth j l x) = Znth i l.
Proof.
  intros.
  destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_gt_dec 0 i) (Z_lt_ge_dec i (Zlength l)));
    destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_gt_dec 0 j) (Z_lt_ge_dec j (Zlength l))).
  - rewrite upd_Znth_diff; auto.
  - rewrite upd_Znth_out_of_range; auto.
  - rewrite !Znth_outofbounds; auto. lia.
    rewrite Zlength_upd_Znth. lia.
  - rewrite upd_Znth_out_of_range; auto.
Qed.

(** * list extentionality *)
(* To prove equality between two lists, a convenient way is to apply extentionality
  and prove their length are equal and each corresponding entries are equal.
  It is convenient because then we can use Znth_solve to solve it. *)

Lemma nth_eq_ext : forall (A : Type) (default : A) (al bl : list A),
  length al = length bl ->
  (forall (i : nat), (0 <= i < length al)%nat -> nth i al default = nth i bl default) ->
  al = bl.
Proof.
  intros. generalize dependent bl.
  induction al; intros;
    destruct bl; try discriminate; auto.
  f_equal.
  - apply (H0 0%nat). simpl. lia.
  - apply IHal.
    + simpl in H. lia.
    + intros. apply (H0 (S i)). simpl. lia.
Qed.

Lemma Znth_eq_ext : forall {A : Type} {d : Inhabitant A} (al bl : list A),
  Zlength al = Zlength bl ->
  (forall (i : Z), 0 <= i < Zlength al -> Znth i al = Znth i bl) ->
  al = bl.
Proof.
  intros. rewrite !Zlength_correct in *. apply nth_eq_ext with d.
  - lia.
  - intros. rewrite  <- (Nat2Z.id i).
    specialize (H0 (Z.of_nat i) ltac:(lia)).
    rewrite !nth_Znth by (rewrite !Zlength_correct in *; lia).
    apply H0.
Qed.

Hint Rewrite repeat_Zrepeat cons_Zrepeat_1_app : list_solve_rewrite.
Hint Rewrite app_nil_r app_nil_l : list_solve_rewrite.
(* Hint Rewrite upd_Znth_unfold using Zlength_solve : list_solve_rewrite. *)

Ltac list_form :=
  autorewrite with list_solve_rewrite in *.

(** * Znth_solve *)
(** Znth_solve is a tactic that simplifies and solves proof goal related to terms headed by Znth. *)

Hint Rewrite @Znth_repeat_inrange using Zlength_solve : Znth.
Hint Rewrite @Znth_sublist using Zlength_solve : Znth.
Hint Rewrite Znth_app1 Znth_app2 using Zlength_solve : Znth.
Hint Rewrite Znth_Zrepeat using Zlength_solve : Znth.
Hint Rewrite Znth_upd_Znth_same Znth_upd_Znth_diff using Zlength_solve : Znth.

Hint Rewrite (@Znth_map _ Inhabitant_Z) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_nat) using Zlength_solve : Znth.

Create HintDb Znth_solve_hint.

(** Znth_solve_rec is the main loop of Znth_solve. It tries to simplify
  the goal and branches when encountering an uncertain concatenation. *)
Ltac Znth_solve_rec :=
  autorewrite with Znth;
  Zlength_simplify;
  auto with Znth_solve_hint;
  try match goal with
  | |- context [Znth ?n (app ?al ?bl)] =>
    let H := fresh in
    pose (H := Z_lt_ge_dec n (Zlength al));
    Zlength_simplify_in H; destruct H;
    Znth_solve_rec
  | |- context [Znth ?n (upd_Znth ?i ?l ?x)] =>
    let H := fresh in
    pose (H := Z.eq_dec n i);
    Zlength_simplify_in H; destruct H;
    Znth_solve_rec
  | |- context [Znth ?n (map ?f ?l)] =>
    unshelve erewrite @Znth_map by Zlength_solve
      (* only 1 : auto with typeclass_instances *)
  end.

Ltac Znth_solve :=
  Zlength_simplify_in_all;
  Znth_solve_rec.

(** Znth_solve2 is like Znth_solve, but it also branches concatenation in context. *)
Ltac Znth_solve2 :=
  Zlength_simplify_in_all; autorewrite with Znth in *; try Zlength_solve; try congruence; (* try solve [exfalso; auto]; *)
  try first
  [ match goal with
    | |- context [Znth ?n (?al ++ ?bl)] =>
          let H := fresh in
          pose (H := Z_lt_ge_dec n (Zlength al)); Zlength_simplify_in_all; destruct H; Znth_solve2
    end
  | match goal with
    | |- context [Znth ?n (upd_Znth ?i ?l ?x)] =>
          let H := fresh in
          pose (H := Z.eq_dec n i); Zlength_simplify_in_all; destruct H; Znth_solve2
    end
  | match goal with
    | |- context [Znth ?n (map ?f ?l)] =>
          unshelve erewrite @Znth_map by Zlength_solve
            (* only 1 : auto with typeclass_instances *)
    end
  | match goal with
    | H0 : context [Znth ?n (?al ++ ?bl)] |- _ =>
          let H := fresh in
          pose (H := Z_lt_ge_dec n (Zlength al)); Zlength_simplify_in_all; destruct H; Znth_solve2
    end
  | match goal with
    | H0 : context [Znth ?n (upd_Znth ?i ?l ?x)] |- _ =>
          let H := fresh in
          pose (H := Z.eq_dec n i); Zlength_simplify_in_all; destruct H; Znth_solve2
    end
  | match goal with
    | H0 : context [Znth ?n (map ?f ?l)] |- _ =>
          unshelve erewrite @Znth_map in H0 by Zlength_solve
            (* only 1 : auto with typeclass_instances *)
    end
  ].

(*************** fapply & fassumption *************)
Lemma imp_refl' : forall P Q : Prop,
  P = Q -> P -> Q.
Proof. intros. congruence. Qed.

Ltac fapply H :=
  match type of H with ?HH =>
  eapply (imp_refl' HH); only 2 : exact H
  end.

Ltac fassumption :=
  first
  [ assumption
  | match goal with
    | H : _ |- _ => fapply H; repeat f_equal; match goal with |- (_ = _)%Z => idtac end; Zlength_solve
    end
  ].

(******************* eq_solve ********************)
Local Lemma prop_unext: forall P Q: Prop, P=Q -> (P<->Q).
Proof. intros. subst; split; auto. Qed.

Ltac eq_solve_with tac :=
  solve [
  repeat multimatch goal with
  | |- @eq Z _ _ => lia
  | |- @eq (_ -> _) _ _ => apply functional_extensionality; intros
  | |- _ <-> _ => apply prop_unext
  | _ => f_equal
  | _ => tac
  end
  ].

Tactic Notation "eq_solve" "with" tactic(tac) := eq_solve_with (tac).
Tactic Notation "eq_solve" := eq_solve with fail.

#[export] Hint Extern 1 (@eq _ _ _) => eq_solve : Znth_solve_hint.
(* #[export] Hint Extern 1 (@eq _ _ _) => fassumption : Znth_solve_hint.
#[export] Hint Extern 1 (@eq _ _ _) => congruence : Znth_solve_hint. *)

(*************** range definitions **********************)
Definition forall_i (lo hi : Z) (P : Z -> Prop) :=
  forall i, lo <= i < hi -> P i.

Definition forall_range {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : A -> Prop) :=
  forall_i lo hi (fun i => P (Znth i l)).

Definition forall_i_range {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : Z -> A -> Prop) :=
  forall_i lo hi (fun i => P i (Znth i l)).

Definition forall_range2 {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop) :=
  forall_i lo hi (fun i => P (Znth i al) (Znth (i + offset) bl)).

Definition forall_triangle {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (al : list A) (bl : list B) (P : A -> B -> Prop) :=
  forall i j, x1 <= i < x2 /\ y1 <= j < y2 /\ i <= j + offset -> P (Znth i al) (Znth j bl).


(****************** range lemmas ************************)

Lemma rangei_split : forall (lo mi hi : Z) (P : Z -> Prop),
  lo <= mi <= hi ->
  forall_i lo hi P <-> forall_i lo mi P /\ forall_i mi hi P.
Proof.
  intros. unfold forall_i. split; intros.
  - (* -> *)
    split; intros; apply H0; lia.
  - (* <- *)
    destruct H0.
    destruct (Z_lt_ge_dec i mi).
    + apply H0; lia.
    + apply H2; lia.
Qed.

Lemma rangei_implies : forall (lo hi : Z) (P Q : Z -> Prop),
  forall_i lo hi (fun i => P i -> Q i) ->
  forall_i lo hi P ->
  forall_i lo hi Q.
Proof. unfold forall_i; intros; auto. Qed.

Lemma rangei_iff : forall (lo hi : Z) (P Q : Z -> Prop),
  forall_i lo hi (fun i => P i <-> Q i) ->
  forall_i lo hi P <-> forall_i lo hi Q.
Proof.
  intros. split; apply rangei_implies; unfold forall_i in *; intros; apply H; auto.
Qed.

Lemma rangei_shift : forall (lo hi offset : Z) (P : Z -> Prop),
  forall_i lo hi P <-> forall_i (lo + offset) (hi + offset) (fun i => P (i - offset)).
Proof.
  intros. unfold forall_i. split; intros.
  - (* -> *)
    apply H; lia.
  - (* <- *)
    replace i with (i + offset - offset) by lia.
    apply H; lia.
Qed.

Lemma rangei_and : forall (lo hi : Z) (P Q : Z -> Prop),
  forall_i lo hi (fun i => P i /\ Q i) <->
  forall_i lo hi P /\ forall_i lo hi Q.
Proof.
  unfold forall_i; intros; split; intros.
  + split; intros; specialize (H i ltac:(assumption)); tauto.
  + destruct H. auto.
Qed.

Lemma rangei_shift' : forall (lo hi lo' hi' : Z) (P Q : Z -> Prop),
  let offset := lo' - lo in
  offset = hi' - hi ->
  forall_i lo' hi' (fun i => Q i <-> P (i - offset)) ->
  forall_i lo hi P <-> forall_i lo' hi' Q.
Proof.
  intros.
  replace lo' with (lo + offset) by lia.
  replace hi' with (hi + offset) by lia.
  rewrite rangei_iff with (P := Q) (Q := fun i => P (i - offset)) by fassumption.
  apply rangei_shift.
Qed.

Lemma forall_range_empty : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : A -> Prop),
  lo = hi ->
  forall_range lo hi l P <->
  True.
Proof.
  intros; split; unfold forall_range, forall_i; intros; auto; lia.
Qed.

Lemma forall_range_Zrepeat : forall {A : Type} {d : Inhabitant A} (lo hi n : Z) (x : A) (P : A -> Prop),
  0 <= lo < hi /\ hi <= n ->
  forall_range lo hi (Zrepeat x n) P ->
  P x.
Proof.
  unfold forall_range, forall_i. intros.
  fapply (H0 lo ltac:(lia)). f_equal. Znth_solve.
Qed.

Lemma forall_range_app1 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  forall_range lo hi (al ++ bl) P <->
  forall_range lo hi al P.
Proof.
  unfold forall_range. intros. apply rangei_iff.
  unfold forall_i. intros. apply prop_unext, f_equal. Znth_solve.
Qed.

Lemma forall_range_app2 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  forall_range lo hi (al ++ bl) P ->
  forall_range (lo - Zlength al) (hi - Zlength al) bl P.
Proof.
  unfold forall_range. intros. eapply rangei_shift'. 3 : apply H0.
  + lia.
  + unfold forall_i. intros. apply prop_unext, f_equal. Znth_solve.
Qed.

Lemma forall_range_app : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  forall_range lo hi (al ++ bl) P ->
  forall_range lo (Zlength al) al P /\
  forall_range 0 (hi - Zlength al) bl P.
Proof.
  unfold forall_range. intros. split; intro; intros.
  - specialize (H0 i ltac:(lia)). simpl in H0. autorewrite with Znth in H0. apply H0.
  - specialize (H0 (i + Zlength al) ltac:(lia)). simpl in H0. autorewrite with Znth in H0. fassumption.
Qed.

Lemma forall_range_upd_Znth : forall {A : Type} {d : Inhabitant A} (lo hi i : Z) (al : list A) (x : A) (P : A -> Prop),
  0 <= i < Zlength al ->
  forall_range lo hi (upd_Znth i al x) P <->
  forall_range lo hi (sublist 0 i al ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength al) al) P.
Proof.
  intros.
  rewrite upd_Znth_unfold by Zlength_solve.
  rewrite cons_Zrepeat_1_app, app_nil_r.
  reflexivity.
Qed.

Lemma forall_range_sublist : forall {A : Type} {d : Inhabitant A} (lo hi lo' hi' : Z) (l : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  forall_range lo hi (sublist lo' hi' l) P ->
  forall_range (lo+lo') (hi+lo') l P.
Proof.
  unfold forall_range, forall_i. intros.
  fapply (H0 (i - lo') ltac:(lia)). f_equal. Znth_solve.
Qed.

Lemma forall_range_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi : Z) (l : list A) (f : A -> B) (P : B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  forall_range lo hi (map f l) P ->
  forall_range lo hi l (fun x => P (f x)).
Proof.
  unfold forall_range, forall_i. intros.
  fapply (H0 i ltac:(lia)). f_equal. rewrite Znth_map by lia. auto.
Qed.

Lemma rangei_uni_empty : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : Z -> A -> Prop),
  lo = hi->
  forall_i_range lo hi l P <->
  True.
Proof.
  intros; split; unfold forall_i_range, forall_i; intros; auto; lia.
Qed.

Lemma rangei_uni_Zrepeat : forall {A : Type} {d : Inhabitant A} (lo hi n : Z) (x : A) (P : Z -> A -> Prop),
  0 <= lo < hi /\ hi <= n ->
  forall_i_range lo hi (Zrepeat x n) P ->
  forall_i lo hi (fun i => P i x).
Proof.
  unfold forall_i_range, forall_i. intros.
  fapply (H0 i ltac:(lia)). f_equal. Znth_solve.
Qed.

Lemma rangei_uni_app1 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : Z -> A -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  forall_i_range lo hi (al ++ bl) P <->
  forall_i_range lo hi al P.
Proof.
  unfold forall_i_range. intros. apply rangei_iff.
  unfold forall_i. intros. apply prop_unext. f_equal. Znth_solve.
Qed.

Lemma rangei_uni_app2 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : Z -> A -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  forall_i_range lo hi (al ++ bl) P ->
  forall_i_range (lo - Zlength al) (hi - Zlength al) bl (fun i => P (i + Zlength al)).
Proof.
  unfold forall_i_range. intros. eapply rangei_shift'. 3 : apply H0.
  + lia.
  + unfold forall_i. intros. apply prop_unext. f_equal.
    - lia.
    - Znth_solve.
Qed.

Lemma rangei_uni_app : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : Z -> A -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  forall_i_range lo hi (al ++ bl) P ->
  forall_i_range lo (Zlength al) al P /\
  forall_i_range 0 (hi - Zlength al) bl (fun i => P (i + Zlength al)).
Proof.
  unfold forall_i_range. intros. split; intro; intros.
  - specialize (H0 i ltac:(lia)). simpl in H0. autorewrite with Znth in H0. apply H0.
  - specialize (H0 (i + Zlength al) ltac:(lia)). simpl in H0. autorewrite with Znth in H0. fassumption.
Qed.

Lemma rangei_uni_sublist : forall {A : Type} {d : Inhabitant A}
  (lo hi lo' hi' : Z) (l : list A) (P : Z -> A -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  forall_i_range lo hi (sublist lo' hi' l) P ->
  forall_i_range (lo+lo') (hi+lo') l (fun i => P (i - lo')).
Proof.
  unfold forall_i_range, forall_i. intros.
  fapply (H0 (i - lo') ltac:(lia)). f_equal. Znth_solve.
Qed.

Lemma rangei_uni_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi : Z) (l : list A) (f : A -> B) (P : Z -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  forall_i_range lo hi (map f l) P ->
  forall_i_range lo hi l (fun i x => P i (f x)).
Proof.
  unfold forall_i_range, forall_i. intros.
  fapply (H0 i ltac:(lia)). f_equal. rewrite Znth_map by lia. auto.
Qed.

Lemma forall_range2_rangei_uniA : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop),
  forall_range2 lo hi offset al bl P <->
  forall_i_range lo hi al (fun i x => P x (Znth (i + offset) bl)).
Proof.
  unfold forall_range2, forall_i_range, forall_i. reflexivity.
Qed.

Lemma forall_range2_rangei_uniB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop),
  forall_range2 lo hi offset al bl P <->
  forall_i_range (lo+offset) (hi+offset) bl (fun i => P (Znth (i - offset) al)).
Proof.
  unfold forall_range2, forall_i_range.
  intros. split; intros.
  + eapply rangei_shift'. 3 : exact H.
    - lia.
    - unfold forall_i. intros. eq_solve.
  + eapply rangei_shift'. 3 : exact H.
    - eq_solve.
    - unfold forall_i. intros. eq_solve.
Qed.

Lemma forall_range2_empty : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  lo = hi ->
  forall_range2 lo hi offset l l' P <->
  True.
Proof.
  intros; split; unfold forall_range2, forall_i; intros; auto; lia.
Qed.

Lemma forall_range2A_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  forall_range2 lo hi offset (al ++ bl) l' P <->
  forall_range2 lo hi offset al l' P.
Proof.
  intros *. do 2 rewrite forall_range2_rangei_uniA. apply rangei_uni_app1.
Qed.

Lemma forall_range2A_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  forall_range2 lo hi offset (al ++ bl) l' P ->
  forall_range2 (lo - Zlength al) (hi - Zlength al) (offset + Zlength al) bl l' P.
Proof.
  intros *. do 2 rewrite forall_range2_rangei_uniA. intros.
  apply rangei_uni_app2 in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma forall_range2A_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  forall_range2 lo hi offset (al ++ bl) l' P ->
  forall_range2 lo (Zlength al) offset al l' P /\
  forall_range2 0 (hi - Zlength al) (offset + Zlength al) bl l' P.
Proof.
  intros *. do 3 rewrite forall_range2_rangei_uniA. intros.
  apply rangei_uni_app in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma forall_range2A_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset i : Z) (l : list A) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= i < Zlength l ->
  forall_range2 lo hi offset (upd_Znth i l x)  l' P <->
  forall_range2 lo hi offset (sublist 0 i l ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l) l) l' P.
Proof.
  intros.
  rewrite upd_Znth_unfold by Zlength_solve.
  rewrite cons_Zrepeat_1_app, app_nil_r.
  reflexivity.
Qed.

Lemma forall_range2A_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi lo' hi' offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  forall_range2 lo hi offset (sublist lo' hi' l) l' P ->
  forall_range2 (lo+lo') (hi+lo') (offset-lo') l l' P.
Proof.
  intros *. do 2 rewrite forall_range2_rangei_uniA. intros.
  apply rangei_uni_sublist in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma forall_range2A_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (lo hi offset : Z) (l : list A) (l' : list B) (f : A -> C) (P : C -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  forall_range2 lo hi offset (map f l) l' P ->
  forall_range2 lo hi offset l l' (fun x => P (f x)).
Proof.
  unfold forall_range2, forall_i. intros.
  fapply (H0 i ltac:(lia)).
  eq_solve with (rewrite Znth_map by lia).
Qed.

Lemma forall_range2A_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi n offset : Z) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo < hi /\ hi <= n ->
  forall_range2 lo hi offset (Zrepeat x n) l' P ->
  forall_range (lo + offset) (hi + offset) l' (P x).
Proof.
  unfold forall_range2, forall_range. intros.
  eapply rangei_shift'. 3 : exact H0.
  + lia.
  + unfold forall_i. intros. eq_solve with Znth_solve.
Qed.

Lemma forall_range2B_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= Zlength al' ->
  forall_range2 lo hi offset l (al' ++ bl') P <->
  forall_range2 lo hi offset l al' P.
Proof.
  intros *. do 2 rewrite forall_range2_rangei_uniB. apply rangei_uni_app1.
Qed.

Lemma forall_range2B_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  Zlength al' <= lo + offset <= hi + offset /\ hi + offset <= Zlength al' + Zlength bl' ->
  forall_range2 lo hi offset l (al' ++ bl') P ->
  forall_range2 lo hi (offset - Zlength al') l bl' P.
Proof.
  intros *. do 2 rewrite forall_range2_rangei_uniB. intros.
  apply rangei_uni_app2 in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma forall_range2B_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= Zlength al' /\ Zlength al' <= hi + offset <= Zlength al' + Zlength bl' ->
  forall_range2 lo hi offset l (al' ++ bl') P ->
  forall_range2 lo (Zlength al' - offset) offset l al' P /\
  forall_range2 (Zlength al' - offset) hi (offset - Zlength al') l bl' P.
Proof.
  intros *. do 3 rewrite forall_range2_rangei_uniB. intros.
  apply rangei_uni_app in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma forall_range2B_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset i : Z) (l : list A) (l' : list B) (x : B) (P : A -> B -> Prop),
  0 <= i < Zlength l' ->
  forall_range2 lo hi offset l (upd_Znth i l' x)  P <->
  forall_range2 lo hi offset l (sublist 0 i l' ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l') l') P.
Proof.
  intros.
  rewrite upd_Znth_unfold by Zlength_solve.
  rewrite cons_Zrepeat_1_app, app_nil_r.
  reflexivity.
Qed.

Lemma forall_range2B_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi lo' hi' offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l' ->
  forall_range2 lo hi offset l (sublist lo' hi' l') P ->
  forall_range2 lo hi (offset + lo') l l' P.
Proof.
  intros *. do 2 rewrite forall_range2_rangei_uniB. intros.
  apply rangei_uni_sublist in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma forall_range2B_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (lo hi offset : Z) (l : list A) (l' : list B) (f : B -> C) (P : A -> C -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= Zlength l' ->
  forall_range2 lo hi offset l (map f l') P ->
  forall_range2 lo hi offset l l' (fun x y => P x (f y)).
Proof.
  unfold forall_range2, forall_i. intros.
  fapply (H0 i ltac:(lia)).
  eq_solve with (rewrite Znth_map by lia).
Qed.

Lemma forall_range2B_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi n offset : Z) (l : list A) (x : B) (P : A -> B -> Prop),
  0 <= lo + offset < hi + offset /\ hi + offset <= n ->
  forall_range2 lo hi offset l (Zrepeat x n) P ->
  forall_range lo hi l (fun y => P y x).
Proof.
  unfold forall_range2, forall_range. intros.
  eapply rangei_shift'. 3 : exact H0.
  + lia.
  + unfold forall_i. intros. eq_solve with Znth_solve.
Qed.

Lemma forall_triangle_rangei_uniA : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop),
  forall_triangle x1 x2 y1 y2 offset al bl P <->
  forall_i_range x1 x2 al (fun i x => forall_i_range y1 y2 bl (fun j y => i <= j + offset -> P x y)).
Proof.
  unfold forall_triangle, forall_i_range, forall_i. intuition.
Qed.

Lemma forall_triangle_rangei_uniB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop),
  forall_triangle x1 x2 y1 y2 offset al bl P <->
  forall_i_range y1 y2 bl (fun j y => forall_i_range x1 x2 al (fun i x => i <= j + offset -> P x y)).
Proof.
  unfold forall_triangle, forall_i_range, forall_i. intuition.
Qed.

Lemma forall_triangle_emptyA : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  x1 = x2 ->
  forall_triangle x1 x2 y1 y2 offset l l' P <->
  True.
Proof.
  intros; split; unfold forall_triangle; intros; auto; lia.
Qed.

Lemma forall_triangle_emptyB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  y1 = y2 ->
  forall_triangle x1 x2 y1 y2 offset l l' P <->
  True.
Proof.
  intros; split; unfold forall_triangle; intros; auto; lia.
Qed.

Lemma forall_triangle_emptyAgtB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  x1 >= y2 + offset ->
  forall_triangle x1 x2 y1 y2 offset l l' P <->
  True.
Proof.
  intros; split; unfold forall_triangle; intros; auto; lia.
Qed.

Lemma forall_triangleA_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 <= x2 /\ x2 <= Zlength al ->
  forall_triangle x1 x2 y1 y2 offset (al ++ bl) l' P <->
  forall_triangle x1 x2 y1 y2 offset al l' P.
Proof.
  intros *. do 2 rewrite forall_triangle_rangei_uniA. apply rangei_uni_app1.
Qed.

Lemma forall_triangleA_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  Zlength al <= x1 <= x2 /\ x2 <= Zlength al + Zlength bl ->
  forall_triangle x1 x2 y1 y2 offset (al ++ bl) l' P ->
  forall_triangle (x1 - Zlength al) (x2 - Zlength al) y1 y2 (offset - Zlength al) bl l' P.
Proof.
  intros *. do 2 rewrite forall_triangle_rangei_uniA. intros.
  apply rangei_uni_app2 in H0. 2 : assumption.
  fapply H0.
  repeat first [
    progress f_equal
  | apply functional_extensionality; intros
  ].
  apply propositional_extensionality. split; intros; apply H1; lia.
Qed.

Lemma forall_triangleA_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 <= Zlength al /\ Zlength al <= x2 <= Zlength al + Zlength bl ->
  forall_triangle x1 x2 y1 y2 offset (al ++ bl) l' P ->
  forall_triangle x1 (Zlength al) y1 y2 offset al l' P /\
  forall_triangle 0 (x2 - Zlength al) y1 y2 (offset - Zlength al) bl l' P.
Proof.
  intros *. do 3 rewrite forall_triangle_rangei_uniA. intros.
  apply rangei_uni_app in H0. 2 : assumption.
  fapply H0.
  repeat first [
    progress f_equal
  | apply functional_extensionality; intros
  ].
  apply propositional_extensionality. split; intros; apply H1; lia.
Qed.

Lemma forall_triangleA_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset i : Z) (l : list A) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= i < Zlength l ->
  forall_triangle x1 x2 y1 y2 offset (upd_Znth i l x) l' P <->
  forall_triangle x1 x2 y1 y2 offset (sublist 0 i l ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l) l) l' P.
Proof.
  intros.
  rewrite upd_Znth_unfold by Zlength_solve.
  rewrite cons_Zrepeat_1_app, app_nil_r.
  reflexivity.
Qed.

Lemma forall_triangleA_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi x1 x2 y1 y2 offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 <= x2 /\ x2 <= hi - lo /\ 0 <= lo <= hi /\ hi <= Zlength l ->
  forall_triangle x1 x2 y1 y2 offset (sublist lo hi l) l' P ->
  forall_triangle (x1 + lo) (x2 + lo) y1 y2 (offset + lo) l l' P.
Proof.
  intros *. do 2 rewrite forall_triangle_rangei_uniA. intros.
  apply rangei_uni_sublist in H0. 2 : assumption.
  fapply H0.
  repeat first [
    progress f_equal
  | apply functional_extensionality; intros
  ].
  apply propositional_extensionality. split; intros; apply H1; lia.
Qed.

Lemma forall_triangleA_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (x1 x2 y1 y2 offset : Z) (l : list A) (l' : list B) (f : A -> C) (P : C -> B -> Prop),
  0 <= x1 <= x2 /\ x2 <= Zlength l ->
  forall_triangle x1 x2 y1 y2 offset (map f l) l' P ->
  forall_triangle x1 x2 y1 y2 offset l l' (fun x => P (f x)).
Proof.
  unfold forall_triangle, forall_i. intros.
  fapply (H0 i j ltac:(lia)).
  eq_solve with (rewrite Znth_map by lia).
Qed.

Lemma forall_triangleA_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (n x1 x2 y1 y2 offset : Z) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 < x2 /\ x2 <= n ->
  forall_triangle x1 x2 y1 y2 offset (Zrepeat x n) l' P <->
  forall_range (Z.max y1 (x1 - offset)) (Z.max y2 (x1 - offset)) l' (P x).
Proof.
  unfold forall_triangle, forall_range, forall_i. intros. split; intros.
  - fapply (H0 x1 i ltac:(lia)).
    eq_solve with (rewrite Znth_Zrepeat by lia).
  - fapply (H0 j ltac:(lia)).
    eq_solve with (rewrite Znth_Zrepeat by lia).
Qed.

Lemma forall_triangleB_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= y1 <= y2 /\ y2 <= Zlength al' ->
  forall_triangle x1 x2 y1 y2 offset l (al' ++ bl') P <->
  forall_triangle x1 x2 y1 y2 offset l al' P.
Proof.
  intros *. do 2 rewrite forall_triangle_rangei_uniB. apply rangei_uni_app1.
Qed.

Lemma forall_triangleB_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  Zlength al' <= y1 <= y2 /\ y2 <= Zlength al' + Zlength bl' ->
  forall_triangle x1 x2 y1 y2 offset l (al' ++ bl') P ->
  forall_triangle x1 x2 (y1 - Zlength al') (y2 - Zlength al') (offset + Zlength al') l bl' P.
Proof.
  intros *. do 2 rewrite forall_triangle_rangei_uniB. intros.
  apply rangei_uni_app2 in H0. 2 : assumption.
  fapply H0.
  repeat first [
    progress f_equal
  | apply functional_extensionality; intros
  ].
  apply propositional_extensionality. split; intros; apply H1; lia.
Qed.

Lemma forall_triangleB_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= y1 <= Zlength al' /\ Zlength al' <= y2 <= Zlength al' + Zlength bl' ->
  forall_triangle x1 x2 y1 y2 offset l (al' ++ bl') P ->
  forall_triangle x1 x2 y1 (Zlength al') offset l al' P /\
  forall_triangle x1 x2 0 (y2 - Zlength al') (offset + Zlength al') l bl' P.
Proof.
  intros *. do 3 rewrite forall_triangle_rangei_uniB. intros.
  apply rangei_uni_app in H0. 2 : assumption.
  fapply H0.
  repeat first [
    progress f_equal
  | apply functional_extensionality; intros
  ].
  apply propositional_extensionality. split; intros; apply H1; lia.
Qed.

Lemma forall_triangleB_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset i : Z) (l : list A) (l' : list B) (x : B) (P : A -> B -> Prop),
  0 <= i < Zlength l' ->
  forall_triangle x1 x2 y1 y2 offset l (upd_Znth i l' x)  P <->
  forall_triangle x1 x2 y1 y2 offset l (sublist 0 i l' ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l') l') P.
Proof.
  intros.
  rewrite upd_Znth_unfold by Zlength_solve.
  rewrite cons_Zrepeat_1_app, app_nil_r.
  reflexivity.
Qed.

Lemma forall_triangleB_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 lo hi offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= y1 <= y2 /\ y2 <= hi - lo /\ 0 <= lo <= hi /\ hi <= Zlength l' ->
  forall_triangle x1 x2 y1 y2 offset l (sublist lo hi l') P ->
  forall_triangle x1 x2 (y1 + lo) (y2 + lo) (offset - lo) l l' P.
Proof.
  intros *. do 2 rewrite forall_triangle_rangei_uniB. intros.
  apply rangei_uni_sublist in H0. 2 : assumption.
  fapply H0.
  repeat first [
    progress f_equal
  | apply functional_extensionality; intros
  ].
  apply propositional_extensionality. split; intros; apply H1; lia.
Qed.

Lemma forall_triangleB_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (x1 x2 y1 y2 offset : Z) (l : list A) (l' : list B) (f : B -> C) (P : A -> C -> Prop),
  0 <= y1 <= y2 /\ y2 <= Zlength l' ->
  forall_triangle x1 x2 y1 y2 offset l (map f l') P ->
  forall_triangle x1 x2 y1 y2 offset l l' (fun x y => P x (f y)).
Proof.
  unfold forall_triangle, forall_i. intros.
  fapply (H0 i j ltac:(lia)).
  eq_solve with (rewrite Znth_map by lia).
Qed.

Lemma forall_triangleB_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 n offset : Z) (l : list A) (x : B) (P : A -> B -> Prop),
  0 <= y1 < y2 /\ y2 <= n ->
  forall_triangle x1 x2 y1 y2 offset l (Zrepeat x n) P <->
  forall_range (Z.min x1 (y2 + offset)) (Z.min x2 (y2 + offset)) l (fun y => P y x).
Proof.
  unfold forall_triangle, forall_range, forall_i. intros. split; intros.
  - fapply (H0 i (y2 - 1) ltac:(lia)).
    eq_solve with (rewrite Znth_Zrepeat by lia).
  - fapply (H0 i ltac:(lia)).
    eq_solve with (rewrite Znth_Zrepeat by lia).
Qed.

(** * range_form *)
(** range_form is a tactic that rewrites properties using quantifier or equantion
  of list to range properties defined above. *)

Ltac apply_in lem H :=
  apply lem in H.

Ltac apply_in_hyps' lem :=
  repeat match goal with
  | H : ?T |- _ => apply lem in H; let n := numgoals in guard n = 1
  end.

Tactic Notation "apply_in_hyps" uconstr(lem) := apply_in_hyps' lem.

Ltac apply_in_hyps_with_Zlength_solve lem :=
  repeat match goal with
  | H : _ |- _ => first [apply -> lem in H | apply lem in H]; [idtac | Zlength_solve ..]
  end.

Ltac apply_in_hyps_with_Zlength_solve_destruct lem :=
  repeat match goal with
  | H : _ |- _ => first [apply -> lem in H | apply lem in H]; [destruct H | Zlength_solve ..]
  end.

Lemma not_In_forall_range_iff : forall {A : Type} {d : Inhabitant A} (x : A) (l : list A),
  ~ In x l <-> forall_range 0 (Zlength l) l (fun e => e <> x).
Proof.
  unfold forall_range, forall_i. intros; split; intros.
  - intro. apply H. subst x. apply Znth_In. auto.
  - intro. induction l; auto.
    inversion H0.
    + subst a. apply H with 0. Zlength_solve.
      autorewrite with sublist. auto.
    + apply IHl; auto. intros.
        specialize (H (i+1) ltac:(Zlength_solve)). autorewrite with list_solve_rewrite Znth in *.
        fassumption.
Qed.

Lemma not_In_forall_range : forall {A : Type} {d : Inhabitant A} (x : A) (l : list A),
  ~ In x l -> forall_range 0 (Zlength l) l (fun e => e <> x).
Proof. intros. apply not_In_forall_range_iff. auto. Qed.

Lemma eq_forall_range2_no_offset : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth i l2) ->
  forall_range2 lo hi 0 l1 l2 eq.
Proof. unfold forall_range2, forall_i. intros. replace (i + 0) with i by lia. auto. Qed.

Lemma eq_forall_range2_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth (i + offset) l2) ->
  forall_range2 lo hi offset l1 l2 eq.
Proof. unfold forall_range2, forall_i. auto. Qed.

Lemma eq_forall_range2_left_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth (offset + i) l2) ->
  forall_range2 lo hi offset l1 l2 eq.
Proof. unfold forall_range2, forall_i. intros. replace (i + offset) with (offset + i) by lia. auto. Qed.

Lemma eq_forall_range2_minus_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth (i - offset) l2) ->
  forall_range2 lo hi (-offset) l1 l2 eq.
Proof. unfold forall_range2, forall_i. intros. replace (i + - offset) with (i - offset) by lia. auto. Qed.

Lemma eq_forall_range2_reverse : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth (i + offset) l1 = Znth i l2) ->
  forall_range2 (lo + offset) (hi + offset) (-offset) l1 l2 eq.
Proof. unfold forall_range2, forall_i. intros. fapply (H (i - offset) ltac:(lia)). eq_solve. Qed.

Lemma eq_forall_range2_reverse_left_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth (offset + i) l1 = Znth i l2) ->
  forall_range2 (lo + offset) (hi + offset) (-offset) l1 l2 eq.
Proof. unfold forall_range2, forall_i. intros. fapply (H (i - offset) ltac:(lia)). eq_solve. Qed.

Lemma eq_forall_range2_reverse_minus_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth (i - offset) l1 = Znth i l2) ->
  forall_range2 (lo - offset) (hi - offset) offset l1 l2 eq.
Proof. unfold forall_range2, forall_i. intros. fapply (H (i + offset) ltac:(lia)). eq_solve. Qed.

Lemma In_Znth_iff : forall {A : Type} {d : Inhabitant A} (l : list A) (x : A),
  In x l <-> exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  intros. split; intro.
  - induction l; inversion H.
    + exists 0. autorewrite with sublist. split; auto. pose proof (Zlength_nonneg l); lia.
    + specialize (IHl H0). destruct IHl as [i []].
      exists (i + 1). autorewrite with sublist. rewrite Znth_pos_cons by lia.
      rewrite Z.add_simpl_r. split; auto. lia. 
  - destruct H as [i []]. subst x. apply Znth_In. auto.
Qed.

Lemma list_eq_forall_range2 : forall {A} {d : Inhabitant A} al bl,
  al = bl ->
  Zlength al = Zlength bl /\ forall_range2 0 (Zlength al) 0 al bl eq.
Proof.
  intros. subst; unfold forall_range2, forall_i; intuition.
Qed.

Lemma forall_range_fold : forall {A} {d : Inhabitant A} lo hi al (P : A -> Prop),
  (forall i, lo <= i < hi -> P (Znth i al)) = forall_range lo hi al P.
Proof. auto. Qed.

Lemma forall_range2_fold : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B},
  forall lo hi offset al bl (P : A -> B -> Prop),
  (forall i, lo <= i < hi -> P (Znth i al) (Znth (i + offset) bl)) = forall_range2 lo hi offset al bl P.
Proof. auto. Qed.

Lemma forall_triangle_fold : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B},
  forall x1 x2 y1 y2 offset al bl (P : A -> B -> Prop),
  (forall i j, x1 <= i < x2 /\ y1 <= j < y2 /\ i <= j + offset -> P (Znth i al) (Znth j bl)) = forall_triangle x1 x2 y1 y2 offset al bl P.
Proof. auto. Qed.

Lemma Forall_Znth : forall {A} {d : Inhabitant A} l P,
  Forall P l <-> forall i, 0 <= i < Zlength l -> P (Znth i l).
Proof.
  intros *.
  split; induction l; intros.
  + rewrite Zlength_nil in *; lia.
  + inversion H. intros. destruct (Z.eq_dec 0 i).
    - subst; rewrite Znth_0_cons; auto.
    - rewrite Znth_pos_cons by Zlength_solve.
      apply IHl; auto.
      list_form.
      Zlength_simplify_in_all; lia.
  + auto.
  + constructor; only 2 : apply IHl; intros.
    - fapply (H 0 ltac:(Zlength_solve)). Znth_solve.
    - fapply (H (i+1) ltac:(Zlength_solve)). list_form; Znth_solve.
Qed.

Lemma Forall_forall_range : forall {A} {d : Inhabitant A} l P,
  Forall P l <-> forall_range 0 (Zlength l) l P.
Proof.
  intros. rewrite Forall_Znth. reflexivity.
Qed.

Require Import Coq.Sorting.Sorted.

Section Sorted.
Variable A : Type.
Variable d : Inhabitant A.
Variable le : A -> A -> Prop.
Context {Hrefl : Relations_1.Reflexive A le}.
Context {Htrans : Relations_1.Transitive le}.

Definition sorted (l : list A) :=
  forall i j, 0 <= i <= j /\ j < Zlength l -> le (Znth i l) (Znth j l).

Lemma sorted_forall_triangle : forall l,
  sorted l -> forall_triangle 0 (Zlength l) 0 (Zlength l) 0 l l le.
Proof.
  unfold forall_triangle, sorted. intros.
  apply H; lia.
Qed.

Lemma Sorted_Znth : forall l,
  Sorted le l <-> forall i j, 0 <= i <= j /\ j < Zlength l -> le (Znth i l) (Znth j l).
Proof.
  split.
  1 : intros H; apply Sorted_StronglySorted in H; auto; revert H.
  all : induction l; intros.
  - Zlength_simplify_in_all. lia.
  - inv H. destruct (Z.eq_dec i 0); list_form; Znth_solve.
    + rewrite Forall_Znth in H4. apply H4; Zlength_solve.
    + apply IHl; auto. Zlength_solve.
  - auto.
  - constructor.
    + apply IHl. intros.
      fapply (H (i+1) (j+1) ltac:(Zlength_solve)). list_form; Znth_solve.
    + destruct l; constructor.
      fapply (H 0 1 ltac:(Zlength_solve)). list_form; Znth_solve.
Qed.

End Sorted.

Arguments sorted {_ _}.
(**************** range tactics **************************)

Module range_rewrite.

Lemma forall_range_empty : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : A -> Prop),
  lo = hi ->
  forall_range lo hi l P ->
  True.
Proof.
  intros.
  eapply forall_range_empty; eauto.
Qed.

Lemma forall_range_Zrepeat : forall {A : Type} {d : Inhabitant A} (lo hi n : Z) (x : A) (P : A -> Prop),
  0 <= lo < hi /\ hi <= n ->
  forall_range lo hi (Zrepeat x n) P ->
  P x.
Proof.
  intros.
  eapply forall_range_Zrepeat; eauto.
Qed.

Lemma forall_range_app1 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  forall_range lo hi (al ++ bl) P ->
  forall_range lo hi al P.
Proof.
  intros.
  eapply forall_range_app1; eauto.
Qed.

Lemma forall_range_app2 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  forall_range lo hi (al ++ bl) P ->
  forall_range (lo - Zlength al) (hi - Zlength al) bl P.
Proof.
  intros.
  eapply forall_range_app2; eauto.
Qed.

Lemma forall_range_app : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  forall_range lo hi (al ++ bl) P ->
  forall_range lo (Zlength al) al P /\
  forall_range 0 (hi - Zlength al) bl P.
Proof.
  intros.
  eapply forall_range_app; eauto.
Qed.

Lemma forall_range_upd_Znth : forall {A : Type} {d : Inhabitant A} (lo hi i : Z) (al : list A) (x : A) (P : A -> Prop),
  0 <= i < Zlength al ->
  forall_range lo hi (upd_Znth i al x) P ->
  forall_range lo hi (sublist 0 i al ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength al) al) P.
Proof.
  intros.
  eapply forall_range_upd_Znth; eauto.
Qed.

Lemma forall_range_sublist : forall {A : Type} {d : Inhabitant A} (lo hi lo' hi' : Z) (l : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  forall_range lo hi (sublist lo' hi' l) P ->
  forall_range (lo+lo') (hi+lo') l P.
Proof.
  intros.
  eapply forall_range_sublist; eauto.
Qed.

Lemma forall_range_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi : Z) (l : list A) (f : A -> B) (P : B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  forall_range lo hi (map f l) P ->
  forall_range lo hi l (fun x => P (f x)).
Proof.
  intros.
  eapply forall_range_map; eauto.
Qed.

Lemma forall_range2_empty : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  lo = hi ->
  forall_range2 lo hi offset l l' P ->
  True.
Proof.
  intros.
  eapply (forall_range2_empty _ _ _ _ _ P); eauto.
Qed.

Lemma forall_range2A_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  forall_range2 lo hi offset (al ++ bl) l' P ->
  forall_range2 lo hi offset al l' P.
Proof.
  intros.
  eapply forall_range2A_app1; eauto.
Qed.

Lemma forall_range2A_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  forall_range2 lo hi offset (al ++ bl) l' P ->
  forall_range2 (lo - Zlength al) (hi - Zlength al) (offset + Zlength al) bl l' P.
Proof.
  intros.
  eapply forall_range2A_app2; eauto.
Qed.

Lemma forall_range2A_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  forall_range2 lo hi offset (al ++ bl) l' P ->
  forall_range2 lo (Zlength al) offset al l' P /\
  forall_range2 0 (hi - Zlength al) (offset + Zlength al) bl l' P.
Proof.
  intros.
  eapply forall_range2A_app; eauto.
Qed.

Lemma forall_range2A_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset i : Z) (l : list A) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= i < Zlength l ->
  forall_range2 lo hi offset (upd_Znth i l x)  l' P ->
  forall_range2 lo hi offset (sublist 0 i l ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l) l) l' P.
Proof.
  intros.
  eapply forall_range2A_upd_Znth; eauto.
Qed.

Lemma forall_range2A_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi lo' hi' offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  forall_range2 lo hi offset (sublist lo' hi' l) l' P ->
  forall_range2 (lo+lo') (hi+lo') (offset-lo') l l' P.
Proof.
  intros.
  eapply forall_range2A_sublist; eauto.
Qed.

Lemma forall_range2A_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (lo hi offset : Z) (l : list A) (l' : list B) (f : A -> C) (P : C -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  forall_range2 lo hi offset (map f l) l' P ->
  forall_range2 lo hi offset l l' (fun x => P (f x)).
Proof.
  intros.
  eapply forall_range2A_map; eauto.
Qed.

Lemma forall_range2A_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi n offset : Z) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo < hi /\ hi <= n ->
  forall_range2 lo hi offset (Zrepeat x n) l' P ->
  forall_range (lo + offset) (hi + offset) l' (P x).
Proof.
  intros.
  eapply forall_range2A_Zrepeat; eauto.
Qed.

Lemma forall_range2B_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= Zlength al' ->
  forall_range2 lo hi offset l (al' ++ bl') P ->
  forall_range2 lo hi offset l al' P.
Proof.
  intros.
  eapply forall_range2B_app1; eauto.
Qed.

Lemma forall_range2B_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  Zlength al' <= lo + offset <= hi + offset /\ hi + offset <= Zlength al' + Zlength bl' ->
  forall_range2 lo hi offset l (al' ++ bl') P ->
  forall_range2 lo hi (offset - Zlength al') l bl' P.
Proof.
  intros.
  eapply forall_range2B_app2; eauto.
Qed.

Lemma forall_range2B_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= Zlength al' /\ Zlength al' <= hi + offset <= Zlength al' + Zlength bl' ->
  forall_range2 lo hi offset l (al' ++ bl') P ->
  forall_range2 lo (Zlength al' - offset) offset l al' P /\
  forall_range2 (Zlength al' - offset) hi (offset - Zlength al') l bl' P.
Proof.
  intros.
  eapply forall_range2B_app; eauto.
Qed.

Lemma forall_range2B_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset i : Z) (l : list A) (l' : list B) (x : B) (P : A -> B -> Prop),
  0 <= i < Zlength l' ->
  forall_range2 lo hi offset l (upd_Znth i l' x)  P <->
  forall_range2 lo hi offset l (sublist 0 i l' ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l') l') P.
Proof.
  intros.
  eapply forall_range2B_upd_Znth; eauto.
Qed.

Lemma forall_range2B_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi lo' hi' offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l' ->
  forall_range2 lo hi offset l (sublist lo' hi' l') P ->
  forall_range2 lo hi (offset + lo') l l' P.
Proof.
  intros.
  eapply forall_range2B_sublist; eauto.
Qed.

Lemma forall_range2B_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (lo hi offset : Z) (l : list A) (l' : list B) (f : B -> C) (P : A -> C -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= Zlength l' ->
  forall_range2 lo hi offset l (map f l') P ->
  forall_range2 lo hi offset l l' (fun x y => P x (f y)).
Proof.
  intros.
  eapply forall_range2B_map; eauto.
Qed.

Lemma forall_range2B_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi n offset : Z) (l : list A) (x : B) (P : A -> B -> Prop),
  0 <= lo + offset < hi + offset /\ hi + offset <= n ->
  forall_range2 lo hi offset l (Zrepeat x n) P ->
  forall_range lo hi l (fun y => P y x).
Proof.
  intros.
  eapply forall_range2B_Zrepeat; eauto.
Qed.

Lemma forall_triangle_emptyA : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  x1 = x2 ->
  forall_triangle x1 x2 y1 y2 offset l l' P ->
  True.
Proof.
  intros.
  eapply (forall_triangle_emptyA _ _ _ _ _ _ _ P); eauto.
Qed.

Lemma forall_triangle_emptyB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  y1 = y2 ->
  forall_triangle x1 x2 y1 y2 offset l l' P ->
  True.
Proof.
  intros.
  eapply (forall_triangle_emptyB _ _ _ _ _ _ _ P); eauto.
Qed.

Lemma forall_triangle_emptyAgtB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  x1 >= y2 + offset ->
  forall_triangle x1 x2 y1 y2 offset l l' P ->
  True.
Proof.
  intros.
  eapply (forall_triangle_emptyAgtB _ _ _ _ _ _ _ P); eauto.
Qed.

Lemma forall_triangleA_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 <= x2 /\ x2 <= Zlength al ->
  forall_triangle x1 x2 y1 y2 offset (al ++ bl) l' P ->
  forall_triangle x1 x2 y1 y2 offset al l' P.
Proof.
  intros.
  eapply forall_triangleA_app1; eauto.
Qed.

Lemma forall_triangleA_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset: Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  Zlength al <= x1 <= x2 /\ x2 <= Zlength al + Zlength bl ->
  forall_triangle x1 x2 y1 y2 offset (al ++ bl) l' P ->
  forall_triangle (x1 - Zlength al) (x2 - Zlength al) y1 y2 (offset - Zlength al) bl l' P.
Proof.
  intros.
  eapply forall_triangleA_app2; eauto.
Qed.

Lemma forall_triangleA_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 <= Zlength al /\ Zlength al <= x2 <= Zlength al + Zlength bl ->
  forall_triangle x1 x2 y1 y2 offset (al ++ bl) l' P ->
  forall_triangle x1 (Zlength al) y1 y2 offset al l' P /\
  forall_triangle 0 (x2 - Zlength al) y1 y2 (offset - Zlength al) bl l' P.
Proof.
  intros.
  eapply forall_triangleA_app; eauto.
Qed.

Lemma forall_triangleA_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset i : Z) (l : list A) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= i < Zlength l ->
  forall_triangle x1 x2 y1 y2 offset (upd_Znth i l x) l' P <->
  forall_triangle x1 x2 y1 y2 offset (sublist 0 i l ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l) l) l' P.
Proof.
  intros.
  eapply forall_triangleA_upd_Znth; eauto.
Qed.

Lemma forall_triangleA_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi x1 x2 y1 y2 offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 <= x2 /\ x2 <= hi - lo /\ 0 <= lo <= hi /\ hi <= Zlength l ->
  forall_triangle x1 x2 y1 y2 offset (sublist lo hi l) l' P ->
  forall_triangle (x1 + lo) (x2 + lo) y1 y2 (offset + lo) l l' P.
Proof.
  intros.
  eapply forall_triangleA_sublist; eauto.
Qed.

Lemma forall_triangleA_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (x1 x2 y1 y2 offset : Z) (l : list A) (l' : list B) (f : A -> C) (P : C -> B -> Prop),
  0 <= x1 <= x2 /\ x2 <= Zlength l ->
  forall_triangle x1 x2 y1 y2 offset (map f l) l' P ->
  forall_triangle x1 x2 y1 y2 offset l l' (fun x => P (f x)).
Proof.
  intros.
  eapply forall_triangleA_map; eauto.
Qed.

Lemma forall_triangleA_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (n x1 x2 y1 y2 offset : Z) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= x1 < x2 /\ x2 <= n ->
  forall_triangle x1 x2 y1 y2 offset (Zrepeat x n) l' P <->
  forall_range (Z.max y1 (x1 - offset)) (Z.max y2 (x1 - offset)) l' (P x).
Proof.
  intros.
  eapply forall_triangleA_Zrepeat; eauto.
Qed.

Lemma forall_triangleB_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= y1 <= y2 /\ y2 <= Zlength al' ->
  forall_triangle x1 x2 y1 y2 offset l (al' ++ bl') P <->
  forall_triangle x1 x2 y1 y2 offset l al' P.
Proof.
  intros.
  eapply forall_triangleB_app1; eauto.
Qed.

Lemma forall_triangleB_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  Zlength al' <= y1 <= y2 /\ y2 <= Zlength al' + Zlength bl' ->
  forall_triangle x1 x2 y1 y2 offset l (al' ++ bl') P ->
  forall_triangle x1 x2 (y1 - Zlength al') (y2 - Zlength al') (offset + Zlength al') l bl' P.
Proof.
  intros.
  eapply forall_triangleB_app2; eauto.
Qed.

Lemma forall_triangleB_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= y1 <= Zlength al' /\ Zlength al' <= y2 <= Zlength al' + Zlength bl' ->
  forall_triangle x1 x2 y1 y2 offset l (al' ++ bl') P ->
  forall_triangle x1 x2 y1 (Zlength al') offset l al' P /\
  forall_triangle x1 x2 0 (y2 - Zlength al') (offset + Zlength al') l bl' P.
Proof.
  intros.
  eapply forall_triangleB_app; eauto.
Qed.

Lemma forall_triangleB_upd_Znth : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 offset i : Z) (l : list A) (l' : list B) (x : B) (P : A -> B -> Prop),
  0 <= i < Zlength l' ->
  forall_triangle x1 x2 y1 y2 offset l (upd_Znth i l' x)  P <->
  forall_triangle x1 x2 y1 y2 offset l (sublist 0 i l' ++ (Zrepeat x 1) ++ sublist (i+1) (Zlength l') l') P.
Proof.
  intros.
  eapply forall_triangleB_upd_Znth; eauto.
Qed.

Lemma forall_triangleB_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 lo hi offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= y1 <= y2 /\ y2 <= hi - lo /\ 0 <= lo <= hi /\ hi <= Zlength l' ->
  forall_triangle x1 x2 y1 y2 offset l (sublist lo hi l') P ->
  forall_triangle x1 x2 (y1 + lo) (y2 + lo) (offset - lo) l l' P.
Proof.
  intros.
  eapply forall_triangleB_sublist; eauto.
Qed.

Lemma forall_triangleB_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (x1 x2 y1 y2 offset : Z) (l : list A) (l' : list B) (f : B -> C) (P : A -> C -> Prop),
  0 <= y1 <= y2 /\ y2 <= Zlength l' ->
  forall_triangle x1 x2 y1 y2 offset l (map f l') P ->
  forall_triangle x1 x2 y1 y2 offset l l' (fun x y => P x (f y)).
Proof.
  intros.
  eapply forall_triangleB_map; eauto.
Qed.

Lemma forall_triangleB_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (x1 x2 y1 y2 n offset : Z) (l : list A) (x : B) (P : A -> B -> Prop),
  0 <= y1 < y2 /\ y2 <= n ->
  forall_triangle x1 x2 y1 y2 offset l (Zrepeat x n) P <->
  forall_range (Z.min x1 (y2 + offset)) (Z.min x2 (y2 + offset)) l (fun y => P y x).
Proof.
  intros.
  eapply forall_triangleB_Zrepeat; eauto.
Qed.

Ltac destruct_range H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    destruct_range H1;
    destruct_range H2
  | forall_range ?lo ?hi _ _ =>
    (* try (
      apply forall_range_empty in H;
      [ clear H | Zlength_solve ]
    ) *)
    idtac
  | forall_range2 ?lo ?hi _ _ _ _ =>
    (* try (
      apply forall_range2_empty in H;
      [ clear H | Zlength_solve ]
    ) *)
    idtac
  | forall_triangle ?lo ?hi _ _ _ _ _ _ =>
    try (
      apply forall_triangle_emptyAgtB in H;
      [ clear H | Zlength_solve ]
    )
  end.


Ltac rewrite_In_Znth_iff :=
  repeat lazymatch goal with
  | H : In ?x ?l |- _ =>
    rewrite In_Znth_iff in H;
    destruct H as [? []]
  end.

Ltac rewrite_list_eq :=
  repeat lazymatch goal with
  | H : @eq (list ?A) ?al ?bl |- _ =>
    apply list_eq_forall_range2 in H;
    destruct H
  end.

Hint Rewrite @Forall_forall_range : list_prop_rewrite.
Hint Rewrite @forall_range_fold : list_prop_rewrite.
Hint Rewrite @forall_range2_fold : list_prop_rewrite.
Hint Rewrite @forall_triangle_fold : list_prop_rewrite.
Hint Rewrite Sorted_Znth : list_prop_rewrite.

Ltac range_form :=
  rewrite_list_eq;
  apply_in_hyps not_In_forall_range;
  apply_in_hyps eq_forall_range2_no_offset;
  apply_in_hyps eq_forall_range2_offset;
  apply_in_hyps eq_forall_range2_left_offset;
  apply_in_hyps eq_forall_range2_minus_offset;
  apply_in_hyps eq_forall_range2_reverse;
  apply_in_hyps eq_forall_range2_reverse_left_offset;
  apply_in_hyps eq_forall_range2_reverse_minus_offset;
  apply_in_hyps sorted_forall_triangle;
  (* repeat (unshelve erewrite @Forall_Znth in *; [solve [auto with typeclass_instances] .. | idtac]); *)
  rewrite_In_Znth_iff;
  (* autorewrite with list_prop_rewrite in *. *)
  unshelve autorewrite with list_prop_rewrite in *; [solve [auto with typeclass_instances] .. | idtac].

Ltac Zlength_solve_print_when_fail :=
  first [
    Zlength_solve
  | lazymatch goal with
    | |- ?Goal =>
      fail 1 "Cannot prove" Goal
    end
  ].

Ltac apply_in_using_Zlength_solve lem H :=
  apply lem in H; [
    destruct_range H
  | Zlength_solve_print_when_fail
    ..
  ].

Ltac range_rewrite :=
  repeat match goal with
  | H : forall_range _ _ ?l _ |- _ =>
    lazymatch l with
    | app ?l1 ?l2 =>
      first [
        apply_in_using_Zlength_solve forall_range_app1 H
      | apply_in_using_Zlength_solve forall_range_app2 H
      | apply_in_using_Zlength_solve forall_range_app H
      ]
    | Zrepeat ?x ?n =>
      apply_in_using_Zlength_solve forall_range_Zrepeat H
    | upd_Znth _ _ _ =>
      apply_in_using_Zlength_solve forall_range_upd_Znth H
    | sublist _ _ _ =>
      apply_in_using_Zlength_solve forall_range_sublist H
    | map _ _ =>
      apply_in_using_Zlength_solve uconstr:(forall_range_map) H
    end
  | H : forall_range2 _ _ _ ?l1 ?l2 _ |- _ =>
    first [
      lazymatch l1 with
      | app _ _ =>
        first [
          apply_in_using_Zlength_solve forall_range2A_app1 H
        | apply_in_using_Zlength_solve forall_range2A_app2 H
        | apply_in_using_Zlength_solve forall_range2A_app H
        ]
      | Zrepeat ?x ?n =>
        apply_in_using_Zlength_solve forall_range2A_Zrepeat H
      | upd_Znth _ _ _ =>
        apply_in_using_Zlength_solve forall_range2A_upd_Znth H
      | sublist _ _ _ =>
        apply_in_using_Zlength_solve forall_range2A_sublist H
      | map _ _ =>
        apply_in_using_Zlength_solve uconstr:(forall_range2A_map) H
      end
    | lazymatch l2 with
      | app _ _ =>
        first [
          apply_in_using_Zlength_solve forall_range2B_app1 H
        | apply_in_using_Zlength_solve forall_range2B_app2 H
        | apply_in_using_Zlength_solve forall_range2B_app H
        ]
      | Zrepeat ?x ?n =>
        apply_in_using_Zlength_solve forall_range2B_Zrepeat H
      | upd_Znth _ _ _ =>
        apply_in_using_Zlength_solve forall_range2B_upd_Znth H
      | sublist _ _ _ =>
        apply_in_using_Zlength_solve forall_range2B_sublist H
      | map _ _ =>
        apply_in_using_Zlength_solve uconstr:(forall_range2B_map) H
      end
    ]
  | H : forall_triangle _ _ _ _ _ ?l1 ?l2 _ |- _ =>
    first [
      lazymatch l1 with
      | app _ _ =>
        first [
          apply_in_using_Zlength_solve forall_triangleA_app1 H
        | apply_in_using_Zlength_solve forall_triangleA_app2 H
        | apply_in_using_Zlength_solve forall_triangleA_app H
        ]
      | Zrepeat ?x ?n =>
        apply_in_using_Zlength_solve forall_triangleA_Zrepeat H
      | upd_Znth _ _ _ =>
        apply_in_using_Zlength_solve forall_triangleA_upd_Znth H
      | sublist _ _ _ =>
        apply_in_using_Zlength_solve forall_triangleA_sublist H
      | map _ _ =>
        apply_in_using_Zlength_solve uconstr:(forall_triangleA_map) H
      end
    | lazymatch l2 with
      | app _ _ =>
        first [
          apply_in_using_Zlength_solve forall_triangleB_app1 H
        | apply_in_using_Zlength_solve forall_triangleB_app2 H
        | apply_in_using_Zlength_solve forall_triangleB_app H
        ]
      | Zrepeat ?x ?n =>
        apply_in_using_Zlength_solve forall_triangleB_Zrepeat H
      | upd_Znth _ _ _ =>
        apply_in_using_Zlength_solve forall_triangleB_upd_Znth H
      | sublist _ _ _ =>
        apply_in_using_Zlength_solve forall_triangleB_sublist H
      | map _ _ =>
        apply_in_using_Zlength_solve uconstr:(forall_triangleB_map) H
      end
    ]
  end.

Ltac range_rewrite_check :=
  try match goal with
  | H : forall_range _ _ ?l _ |- _ =>
    lazymatch l with
    | sublist _ _ _ =>
      idtac "Warning:" l "is not simplified in" H
    | app _ _ =>
      idtac "Warning:" l "is not simplified in" H
    | map _ _ =>
      idtac "Warning:" l "is not simplified in" H
    end
  | H : forall_range2 _ _ ?l1 ?l2 _ |- _ =>
    first [
      lazymatch l1 with
      | sublist _ _ _ =>
        idtac "Warning:" l1 "is not simplified in" H
      | app _ _ =>
        idtac "Warning:" l1 "is not simplified in" H
      | map _ _ =>
        idtac "Warning:" l1 "is not simplified in" H
      end
    | lazymatch l2 with
      | sublist _ _ _ =>
        idtac "Warning:" l2 "is not simplified in" H
      | app _ _ =>
        idtac "Warning:" l2 "is not simplified in" H
      | map _ _ =>
        idtac "Warning:" l2 "is not simplified in" H
      end
    ]
  | H : forall_triangle _ _ _ _ _ ?l1 ?l2 _ |- _ =>
    first [
      lazymatch l1 with
      | sublist _ _ _ =>
        idtac "Warning:" l1 "is not simplified in" H
      | app _ _ =>
        idtac "Warning:" l1 "is not simplified in" H
      | map _ _ =>
        idtac "Warning:" l1 "is not simplified in" H
      end
    | lazymatch l2 with
      | sublist _ _ _ =>
        idtac "Warning:" l2 "is not simplified in" H
      | app _ _ =>
        idtac "Warning:" l2 "is not simplified in" H
      | map _ _ =>
        idtac "Warning:" l2 "is not simplified in" H
      end
    ]
  end.
End range_rewrite.

Ltac range_form := range_rewrite.range_form.
Ltac range_rewrite := range_rewrite.range_rewrite.
Ltac range_rewrite_check := range_rewrite.range_rewrite_check.

Lemma range_le_lt_dec : forall lo i hi,
  {lo <= i < hi} + {~lo <= i < hi}.
Proof.
  intros.
  destruct (Z_lt_ge_dec i lo); destruct (Z_lt_ge_dec i hi); left + right; lia.
Qed.

Ltac destruct_range i lo hi :=
  destruct (range_le_lt_dec lo i hi).

Lemma Z_le_lt_dec : forall x y,
  {x <= y} + {y < x}.
Proof.
  intros. destruct (Z_lt_ge_dec y x); [right|left]; auto. lia.
Qed.

Ltac pose_new_res i lo hi H res :=
  assert_fails (assert res by assumption);
  destruct_range i lo hi;
  [ (tryif exfalso; lia then gfail else idtac);
    assert res by apply (H i ltac:(lia))
  | try lia
  ].

Ltac pose_new_res_tri i j x1 x2 y1 y2 offset H res :=
  assert_fails (assert res by assumption);
  destruct_range i x1 x2;
  destruct_range j y1 y2;
  destruct (Z_le_lt_dec i (j + offset));
  [ (tryif exfalso; lia then gfail else idtac);
    assert res by apply (H i j ltac:(lia))
  | try lia ..
  ].

Ltac instantiate_bound_set := false.

Module range_saturate.

Definition Znth' := @Znth.
Arguments Znth' {_ _}.

Definition forall_range' := @forall_range.
Arguments forall_range' {_ _}.

Definition forall_range2' := @forall_range2.
Arguments forall_range2' {_ _}.

Definition forall_triangle' := @forall_triangle.
Arguments forall_triangle' {_ _}.

Definition range_saturate_shift {A : Type} (l : list A) (s : Z) :=
  True.
Definition range_saturate_shift' := @range_saturate_shift.
Arguments range_saturate_shift' {_}.

Module check_non_zero_loop.

Lemma pose_range_saturate_shift : forall {A : Type} (l : list A) (s : Z),
  range_saturate_shift l s.
Proof. intros. apply I. Qed.

Hint Rewrite Z.add_0_r : Z_normalize_0.
Hint Rewrite Z.add_0_l : Z_normalize_0.
Hint Rewrite Z.sub_0_r : Z_normalize_0.

Ltac pose_range_saturate_shift l s :=
  let H := fresh in
  pose proof (pose_range_saturate_shift l s) as H;
  autorewrite with Z_normalize_0 in H.

Ltac loop2 :=
  let flag := instantiate_bound_set in
  repeat lazymatch goal with
  | H : range_saturate_shift ?l1 ?s1,
    H1 : forall_range2 ?lo ?hi ?s ?l1 ?l2 ?P |- _ =>
    lazymatch goal with
    | H2 : range_saturate_shift l2 ?s2 |- _ =>
      tryif assert (s1 + s = s2) by Zlength_solve
      then idtac
      else fail 1
    | |- _ =>
      pose_range_saturate_shift l2 (s1 + s)
    end;
    change @forall_range2 with @forall_range2' in H1
  | H : range_saturate_shift ?l2 ?s2,
    H1 : forall_range2 ?lo ?hi ?s ?l1 ?l2 ?P |- _ =>
    pose_range_saturate_shift l1 (s2 - s);
    change @forall_range2 with @forall_range2' in H1
  | H : range_saturate_shift ?l1 ?s1,
    H1 : forall_triangle _ _ _ _ ?s ?l1 ?l2 ?P |- _ =>
    lazymatch flag with
    | true =>
      lazymatch goal with
      | H2 : range_saturate_shift l2 ?s2 |- _ =>
        tryif assert (s1 + s = s2) by Zlength_solve
        then idtac
        else fail 1
      | |- _ =>
        pose_range_saturate_shift l2 (s1 + s)
      end;
      change @forall_triangle with @forall_triangle' in H1
    end
  | H : range_saturate_shift ?l2 ?s2,
    H1 : forall_triangle _ _ _ _ ?s ?l1 ?l2 ?P |- _ =>
    lazymatch flag with
    | true =>
      pose_range_saturate_shift l1 (s2 - s);
      change @forall_triangle with @forall_triangle' in H1
    end
  end.

Ltac loop1 :=
  let flag := instantiate_bound_set in
  repeat lazymatch goal with
  | H : forall_range2 ?lo ?hi ?s ?l1 ?l2 ?P |- _ =>
    pose_range_saturate_shift l1 0;
    tryif loop2
    then idtac
    else fail 1
  | H : forall_triangle _ _ _ _ _ ?l1 ?l2 ?P |- _ =>
    lazymatch flag with
    | true =>
      pose_range_saturate_shift l1 0;
      tryif loop2
      then idtac
      else fail 1
    end
  end;
  change @forall_range2' with @forall_range2 in *;
  change @forall_triangle' with @forall_triangle in *.

Ltac check_non_zero_loop_old :=
  tryif (try (loop1; fail 1))
  then fail "The goal has non-zero loop"
  else idtac.

Ltac check_non_zero_loop :=
  tryif loop1
  then idtac
  else fail "List solver cannot solve this goal because it is entangled, which means it has assumptions like (sublist 0 (n-1) al = sublist 1 n al)".

Ltac clear0 :=
  repeat lazymatch goal with
  | H : range_saturate_shift _ _ |- _ =>
    clear H
  end.

End check_non_zero_loop.

Ltac check_non_zero_loop := check_non_zero_loop.check_non_zero_loop.

Definition instantiate_index {A} (x : A) := True.
Definition instantiate_index' := @instantiate_index.
Arguments instantiate_index' {_}.

Module find_instantiate_index.

Lemma pose_instantiate_index {A} (x : A) : instantiate_index x.
Proof. apply I. Qed.

Ltac pose_instantiate_index x :=
  let H := fresh in
  pose proof (pose_instantiate_index x) as H;
  autorewrite with Z_normalize_0 in H;
  lazymatch type of H with
  | instantiate_index (Znth' ?i ?l) =>
    try lazymatch goal with
    | H1 : instantiate_index (Znth' i l),
      H2 : instantiate_index (Znth' i l) |- _ =>
      clear H
    end
  end.

Ltac add_index i l :=
  (* try (
    (* success if not exist, fail 0 if exist *)
    try match goal with
    | H : instantiate_index (Znth' ?j l) |- _=>
      assert (i = j) by Zlength_solve;
      fail 2
    end;
    pose proof (pose_instantiate_index (Znth' i l))
  ). *)
  lazymatch goal with
  | H : instantiate_index (Znth' i l) |- _ =>
    idtac
  | _ =>
    pose_instantiate_index (Znth' i l)
  end.

Ltac process i l :=
  lazymatch goal with
  | H : range_saturate_shift l ?s |- _ =>
    add_index i l;
    change @range_saturate_shift with @range_saturate_shift' in H;
    repeat lazymatch goal with
    | H1 : range_saturate_shift ?l1 ?s1 |- _ =>
      add_index (i - s + s1) l1;
      change @range_saturate_shift with @range_saturate_shift' in H1
    end;
    change @range_saturate_shift' with @range_saturate_shift in *
  | _ =>
    add_index i l
  end.

Ltac index_set :=
  repeat lazymatch goal with
  | _ : context [Znth ?i ?l] |- _ =>
    process i l;
    change (Znth i l) with (Znth' i l) in *
  | |- context [Znth ?i ?l] =>
    process i l;
    change (Znth i l) with (Znth' i l) in *
  end;
  change @Znth' with @Znth in *.

Ltac bound_set :=
  repeat lazymatch goal with
  | H : forall_range ?lo ?hi ?l _ |- _ =>
    process lo l;
    process (hi - 1) l;
    change @forall_range with @forall_range' in H
  end;
  change @forall_range' with @forall_range in *;
  repeat lazymatch goal with
  | H : forall_range2 ?lo ?hi _ ?l1 ?l2 _ |- _ =>
    process lo l1;
    process (hi - 1) l1;
    change @forall_range2' with @forall_range2' in H
  end;
  change @forall_range2' with @forall_range2 in *;
  repeat lazymatch goal with
  | H : forall_triangle ?x1 ?x2 ?y1 ?y2 _ ?l1 ?l2 _ |- _ =>
    process x1 l1;
    process (x2 - 1) l1;
    process y1 l2;
    process (y2 - 1) l2;
    change @forall_triangle with @forall_triangle' in H
  end;
  change @forall_triangle' with @forall_triangle in *;
  change @Znth' with @Znth in *.

Ltac find_instantiate_index :=
  index_set;
  let flag := instantiate_bound_set in
  lazymatch flag with
  | true =>
    bound_set
  | false =>
    idtac
  end.

Ltac clear0 :=
  repeat lazymatch goal with
  | H : instantiate_index _ |- _ =>
    clear H
  end.

End find_instantiate_index.

Ltac find_instantiate_index := find_instantiate_index.find_instantiate_index.

Ltac pose_new_res i lo hi H res ::=
  assert_fails (assert res by assumption);
  destruct_range i lo hi;
  [ try (exfalso; lia);
    assert res by apply (H i ltac:(lia));
    try (lia)
  | try (lia)
  ].

Ltac pose_new_res_tri i j x1 x2 y1 y2 offset H res :=
  assert_fails (assert res by assumption);
  destruct_range i x1 x2;
  destruct_range j y1 y2;
  destruct (Z_le_lt_dec i (j + offset));
  [ try (exfalso; lia);
    assert res by apply (H i j ltac:(lia));
    try (lia)
  | try (lia)
    ..
  ].

Ltac range_saturate_uni H :=
  lazymatch type of H with
  | forall_range ?lo ?hi ?l ?P =>
    repeat lazymatch goal with
    | H1 : instantiate_index (Znth ?i l) |- _ =>
      let res := eval cbv beta in (P (Znth i l)) in
      pose_new_res i lo hi H res;
      change @instantiate_index with @instantiate_index' in H1
    end;
    change @instantiate_index' with @instantiate_index in *
  end.

Ltac range_saturate_bin H :=
  lazymatch type of H with
  | forall_range2 ?lo ?hi ?offset ?l1 ?l2 ?P =>
    repeat lazymatch goal with
    | H1 : instantiate_index (Znth ?i l1) |- _ =>
      let res := eval cbv beta in (P (Znth i l1) (Znth (i + offset) l2)) in
      pose_new_res i lo hi H res;
      change @instantiate_index with @instantiate_index' in H1
    end;
    change @instantiate_index' with @instantiate_index in *
  end.

Ltac range_saturate_tri H :=
  lazymatch type of H with
  | forall_triangle ?x1 ?x2 ?y1 ?y2 ?offset ?l1 ?l2 ?P =>
    repeat lazymatch goal with
    | H1 : instantiate_index (Znth ?i l1) |- _ =>
      repeat lazymatch goal with
      | H2 : instantiate_index (Znth ?j l2) |- _ =>
        let res := eval cbv beta in (P (Znth i l1) (Znth j l2)) in
        pose_new_res_tri i j x1 x2 y1 y2 offset H res;
        change @Znth with @Znth' in H2
      | H2 : instantiate_index' (Znth ?j l2) |- _ =>
        let res := eval cbv beta in (P (Znth i l1) (Znth j l2)) in
        pose_new_res_tri i j x1 x2 y1 y2 offset H res;
        change @Znth with @Znth' in H2
      end;
      change @Znth' with @Znth in *;
      change @instantiate_index with @instantiate_index' in H1
    end;
    change @instantiate_index' with @instantiate_index in *
  end.

Ltac range_saturate :=
  repeat lazymatch goal with
  | H : forall_range _ _ _ _ |- _ =>
    range_saturate_uni H;
    change @forall_range with @forall_range' in H
  | H : forall_range2 _ _ _ _ _ _ |- _ =>
    range_saturate_bin H;
    change @forall_range2 with @forall_range2' in H
  | H : forall_triangle _ _ _ _ _ _ _ _ |- _ =>
    range_saturate_tri H;
    change @forall_triangle with @forall_triangle' in H
  end;
  change @forall_range' with @forall_range in *;
  change @forall_range2' with @forall_range2 in *;
  change @forall_triangle' with @forall_triangle in *.

Goal forall A {d : Inhabitant A} (P : A -> Prop) l a0 a1 a2 a3 a4 a5,
  Zlength l = 10 ->
  a0 = Znth 0 l /\
  a1 = Znth 1 l /\
  a2 = Znth 2 l /\
  a3 = Znth 3 l /\
  a4 = Znth 4 l /\
  a5 = Znth 5 l /\
  a5 = Znth 6 l /\
  a5 = Znth 7 l ->
  forall_range 5 10 l P ->
  P a5.
Proof.
  intros.
  find_instantiate_index.
  range_saturate.
Abort.

End range_saturate.

Ltac check_non_zero_loop := range_saturate.check_non_zero_loop.
Ltac find_instantiate_index := range_saturate.find_instantiate_index.

Ltac range_saturate :=
  check_non_zero_loop;
  find_instantiate_index; range_saturate.check_non_zero_loop.clear0;
  range_saturate.range_saturate; range_saturate.find_instantiate_index.clear0.

Ltac Znth_simplify :=
  Znth_solve.

Ltac Znth_simplify_in_all :=
  Znth_solve2.

Arguments Zlength_fact {_}.

Ltac list_prop_solve' :=
  list_form; range_rewrite.range_form; range_rewrite;
  range_rewrite_check;
  Znth_solve2;
  autorewrite with Z_normalize_0 in *;
  range_saturate;
  Znth_solve2;
  auto with Znth_solve_hint;
  try fassumption.

Ltac list_prop_solve :=
  list_prop_solve';
  fail "list_prop_solve cannot solve this goal".

Create HintDb list_solve_unfold.

(* Tactic apply_list_ext applies the proper extensionality lemma and proves
  the lengths are the same and reduces the goal to relation between entries. *)
Ltac apply_list_ext :=
  first
  [ match goal with |- @eq ?list_A _ _ =>
      match eval compute in list_A with list ?A =>
        apply (@Znth_eq_ext A ltac:(auto with typeclass_instances))
      end
    end;
    only 1 : Zlength_solve
  | match goal with |- @Forall ?A ?P ?l =>
      rewrite Forall_Znth;
      intros
    end
  | match goal with |- @forall_range ?A ?d ?lo ?hi ?l ?P =>
      rewrite <- forall_range_fold;
      intros
    end
  ];
  Zlength_simplify;
  intros.

Ltac customizable_list_solve_preprocess := idtac.

Ltac list_solve_preprocess :=
  customizable_list_solve_preprocess;
  autounfold with list_solve_unfold in *;
  unshelve autorewrite with list_solve_rewrite in *; [solve [auto with typeclass_instances] .. | idtac];
  repeat match goal with [ |- _ /\ _ ] => split end;
  intros.

Ltac list_solve :=
  intros;
  try lia;
  try match goal with |- context [@Zlength] => Zlength_solve end;
  list_solve_preprocess;
  Zlength_simplify_in_all; try lia;
  Znth_simplify_in_all; auto with Znth_solve_hint;
  try fassumption;
  Zlength_simplify_in_all; try lia;
  try (
    apply_list_ext; Znth_solve;
    auto with Znth_solve_hint; try fassumption
  );
  list_prop_solve';
  fail "list_solve cannot solve this goal".

Ltac list_simplify :=
  intros;
  list_solve_preprocess;
  Zlength_simplify_in_all; try lia;
  Znth_simplify_in_all; auto with Znth_solve_hint;
  try fassumption;
  Zlength_simplify_in_all; try lia;
  try (
    apply_list_ext; Znth_solve;
    auto with Znth_solve_hint; try fassumption
  );
  list_prop_solve'.

(** * quick_list_solve and simplify *)
Ltac quick_list_simplify :=
  try lia;
  try match goal with |- context [@Zlength] => Zlength_solve end;
  list_solve_preprocess;
  Zlength_simplify_in_all; try lia;
  Znth_simplify_in_all; auto with Znth_solve_hint;
  try fassumption;
  Zlength_simplify_in_all; try lia;
  try (
    apply_list_ext; Znth_solve;
    auto with Znth_solve_hint; try fassumption
  ).

Ltac quick_list_solve :=
  quick_list_simplify;
  fail "quick_list_solve cannot solve this goal".
