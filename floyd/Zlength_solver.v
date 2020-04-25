(* Definitions and lemmas used in list solver *)
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import VST.floyd.sublist.
Import ListNotations.

(** This file provides a almost-complete solver for list with concatenation.
  Its core symbols include:
    Zlength
    Znth
    Zrepeat
    app
    sublist
    map.
  And it also interprets these symbols by convernting to core symbols:
    list_repeat (Z.to_nat _)
    nil
    cons
    upd_Znth. *)

(** * Zlength_solve *)
(** Zlength_solve is a tactic that solves linear arithmetic about length of lists. *)

(* Auxilary lemmas for Zlength_solve. *)
Lemma repeat_list_repeat : forall {A : Type} (n : nat) (x : A),
  repeat x n = list_repeat n x.
Proof. intros. induction n; simpl; try f_equal; auto. Qed.

Definition Zrepeat {A : Type} (x : A) (n : Z) : list A :=
  repeat x (Z.to_nat n).

Lemma Zlength_Zrepeat : forall (A : Type) (x : A) (n : Z),
  0 <= n ->
  Zlength (Zrepeat x n) = n.
Proof. intros *. unfold Zrepeat. rewrite repeat_list_repeat. apply @Zlength_list_repeat. Qed.

Local Lemma Zlength_firstn : forall (A : Type) n (l : list A),
  Zlength (firstn n l) = Z.min (Z.max (Z.of_nat n) 0) (Zlength l).
Proof.
  induction n; intros.
  - simpl. rewrite Zlength_nil.
    pose proof (Zlength_nonneg l). lia.
  - destruct l; simpl.
    + rewrite Zlength_nil. lia.
    + rewrite !Zlength_cons.
      rewrite IHn.
      pose proof (Zlength_nonneg l). lia.
Qed.

Local Lemma Zlength_firstn_to_nat : forall (A : Type) n (l : list A),
  Zlength (firstn (Z.to_nat n) l) = Z.min (Z.max n 0) (Zlength l).
Proof.
  intros.
  rewrite Zlength_firstn.
  lia.
Qed.

Local Lemma Zlength_skipn : forall (A : Type) n (l : list A),
  Zlength (skipn n l) = Z.max (Zlength l - (Z.max (Z.of_nat n) 0)) 0.
Proof.
  induction n; intros.
  - simpl.
    pose proof (Zlength_nonneg l). lia.
  - destruct l; simpl.
    + rewrite Zlength_nil. lia.
    + rewrite !Zlength_cons.
      rewrite IHn.
      pose proof (Zlength_nonneg l). lia.
Qed.

Local Lemma Zlength_skipn_to_nat : forall (A : Type) n (l : list A),
  Zlength (skipn (Z.to_nat n) l) = Z.max (Zlength l - (Z.max n 0)) 0.
Proof.
  intros.
  rewrite Zlength_skipn.
  lia.
Qed.

Lemma Zlength_sublist2 : forall (A : Type) lo hi (l : list A),
  Zlength (sublist lo hi l) = Z.max (Z.min hi (Zlength l) - Z.max lo 0) 0.
Proof.
  intros.
  unfold sublist.
  rewrite Zlength_skipn_to_nat, Zlength_firstn_to_nat.
  lia.
Qed.

Lemma Zlength_upd_Znth : forall (A : Type) i l (x : A),
  Zlength (upd_Znth i l x) = Zlength l.
Proof.
  intros.
  unfold upd_Znth. if_tac; auto.
  rewrite Zlength_app, Zlength_cons.
  rewrite !Zlength_sublist2. lia.
Qed.

Definition Zlength_fact P : Prop := P.

Lemma Zlength_fact_intro : forall (P : Prop),
  P -> Zlength_fact P.
Proof.
  auto.
Qed.

Lemma Zlength_fact_elim : forall (P : Prop),
  Zlength_fact P -> P.
Proof.
  auto.
Qed.

(** create a new database, do nothing if database already exists. *)
Ltac init_Zlength_db :=
  idtac.

(** remove the database, do nothing if database doesn't exist. *)
Ltac clear_Zlength_db :=
  repeat lazymatch goal with
  | f : Zlength_fact _ |- _ =>
    clear f
  end.

(** Add a new result to the databasem without checking for duplication. *)
Ltac add_Zlength_res H :=
  pose proof (Zlength_fact_intro _ H).

(** Test whether l exists in the database.
 * Success without side effect if existing, fail otherwise. *)
Ltac search_Zlength l :=
  lazymatch goal with
  | f : Zlength_fact (Zlength l = _) |- _ =>
    idtac
  end.

(* Arguments:
  l - the list to calculate length
  H - the name for result
*)
Ltac pose_Zlength l H :=
  lazymatch goal with
  | f : Zlength_fact (Zlength l = _) |- _ =>
    pose proof (Zlength_fact_elim _ f) as H
  end.

Ltac get_Zlength l :=
  lazymatch goal with
  | f : Zlength_fact (Zlength l = _) |- _ =>
    constr:(Zlength_fact_elim _ f)
  end.

Goal forall A (al bl cl : list A) n m,
  Zlength al = n -> Zlength bl = n -> Zlength cl = n + m ->
  Zlength al = n /\ Zlength bl = n /\ Zlength cl = n + m.
Proof.
  intros.
  init_Zlength_db.
  add_Zlength_res H.
  search_Zlength al.
  Fail search_Zlength bl.
  add_Zlength_res H0.
  search_Zlength bl.
  Fail search_Zlength cl.
  add_Zlength_res H1.
  search_Zlength cl.
  search_Zlength bl.
  pose_Zlength al ltac:(fresh).
Abort.

Lemma calc_Zlength_var : forall A (l : list A),
  Zlength l = Zlength l.
Proof.
  auto.
Qed.

Lemma calc_Zlength_nil : forall A,
  Zlength (@nil A) = 0.
Proof.
  auto.
Qed.

Lemma calc_Zlength_cons : forall A (l : list A) len x,
  Zlength l = len ->
  Zlength (x :: l) = 1 + len.
Proof.
  intros.
  rewrite Zlength_cons.
  lia.
Qed.

Lemma calc_Zlength_app : forall A (al bl : list A) alen blen,
  Zlength al = alen ->
  Zlength bl = blen ->
  Zlength (al ++ bl) = alen + blen.
Proof.
  intros.
  rewrite Zlength_app.
  lia.
Qed.

Lemma calc_Zlength_sublist : forall A (l : list A) len lo hi,
  Zlength l = len ->
  0 <= lo <= hi ->
  hi <= len ->
  Zlength (sublist lo hi l) = hi - lo.
Proof.
  intros.
  rewrite Zlength_sublist;
  lia.
Qed.

Lemma calc_Zlength_upd_Znth : forall A (l : list A) len i x,
  Zlength l = len ->
  Zlength (upd_Znth i l x) = len.
Proof.
  intros; subst; apply Zlength_upd_Znth.
Qed.

Lemma calc_Zlength_map : forall A B (l : list A) len (f : A -> B),
  Zlength l = len ->
  Zlength (map f l) = len.
Proof.
  intros.
  rewrite Zlength_map.
  auto.
Qed.

Ltac calc_Zlength_extra l := fail.

Ltac calc_Zlength l :=
  first
  [ search_Zlength l
  | lazymatch l with
    | @nil ?A =>
      add_Zlength_res (calc_Zlength_nil A)
    | @cons ?A ?x ?l =>
      calc_Zlength l;
      let H := get_Zlength l in
      add_Zlength_res (calc_Zlength_cons A l _ x H)
    | @app ?A ?l1 ?l2 =>
      calc_Zlength l1; calc_Zlength l2;
      let H1 := get_Zlength l1 in
      let H2 := get_Zlength l2 in
      add_Zlength_res (calc_Zlength_app A l1 l2 _ _ H1 H2)
    | @Zrepeat ?A ?x ?n =>
      add_Zlength_res (Zlength_Zrepeat A x n ltac:(lia))
    | @sublist ?A ?lo ?hi ?l =>
      calc_Zlength l;
      let H := get_Zlength l in
      let Z_solve :=
        try lia;
        fail 0 "cannot prove" lo hi "are in range for" l
      in
      add_Zlength_res (calc_Zlength_sublist A l _ lo hi H ltac:(Z_solve) ltac:(Z_solve))
    | @upd_Znth ?A ?i ?l ?x =>
      calc_Zlength l;
      let H := get_Zlength l in
      add_Zlength_res (calc_Zlength_upd_Znth A l _ i x H)
    | @map ?A ?B ?f ?l =>
      calc_Zlength l;
      let H := get_Zlength l in
      add_Zlength_res (calc_Zlength_map A B l _ f H)
    | _ =>
      tryif first [
        calc_Zlength_extra l
      | add_Zlength_res (calc_Zlength_var _ l);
        pose proof (Zlength_nonneg l)
      ] then idtac
      else
        fail "calc_Zlength does not support" l
    end
  ].

Ltac Zlength_solve :=
  init_Zlength_db;
  repeat match goal with
  | |- context [Zlength ?l] =>
    progress (
      calc_Zlength l;
      try (
        let H := get_Zlength l in
        rewrite !H
      )
    )
  end;
  lia.

















(** * list_form *)
Lemma list_repeat_Zrepeat : forall (A : Type) (x : A) (n : Z),
  list_repeat (Z.to_nat n) x = Zrepeat x n.
Proof. intros *. rewrite <- repeat_list_repeat. auto. Qed.

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
Proof. intros. unfold Zrepeat. rewrite repeat_list_repeat. apply Znth_list_repeat_inrange; auto. Qed.

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
  destruct (Sumbool.sumbool_and _ _ _ _ (zle 0 i) (zlt i (Zlength l)));
    destruct (Sumbool.sumbool_and _ _ _ _ (zle 0 j) (zlt j (Zlength l))).
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
