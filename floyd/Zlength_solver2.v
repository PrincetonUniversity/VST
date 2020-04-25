Require Import VST.floyd.base2.
Require Export VST.floyd.Zlength_solver_base.
Require Import Lia.
Import ListNotations.

(** list_solver2 is a solver using a database of the form
  H ：Zlength_fact (Zlength al = n)
  H2 ：Zlength_fact (Zlength bl = m)
  ...
  And it stores the final simplified result, e.g.
  Zlength (map f (al ++ bl)) = Zlength al + Zlength bl).
 *)

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
        first[
          lia
        | fail 0 "cannot prove" lo hi "are in range for" l
        ]
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
      first [
        is_var l;
        add_Zlength_res (calc_Zlength_var _ l);
        pose proof (Zlength_nonneg l)
      | calc_Zlength_extra l
      | fail "calc_Zlength does not support" l
      ]
    end
  ].

Ltac Zlength_only :=
  init_Zlength_db;
  repeat match goal with
  | |- context [Zlength ?l] =>
    tryif is_var l then
      fail
    else
      calc_Zlength l;
      let H := get_Zlength l in
      rewrite !H
  end.

Ltac Zlength_solve :=
  init_Zlength_db;
  repeat match goal with
  | |- context [Zlength ?l] =>
    tryif is_var l then
      fail
    else
      calc_Zlength l;
      let H := get_Zlength l in
      rewrite !H
  end;
  lia.

Ltac Zlength_solve_cached :=
  init_Zlength_db;
  repeat match goal with
  | |- context [Zlength ?l] =>
    tryif is_var l then
      fail
    else
      calc_Zlength l;
      let H := get_Zlength l in
      rewrite !H
  end;
  clear_Zlength_db;
  lia.

Ltac Zlength_solve_cached2 :=
  repeat match goal with
  | |- context [Zlength ?l] =>
    tryif is_var l then
      fail
    else
      init_Zlength_db;
      calc_Zlength l;
      let H := get_Zlength l in
      rewrite !H;
      clear_Zlength_db
  end;
  lia.


