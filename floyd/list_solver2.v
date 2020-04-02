Require Import VST.floyd.base2.
Require Export VST.floyd.list_solver_base.
Import ListNotations.

(** list_solver4 is a solver using a database of the form
  Zlength_db [Zlength al = n; Zlength bl = m; ...].
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

Lemma calc_Zlength_var : forall A (al : list A),
  Zlength al = Zlength al.
Proof.
  auto.
Qed.

Lemma calc_Zlength_app : forall A (al bl : list A) alen blen,
  Zlength al = alen ->
  Zlength bl = blen ->
  Zlength (al ++ bl) = alen + blen.
Proof.
  intros.
  rewrite Zlength_app.
  omega.
Qed.

Lemma calc_Zlength_sublist : forall A (l : list A) len lo hi,
  Zlength l = len ->
  0 <= lo <= hi ->
  hi <= len ->
  Zlength (sublist lo hi l) = hi - lo.
Proof.
  intros.
  rewrite Zlength_sublist;
  omega.
Qed.

Lemma calc_Zlength_map : forall A B (l : list A) len (f : A -> B),
  Zlength l = len ->
  Zlength (map f l) = len.
Proof.
  intros.
  rewrite Zlength_map.
  auto.
Qed.

Ltac calc_Zlength l :=
(*   idtac l; *)
  first
  [ search_Zlength l
  | lazymatch l with
    | ?l1 ++ ?l2 =>
      calc_Zlength l1; calc_Zlength l2;
      let H1 := get_Zlength l1 in
      let H2 := get_Zlength l2 in
      add_Zlength_res (calc_Zlength_app _ l1 l2 _ _ H1 H2)
    | Zrepeat ?x ?n =>
      add_Zlength_res (Zlength_Zrepeat _ x n ltac:(omega))
    | sublist ?lo ?hi ?l =>
      calc_Zlength l;
      let H := get_Zlength l in
      let Z_solve :=
        first[
          omega
        | fail 0 "cannot prove" lo hi "are in range for" l
        ]
      in
      add_Zlength_res (calc_Zlength_sublist _ l _ lo hi H ltac:(Z_solve) ltac:(Z_solve))
    | map ?f ?l =>
      calc_Zlength l;
      let H := get_Zlength l in
      add_Zlength_res (calc_Zlength_map _ _ l _ f H)
    | _ =>
      first [
        is_var l;
        add_Zlength_res (calc_Zlength_var _ l);
        pose proof (Zlength_nonneg l)
      | fail "calc_Zlength does not support" l
      ]
    end
  ];
(*   idtac "ok" l; *)
  idtac.

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
  omega.

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
  omega.

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
  omega.


Goal forall A (al bl cl : list A) n m,
  Zlength al = n -> Zlength bl = m -> Zlength cl = n + m ->
  Zlength cl = Zlength (al ++ bl).
Proof.
  intros.
  Zlength_solve_cached2.
Abort.
(* 
Require VST.floyd.list_solver.
Ltac list_form := list_solver.list_form.

Example strcat_loop2 : forall n x ld ls,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  Zlength (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero]))))))
  = Zlength (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef).
Proof.
  idtac "strcat_loop2".
  intros.
  list_form.
  Time Zlength_solve.
Time Qed.

Example strcat_return_new : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros.
  list_form. apply Znth_eq_ext.
  Time Zlength_solve.
Abort. *)

(* Ltac Zlength_solve ::= Zlength_solve. *)

Require VST.floyd.list_solver.
Ltac list_solver.Zlength_solve ::= Zlength_solve.

