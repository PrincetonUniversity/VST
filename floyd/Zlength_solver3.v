Require Import VST.floyd.base2.
Require Export VST.floyd.Zlength_solver_base.
Require Import Lia.
Import ListNotations.

(** list_solver3 is a solver using a database of the form
  Zlength_db [Zlength al = n; Zlength bl = m; ...].
  And it stores the final simplified result, e.g.
  Zlength (map f (al ++ bl)) = Zlength al + Zlength bl).
 *)

Inductive Zlength_db : list Prop -> Prop :=
| Zlength_db_nil : Zlength_db nil
| Zlength_db_cons : forall (P : Prop) tl,
      P ->
      Zlength_db tl ->
      Zlength_db (P :: tl).

Lemma In_Zlength_db : forall db_list A (l : list A) len,
  Zlength_db db_list ->
  In (Zlength l = len) db_list ->
  Zlength l = len.
Proof.
  intros.
  induction db_list.
  - inversion H0.
  - inversion H0.
    + inv H; auto.
    + inv H; auto.
Qed.

(** create a new database, do nothing if database already exists. *)
Ltac init_Zlength_db :=
  first [
    lazymatch goal with
    | _ : Zlength_db _ |- _ =>
      idtac
    end
  | pose proof Zlength_db_nil
  ].

(** remove the database, do nothing if database doesn't exist. *)
Ltac clear_Zlength_db :=
  lazymatch goal with
  | db : Zlength_db _ |- _ =>
    clear db
  | _ =>
    idtac
  end.

(** Add a new result to the databasem without checking for duplication. *)
Ltac add_Zlength_res H :=
  lazymatch type of H with Zlength ?l = ?len =>
    lazymatch goal with db : Zlength_db _ |- _ =>
      let new_db := fresh in
      pose proof (Zlength_db_cons (Zlength l = len) _ H db) as new_db;
      clear db;
      rename new_db into db
(*     | _ => fail 0 "xxx" *)
    end
(*     | _ => fail 0 "yyy" *)
  end.

(** Test whether l exists in the database.
 * Success without side effect if existing, fail otherwise. *)
Ltac search_Zlength l :=
  lazymatch goal with db : Zlength_db ?db_list |- _ =>
    let rec search_aux db_list :=
      lazymatch db_list with
      | nil => fail 0 l "is not found in Zlength_db"
      | (Zlength l = _) :: _ => idtac
      | _ :: ?db_tl => search_aux db_tl
      end
    in
    search_aux db_list
  end.

Hint Resolve in_eq in_cons : In.

(* Arguments:
  l - the list to calculate length
  H - the name for result
*)
Ltac pose_Zlength l H :=
  let In_solve :=
    auto 1000 with nocore In; fail 0 l "is not found in database"
  in
  lazymatch goal with db : Zlength_db ?db_list |- _ =>
    pose proof (In_Zlength_db _ _ l _ db ltac:(In_solve)) as H
  end.

Ltac get_Zlength l :=
  let In_solve :=
    auto 1000 with nocore In; fail 0 l "is not found in database"
  in
  lazymatch goal with db : Zlength_db ?db_list |- _ =>
    constr:(In_Zlength_db _ _ l _ db ltac:(In_solve))
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

Lemma calc_Zlength_nil : forall A,
  Zlength (@nil A) = 0.
Proof.
  auto.
Qed.

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

Ltac calc_Zlength l := idtac.

Ltac calc_Zlength_default l :=
  first
  [ search_Zlength l
  | lazymatch l with
    | @nil ?A =>
      add_Zlength_res (calc_Zlength_nil A)
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
      | fail "calc_Zlength does not support" l
      ]
    end
  ].

Ltac calc_Zlength l ::=
  calc_Zlength_default l.

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

