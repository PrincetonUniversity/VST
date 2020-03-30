Require Import VST.floyd.base2.
Require Export VST.floyd.list_solver_base.
Import ListNotations.

(** list_solver3 is a solver using a database of the form
  Zlength_db [Zlength al = n; Zlength bl = m; ...].
  And it stores only one layer of simplification, e.g.
  Zlength (map f (al ++ bl)) = Zlength (al ++ bl).
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



(** Add a new result to the databasem without checking for duplication. *)
Ltac add_Zlength_res H :=
  lazymatch type of H with Zlength ?l = ?len =>
    lazymatch goal with db : Zlength_db _ |- _ =>
      let new_db := fresh in
      pose proof (Zlength_db_cons _ _ H db) as new_db;
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

Ltac calc_Zlength l :=
(*   idtac l; *)
  first
  [ search_Zlength l
  | lazymatch l with
    | ?l1 ++ ?l2 =>
      calc_Zlength l1; calc_Zlength l2;
      add_Zlength_res (Zlength_app _ l1 l2)
    | Zrepeat ?x ?n =>
      add_Zlength_res (Zlength_Zrepeat _ x n ltac:(omega))
    | sublist ?lo ?hi ?l =>
      calc_Zlength l;
      first [
        let H := get_Zlength l in
        add_Zlength_res (Zlength_sublist lo hi l ltac:(rewrite !H; omega) ltac:(rewrite !H; omega))
      | add_Zlength_res (Zlength_sublist lo hi l ltac:(omega) ltac:(omega))
      ]
    | map ?f ?l =>
      calc_Zlength l;
      add_Zlength_res (Zlength_map _ _ f l)
    | _ =>
      first [
        is_var l;
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
  init_Zlength_db.
  Time Zlength_solve.
Time Qed.

Goal forall A (al bl cl : list A) n m,
  Zlength al = n -> Zlength bl = m -> Zlength cl = n + m ->
  Zlength cl = Zlength (al ++ bl).
Proof.
  intros.
  Zlength_solve.
Abort.

