Require Import VST.floyd.base2.
Require Import VST.floyd.list_solver_base.


(** list_solver2 is a list solver using a database of the form
  Zlength_tag /\ Zlength al = n /\ Zlength bl = m /\ ...
 *)

(***************** Zlength_solve using a database *************)
Definition Zlength_tag := True.

Lemma Zlength_db_new : forall (H : Prop), H -> Zlength_tag /\ H.
Proof. unfold Zlength_tag. tauto. Qed.

Lemma Zlength_db_inc : forall (H H0 : Prop), H -> Zlength_tag /\ H0 -> Zlength_tag /\ (H /\ H0).
Proof. tauto. Qed.

Ltac init_Zlength_db :=
  idtac.

Ltac clear_Zlength_db :=
  lazymatch goal with
  | db : Zlength_tag /\ _ |- _ =>
    clear db
  | _ =>
    idtac
  end.

Ltac add_Zlength_res H :=
  first
  [ match goal with res_db : Zlength_tag /\ ?res |- _ =>
      let new_db := fresh in
      pose (Zlength_db_inc _ _ H res_db) as new_db;
      clearbody new_db;
      clear res_db;
      rename new_db into res_db
    end
  | let new_db := fresh "Zlength_db" in
    pose (Zlength_db_new _ H) as new_db;
    clearbody new_db
  ].

Ltac search_Zlength l :=
  match goal with res_db : Zlength_tag /\ ?res |- _ =>
    let rec search_aux res :=
      match res with
      | ?res1 /\ ?res2 => first [search_aux res1 | search_aux res2]
      | Zlength l = _ => idtac
      end
    in
    search_aux res
  end.

Ltac get_Zlength l :=
  lazymatch goal with
  | db : Zlength_tag /\ ?res |- _ =>
    let rec get_aux db :=
      lazymatch type of db with
      | Zlength l = _ /\ ?res2 =>
        constr:(proj1 db)
      | Zlength l = _ =>
        db
      | _ =>
        get_aux (proj2 db)
      end
    in
    get_aux (proj2 db)
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
  let H := get_Zlength al in
  pose proof H.
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
      add_Zlength_res (Zlength_sublist lo hi l ltac:(omega) ltac:(omega))
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
  ].

Ltac Zlength_eq_solve_by_calc :=
  repeat lazymatch goal with
  | |- _ /\ _ => split
  end;
  (* Consider the first _ as {=, <, <=, ...}. *)
  lazymatch goal with
  | |- _ (Zlength ?l1) (Zlength ?l2) =>
    calc_Zlength l1; calc_Zlength l2; omega
  | |- _ (Zlength ?l1) _ =>
    calc_Zlength l1; omega
  | |- _ _ (Zlength ?l2) =>
    calc_Zlength l2; omega
  | |- _ _ _ =>
    omega
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
  clear_Zlength_db;
  omega.

