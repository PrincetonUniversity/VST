Require Export VST.floyd.list_solver.
Require Export VST.floyd.Zlength_solver5.
Require Import VST.floyd.base2.
Require Import VST.floyd.reptype_lemmas.

Ltac list_solver.Zlength_solve ::= Zlength_solve.
(* Ltac Zlength_simpl_conc ::= autorewrite with Zlength. *)
(* Ltac Zlength_simpl_in H ::= autorewrite with Zlength in H. *)
(* Ltac Zlength_simpl_all ::= autorewrite with Zlength in *. *)
Ltac Zlength_simpl_conc ::=
  repeat match goal with
  | |- context [@Zlength ?A _] =>
    lazymatch A with
    | reptype _ =>
      let A' := eval compute in A in
      change A with A'
    end
  end;
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

Ltac Zlength_simpl_in H ::=
  init_Zlength_db;
  repeat match type of H with
  | context [Zlength ?l] =>
    tryif is_var l then
      fail
    else
      calc_Zlength l;
      let H1 := get_Zlength l in
      rewrite !H1 in H
  end.

Ltac Zlength_simpl_all ::=
  Zlength_simpl_conc;
  repeat match goal with
  | H : _ |- _ =>
    lazymatch type of H with
    | Zlength_fact _ => fail
    | _ =>
      match type of H with
      | context [Zlength ?l] =>
        tryif is_var l then
          fail
        else
          calc_Zlength l;
          let H1 := get_Zlength l in
          rewrite !H1 in H
      end
    end
  end.
