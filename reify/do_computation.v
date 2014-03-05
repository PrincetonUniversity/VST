(* compute.v - Mario Alvarez - January 2014
 * Implementation of "compute" solver plugin for MirrorShard *)

(* Need all of these? *)
(* Require Import floyd.proofauto. *)
Require Import types.
Require Import MirrorShard.Expr.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.

(* Cleaner syntax for Nat pattern-matches and function lists *)
Local Open Scope nat.
Import List.
Import ListNotations.

(* Listing of which functions compute directly into consts (taking no arguments)
 * and which do not. *)
(*
Definition is_const_base (f : func) :=
  match f with
    | 1  (* O_f *)
    | 20 (* Z0_f *)
    | 23 (* xH_f *)
    | 35 (* Ceq_f *)
    | 36 (* Cne_f *)
    | 37 (* Clt_f *)
    | 38 (* Cle_f *)
    | 39 (* Cgt_f *)
    | 40 (* Cge_f *)
    | 47 (* int_max_unsigned *)
      => true

    | _ => false
  end.
 *)
Section typed.
  Variable all_types : list type.
  Variable all_functions : list (signature all_types).
  (* shadow definitions from functions.v with more useful ones *)
  (* Let all_types := (all_types_r user_types). *)

  Definition is_const_base (f : func) :=
    NPeano.ltb f (computable_prefix_length all_types).

  (* Decide if an expression can compute directly into a Const
   * (by converting the pre-defined functions we have defined
   * as convertible into consts) *)
  Fixpoint is_const (e : expr all_types) :=
    let is_const_l (es : list (expr all_types)) : bool :=
        fold_right andb true (map is_const es)
    in
    match e with
      (* it and its arguments must be const *)
      | Func f es => andb (is_const_base f) (is_const_l es)
      | Const _ _ => true
      (*    | Equal _ l r => andb (is_const l) (is_const r) *)
      | _ => false

    end.

  (* Simplify an expression, if we can.
   * Expects that a user-supplied Ltac will have already converted
   * user-defined functions into Consts, as appropriate *)

  Definition do_computation (e : expr all_types) (t : tvar) :
    option (tvarD all_types t) :=
    if is_const e then
      match (@exprD all_types (*(functions ++*) all_functions nil nil e t) with
        | Some v => Some v
        | None => None (** should be dead code if e is well typed **)
      end
    else
      None.

  (*Lemma do_computation_correct : forall (user_functions : list (signature all_types)) (e : expr all_types) (t : tvar) (v : tvarD all_types t),
                                   do_computation user_functions e t = Some v ->
                                   forall (vars uvars : env all_types),
                                     exprD (functions ++ user_functions) uvars vars e t = Some v.*)
  Lemma do_computation_correct : forall (e : expr all_types) (t : tvar) (v : tvarD all_types t),
                                   do_computation e t = Some v ->
                                   forall (vars uvars : env all_types),
                                     exprD (all_functions) uvars vars e t = Some v.
  Proof.
    intros.
    unfold do_computation in *.
    destruct (is_const e); try congruence.
    remember (exprD (all_functions) [] [] e t) as exprDf.
    (* rewrite HeqexprDf in H. *)
    destruct exprDf.
    - symmetry in HeqexprDf.
      eapply exprD_weaken in HeqexprDf.
      rewrite app_nil_l in HeqexprDf.
      rewrite app_nil_l in HeqexprDf.
      rewrite HeqexprDf.
      assumption.

    - inversion H.
  Qed.

  (* Some fun little examples *) (*
  Eval vm_compute in (do_computation nil (Func 13 [(Func 1 [])]) (tvType 11)).

  Eval vm_compute in (do_computation nil (Equal nat_tv (Func 1 []) (Func 1 [])) tvProp).
  Eval vm_compute in (do_computation nil (Equal nat_tv (Func 13 [(Func 1 [])]) (Func 1 [])) tvProp).
  Eval vm_compute in (do_computation nil (Equal nat_tv (Func 13 [(Func 1 [])]) (Func 13 [(Func 1 [])])) tvProp). *)

  Definition do_computation_equal (e : expr all_types) : bool :=
    match e with
      | Equal t l r =>
        match do_computation l t with
          | Some l' =>
            match do_computation r t with
              | Some r' => get_Eq all_types t l' r'
              | _ => false
            end
          | _ => false
        end
      | _ => false
    end.

  (* some tests for do_computation_equal *)
  Eval vm_compute in (do_computation (Func 1 []) (tvType 11)).
  Eval vm_compute in (do_computation_equal (Equal (tvType 11) (Func 13 [(Func 1 [])]) (Func 13 [(Func 1 [])]))).

  (* consider tactic needed for this correctness proof *)
  Require Import ExtLib.Tactics.Consider.
  Lemma do_computation_equal_correct :
    forall (t : tvar) (l r : expr all_types),
      do_computation_equal (Equal t l r) = true ->
      exists (res : tvarD all_types t),
        do_computation l t = Some res /\
        do_computation r t = Some res.

  Proof.
    intros.
    simpl in H.
    remember (do_computation r t) as do_rhs.
    remember (do_computation l t) as do_lhs.
    destruct do_lhs; destruct do_rhs; try (solve [inversion H]).
    - consider (get_Eq all_types t t0 t1). intro.
      exists t0. rewrite <- H. split; reflexivity.
  Qed.

End typed.