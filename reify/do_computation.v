(* compute.v - Mario Alvarez - January 2014
 * Implementation of "compute" solver plugin for MirrorShard *)

(* Need all of these? *)
Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import MirrorShard.Expr.

Module do_computation (uk : unknown_types).

Module our_funcs := funcs uk.
Import our_funcs.
Import all_types.

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
Definition is_const_base (f : func) :=
NPeano.ltb f computable_prefix_length.

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
Definition do_computation (user_functions : list (signature all_types)) (e : expr all_types) (t : tvar) : 
option (tvarD all_types t) :=
if is_const e then
  match (@exprD all_types (functions ++ user_functions) nil nil e t) with
    | Some v => Some v
    | None => None (** should be dead code if e is well typed **)
  end
else
  None.

Lemma do_computation_correct : forall (user_functions : list (signature all_types)) (e : expr all_types) (t : tvar) (v : tvarD all_types t),
do_computation user_functions e t = Some v ->
forall (vars uvars : env all_types),
exprD (functions ++ user_functions) uvars vars e t = Some v.
Proof.
  intros.
  unfold do_computation in *.
  destruct (is_const e); try congruence.
  remember (exprD (functions ++ user_functions) [] [] e t) as exprDf.
  destruct exprDf.
  - inversion H; subst.
    symmetry in HeqexprDf.
    eapply exprD_weaken in HeqexprDf.
    eassumption.
  - inversion H.
Qed.

(* Some fun little examples *)
Eval vm_compute in (do_computation nil (Func 13 [(Func 1 [])]) (tvType 11)).
Eval vm_compute in (do_computation nil (Equal nat_tv (Func 1 []) (Func 1 [])) tvProp).
Eval vm_compute in (do_computation nil (Equal nat_tv (Func 13 [(Func 1 [])]) (Func 1 [])) tvProp).
Eval vm_compute in (do_computation nil (Equal nat_tv (Func 13 [(Func 1 [])]) (Func 13 [(Func 1 [])])) tvProp).

Print expr.
Print tvar.
Check nth_error.

Eval vm_compute in (nth_error [1; 2; 3; 4] 3).
Print Impl.
Print Sig.

(* Computes an Expr that represents an equality (for types with decidable equality), 
 * Appealing to the decision procedures contained in the type signature *)
Check const_seqb.
Print const_seqb.
Locate const_seqb.


Definition do_computation_equal (user_functions : list (signature all_types)) (e : expr all_types) : bool.
remember e as exp; destruct e.
(* We just return false in all cases except for Equal *)
- apply false.
- apply false.
- apply false.
(* Equal *)
- destruct (do_computation user_functions e1 t).
  (* lhs successfully computes *)
  + destruct (do_computation user_functions e2 t).
    (* rhs also successfully computes *)
    { destruct t.
      (* if t is tvProp, give up (no equality on Props!) *)
      - apply false.
      (* if t is an actual type, things get interesting.
         we need to do some manipulation to get types to work out.
         a naive approach would lead to Coq thinking that the implementation
         pulled out of the types list, and the implementation from the tvarD
         returned by do_computation don't match - but they do! *)
      - unfold tvarD in *. unfold Impl_ in *.
        destruct (nth_error all_types n).
        (* if we found the type (we should have...) actually check equality *)
        + apply (t.(Eqb) t0 t1).
        (* otherwise, give up *)
        + apply false.
    }
    (* rhs failed to compute *)
    { apply false. }
  (* lhs failed to compute *)
  + apply false.
(* the rest... *)
- apply false.
- apply false.
Defined.


(* some tests for do_compute_prop *)
Eval vm_compute in (do_computation nil (Func 1 []) (tvType 11)).
Eval vm_compute in (do_computation_equal nil (Equal (tvType 11) (Func 13 [(Func 1 [])]) (Func 13 [(Func 1 [])]))).

Eval vm_compute in (do_computation nil (Func 13 [(Func 1 [])]) (tvType 11)).
Eval vm_compute in (do_computation nil (Equal nat_tv (Func 1 []) (Func 1 [])) tvProp).
Eval vm_compute in (do_computation nil (Equal nat_tv (Func 13 [(Func 1 [])]) (Func 1 [])) tvProp).
Eval vm_compute in (do_computation nil (Equal nat_tv (Func 13 [(Func 1 [])]) (Func 13 [(Func 1 [])])) tvProp).


End do_computation.