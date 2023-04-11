(** * Utilities / extensions for the Ltac2 "constr" type *)

Require Import Ltac2.Ltac2.

(* The coressponding functions in the Ltac2 library don't match the OCaml parameter order.
   If we want to use the OCaml order for the constr fold functions we need to redefine it - otherwise we can't use (fold_right f) as function argument to the array *)

Ltac2 rec array_fold_right_aux (f : 'b -> 'a -> 'a) (b : 'b array) (a : 'a) (pos : int) (len : int) : 'a :=
  (* Note: one could compare pos<0.
     We keep an extra len parameter so that the function can be used for any sub array *)
  match Int.equal len 0 with
  | true => a
  | false => array_fold_right_aux f b (f (Array.get b pos) a) (Int.sub pos 1) (Int.sub len 1)
  end.

Ltac2 array_fold_right (f : 'b -> 'a -> 'a) (b : 'b array) (a : 'a) := array_fold_right_aux f b a (Int.sub (Array.length b) 1) (Array.length b).

(** This is a simple (and fast) function to call "f" on all applications.
    It is intended to extract data from terms which are mostly applications of constructors on some terms.
    It does not recurse into type terms, matches, lambdas, fixpoints.
    In applications it does not recurse into function terms, but into arguments. 
    The function "f" is only called for terms which are applications. *)

Ltac2 rec fold_right_app (f : constr -> 'a -> 'a ) (term : constr) (a : 'a ) : 'a :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Cast constr1 cast constr2
    (* Don't recurse into type of cast - just the cast term *)
    => fold_right_app f constr1 a
  | Constr.Unsafe.Prod binder constr
    (* Don't recurse into type of binder - just the bound term *)
    => fold_right_app f constr a
  | Constr.Unsafe.LetIn binder constr1 constr2
    (* Don't recurse into type of binder - just the assigned and bound term *)
    => fold_right_app f constr1 (fold_right_app f constr2 a)
  | Constr.Unsafe.App constr_func constr_arr_args
    (* Call "f" for the complete "term" *)
    (* Don't recurse into the function term - just into the array of arguments *)
    => f term (array_fold_right (fold_right_app f) constr_arr_args a)
  | _ => a
  end.

(** Examples *)

(*
Ltac2 Eval fold_right_app (fun c l => c :: l) constr:(1+2+3) [].
*)


