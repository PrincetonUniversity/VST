(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

Require Import FCF.Comp.

Local Open Scope comp_scope.

(* ret is used to promote anything in Set to a probabilistic computation.  There must be an EqDec proof in the environment for the set in order for this notation to work. *)
Notation "'ret' v" := (Ret (EqDec_dec _) v)
  (at level 75).

(* A computation that samples a bit vector of length n (uniformly). *)
Notation "{ 0 , 1 } ^ n" := (Rnd n)
  (right associativity, at level 77) : comp_scope.

(* A computation that flips a fair coin. *)
Notation "{ 0 , 1 }" := (Bind (Rnd 1) (fun m => ret (Vector.hd m)))
  (right associativity, at level 75) : comp_scope.

(* A sequence of probabilistic computations. *)
Notation "x <-$ c1 ; c2" := (@Bind _ _ c1%comp (fun x => c2)) 
  (right associativity, at level 81, c1 at next level) : comp_scope.

(* The following notations run the first computation that produces a tuple, unpacks the tuple, and provides names for the values that can be used by the second computation. *)
Notation "[ x1 , x2 ] <-$2 c1 ; c2" := 
  (Bind c1%comp (fun z => let '(x1, x2) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

Notation "[ x1 , x2 , x3 ] <-$3 c1 ; c2" := 
  (Bind c1%comp (fun z => let '(x1, x2, x3) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

(* setLet enables "let" notation but ensures that the first type is in Set.  This helps check some errors in definitions. *)
Definition setLet(A : Set)(B : Type)(a : A)(f : A -> B) := f a.

(* A more consistent notation for let x := e1 in e2. *)
Notation "x <- e1 ; e2" := (setLet e1 (fun x => e2)) (right associativity, at level 81, e1 at next level) : comp_scope.

(* The following notations simply unpack the tuple in the first term and name all the values so they can be used in the second term. *)
Notation "[ x1 , x2 ] <-2 e1 ; c2" := (let '(x1, x2) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 ] <-3 e1 ; c2" := (let '(x1, x2, x3) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 , x4 ] <-4 e1 ; c2" := (let '(x1, x2, x3, x4) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 , x4 , x5 ] <-5 e1 ; c2" := (let '(x1, x2, x3, x4, x5) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

(* Run a sequence of probabilistic computations with oracle access. *)
Notation "x <--$ c1 ; c2" := (OC_Bind c1%comp (fun x => c2)) 
  (right associativity, at level 81, c1 at next level) : comp_scope.

(* The following notations run the first computation (with oracle access) that produces a tuple, unpacks the tuple, and provides names for the values that can be used by the second computation. *)
Notation "[ x1 , x2 ] <--$2 c1 ; c2" := 
  (OC_Bind c1%comp (fun z => let '(x1, x2) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

Notation "[ x1 , x2 , x3 ] <--$3 c1 ; c2" := 
  (OC_Bind c1%comp (fun z => let '(x1, x2, x3) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

(* Promote a computation into a computation with oracle access. *)
Notation "$ c" := (OC_Ret _ _ c) (at level 79) : comp_scope.


(* The maybe monad and probabilistic maybe monad. *)
Notation "x <-? c1 ; c2" := (maybeBind c1 (fun x => (c2)))
                              (right associativity, at level 81, c1 at next level) : comp_scope.

Definition maybeBindComp(A B : Set)(eqdb : EqDec B)(c : Comp (option A))(f : A -> Comp B) : Comp (option B) :=
  opt_a <-$ c;
  match opt_a with
    | None => ret None
    | Some a => b <-$ (f a); ret (Some b)
  end.

Notation "x <-$? c1 ; c2" := 
   (maybeBindComp _ (c1)%comp (fun x => (c2)%comp))
                              (right associativity, at level 81, c1 at next level) : comp_scope.


Infix "xor" := (BVxor _) (at level 30).

