(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

(* An attempt at uniform notation.  It works okay for writing definitions, but eventually you have to leave the monad in a proof, and then you lose the notation.  So this approach probably won't work very well. *)

Require Import FCF.Comp.

Class Monad
      (M : Set -> Type) :=
  {
      MRet : forall (A : Set), EqDec A -> A -> M A;
      MBind : forall (A : Set), M A -> forall (B : Set), (A -> M B) -> M B

      (*
      right_ident : forall (A : Type)(a : M A), a = Bind a (@Ret A);
      left_ident : forall (A : Type)(a : A)(B : Type)(f : A -> M B),
                     f a = Bind (Ret a) f
      associativity
*)
  }.

Instance IdentMonad : Monad (fun (A: Set) => A).
econstructor.
intuition.
intuition.
Defined.

Instance CompMonad : Monad Comp.
econstructor.
intuition.
apply Ret; intuition.
unfold eq_dec; intuition.
eapply EqDec_dec; trivial.

intuition.
eapply Bind; eauto.
Defined.


Instance OracleCompMonad : forall (D R : Set), Monad (OracleComp D R).

econstructor.
intuition.
apply (OC_Ret _ _ (Ret (EqDec_dec _ ) H0)).

intuition.
eapply OC_Bind; eauto.

Defined.

Notation "x <- c1 ; c2" := (MBind c1 _ (fun x => c2)) 
  (right associativity, at level 81, c1 at next level) : comp_scope.

Notation "$ { 0 , 1 } ^ n" := (Rnd n)
  (right associativity, at level 77) : comp_scope.

Notation "$ { 0 , 1 }" := (Bind (Rnd 1) (fun m => Ret _ (Vector.hd m)))
  (right associativity, at level 75) : comp_scope.

Notation "'ret' v" := (MRet _ v)
  (at level 75).

Notation "'cret' v" := (Ret (EqDec_dec _) v)
  (at level 75).

Notation "'ocret' v" := (OC_Ret _ _ v)
  (at level 75).

Notation "[ x1 , x2 ] <- c1 ; c2" := 
  (MBind c1 _ (fun z => let '(x1, x2) := z in c2)) (right associativity, at level 81, c1 at next level) : comp_scope.



Local Open Scope comp_scope.