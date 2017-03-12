Load loadpath.
Require Import Coq.Lists.List Coq.Arith.EqNat Coq.Arith.Compare_dec
               Coq.ZArith.ZArith.
Require Import veristar.tactics.

Set Implicit Arguments.
Unset Strict Implicit.

Section option.
Variables (A B : Type) (h : A -> B) (f : A -> option B) (o : option A).

Definition omap := match o with Some a => Some (h a) | None => None end.

Definition obnd := match o with Some a => f a | None => None end.

End option.
Implicit Arguments omap [A B].
Implicit Arguments obnd [A B].

Definition isSome {A : Type} (o : option A) :=
  match o with Some _ => true | _ => false end.

Section comp.
Variables (A B C : Type) (g : B -> C) (f : A -> B) (a : A).

Definition compose := g (f a).

End comp.
Implicit Arguments compose [A B C].

(*new notation*)
(*Notation "f \o g" := (compose f g) (at level 54, right associativity).*)

(*for backwards compatibility*)
Infix "oo" := compose (at level 54, right associativity).

(*why does List appear to not export this notation?*)
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

Fixpoint zip_with_acc {A B : Type} acc (l1 : list A) (l2 : list B) :=
  match l1, l2 with
    | a :: l1', b :: l2' => (a, b) :: zip_with_acc acc l1' l2'
    | _, _ => acc
  end.

Definition zip {A B : Type} := @zip_with_acc A B [].

Section iter.
Variables (A : Type) (f : nat -> A -> A).

Fixpoint iter (n : nat) (a : A) :=
  match n with
    | O => a
    | S n' => iter n' (f n' a)
  end.

End iter.
Implicit Arguments iter [A].

Section tryfind.
Variables (A E B : Type) (f : A -> E + B).

Fixpoint tryfind (err : E) (l : list A) :=
  match l with
    | nil => inl _ err
    | a :: l' => match f a with
                   | inl err' => tryfind err' l'
                   | inr success as r => r
                 end
  end.

End tryfind.

Definition max (n m : nat) := if leb n m then m else n.

Definition maxs (l : list nat) := fold_left (fun m n => max m n) l 0.

Definition elemb (n : nat) := existsb (fun m => beq_nat n m).

(*positive lemmas*)

Require Import ZArith.

Lemma Ppred_decrease n : (n<>1)%positive -> (nat_of_P (Ppred n)<nat_of_P n)%nat.
Proof.
intros; destruct (Psucc_pred n) as [Hpred | Hpred]; try contradiction;
  pattern n at 2; rewrite <- Hpred; rewrite nat_of_P_succ_morphism; omega.
Defined.

Ltac Ppred_tac n :=
  apply Ppred_decrease; destruct n;
  let H := fresh "H" in intro H; try (inversion H||inversion H1); congruence.

Definition Pleb (x y : positive) :=
  match Pcompare x y Eq with
    | Lt => true
    | Eq => true
    | Gt => false
  end.

Lemma Pleb_Ple (x y : positive) : Pleb x y = true <-> Ple x y.
Proof.
unfold Pleb, Ple; split; intro H1.
intro H2; done(rewrite H2 in H1).
done(remember ((x ?= y)%positive Eq) as b; destruct b).
Qed.

(* N lemmas *)

Require Import NArith NOrderedType.

Definition Nleb (x y : N) :=
  match Ncompare x y with
    | Lt => true
    | Eq => true
    | Gt => false
  end.

Lemma Nleb_Nle (x y : N) : Nleb x y = true <-> Nle x y.
Proof.
unfold Nleb, Nle; split; intro H1.
intro H2; done(rewrite H2 in H1).
done(remember ((x ?= y)%N) as b; destruct b).
Qed.

(*reverse comparison*)

Section revc.
Variables (A : Type) (c : A -> A -> comparison).

Definition revc a1 a2 :=
  match c a1 a2 with
    | Gt => Lt
    | Eq => Eq
    | Lt => Gt
  end.

End revc.

Inductive ret_kind (val : Type) : Type :=
| Success : val -> ret_kind val
| Failure : ret_kind val.

Implicit Arguments Success [val].
Implicit Arguments Failure [val].

