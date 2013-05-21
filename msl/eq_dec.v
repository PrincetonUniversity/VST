(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(* This file contains the class of decidable equality and associated theory
    of updateable functions. *)

Require Import msl.base.

(* Class of decidable equality *)
Class EqDec (A : Type) : Type := 
  eq_dec : forall a a' : A, {a = a'} + {a <> a'}.

Instance EqDec_nat : EqDec nat := eq_nat_dec.

(* Theory of updateable functions, defined over decideable domain *)
Definition upd {A} `{EqDec A} (B : Type) (f : A -> B) (a : A) (b : B) : A -> B :=
  fun a' => if eq_dec a a' then b else f a'.
Implicit Arguments upd [A H B].

Lemma upd_eq {A} `{EqDec A} : forall B (f : A -> B) a b, 
  upd f a b a = b.
Proof with auto.
  intros.
  unfold upd.
  case (eq_dec a a)...
  intro.
  destruct n...
Qed.
Implicit Arguments upd_eq [A H B].

Lemma upd_eq' {A} `{EqDec A} : forall B (f : A -> B) a b a',
  a = a' ->
  upd f a b a' = b.
Proof.
  intros. subst a'. apply upd_eq.
Qed.
Implicit Arguments upd_eq' [A H B].

Lemma upd_neq {A} `{EqDec A} : forall B (f : A -> B) a b a',
  a <> a' ->
  upd f a b a' = f a'.
Proof with auto.
  intros.
  unfold upd.
  case (eq_dec a a')...
  intros.
  subst a'.
  destruct H0...
Qed.
Implicit Arguments upd_neq [A H B].

Instance nat_eq_dec: EqDec nat.
Proof.
  repeat intro.
 destruct (lt_eq_lt_dec a a') as [[?|?]| ?]; auto;
  right; intro; subst; eapply lt_irrefl; eauto.
Defined.

Instance EqDec_prod (A: Type) (EA: EqDec A) (B: Type) (EB: EqDec B) : EqDec (A*B).
Proof.
 hnf. decide equality; try apply eq_dec.
Defined.

Instance EqDec_list (A: Type) (EA: EqDec A) : EqDec (list A).
Proof.
 hnf. apply list_eq_dec; intros; apply EA.
Defined.
