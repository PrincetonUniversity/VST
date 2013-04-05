(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(** This library reexports portions of the Coq standard libraries used
    throughtout the proof.  It also defines some convenience tactics.
 *)
Add LoadPath "..".
Require Export msl.Extensionality.
Require Export List.
Require Export Bool.
Require Export Omega.
Require Export Relations.


Definition compose (A B C:Type) (g:B -> C) (f:A -> B) := fun x => g (f x).
Implicit Arguments compose [A B C].
Infix "oo" := compose (at level 54, right associativity).

Lemma compose_assoc (A B C D:Type) (h:C->D) (g:B->C) (f:A->B) :
  (h oo g) oo f = h oo g oo f.
Proof.
  intros; apply extensionality; intro x; unfold compose; auto.
Qed.

Definition id (A:Type) := fun x:A => x.

Lemma id_unit1 : forall A B (f:A->B), f oo id A = f.
Proof.
  intros; apply extensionality; intro x; auto.
Qed.

Lemma id_unit2 : forall A B (f:A->B), id B oo f = f.
Proof.
  intros; apply extensionality; intro x; auto.
Qed.

Record bijection (A B:Type) : Type := Bijection {
  bij_f: A -> B;
  bij_g: B -> A;
  bij_fg: forall x, bij_f (bij_g x) = x;
  bij_gf: forall x, bij_g (bij_f x) = x
}.

Lemma bij_f_inj {A} {B} (bij: bijection A B): 
     forall x y, bij_f _ _ bij x = bij_f _ _ bij y -> x=y.
Proof.
intros. rewrite <- (bij_gf _ _ bij x). rewrite <- (bij_gf _ _ bij y).
 rewrite H; auto.
Qed.

Lemma bij_g_inj {A} {B} (bij: bijection A B): 
     forall x y, bij_g _ _ bij x = bij_g _ _ bij y -> x=y.
Proof.
intros. rewrite <- (bij_fg _ _ bij x). rewrite <- (bij_fg _ _ bij y).
 rewrite H; auto.
Qed.


(** Perform inversion on a hypothesis, removing it from the context, and
    perform substitutions
  *)
Tactic Notation "inv" hyp(H) := inversion H; clear H; subst.

Ltac detach H :=
  match goal with [ H : (?X -> ?Y) |- _ ] =>
    cut Y; [ clear H; intro H | apply H; clear H ]
  end.

(** Specialize a hypothesis with respect to specific terms or proofs. *)
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.

Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 

Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

 Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).

(* Some further tactics, from Barrier Project *)

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
  (generalize (H a b c d e f); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) :=
  (generalize (H a b c d e f g); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) :=
  (generalize (H a b c d e f g h); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) :=
  (generalize (H a b c d e f g h i); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) constr(o) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) constr(o) constr(p) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "disc" := (try discriminate).

Tactic Notation "contr" := (try contradiction).

Tactic Notation "congr" := (try congruence).

Tactic Notation  "icase" constr(v) := (destruct v; disc; contr; auto).

Tactic Notation "omegac" := (elimtype False; omega).

Tactic Notation "copy" hyp(H) := (generalize H; intro).
