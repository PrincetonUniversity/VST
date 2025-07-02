Require Export VST.msl.Axioms.

(* NO AXIOMS AFTER THIS POINT *)

Require Import Stdlib.Logic.EqdepFacts.

(* From EqdepTh we obtain inj_pair and inj_pairT2 without
   use of excluded middle:
 *)
Module EqdepElim: EqdepElimination.
Lemma eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.
Proof.
  intros.
  apply Streicher_K__eq_rect_eq.
  apply UIP_refl__Streicher_K.
  hnf; intros; hnf; intros.
  apply proof_irr.
Qed.
End EqdepElim.

Module EqdepTh := EqdepTheory EqdepElim.
Export EqdepTh.

(* Generalize the extensionality tactic from the Coq library. *)
Tactic Notation "extensionality" :=
 let x := fresh "x" in extensionality x.

Tactic Notation "extensionality" ident(x0) ident(x1) :=
  extensionality x0; extensionality x1.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) :=
  extensionality x0; extensionality x1; extensionality x2.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3)
  ident(x4) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3;
  extensionality x4.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3)
  ident(x4) ident(x5) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3;
  extensionality x4; extensionality x5.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3)
  ident(x4) ident(x5) ident(x6) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3;
  extensionality x4; extensionality x5; extensionality x6.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3)
  ident(x4) ident(x5) ident(x6) ident(x7) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3;
  extensionality x4; extensionality x5; extensionality x6; extensionality x7.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3)
  ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3;
  extensionality x4; extensionality x5; extensionality x6; extensionality x7;
  extensionality x8.

Tactic Notation "extensionality" ident(x0) ident(x1) ident(x2) ident(x3)
  ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) :=
  extensionality x0; extensionality x1; extensionality x2; extensionality x3;
  extensionality x4; extensionality x5; extensionality x6; extensionality x7;
  extensionality x8; extensionality x9.

Lemma imp_ext: forall (A A' B B' : Prop), (A=A') -> (A -> (B=B')) -> ((A->B)=(A'->B')).
Proof.
intros.
subst A'.
apply prop_ext; split; intros; auto.
rewrite <- H0; auto. rewrite H0; auto.
Qed.

Lemma exists_ext: forall (A: Type) F G, (forall x: A, F x = G x) -> (Logic.ex F = Logic.ex G).
Proof.
intros.
apply prop_ext; split; intro; destruct H0; exists x.
rewrite <- H; auto.
rewrite H; auto.
Qed.

Lemma and_ext: forall A B C D, A=B -> C=D -> (A /\ C) = (B /\ D).
Proof.
intros.
rewrite H; rewrite H0; auto.
Qed.

Lemma and_ext': forall (A: Prop) B C D, A=B -> (A -> (C=D)) -> (A /\ C) = (B /\ D).
Proof.
intros.
subst B.
apply prop_ext.
intuition; subst; auto.
Qed.

Lemma or_ext: forall A B C D, A=B -> C=D -> (A \/ C) = (B \/ D).
Proof.
intros.
rewrite H; rewrite H0; auto.
Qed.

Lemma forall_ext: forall (A: Type) (F: A -> Prop) G, (forall x:A, F x = G x) -> (forall x, F x) = (forall x, G x).
Proof.
intros.
apply prop_ext. split; intros. rewrite <- H; auto. rewrite H; auto.
Qed.

Lemma existT_ext:
  forall (A: Type) (P: A -> Prop) (x y: A) (Hx: P x) (Hy: P y),
     x = y -> existT _ x Hx = existT _ y Hy.
Proof.
intros.
subst.
rewrite (proof_irr Hx Hy); auto.
Qed.

Lemma exist_ext:
  forall (A: Type) (P: A -> Prop) (x y: A) (Hx: P x) (Hy: P y),
     x = y -> exist _ x Hx = exist _ y Hy.
Proof.
intros.
subst.
rewrite (proof_irr Hx Hy); auto.
Qed.

Ltac f_equal :=
  (match goal with
     (* doing it this way can sometimes induce fewer universe constraints
        than Prelude.f_equal produces *)
   | |- exist _ _ _ = exist _ _ _ => apply exist_ext
   | |- existT _ _ _ = existT _ _ _ => apply existT_ext
  end;
   try reflexivity; try congruence)
   || Corelib.Init.Prelude.f_equal.

Lemma exist_ext' : forall A F (x y:@sig A F),
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x; destruct y; simpl in *.
  subst x0.
  replace f0 with f by apply proof_irr; auto.
Qed.
