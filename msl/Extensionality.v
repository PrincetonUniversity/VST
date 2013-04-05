Require Export msl.Axioms.

(*** NO AXIOMS AFTER THIS POINT ******************)

Require Import EqdepFacts.

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
  unfold UIP_refl_.
  intros.
  apply proof_irr.
Qed.
End EqdepElim.

Module EqdepTh := EqdepTheory EqdepElim.
Export EqdepTh.

(* Generalize the extensionality tactic from the Coq library. *)
Tactic Notation "extensionality" := 
 let x := fresh "x" in extensionality x.

Tactic Notation "extensionality" ident(x) ident(y) := 
    extensionality x; extensionality y.

Tactic Notation "extensionality" ident(x) ident(y) ident(z):= 
    extensionality x; extensionality y z.

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
