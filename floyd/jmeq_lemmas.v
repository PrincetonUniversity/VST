Require Import Coq.Setoids.Setoid.
Require Import VST.msl.Extensionality.

(******************************************

Copied From Coq.Logic.JMeq.

No longer involving JMeq_eq, which is potentially inconsistenty with homotopy
type theory.

TODO: let reflexivity, symmetry and transitivity work again.

******************************************)

Definition JMeq {A:Type} (x:A) {B:Type} (y: B): Prop :=
  {H: A = B | eq_rect A (fun T: Type => T) x B H = y}.

Lemma JMeq_refl: forall {A: Type} (x: A), JMeq x x.
Proof.
  intros.
  exists eq_refl.
  rewrite <- eq_rect_eq.
  auto.
Qed.
Hint Resolve JMeq_refl.

Lemma JMeq_sym : forall {A B:Type} {x:A} {y:B}, JMeq x y -> JMeq y x.
Proof.
destruct 1; trivial.
subst.
trivial.
Qed.
Hint Immediate JMeq_sym.

Lemma JMeq_trans :
 forall {A B C:Type} {x:A} {y:B} {z:C}, JMeq x y -> JMeq y z -> JMeq x z.
Proof.
destruct 2; trivial.
subst.
auto.
Qed.

Lemma JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.
Proof.
  intros.
  destruct H.
  rewrite <- eq_rect_eq in e.
  auto.
Qed.

Lemma JMeq_ind : forall (A:Type) (x:A) (P:A -> Prop),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'.
inversion H'.
subst.
 case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rec : forall (A:Type) (x:A) (P:A -> Set),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rect : forall (A:Type) (x:A) (P:A->Type),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_ind_r : forall (A:Type) (x:A) (P:A -> Prop),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rec_r : forall (A:Type) (x:A) (P:A -> Set),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rect_r : forall (A:Type) (x:A) (P:A -> Type),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_congr :
 forall (A:Type) (x:A) (B:Type) (f:A->B) (y:A), JMeq x y -> f x = f y.
Proof.
intros A x B f y H; case JMeq_eq with (1 := H); trivial.
Qed.

(** [JMeq] is equivalent to [eq_dep Type (fun X => X)] *)

Require Import Coq.Logic.Eqdep.

Lemma JMeq_eq_dep_id :
 forall (A B:Type) (x:A) (y:B), JMeq x y -> eq_dep Type (fun X => X) A x B y.
Proof.
destruct 1.
subst.
rewrite <- eq_rect_eq.
apply eq_dep_intro.
Qed.

Lemma eq_dep_id_JMeq :
 forall (A B:Type) (x:A) (y:B), eq_dep Type (fun X => X) A x B y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl.
Qed.

(** [eq_dep U P p x q y] is strictly finer than [JMeq (P p) x (P q) y] *)

Lemma eq_dep_JMeq :
 forall U P p x q y, eq_dep U P p x q y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl.
Qed.

Lemma eq_dep_strictly_stronger_JMeq :
 exists U P p q x y, JMeq x y /\ ~ eq_dep U P p x q y.
Proof.
exists bool. exists (fun _ => True). exists true. exists false.
exists I. exists I.
split.
trivial.
intro H.
assert (true=false) by (destruct H; reflexivity).
discriminate.
Qed.

(** However, when the dependencies are equal, [JMeq (P p) x (P q) y]
    is as strong as [eq_dep U P p x q y] (this uses [JMeq_eq]) *)

Lemma JMeq_eq_dep :
  forall U (P:U->Prop) p q (x:P p) (y:P q),
  p = q -> JMeq x y -> eq_dep U P p x q y.
Proof.
intros.
destruct H.
apply JMeq_eq in H0 as ->.
reflexivity.
Qed.

(* Compatibility *)
Notation sym_JMeq := JMeq_sym (only parsing).
Notation trans_JMeq := JMeq_trans (only parsing).

(******************************************

The following is the original floyd/jmeq_lemmas.v

******************************************)

Lemma eq_rect_JMeq: forall (A:Type) (x y: A) F (v: F x) (H: x = y), JMeq (eq_rect x F v y H) v.
Proof.
  intros.
  subst.
  rewrite <- eq_rect_eq.
  apply JMeq_refl.
Qed.

Lemma eq_rect_r_JMeq: forall (A:Type) (x y: A) F (v: F x) (H: y = x), JMeq (eq_rect_r F v H) v.
Proof.
  intros.
  subst.
  unfold eq_rect_r; rewrite <- eq_rect_eq.
  apply JMeq_refl.
Qed.

Lemma JMeq_sumtype_ll: forall A B C D x y, A = C -> B = D ->
  (@JMeq (A + B) (inl x) (C + D) (inl y)) ->
  JMeq x y.
Proof.
  unfold not.
  intros.
  subst.
  inversion H1.
  apply JMeq_eq in H1.
  inversion H1.
  apply JMeq_refl.
Qed.

Lemma JMeq_sumtype_rr: forall A B C D x y, A = C -> B = D ->
  (@JMeq (A + B) (inr x) (C + D) (inr y)) ->
  JMeq x y.
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
  apply JMeq_refl.
Qed.

Lemma JMeq_sumtype_lr: forall A B C D x y, A = C -> B = D -> ~ (@JMeq (A + B) (inl x) (C + D) (inr y)).
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
Qed.

Lemma JMeq_sumtype_rl: forall A B C D x y, A = C -> B = D -> ~ (@JMeq (A + B) (inr x) (C + D) (inl y)).
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
Qed.

Ltac solve_JMeq_sumtype H :=
  match type of H with
  | JMeq ?x ?y =>
    destruct x; destruct y;
     [apply JMeq_sumtype_ll in H; auto
     |apply JMeq_sumtype_lr in H; auto; inversion H
     |apply JMeq_sumtype_rl in H; auto; inversion H
     |apply JMeq_sumtype_rr in H; auto]
  end.

Lemma JMeq_inl: forall A B C D (x: A) (y: C), A = C -> B = D -> JMeq x y -> @JMeq (A + B) (inl x) (C + D) (inl y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  apply JMeq_refl.
Qed.

Lemma JMeq_inr: forall A B C D (x: B) (y: D), A = C -> B = D -> JMeq x y -> @JMeq (A + B) (inr x) (C + D) (inr y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  apply JMeq_refl.
Qed.

Lemma JMeq_fst: forall A B C D (x: A*B) (y: C*D), A = C -> B = D -> JMeq x y -> JMeq (fst x) (fst y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  apply JMeq_refl.
Qed.

Lemma JMeq_snd: forall A B C D (x: A*B) (y: C*D), A = C -> B = D -> JMeq x y -> JMeq (snd x) (snd y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  apply JMeq_refl.
Qed.

Lemma JMeq_pair: forall A B C D (a: A) (b: B) (c: C) (d: D), JMeq a b -> JMeq c d -> JMeq (a, c) (b, d).
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  apply JMeq_refl.
Qed.

Lemma eq_rect_r_eq_rect_r_eq_sym: forall {T} {A B: T} F x (H: A = B),
  eq_rect_r F (eq_rect_r F x H) (eq_sym H) = x.
Proof.
  intros.
  apply JMeq_eq.
  apply JMeq_sym.
  apply @JMeq_sym; eapply JMeq_trans.
  + apply eq_rect_r_JMeq.
  + apply eq_rect_r_JMeq.
Qed.

Lemma eq_rect_r_eq_rect_r_eq_sym': forall {T} {A B: T} F x (H: B = A),
  eq_rect_r F (eq_rect_r F x (eq_sym H)) H = x.
Proof.
  intros.
  apply JMeq_eq.
  apply JMeq_sym.
  apply @JMeq_sym; eapply JMeq_trans.
  + apply eq_rect_r_JMeq.
  + apply eq_rect_r_JMeq.
Qed.

Lemma JMeq_func: forall A B C D (f: A -> B) (g: C -> D) x y,
  A = C -> B = D ->
  JMeq x y -> JMeq f g -> JMeq (f x) (g y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  apply JMeq_eq in H2.
  subst.
  apply JMeq_refl.
Qed.

Lemma eq_JMeq: forall A (x y: A), x=y -> JMeq x y.
Proof. intros. subst. apply JMeq_refl.
Qed.

Lemma list_func_JMeq: forall {A B C} (a: list A) (b: list B) (f: forall X, list X -> C), A = B -> JMeq a b -> f A a = f B b.
Proof.
  intros; subst.
  apply JMeq_eq in H0.
  subst.
  auto.
Qed.

Lemma JMeq_sigT: forall {A B} (a: A), A = B -> {b: B | JMeq a b}.
Proof.
  intros.
  subst.
  exists a.
  apply JMeq_refl.
Qed.

Arguments JMeq_eq {A} {x y} _.
