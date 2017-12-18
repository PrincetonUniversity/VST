Require Import Coq.Setoids.Setoid.
Require Import VST.msl.Extensionality.

(******************************************

Copied From Coq.Logic.JMeq.

No longer involving JMeq_eq, which is potentially inconsistenty with homotopy
type theory.

TODO: let reflexivity, symmetry and transitivity work again.

******************************************)

Definition JMeq {A:Type} (x:A) {B:Type} (y: B): Prop :=
  {H: @eq Type A B | @eq_rect Type A (fun T: Type => T) x B H = y}.

Lemma JMeq_refl: forall {A: Type} (x: A), JMeq x x.
Proof.
  intros.
  exists eq_refl.
  rewrite <- eq_rect_eq.
  auto.
Qed.
Hint Resolve JMeq_refl.

Lemma JMeq_sym : forall {A: Type} {B:Type} {x:A} {y:B}, JMeq x y -> JMeq y x.
Proof.
  intros.
  destruct H as [?H ?H].
  exists (eq_sym H).
  rewrite <- H0.
  destruct H.
  simpl.
  apply eq_refl.
Qed.
Hint Immediate JMeq_sym.

Lemma JMeq_trans :
 forall {A: Type} {B: Type} {C:Type} {x:A} {y:B} {z:C}, JMeq x y -> JMeq y z -> JMeq x z.
Proof.
  intros.
  destruct H as [?H ?H], H0 as [?H ?H].
  exists (eq_trans H H0).
  destruct H, H0.
  rewrite <- H2, <- H1.
  reflexivity.
Qed.

Lemma JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.
Proof.
  intros.
  destruct H.
  rewrite <- eq_rect_eq in e.
  exact e.
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
 forall (A:Type) (B:Type) (x:A) (y:B), JMeq x y -> eq_dep Type (fun X:Type => X) A x B y.
Proof.
destruct 1.
subst.
rewrite <- eq_rect_eq.
apply eq_dep_intro.
Qed.

Lemma eq_dep_id_JMeq :
 forall (A: Type) (B:Type) (x:A) (y:B), eq_dep Type (fun X:Type => X) A x B y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl.
Qed.

(** [eq_dep U P p x q y] is strictly finer than [JMeq (P p) x (P q) y] *)

Lemma eq_dep_JMeq :
 forall (U: Type) (P: U -> Type) p x q y, eq_dep U P p x q y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl.
Qed.

Lemma eq_dep_strictly_stronger_JMeq :
 exists (U: Type) (P: U -> Type) p q x y, JMeq x y /\ ~ eq_dep U P p x q y.
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
  forall (U:Type) (P:U->Prop) p q (x:P p) (y:P q),
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

Lemma eq_rect_JMeq: forall (A:Type) (x y: A) (F: A -> Type) (v: F x) (H: x = y), JMeq (eq_rect x F v y H) v.
Proof.
  intros.
  subst.
  rewrite <- eq_rect_eq.
  apply JMeq_refl.
Qed.

Lemma eq_rect_r_JMeq: forall (A:Type) (x y: A) (F: A -> Type) (v: F x) (H: y = x), JMeq (eq_rect_r F v H) v.
Proof.
  intros.
  subst.
  unfold eq_rect_r; rewrite <- eq_rect_eq.
  apply JMeq_refl.
Qed.

Lemma JMeq_sumtype_ll: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: A) (y: C), @eq Type A C -> @eq Type B D -> 
  (@JMeq (A + B) (inl x) (C + D) (inl y)) ->
  JMeq x y.
Proof.
  intros.
  exists H.
  destruct H1 as [?H ?H].
  revert H1 H2.
  destruct H, H0.
  intros.
  rewrite <- eq_rect_eq in H2.
  inversion H2.
  apply eq_refl.
Qed.

Lemma JMeq_sumtype_rr: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: B) (y: D), @eq Type A C -> @eq Type B D -> 
  (@JMeq (A + B) (inr x) (C + D) (inr y)) ->
  JMeq x y.
Proof.
  intros.
  exists H0.
  destruct H1 as [?H ?H].
  revert H1 H2.
  destruct H, H0.
  intros.
  rewrite <- eq_rect_eq in H2.
  inversion H2.
  apply eq_refl.
Qed.

Lemma JMeq_sumtype_lr: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: A) (y: D), @eq Type A C -> @eq Type B D -> ~ (@JMeq (A + B) (inl x) (C + D) (inr y)).
Proof.
  unfold not.
  intros.
  destruct H1 as [?H ?H].
  revert H1 H2.
  destruct H, H0.
  intros.
  rewrite <- eq_rect_eq in H2.
  inversion H2.
Qed.

Lemma JMeq_sumtype_rl: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: B) (y: C), @eq Type A C -> @eq Type B D -> ~ (@JMeq (A + B) (inr x) (C + D) (inl y)).
Proof.
  unfold not.
  intros.
  destruct H1 as [?H ?H].
  revert H1 H2.
  destruct H, H0.
  intros.
  rewrite <- eq_rect_eq in H2.
  inversion H2.
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

Lemma JMeq_inl: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: A) (y: C), @eq Type B D -> JMeq x y -> @JMeq (A + B) (inl x) (C + D) (inl y).
Proof.
  intros.
  destruct H0 as [?H ?H].
  pose (f_equal2 := 
          fun (A1 : Type) (A2 : Type) (B : Type) (f : forall (_ : A1) (_ : A2), B) 
            (x1 y1 : A1) (x2 y2 : A2) (H : @eq A1 x1 y1) =>
          match H in (eq _ y) return (forall _ : @eq A2 x2 y2, @eq B (f x1 x2) (f y y2)) with
          | eq_refl => fun H0 : @eq A2 x2 y2 => match H0 in (eq _ y) return (@eq B (f x1 x2) (f x1 y)) with
                                                | eq_refl => @eq_refl B (f x1 x2)
                                                end
          end).
  exists (f_equal2 _ _ _ sum _ _ _ _ H0 H).
  destruct H, H0.
  rewrite <- H1.
  unfold f_equal2.
  simpl.
  apply eq_refl.
Qed.

Lemma JMeq_inr: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: B) (y: D), @eq Type A C -> JMeq x y -> @JMeq (A + B) (inr x) (C + D) (inr y).
Proof.
  intros.
  destruct H0 as [?H ?H].
  pose (f_equal2 := 
          fun (A1 : Type) (A2 : Type) (B : Type) (f : forall (_ : A1) (_ : A2), B) 
            (x1 y1 : A1) (x2 y2 : A2) (H : @eq A1 x1 y1) =>
          match H in (eq _ y) return (forall _ : @eq A2 x2 y2, @eq B (f x1 x2) (f y y2)) with
          | eq_refl => fun H0 : @eq A2 x2 y2 => match H0 in (eq _ y) return (@eq B (f x1 x2) (f x1 y)) with
                                                | eq_refl => @eq_refl B (f x1 x2)
                                                end
          end).
  exists (f_equal2 _ _ _ sum _ _ _ _ H H0).
  destruct H, H0.
  rewrite <- H1.
  unfold f_equal2.
  simpl.
  apply eq_refl.
Qed.

Lemma JMeq_fst: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: A*B) (y: C*D), @eq Type A C -> @eq Type B D -> JMeq x y -> JMeq (fst x) (fst y).
Proof.
  intros.
  exists H.
  destruct H1 as [?H ?H].
  revert H1 H2.
  destruct H, H0.
  intros.
  rewrite <- eq_rect_eq in H2.
  rewrite H2.
  apply eq_refl.
Qed.

Lemma JMeq_snd: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: A*B) (y: C*D), @eq Type A C -> @eq Type B D -> JMeq x y -> JMeq (snd x) (snd y).
Proof.
  intros.
  exists H0.
  destruct H1 as [?H ?H].
  revert H1 H2.
  destruct H, H0.
  intros.
  rewrite <- eq_rect_eq in H2.
  rewrite H2.
  apply eq_refl.
Qed.

Lemma JMeq_pair: forall (A: Type) (B: Type) (C: Type) (D: Type) (a: A) (b: B) (c: C) (d: D), JMeq a b -> JMeq c d -> JMeq (a, c) (b, d).
Proof.
  intros.
  destruct H as [?H ?H], H0 as [?H ?H].
  pose (f_equal2 := 
          fun (A1 : Type) (A2 : Type) (B : Type) (f : forall (_ : A1) (_ : A2), B) 
            (x1 y1 : A1) (x2 y2 : A2) (H : @eq A1 x1 y1) =>
          match H in (eq _ y) return (forall _ : @eq A2 x2 y2, @eq B (f x1 x2) (f y y2)) with
          | eq_refl => fun H0 : @eq A2 x2 y2 => match H0 in (eq _ y) return (@eq B (f x1 x2) (f x1 y)) with
                                                | eq_refl => @eq_refl B (f x1 x2)
                                                end
          end).
  exists (f_equal2 _ _ _ prod _ _ _ _ H H0).
  destruct H, H0.
  rewrite <- H1, <- H2.
  unfold f_equal2.
  simpl.
  apply eq_refl.
Qed.

Lemma eq_rect_r_eq_rect_r_eq_sym: forall {T} {A B: T} F x (H: A = B),
  eq_rect_r F (eq_rect_r F x H) (eq_sym H) = x.
Proof.
  intros.
  destruct H.
  reflexivity.
Qed.

Lemma eq_rect_r_eq_rect_r_eq_sym': forall {T} {A B: T} F x (H: B = A),
  eq_rect_r F (eq_rect_r F x (eq_sym H)) H = x.
Proof.
  intros.
  destruct H.
  reflexivity.
Qed.

Lemma JMeq_func: forall (A: Type) (B: Type) (C: Type) (D: Type) (f: A -> B) (g: C -> D) x y,
  @eq Type B D ->
  JMeq x y -> JMeq f g -> JMeq (f x) (g y).
Proof.
  intros.
  exists H.
  destruct H0 as [?H ?H], H1 as [?H ?H].
  destruct H, H0.
  rewrite <- eq_rect_eq in H3.
  rewrite H3, <- H2.
  apply eq_refl.
Qed.

Lemma eq_JMeq: forall A (x y: A), x=y -> JMeq x y.
Proof. intros. subst. apply JMeq_refl.
Qed.

Lemma list_func_JMeq: forall {A: Type} {B: Type} {C: Type} (a: list A) (b: list B) (f: forall X, list X -> C), @eq Type A B -> JMeq a b -> f A a = f B b.
Proof.
  intros.
  destruct H0 as [? ?].
  destruct H.
  rewrite <- eq_rect_eq in e.
  rewrite e.
  auto.
Qed.

Lemma list_func_JMeq': forall {A: Type} {B: Type} (a: list A) (b: list B) (a': A) (b': B) (f: forall X, list X -> X -> X), JMeq a b -> JMeq a' b' -> JMeq (f A a a') (f B b b').
Proof.
  intros.
  destruct H as [?H ?H], H0 as [?H ?H].
  exists H0.
  rewrite <- H1, <- H2.
  destruct H0.
  simpl.
  rewrite <- eq_rect_eq.
  apply eq_refl.
Qed.

Lemma JMeq_sigT: forall {A: Type} {B: Type} (a: A), @eq Type A B -> {b: B | JMeq a b}.
Proof.
  intros.
  unfold JMeq.
  destruct H.
  exists a.
  apply JMeq_refl.
Qed.

Arguments JMeq_eq {A} {x y} _.
