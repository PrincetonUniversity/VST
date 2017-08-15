Module FOO1.

Parameter P: (Type -> Type) -> Prop.

Record functor: Type := {
  F: Type -> Type;
  FF: P F
}.

Definition fsig (I: Type) (f: I -> functor): functor.
Admitted.

Definition fooo := fsig functor (fun A => A).

End FOO1.


Module FOO2.

Require Import VST.msl.base.

Set Implicit Arguments.

Record functorFacts (PS : Type -> Type)
 (fmap : forall A B (f1 : A -> B) (f2 : B -> A), PS A -> PS B) : Prop :=
FunctorFacts {
  ff_id : forall A, fmap _ _ (id A) (id A) = id (PS A);
  ff_comp : forall A B C (f1 : B -> C) (f2 : C -> B) (g1 : A -> B)
(g2 : B -> A), fmap _ _ f1 f2 oo fmap _ _ g1 g2 = fmap _ _ (f1 oo g1) (g2 oo f2)
}.

Record functor : Type := Functor {
  _functor: Type -> Type;
  fmap : forall A B (f1 : A -> B) (f2 : B -> A), _functor A -> _functor B;
  functor_facts : functorFacts _functor fmap
}.

Coercion _functor: functor >-> Funclass.

Lemma fmap_id {F: functor} : forall A, fmap F (id A) (id A) = id (F A).
Proof. intros. destruct F as [F FM [? ?]]; simpl. apply ff_id0. Qed.

Lemma fmap_comp {F: functor} : forall A B C (f1 : B -> C) (f2: C -> B)
(g1 : A -> B) (g2: B -> A),
  fmap F f1 f2 oo fmap F g1 g2 = fmap F (f1 oo g1) (g2 oo f2).
Proof. intros. destruct F as [F FM [? ?]]; simpl. apply ff_comp0. Qed.

Lemma fmap_app {F: functor} : forall A B C (f1 : B -> C) (f2: C -> B)
(g1 : A -> B) (g2: B -> A) x,
  fmap F f1 f2 (fmap F g1 g2 x) = fmap F (f1 oo g1) (g2 oo f2) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

Definition fsig {I: Type} (F: I -> functor): functor.
  refine (@Functor
   (fun T => @sigT I (fun i => F i T))
   (fun _ _ f g x => match x with existT _ i x0 => existT _ i (fmap (F i) f g x0) end) _).
  constructor; intros; simpl.
  + extensionality p; destruct p as [i a]; simpl.
    rewrite !fmap_id; auto.
  + extensionality p; destruct p as [i a]; simpl.
    unfold compose at 1. rewrite !fmap_app; auto.
Defined.

Record fake_functor : Type := fake_Functor {
  fake__functor: Type -> Type;
  fake_fmap : forall A B (f1 : A -> B) (f2 : B -> A), fake__functor A -> fake__functor B;
  fake_functor_facts : functorFacts fake__functor fake_fmap
}.

Definition super_fsig : functor.
  refine (@Functor
   (fun T => @sigT fake_functor (fun F => fake__functor F T))
   (fun _ _ f g x => match x with existT _ F x0 => existT _ F (fake_fmap F f g x0) end) _).
  constructor; intros; simpl.
  + extensionality p; destruct p as [F a]; simpl.
    rewrite (ff_id (fake_functor_facts F)); auto.
  + extensionality p; destruct p as [F a]; simpl.
    unfold compose at 1. rewrite <- (ff_comp (fake_functor_facts F)); auto.
Defined.

Parameter f: functor.
Parameter A: Type.
Parameter x: f A.

Check (existT (fun F => fake__functor F A)
  (@fake_Functor (_functor f) _ (functor_facts f)) x).

Notation "'SUPER_FSIG' f A x" := (existT (fun F => fake__functor F A)
  (fake_Functor (functor_facts f)) x) (at level 50).


Definition foo: functor := @fsig functor (fun A => A).

