(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.

Set Implicit Arguments.

Module CovariantFunctor.

Record functorFacts (PS : Type -> Type)
  (fmap : forall A B (f : A -> B), PS A -> PS B) : Type :=
FunctorFacts {
  ff_id : forall A, fmap _ _ (id A) = id (PS A);
  ff_comp : forall A B C (f : B -> C) (g : A -> B),
fmap _ _ f oo fmap _ _ g = fmap _ _ (f oo g)
}.

Record functor : Type := Functor {
  _functor: Type -> Type;
  fmap : forall A B (f : A -> B), _functor A -> _functor B;
  functor_facts : functorFacts _functor fmap
}.

End CovariantFunctor.

Module ContraVariantFunctor.

Record functorFacts (PS : Type -> Type)
  (fmap : forall A B (f : B -> A), PS A -> PS B) : Type :=
FunctorFacts {
  ff_id : forall A, fmap _ _ (id A) = id (PS A);
  ff_comp : forall A B C (f : C -> B) (g : B -> A),
fmap _ _ f oo fmap _ _ g = fmap _ _ (g oo f)
}.

Record functor : Type := Functor {
  _functor: Type -> Type;
  fmap : forall A B (f : B -> A), _functor A -> _functor B;
  functor_facts : functorFacts _functor fmap
}.

End ContraVariantFunctor.

Module MixVariantFunctor.

Record functorFacts (PS : Type -> Type)
 (fmap : forall A B (f1 : A -> B) (f2 : B -> A), PS A -> PS B) : Type :=
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

End MixVariantFunctor.

Module CovariantBiFunctor.

Record functorFacts (PS : Type -> Type -> Type)
 (fmap : forall A1 B1 A2 B2 (f1 : A1 -> B1) (f2 : A2 -> B2),
    PS A1 A2 -> PS B1 B2) : Type :=
FunctorFacts {
  ff_id : forall A1 A2, fmap _ _ _ _ (id A1) (id A2) = id (PS A1 A2);
  ff_comp : forall A1 A2 B1 B2 C1 C2 (f1 : B1 -> C1) (f2 : B2 -> C2)
(g1 : A1 -> B1) (g2 : A2 -> B2),
  fmap _ _ _ _ f1 f2 oo fmap _ _ _ _ g1 g2 = fmap _ _ _ _ (f1 oo g1) (f2 oo g2)
}.

Record functor : Type := Functor {
  _functor: Type -> Type -> Type;
  fmap : forall A1 B1 A2 B2 (f1 : A1 -> B1) (f2 : A2 -> B2),
    _functor A1 A2 -> _functor B1 B2;
  functor_facts : functorFacts _functor fmap
}.

End CovariantBiFunctor.

Module CoContraVariantBiFunctor.

Record functorFacts (PS : Type -> Type -> Type)
 (fmap : forall A1 B1 A2 B2 (f1 : A1 -> B1) (f2 : B2 -> A2),
    PS A1 A2 -> PS B1 B2) : Type :=
FunctorFacts {
  ff_id : forall A1 A2, fmap _ _ _ _ (id A1) (id A2) = id (PS A1 A2);
  ff_comp : forall A1 A2 B1 B2 C1 C2 (f1 : B1 -> C1) (f2 : C2 -> B2)
(g1 : A1 -> B1) (g2 : B2 -> A2),
  fmap _ _ _ _ f1 f2 oo fmap _ _ _ _ g1 g2 = fmap _ _ _ _ (f1 oo g1) (g2 oo f2)
}.

Record functor : Type := Functor {
  _functor: Type -> Type -> Type;
  fmap : forall A1 B1 A2 B2 (f1 : A1 -> B1) (f2 : B2 -> A2),
    _functor A1 A2 -> _functor B1 B2;
  functor_facts : functorFacts _functor fmap
}.

End CoContraVariantBiFunctor.

Coercion CovariantFunctor._functor:
  CovariantFunctor.functor >-> Funclass.
Coercion ContraVariantFunctor._functor:
  ContraVariantFunctor.functor >-> Funclass.
Coercion MixVariantFunctor._functor:
  MixVariantFunctor.functor >-> Funclass.
Coercion CovariantBiFunctor._functor:
  CovariantBiFunctor.functor >-> Funclass.
Coercion CoContraVariantBiFunctor._functor:
  CoContraVariantBiFunctor.functor >-> Funclass.

Module CovariantFunctorLemmas.

Import CovariantFunctor.

Lemma fmap_id {F: functor} : forall A, fmap F (id A) = id (F A).
Proof. intros. destruct F as [F FM [ff_id ?]]; simpl. apply ff_id. Qed.

Lemma fmap_comp {F: functor} : forall A B C (f : B -> C) (g : A -> B),
  fmap F f oo fmap F g = fmap F (f oo g).
Proof. intros. destruct F as [F FM [? ff_comp]]; simpl. apply ff_comp. Qed.

Lemma fmap_app {F: functor} : forall A B C (f : B -> C) (g : A -> B) x,
  fmap F f (fmap F g x) = fmap F (f oo g) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

End CovariantFunctorLemmas.

Module ContraVariantFunctorLemmas.

Import ContraVariantFunctor.

Lemma fmap_id {F: functor} : forall A, fmap F (id A) = id (F A).
Proof. intros. destruct F as [F FM [ff_id ?]]; simpl. apply ff_id. Qed.

Lemma fmap_comp {F: functor} : forall A B C (f : C -> B) (g : B -> A),
  fmap F f oo fmap F g = fmap F (g oo f).
Proof. intros. destruct F as [F FM [? ff_comp]]; simpl. apply ff_comp. Qed.

Lemma fmap_app {F: functor} : forall A B C (f : C -> B) (g : B -> A) x,
  fmap F f (fmap F g x) = fmap F (g oo f) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

End ContraVariantFunctorLemmas.

Module MixVariantFunctorLemmas.

Import MixVariantFunctor.

Lemma fmap_id {F: functor} : forall A, fmap F (id A) (id A) = id (F A).
Proof. intros. destruct F as [F FM [ff_id ?]]; simpl. apply ff_id. Qed.

Lemma fmap_comp {F: functor} : forall A B C (f1 : B -> C) (f2: C -> B)
(g1 : A -> B) (g2: B -> A),
  fmap F f1 f2 oo fmap F g1 g2 = fmap F (f1 oo g1) (g2 oo f2).
Proof. intros. destruct F as [F FM [? ff_comp]]; simpl. apply ff_comp. Qed.

Lemma fmap_app {F: functor} : forall A B C (f1 : B -> C) (f2: C -> B)
(g1 : A -> B) (g2: B -> A) x,
  fmap F f1 f2 (fmap F g1 g2 x) = fmap F (f1 oo g1) (g2 oo f2) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

End MixVariantFunctorLemmas.

Module CovariantBiFunctorLemmas.

Import CovariantBiFunctor.

Lemma fmap_id {F: functor} : forall A1 A2, fmap F (id A1) (id A2) = id (F A1 A2).
Proof. intros. destruct F as [F FM [ff_id ?]]; simpl. apply ff_id. Qed.

Lemma fmap_comp {F: functor} : forall A1 A2 B1 B2 C1 C2 (f1 : B1 -> C1)
(f2: B2 -> C2) (g1 : A1 -> B1) (g2: A2 -> B2),
  fmap F f1 f2 oo fmap F g1 g2 = fmap F (f1 oo g1) (f2 oo g2).
Proof. intros. destruct F as [F FM [? ff_comp]]; simpl. apply ff_comp. Qed.

Lemma fmap_app {F: functor} : forall A1 A2 B1 B2 C1 C2 (f1 : B1 -> C1)
(f2: B2 -> C2) (g1 : A1 -> B1) (g2: A2 -> B2) x,
  fmap F f1 f2 (fmap F g1 g2 x) = fmap F (f1 oo g1) (f2 oo g2) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

End CovariantBiFunctorLemmas.

Module CoContraVariantBiFunctorLemmas.

Import CoContraVariantBiFunctor.

Lemma fmap_id {F: functor} : forall A1 A2, fmap F (id A1) (id A2) = id (F A1 A2).
Proof. intros. destruct F as [F FM [ff_id ?]]; simpl. apply ff_id. Qed.

Lemma fmap_comp {F: functor} : forall A1 A2 B1 B2 C1 C2 (f1 : B1 -> C1)
(f2: C2 -> B2) (g1 : A1 -> B1) (g2: B2 -> A2),
  fmap F f1 f2 oo fmap F g1 g2 = fmap F (f1 oo g1) (g2 oo f2).
Proof. intros. destruct F as [F FM [? ff_comp]]; simpl. apply ff_comp. Qed.

Lemma fmap_app {F: functor} : forall A1 A2 B1 B2 C1 C2 (f1 : B1 -> C1)
(f2: C2 -> B2) (g1 : A1 -> B1) (g2: B2 -> A2) x,
  fmap F f1 f2 (fmap F g1 g2 x) = fmap F (f1 oo g1) (g2 oo f2) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

End CoContraVariantBiFunctorLemmas.

Module GeneralFunctorGenerator.

Lemma CovariantFunctor_MixVariantFunctorFacts (F: CovariantFunctor.functor) :
  MixVariantFunctor.functorFacts (fun T : Type => F T)
  (fun (A B : Type) (f : A -> B) (_ : B -> A) => CovariantFunctor.fmap F f).
Proof.
  constructor; intros; simpl.
  + apply CovariantFunctor.ff_id, CovariantFunctor.functor_facts.
  + apply CovariantFunctor.ff_comp, CovariantFunctor.functor_facts.
Qed.

Definition CovariantFunctor_MixVariantFunctor (F: CovariantFunctor.functor) :=
  MixVariantFunctor.Functor (CovariantFunctor_MixVariantFunctorFacts F).

Lemma ContraVariantFunctor_MixVariantFunctorFacts
  (F: ContraVariantFunctor.functor):
  MixVariantFunctor.functorFacts (fun T : Type => F T)
  (fun (A B : Type) (_ : A -> B) (f : B -> A) => ContraVariantFunctor.fmap F f).
Proof.
  constructor; intros; simpl.
  + apply ContraVariantFunctor.ff_id, ContraVariantFunctor.functor_facts.
  + apply ContraVariantFunctor.ff_comp, ContraVariantFunctor.functor_facts.
Qed.

Definition ContraVariantFunctor_MixVariantFunctor (F: ContraVariantFunctor.functor) :=
  MixVariantFunctor.Functor (ContraVariantFunctor_MixVariantFunctorFacts F).

Lemma CovariantFunctor_CoContraVariantBiFunctorFacts
  (F: CovariantFunctor.functor):
  CoContraVariantBiFunctor.functorFacts (fun T1 T2 : Type => F T1)
  (fun (A B C D : Type) (f : A -> B) (_ : D -> C) => CovariantFunctor.fmap F f).
Proof.
  constructor; intros; simpl.
  + apply CovariantFunctor.ff_id, CovariantFunctor.functor_facts.
  + apply CovariantFunctor.ff_comp, CovariantFunctor.functor_facts.
Qed.

Definition CovariantFunctor_CoContraVariantBiFunctor (F: CovariantFunctor.functor) :=
  CoContraVariantBiFunctor.Functor (CovariantFunctor_CoContraVariantBiFunctorFacts F).

Lemma CoContraVariantBiFunctor_MixVariantFunctorFacts
  (F: CoContraVariantBiFunctor.functor):
  MixVariantFunctor.functorFacts (fun T : Type => F T T)
  (fun (A B : Type) (f : A -> B) (g : B -> A) => CoContraVariantBiFunctor.fmap F f g).
Proof.
  constructor; intros; simpl.
  + apply CoContraVariantBiFunctor.ff_id,
          CoContraVariantBiFunctor.functor_facts.
  + apply CoContraVariantBiFunctor.ff_comp,
          CoContraVariantBiFunctor.functor_facts.
Qed.

Definition CoContraVariantBiFunctor_MixVariantFunctor (F: CoContraVariantBiFunctor.functor) :=
  MixVariantFunctor.Functor (CoContraVariantBiFunctor_MixVariantFunctorFacts F).

Lemma CovariantFunctor_CovariantFunctor_composeFacts
  (F1 F2: CovariantFunctor.functor):
  CovariantFunctor.functorFacts (fun T : Type => F1 (F2 T))
  (fun (A B : Type) (f : A -> B) => CovariantFunctor.fmap F1 (CovariantFunctor.fmap F2 f)).
Proof.
  constructor; intros; simpl.
  + rewrite !CovariantFunctorLemmas.fmap_id; auto.
  + rewrite !CovariantFunctorLemmas.fmap_comp; auto.
Qed.

Definition CovariantFunctor_CovariantFunctor_compose (F1 F2: CovariantFunctor.functor) :=
  CovariantFunctor.Functor (CovariantFunctor_CovariantFunctor_composeFacts F1 F2).

Lemma CovariantFunctor_MixVariantFunctor_composeFacts
  (F1: CovariantFunctor.functor) (F2: MixVariantFunctor.functor):
  MixVariantFunctor.functorFacts (fun T : Type => F1 (F2 T))
  (fun (A B : Type) (f : A -> B) (g : B -> A) =>
   CovariantFunctor.fmap F1 (MixVariantFunctor.fmap F2 f g)).
Proof.
  constructor; intros; simpl.
  + rewrite MixVariantFunctorLemmas.fmap_id, CovariantFunctorLemmas.fmap_id; auto.
  + rewrite !CovariantFunctorLemmas.fmap_comp, MixVariantFunctorLemmas.fmap_comp; auto.
Qed.

Definition CovariantFunctor_MixVariantFunctor_compose (F1: CovariantFunctor.functor) (F2: MixVariantFunctor.functor) :=
  MixVariantFunctor.Functor (CovariantFunctor_MixVariantFunctor_composeFacts F1 F2).

Lemma CovariantBiFunctor_CovariantFunctor_composeFacts
  (F: CovariantBiFunctor.functor)
  (F1 F2: CovariantFunctor.functor):
  CovariantFunctor.functorFacts (fun T : Type => F (F1 T) (F2 T))
    (fun (A B : Type) (f : A -> B) =>
     CovariantBiFunctor.fmap F (CovariantFunctor.fmap F1 f) (CovariantFunctor.fmap F2 f)).
Proof.
  constructor; intros; simpl.
  + rewrite !CovariantFunctorLemmas.fmap_id, CovariantBiFunctorLemmas.fmap_id; auto.
  + rewrite CovariantBiFunctorLemmas.fmap_comp, !CovariantFunctorLemmas.fmap_comp; auto.
Qed.

Definition CovariantBiFunctor_CovariantFunctor_compose
  (F: CovariantBiFunctor.functor)
  (F1 F2: CovariantFunctor.functor) :=
  CovariantFunctor.Functor (CovariantBiFunctor_CovariantFunctor_composeFacts F F1 F2).

Lemma CovariantBiFunctor_MixVariantFunctor_composeFacts
  (F: CovariantBiFunctor.functor)
  (F1 F2: MixVariantFunctor.functor):
  MixVariantFunctor.functorFacts (fun T : Type => F (F1 T) (F2 T))
    (fun (A B : Type) (f : A -> B) (g : B -> A) =>
     CovariantBiFunctor.fmap F (MixVariantFunctor.fmap F1 f g) (MixVariantFunctor.fmap F2 f g)).
Proof.
  constructor; intros; simpl.
  + rewrite !MixVariantFunctorLemmas.fmap_id, CovariantBiFunctorLemmas.fmap_id; auto.
  + rewrite CovariantBiFunctorLemmas.fmap_comp, !MixVariantFunctorLemmas.fmap_comp; auto.
Qed.

Definition CovariantBiFunctor_MixVariantFunctor_compose
  (F: CovariantBiFunctor.functor)
  (F1 F2: MixVariantFunctor.functor):=
  MixVariantFunctor.Functor (CovariantBiFunctor_MixVariantFunctor_composeFacts F F1 F2).

Lemma CoContraVariantBiFunctor_CoContraVariantFunctor_composeFacts
  (F: CoContraVariantBiFunctor.functor)
  (F1: CovariantFunctor.functor)
  (F2: ContraVariantFunctor.functor):
  CovariantFunctor.functorFacts (fun T : Type => F (F1 T) (F2 T))
    (fun (A B : Type) (f : A -> B) =>
     CoContraVariantBiFunctor.fmap F (CovariantFunctor.fmap F1 f)
       (ContraVariantFunctor.fmap F2 f)).
Proof.
  constructor; intros; simpl.
  + rewrite CovariantFunctorLemmas.fmap_id, ContraVariantFunctorLemmas.fmap_id, CoContraVariantBiFunctorLemmas.fmap_id; auto.
  + rewrite CoContraVariantBiFunctorLemmas.fmap_comp, CovariantFunctorLemmas.fmap_comp, ContraVariantFunctorLemmas.fmap_comp; auto.
Qed.

Definition CoContraVariantBiFunctor_CoContraVariantFunctor_compose
  (F: CoContraVariantBiFunctor.functor)
  (F1: CovariantFunctor.functor)
  (F2: ContraVariantFunctor.functor) :=
  CovariantFunctor.Functor (CoContraVariantBiFunctor_CoContraVariantFunctor_composeFacts F F1 F2).

Lemma CoContraVariantBiFunctor_MixVariantFunctor_composeFacts
  (F: CoContraVariantBiFunctor.functor)
  (F1 F2: MixVariantFunctor.functor):
  MixVariantFunctor.functorFacts (fun T : Type => F (F1 T) (F2 T))
    (fun (A B : Type) (f : A -> B) (g : B -> A) =>
     CoContraVariantBiFunctor.fmap F (MixVariantFunctor.fmap F1 f g)
       (MixVariantFunctor.fmap F2 g f)).
Proof.
  constructor; intros; simpl.
  + rewrite !MixVariantFunctorLemmas.fmap_id, CoContraVariantBiFunctorLemmas.fmap_id; auto.
  + rewrite CoContraVariantBiFunctorLemmas.fmap_comp, !MixVariantFunctorLemmas.fmap_comp; auto.
Qed.

Definition CoContraVariantBiFunctor_MixVariantFunctor_compose
  (F: CoContraVariantBiFunctor.functor)
  (F1 F2: MixVariantFunctor.functor):=
  MixVariantFunctor.Functor (CoContraVariantBiFunctor_MixVariantFunctor_composeFacts F F1 F2).

End GeneralFunctorGenerator.

Module CovariantBiFunctorGenerator.

Import CovariantBiFunctor.
Import CovariantBiFunctorLemmas.

Definition Fpair: functor.
  refine (@Functor
   (fun T1 T2 => prod T1 T2)
   (fun _ _ _ _ f1 f2 x => (f1 (fst x), f2 (snd x))) _).
  constructor; intros; simpl; auto.
  extensionality p; destruct p as [a1 a2]; simpl; auto.
Defined.

Definition Fchoice: functor.
  refine (@Functor
   (fun T1 T2 => sum T1 T2)
   (fun _ _ _ _ f1 f2 x =>
      match x with
      | inl x => inl (f1 x)
      | inr x => inr (f2 x)
      end) _).
  constructor; intros; simpl.
  + extensionality c.
    destruct c; auto.
  + extensionality c.
    destruct c; unfold compose; simpl; auto.
Defined.

End CovariantBiFunctorGenerator.

Module CoContraVariantBiFunctorGenerator.

Import CoContraVariantBiFunctor.
Import CoContraVariantBiFunctorLemmas.

Definition Ffunc: functor.
  refine (@Functor
   (fun T1 T2 => T2 -> T1)
   (fun _ _ _ _ f1 f2 x => fun a => f1 (x (f2 a))) _).
  constructor; intros; simpl; auto.
Defined.

End CoContraVariantBiFunctorGenerator.

Module CovariantFunctorGenerator.

Import CovariantFunctor.
Import CovariantFunctorLemmas.

Definition fconst (T : Type): functor.
  refine (@Functor (fun _ => T) (fun _ _ _ x => x) _).
  constructor; intros; auto.
Defined.

Definition fidentity: functor.
  refine (@Functor (fun T => T) (fun _ _ f => f) _).
  constructor; intros; auto.
Defined.

Definition Foption: functor.
  refine (@Functor (fun T => option T)
   (fun _ _ f x => match x with Some x0 => Some (f x0) | _ => None end) _).
  constructor; intros; simpl; auto.
  + extensionality x; destruct x; auto.
  + extensionality x; destruct x; auto.
Defined.

Definition Flist: functor.
  refine (@Functor (fun T => list T)
   (fun _ _ f x => map f x) _).
  constructor; intros; simpl; auto.
  + extensionality x; apply map_id.
  + extensionality x; apply map_map.
Defined.

Definition fpair (F1 F2: functor): functor :=
  GeneralFunctorGenerator.CovariantBiFunctor_CovariantFunctor_compose
  CovariantBiFunctorGenerator.Fpair
  F1
  F2.

Goal forall (F1 F2: functor) (T: Type), fpair F1 F2 T = prod (F1 T) (F2 T).
reflexivity.
Qed.

Definition fchoice (F1 F2: functor): functor :=
  GeneralFunctorGenerator.CovariantBiFunctor_CovariantFunctor_compose
  CovariantBiFunctorGenerator.Fchoice
  F1
  F2.

Definition foption (F: functor): functor :=
  GeneralFunctorGenerator.CovariantFunctor_CovariantFunctor_compose
  Foption
  F.

Definition flist (F: functor): functor :=
  GeneralFunctorGenerator.CovariantFunctor_CovariantFunctor_compose
  Flist
  F.

Goal forall (F : functor) (T: Type), foption F T = option (F T).
reflexivity.
Qed.

Definition ffunc (F1: ContraVariantFunctor.functor) (F2: functor): functor :=
  GeneralFunctorGenerator.CoContraVariantBiFunctor_CoContraVariantFunctor_compose
  CoContraVariantBiFunctorGenerator.Ffunc
  F2
  F1.

Goal forall (F1 : ContraVariantFunctor.functor) (F2: functor) (T: Type),
  ffunc F1 F2 T = (F1 T -> F2 T).
reflexivity.
Qed.

Definition fsig {I: Type} (F: I -> functor): functor.
  refine (@Functor
   (fun T => @sigT I (fun i => F i T))
   (fun _ _ f x => match x with existT _ i x0 => existT _ i (fmap (F i) f x0) end) _).
  constructor; intros; simpl.
  + extensionality p; destruct p as [i a]; simpl.
    rewrite !fmap_id; auto.
  + extensionality p; destruct p as [i a]; simpl.
    unfold compose at 1. rewrite !fmap_app; auto.
Defined.

Definition fsubset (F: functor) (P: forall A, F A -> Prop)
  (Pfmap: forall A B (f: A -> B) x, P A x -> P B (fmap F f x)): functor.
  refine (@Functor
   (fun T => {x: F T | P T x})
   (fun _ _ f x =>
      match x with exist _ x' H => exist _ (fmap F f x')
                                           (Pfmap _ _ f x' H) end) _).
  constructor; intros; simpl.
  + extensionality x; destruct x as [x ?H].
    apply exist_ext.
    rewrite !fmap_id; auto.
  + extensionality x; destruct x as [x ?H].
    apply exist_ext.
    rewrite !fmap_app; auto.
Defined.

End CovariantFunctorGenerator.

Module MixVariantFunctorGenerator.

Import MixVariantFunctor.
Import MixVariantFunctorLemmas.

Definition fconst (T : Type): functor :=
  GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor
  (CovariantFunctorGenerator.fconst T).

Definition fidentity: functor :=
  GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor
  CovariantFunctorGenerator.fidentity.

Definition fpair (F1 F2: functor): functor :=
  GeneralFunctorGenerator.CovariantBiFunctor_MixVariantFunctor_compose
  CovariantBiFunctorGenerator.Fpair
  F1
  F2.

Definition fchoice (F1 F2: functor): functor :=
  GeneralFunctorGenerator.CovariantBiFunctor_MixVariantFunctor_compose
  CovariantBiFunctorGenerator.Fchoice
  F1
  F2.

Definition foption (F: functor): functor :=
  GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor_compose
  CovariantFunctorGenerator.Foption
  F.

Definition flist (F: functor): functor :=
  GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor_compose
  CovariantFunctorGenerator.Flist
  F.

Definition ffunc (F1 F2: functor): functor :=
  GeneralFunctorGenerator.CoContraVariantBiFunctor_MixVariantFunctor_compose
  CoContraVariantBiFunctorGenerator.Ffunc
  F2
  F1.

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

Definition fpi {I: Type} (F: I -> functor): functor.
  refine (@Functor
   (fun T => forall i: I, F i T)
   (fun _ _ f g x => fun i => fmap (F i) f g (x i)) _).
  constructor; intros; simpl.
  + extensionality p i; simpl.
    rewrite !fmap_id; auto.
  + extensionality p i; simpl.
    unfold compose at 1. rewrite !fmap_app; auto.
Defined.

Definition fsubset (F: functor) (P: forall A, F A -> Prop)
  (Pfmap: forall A B f g x, P A x -> P B (fmap F f g x)): functor.
  refine (@Functor
   (fun T => {x: F T | P T x})
   (fun _ _ f g x =>
      match x with exist _ x' H => exist _ (fmap F f g x')
                                           (Pfmap _ _ f g x' H) end) _).
  constructor; intros; simpl.
  + extensionality x; destruct x as [x ?H].
    apply exist_ext.
    rewrite !fmap_id; auto.
  + extensionality x; destruct x as [x ?H].
    apply exist_ext.
    rewrite !fmap_app; auto.
Defined.

End MixVariantFunctorGenerator.

Unset Implicit Arguments.

