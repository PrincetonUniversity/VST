(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.

Set Implicit Arguments.

Record functorFacts (PS : Type -> Type)
    (fmap : forall A B (f : A -> B), PS A -> PS B) 
    : Type := FunctorFacts
{
  ff_id : forall A, fmap _ _ (id A) = id (PS A);
  ff_comp : forall A B C (f : B -> C) (g : A -> B), fmap _ _ f oo fmap _ _ g = fmap _ _ (f oo g)
}.

(* Parameterized structures *)
Class functor (F : Type -> Type) 
                        : Type := Functor {
  fmap : forall A B (f : A -> B), F A -> F B;
  functor_facts : functorFacts F fmap
}.

Lemma fmap_id {F} `{functor F} : forall A, fmap (id A) = id (F A).
Proof. intros. destruct H. destruct functor_facts0. apply ff_id0. Qed.

Lemma fmap_comp {F} `{functor F} : forall A B C (f : B -> C) (g : A -> B),
  fmap f oo fmap g = fmap (f oo g).
Proof. intros. destruct H. destruct functor_facts0. apply ff_comp0. Qed.

Lemma fmap_app {F} `{functor F} : forall A B C (f : B -> C) (g : A -> B) x,
  fmap f (fmap g x) = fmap (f oo g) x.
Proof. intros. rewrite <- fmap_comp; auto. Qed.

(* GENERATORS *)

Section ConstFunctor.
  Variable T : Type.

  Definition fconst (A : Type) : Type := T.
  Definition fconst_fmap (A B : Type) (f : A -> B) (fA : fconst A) : fconst B :=
    fA.

  Lemma ff_const : functorFacts fconst fconst_fmap.
  Proof with auto.
    constructor...
  Qed.

  Definition f_const : functor fconst := Functor ff_const.
  Existing Instance f_const.
End ConstFunctor.

Section IdentityFunctor.
  Definition fidentity (A : Type) : Type := A.
  Definition fidentity_fmap (A B : Type) (f : A -> B) : fidentity A -> fidentity B := 
    f.
  
  Lemma ff_identity : functorFacts fidentity fidentity_fmap.
  Proof with auto.
    constructor...
  Qed.
  
  Definition f_identity : functor fidentity := Functor ff_identity.
  Existing Instance f_identity.
End IdentityFunctor.  

Section PairFunctor.
  Variables F1 : Type -> Type.
  Variable fF1 : functor F1.
  Variable F2 : Type -> Type.
  Variable fF2 : functor F2.
  
  Definition fpair (A : Type) : Type := (F1 A * F2 A)%type.
  Definition fpair_fmap (A B : Type) (f : A -> B) (pA : fpair A) : fpair B :=
    match pA with (p1, p2) => (fmap f p1, fmap f p2) end.
  
  Lemma ff_pair : functorFacts fpair fpair_fmap.
  Proof with auto.
    constructor; intros.
    extensionality p. destruct p.
    simpl.
    rewrite fmap_id. rewrite fmap_id...
    extensionality p. destruct p.
    simpl.
    rewrite <- fmap_comp. rewrite <- fmap_comp...
  Qed.

  Definition f_pair : functor fpair := Functor ff_pair.
  Existing Instance f_pair.
End PairFunctor.

Section OptionFunctor.
  Variable F:Type -> Type.
  Variable fF: functor F.

  Definition foption A := option (F A).

  Lemma ff_option : functorFacts foption (fun A B f => option_map (fmap f)).
  Proof.
    constructor.
    intros. extensionality. destruct x; simpl; auto.
    unfold id at 2. f_equal.
    rewrite fmap_id. auto.

    intros. extensionality. destruct x; simpl; auto.
    unfold compose at 1. simpl.
    f_equal. rewrite <- fmap_comp; auto.
  Qed.

  Definition f_option : functor foption := Functor ff_option.
  Existing Instance f_option.
End OptionFunctor.

Section CoFunFunctor.
(* For the domain, we require the constant to avoid covariance.  Maybe
    there is a nicer way to do this, but for now... 
  Variable dom : Type -> Type. 
  Variable ps_dom : pstruct dom.
  Definition pfun_fmap (A B:Type) (f:A->B) (g : B -> A) (x: pfun A) : pfun B := 
    (fmap f) oo (x oo fmap g).
*)
  Variable dom : Type.
  Variable rng : Type -> Type.  
  Variable f_rng : functor rng.
  
  Definition ffun (A : Type) : Type := dom -> rng A.
  Definition ffun_fmap (A B:Type) (f:A->B) (x: ffun A) : ffun B := 
    (fmap f) oo x.

  Lemma ff_fun : functorFacts ffun ffun_fmap.
  Proof with auto.
    constructor;
    unfold ffun_fmap; intros;
    [rewrite fmap_id | rewrite <- fmap_comp];
    extensionality x y...
  Qed.
  
  Definition f_fun : functor ffun := Functor ff_fun.
  Existing Instance f_fun.
End CoFunFunctor.


Section SigmaFunctor.
  Variable I:Type.
  Variable F: I -> Type -> Type.
  Variable fF : forall i , functor (F i).
  
  Definition fsig X := @sigT I (fun i => F i X).

  Definition fsigma_map (A B:Type) (f:A -> B) (x:fsig A) : fsig B :=
    match x with
    | existT i x' => existT (fun i => F i B) i (fmap f x')
    end.

  Definition ff_sigma : functorFacts fsig fsigma_map.
  Proof.
    constructor; unfold fsigma_map; simpl; intros.
    extensionality x. destruct x. simpl.
    rewrite fmap_id. auto.
    extensionality x. destruct x. simpl.
    rewrite <- fmap_comp.
    auto.
  Qed.

  Definition f_sigma : functor fsig := Functor ff_sigma.
  Existing Instance f_sigma.
End SigmaFunctor.
  
Section SubsetFunctor.
  Variable F:Type -> Type.
  Variable fF: functor F.

  Variable P : forall A, F A -> Prop.

  Variable HPfmap1 : forall A B (f:A->B) x, 
    P x -> P (fmap f x).

  Definition subset A := { x:F A | P x }.
  
  Definition subset_fmap (A B:Type) (f:A->B) (x:subset A) : subset B :=
    match x with
    | exist x' H => exist (fun x => P x) (fmap f x') (HPfmap1 f H)
    end.

  Lemma ff_subset : functorFacts subset subset_fmap.
  Proof.
    constructor; unfold subset_fmap; intros.
    extensionality. destruct x; simpl.
    generalize (HPfmap1 (id A) p).
    rewrite fmap_id; intros.
    unfold id; simpl.
    replace p0 with p by apply proof_irr; auto.
    extensionality. destruct x; simpl.
    unfold compose at 1.
    generalize (HPfmap1 (f oo g) p).
    rewrite <- fmap_comp.
    intros.
    replace p0 with
      (HPfmap1 f (HPfmap1 g p))
      by apply proof_irr; auto.
  Qed.

  Definition f_subset : functor subset := Functor ff_subset.
  Existing Instance f_subset.
End SubsetFunctor.

Unset Implicit Arguments.
