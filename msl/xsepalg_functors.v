(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.functors_variant.
Require Import msl.sepalg.
Require Import msl.xsepalg_generators.

Set Implicit Arguments.

Import MixVariantFunctor.
Import MixVariantFunctorLemmas.
Import MixVariantFunctorGenerator.

(* Parameterized separating structures, useful for knot_prop_sa and 
    maybe for the general sa_knot. *)

Definition Join_paf (F: functor): Type :=
  forall A, Join (F A).
Definition Perm_paf {F: functor} (paf_join: forall A, Join (F A)): Type :=
  forall A: Type, Perm_alg (F A).
Definition Sep_paf {F: functor} (paf_join: forall A, Join (F A)): Type :=
  forall A: Type, Sep_alg (F A).
Definition Canc_paf {F: functor} (paf_join: forall A, Join (F A)): Type :=
  forall A: Type, Canc_alg (F A).
Definition Disj_paf {F: functor} (paf_join: forall A, Join (F A)): Type :=
  forall A: Type, Disj_alg (F A).

Record pafunctor (F: functor) (paf_join: forall A, Join (F A)): Type := Pafunctor
{
  paf_join_hom : forall A B (f : A -> B) (g: B -> A), join_hom (fmap F f g)
}.

(* GENERATORS *)

Section ConstPAFunctor.

  Variables (T : Type)(J_T: Join T).

  Definition paf_const : pafunctor (fconst T) (fun _ => J_T).
    constructor.
    split; intros; auto.
  Defined.
End ConstPAFunctor.

Section PairSAFunctor.
  Variables (F1 F2: functor).
  Variables (J_F1: forall A, Join (F1 A)) (pafF1: pafunctor F1 J_F1).
  Variables (J_F2: forall A, Join (F2 A)) (pafF2: pafunctor F2 J_F2).

  (* The second argument must be explicitly specified (instead of _) *)
  (* Or else, it will cause universe inconsistency in floyd. *)
  Definition paf_pair : @pafunctor (fpair F1 F2) (fun A : Type => Join_prod (F1 A) (J_F1 A) (F2 A) (J_F2 A)).
  Proof with auto.
    constructor; repeat intro.
    split; repeat intro.
    + destruct H.
      destruct x. destruct y. destruct z.
      split; simpl in *.
      - apply (proj1 (@paf_join_hom _ _ pafF1 _ _ _ _ _ _ _))...
      - apply (proj1 (@paf_join_hom _ _ pafF2 _ _ _ _ _ _ _))...
    + destruct H.
      destruct x. destruct y. destruct z.
      split; simpl in *.
      - eapply (proj2 (@paf_join_hom _ _ pafF1 _ _ _ _ _ _ _)) in H...
      - eapply (proj2 (@paf_join_hom _ _ pafF2 _ _ _ _ _ _ _)) in H0...
  Defined.

End PairSAFunctor.

Section CoFunSAFunctor.
  Variables (dom: Type) (rng : functor).
  Variables (Join_rng: forall A, Join (rng A)) (pss_rng : pafunctor rng Join_rng).

  Definition paf_fun : @pafunctor (ffunc (fconst dom) rng)
                         (fun A => Join_fun dom _ (Join_rng A)).
  Proof with auto.
    constructor; split; simpl; intros; intro i; intros.
    + spec H i.
      apply (proj1 (paf_join_hom pss_rng f g (x i) (y i) (z i)) H).
    + spec H i.
      apply (proj2 (paf_join_hom pss_rng f g (x i) (y i) (z i)) H).
  Defined.

End CoFunSAFunctor.
(*
Section SigmaSAFunctor.
  Variable I:Type.
  Variables (F: I -> Type -> Type) (fF : forall i , functor (F i)).
  
  Existing Instance f_sigma.
  Variables (JOIN: forall i A, Join (F i A))
                  (paF: forall i A, Perm_alg (F i A))
       (fSA : forall i, pafunctor (fF i)).

  Existing Instance Join_sigma.

  Hypothesis inj_sig : forall A i x y, existT (fun i => F i A) i x = existT (fun i => F i A) i y -> x = y.

  Instance pa_fsigma: forall X : Type, Perm_alg {i : I & F i X} := 
    fun X => Perm_sigma I (fun i => F i X) _ (fun i => paF i X).

  Instance paf_sigma : @pafunctor _ (f_sigma F fF) _.
  Proof.
    constructor; simpl; intros.
    hnf; simpl; intros.
    inv H. constructor.
    apply paf_join_hom; auto.
    
    hnf; simpl; intros.
    destruct x' as [xi x'].
    destruct y as [yi y].
    destruct z as [zi z].
    unfold fsigma_map in H.
    assert (xi = yi /\ yi = zi).
    inv H; auto.
    destruct H0. subst zi yi.
    rename xi into i.
    assert (join x' (fmap f y) (fmap f z)).
    inv H; auto.
    apply inj_sig in H2.
    apply inj_sig in H3.
    apply inj_sig in H4.
    subst. auto.
    apply paf_preserves_unmap_left in H0.
    destruct H0 as [x [y0 [?[??]]]].
    exists (existT (fun i => F i A) i x).
    exists (existT (fun i => F i A) i y0).
    intuition.
    constructor; auto.
    unfold fsigma_map; f_equal; auto.
    unfold fsigma_map; f_equal; auto.

    hnf; simpl; intros.
    destruct x as [xi x].
    destruct y as [yi y].
    destruct z' as [zi z'].
    assert (xi = yi /\ yi = zi).
    inv H; auto.
    destruct H0. subst zi yi.
    rename xi into i.
    assert (join (fmap f x) (fmap f y) z').
    inv H; auto.
    apply inj_sig in H2.
    apply inj_sig in H3.
    apply inj_sig in H4.
    subst. auto.
    apply paf_preserves_unmap_right in H0.
    destruct H0 as [y0 [z [?[??]]]].
    exists (existT (fun i => F i A) i y0).
    exists (existT (fun i => F i A) i z).
    intuition.
    constructor; auto.
    unfold fsigma_map; f_equal; auto.
    unfold fsigma_map; f_equal; auto.
  Qed.

End SigmaSAFunctor.
*)
Section SepAlgSubset_Functor.
  Variables (F: functor).
  Variables (JOIN: forall A, Join (F A))
            (fSA : @pafunctor F JOIN).
  
  Variable P : forall A, F A -> Prop.
  Arguments P {A} _.
  Hypothesis HPfmap : forall A B (f: A -> B) (g: B -> A) x,
    P x -> P (fmap F f g x).
  
  Definition paf_subset :
    @pafunctor (fsubset F (@P) HPfmap) (fun A => Join_prop _ _ P).
  Proof.
    constructor.
    repeat intro. simpl.
    split.
    + destruct x as [x Hx].
      destruct y as [y Hy].
      destruct z as [z Hz].
      red; simpl.
      apply paf_join_hom; auto.
    + destruct x as [x Hx].
      destruct y as [y Hy].
      destruct z as [z Hz].
      red; simpl.
      apply paf_join_hom; auto.
  Defined.

End SepAlgSubset_Functor.

