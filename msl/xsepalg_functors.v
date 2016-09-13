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

  Definition paf_pair : @pafunctor (fpair F1 F2) _.
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

Section SepAlgSubset_Functor.
  Variables (F: Type -> Type) (fF : functor F).
  Variables(JOIN: forall A, Join (F A))
                  (paF: forall A, Perm_alg (F A))
                  (fSA : pafunctor fF).
  
  Variable P : forall A, F A -> Prop.

  Hypothesis HPunit :
    forall A (x e: F A), P x -> unit_for e x -> P e.
  Hypothesis HPjoin : forall A (x y z : F A),
    join x y z -> P x -> P y -> P z.
  Hypothesis HPfmap1 : forall A B (f:A->B) x,
    P x -> P (fmap f x).
  Hypothesis HPfmap2 : forall A B (f:A->B) x, 
    P (fmap f x) -> P x.

  Instance pa_fsubset X : Perm_alg (subset F P X).
  Proof. apply Perm_prop; auto. apply HPjoin. Qed.

  Existing Instance fF.
  Existing Instance f_subset.

  Instance saf_subset : @pafunctor _ (f_subset fF P HPfmap1) _.
  Proof.
    constructor.

    repeat intro. simpl.
    destruct x as [x Hx].
    destruct y as [y Hy].
    destruct z as [z Hz].
    red; simpl.
    apply paf_join_hom; auto.
    
    intros. simpl; hnf; intros.
    destruct x' as [x' Hx'].
    destruct y as [y Hy].
    destruct z as [z Hz].
    simpl in *.
    do 2 red in H. simpl in H.
    apply paf_preserves_unmap_left in H.
    destruct H as [x [y0 [?[??]]]].
    subst x'.
    exists (exist (fun x => @P A x) x (HPfmap2 _ _  Hx')).
    assert (P y0).
    apply (HPfmap2 f). rewrite H1. apply HPfmap1. auto.
    exists (exist (fun x => @P A x) y0 H0).
    intuition.
    simpl.
    replace (HPfmap1 f (HPfmap2 f x Hx')) with Hx'
      by apply proof_irr; auto.
    simpl.
    generalize (HPfmap1 f H0).
    rewrite H1. intros.
    replace p with (HPfmap1 f Hy) by apply proof_irr; auto.
 
    intros. simpl; hnf; intros.
    destruct x as [x Hx].
    destruct y as [y Hy].
    destruct z' as [z' Hz'].
    simpl in *.
    do 2 red in H. simpl in H.
    apply paf_preserves_unmap_right in H.
    destruct H as [y0 [z [?[??]]]].
    subst z'.
    assert (P y0).
    apply (HPfmap2 f). rewrite H0. apply HPfmap1. auto.
    exists (exist (fun x => @P A x) y0 H1).
    exists (exist (fun x => @P A x) z (HPfmap2 _ _  Hz')).
    intuition.
    simpl.
    generalize (HPfmap1 f H1).
    rewrite H0. intros.
    replace p with (HPfmap1 f Hy) by apply proof_irr; auto.
    simpl.
    replace (HPfmap1 f (HPfmap2 f z Hz')) with Hz'
      by apply proof_irr; auto.
  Qed.
 
End SepAlgSubset_Functor.
*)

