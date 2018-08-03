(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.

Set Implicit Arguments.

Import MixVariantFunctor.
Import MixVariantFunctorLemmas.
Import MixVariantFunctorGenerator.

(* Parameterized separating structures, useful for knot_prop_sa and
    maybe for the general sa_knot. *)

Section unmaps.
  Variables (A: Type)(J_A: Join A).
  Variables (B: Type)(J_B: Join B).

  Definition unmap_left (f:A -> B) :=
    forall x' y z,
      join x' (f y) (f z) ->
      { x:A & { y0:A | join x y0 z /\ f x = x' /\ f y0 = f y }}.

  Definition unmap_right (f:A -> B) :=
    forall x y z',
      join (f x) (f y) z' ->
      { y0: A & { z:A | join x y0 z /\ f y0 = f y /\ f z = z' }}.
End unmaps.
(*
Implicit Arguments unmap_right.
Implicit Arguments unmap_left.
*)

(*
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
*)

(* TODO: change pafunctor, unmap_left, unmap_right into prop *)
Record pafunctor (F: functor) (paf_join: forall A, Join (F A)): Type := Pafunctor
{
  paf_join_hom : forall A B (f : A -> B) (g: B -> A), join_hom (fmap F f g);
  paf_preserves_unmap_left : forall A B (f : A -> B) (g: B -> A),
    unmap_left (paf_join A) (paf_join B) (fmap F f g);
  paf_preserves_unmap_right : forall A B (f : A -> B) (g: B -> A),
    unmap_right (paf_join A) (paf_join B) (fmap F f g)
}.

(* GENERATORS *)

Section ConstPAFunctor.

  Variables (T : Type)(J_T: Join T).

  Lemma paf_const : pafunctor (fconst T) (fun _ => J_T).
    constructor; intros; hnf; intros.
    + auto.
    + exists x'. exists y. auto.
    + exists y. exists z'. auto.
  Qed.
End ConstPAFunctor.

Section EquivPAFunctor.
  Variables (F : functor).

  Lemma paf_equiv : @pafunctor F (fun A => @Join_equiv (F A)).
  Proof with auto.
    constructor; repeat intro.
    destruct H; subst; split...
    destruct H; subst.
    exists z. exists z. split...
    destruct H; subst.
    exists x. exists x. split...
  Qed.

End EquivPAFunctor.

Section PairSAFunctor.
  Variables (F1 F2: functor).
  Variables (J_F1: forall A, Join (F1 A)) (pafF1: pafunctor F1 J_F1).
  Variables (J_F2: forall A, Join (F2 A)) (pafF2: pafunctor F2 J_F2).

  (* The second argument must be explicitly specified (instead of _) *)
  (* Or else, it will cause universe inconsistency in floyd. *)
  Lemma paf_pair : @pafunctor (fpair F1 F2) (fun A : Type => Join_prod (F1 A) (J_F1 A) (F2 A) (J_F2 A)).
  Proof with auto.
    constructor; repeat intro.
    + destruct H.
      destruct x. destruct y. destruct z.
      split; simpl in *.
      - apply (@paf_join_hom _ _ pafF1 _ _ _ _ _ _ _); auto.
      - apply (@paf_join_hom _ _ pafF2 _ _ _ _ _ _ _); auto.
    + (* PU *)
      destruct x' as [f0 f1], y as [f2 f3], z as [f4 f5].
      destruct H.
      simpl in H, H0.
      generalize (paf_preserves_unmap_left pafF1 f g f0 f2 f4 H); intro X.
      destruct X as [x1 [y01 [? [? ?]]]].
      generalize (paf_preserves_unmap_left pafF2 f g f1 f3 f5 H0); intro X.
      destruct X as [x2 [y02 [? [? ?]]]].
      exists (x1, x2). exists (y01, y02).
      split. split...
      split; simpl; congruence.
    + destruct x as [f0 f1], y as [f2 f3], z' as [f4 f5].
      destruct H.
      simpl in H, H0.
      generalize (paf_preserves_unmap_right pafF1 f g f0 f2 f4 H); intro X.
      destruct X as [y01 [z1 [? [? ?]]]].
      generalize (paf_preserves_unmap_right pafF2 f g f1 f3 f5 H0); intro X.
      destruct X as [y02 [z2 [? [? ?]]]].
      exists (y01, y02). exists (z1, z2).
      split. split...
      split; simpl; congruence.
  Qed.
End PairSAFunctor.

Section CoFunSAFunctor.
  Variables (dom: Type) (rng : functor).
  Variables (Join_rng: forall A, Join (rng A)) (pss_rng : pafunctor rng Join_rng).

  Definition paf_fun : @pafunctor (ffunc (fconst dom) rng)
                         (fun A => Join_fun dom _ (Join_rng A)).
  Proof with auto.
    constructor; simpl; intros; intro; intros.
    + intro i.
      specialize ( H i).
      apply (paf_join_hom pss_rng f g _ _ _ H).
    + set (f' := fun d => paf_preserves_unmap_left pss_rng f g _ _ _ (H d)).
      exists (fun d => projT1 (f' d)).
      exists (fun d => proj1_sig (projT2 (f' d))).
      split.
      - intro d. (*spec f' d. *)
        destruct (f' d) as [x [y0 [? [? ?]]]]...
      - split; extensionality d;
        simpl; unfold compose, f';
        remember (paf_preserves_unmap_left pss_rng f g (x' d) (y d) (z d) (H d));
        destruct s as [x [y0 [? [? ?]]]]...
    + set (f' := fun d => paf_preserves_unmap_right pss_rng f g (x d) (y d) (z' d) (H d)).
      exists (fun d => projT1 (f' d)).
      exists (fun d => proj1_sig (projT2 (f' d))).
      split.
      - intro d. (*spec f' d. *)
        destruct (f' d) as [y0 [z [? [? ?]]]]...
      - split; extensionality d;
        simpl; unfold compose, f';
        remember (paf_preserves_unmap_right pss_rng f g (x d) (y d) (z' d) (H d));
        destruct s as [y0 [z [? [? ?]]]]...
  Qed.
End CoFunSAFunctor.
(*
(* This one is not used. *)
(* And the assumption, inj_sig, is wierd. *)
Section SigmaSAFunctor.
  Variable I:Type.
  Variables (F: I -> functor).

  Variables (JOIN: forall i A, Join (F i A))
            (fSA : forall i, pafunctor (F i) (JOIN i)).

  Existing Instance Join_sigma.

  Hypothesis inj_sig : forall A i x y,
    existT (fun i => F i A) i x = existT (fun i => F i A) i y -> x = y.

  Lemma paf_sigma : @pafunctor (fsig F)
                         (fun A => Join_sigma I (fun i => F i A) (fun i => JOIN i A)).
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
  Hypothesis HPfmap1 : forall A B (f: A -> B) (g: B -> A) x,
    P x -> P (fmap F f g x).
  Hypothesis HPfmap2 : forall A B (f: A -> B) (g: B -> A) x,
    P (fmap F f g x) -> P x.

  Definition paf_subset :
    @pafunctor (fsubset F (@P) HPfmap1) (fun A => Join_prop _ _ P).
  Proof.
    constructor.
    + repeat intro.
      destruct x as [x Hx].
      destruct y as [y Hy].
      destruct z as [z Hz].
      red; simpl.
      apply paf_join_hom; auto.
    + intros. simpl; hnf; intros.
      destruct x' as [x' Hx'].
      destruct y as [y Hy].
      destruct z as [z Hz].
      simpl in *.
      do 2 red in H. simpl in H.
      apply (paf_preserves_unmap_left fSA) in H.
      destruct H as [x [y0 [?[??]]]].
      subst x'.
      exists (exist (fun x => @P A x) x (HPfmap2 _ _ _ Hx')).
      assert (P y0). {
        apply (HPfmap2 f g). rewrite H1. apply HPfmap1. auto.
      }
      exists (exist (fun x => @P A x) y0 H0).
      intuition.
      - simpl.
        replace (HPfmap1 f g (HPfmap2 f g x Hx')) with Hx'
          by apply proof_irr.
        apply exist_ext; auto.
      - apply exist_ext; auto.
    + intros. simpl; hnf; intros.
      destruct x as [x Hx].
      destruct y as [y Hy].
      destruct z' as [z' Hz'].
      simpl in *.
      do 2 red in H. simpl in H.
      apply (paf_preserves_unmap_right fSA) in H.
      destruct H as [y0 [z [?[??]]]].
      subst z'.
      assert (P y0). {
        apply (HPfmap2 f g). rewrite H0. apply HPfmap1. auto.
      }
      exists (exist (fun x => @P A x) y0 H1).
      exists (exist (fun x => @P A x) z (HPfmap2 _ _ _ Hz')).
      intuition.
      - apply exist_ext; auto.
      - simpl.
        replace (HPfmap1 f g (HPfmap2 f g z Hz')) with Hz' by apply proof_irr.
        apply exist_ext; auto.
  Qed.

End SepAlgSubset_Functor.

