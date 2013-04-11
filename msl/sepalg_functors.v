(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.functors.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.

Section unmaps.
  Variables (A: Type)(J_A: Join A)(A_pa: Perm_alg A).
  Variables (B: Type)(J_B: Join B)(B_pa: Perm_alg B).

  Definition unmap_left (f:A -> B) :=
    forall x' y z,
      join x' (f y) (f z) ->
      { x:A & { y0:A | join x y0 z /\ f x = x' /\ f y0 = f y }}.

  Definition unmap_right (f:A -> B) :=
    forall x y z',
      join (f x) (f y) z' ->
      { y0: A & { z:A | join x y0 z /\ f y0 = f y /\ f z = z' }}.
End unmaps.
Implicit Arguments unmap_right.
Implicit Arguments unmap_left.

Set Implicit Arguments.

(* Parameterized separating structures, useful for knot_prop_sa and 
    maybe for the general sa_knot. *)
Class pafunctor {F: Type -> Type} (FUN: functor F){J_F: forall A, Join (F A)}
    : Type := PaFunctor
{
  paf_join_hom : forall A B (f : A -> B),
    join_hom (fmap f);
  paf_preserves_unmap_left : forall A B (f : A -> B),
    unmap_left (J_F A) (J_F B) (fmap f);
  paf_preserves_unmap_right : forall A B (f : A -> B),
    unmap_right (J_F A) (J_F B) (fmap f)
}.

Definition f_paf {P} `{functor P} : functor P.
intros. apply H. Defined.
Existing Instance f_paf.

Definition Perm_paf {F: Type -> Type}(FUN: functor F)(J_F: forall A, Join (F A)) :=
                  forall (A: Type){JA: Join A}{Perm_A: Perm_alg A}, Perm_alg (F A).
Definition Sep_paf {F}(FUN: functor F)(J_F: forall A, Join (F A)) :=
                  forall (A: Type){JA: Join A}{Perm_A: Perm_alg A}{Sep_A: Sep_alg A}, Sep_alg (F A).
Definition Canc_paf {F}(FUN: functor F)(J_F: forall A, Join (F A)) := 
                  forall (A: Type){JA: Join A}{Perm_A: Perm_alg A}{Canc_A: Canc_alg A}, Canc_alg (F A).
Definition Disj_paf {F}(FUN: functor F)(J_F: forall A, Join (F A)) :=
                  forall (A: Type){JA: Join A}{Perm_A: Perm_alg A}{Disj_A: Disj_alg A}, Disj_alg (F A).

(* GENERATORS *)

Section ConstPAFunctor.
  Variables (T : Type)(J_T: Join T) (pa_T : Perm_alg T).
  
  Existing Instance f_const.
  Instance pa_fconst (A : Type) : Perm_alg (fconst T A) :=  pa_T.
  Instance paf_const : pafunctor (f_const T).
  Proof with auto.
    constructor; repeat intro...
    exists x'. exists y...
    exists y. exists z'...
  Qed.

End ConstPAFunctor.

Section EquivPAFunctor.
  Variables (F : Type -> Type) (f_F : functor F).

  Instance paf_equiv : @pafunctor _ f_F  (fun A => @Join_equiv (F A)).
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
  Variables (F1 : Type -> Type) (fF1 : functor F1).
  Variables (F2 : Type -> Type) (fF2 : functor F2).
  
  Existing Instance f_pair.
  Variables (J_F1: forall A, Join (F1 A)) (paF1: forall A, Perm_alg (F1 A)) 
         (pafF1: pafunctor fF1).
  Variables (J_F2: forall A, Join (F2 A)) (paF2: forall A, Perm_alg (F2 A)) 
         (pafF2: pafunctor fF2).

  Instance pa_fpair (A : Type) : Perm_alg (fpair F1 F2 A) :=
    Perm_prod (paF1 A) (paF2 A).

  Instance paf_pair : @pafunctor _ (f_pair fF1 fF2) _.
  Proof with auto.
    constructor; repeat intro.
    destruct H.
    destruct x. destruct y. destruct z.
    split; simpl in *;  eapply paf_join_hom...
(* PU *)
    icase x'; icase y; icase z.
    destruct H.
    simpl in H, H0.
    generalize (paf_preserves_unmap_left f f0 f2 f4 H); intro X.
    destruct X as [x1 [y01 [? [? ?]]]].
    generalize (paf_preserves_unmap_left f f1 f3 f5 H0); intro X.
    destruct X as [x2 [y02 [? [? ?]]]].
    exists (x1, x2). exists (y01, y02).
    split. split...
    split; simpl; congruence.
    icase x; icase y; icase z'.
    destruct H.
    simpl in H, H0.
    generalize (paf_preserves_unmap_right f f0 f2 f4 H); intro X.
    destruct X as [y01 [z1 [? [? ?]]]].
    generalize (paf_preserves_unmap_right f f1 f3 f5 H0); intro X.
    destruct X as [y02 [z2 [? [? ?]]]].
    exists (y01, y02). exists (z1, z2).
    split. split...
    split; simpl; congruence.
  Qed.

End PairSAFunctor.

Section CoFunSAFunctor.
  Variable dom : Type.
  Variable rng : Type -> Type.  
  Variable (f_rng : functor rng).
  
  Existing Instance f_fun.

  Variables (Join_rng: forall A, Join (rng A)) (pa_rng: forall A, Perm_alg (rng A))
       (pss_rng : pafunctor f_rng).

  Instance pa_ffun (A: Type) : Perm_alg (ffun dom rng A) :=
          Perm_fun _ _  _ _.

  Instance paf_fun : @pafunctor _ (f_fun dom f_rng) _.
  Proof with auto.
    constructor; simpl; intros; intro; intros.  intro i.
    spec H i.
    apply (paf_join_hom f (x i) (y i) (z i) H).
    (* PU *)
    set (f' := fun d => paf_preserves_unmap_left f (x' d) (y d) (z d) (H d)).
    exists (fun d => projT1 (f' d)).
    exists (fun d => projT1 (projT2 (f' d))).
    split.
    intro d. spec f' d.
    destruct f' as [x [y0 [? [? ?]]]]...
    split; extensionality d;
    simpl; unfold ffun_fmap, compose, f';
    remember (paf_preserves_unmap_left f (x' d) (y d) (z d) (H d));
    destruct s as [x [y0 [? [? ?]]]]...
    (* RIGHT *)
    set (f' := fun d => paf_preserves_unmap_right f (x d) (y d) (z' d) (H d)).
    exists (fun d => projT1 (f' d)).
    exists (fun d => projT1 (projT2 (f' d))).
    split.
    intro d. spec f' d.
    destruct f' as [y0 [z [? [? ?]]]]...
    split; extensionality d;
    simpl; unfold ffun_fmap, compose, f';
    remember (paf_preserves_unmap_right f (x d) (y d) (z' d) (H d));
    destruct s as [y0 [z [? [? ?]]]]...
  Qed.

End CoFunSAFunctor.

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
