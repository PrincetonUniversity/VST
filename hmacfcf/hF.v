(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.PRF.
Require Import hmacfcf.splitVector.
Require Import hmacfcf.cAU.
Require Import fcf.CompFold.
Require Import fcf.DetSem fcf.SemEquiv.

Local Open Scope list_scope.

Section hF.

  Variable b k c : nat.

  Variable h : Bvector c -> Bvector b -> Bvector c.
  Variable F : Bvector k -> list (Bvector b) -> Bvector b.

  Definition hF key m :=
    [k_Out, k_In] <-2 splitVector c k key;
    h k_Out (F k_In m).

  Variable A : OracleComp (list (Bvector b)) (Bvector c) bool.
  Hypothesis A_wf : well_formed_oc A.

  (* Step 0: inline and simplify *)
  Definition G0 :=
    k_in <-$ {0, 1}^k;
    k_out <-$ {0, 1}^c;
    [b, _] <-$2 A _ _ (fun (_ : unit) m => ret (h k_out (F k_in m), tt)) tt;
    ret b.

  (* Step 1: replace h with a random function *)
  Definition G1 :=
    k_in <-$ {0, 1}^k;
    [b, _] <-$2 A _ _
    (fun (s : list (Bvector b * Bvector c)) m =>
      randomFunc ({0, 1}^c) _ s (F k_in m)) nil;
    ret b.

  (* Step 2: from cAU, identical random function inputs imply identical messages.  So this is equivalent to a random function with the domain of messages. *)
  Definition G2 :=
    [b, _] <-$2 A _ _
    (fun (s : list (list (Bvector b) * Bvector c)) m =>
      randomFunc ({0, 1}^c) _ s m) nil;
    ret b.


  Definition G0_1 :=
    [k_out, k_in] <-$2 (
    key <-$ {0, 1}^(c + k);
    ret splitVector c k key);
    [b, _] <-$2 A _ _ (fun (_ : unit) m => ret (h k_out (F k_in m), tt)) tt;
    ret b.

  Theorem G0_1_equiv :
    Pr[PRF_G_A ({0, 1}^(c + k)) hF _ A] == Pr[G0_1].

    unfold PRF_G_A, G0_1.
    inline_first.
    comp_skip.
    unfold f_oracle, hF.
    remember (splitVector c k x) as z.
    comp_simp.
    reflexivity.
  Qed.

  Theorem G0_1_G0_equiv :
    Pr[G0_1] == Pr[G0].

    unfold G0_1, G0.
    eapply eqRat_trans.
    eapply evalDist_seq_eq.
    eapply Rnd_split_equiv.
    intros.
    eapply eqRat_refl.

    inline_first.
    comp_swap_r.
    comp_skip.
    inline_first.
    comp_skip.

  Qed.

  Theorem G0_equiv :
    Pr[PRF_G_A ({0, 1}^(c + k)) hF _ A] == Pr[G0].

    rewrite G0_1_equiv.
    apply G0_1_G0_equiv.

  Qed.

  Definition hF_oracle k_in (s : unit) m : OracleComp (Bvector b) (Bvector c) (Bvector c * unit) :=
    r <--$ OC_Query _ (F k_in m);
    $ ret (r, tt).

  (* Need to use OC_Run here because hF_oracle calls F before querying the oracle. *)
  Definition PRF_h_A : OracleComp (Bvector b) (Bvector c) bool :=
    k_in <--$$ {0, 1}^k;
    [r, _] <--$2 OC_Run _ _ _ A (hF_oracle k_in) tt;
    $ ret r.

  Definition G1_1 :=
    k_out <-$ { 0 , 1 }^c;
    [b, _] <-$2 PRF_h_A _ _ (f_oracle h _ k_out) tt;
    ret b.

  Definition G1_2 :=
    [b, _] <-$2 PRF_h_A _ _ (randomFunc ({0, 1}^c) _) nil;
    ret b.

  Local Opaque evalDist.

  Theorem G0_G1_1_equiv :
    Pr[G0] == Pr[G1_1].

    unfold G0, G1_1.
    comp_swap_l.
    comp_skip.
    unfold PRF_h_A.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    unfold f_oracle.
    eapply comp_spec_eq_impl_eq.
    comp_skip.

    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => True)).
    trivial.
    intuition.
    inline_first.
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.
    simpl in *.
    intuition; subst.
    comp_simp.
    simpl.
    inline_first.
    comp_simp.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem G1_1_2_close :
    | Pr[G1_1] - Pr[G1_2] | <= PRF_Advantage ({0, 1}^c) ({0, 1}^c) h _ _ PRF_h_A.

    reflexivity.

  Qed.

  Theorem G1_2_G1_equiv :
    Pr[G1_2] == Pr[G1].

    unfold G1_2, G1.
    unfold PRF_h_A.
    simpl.
    inline_first.
    comp_skip.
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => snd a = b)).
    trivial.

    intuition.
    subst.
    inline_first.
    simpl.
    eapply comp_spec_eq_trans_r.
    2: eapply comp_spec_right_ident.
    comp_skip.
    apply (oneVector c).
    apply (oneVector c).
    inline_first.
    simpl.
    eapply comp_spec_ret; intuition.

    simpl in *.
    intuition; subst.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem G0_G1_equiv :
    | Pr[G0] - Pr[G1] | <= PRF_Advantage ({0, 1}^c) ({0, 1}^c) h _ _ PRF_h_A.

    rewrite G0_G1_1_equiv.
    rewrite <- G1_2_G1_equiv.
    eapply G1_1_2_close.

  Qed.


  Definition randomFunc_mem (D R : Set)(eqdd : EqDec D)(eqdr : EqDec R)(RndR : Comp R) (ls : list (D * R))d :=
    match (arrayLookup _ ls d) with
      | Some r =>
        ret (r, (d, r) :: ls)
      | None =>
        r <-$ RndR; ret (r, (d, r) :: ls)
    end.

    Theorem randomFunc_mem_spec :
    forall (D R : Set)(eqdd : EqDec D)(eqdr : EqDec R)(RndR : Comp R) (x1 x2 : list (D * R)) a,
      (forall z, arrayLookup _ x1 z = arrayLookup _ x2 z) ->
    comp_spec
     (fun y1 y2 =>
      fst y1 = fst y2 /\
      (forall x,
       arrayLookup _ (snd y1) x =
       arrayLookup _ (snd y2) x))
     (randomFunc_mem _ _ RndR x1 a)
     (randomFunc RndR _ x2 a).

    intuition.
    unfold randomFunc, randomFunc_mem.
    rewrite H.
    case_eq (arrayLookup eqdd x2 a ); intuition.

    eapply comp_spec_ret; intuition.
    simpl.
    case_eq (eqb x a); intuition.
    rewrite eqb_leibniz in H1.
    subst.
    intuition.

    comp_skip.
    eapply comp_base_exists; intuition.
    eapply comp_base_exists; intuition.

    eapply comp_spec_ret; intuition.
    simpl.
    rewrite H.
    trivial.
  Qed.

  Definition G2_1 :=
    k_in <-$ {0, 1}^k;
    [b, _] <-$2 A _ _ (fun s d => randomFunc_mem _ _ ({0, 1}^c) s (F k_in d)) nil;
    ret b.

  Theorem G2_1_equiv :
    Pr[G1] == Pr[G2_1].

    unfold G1, G2_1.
    comp_skip.
    eapply comp_spec_eq_impl_eq.
    comp_skip.

    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => forall x, arrayLookup _ a x = arrayLookup _ b x));
    intuition.

    eapply comp_spec_symm.
    eapply comp_spec_consequence.
    eapply randomFunc_mem_spec; intuition.
    intuition.
    comp_simp.
    simpl in *.
    intuition.
    subst.
    eapply comp_spec_eq_refl.

  Qed.

  Fixpoint arrayLookup_f (A B C : Set)(eqd : EqDec B)(ls : list ((A * B) * C))(a : B) :=
    match ls with
      | nil => None
      | ((x, z), y) :: ls' =>
        if (eqb a z) then (Some y) else (arrayLookup_f _ ls' a)
    end.

  Definition F_randomFunc k_in f d :=
    match arrayLookup_f _ f (F k_in d) with
      | Some r => ret (r, ((d, F k_in d), r) :: f)
      | None => r <-$ {0, 1}^c; ret (r, ((d, F k_in d), r) :: f)
    end.

  Definition G2_2 :=
    k_in <-$ {0, 1}^k;
    [b, _] <-$2 A _ _ (F_randomFunc k_in) nil;
    ret b.

    Theorem arrayLookup_f_equiv :
      forall (A B C : Set) (eqdb : EqDec B) (x1 : list (B * C)) (x2 : list (A * B * C)) (a : B),
      list_pred
         (fun c0 d =>
          fst c0 = snd (fst d) /\ snd c0 = snd d) x1 x2 ->
         arrayLookup _ x1 a = arrayLookup_f _ x2 a.

      induction x1; inversion 1; intuition; simpl in *.
      subst.
      destruct a.
      destruct a2.
      simpl in *.
      subst.
      destruct p.
      simpl.
      destruct (eqb a0 b0 ); intuition.

    Qed.

  Theorem G2_1_2_equiv :
    Pr[G2_1] == Pr[G2_2].

    unfold G2_1, G2_2.
    comp_skip.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => list_pred (fun c d =>  fst c = (snd (fst d)) /\ snd c = snd d) a b)).
    econstructor.
    intuition.
    unfold randomFunc_mem, F_randomFunc.

    erewrite arrayLookup_f_equiv ; eauto.
    destruct (arrayLookup_f (Bvector_EqDec b) x2 (F x a) ); intuition.
    eapply comp_spec_ret; intuition.
    simpl.
    econstructor.
    simpl.
    intuition.
    trivial.
    comp_skip.
    apply (oneVector c).
    apply (oneVector c).
    eapply comp_spec_ret; intuition.
    simpl.
    econstructor.
    intuition.
    eauto.

    comp_simp.
    simpl in *; intuition.
    subst.
    eapply comp_spec_eq_refl.

  Qed.


  Fixpoint findCollision_1 (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list (A * B))(a : A)(b : B) :=
    match ls with
      | nil => None
      | (a', b') :: ls' => if
        (eqb b b' && (negb (eqb a a')))
        then (Some a') else (findCollision_1 _ _ ls' a b)
    end.

  Definition collidesWith (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list (A * B))(a : A) b :=
    if (findCollision_1 _ _ ls a b) then true else false.

  Fixpoint findCollision(A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list (A * B)) : option (A * A * B) :=
    match ls with
      | nil => None
      | (a, b) :: ls' => let a' := (findCollision_1 _ _ ls' a b) in
        match a' with
          | None =>  (findCollision _ _ ls')
          | Some p' => Some (a, p', b)
        end
    end.

  Definition funcCollision (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list (A * B)) :=
    if (findCollision _ _ ls) then true else false.

  Definition G2_3 :=
    k_in <-$ {0, 1}^k;
    [b, f] <-$2 A _ _ (F_randomFunc k_in) nil;
    ret (b, funcCollision _ _ (fst (split f))).

  Theorem G2_2_3_equiv :
    Pr[G2_2] == Pr[x <-$ G2_3; ret fst x].

    unfold G2_2, G2_3.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    intuition.

  Qed.


  Definition G2_4 :=
    k_in <-$ {0, 1}^k;
    [b, f] <-$2 A _ _ (fun s a => b <- F k_in a; randomFunc_mem _ _ ({0, 1}^c) s (a, b)) nil;
    ret (b, funcCollision _ _ (fst (split f))).

  Theorem arrayLookup_noCollision_eq :
    forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B)(x1 : list ((A * B) * C)) a b0 b,
      arrayLookup _ x1 (a, b) = Some b0 ->
      collidesWith _ _ (fst (split x1)) a b = false ->
      arrayLookup_f _ x1 b = Some b0.

    induction x1; intuition; simpl in *.

    remember (split x1) as z.
    destruct z.
    simpl in *.
    unfold collidesWith in *.
    simpl in *.
    case_eq (eqb b3 b1); intuition.
    rewrite H1 in H0.
    simpl in *.
    case_eq (eqb a0 a); intuition.
    rewrite H2 in H0.
    simpl in *.
    rewrite eqb_leibniz in H1.
    rewrite eqb_leibniz in H2.
    subst.
    unfold eqbPair in *.
    simpl in *.
    repeat rewrite eqb_refl in H.
    simpl in *.
    trivial.

    rewrite H2 in H0.
    simpl in *.
    discriminate.

    rewrite H1 in H0.
    simpl in *.
    unfold eqbPair in *.
    simpl in *.
    rewrite H1 in H.
    case_eq (eqb a0 a); intuition.
    rewrite H2 in H.
    simpl in *.
    eapply IHx1; eauto.
    rewrite H2 in H.
    simpl in *.
    eapply IHx1; eauto.

  Qed.

  Theorem in_impl_collidesWith :
    forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list (A * B))(a a': A) (b : B),
      In (a, b) ls ->
      a <> a' ->
      collidesWith _ _ ls a' b = true.

    unfold collidesWith in *.

    induction ls; intuition; simpl in *.
    intuition.
    pairInv.
    case_eq (eqb a' a); intuition.
    rewrite  eqb_leibniz in H.
    subst.
    intuition.

    rewrite eqb_refl.
    simpl in *.
    trivial.

    case_eq (eqb b1 b0); intuition.
    case_eq (eqb a' a0); intuition.
    simpl.
    eapply IHls; intuition.
    eauto.
    subst; intuition.

    simpl.
    eapply IHls; eauto.

  Qed.

  Theorem funcCollision_false_impl_collidesWith_false :
    forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B) ls (a : A) (b : B),
      funcCollision _ _ ls = false ->
      In (a, b) ls ->
      collidesWith _ _ ls a b = false.

    induction ls; intuition; simpl in *.
    intuition.
    pairInv.

    unfold collidesWith, funcCollision in *.
    simpl in *.
    repeat rewrite eqb_refl.
    simpl.
    case_eq (findCollision_1 eqda eqdb ls a b1); intuition.
    rewrite H0 in H.
    discriminate.

    unfold collidesWith, funcCollision in *.
    simpl in *.
    case_eq (eqb a0 a); intuition.
    rewrite eqb_leibniz in H0.
    subst.
    rewrite eqb_refl.
    simpl.
    case_eq (findCollision_1 eqda eqdb ls a b0); intuition;
    rewrite H0 in H.
    discriminate.

    case_eq (eqb b1 b0); intuition.
    simpl.

    eapply IHls; intuition.

    simpl.
    eapply IHls; intuition.

    assert (a <> a0).
    intuition.
    subst.
    rewrite eqb_refl in H0.
    discriminate.
    case_eq (eqb a a0); intuition.
    rewrite eqb_leibniz in H3.
    subst.
    intuition.
    simpl.
    case_eq (eqb b1 b0); intuition.
    simpl.
    rewrite eqb_leibniz in H4.
    subst.

    specialize (in_impl_collidesWith  _ _ ls _ H1 H2); intuition.
    unfold collidesWith in H4.
    destruct (findCollision_1 eqda eqdb ls a0 b0);
      discriminate.

    simpl.
    case_eq (findCollision_1 eqda eqdb ls a0 b0); intuition.
    rewrite H5 in H.
    discriminate.

    rewrite H5 in H.
    eapply IHls; intuition.
  Qed.


  Theorem arrayLookup_Some_In_split:
    forall (A B : Set) (eqd : EqDec A) (arr : list (A * B)) (a : A) (b : B),
      arrayLookup eqd arr a = Some b -> In a (fst (split arr)).

    induction arr; intuition; simpl in *.
    discriminate.

    remember (split arr) as z.
    destruct z.

    simpl.
    case_eq (eqb a a0); intuition.
    rewrite eqb_leibniz in H0.
    intuition.
    rewrite H0 in H.
    right.
    eapply IHarr; intuition.
    eauto.
  Qed.

  Theorem arrayLookup_noCollision_eq_f :
    forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B)(x1 : list ((A * B) * C)) (a : A) (b : B) c,
      arrayLookup_f _ x1 b = Some c ->
      collidesWith _ _ (fst (split x1)) a b = false ->
      arrayLookup _ x1 (a, b) = Some c.

    induction x1; intuition; simpl in *.
    remember (split x1) as z.
    destruct z.
    simpl in *.

    unfold collidesWith in *.
    simpl in *.
    case_eq (eqb b2 b1); intuition.
    rewrite H1 in H.
    rewrite H1 in H0.
    inversion H; clear H; subst.
    simpl in *.
    case_eq (eqb a0 a); intuition.
    rewrite H in H0.
    simpl in *.
    rewrite eqb_leibniz in H1.
    rewrite eqb_leibniz in H.
    subst.
    unfold eqbPair.
    simpl.
    repeat rewrite eqb_refl.
    simpl.
    trivial.

    rewrite H in H0.
    simpl in *.
    discriminate.

    rewrite H1 in H0.
    rewrite H1 in H.
    simpl in *.
    unfold eqbPair.
    simpl.
    rewrite H1.
    case_eq (eqb a0 a); intuition.
    simpl.
    eapply IHx1; eauto.

    simpl.
    eapply IHx1; eauto.
  Qed.

  Theorem funcCollision_true_cons :
    forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B) (ls : list (A * B)) a,
      funcCollision _ _ ls = true ->
      funcCollision _ _ (a :: ls) = true.

    unfold funcCollision.
    intuition.
    simpl in *.
    destruct (findCollision_1 eqda eqdb ls a0 b0).
    trivial.
    trivial.

  Qed.

  Theorem F_randomFunc_preserves_coll :
    forall c0 x d a b0,
      funcCollision _ _ (fst (split c0)) = true ->
      In (a, b0) (getSupport (F_randomFunc x c0 d)) ->
      funcCollision _ _ (fst (split b0)) = true.

    intuition.
    unfold F_randomFunc in *.
    case_eq (arrayLookup_f (Bvector_EqDec b) c0 (F x d)); intuition.
    rewrite H2 in H1.
    repeat simp_in_support.
    simpl in *.
    remember (split c0) as z.
    destruct z.
    simpl in *.

    eapply funcCollision_true_cons; eauto.

    rewrite H2 in H1.

    repeat simp_in_support.
    simpl in *.
    remember (split c0) as z.
    destruct z.
    simpl in *.
    eapply funcCollision_true_cons; eauto.

  Qed.

  Theorem randomFunc_mem_preserves_coll :
    forall (D1 D2 R : Set)(eqdd : EqDec D1)(eqdd2 : EqDec D2)(eqdr : EqDec R) (RndR : Comp R) (c0 : list ((D1 * D2) * R)) d a b0,
      funcCollision _ _ (fst (split c0)) = true ->
      In (a, b0) (getSupport (randomFunc_mem _ _  RndR c0 d)) ->
      funcCollision _ _ (fst (split b0)) = true.

    intuition.
    unfold randomFunc_mem in *.
    destruct (arrayLookup _ c0 (a, b0)).
    repeat simp_in_support.
    simpl in *.
    remember (split c0) as z.
    destruct z.
    simpl in *.
    eapply funcCollision_true_cons; eauto.
    repeat simp_in_support.
    simpl in *.
    remember (split c0) as z.
    destruct z.
    simpl in *.
    eapply funcCollision_true_cons; eauto.

  Qed.

  Theorem F_randomFunc_wf :
    forall x y z,
      well_formed_comp (F_randomFunc x y z).

    intuition.
    unfold F_randomFunc.
    destruct (arrayLookup_f _ y (F x z)); wftac.

  Qed.

  Theorem randomFunc_mem_wf :
    forall (A B : Set) x y z (w : list (A * B)) v,
      well_formed_comp z ->
      well_formed_comp (randomFunc_mem x y z w v).

    intuition.
    unfold randomFunc_mem.
    destruct (arrayLookup x w v); intuition; wftac.

  Qed.

  Theorem A_randomFunc_F_spec :
    forall x,
      comp_spec (fun y1 y2 =>
        funcCollision (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b)
       (fst (split (snd y1))) =
       funcCollision (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b)
       (fst (split (snd y2))) /\
        (funcCollision (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b)
       (fst (split (snd y1))) = false ->
       y1 = y2))
       (A (list (list (Bvector b) * Bvector b * Bvector c))
        (list_EqDec
           (pair_EqDec
              (pair_EqDec (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b))
              (Bvector_EqDec c))) (F_randomFunc x) nil)
     (A (list (list (Bvector b) * Bvector b * Bvector c))
        (list_EqDec
           (pair_EqDec
              (pair_EqDec (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b))
              (Bvector_EqDec c)))
        (fun (s : list (list (Bvector b) * Bvector b * Bvector c))
           (a : list (Bvector b)) =>
         randomFunc_mem
           (pair_EqDec (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b))
           (Bvector_EqDec c) ({ 0 , 1 }^c) s (a, F x a)) nil).

    intuition.

    eapply comp_spec_consequence.
    eapply (@oc_comp_spec_eq_until_bad _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun z => funcCollision _ _ (fst (split z)))
      (fun z => funcCollision _ _ (fst (split z)))
      (fun a b => a = b)).

    intuition.
    eapply F_randomFunc_wf.
    intuition.
    eapply randomFunc_mem_wf.
    wftac.

    intuition; subst.

    unfold F_randomFunc.
    unfold randomFunc_mem.

    case_eq ( arrayLookup
         (pair_EqDec (list_EqDec (Bvector_EqDec b)) (Bvector_EqDec b)) x2
         (a, F x a)); intuition.
    case_eq (arrayLookup_f (Bvector_EqDec b) x2 (F x a)); intuition.
    eapply comp_spec_ret; intuition.
    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.
    trivial.

    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.

    erewrite arrayLookup_noCollision_eq in H2; eauto.
    inversion H2; clear H2; subst.
    trivial.

    erewrite arrayLookup_noCollision_eq in H2; eauto.
    inversion H2; clear H2; subst.
    trivial.

    eapply funcCollision_false_impl_collidesWith_false.
    unfold funcCollision in *.
    simpl in *.
    destruct (findCollision_1 (list_EqDec (Bvector_EqDec b))
      (Bvector_EqDec b) l a (F x a)).
    discriminate.
    assert (l = fst (split x2)).
    rewrite <- Heqz.
    trivial.
    subst.
    eauto.

    eapply arrayLookup_Some_In_split.
    eauto.

    assert (l = (fst (split x2))).
    rewrite <- Heqz.
    trivial.
    subst.
    unfold funcCollision in *.
    simpl in *.
    unfold collidesWith.
    destruct (findCollision_1 (list_EqDec (Bvector_EqDec b))
               (Bvector_EqDec b) (fst (split x2)) a (F x a)).
    discriminate.
    trivial.

    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.

    erewrite arrayLookup_noCollision_eq in H2; eauto.
    inversion H2; clear H2; subst.
    intuition.
    unfold funcCollision, collidesWith in *.
    simpl in *.
    assert (l = fst (split x2)).
    rewrite <- Heqz.
    trivial.
    subst.
    destruct (findCollision_1 (list_EqDec (Bvector_EqDec b))
               (Bvector_EqDec b) (fst (split x2)) a (F x a)).
    discriminate.
    trivial.

    comp_irr_l.
    eapply comp_spec_ret; intuition.
    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl.
    trivial.

    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.

    erewrite arrayLookup_noCollision_eq in H2; eauto.
    discriminate.
    assert (l = fst (split x2)).
    rewrite <- Heqz.
    trivial.
    subst.
    eapply funcCollision_false_impl_collidesWith_false.

    unfold funcCollision in *.
    simpl in *.
    destruct ( findCollision_1 (list_EqDec (Bvector_EqDec b))
               (Bvector_EqDec b) (fst (split x2)) a (F x a)).
    discriminate.
    eauto.
    eapply arrayLookup_Some_In_split.
    eauto.

    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.

    erewrite arrayLookup_noCollision_eq in H2; eauto.
    discriminate.
    assert (l = fst (split x2)).
    rewrite <- Heqz.
    trivial.
    subst.
    eapply funcCollision_false_impl_collidesWith_false.

    unfold funcCollision in *.
    simpl in *.
    destruct ( findCollision_1 (list_EqDec (Bvector_EqDec b))
               (Bvector_EqDec b) (fst (split x2)) a (F x a)).
    discriminate.
    eauto.
    eapply arrayLookup_Some_In_split.
    eauto.

    case_eq (arrayLookup_f (Bvector_EqDec b) x2 (F x a)); intuition.
    comp_irr_r.
    eapply comp_spec_ret; intuition.
    simpl.
    remember (split x2) as z.
    destruct z.
    simpl.
    trivial.

    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.

    erewrite arrayLookup_noCollision_eq_f in H; eauto.
    discriminate.
    unfold funcCollision, collidesWith in *.
    simpl in *.
    assert (l = (fst (split x2))).
    rewrite <- Heqz.
    trivial.
    subst.
    destruct (findCollision_1 (list_EqDec (Bvector_EqDec b))
               (Bvector_EqDec b) (fst (split x2)) a (F x a)).
    discriminate.
    trivial.

    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.

    erewrite arrayLookup_noCollision_eq_f in H; eauto.
    discriminate.
    unfold funcCollision, collidesWith in *.
    simpl in *.
    assert (l = (fst (split x2))).
    rewrite <- Heqz.
    trivial.
    subst.
    destruct (findCollision_1 (list_EqDec (Bvector_EqDec b))
               (Bvector_EqDec b) (fst (split x2)) a (F x a)).
    discriminate.
    trivial.

    comp_skip.
    apply (oneVector c).
    apply (oneVector c).
    eapply comp_spec_ret; intuition.

    intros.
    eapply F_randomFunc_preserves_coll;
    eauto.

    intuition.

    eapply randomFunc_mem_preserves_coll; eauto.

    trivial.
    trivial.

    intuition.
    simpl in *; subst.
    destruct b1; trivial.

    Grab Existential Variables.
    trivial.
  Qed.

  Theorem G2_3_4_bad_eq :
    Pr[x <-$ G2_3; ret (snd x)] == Pr[x <-$ G2_4; ret (snd x)].

    unfold G2_3, G2_4.
    inline_first.
    comp_skip.
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply A_randomFunc_F_spec.
    simpl in *.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.
  Qed.

  Theorem G2_3_4_eq_until_bad :
    forall x,
      evalDist G2_3 (x, false) == evalDist G2_4 (x, false).

    intuition.
    unfold G2_3, G2_4.
    inline_first.
    comp_skip.
    inline_first.
    eapply comp_spec_impl_eq.
    comp_skip.
    eapply A_randomFunc_F_spec.
    simpl in *.
    comp_simp.
    eapply comp_spec_ret; intuition.

    pairInv.
    intuition.
    pairInv.
    trivial.

    pairInv.
    simpl in *.
    rewrite H3 in H4.
    intuition.
    pairInv.
    trivial.

  Qed.


  Definition F_randomFunc_O f d :
    OracleComp
    (list (Bvector b))
    (Bvector b)
    (Bvector c * list ((list (Bvector b) * Bvector b) * Bvector c))  :=
    fd <--$ OC_Query _ d;
    match arrayLookup_f _ f fd with
      | Some r => $ ret (r, ((d, fd), r) :: f)
      | None => r <--$$ {0, 1}^c; $ ret (r, ((d, fd), r) :: f)
    end.

  Definition au_F_A : OracleComp (list (Bvector b)) (Bvector b) _ :=
    [_, p ] <--$2 OC_Run _ _ _ A F_randomFunc_O nil;
    let coll :=
      match (findCollision _ _ (fst (split p)) ) with
        | None => (nil, nil)
        | Some p => fst p
      end in
      $ ret (coll).

  Definition G2_3_bad :=
    k_in <-$ {0, 1}^k;
    [p, _] <-$2 au_F_A _ _ (WCR_Oracle _ F k_in) tt;
    [d1, d2] <-2 p;
    ret (negb (eqb d1 d2) && eqb (F k_in d1) (F k_in d2)).

  Theorem G2_3_bad_small :
    Pr[G2_3_bad] == Adv_WCR _ _ F (Rnd k) au_F_A.

    reflexivity.

  Qed.

    Theorem findCollision_1_correct :
      forall (A B : Set) eqd1 eqd2 (ls : list (A * B)) (x1 x2 : A) y,
      findCollision_1 eqd1 eqd2 ls x1 y =
       Some x2 ->
       x1 <> x2 /\
       In (x2, y) ls.

      induction ls; intros; simpl in *.
      discriminate.

      destruct a.
      case_eq (eqb y b0); intros.
      rewrite H0 in H.
      case_eq (eqb x1 a); intros.
      rewrite H1 in H.
      simpl in *.
      eapply IHls in H.
      intuition.

      rewrite H1 in H.
      simpl in *.
      inversion H; clear H; subst.
      rewrite eqb_leibniz in H0.
      subst.
      intuition.
      subst.
      rewrite eqb_refl in H1.
      discriminate.

      rewrite H0 in H.
      simpl in *.
      eapply IHls in H.
      intuition.

    Qed.

    Theorem findCollision_correct :
      forall (A B : Set) eqd1 eqd2 (ls : list (A * B)) (x1 x2 : A) y,
      findCollision eqd1 eqd2 ls =
       Some (x1, x2, y) ->
       x1 <> x2 /\
       In (x1, y) ls /\
       In (x2, y) ls.

      induction ls; intros; simpl in *;
      subst; try discriminate.

      destruct a.

      case_eq (findCollision_1 eqd1 eqd2 ls a b0); intros.
      rewrite H0 in H.
      eapply findCollision_1_correct in H0.
      intuition.
      subst.
      inversion H; clear H; subst.
      intuition.
      inversion H; clear H; subst.
      intuition.
      inversion H; clear H; subst.
      intuition.

      rewrite H0 in H.
      eapply IHls in H.
      intuition.
    Qed.

  Theorem G2_3_bad_equiv :
    Pr[x <-$ G2_3; ret (snd x)] == Pr[G2_3_bad].

    unfold G2_3, G2_3_bad.
    inline_first.
    comp_skip.
    unfold au_F_A.
    simpl.
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.

    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => a = fst b)).
    trivial.
    intuition.
    subst.
    unfold F_randomFunc, WCR_Oracle.
    inline_first.
    comp_simp.
    case_eq (arrayLookup_f (Bvector_EqDec b) (fst x2) (F x a)); intuition.
    simpl.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.

    simpl.
    inline_first.
    comp_skip.
    apply (oneVector c).
    apply (oneVector c).
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.

    simpl in *.
    intuition; subst.
    comp_simp.
    simpl.
    inline_first.
    unfold funcCollision.
    case_eq (findCollision (list_EqDec (Bvector_EqDec b))
                (Bvector_EqDec b) (fst (split (fst (snd b1))))); intuition.
    destruct p.
    destruct p.
    simpl.
    comp_simp.
    eapply comp_spec_ret; intuition.

    destruct b1.
    simpl in *.
    destruct p.
    simpl in *.

    apply findCollision_correct in H2.
    intuition.
    case_eq (eqb l l0); intuition.
    rewrite eqb_leibniz in H4.
    intuition.
    simpl.

    assert (forall a b, In (a, b) (fst (split l1)) -> b = F x a).
    intuition.
    eapply (@oc_comp_invariant _ _ _ _ _ (fun l1 => forall a b, In (a, b) (fst (split l1)) -> b = F x a)) in H0.
    eauto.
    intuition.
    unfold F_randomFunc in *.
    case_eq (arrayLookup_f (Bvector_EqDec b) c0 (F x d)); intuition.
    rewrite H11 in H7.
    repeat simp_in_support.
    simpl in *.
    remember (split c0) as z.
    destruct z.
    simpl in *.
    intuition.
    pairInv.
    trivial.
    rewrite H11 in H7.
    repeat simp_in_support.
    simpl in *.
    remember (split c0) as z.
    destruct z.
    simpl in *.
    intuition.
    pairInv.
    trivial.

    intuition.
    simpl in *.
    intuition.
    trivial.

    assert (b0 = F x l).
    eapply H6.
    trivial.
    eapply H6 in H5.
    subst.
    rewrite H7.
    rewrite eqbBvector_complete.
    trivial.

    comp_simp.
    rewrite eqb_refl.
    simpl.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem G2_3_4_close :
    | Pr[x <-$ G2_3; ret fst x] - Pr[x <-$ G2_4; ret fst x] | <=
      Adv_WCR _ _ F (Rnd k) au_F_A.

    eapply leRat_trans.
    eapply fundamental_lemma_h.
    eapply  G2_3_4_bad_eq .
    eapply  G2_3_4_eq_until_bad.
    rewrite G2_3_bad_equiv.
    rewrite G2_3_bad_small.
    intuition.

  Qed.

  Definition G2_5 :=
    [b, _] <-$2 A _ _ (fun s a => randomFunc_mem _ _ ({0, 1}^c) s a) nil;
    ret b.

  Theorem G2_4_5_equiv :
    Pr[x <-$ G2_4; ret fst x] == Pr[G2_5].

    unfold G2_4, G2_5.
    inline_first.
    comp_irr_l.
    wftac.
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.

    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => forall z, arrayLookup _ a (z, (F x z)) = arrayLookup _ b z)).
    intuition.
    intuition.
    unfold randomFunc_mem.
    rewrite H0.
    case_eq ( arrayLookup (list_EqDec (Bvector_EqDec b)) x2 a); intuition.
    eapply comp_spec_ret; intuition.
    simpl in *.
    unfold eqbPair.
    simpl.
    case_eq (eqb z a); intuition.
    simpl.
    rewrite eqb_leibniz in H3.
    subst.
    rewrite eqbBvector_complete.
    trivial.
    simpl.
    eauto.

    comp_skip.
    apply (oneVector c).
    apply (oneVector c).
    eapply comp_spec_ret; intuition.
    simpl.
    unfold eqbPair.
    simpl.
    case_eq (eqb z a); intuition.
    simpl.
    rewrite eqb_leibniz in H5.
    subst.
    rewrite eqbBvector_complete.
    trivial.
    simpl.
    trivial.

    comp_simp.
    simpl in *.
    intuition; subst.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem G2_5_equiv :
    Pr[G2_5] == Pr[G2].

    unfold G2_5, G2.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => forall z, arrayLookup _ a z = arrayLookup _ b z)).
    intuition.

    intuition.
    eapply randomFunc_mem_spec.
    intuition.
    simpl in *.
    intuition.
    subst.
    comp_simp.
    simpl.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem G1_G2_equiv :
    | Pr[G1] - Pr[G2] | <= Adv_WCR _ _ F (Rnd k) au_F_A.

    rewrite G2_1_equiv.
    rewrite G2_1_2_equiv.
    rewrite G2_2_3_equiv.
    rewrite <- G2_5_equiv.
    rewrite <- G2_4_5_equiv.
    eapply G2_3_4_close.

  Qed.


  Theorem G2_equiv :
    Pr[G2] == Pr[PRF_G_B ({0, 1}^c) _ _ A].

    reflexivity.

  Qed.

  Theorem hF_PRF :
    PRF_Advantage ({0, 1}^(c + k)) ({0, 1}^c) hF _ _ A <=
    PRF_Advantage ({0, 1}^c) ({0, 1}^c) h _ _ PRF_h_A +
    Adv_WCR _ _ F (Rnd k) au_F_A.

    unfold PRF_Advantage.
    rewrite G0_equiv.
    eapply ratDistance_le_trans.
    eapply G0_G1_equiv.
    rewrite <- G2_equiv.
    eapply G1_G2_equiv.

  Qed.


End hF.

