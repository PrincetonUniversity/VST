(* The PRP PRF switching lemma.  This proof uses the outdated state-related definitions.  We need to update this proof to use the definitions and theory in Procedure.v *)

Set Implicit Arguments.

Require Import Crypto.
Require Import Permutation.
Require Import ConstructedFunc.
Require Import State.

Local Open Scope list_scope.
Local Open Scope array_scope.

(* We start by extending the theory of constructed permutations with a notion of "bad" permutations.  A permutation is "bad" if, at some point in the past, it attempted to choose a new value for its range, and on the first attempt it produced a value that is already in its range. *)
Section PRP_PRF.
  Variable n : nat. (* bit vector length *)

  Hint Resolve getUnusedR_wf : wftac.
  Hint Resolve well_formed_perm_1 : wftac.
  
  Definition getUnusedBvector := @getUnusedR (Bvector n) _ _ (Rnd n).
  Definition well_formed_Bvector_perm := @well_formed_perm (Bvector n) _ _ _ (Rnd n).
  Definition randomPerm_Bvector := @randomPerm (Bvector n) _ _ _ (Rnd n).

  Lemma getUnusedBvector_wf_h : forall ls r,
       inRange _ ls r = false ->
       well_formed_comp (getUnusedBvector ls).

    intuition.
    eapply getUnusedR_wf; wftac.
    simpl.
    eapply in_getAllBvectors.
  Qed.

  Theorem getUnusedBvector_wf : forall ls d,
       well_formed_Bvector_perm ls ->
       ls # d = None ->
       well_formed_comp (getUnusedBvector ls).

    intuition.
    eapply well_formed_perm_1 in H.
    destruct H.
    intuition.
    unfold getUnusedBvector.
    eapply getUnusedR_wf; wftac.
    eauto.
  Qed.
  Hint Resolve getUnusedBvector_wf : wftac.

  (* A random permutation in which the loop that gets an unused value from the range is unrolled one step.  This is useful when comparing to a random function. *)
  Definition randomPerm_unroll(p : (list (Bvector n * Bvector n)) * Bvector n) : Comp (list (Bvector n * Bvector n) * Bvector n) :=
    let (f, d) := p in
    match f#d with
      | None => (r <-$ (r0 <-$ {0, 1}^n; if (negb (inRange _ f r0)) then ret r0 else getUnusedBvector f) ; ret ((d, r) :: f, r))
      | Some r => ret (f, r)
    end.

   Lemma randomPerm_unroll_wf : forall ls b0, 
    (forall x, ls#x = None -> exists r, inRange _ ls r = false) ->
    well_formed_comp (randomPerm_unroll (ls, b0)).

    intuition.
    unfold randomPerm_unroll.
    case_eq (ls#b0); intuition; wftac.
    edestruct H; eauto.
    eapply getUnusedBvector_wf_h.
    eauto.
  Qed.

  (* A random permutation in which the loop that gets an unused value form the range is unrolled one step and the permutation keeps track of whether the first attempt located a value that is already in the range.  This is useful when comparing to a random function. *)
  Definition randomPerm_bad(p : (list (Bvector n * Bvector n)) *  Bvector n) : Comp (list (Bvector n * Bvector n) * Bvector n) :=
    let (f, d) := p in 
    match f#d with
      | None => 
        r0 <-$ {0,1} ^ n; 
        r <-$ if (negb (inRange _ f r0)) then ret r0 else getUnusedBvector f;
          ret (if (inRange _ f r0) then ((d, r) :: (d, r0) :: f) else ((d, r) :: f), r)
      | Some r => ret (f, r)
    end.

  Fixpoint checkBad(f : list (Bvector n * Bvector n)) : bool :=
    match f with
      | nil => false
      | (d, r) :: f' =>
        orb (inRange _ f' r) (checkBad f')
    end.

  
  Lemma randomPerm_bad_wf : forall ls d,
    well_formed_Bvector_perm ls ->
    well_formed_comp (randomPerm_bad (ls, d)).
    
    intuition.
    unfold randomPerm_bad.
    case_eq (ls#d); intuition.
    wftac.
    wftac.
  Qed.
  Hint Resolve randomPerm_bad_wf : wftac.

  Lemma randomPerm_eq_unroll : forall s d x,
    well_formed_Bvector_perm s ->
    evalDist (randomPerm_Bvector (s, d)) x ==
    evalDist (randomPerm_unroll (s, d)) x.
    
    intuition.
    unfold randomPerm_Bvector, randomPerm, randomPerm_unroll.
    case_eq (s#d); intuition.
    unfold getUnusedR.
    comp_skip.
    eapply repeat_unroll_eq; wftac.
    eapply well_formed_perm_1 in H; eauto.
    destruct H.
    exists x0.
    eapply filter_In; intuition.
    destruct (inRange _ s x0); intuition.
  Qed.

  
  Lemma randomPerm_unroll_preserves_wf : forall ls d ls' r,
    well_formed_Bvector_perm ls ->
    In (ls', r) (getSupport (randomPerm_unroll (ls, d))) ->
    well_formed_Bvector_perm ls'.
    
    intuition.
    unfold randomPerm_unroll in *.
    case_eq (ls#d); intuition.
    rewrite H1 in H0.
    simpl in *.
    intuition.
    inversion H2; clear H2; subst.
    trivial.

    rewrite H1 in H0.
    apply getSupport_Bind_In in H0.
    destruct H0.
    intuition.
    apply getSupport_Bind_In in H2.
    destruct H2.
    intuition.
    simpl in H3.
    intuition.
    inversion H0; clear H0; subst.
    case_eq (inRange _ ls x0); intuition;
    rewrite H0 in H4.
    simpl in *.
    apply filter_In in H4.
    intuition.
    eapply well_formed_perm_cons; eauto.
    destruct (inRange _ ls r); intuition.
    simpl in *.
    intuition. subst.
    eapply well_formed_perm_cons; eauto.

  Qed.


  Lemma randomPerm_unroll_preserves_wf_pair : forall ls d p,
    well_formed_Bvector_perm ls ->
    In p (getSupport (randomPerm_unroll (ls, d))) ->
    well_formed_Bvector_perm (fst p).

    intuition.
    destruct p.
    eapply randomPerm_unroll_preserves_wf; eauto.
  Qed.
 

  Lemma randomPerm_bad_preserves_wf : forall ls d ls' r,
    well_formed_Bvector_perm ls ->
    In (ls', r) (getSupport (randomPerm_bad (ls, d))) ->
    well_formed_Bvector_perm ls'.
    
    intuition.
    unfold randomPerm_bad in *.
    case_eq (ls#d); intuition;
    rewrite H1 in H0.
    simp_in_support.
    trivial.

    simp_in_support.
    case_eq (inRange _ ls x); intuition;
    rewrite H0 in H3.
    simp_in_support.
    simpl in *.
    intuition.
    inversion H3; clear H3; subst.
    apply filter_In in H4.
    intuition.
    unfold well_formed_Bvector_perm, well_formed_perm in *.
    intuition.
    destruct (in_dec (EqDec_dec _) d lsd).
    specialize (H6 d).
    intuition.
    simpl in *.
    rewrite eqbBvector_complete in H7.
    discriminate.
    edestruct (H (d :: lsd)).
    econstructor; trivial.
    intuition.
    simpl in H7.
    intuition. subst.
    trivial.
    specialize (H6 d0).
    intuition.
    simpl in H7.
    destruct (eqbBvector d0 d).
    discriminate.
    trivial.

    intuition.
    destruct (in_dec (EqDec_dec _) r x0).
    exists (removeFirst (EqDec_dec _) x0 r).
    intuition.
    simpl.
    case_eq (eqbBvector r0 r); intuition.
    apply eqbBvector_sound in H11.
    subst.
    exfalso.
    eapply removeFirst_NoDup_not_in; eauto.

    case_eq (eqbBvector r0 x); intuition.
    apply eqbBvector_sound in H12.
    subst.
    assert (inRange  _ ls x = false).
    eapply H8.
    eapply removeFirst_in_iff.
    eauto.
    congruence.
    eapply H8.
    eapply removeFirst_in_iff.
    eauto.
    simpl.
    eapply in_getAllBvectors.
    eapply removeFirst_NoDup.
    trivial.
    eapply eq_add_S.
    simpl in H10.
    rewrite H10.
    symmetry.
    eapply removeFirst_length.
    trivial.

    destruct x0.
    simpl in *.
    omega.
    exists x0.
    intuition.
    simpl.
    simpl in n1.
    intuition.
    case_eq (eqbBvector r0 r); intuition.
    apply eqbBvector_sound in H13.
    subst.
    intuition.
    case_eq (eqbBvector r0 x); intuition.
    apply eqbBvector_sound in H14.
    subst.
    assert (inRange _ ls x = false).
    eapply H8.
    simpl.
    right.
    trivial.
    congruence.
    eapply H8.
    simpl.
    intuition.
    simpl.
    eapply in_getAllBvectors.
    inversion H7; clear H7; subst.
    trivial.
    
    repeat simp_in_support.
    eapply well_formed_perm_cons; trivial.

    simpl in *.
    discriminate.
  Qed.

  Lemma randomPerm_bad_preserves_wf_pair : forall ls d p,
    well_formed_Bvector_perm ls ->
    In p (getSupport (randomPerm_bad (ls, d))) ->
    well_formed_Bvector_perm (fst p).

    intuition.
    destruct p.
    eapply randomPerm_bad_preserves_wf; eauto.
  Qed.

  Definition Bvector_perms_eq := @perms_eq (Bvector n) _ _ _ (Rnd n).
  
  Lemma randomPerm_unroll_bad_inv : 
    comp_spec 
    (fun p1 p2 => (snd p1) = (snd p2) /\ Bvector_perms_eq (fst p1) (fst p2)) 
    (fun p1 p2 => (snd p1) = (snd p2) /\ Bvector_perms_eq (fst p1) (fst p2))
    randomPerm_unroll randomPerm_bad.
    
    unfold comp_spec.
    
    intuition.
    simpl in H1.
    subst.
    unfold randomPerm_unroll, randomPerm_bad.
    unfold Bvector_perms_eq, perms_eq, funcs_eq in *.
    intuition.
    destruct d2.
    unfold snd.
    simpl in H3.

    rewrite H3.
    case_eq (l # b); intuition.

    comp_simp.
    eapply H0; intuition.

    unfold randomPerm_unroll.
    simpl.
    rewrite H3.
    rewrite H4.
    simpl.
    intuition.

    unfold randomPerm_bad.
    rewrite H4.
    simpl.
    intuition.
    
    inline_first.
    comp_skip.
    inline_first.
    
    unfold fst, snd in H5.
    rewrite H5.
    case_eq (inRange _ l r2); intuition; unfold negb.
    comp_skip.
    eapply getUnusedR_eq; intuition.

    comp_simp.
    eapply H0; intuition; unfold fst.
    eapply well_formed_perm_cons; trivial.
    rewrite H3.
    trivial.
    eapply getUnusedR_not_inRange.
    rewrite H3.
    eauto.
    eauto.
    
    eapply well_formed_perm_cons_2; intuition.
    simpl.
    destruct (eqbBvector d b); intuition.
    simpl.
    case_eq (eqbBvector r r0); intuition.
    case_eq (eqbBvector r r2); intuition.
    apply eqbBvector_sound in H12.
    subst.
    rewrite H5.
    trivial.

    unfold snd.
    
    eapply getSupport_In_evalDist.
    intuition.
    eapply getSupport_In_evalDist.
    eapply (@inSupportRandomPerm (Bvector n) (Bvector n)).
    eauto.
    rewrite H3.
    eauto.
    rewrite randomPerm_eq_unroll.
    trivial.
    simpl in H1.
    trivial.

    Theorem inSupportRandomPerm_bad : 
      forall a b r1 r2,
        In r1 (getSupport (getUnusedBvector a)) ->
        inRange _ a r2  = true ->
        a # b = None ->
        In ((b, r1) :: (b, r2) :: a, r1) (getSupport (randomPerm_bad (a, b))).
      
      intuition.
      unfold randomPerm_bad.
      rewrite H1.
      eapply getSupport_In_Seq.
      simpl.
      eapply (in_getAllBvectors r2).
      eapply getSupport_In_Seq.
      rewrite H0.
      unfold negb.
      eauto.
      rewrite H0.
      simpl.
      intuition.
    Qed.

    eapply inSupportRandomPerm_bad; eauto.
    
    comp_simp.

    eapply H0; intuition; unfold fst.
    eapply well_formed_perm_cons; intuition.
    rewrite H3.
    trivial.
    rewrite H5.
    trivial.
    eapply well_formed_perm_cons; eauto.
    simpl.
    rewrite H3.
    trivial.
    simpl.
    rewrite H5.
    trivial.      

    unfold snd.
    eapply getSupport_In_evalDist.
    intuition.
    eapply getSupport_In_evalDist.
    eapply (@inSupportRandomPerm (Bvector n) (Bvector n)).

    simpl.
    eapply filter_In.
    split.
    eapply H8.
    
    instantiate (1:=a).
    rewrite H5.
    rewrite H6.
    trivial.
    rewrite H3.
    eauto.

    rewrite randomPerm_eq_unroll.
    trivial.
    simpl in H1.
    trivial.

     Theorem inSupportRandomPerm_bad_1 : 
      forall a b r1,
        In r1 (getSupport (getUnusedBvector a)) ->
        a # b = None ->
        In ((b, r1) :: a, r1) (getSupport (randomPerm_bad (a, b))).
      
      intuition.
      unfold randomPerm_bad.
      rewrite H0.
      eapply getSupport_In_Seq.
      simpl.
      eapply (in_getAllBvectors r1).
      eapply getSupport_In_Seq.
      erewrite getUnusedR_not_inRange.
      simpl.
      intuition.
      eauto.
      eauto.
      erewrite getUnusedR_not_inRange.
      simpl.
      intuition.
      eauto.
      eauto.
    Qed.

     eapply inSupportRandomPerm_bad_1; eauto.
     simpl.
     eapply filter_In.
     split.
     eapply in_getAllBvectors.  
     rewrite H6.
     trivial.

  Qed.

  
  Lemma filter_eq : forall (A : Set)(ls : list A)(P1 P2 : A -> bool),
    (forall a, In a ls -> P1 a = P2 a) ->
    filter P1 ls = filter P2 ls.
    
    induction ls; intuition; simpl in *.
    rewrite (H a); intuition.
    destruct (P2 a).
    f_equal.
    eapply IHls; intuition.
    eapply IHls; intuition.
  Qed.


  Lemma randomPerm_bad_preserves_bad : forall ls ls' v r,
    checkBad ls = true ->
    In (ls', r) (getSupport (randomPerm_bad (ls, v))) ->
    checkBad ls' = true.

    intuition.
    unfold randomPerm_bad in *.
    case_eq (ls # v); intuition;
      rewrite H1 in H0.
    simp_in_support.
    trivial.
    repeat simp_in_support.
    simpl.
    rewrite H.
    eapply orb_true_r.
    case_eq (inRange _ ls x); intuition.
    simpl.
    rewrite H.
    rewrite orb_true_r.
    eapply orb_true_r.
    simpl.
    rewrite H.
    eapply orb_true_r.

  Qed.

  Definition randomFunc_Bvector := @randomFunc (Bvector n) _ _ _ (Rnd n).

  Lemma randomFunc_preserves_bad : forall ls ls' v r,
    checkBad ls = true ->
    In (ls', r) (getSupport (randomFunc_Bvector (ls, v))) ->
    checkBad ls' = true.

    intuition.
    unfold randomFunc_Bvector, randomFunc in *.
    case_eq (ls # v); intuition;
      rewrite H1 in H0.
    simp_in_support.
    trivial.

    repeat simp_in_support.
    simpl.
    rewrite H.
    eapply orb_true_r.

  Qed.

  Lemma perm_func_bad_spec : 
    comp_spec 
      (fun p1 p2 => checkBad (fst p1) = true /\ checkBad (fst p2) = true /\ well_formed_Bvector_perm (fst p2)) 
      (fun p1 p2 => checkBad (fst p1) = true /\ checkBad (fst p2) = true /\ well_formed_Bvector_perm (fst p2))
      (randomFunc_Bvector) 
      randomPerm_bad.

    intuition.
    unfold comp_spec.
    intuition.
    
    unfold randomFunc_Bvector, randomFunc, randomPerm_bad.
    destruct d2.
    case_eq (a # b); intuition; case_eq (l # b0); intuition.

    comp_simp.
    eapply H2; intuition.
    unfold randomFunc_Bvector, randomFunc.
    rewrite H4.
    simpl.
    intuition.
    unfold randomPerm_bad.
    rewrite H5.
    simpl.
    intuition.
    
    inline_first.
    comp_irr_r; wftac.
    inline_first.
    case_eq (inRange _ l x); intuition; unfold negb.
    comp_irr_r; wftac.
    comp_simp.
    eapply H2; intuition.

    simpl.
    destruct (eqbBvector x0 x); intuition.
    unfold fst.
    eapply well_formed_perm_cons_2; intuition.

    unfold randomFunc_Bvector, randomFunc.
    rewrite H4.
    simpl.
    intuition.
    
    eapply inSupportRandomPerm_bad; eauto.

    comp_simp.
    eapply H2; intuition.
    unfold fst.
    simpl.
    simpl in H0.
    rewrite H0.
    eapply orb_true_r.
    unfold fst in *.
    eapply well_formed_perm_cons; intuition.

    unfold randomFunc_Bvector, randomFunc.
    rewrite H4.
    simpl.
    intuition.
    eapply inSupportRandomPerm_bad_1; eauto.
    simpl.
    eapply filter_In.
    intuition.
    rewrite H7.
    trivial.

    comp_simp.
    inline_first.
    comp_irr_l.
    wftac.
    eapply H2; intuition.
    simpl in *.
    rewrite H1.
    eapply orb_true_r.

    eapply inSupportRandomFunc;
    trivial.

    unfold randomPerm_bad.
    rewrite H5.
    simpl.
    intuition.

    inline_first.
    comp_skip.
    inline_first.
    case_eq (inRange _ l r2); intuition; unfold negb.
    comp_irr_r; wftac.
    comp_simp.
    eapply H2; intuition.
    simpl in *.
    rewrite H1.
    eapply orb_true_r.
    
    simpl.
    destruct (eqbBvector x r2); intuition.
    simpl.
    eapply well_formed_perm_cons_2; intuition.

    eapply inSupportRandomFunc; trivial.
    eapply inSupportRandomPerm_bad; trivial.

    comp_simp.
    eapply H2; intuition.
    simpl in *.
    rewrite H1.
    eapply orb_true_r.
    simpl in *.
    rewrite H0.
    eapply orb_true_r.
    eapply well_formed_perm_cons; intuition.

    eapply inSupportRandomFunc; trivial.
    eapply inSupportRandomPerm_bad_1; trivial.
    simpl.
    eapply filter_In; intuition.
    rewrite H6.
    trivial.

  Qed.

  Lemma perm_func_not_bad_spec : 
    let s1 := (fun p1 p2 => checkBad (fst p1) = false /\ checkBad (fst p2) = false /\ snd p1 = snd p2 /\ (forall v, (fst p1) # v = ((fst p2) # v)) /\ (forall r, inRange  _ (fst p1) r = inRange _ (fst p2) r) /\ well_formed_Bvector_perm (fst p2)) in
    comp_spec 
    s1 
    (fun p1 p2 => s1 p1 p2 \/ (checkBad (fst p1) = true /\ checkBad (fst p2) = true /\ well_formed_Bvector_perm (fst p2)))
    (randomFunc_Bvector)
    randomPerm_bad.

    unfold comp_spec; intuition.

    unfold randomFunc_Bvector, randomFunc, randomPerm_bad.
    simpl in H2.
    subst.
    destruct d2.
    unfold snd.
    simpl in H3.
    rewrite H3.
    case_eq (l # b); intuition.
    comp_simp.
    eapply H5; intuition.

    simpl.
    rewrite H3.
    rewrite H2.
    simpl.
    intuition.

    simpl.
    rewrite H2.
    simpl.
    intuition.

    inline_first.
    comp_skip.
    inline_first.
    case_eq (inRange _ l r2); intuition; unfold negb.
    comp_irr_r; wftac.
    comp_simp.
    eapply H5; intuition.
    right.
    intuition.
    simpl.
    simpl in H4.
    rewrite H4.
    rewrite H7.
    eapply orb_true_l.
    simpl.
    case_eq (eqbBvector x r2); intuition.
    eapply well_formed_perm_cons_2; intuition.

    eapply inSupportRandomFunc; trivial.
    simpl.
    rewrite H3.
    trivial.

    eapply inSupportRandomPerm_bad; trivial.
    
    comp_simp.
    eapply H5; intuition.
    left; intuition.

    simpl in *.
    rewrite H4.
    rewrite H7.
    rewrite H1.
    trivial.
    simpl in *.

    rewrite H7.
    rewrite H0.
    trivial.

    simpl.
    rewrite H3.
    trivial.

    simpl.
    rewrite H4.
    trivial.

    unfold fst.
    eapply well_formed_perm_cons; intuition.

    eapply inSupportRandomFunc; trivial.
    simpl.
    rewrite H3.
    trivial.

    eapply inSupportRandomPerm_bad_1; trivial.
    simpl.
    eapply filter_In.
    intuition.
    rewrite H7.
    trivial.
  Qed.

  
  Definition randomFunc_eager(p: (list (Bvector n * Bvector n)) * Bvector n) : Comp (list (Bvector n * Bvector n) * Bvector n) :=
    let (f, d) := p in
    r <-$ {0, 1}^n;
    f' <- f ++ (d, r) :: nil;
    match f # d with
      | None => ret (f', r) 
      | Some r => ret (f', r)
    end.

  Lemma checkBad_permutation : forall ls1 ls2,
    Permutation ls1 ls2 ->
    checkBad ls1 = checkBad ls2.

    induction 1; intuition; simpl in *.
    rewrite IHPermutation.
    erewrite inRange_permutation.
    eauto.
    trivial.

    case_eq (eqbBvector b0 b); intuition.
    apply eqbBvector_sound in H. subst.
    rewrite eqbBvector_complete.
    simpl.
    trivial.
    case_eq (eqbBvector b b0); intuition.
    apply eqbBvector_sound in H0.
    subst.
    rewrite eqbBvector_complete in H.
    discriminate.
    destruct (inRange _ l b0).
    destruct (inRange _ l b).
    simpl.
    trivial.
    simpl.
    trivial.

    simpl.
    trivial.
    eauto.
  Qed.

  Lemma checkBad_app_cons : forall ls d r,
    checkBad (ls ++ (d, r) :: nil) = checkBad ((d , r) :: ls).

    intuition.
    symmetry.
    eapply checkBad_permutation.
    eapply Permutation_cons_append.
  Qed.

  Lemma checkBad_app : forall ls ls',
    checkBad ls = true ->
    checkBad (ls ++ ls') = true.

    induction ls; intuition; simpl in *.
    apply orb_true_iff in H.
    intuition.
    rewrite inRange_app.
    simpl.
    trivial.
    trivial.
  Qed.

  Lemma randomFunc_eager_spec : 
    stateful_comp_spec  
      (fun s1 s2 => (checkBad s1 = true -> checkBad s2 = true) /\ (forall d, s1 # d = (s2 # d)) /\ forall r, inRange _ s1 r = true -> inRange _ s2 r = true) 
      (fun p1 p2 => snd p1 = snd p2) (fun p1 p2  => snd p1 = snd p2)
      (randomFunc_Bvector) 
      randomFunc_eager.

    intuition.
    unfold stateful_comp_spec, comp_spec.
    intuition.
    
    unfold randomFunc_Bvector, randomFunc, randomFunc_eager.
    simpl in H1.
    subst.
    destruct d2.
    simpl in H2.
    unfold snd.
    rewrite H2.

    inline_first.
    
    case_eq (l # b); intuition.
    comp_simp.
    inline_first.
    comp_irr_r; wftac.
    comp_simp.
    eapply H3; intuition.
    
    simpl in *.
    eapply checkBad_app; trivial.
    simpl.
    erewrite arrayLookup_app_some; eauto.
    simpl in *.
    rewrite inRange_app_cons.
    simpl.
    case_eq (eqbBvector r x); intuition.

    simpl.
    rewrite H2.
    rewrite H1.
    simpl.
    intuition.

    Theorem inSupportRandomFunc_eager_Some : 
      forall l a r b,
        l # a = Some b ->
        In (l ++ (a, r) :: nil, b) (getSupport (randomFunc_eager (l, a))).

      intuition.
      unfold randomFunc_eager.
      eapply getSupport_In_Seq.
      simpl.
      eapply in_getAllBvectors.
      rewrite H.
      unfold setLet.
      simpl.
      intuition.
    Qed.

    Theorem inSupportRandomFunc_eager_None : 
      forall l a r,
        l # a = None ->
        In (l ++ (a, r) :: nil, r) (getSupport (randomFunc_eager (l, a))).

      intuition.
      unfold randomFunc_eager.
      eapply getSupport_In_Seq.
      simpl.
      eapply in_getAllBvectors.
      rewrite H.
      unfold setLet.
      simpl.
      intuition.
    Qed.


    eapply inSupportRandomFunc_eager_Some.
    trivial.

    inline_first.
    comp_skip.
    
    comp_simp.
    eapply H3; intuition.
    simpl in *.
    rewrite checkBad_app_cons.
    simpl.
    apply orb_true_iff in H5.
    intuition.
    
    simpl.
    case_eq (eqbBvector d b); intuition.
    apply eqbBvector_sound in H5.
    subst.
    rewrite arrayLookup_app_some_eq; trivial.
   
    rewrite arrayLookup_app_none; trivial.
    simpl.
    rewrite H5.
    intuition.

    simpl in *.
    case_eq (eqbBvector r r2); intuition.
    rewrite H8 in H5.
    apply eqbBvector_sound in H8.
    subst.
    rewrite inRange_app_cons.
    simpl.
    rewrite eqbBvector_complete.
    trivial.
    eapply inRange_app.
    rewrite H8 in H5.
    intuition.

    eapply inSupportRandomFunc; trivial.
    simpl.
    rewrite H2.
    trivial.

    eapply inSupportRandomFunc_eager_None; trivial.
    

  Qed.

  Lemma randomFunc_eager_bad_eq : 
    stateful_comp_spec  
      (fun s1 s2 => (checkBad s1 = checkBad s2) /\ (forall r, inRange _ s1 r = inRange _ s2 r)) 
      (fun p1 p2 => True) (fun p1 p2 => True)
      randomFunc_eager 
      randomFunc_eager.

    intuition.
    unfold stateful_comp_spec, comp_spec.
    intuition.
    
    unfold randomFunc_eager.
    comp_simp.
    inline_first.
    comp_skip.
    case_eq (a # b); intuition;
    case_eq (l # b0); intuition;
    comp_simp;
    eapply H2; intuition;

    try match goal with
        | [|- _ = _ ] => simpl in *; repeat rewrite checkBad_app_cons; 
                                          repeat rewrite inRange_app_cons; simpl;
                                          repeat rewrite H3; repeat rewrite H0; intuition
        | [|- In (?a ++ (?b, ?r) :: nil, ?r) (getSupport (randomFunc_eager (?a, ?b))) ] =>
          eapply inSupportRandomFunc_eager_None; trivial
        | [|- In (?a ++ (?b, ?r) :: nil, _) (getSupport (randomFunc_eager (?a, ?b))) ] =>
          eapply inSupportRandomFunc_eager_Some; trivial
        end.

  Qed.

  Lemma filter_NoDup_perm : forall (A : Set)(eqd: eq_dec A) u ls,
    NoDup ls ->
    NoDup u ->
    (forall a, In a ls -> In a u) ->
    Permutation (filter (fun a => if (in_dec eqd a ls) then true else false) u) ls.
    
    induction u; intuition; simpl in *.
    destruct ls.
    econstructor.
    specialize (H1 a); simpl in *.
    intuition.
    
    inversion H0; clear H0; subst.
    destruct (in_dec eqd a ls).
    symmetry.
    eapply perm_trans.
    eapply (removeFirst_permutation eqd).
    eauto.
    eapply perm_skip.
    eapply Permutation_sym.
    erewrite filter_eq.
    eapply IHu; intuition.
    eapply removeFirst_NoDup.
    trivial.
    specialize (H1 a0).
    intuition.
    edestruct H1.
    eapply removeFirst_in_iff.
    eauto.
    subst.
    exfalso.
    eapply removeFirst_NoDup_not_in.
    eapply H.
    eauto.
    trivial.
    intuition.
    destruct (in_dec eqd a0 ls).
    destruct (in_dec eqd a0 (removeFirst eqd ls a)).
    trivial.
    exfalso.
    destruct (eqd a a0); subst.
    intuition.
    eapply n0.
    eapply removeFirst_in; eauto.
    destruct (in_dec eqd a0 (removeFirst eqd ls a)).
    exfalso.
    eapply removeFirst_not_in; eauto.
    trivial.
    
    eapply IHu; intuition.
    specialize (H1 a0); intuition.
    subst.
    intuition.
  Qed.

  Lemma randomFunc_eager_wf : forall ls d,
    well_formed_comp (randomFunc_eager (ls, d)).
    
    intuition.
    unfold randomFunc_eager.
    wftac.
    intuition.
    destruct (ls # d); wftac.
    
    
  Qed.
  
  Lemma randomFunc_eager_preserves_bad : forall ls d ls' r,
    In (ls', r) (getSupport (randomFunc_eager (ls, d))) ->
    checkBad ls = true ->
    checkBad ls' = true.
    
    intuition.
    unfold randomFunc_eager in *.
    simp_in_support.
    case_eq (ls # d); intuition;
    rewrite H in H2;
    simp_in_support.
    rewrite checkBad_app_cons; simpl.
    rewrite H0.
    eapply orb_true_r.
    rewrite checkBad_app_cons; simpl.
    rewrite H0.
    eapply orb_true_r.
    
  Qed.

  (*************************************************************************************)
  (*----------------------  PRP-PRF Switching Lemma Proof Begins Here -----------------*)
  (*************************************************************************************)

  Variable q : nat. (* number of queries *)
  Variable A : AdversaryWithOracle unit bool (Bvector n) (Bvector n) (list (Bvector n * Bvector n)).
  
  Definition PRF_G :=
    s_O <- (@nil (Bvector n * Bvector n));
    p <-$ (A queries (randomFunc_Bvector) ) q s_O tt; 
    ret fst p.

  Definition PRP_G :=
    s_O <- (@nil (Bvector n * Bvector n));
    p <-$ (A queries (randomPerm_Bvector)) q s_O tt;
    ret fst p.

  Definition PRP_PRF_Advantage :=
    | Pr[PRP_G] - Pr[PRF_G] |.


  Definition PRP_S1 :=
    s_O <- (@nil (Bvector n * Bvector n));
    p <-$ (A queries randomPerm_bad) q s_O tt;
    ret fst p.


  Definition PRP_S0 :=
    s_O <- (@nil (Bvector n * Bvector n));
    p <-$ (A queries randomPerm_unroll) q s_O tt;
    ret fst p.

  Theorem well_formed_Bvector_perm_nil : well_formed_Bvector_perm nil.

    unfold well_formed_Bvector_perm, well_formed_perm.
    intuition.
    econstructor.
    intuition.
    simpl.
    eapply in_getAllBvectors.
    trivial.
    
  Qed.
  
  Theorem Bvector_perms_eq_nil : Bvector_perms_eq nil nil.

    unfold Bvector_perms_eq, perms_eq.
    intuition.
    eapply well_formed_Bvector_perm_nil.
    eapply well_formed_Bvector_perm_nil.
    unfold funcs_eq.
    intuition.  
  Qed.

  Lemma PRP_G_eq_S0 : 
    Pr[PRP_G] == Pr[PRP_S0].

    unfold PRP_G, PRP_S0.

    eapply (A_query_inv _ _ _ _ well_formed_Bvector_perm); intuition.
    eapply well_formed_Bvector_perm_nil.
    eapply randomPerm_preserves_wf_pair; eauto.
    eapply randomPerm_unroll_preserves_wf_pair; eauto.
    eapply randomPerm_eq_unroll.
    trivial.
  Qed.

  Lemma PRP_S0_eq_S1 : 
    Pr[PRP_S0] == Pr[PRP_S1].

    unfold PRP_S0, PRP_S1.

    eapply (A_query_spec_eq _ _ randomPerm_unroll_bad_inv); intuition.
    eapply Bvector_perms_eq_nil.

    subst.
    simpl.
    intuition.
  Qed.
 
  Definition PRF_G_bad :=
    s_O <- nil;
    p <-$ (A queries (randomFunc_Bvector)) q s_O tt;
    ret (checkBad (snd p)).

  Definition PRP_S1_bad :=
    s_O <- nil;
    p <-$ (A queries randomPerm_bad) q s_O tt;
    ret (checkBad (snd p)).
 
  Lemma badness_same :
    Pr[PRF_G_bad] == Pr[PRP_S1_bad].

    intuition.
    unfold PRF_G_bad, PRP_S1_bad.

    eapply (A_query_spec_2_eq _ _ _ _ perm_func_not_bad_spec perm_func_bad_spec); intros; intuition.

    unfold fst.
    eapply well_formed_Bvector_perm_nil.

    simpl in *.
    rewrite H.
    rewrite H0.
    intuition.
    
    simpl in *.
    rewrite H.
    rewrite H0.
    intuition.

  Qed.

  Definition PRF_G_both :=
    s_O <- nil;
    p <-$ (A queries (randomFunc_Bvector)) q s_O tt;
    ret (fst p, checkBad (snd p)).

  Definition PRP_S1_both :=
    s_O <- nil;
    p <-$ (A queries randomPerm_bad) q s_O tt;
    ret (fst p, checkBad (snd p)).

  Lemma func_perm_eq_when_good : forall x,
    evalDist PRF_G_both (x, false) ==
    evalDist PRP_S1_both (x, false).

    intuition.
    eapply (A_query_spec_2_eq _ _ _ _ perm_func_not_bad_spec perm_func_bad_spec); intros; intuition.
    simpl.
    eapply well_formed_Bvector_perm_nil.
    unfold fst, snd.
    unfold fst in H0, H.
    rewrite H0.
    rewrite H.
    intuition.
    simpl in *.
    rewrite H0.
    rewrite H.
    destruct (EqDec_dec (pair_EqDec bool_EqDec bool_EqDec) (s_A1', true) (x, false)); destruct (EqDec_dec (pair_EqDec bool_EqDec bool_EqDec) (s_A2', true) (x, false)); intuition; pairInv.
  Qed.

  Lemma func_perm_close : forall x,
    | evalDist PRF_G x - evalDist PRP_S1 x | <= Pr[PRF_G_bad].

    intuition.
    eapply fundamental_lemma.
    eapply pair_EqDec.
    eapply bool_EqDec.
    eapply list_EqDec.
    eapply pair_EqDec;
    eapply Bvector_EqDec.
    eapply badness_same.

    eapply func_perm_eq_when_good.
  Qed.

  Definition PRF_eager_G_bad :=
    s_O <- nil; 
    p <-$ (A queries randomFunc_eager) q s_O tt; 
    ret checkBad (snd p).


  Lemma randomFunc_bad_le_eager : 
    Pr [PRF_G_bad] <= Pr [PRF_eager_G_bad].

    unfold PRF_G_bad, PRF_eager_G_bad.

    eapply (A_query_spec _ _ _ randomFunc_eager_spec); intuition.
    simpl.

    destruct (checkBad o1).
    rewrite H1.
    intuition.
    trivial.

    destruct (EqDec_dec bool_EqDec false true); try discriminate.
    eapply rat0_le_all.    

  Qed.

  Definition randomFunc_eager_loop :=
    s <-$ compLoop _ randomFunc_eager q nil (oneVector n);
    ret checkBad s.
  
  Lemma randomFunc_G_eq_loop : 
    Pr[PRF_eager_G_bad] == Pr[randomFunc_eager_loop].

    intuition.
    unfold PRF_eager_G_bad, randomFunc_eager_loop.
    eapply (runA_eq_compLoop _ _ randomFunc_eager_bad_eq); intuition.
    
    simpl.
    rewrite H0.
    intuition.
  Qed.

  Lemma checkBad_NoDup : forall ls,
    checkBad ls = false ->
    NoDup (map (@snd (Bvector n) (Bvector n)) ls).
    
    induction ls; intuition; simpl in *.
    econstructor.
    destruct a.
    apply orb_false_elim in H.
    intuition.
    econstructor.
    intuition.
    simpl in *.
    rewrite inRange_in_dec in H0.
    destruct (in_dec (EqDec_dec (Bvector_EqDec n)) b0 (map (snd (B:=Bvector n)) ls)).
    discriminate.
    intuition.
    trivial.
    
  Qed.
  
  Lemma compLoop_randomFunc_eager_le_bound: forall count s_O d,
    checkBad s_O = false ->
    Pr [p <-$ compLoop _ randomFunc_eager count s_O d; ret (checkBad p)] <= 
    if (checkBad s_O) then 1 else 
    ((count / 1) * (length s_O/ expnat 2 n) + (count * count / expnat 2 n)).

    induction count; intuition.

    unfold compLoop.
    comp_simp.
    comp_ute.
    eapply rat0_le_all.

    unfold compLoop.

    unfold randomFunc_eager.
    fold randomFunc_eager.
    inline_first.

    eapply trans.
    eapply (@evalDist_bind_case_split leRat _ (inRange _ s_O)
    (length s_O / expnat 2 n)
    1
    (count / 1 * (S (length s_O) / expnat 2 n) + count * count / expnat 2 n)
    bool (Rnd n)); intuition.
    wftac.
    
    simpl.
    rewrite sumList_factor_constant_l.
    (* there are (length ls) distinct elements in the list, so this must be true *)
    assert (sumList (getAllBvectors n)
     (fun a : Bvector n =>
      if EqDec_dec bool_EqDec (inRange _ s_O a) true then 1 else 0) == (length s_O / 1)).
    rewrite (sumList_filter_partition (inRange _ s_O)).
    eapply eqRat_trans.
    eapply ratAdd_eqRat_compat.
    eapply sumList_body_eq.
    intuition.
    apply filter_In in H0.
    intuition.
    destruct (EqDec_dec bool_EqDec (inRange _ s_O a) true).
    eapply eqRat_refl.
    congruence.
    eapply sumList_0.
    intuition.
    apply filter_In in H0.
    intuition.
    destruct (EqDec_dec bool_EqDec (inRange _ s_O a) true); intuition.
    rewrite e in H2.
    simpl in *.
    discriminate.
    
    rewrite sumList_body_const.
    rewrite ratMult_1_l.
    rewrite <- ratAdd_0_r.
    eapply eqRat_terms.
   
    erewrite filter_eq.
    Focus 2.
    intros.
    eapply inRange_in_dec.
    
    apply checkBad_NoDup in H.
    erewrite <- (map_length _ s_O).

    eapply Permutation_length.
    eapply filter_NoDup_perm; intuition.
    eapply getAllBvectors_NoDup.
    eapply in_getAllBvectors.
    trivial.

    rewrite H0.
    rewrite <- ratMult_num_den.
    eapply eqRat_terms.
    omega.
    unfold posnatMult, natToPosnat, posnatToNat.
    omega.  

    case_eq (s_O # d); intuition.

    comp_simp.
    comp_irr_l.

    specialize (compLoop_wf _ randomFunc_eager); intuition.
    eapply H2; intuition.
    eapply randomFunc_eager_wf.

    assert (checkBad x = true).
    eapply (@compLoop_inv _ _ _ _ _ (fun x => checkBad x = true)); intuition.
    eapply randomFunc_eager_preserves_bad.
    eauto.
    trivial.
    Focus 2.
    eauto.
    rewrite checkBad_app_cons.
    simpl.
    rewrite H0.
    trivial.
    simpl.
    destruct (EqDec_dec bool_EqDec (checkBad x) true); try congruence.
    intuition.
    
    comp_simp.
    comp_irr_l.
    specialize (compLoop_wf _ randomFunc_eager); intuition.
    eapply H2; intuition.
    eapply randomFunc_eager_wf.

    assert (checkBad x = true).
    eapply (@compLoop_inv _ _ _ _ _ (fun x => checkBad x = true)); intuition.
    eapply randomFunc_eager_preserves_bad.
    eauto.
    trivial.
    Focus 2.
    eauto.
    rewrite checkBad_app_cons.
    simpl.
    rewrite H0.
    trivial.
    simpl.
    destruct (EqDec_dec bool_EqDec (checkBad x) true); try congruence.
    intuition.

    case_eq (s_O # d); intuition.
    comp_simp.

    eapply trans.
    eapply IHcount.
    rewrite checkBad_app_cons.
    simpl; intuition.

    rewrite checkBad_app_cons.
    simpl.
    rewrite H0.
    rewrite H.
    simpl.
    rewrite app_length.
    simpl.
    rewrite plus_comm.
    simpl.
    intuition.

    comp_simp.
    eapply trans.
    eapply IHcount.
    rewrite checkBad_app_cons.
    simpl; intuition.
    rewrite checkBad_app_cons.
    simpl.
    rewrite H0.
    rewrite H.
    simpl.

    rewrite app_length.
    simpl.
    rewrite plus_comm.
    simpl.
    intuition.
    
    rewrite ratMult_1_r.
    eapply leRat_trans.
    eapply ratAdd_leRat_compat.
    eapply leRat_refl.
    eapply ratMult_leRat_compat.
    eapply ratSubtract_le.
    eapply leRat_refl.
    eapply leRat_refl.
    rewrite ratMult_1_l.
    repeat rewrite <- ratMult_num_den.
    assert (RatIntro (count * S (length s_O)) (posnatMult (pos 1) (pos expnat 2 n)) == count * S (length s_O) / expnat 2 n).
    eapply eqRat_terms.
    trivial.
    simpl.
    omega.
    rewrite H0.
    rewrite <- ratAdd_num.
    rewrite <- ratAdd_num.
    assert (RatIntro (S count * length s_O) (posnatMult (pos 1) (pos expnat 2 n)) == S count * length s_O / expnat 2 n).
    eapply eqRat_terms.
    trivial.
    simpl.
    omega.
    rewrite H.
    rewrite H1.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    rewrite <- ratAdd_num.
    eapply eqRat_refl.
    eapply leRat_num.
    simpl.
    rewrite mult_comm.
    simpl.
    rewrite (mult_comm count  (S count)).
    simpl.
    repeat rewrite plus_assoc.
    rewrite (mult_comm count (length s_O)).
    omega.

  Qed.

  Lemma randomFunc_eager_loop_le_bound :
    Pr[randomFunc_eager_loop] <= q * q / expnat 2 n.

    eapply leRat_trans.
    eapply compLoop_randomFunc_eager_le_bound.
    trivial.

    simpl.
    rewrite <- ratMult_num_den.
    rewrite mult_0_r.
    rewrite rat_num_0.
    rewrite <- ratAdd_0_l.
    intuition.

  Qed.


  (* note: bounds could be better *)
  Theorem PRP_PRF_Switching : PRP_PRF_Advantage <= (q * q / expnat 2 n).

    intuition.
    unfold PRP_PRF_Advantage.
    rewrite PRP_G_eq_S0.
    rewrite PRP_S0_eq_S1.
    rewrite ratDistance_comm.
    rewrite func_perm_close.
    rewrite randomFunc_bad_le_eager.
    rewrite randomFunc_G_eq_loop.
    eapply randomFunc_eager_loop_le_bound.
  Qed.

  Print Assumptions PRP_PRF_Switching.

End PRP_PRF.

(*
Section PRP_Cipher.

  Variable n : nat. 
  Variable k1 k2 : Bvector n.

  Local Open Scope vector_scope.
  Fixpoint eagerPerm_h(z : nat)(range : list (Bvector n)) : Comp (list (Bvector z * Bvector n)):=
    match z with
      | O => v <- Repeat ({0, 1}^n) (fun v => if (in_dec (@Bvector_eq_dec n) v range) then false else true);
        ret ((Vector.nil bool, v) :: nil)%list
      | S z' =>
        ls1 <- eagerPerm_h z' range;
        ls2 <- eagerPerm_h z' (range ++ (map (fun p => snd p) ls1));
        ls1' <-! (map (fun (p : Bvector z' * Bvector n) => (Vector.cons bool false z' (fst p), snd p)) ls1);
        ls2' <-! (map (fun (p : Bvector z' * Bvector n) => (Vector.cons bool true z' (fst p), snd p)) ls2);
        ret (ls1' ++ ls2')
    end.

  Definition eagerPerm :=
    eagerPerm_h n nil.


    match v with
      | Vector.nil => ret nil
      | b :: v' => 
        ls1 <- eagerPerm_h v';
        ls2 <- eagerPerm_h v';
        
    end.

  Definition perm := (@randomPerm n).

  Definition encrypt(s_perm : list (Bvector n * Bvector n))(m : Bvector n) := 
    p <- perm (s_perm, (BVxor n k1 m));
    ret (fst p, (BVxor n k2 (snd p))).

  (* We need the inverse permutation for this -- we can build it out of the one we have by swapping the order of the pairs in the list.  It might be easier to sample the entire permutation up front. *)

End PRP_Cipher.
*)