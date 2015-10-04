(* A theory of constructed functions and permutations, including random functions and random permutations. *)

Set Implicit Arguments.
Require Import Crypto.
Require Import Permutation.
Require Import CompFold. 
Require Export Array.

Local Open Scope list_scope.
Local Open Scope array_scope.

Require Import State.

Definition oracleMap(D R S: Set)(eqds : EqDec S)(eqdr : EqDec R)(oracle : (S * D) -> Comp (S * R))(s : S)(ds : list D) :=
  compFold _ (fun acc d => [s, rs] <-2 acc; [s, r] <-$2 oracle (s, d); ret (s, rs ++ r :: nil)) (s, nil) ds.

Section RandomFunc.

  Variable D R : Set.
  Hypothesis D_EqDec : EqDec D.
  Hypothesis R_EqDec : EqDec R.

  Variable RndR : Comp R.
  Hypothesis RndR_wf : well_formed_comp RndR.

  (* A random function *)
  Definition randomFunc(p : (list (D * R)) * D) : Comp (list (D * R) * R) :=
    let (f, d) := p in
    match (arrayLookup _ f d) with
      | None => (r <-$ RndR; ret ((d, r) :: f, r))
      | Some r => ret (f, r)
    end.  
  Lemma randomFunc_wf : forall p, 
    well_formed_comp (randomFunc p).

    intuition.
    unfold randomFunc.
    case_eq (a#b); intuition; wftac.

  Qed.

  (* Eager random functions can be used to simplify many definitions. *)
  Fixpoint randomFunc_eager_arr(allD : list D) :=
    match allD with
        | nil => ret nil
        | d :: allD' =>
          arr' <-$ randomFunc_eager_arr allD';
            r <-$ RndR;
            ret ((d, r) :: arr')
    end.
    

  Hint Resolve randomFunc_wf : wftac.

  Theorem inSupportRandomFunc : 
    forall a b r,
      a # b = None ->
      In r (getSupport RndR) ->
      In ((b, r) :: a, r) (getSupport (randomFunc (a, b))).
    
    intuition.
    unfold randomFunc.
    rewrite H.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.

  Qed.

  Section PRF.

    Variable eta : nat.
    Variable f : Bvector eta -> D -> R.
    Variable A : AdversaryWithOracle unit bool D R (list (D * R)).
    Variable q : nat.

    Definition f_oracle (k : Bvector eta)(p : (list (D * R)) * D) : Comp ((list (D * R)) * R) :=
      [s, d] <-2 p;
      ret (nil, f k d).

    Definition PRF_G0 :=
      k <-$ {0, 1} ^ eta;
      [b, _] <-$2 (A queries (f_oracle k)) q nil tt;
      ret b.

    Definition PRF_G1 :=
      [b, _] <-$2 (A queries randomFunc) q nil tt;
      ret b.

    Definition PRF_Advantage := | Pr[PRF_G0] - Pr[PRF_G1] |.

  End PRF.
  (* A PRF that is secure against a non-adaptive adversary. *)
  Section PRF_NA.

    Variable eta : nat.
    Variable f : Bvector eta -> D -> R.

    Section PRF_NA_Adversary.
      Variable A_state : Set.
      Variable A1 : Comp ((list D) * A_state ).
      Variable A2 : A_state -> list R -> Comp bool.
      Definition A := (A1, A2).
      
      Definition PRF_NA_G0 :=
        lsD <-& A;
        lsR <-$ (k <-$ {0, 1} ^ eta; ret (map (f k) lsD));
        A lsR.

      Definition PRF_NA_G1 :=
        lsD <-& A;
        [_, lsR] <-$2 oracleMap _ _ randomFunc nil lsD;
        A lsR.

      Definition PRF_NA_Advantage := 
      | Pr[PRF_NA_G0] - Pr[PRF_NA_G1] |.   

    End PRF_NA_Adversary.

    Variable efficient : forall(x : Type), x -> Prop.
      
    Definition PRF_NA_Assumption epsilon :=
      forall A_state A1 A2,
        efficient A1 ->
        efficient A2 -> 
        @PRF_NA_Advantage A_state A1 A2 <= epsilon.
      
  End PRF_NA.


  (* An iterated PRF security definition.  The adversary supplies several lists of PRF inputs.  The definition chooses a new random key for each list.  *)
  Section PRF_NAI.

    Variable eta : nat.
    Variable f : Bvector eta -> D -> R.
    Variable A_state : Set.
    Variable A1 : Comp ((list (list D)) * A_state ).
    Variable A2 : A_state -> list (list R) -> Comp bool.

    Definition PRF_NAI_G0 :=
      [lsDs, s_A] <-$2 A1;
      lsRs <-$ compMap _ (fun lsD => k <-$ {0, 1}^eta; ret (map (f k) lsD)) lsDs;
      A2 s_A lsRs.

    Definition PRF_NAI_G1 :=
      [lsDs, s_A] <-$2 A1;
      lsRs <-$ compMap _ (fun lsD => [_, lsR] <-$2 oracleMap _ _ randomFunc nil lsD; ret lsR) lsDs;
      A2 s_A lsRs.

    Definition PRF_NAI_Advantage := 
    | Pr[PRF_NAI_G0] - Pr[PRF_NAI_G1] |.   

                         
  End PRF_NAI.
  

End RandomFunc.

Section RandomPerm.

  Variable D R : Set.
  Hypothesis D_EqDec : EqDec D.
  Hypothesis R_EqDec : EqDec R.

  Variable RndR : Comp R.
  Hypothesis RndR_wf : well_formed_comp RndR.

  Fixpoint inRange(f : list (D * R))(r : R) :=
    match f with
      | nil => false
      | (d', r') :: f' => 
        if (eqb r r') then true
          else (inRange f' r)
    end.

  Definition getUnusedR(f : list (D * R)) :=
    Repeat (RndR) (fun r => negb (inRange f r)).

  Lemma getUnusedR_eq : forall ls1 ls2 x,
    (forall r, inRange ls1 r = inRange ls2 r) ->
    evalDist (getUnusedR ls1) x == evalDist (getUnusedR ls2) x.
    
    intuition.

    destruct (in_dec (EqDec_dec _) x (getSupport (getUnusedR ls1))).
    unfold getUnusedR in *.    
    
    simpl in i.
    apply filter_In in i; intuition.
    eapply evalDist_Repeat_eq.
    intuition.
    rewrite H.
    trivial.
    eapply filter_In; intuition.
    eapply sumList_permutation.
    eapply NoDup_Permutation.
    eapply filter_NoDup.
    eapply getSupport_NoDup.
    eapply filter_NoDup.
    eapply getSupport_NoDup.
    intuition.
    apply filter_In in H2; intuition.
    eapply filter_In; intuition.
    rewrite <- H.
    trivial.
    apply filter_In in H2; intuition.
    eapply filter_In; intuition.
    rewrite H.
    trivial.
    
    unfold getUnusedR in *.
    simpl in n.
    apply filter_not_In in n.
    intuition.
    simpl.
    rewrite getSupport_not_In_evalDist_h; intuition.
    repeat rewrite ratMult_0_r.
    intuition.
    
    simpl.
    unfold indicator.
    rewrite <- H.
    rewrite H0.
    repeat rewrite ratMult_0_l.
    intuition.
    
  Qed.

  Lemma inRange_map : forall ls x,
    inRange ls x = true -> 
    In x (map (@snd D R) ls).
    
    induction ls; intuition; simpl in *.
    discriminate.
    case_eq (eqb x b); intuition.
    rewrite eqb_leibniz in H0.
    subst.
    intuition.
    
    right.
    eapply IHls.
    rewrite H0 in H.
    trivial.
  Qed.


  Lemma getUnusedR_wf : forall ls r,
    inRange ls r = false ->
    In r (getSupport RndR) ->
    well_formed_comp (getUnusedR ls).

    intuition.
    unfold getUnusedR.
    eapply (well_formed_Repeat _ _ r).
    wftac.
 
    eapply filter_In.
    intuition.
    rewrite H.
    simpl.
    trivial.

    Grab Existential Variables.
    unfold eq_dec; intuition.
    eapply (EqDec_dec _).
  Qed.
  Hint Resolve getUnusedR_wf : wftac.
  

  (* A random permutation *)
  Definition randomPerm(p : (list (D * R) *  D)) : Comp (list (D * R) * R) :=
    let (f, d) := p in 
    match (f#d) with
      | None => (r <-$ getUnusedR f ; ret ((d, r) :: f, r))
      | Some r => ret (f, r)
    end.

  Lemma randomPerm_wf : forall ls b0, 
    (forall x, ls#x = None -> exists r, inRange ls r = false /\ In r (getSupport RndR)) ->
    well_formed_comp (randomPerm (ls, b0)).

    intuition.
    unfold randomPerm.
    case_eq (ls#b0); intuition; wftac.
    edestruct H; eauto.
    intuition.
    wftac.
  Qed.

  (* Many proofs involving random permutations will need to query the random permutation repeatedly.  In order to show that each call to the permutation is well-formed, we need to preserve the invariant that the state of the permutation is actually a permutation (as opposed to an arbitrary function).  The well_formed_perm is the predicate that we will use for this invariant. *)
  Definition well_formed_perm ls := 
    forall lsd, 
      NoDup lsd ->
      (forall d, In d lsd -> ls#d = None) -> 
      exists lsr, 
        (forall r, In r lsr -> inRange ls r = false /\ In r (getSupport RndR)) /\ 
        NoDup lsr /\
        length lsd = length lsr.

  (*
  Lemma well_formed_perm_nil : well_formed_perm nil.
    
    intuition.
    unfold well_formed_perm.
    intuition.
    econstructor.
    intuition.
    eapply H1.
    eapply getSupport_NoDup.
    
    exists lsd.
    intuition.

  Qed.
*)

  Lemma well_formed_perm_1 : forall ls,
    well_formed_perm ls ->
    forall d, 
    ls#d = None ->
    exists r, inRange ls r = false /\ In r (getSupport RndR).

    intuition.
    specialize (H (d :: nil)).
    edestruct H.
    econstructor.
    simpl. intuition.
    econstructor.
    intuition.
    simpl in *.
    intuition. subst.
    trivial.

    intuition.
    destruct x.
    simpl in *.
    omega.
    destruct x; simpl in *.
    econstructor.
    eapply H2.
    intuition.
    omega.
  Qed.
  Hint Resolve well_formed_perm_1 : wftac.


  Lemma removeFirst_length : forall (A : Set)(eqd : eq_dec A)(ls : list A) a,
    In a ls ->
    S (length (removeFirst eqd ls a)) = length ls.
    
    induction ls; intuition; simpl in *.
    intuition.
    subst.
    f_equal.
    destruct (eqd a0 a0).
    trivial.
    congruence.
    destruct (eqd a0 a); subst.
    trivial.
    simpl.
    f_equal.
    eauto.
  Qed.

  Lemma well_formed_perm_cons : forall ls d r,
    well_formed_perm ls ->
    ls#d = None ->
    inRange ls r = false ->
    well_formed_perm ((d, r) :: ls).

    unfold well_formed_perm in *.
    intuition.
    destruct (in_dec (EqDec_dec _) d lsd).
    specialize (H3 d).
    intuition.
    simpl in *.
    rewrite eqb_refl in H4.
    discriminate.

    edestruct (H (d :: lsd)).
    econstructor; trivial.
    intuition.
    simpl in *.
    intuition. subst.
    trivial.
    specialize (H3 d0).
    intuition.
    destruct (eqb d0 d).
    discriminate.
    trivial.

    intuition.
    (* now I have |lsd| + 1 unique elements that are not in the range *)
    (* but r may be in there *)
    destruct (in_dec (EqDec_dec _) r x).
    (* r is in the list, take it out and we get a list of the correct length *)
    exists (removeFirst (EqDec_dec _) x r).
    intuition.
    simpl.
    case_eq (eqb r0 r); intuition.
    rewrite eqb_leibniz in H8.
    subst.
    exfalso.
    eapply removeFirst_NoDup_not_in.
    eapply H4.
    eapply H6.
    eapply H5.
    eapply removeFirst_in_iff.
    eauto.
    eapply H5.
    eapply removeFirst_in_iff.
    eauto.

    eapply removeFirst_NoDup.
    trivial.

    simpl in H7.
    eapply eq_add_S.
    rewrite H7.
    symmetry.
    eapply removeFirst_length.
    trivial.

    (* r is not in the list, just use the tail of it *)
    destruct x.
    simpl in *. omega.
    exists x.
    intuition.
    simpl in *.
    intuition.
    case_eq (eqb r1 r); intuition.
    exfalso.
    rewrite eqb_leibniz in H10.
    subst.
    intuition.
    eapply H5.
    right.
    trivial.
    eapply H5.
    simpl.
    intuition.
    inversion H4; clear H4; subst.
    trivial.
  Qed.

  Lemma well_formed_perm_cons_2 : forall ls d r1 r2,
    well_formed_perm ls ->
    inRange ls r2 = true ->
    ls#d = None ->
    well_formed_perm ((d, r1) :: (d, r2) :: ls).
    
    intuition.
    unfold well_formed_perm.
    intuition.
    destruct (in_dec (EqDec_dec _) d lsd).
    specialize (H3 d).
    intuition.
    simpl in *.
    rewrite eqb_refl in H4.
    discriminate.
    edestruct (H (d :: lsd)).
    econstructor; trivial.
    intuition.
    simpl in H4.
    intuition. subst.
    trivial.

    specialize (H3 d0).
    intuition.
    simpl in *.
    destruct (eqb d0 d).
    discriminate.
    trivial.
    
    intuition.
    destruct (in_dec (EqDec_dec _) r1 x).
    exists (removeFirst (EqDec_dec _) x r1).
    intuition.
    simpl.
    case_eq (eqb r r1); intuition.
    rewrite eqb_leibniz in H8.
    subst.
    exfalso.
    eapply removeFirst_NoDup_not_in.
    eapply H4.
    eauto.
    case_eq (eqb r r2); intuition.
    rewrite eqb_leibniz in H9.
    subst.
    assert (inRange ls r2 = false).
    eapply H5.
    eapply removeFirst_in_iff.
    eauto.
    congruence.
    eapply H5.
    eapply removeFirst_in_iff.
    eauto.
    eapply H5.
    eapply removeFirst_in_iff.
    eauto.
    eauto using removeFirst_NoDup.
    eapply eq_add_S.
    simpl in H7.
    rewrite H7.
    symmetry.
    eapply removeFirst_length.
    trivial.
    
    destruct x.
    simpl in *.
    omega.
    exists x.
    intuition.
    simpl in *.
    case_eq (eqb r0 r1); intuition.
    rewrite eqb_leibniz in H8.
    subst.
    intuition.
    case_eq (eqb r0 r2); intuition.
    rewrite eqb_leibniz in H11.
    subst.
    assert (inRange ls r2 = false).
    eapply H5.
    intuition.
    congruence.
    eapply H5.
    intuition.
    eapply H5.
    simpl.
    intuition.
    inversion H4; clear H4; subst.
    trivial.
  Qed.

  Lemma getUnusedR_preserves_wf : forall ls d r,
    well_formed_perm ls ->
    ls#d = None ->
    In r (getSupport (getUnusedR ls)) -> 
    well_formed_perm ((d, r) :: ls).

    intuition.
    unfold getUnusedR in *.
    simpl in H1.
    apply filter_In in H1.
    intuition.

    eapply well_formed_perm_cons; eauto.
    destruct (inRange ls r); simpl in *; congruence.

  Qed.

  
  Lemma getUnusedR_ret_preserves_wf : forall ls ls' d r,
    well_formed_perm ls ->
    ls#d = None ->
    In (ls', r) (getSupport (r <-$ getUnusedR ls; ret ((d, r) :: ls, r))) -> 
    well_formed_perm ls'.

    intuition.
    apply getSupport_Bind_In in H1.
    destruct H1.
    intuition.
    simpl in H3.
    intuition.
    inversion H1; clear H1; subst.
    eapply getUnusedR_preserves_wf; eauto.

  Qed.
 

  Lemma randomPerm_preserves_wf : forall ls d ls' r,
    well_formed_perm ls ->
    In (ls', r) (getSupport (randomPerm (ls, d))) ->
    well_formed_perm ls'.
    
    intuition.
    unfold randomPerm in *.
    case_eq (ls#d); intuition.
    rewrite H1 in H0.
    simpl in *.
    intuition.
    inversion H2; clear H2; subst.
    trivial.

    rewrite H1 in H0.
    eapply getUnusedR_ret_preserves_wf; eauto.
  Qed.

  Lemma randomPerm_preserves_wf_pair : forall ls d p,
    well_formed_perm ls ->
    In p (getSupport (randomPerm (ls, d))) ->
    well_formed_perm (fst p).

    intuition.
    destruct p.
    eapply randomPerm_preserves_wf; eauto.

  Qed.


  Lemma getUnusedR_not_inRange : forall ls d r,
    ls#d = None -> 
    In r (getSupport (getUnusedR ls)) ->
    inRange ls r = false.

    intuition.
    unfold getUnusedR in *.
    simpl in *.
    eapply filter_In in H0.
    intuition.
    destruct (inRange ls r); intuition.
  Qed.

  Lemma funcLookup_inRange_true : forall s d r,
    s#d = Some r ->
    inRange s r = true.

    induction s; intuition; simpl in *.
    discriminate.
    
    case_eq (eqb d a0); intuition;
    rewrite H0 in H.
    inversion H; clear H; subst.
    rewrite eqb_refl.
    trivial.

    case_eq (eqb r b); intuition.
    eauto.

  Qed.

  Lemma inRange_permutation : forall ls1 ls2 r,
    Permutation ls1 ls2 ->
    inRange ls1 r = inRange ls2 r.

    induction 1; intuition; simpl in *.
    rewrite IHPermutation.
    trivial.
    case_eq (eqb r b0); intuition.
    rewrite eqb_leibniz in H.
    subst.
    destruct (eqb b0 b); intuition.

    eauto.
    
  Qed.

  Lemma inRange_app_cons : forall ls d r x,
    inRange (ls ++ (d, r) :: nil) x = inRange ((d , r) :: ls) x.

    intuition.
    symmetry.
    eapply inRange_permutation.
    eapply Permutation_cons_append.
  Qed.

  Lemma inRange_app : forall ls ls' r,
    inRange ls r = true ->
    inRange (ls ++ ls') r = true.

    induction ls; intuition; simpl in *.
    case_eq (eqb r b); intuition.
    eapply IHls.
    rewrite H0 in H.
    trivial.
  Qed.

  Lemma notInArrayLookupNone : 
    forall (A B : Set)(eqd : EqDec A)(arr : Array A B) a,
      (~ In a (fst (unzip arr))) ->
      (arr # a) = None.
    
    induction arr; intuition; simpl in *.
    
    case_eq (eqb a a0); intuition.
    rewrite eqb_leibniz in H0.
    subst.
    intuition.
    
  Qed.

  Ltac hypInv :=
      try (match goal with
          | [H: Some _ = Some _ |-_ ] => inversion H; clear H; subst
      end); try pairInv.


  Lemma arrayLookup_Some_In_unzip : 
  forall (A B : Set)(eqd : EqDec A)(arr : Array A B) a b,
    (arr # a) = Some b ->
    In a (fst (unzip arr)).
  
  induction arr; intuition; simpl in *.
  discriminate.
  
  case_eq (eqb a a0); intuition;
  rewrite H0 in *.
  hypInv.
  rewrite eqb_leibniz in H0.
  subst.
  intuition.
  
  right.
  eapply IHarr.
  eauto.
  
Qed.

  (*
  Lemma funcLookup_app_some_eq : forall ls d (v : R),
    ls#d = None ->
    (ls ++ (d, v) :: nil)#d = Some v.
    
    intuition.
    eapply arrayLookup_app_some_eq.
    eauto.
    
  Qed.

  Lemma funcLookup_app_none : forall ls d d' (v' : R),
    ls#d = None ->
    (ls ++ (d, v') :: nil) # d' = (((d, v') :: ls)#d').

    intuition.
    eapply arrayLookup_app_none; eauto.

  Qed.

  Lemma funcLookup_app_ne : forall ls d (r : R) d',
    d <> d' ->
    (ls ++ (d, r) :: nil)#d' = (ls#d').
    
    intuition.
    eapply arrayLookup_app_ne; eauto.
    
  Qed.
  
  Lemma funcLookup_app_some : forall ls d d' (v v' : R),
    ls#d = Some v ->
    (ls ++ (d, v') :: nil)#d' = (ls#d').

    intuition.
    eapply arrayLookup_app_some.
    eauto.
  Qed.
*)

  Lemma inRange_in_dec : forall ls r,
    inRange ls r = if (in_dec (EqDec_dec _) r (map (@snd D R) ls)) then true else false.
    
    induction ls; intuition; simpl in *.
    destruct (EqDec_dec R_EqDec b r); subst.
    rewrite eqb_refl.
    trivial.
    case_eq (eqb r b); intuition.
    rewrite eqb_leibniz in H.
    subst.
    intuition.
    exfalso.
    intuition.
    specialize (IHls r).
    destruct (in_dec (EqDec_dec R_EqDec) r (map (snd (B:=R)) ls)).
    trivial.
    trivial.
  Qed.

  Theorem inSupportRandomPerm : 
    forall a b r,
      In r (getSupport (getUnusedR a)) ->
      a # b = None ->
      In ((b, r) :: a, r) (getSupport (randomPerm (a, b))).
    
    intuition.
    unfold randomPerm.
    rewrite H0.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.

  Qed.


  (* Equivalence of functions and permutations. *)
  Definition funcs_eq s1 s2 :=
    (forall d, s1#d = (s2#d)) /\
    (forall r, inRange s1 r = inRange s2 r).
  
  Definition perms_eq s1 s2 :=
    well_formed_perm s1 /\
    well_formed_perm s2 /\
    funcs_eq s1 s2.

  (*
  Lemma perms_eq_nil : perms_eq nil nil.
    
    unfold perms_eq.
    intuition.
    eapply well_formed_perm_nil.
    eapply well_formed_perm_nil.
    unfold funcs_eq.
    intuition.
  Qed.
*)

  (* Eager random permutations can be used to simplify many definitions. *)
  Fixpoint randomPerm_eager_arr(allD : list D) :=
    match allD with
        | nil => ret nil
        | d :: allD' =>
          arr' <-$ randomPerm_eager_arr allD';
            r <-$ getUnusedR arr';
            ret ((d, r) :: arr')
    end.

End RandomPerm.