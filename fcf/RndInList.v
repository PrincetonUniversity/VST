(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.

Local Open Scope nat_scope.

Theorem qam_count_gen : 
  forall (A B C : Set)(c : OracleComp A B C)(q : nat),
    queries_at_most c q ->
    forall (S : Set)(count : S -> nat)(eqds : EqDec S)(o : S -> A -> Comp (B * S))(s : S)(n : nat),
      (forall a b x y,
        In (a, b) (getSupport (o x y)) ->
          count b <= n + (count x)) ->
      forall a b, 
      In (a, b) (getSupport (c _ _ o s)) ->
      count b <= q * n + (count s).
    
  Opaque getSupport.
  induction 1; intuition; simpl in *.

  (* Bind case *)
  repeat simp_in_support.
  destruct x.
  rewrite mult_plus_distr_r.
  pose proof H4.
  eapply (IHqueries_at_most _ count) in H4.
  eapply (H1 _ _ S count) in H5.
  rewrite H5.
  rewrite plus_comm.
  rewrite <- (plus_assoc).
  rewrite (plus_comm (q2 * n)).
  rewrite plus_assoc.
  eapply plus_le_compat.
  eauto.
  eapply le_refl.
  intuition.
  intuition.

  (* query case *)
  rewrite plus_0_r.
  eapply H; eauto.

  (* ret case *)
  Transparent getSupport.
  repeat simp_in_support.
  intuition.

  (* run case *)
  repeat simp_in_support.

  destruct x.
  simpl in *.

  specialize (IHqueries_at_most (S * S0)%type (fun p =>  count (snd p)) _ 
  (fun (x : S * S0) (y : A) =>
                p <-$ (oc (fst x) y) S0 eqds0 o (snd x);
                ret (fst (fst p), (snd (fst p), snd p)))
  (s, s0) (q2 * n)
  ).
  
  eapply le_trans.
  eapply IHqueries_at_most.
  intuition.
  simpl.
  repeat simp_in_support.
  destruct x.
  simpl in *.
  eapply H1.
  eauto.
  eauto.
  eauto.
  simpl.
  rewrite mult_assoc.
  intuition.

  (* trans case *)
  eapply le_trans.
  eapply IHqueries_at_most.
  eauto.
  eauto.
  eapply plus_le_compat; intuition.
  eapply mult_le_compat; intuition.

  Grab Existential Variables.
  repeat econstructor.
  eauto.

Qed.

Local Open Scope rat_scope.

Theorem evalDist_bind_event_le : 
  forall (A : Set)(c : Comp A)(f : A -> Comp bool)(evta : A -> bool) (k1 k2 : Rat),
    Pr[a <-$ c; ret (evta a)] <= k1 ->
    (forall a, In a (getSupport c) -> evta a = false -> Pr[f a] <= k2) ->
    Pr[a <-$ c; f a] <= k1 + k2.

  intuition.
  simpl in *.
  rewrite (sumList_partition evta).

  eapply ratAdd_leRat_compat.
  assert ( sumList (getSupport c)
     (fun a : A => evalDist c a * Pr  [f a ] * (if evta a then 1 else 0)) <=
            sumList (getSupport c)
        (fun b : A =>
         evalDist c b * (if EqDec_dec bool_EqDec (evta b) true then 1 else 0)) ).

  eapply sumList_le; intuition.
  destruct (EqDec_dec bool_EqDec (evta a) true ).
  rewrite e.

  eapply ratMult_leRat_compat; intuition.
  eapply leRat_trans.
  eapply ratMult_leRat_compat.
  eapply leRat_refl.
  eapply evalDist_le_1.
  rewrite ratMult_1_r.
  intuition.

  destruct (evta a); intuition.
  repeat rewrite ratMult_0_r.
  eapply rat0_le_all.
  rewrite H1.
  eapply H.

  assert ( sumList (getSupport c)
     (fun a : A => evalDist c a * Pr  [f a ] * (if evta a then 0 else 1)) <=
            sumList (getSupport c)
     (fun a : A => k2 * (evalDist c a * (if evta a then 0 else 1)))).

  eapply sumList_le.
  intuition.
  case_eq (evta a); intuition.
  eapply eqRat_impl_leRat.
  repeat rewrite ratMult_0_r.
  intuition.
  rewrite H0.
  eapply eqRat_impl_leRat.
  repeat rewrite ratMult_1_r.
  eapply ratMult_comm.
  trivial.
  trivial.

  rewrite H1.
  rewrite sumList_factor_constant_l.

  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply ratMult_1_r.
  }
  eapply ratMult_leRat_compat; intuition.
  
  
  assert (sumList (getSupport c)
     (fun a : A => evalDist c a * (if evta a then 0 else 1)) <=
          sumList (getSupport c)
     (fun a : A => evalDist c a)).

  eapply sumList_le.
  intuition.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply ratMult_1_r.
  }
  eapply ratMult_leRat_compat; intuition.
  destruct (evta a); intuition.
  eapply rat0_le_all.
  rewrite H2.
  eapply evalDist_sum_le_1.
Qed.

Theorem oc_eventProb : 
  forall (A B C : Set)(c : OracleComp A B C) n,
    queries_at_most c n ->
    forall
    (S : Set)(eqds : EqDec S)(o : S -> A -> Comp (B * S))
    (count : S -> nat)(evt : S -> bool)(s : S)(k : nat -> Rat) i,
      (forall (n1 n2 : nat), (n1 <= n2)%nat -> (k n1 <= k n2)) ->
      evt s = false ->
      (forall s a, evt s = false -> Pr[p <-$ o s a; ret (evt (snd p))] <= (k (i + (count s))%nat)) ->
      (forall s s' a b, In (b, s') (getSupport (o s a)) ->
                        count s' <= i + (count s))%nat ->
      Pr[p <-$ c _ _ o s; ret (evt (snd p))] <= (n / 1) * (k (i * n + (count s))%nat).

  Local Opaque evalDist.

  induction 1; intuition; simpl in *.
  inline_first.

  assert (
       Pr 
   [a <-$ c S eqds o s;
    p <-$ ([z, s']<-2 a; (f z) S eqds o s'); ret evt (snd p) ] <=
   q1 / 1 * k (i * q1 + count s)%nat + 
   q2 / 1 * k (i * q2 + (i * q1 + count s))%nat 
                     ).

  eapply evalDist_bind_event_le.
  eapply (@IHqueries_at_most _ _ _ count evt); intuition.
  intros.
  comp_simp.
  eapply leRat_trans.
  eapply (@H1 _ _ _ _ _ count evt).
  eapply H2.
  trivial.
  intuition.
  intuition.
  eapply ratMult_leRat_compat; intuition.
  eapply H2.
  eapply plus_le_compat; intuition.

  eapply le_trans.
  eapply (qam_count_gen _ _ _ _ _ i).
  intuition.
  eapply H5.
  eauto.
  eauto.
  rewrite mult_comm.
  intuition.

  rewrite H6.
  clear H6.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    rewrite ratAdd_num.
    eapply ratMult_distrib_r.
  }
  eapply ratAdd_leRat_compat;
  eapply ratMult_leRat_compat; intuition.
  eapply H2.
  rewrite mult_plus_distr_l.
  rewrite plus_comm.
  repeat rewrite <- plus_assoc.
  eapply plus_le_compat; intuition.

  rewrite H1; intuition.
  rewrite <- ratMult_1_l.
  eapply ratMult_leRat_compat; intuition.
  eapply leRat_terms; intuition.

  inline_first.
  eapply distro_irr_le.
  intuition.
  comp_simp.
  simpl.
  rewrite H0.
  rewrite evalDist_ret_0.
  eapply rat0_le_all.
  congruence.

  inline_first.

  assert (EqDec C).
  eapply oc_EqDec; intros.
  eapply c.
  assert (B * S).
  eapply oc_base_exists.
  eapply oc.
  trivial.
  trivial.
  intuition.
  assert (B' * S0).
  eapply comp_base_exists.
  eapply o.
  trivial.
  trivial.
  intuition.
  intuition.
  trivial.


  assert
    (
      (evalDist
        (Bind
           (c (prod S S0) (pair_EqDec eqds eqds0)
              (fun (x : prod S S0) (y : A) =>
               Bind ((oc (fst x) y) S0 eqds0 o (snd x))
                 (fun p : prod (prod B S) S0 =>
                  Ret (EqDec_dec (pair_EqDec eqdb (pair_EqDec eqds eqds0)))
                    (pair (fst (fst p)) (pair (snd (fst p)) (snd p)))))
              (pair s s0))
           (fun a : prod C (prod S S0) =>
            Bind
              (Ret
                 (EqDec_dec
                    (pair_EqDec
                       (pair_EqDec
                          (oc_EqDec c
                             (fun x : A =>
                              fst
                                (oc_base_exists (oc s x)
                                   (fun y : A' =>
                                    fst (comp_base_exists (o s0 y)))))
                             (fun x : A =>
                              EqDec_pair_l
                                (oc_EqDec (oc s x)
                                   (fun y : A' =>
                                    fst (comp_base_exists (o s0 y)))
                                   (fun y : A' =>
                                    EqDec_pair_l (comp_EqDec (o s0 y)) s0)) s))
                          eqds) eqds0))
                 (pair (pair (fst a) (fst (snd a))) (snd (snd a))))
              (fun p : prod (prod C S) S0 =>
               Ret (EqDec_dec bool_EqDec) (evt (snd p))))) true)
   ==
   Pr 
   [a <-$
    c (S * S0)%type (pair_EqDec eqds eqds0)
      (fun (x : S * S0) (y : A) =>
       p <-$ (oc (fst x) y) S0 eqds0 o (snd x);
       ret (fst (fst p), (snd (fst p), snd p))) (s, s0);
     ret (evt (snd (snd a))) ]
   ).

  comp_skip.
  simpl.
  intuition.
  rewrite H7.
  clear H7.

  
  eapply leRat_trans.
  eapply (@IHqueries_at_most _ _ 
                             ((fun (x : S * S0) (y : A) =>
       p <-$ (oc (fst x) y) S0 eqds0 o (snd x);
       ret (fst (fst p), (snd (fst p), snd p))))
                             (fun p => count (snd p)) (fun p => evt (snd p))
         _ (fun x => q2 / 1 * k (x)%nat) (i * q2)%nat).
  intuition.
  eapply ratMult_leRat_compat; intuition.
  trivial.
  intuition.
  
  comp_inline_l.
  assert (
      Pr 
   [a1 <-$ (oc (fst (a, b)) a0) S0 eqds0 o (snd (a, b));
    p <-$ ret (fst (fst a1), (snd (fst a1), snd a1)); ret evt (snd (snd p)) ]
   ==
   Pr 
   [a1 <-$ (oc (fst (a, b)) a0) S0 eqds0 o (snd (a, b));
    ret evt (snd a1) ]
   ).


  comp_skip.
  simpl.
  intuition.
  rewrite H8.
  clear H8.
  simpl.
  eapply leRat_trans.

  eapply (@H1 ); intuition.
  reflexivity.
  intuition.
  repeat simp_in_support.
  destruct x.
  simpl in *.
  rewrite mult_comm.
  eapply qam_count_gen.
  eapply H0.
  intuition.
  eapply H5.
  eapply H7.
  eapply H8.
  simpl.
  rewrite <- ratMult_assoc.
  eapply ratMult_leRat_compat; intuition.
  eapply eqRat_impl_leRat.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms; intuition.
  eapply H2.
  eapply plus_le_compat; intuition.
  rewrite <- mult_assoc.
  eapply mult_le_compat; intuition.
  rewrite mult_comm.
  intuition.

  rewrite IHqueries_at_most.
  eapply ratMult_leRat_compat; intuition.
  eapply leRat_terms; intuition.
  intuition.
  trivial.
  intuition.
  intuition.

  Grab Existential Variables.
  trivial.

  repeat econstructor; eauto.

Qed.

Theorem oc_eventProb_0_1 : 
  forall (S : Set)(count : S -> nat)(evt : S -> bool)(k : nat -> Rat)
         (A B C : Set)(c : OracleComp A B C) n,
    queries_at_most c n ->
    forall
    (eqds : EqDec S)(o : S -> A -> Comp (B * S))
    (s : S),
      (forall (n1 n2 : nat), (n1 <= n2)%nat -> (k n1 <= k n2)) ->
      evt s = false ->
      (forall s a, evt s = false -> Pr[p <-$ o s a; ret (evt (snd p))] <= (k (1 + (count s))%nat)) ->
      (forall s s' a b, In (b, s') (getSupport (o s a)) ->
                        count s' <= 1 + (count s))%nat ->
      count s = 0%nat ->
      Pr[p <-$ c _ _ o s; ret (evt (snd p))] <= (n / 1) * (k n).  

  intuition.
  eapply leRat_trans.
  eapply oc_eventProb; intuition.
  eauto.
  rewrite H4.
  rewrite mult_1_l.
  rewrite plus_0_r.
  intuition.
Qed.

Local Open Scope nat_scope.



Theorem qam_count : 
  forall (A B C : Set)(c : OracleComp A B C)(q : nat),
    queries_at_most c q ->
    forall (S : Set)(count : S -> nat)(eqds : EqDec S)(o : S -> A -> Comp (B * S))(s : S),
      (forall a b x y,
        In (a, b) (getSupport (o x y)) ->
          count b <= 1 + (count x)) ->
      count s = 0 ->
      forall a b, 
      In (a, b) (getSupport (c _ _ o s)) ->
      count b <= q.

  intuition.
  eapply le_trans.
  eapply qam_count_gen; eauto.
  omega.

Qed.

Local Transparent evalDist.

Section RndInList.
  
  Variable eta : nat.

  Theorem RndInList_prob_h :
    forall (ls : list (Bvector eta)),
      (Pr[r <-$ {0, 1}^eta;
        ret (if (in_dec (EqDec_dec _) r ls) then true else false)
      ] <= (length ls) / 2 ^ eta)%rat.

    induction ls; intuition.
    simpl.
    eapply eqRat_impl_leRat.
    eapply eqRat_trans.
    eapply sumList_0.
    intros.
    destruct ( EqDec_dec bool_EqDec false true); intuition.
    eapply ratMult_0_r.
    symmetry.
    eapply rat_num_0.

    simpl in *.

    rewrite (sumList_filter_partition (eqb a)).
    eapply leRat_trans.
    eapply ratAdd_leRat_compat.
    eapply sumList_le.
    intros.
    destruct (EqDec_dec (Bvector_EqDec eta) a a0 ); subst.
    destruct ( EqDec_dec bool_EqDec true true).
    eapply eqRat_impl_leRat.
    eapply ratMult_1_r.
    intuition.
    apply filter_In in H.
    intuition.
    rewrite eqb_leibniz in H1.
    exfalso.
    intuition.

    eapply leRat_refl.

    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.

      symmetry.
      eapply rat_num_S.
    }
    eapply ratAdd_leRat_compat.
    rewrite (@sumList_exactly_one _ a).
    eapply leRat_refl.
    eapply filter_NoDup.
    eapply getAllBvectors_NoDup.
    eapply filter_In.
    intuition.
    eapply in_getAllBvectors.
    eapply eqb_refl.
    intuition.
    eapply filter_In in H.
    intuition.
    rewrite eqb_leibniz in H2.
    subst.
    intuition.
    
    eapply leRat_trans.
    2:{
      eapply IHls.
    }

    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      eapply (sumList_filter_partition (fun b => negb (eqb a b))).
    }

    rewrite ratAdd_0_r.
    eapply ratAdd_leRat_compat.
    eapply sumList_le.
    intuition.
    eapply ratMult_leRat_compat.
    intuition.
    apply filter_In in H.
    intuition.
    destruct (EqDec_dec (Bvector_EqDec eta) a a0 ).
    subst.
    rewrite eqb_refl in H1.
    simpl in *. discriminate.
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) a0 ls); intuition.
    
    eapply rat0_le_all.
  Qed.

  Theorem RndInList_prob :
    forall (ls : list (Bvector eta))(q : nat),
      length ls <= q ->
      (Pr[r <-$ {0, 1}^eta;
        ret (if (in_dec (EqDec_dec _) r ls) then true else false)
      ] <= q / 2 ^ eta)%rat.

    intuition.
    eapply leRat_trans.
    eapply RndInList_prob_h.
    eapply leRat_terms; intuition.

  Qed.
  
End RndInList.

Local Open Scope rat_scope.

Theorem RndNat_eq_any : 
  forall (eta : nat)(x : Bvector eta),
    Pr  [a0 <-$ { 0 , 1 }^eta; ret (eqb x a0) ] == 1 / 2^eta.

  intuition.
  simpl.
  rewrite (@sumList_exactly_one _ x).
  rewrite eqbBvector_complete.
  destruct (EqDec_dec bool_EqDec true true); intuition.
  rewrite ratMult_1_r.
  reflexivity.
  eapply getAllBvectors_NoDup.
  apply in_getAllBvectors.

  intuition.
  destruct (EqDec_dec bool_EqDec (eqbBvector x b) true); intuition.
  apply eqbBvector_sound in e.
  intuition.
  eapply ratMult_0_r.

Qed.

Require Import fcf.CompFold.
Local Opaque evalDist.

Section FixedInRndList.
  
  Variable A : Set.
  Variable eta : nat.

  Theorem FixedInRndList_prob :
    forall (ls : list A)(x : Bvector eta),
      (Pr[lsR <-$ compMap _ (fun _ => {0, 1}^eta) ls; ret (if (in_dec (EqDec_dec _) x lsR) then true else false)
      ] <= (length ls) / 2 ^ eta)%rat.

    induction ls; intuition.
    simpl.
    comp_simp.
    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition.

    simpl.
    inline_first.
    eapply leRat_trans.
    eapply (evalDist_bind_event_le _ _ (fun z => eqb x z)).
    eapply eqRat_impl_leRat.
    apply RndNat_eq_any.
    intuition.
    
    assert (Pr 
   [lsR <-$
    (lsb' <-$ compMap (Bvector_EqDec eta) (fun _ : A => { 0 , 1 }^eta) ls;
     ret (a0 :: lsb')%list);
    ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) x lsR then true else false)
   ] ==
            Pr 
   [lsR <-$ compMap (Bvector_EqDec eta) (fun _ : A => { 0 , 1 }^eta) ls;
    ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) x lsR then true else false)
   ]).

    inline_first.
    comp_skip.

    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x (a0 :: x0)).
    simpl in i.
    intuition; subst.
    rewrite eqb_refl in *.
    discriminate.
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x x0); intuition.
    simpl in n; intuition.
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x x0); intuition.

    rewrite H1.
    rewrite IHls.
    reflexivity.
    
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      cutrewrite (S (length ls) = 1 + (length ls))%nat.
      apply ratAdd_num.
      trivial.
    }
    reflexivity.
  Qed.
  
End FixedInRndList.


Section RndInAdaptive.

  Variable A B C : Set.
  
  Local Open Scope rat_scope.

  Theorem orb_prob : 
    forall (A B : Set)(c : Comp A)(f : A -> Comp B) evt1 evt2 k1 k2,
      Pr[x <-$ c; ret (evt1 x)] <= k1 ->
      (forall a, In a (getSupport c) -> evt1 a = false -> Pr[y <-$ f a; ret (evt2 y)] <= k2) ->
      Pr[x <-$ c; y <-$ f x; ret (evt1 x || evt2 y)] <= k1 + k2.

    intuition.
    rewrite evalDist_seq_step.
    rewrite (sumList_partition evt1).
    eapply ratAdd_leRat_compat.

    Transparent evalDist.
    simpl in H.
    eapply leRat_trans.
    2:{
      eapply H.
    }
    eapply sumList_le.
    intuition.
    rewrite ratMult_assoc.
    eapply ratMult_leRat_compat.
    intuition.

    case_eq (evt1 a); intuition.
    rewrite ratMult_1_r.
    eapply leRat_trans.
    eapply distro_irr_le.
    intros.
    rewrite orb_true_l.
    simpl.
    destruct (EqDec_dec bool_EqDec true true ).
    eapply leRat_refl.
    intuition.
    destruct (EqDec_dec bool_EqDec true true); intuition.
    
    destruct (EqDec_dec bool_EqDec false true); intuition.
    discriminate.
    rewrite ratMult_0_r; intuition.

    assert ( sumList (getSupport c)
   (fun a : A0 =>
    evalDist c a * Pr  [y <-$ f a; ret evt1 a || evt2 y ] *
    (if evt1 a then 0 else 1)) <=
     sumList (getSupport c)
   (fun a : A0 =>
    evalDist c a *
    (if evt1 a then 0 else 1) * k2)).
    eapply sumList_le; intuition.
    case_eq (evt1 a); intuition.
    repeat rewrite ratMult_0_r.
    eapply eqRat_impl_leRat.
    symmetry.
    apply ratMult_0_l.
    repeat rewrite ratMult_1_r.
    eapply ratMult_leRat_compat; intuition.

    rewrite H1.
    clear H1.
    rewrite sumList_factor_constant_r.
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      eapply ratMult_1_l.
    }
    eapply ratMult_leRat_compat; intuition.
    assert ( sumList (getSupport c)
   (fun a : A0 => evalDist c a * (if evt1 a then 0 else 1)) <=
    sumList (getSupport c)
   (fun a : A0 => evalDist c a)).
    eapply sumList_le.
    intuition.
    destruct (evt1 a); intuition.
    rewrite ratMult_0_r.
    eapply rat0_le_all.
    rewrite ratMult_1_r.
    intuition.
    rewrite H1. clear H1.
    eapply evalDist_sum_le_1.
  Qed.    

  Theorem RndInAdaptive_prob : 
    forall (c : OracleComp A B C)(q : nat),
      queries_at_most c q ->
      forall (S : Set)(evt : S -> bool)(eqd : EqDec S)(o : S -> A -> Comp (B * S))(k : Rat),
        (forall a b, 
          evt a = false ->
          Pr[ d <-$ o a b; ret (evt (snd d))] <= k)->
        (forall a b x y,
          In (a, b) (getSupport (o x y)) -> evt x = true -> evt b = true) ->
        forall (s : S),
          evt s = false ->
          Pr[ d <-$ c _ _ o s; ret (evt (snd d))] <= q / 1 * k.

    induction 1; intuition.

    Opaque evalDist.
    simpl.

    assert ( Pr 
   [d <-$ (z0 <-$ c S eqd o s; [z, s']<-2 z0; (f z) S eqd o s');
    ret evt (snd d) ] ==
    Pr 
   [a <-$ c S eqd o s;
    d <-$ (f (fst a)) S eqd o (snd a); 
    ret (evt (snd a) || evt (snd d)) ]).

    inline_first.
    comp_skip.
    comp_simp.
    comp_skip.
    simpl.
    intuition.
    simpl.
    destruct x; simpl in*.
    case_eq (evt s0); intuition.
    assert (evt s1 = true).
    eapply oc_comp_invariant_f;
    eauto.
    rewrite H8.
    simpl; intuition.
    rewrite orb_false_l.
    intuition.
    
    rewrite H5.
    clear H5.
    

    assert (Pr 
   [a <-$ c S eqd o s;
    d <-$ (f (fst a)) S eqd o (snd a); ret evt (snd a) || evt (snd d) ] <=
   q1 / 1 * k + q2 / 1 * k).
    eapply orb_prob.
   
    eapply IHqueries_at_most;
    eauto.
    intros.
    eapply H1; eauto.

    destruct a; repeat econstructor; eauto.

    rewrite H5.
    eapply eqRat_impl_leRat.
    rewrite ratAdd_den_same.
    rewrite ratMult_distrib_r.
    intuition.

    (* Query case *)
    Opaque evalDist.
    simpl.
    rewrite H; intuition.
    eapply eqRat_impl_leRat.
    symmetry.
    eapply ratMult_1_l.

    (* Ret case *)
    simpl.
    inline_first.
    comp_at comp_ret leftc 1%nat.
    simpl.
    Transparent evalDist.
    simpl.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    eapply sumList_0.
    intuition.
    rewrite H1.
    destruct (EqDec_dec bool_EqDec false true).
    discriminate.
    eapply ratMult_0_r.
    eapply rat0_le_all.

    (* Run case *)
    Opaque evalDist.
    assert (A -> B).
    intuition.
    assert (B * S).
    eapply oc_base_exists; eauto.
    intuition.
    assert (B' * S0).
    eapply comp_base_exists; eauto.
    intuition.
    intuition.
    
    assert (EqDec C).
    eapply oc_EqDec; eauto.
  
    simpl.

    specialize (IHqueries_at_most (S * S0)%type (fun p => evt (snd p)) _ (fun (x : S * S0) (y : A) =>
        p <-$ (oc (fst x) y) S0 eqd o (snd x);
        ret (fst (fst p), (snd (fst p), snd p)))  (q2 / 1 * k)).
 
    inline_first.
    comp_at comp_ret leftc 1%nat.
 
    eapply leRat_trans.
    eapply IHqueries_at_most.

    intuition.
    simpl in H7.
    inline_first.
    simpl.
    comp_at comp_ret leftc 1%nat.
    
    eapply H1; eauto.
    intuition.
    simpl.
    repeat simp_in_support.
    destruct x.
    simpl.
    eapply oc_comp_invariant_f; eauto.
    trivial.

    rewrite <- ratMult_assoc.
    eapply ratMult_leRat_compat; intuition.
    rewrite <- ratMult_num_den.
    eapply eqRat_impl_leRat.
    eapply eqRat_terms; intuition.

    (* trans case *)
    eapply leRat_trans.
    eapply IHqueries_at_most; eauto.
    eapply ratMult_leRat_compat; intuition.
    eapply leRat_terms; intuition.

  Qed.


End RndInAdaptive.
   