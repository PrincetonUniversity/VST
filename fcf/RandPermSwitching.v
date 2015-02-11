
Set Implicit Arguments.

Require Import FCF.
Require Import PRF.
Require Import RndInList.

Local Open Scope list_scope.

Inductive in_oc_supp : forall (A B C : Set), C -> OracleComp A B C -> Prop :=
| in_oc_supp_Bind : 
    forall (A B C C' : Set)(c : OracleComp A B C')(f : C' -> OracleComp A B C) x y,
      in_oc_supp x c ->
      in_oc_supp y (f x) ->
      in_oc_supp y (OC_Bind c f)
| in_oc_supp_Query : 
    forall (A B : Set)(a : A)(b : B),
      in_oc_supp b (OC_Query B a)
| in_oc_supp_Ret : 
  forall (A B C : Set)(c : Comp C) x,
    In x (getSupport c) ->
    in_oc_supp x (OC_Ret A B c)
| in_oc_supp_Run : 
  forall (A A' B B' C S : Set)(eqds : EqDec S)(eqda : EqDec A)(eqdb : EqDec B)
    (c : OracleComp A B C)(oc : S -> A -> OracleComp A' B' (B * S)) s x s',
    in_oc_supp x c ->
    in_oc_supp (x, s') (OC_Run _ _ _ c oc s).

Theorem in_oc_supp_complete : 
  forall (A B C : Set){eqdc : EqDec C}(c : OracleComp A B C) x
    (S : Set)(eqds : EqDec S)(o : S -> A -> Comp (B * S))(s : S) s',
    In (x, s') (getSupport (c _ _ o s)) ->
    in_oc_supp x c .
  
  induction c; intuition; repeat simp_in_support.
  econstructor.

  Local Opaque getSupport.
  simpl in *.
  repeat simp_in_support.
  destruct x.
  simpl.
  destruct p.
  simpl.
   
  econstructor.
  eapply (@IHc _ _ (S * S0)%type).
  eapply H1.

  simpl in *.
  repeat simp_in_support.
  econstructor.
  intuition.
  
  assert (EqDec C).
  eapply oc_EqDec.
  eapply c.
  intuition.
  assert (B * S).
  eapply comp_base_exists.
  eapply o0.
  trivial.
  intuition.
  intuition.
  intuition.
  assert (EqDec (B * S)).
  eapply comp_EqDec.
  eapply o0; trivial.
  eapply EqDec_pair_l.
  eapply H2.
  trivial.

  simpl in *.
  repeat simp_in_support.
  destruct x0.
  econstructor.
  eapply (@H0 _ S).
  eapply H2.
  eapply (@H _ _ _ S).
  eapply H3.

  Grab Existential Variables.
  eapply EqDec_pair_l.
  eauto.
  trivial.

Qed.
    
Local Open Scope nat_scope.

Inductive queries_at_most' : forall (A B C : Set), OracleComp A B C -> nat -> Prop :=
| qam_Bind : 
  forall (A B C C' : Set)(eqdc' : EqDec C')(c : OracleComp A B C')(f : C' -> OracleComp A B C) q1 q2,
    queries_at_most' c q1 ->
    (forall c', 
       in_oc_supp c' c ->
       queries_at_most' (f c') q2) ->
    queries_at_most' (OC_Bind c f) (q1 + q2)
| qam_Query : 
  forall (A B : Set)(a : A),
  queries_at_most' (OC_Query B a) 1
| qam_Ret : 
  forall (A B C : Set)(c : Comp C),
    queries_at_most' (OC_Ret A B c) 0
| qam_Run :
  forall (A A' B B' C S : Set)(eqds : EqDec S)(eqda : EqDec A)(eqdb : EqDec B)
    (c : OracleComp A B C)(oc : S -> A -> OracleComp A' B' (B * S)) s q1 q2,
    queries_at_most' c q1 ->
    (forall s a, queries_at_most' (oc s a) q2) ->
    queries_at_most' (OC_Run _ _ _ c oc s) (q1 * q2)
| qam_le : 
  forall (A B C : Set)(c : OracleComp A B C) q1 q2,
    queries_at_most' c q1 ->
    q1 <= q2 ->
    queries_at_most' c q2.

Theorem qam_count_gen' : 
  forall (A B C : Set)(c : OracleComp A B C)(q : nat),
    queries_at_most' c q ->
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
  eapply (IHqueries_at_most' _ count) in H4.
  eapply (H1 _ _ _ count) in H5.
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

  specialize (IHqueries_at_most' (S * S0)%type (fun p =>  count (snd p)) _ 
  (fun (x : S * S0) (y : A) =>
                p <-$ (oc (fst x) y) S0 eqds0 o (snd x);
                ret (fst (fst p), (snd (fst p), snd p)))
  (s, s0) (q2 * n)
  ).
  
  eapply le_trans.
  eapply IHqueries_at_most'.
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
  eapply IHqueries_at_most'.
  eauto.
  eauto.
  eapply plus_le_compat; intuition.
  eapply mult_le_compat; intuition.

  Grab Existential Variables.
  eapply in_oc_supp_complete; eauto.

Qed.

(*
Definition countOracle{A B State : Set}{eqdb : EqDec B}{eqds : EqDec State}(defB : B)(o : State -> A -> Comp (B * State)) p a :=
  [s, n] <-2 p;
  match n with
    | 0 => ret (defB, p)
    | S n' =>
      [b', s'] <-$2 o s a;
        ret (b', (s', n'))
  end.

Theorem countOracle_equiv : 
  forall (A B C : Set)(defB : B)(eqdb : EqDec B)(eqdc : EqDec C)(c : OracleComp A B C) n,
    queries_at_most' c n ->
    forall (S : Set)(eqd : EqDec S)(o : S -> A -> Comp (B * S))(s : S),
      comp_spec 
        (fun a b => fst a = fst b /\ snd a = fst (snd b))
        (c _ _ o s)
        (c _ _ (countOracle defB o) (s, n)).

  induction 1; intuition; simpl in *.

  admit.
  admit.
  admit.

  comp_skip.
  admit.
  admit.
  assert (EqDec C).
  eapply EqDec_pair_l.
  eauto.
  trivial.

  assert (B * S).
  eapply oc_base_exists.
  eapply oc

  specialize (@IHqueries_at_most' eqdb0 H2 defB (S * S0)%type).
  eapply H1.
  eapply oc_comp_spec_eq.

Qed.
          
*)

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
  Focus 2.
  eapply eqRat_impl_leRat.
  eapply ratMult_1_r.
  eapply ratMult_leRat_compat; intuition.
  
  
  assert (sumList (getSupport c)
     (fun a : A => evalDist c a * (if evta a then 0 else 1)) <=
          sumList (getSupport c)
     (fun a : A => evalDist c a)).

  eapply sumList_le.
  intuition.
  eapply leRat_trans.
  Focus 2.
  eapply eqRat_impl_leRat.
  eapply ratMult_1_r.
  eapply ratMult_leRat_compat; intuition.
  destruct (evta a); intuition.
  eapply rat0_le_all.
  rewrite H2.
  eapply evalDist_sum_le_1.
Qed.

Theorem oc_eventProb : 
  forall (A B C : Set)(c : OracleComp A B C) n,
    queries_at_most' c n ->
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
  eapply (@IHqueries_at_most' _ _ _ count evt); intuition.
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

  Require Import RndInList.
  eapply le_trans.
  eapply (qam_count_gen' _ _ _ _ _ i).
  intuition.
  eapply H5.
  eauto.
  eauto.
  rewrite mult_comm.
  intuition.

  rewrite H6.
  clear H6.
  
  eapply leRat_trans.
  Focus 2.
  eapply eqRat_impl_leRat.
  symmetry.
  rewrite ratAdd_num.
  eapply ratMult_distrib_r.
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
  eapply (@IHqueries_at_most' _ _ 
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
  eapply qam_count_gen'.
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

  rewrite IHqueries_at_most'.
  eapply ratMult_leRat_compat; intuition.
  eapply leRat_terms; intuition.
  intuition.
  trivial.
  intuition.
  intuition.

  Grab Existential Variables.
  trivial.
  eapply in_oc_supp_complete; eauto.

Qed.

Theorem oc_eventProb_0_1 : 
  forall (S : Set)(count : S -> nat)(evt : S -> bool)(k : nat -> Rat)
         (A B C : Set)(c : OracleComp A B C) n,
    queries_at_most' c n ->
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

(*
Definition maxCount_o(D R S : Set){eqdr : EqDec R}{eqds : EqDec S}(count : S -> nat)(o : S -> D -> Comp (R * S))
           (defR : R)(m : nat)(s : S)(d : D) :=
  if (ge_dec (count s) m) then (ret (defR, s)) else
    o s d.

Theorem maxCount_o_equiv : 
    forall (D R C: Set)(A : OracleComp D R C) (n1: nat),
      queries_at_most A n1 ->
      forall (S : Set)(count : S -> nat)(o : S -> D -> Comp (R * S))(defR : R)(eqdr : EqDec R)(eqds : EqDec S)(RndR : Comp R) s x n2,
        (n1 + (count s) <= n2)%nat ->
        evalDist (A _ _ o s) x ==
        evalDist (A _ _ (maxCount_o count o defR n2) s) x.
  
  Local Opaque evalDist.
  induction 1; intuition; simpl in *.

  comp_skip.
  comp_simp.
  eapply H1.

  specialize (qam_count_gen H (fun (p : list (A * B)) => length p) _ (randomFunc RndR eqdd) ls); intuition.
  eapply le_trans.
  eapply plus_le_compat.
  eapply le_refl.
  eapply H4.
  intuition; simpl in *.
  unfold randomFunc in *.
  destruct (arrayLookup eqdd x y); repeat simp_in_support.
  omega.
  simpl.
  assert ( (S (length x) <= 1+ length x)%nat).
  omega.
  eapply H5.
  eapply H3.
  omega.

  unfold randomFunc, randomFunc_max.
  destruct (arrayLookup eqdd ls a).
  eapply evalDist_ret_eq; intuition.
  comp_skip.
  destruct (ge_dec (length ls) n2).
  omega.
  eapply evalDist_ret_eq; intuition.

  eapply eqRat_refl.

  comp_skip.
  remember (map 

  eapply (@IHqueries_at_most _ _ RndR ls.

  trivial.
  

  erewrite H4.


  Print RndInList.

  rewrite <- H2.
  eapply plus_le_compat; intuition.
  omega.
  
Qed.
*)

Section RandPermSwitching.
  
  Variable A D R : Set.
  Variable RndR : Comp R.
  Hypothesis RndR_wf : well_formed_comp RndR.
  
  Variable A2 : OracleComp D R bool.
  

  Hypothesis eqdd : EqDec D.
  Hypothesis eqdr : EqDec R.

  Variable fBad : list (D * R) -> D -> R -> bool.
  Variable badProb : nat -> Rat.
  Hypothesis badProb_mono : forall n1 n2, (n1 <= n2)%nat -> badProb n1 <= badProb n2.


  Hypothesis A2_wf : well_formed_oc A2.
  Variable A2_queries : nat.
  Hypothesis A2_queries_correct : queries_at_most' A2 A2_queries.
  Hypothesis badProb_correct :
    forall d f,
      Pr [r <-$ RndR;
           ret (fBad f d r)] <= badProb (S (length f)).

   Hypothesis goodExists :
    forall d f,
      (length f <= A2_queries) %nat ->
      exists r, 
        In r (getSupport RndR) /\
        fBad f d r = false.

  (*
  Hypothesis fBad_single : 
    forall d r,
      fBad ((d, r) :: nil) = false.
*)

  (*
  Hypothesis goodExists :
    forall d f,
      arrayLookup _ f d = None ->
      exists r, 
        In r (getSupport RndR) /\
        fBad f d r = false.
*)

  Definition rndNotBad(d : D)(f : list (D * R)):=
    Repeat RndR (fun r => negb (fBad f d r)).

  Definition GenRP(s : list (D * R))(d : D) : Comp (R * list (D * R)) :=
    match arrayLookup _ s d with
      | Some r => ret (r, s)
      | None => r <-$ (rndNotBad d s); ret (r, (d, r) :: s)
    end.
    
  Definition RPS_G0  :=
    [b, _] <-$2 A2 _ _ (@randomFunc D R RndR _ ) nil;
    ret b.

  Definition RPS_G1 :=
    [b, _] <-$2 A2 _ _ GenRP nil;
    ret b.

   Definition randomFunc_bad (s : list (D * R) * bool) d :=
    [s, bad] <-2 s;
    match (arrayLookup _ s d) with
        | Some r => ret (r, (s, bad))
        | None => 
          r <-$ RndR; 
          newF <- ((d, r) :: s);
          bad' <- fBad s d r;
          ret (r, (newF, bad || bad'))
    end.

   Definition GenRP_bad (s : list (D * R) * bool) d :=
    [s, bad] <-2 s;
    match (arrayLookup _ s d) with
        | Some r => ret (r, (s, bad))
        | None => 
          r <-$ RndR; 
          newF <- ((d, r) :: s);
          bad' <- fBad s d r;
          if (bad') then
            (r <-$ rndNotBad d s;
            ret (r, ((d, r) :: s, bad || bad')))
          else
            ret (r, (newF, bad || bad'))
    end.

  Definition RPS_G_1 :=
    [b, s] <-$2 A2 _ _ (randomFunc_bad) (nil, false);
    ret (b, snd s).

  Definition RPS_G_2 :=
    [b, s] <-$2 A2 _ _ (GenRP_bad) (nil, false);
    ret (b, snd s).

 
  Theorem randomFunc_bad_wf : 
    forall a b,
      well_formed_comp (randomFunc_bad a b).
    
    intuition.
    unfold randomFunc_bad.
    destruct (arrayLookup eqdd a0 b0); wftac.

  Qed.

  Theorem GenRP_bad_wf : 
    forall a b, 
      (length (fst a) <= A2_queries)%nat ->
      well_formed_comp (GenRP_bad a b).

    intuition.
    simpl in *.
    case_eq (arrayLookup eqdd a0 b0); intuition; wftac.
    unfold rndNotBad; wftac.
    edestruct goodExists ; eauto.
    intuition.
    econstructor.
    unfold eq_dec; intuition.
    eapply (EqDec_dec _).
    trivial.
    eapply filter_In; intuition.
    eauto.
    rewrite H4.
    trivial.
  
  Qed.


  Theorem rf_rp_oc_eq_until_bad : 
    comp_spec 
      (fun y1 y2 =>
         snd (snd y1) = snd (snd y2) /\
          (snd (snd y1) = false -> fst (snd y1) = fst (snd y2) /\ fst y1 = fst y2))
      (A2 (list (D * R) * bool)%type _
          randomFunc_bad (nil, false))
      (A2 (list (D * R) * bool)%type _ 
          GenRP_bad (nil, false)).
    
    eapply comp_spec_consequence.
    eapply (@oc_comp_spec_eq_until_bad _ _ _ _ _ _ _ _ _ _ _ _ _ 
                                       (fun a => snd a)
                                       (fun a => snd a)
                                       (fun a b => (fst a = fst b))).
    intuition.
    eapply randomFunc_bad_wf.
    intuition.
    eapply GenRP_bad_wf.
    admit.

    intuition.
    simpl in *.
    subst.
 
    case_eq (arrayLookup eqdd a0 a1); intuition.
    eapply comp_spec_ret; intuition.

    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.

    case_eq ( fBad a0 a1 b); intuition.
    comp_irr_r.
    unfold rndNotBad.
    edestruct goodExists.
    eauto.
    intuition.
    econstructor.
    unfold eq_dec; intuition.
    eapply (EqDec_dec _).
    trivial.
    eapply filter_In; intuition.
    eauto.
    rewrite H5.
    trivial.
    eapply comp_spec_ret.
    simpl.
    split.
    intuition.
    intros.
    rewrite orb_true_r in H4.
    discriminate.
    eapply comp_spec_ret; intuition.
    intuition.
    simpl in *.
    case_eq (arrayLookup eqdd a1 d); intuition.
    rewrite H1 in H0.
    repeat simp_in_support.
    trivial.
    rewrite H1 in H0.
    repeat simp_in_support.
    trivial.
     
    intuition.
    simpl in *.
    case_eq (arrayLookup eqdd a1 d ); intuition;
    rewrite H1 in H0;
    repeat simp_in_support;
    trivial.
    
    trivial.
    trivial.

    intuition.
    
    Grab Existential Variables.
    trivial.
    
  Qed.
  
  
  Theorem RPS_G_1_2_bad_same :
     Pr  [x <-$ RPS_G_1; ret snd x ] == Pr  [x <-$ RPS_G_2; ret snd x ].

    unfold RPS_G_1, RPS_G_2.
    inline_first.
    
    eapply comp_spec_impl_eq.
    comp_skip.
    eapply rf_rp_oc_eq_until_bad.

    intuition.
    simpl in *.
    intuition.
    destruct b.
    simpl in *.
    destruct p; simpl in *.
    subst.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.

  Qed.

  Theorem RPG_G_1_2_eq_until_bad : 
    forall a : bool,
      evalDist RPS_G_1 (a, false) == evalDist RPS_G_2 (a, false).

    
    intuition.
    unfold RPS_G_1, RPS_G_2.
    eapply comp_spec_impl_eq.
    comp_skip.
    eapply rf_rp_oc_eq_until_bad.

    intuition.
    simpl in *.
    intuition.
    destruct b.
    simpl in *.
    destruct p; simpl in *.
    eapply comp_spec_ret; intuition.
    pairInv.
    subst.
    intuition.
    subst.
    intuition.
    subst.
    pairInv.
    intuition.
    subst.
    trivial.

  Qed.

  Theorem RPS_G_1_bad_small : 
    Pr  [x <-$ RPS_G_1; ret snd x ] <= A2_queries / 1 * badProb A2_queries.

    unfold RPS_G_1.
    inline_first.
  
    assert (Pr 
   [a <-$
    A2 (list (D * R) * bool)%type _
      (randomFunc_bad) (nil, false);
    x <-$ ([b, s]<-2 a; ret (b, snd s)); ret snd x ]
   ==
   Pr 
   [a <-$
    A2 (list (D * R) * bool)%type _
      (randomFunc_bad) (nil, false);
    ret snd (snd a) ]
   ).
    comp_skip.
    comp_simp.
    reflexivity.
    rewrite H.
    clear H.
    
    eapply leRat_trans.
    eapply (@oc_eventProb_0_1 _ (fun p => length (fst p)) _ badProb).
    eauto.
    eapply badProb_mono.
    trivial.
    intuition.
    simpl in *.
    subst.
    case_eq (arrayLookup eqdd a a0); intuition.
    comp_simp.
    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    congruence.
    
    simpl in *.
    eapply leRat_trans.
    Focus 2.
    eapply badProb_correct.
    inline_first.
    comp_skip.
    simpl.
    eapply leRat_refl.
    intuition.
    simpl in *.
    destruct (arrayLookup eqdd a a1);
    repeat simp_in_support.
    omega.
    simpl.
    intuition.
    
    trivial.
    intuition.

  Qed.

  Theorem RPS_G_1_2_close :  
  | Pr[x <-$ RPS_G_1; ret fst x] - Pr[x <-$ RPS_G_2; ret fst x] | <= (A2_queries / 1)  * badProb A2_queries.
    
    intuition.
    eapply leRat_trans.
    eapply fundamental_lemma_h.
    
    (* badness is the same. *)
    eapply RPS_G_1_2_bad_same.
    
    eapply RPG_G_1_2_eq_until_bad.

    eapply RPS_G_1_bad_small.
    
  Qed.

  Theorem RPS_G0_equiv : 
    Pr[RPS_G0] == Pr[x <-$ RPS_G_1; ret fst x].

    unfold RPS_G0, RPS_G_1.
    inline_first.
    eapply (comp_spec_eq_impl_eq).
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => a = fst b)); trivial.
    intuition.
    subst.
    unfold randomFunc, randomFunc_bad.
    comp_simp.
    simpl.
    case_eq ( arrayLookup eqdd l a ); intuition.
    eapply comp_spec_ret; intuition.
    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition.
    
    comp_simp.
    simpl in *; intuition.
    subst.
    eapply comp_spec_eq_refl.
    
  Qed.

  Theorem RPS_G1_equiv : 
    Pr[x <-$ RPS_G_2; ret fst x] == Pr[RPS_G1].

    unfold RPS_G_2, RPS_G1.
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => fst a = b)); trivial.
    intuition.
    unfold GenRP, GenRP_bad.
    subst.
    simpl.
    case_eq (arrayLookup eqdd a0 a); intuition.
    eapply comp_spec_ret; intuition.

    unfold rndNotBad.

    assert (
        comp_spec 
          eq
          (r <-$ (r <-$ RndR; if (negb (fBad a0 a r)) then (ret r) else (Repeat RndR (fun r : R => negb (fBad a0 a r))));

           ret (r, (a, r) :: a0))
          (r <-$ Repeat RndR (fun r : R => negb (fBad a0 a r));
           ret (r, (a, r) :: a0))
      ).

    eapply eq_impl_comp_spec_eq.
    intuition.
    symmetry.
    comp_skip.
    eapply repeat_unroll_eq.
    trivial.
    edestruct goodExists; eauto.
    intuition.
    econstructor.
    eapply filter_In; intuition.
    eauto.
    rewrite H2.
    trivial.
    eapply comp_spec_eq_trans_r.
    Focus 2.
    eapply H0.
    clear H0.
    inline_first.
    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    case_eq (fBad a0 a b0); intuition.
    simpl.
    comp_skip.
    eapply comp_spec_ret; intuition.
    simpl.
    comp_simp.
    eapply comp_spec_ret; intuition.
    comp_simp.
    simpl in *.
    intuition; subst.
    eapply comp_spec_eq_refl.
    
  Qed.

  Theorem RPS_G0_1_close :  
  | Pr[RPS_G0] - Pr[RPS_G1] | <= (A2_queries / 1)  * badProb A2_queries.
    
    rewrite RPS_G0_equiv.
    rewrite <- RPS_G1_equiv.
    eapply RPS_G_1_2_close.
  Qed.

End RandPermSwitching.