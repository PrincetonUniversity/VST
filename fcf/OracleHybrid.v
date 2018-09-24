(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import fcf.RndInList. 

Section OracleHybrid.

  Variable A B State S_A : Set.
  (* At one point in the proof, we need to know that B is inhabited *)
  Variable b : B. 
  Hypothesis eqdb : EqDec B.
  Hypothesis eqdState : EqDec State.
  Hypothesis eqdS_A : EqDec S_A.
  
  (* Two oracles, which we want to show are indistinguishable *)
  Variable O1 O2 : State -> A -> Comp (B * State).
  Hypothesis O1_wf : forall s a, well_formed_comp (O1 s a).
  Hypothesis O2_wf : forall s a, well_formed_comp (O2 s a).

  (* The "adversary" that attempts to distinguish the oracles using at most q queries. *)
  Variable A0 : Comp (State * S_A).
  Variable A1 : S_A -> OracleComp A B bool.
  Hypothesis A0_wf : well_formed_comp A0.
  Hypothesis A1_wf : forall s_A, well_formed_oc (A1 s_A).
  Variable q : nat.
  Hypothesis A1_qam : 
    forall s s_A, 
      In (s, s_A) (getSupport A0) ->
      queries_at_most (A1 s_A) q.

  (* This proof will show that G1 and G2 are close *)
  Definition G1 := 
    [s, s_A] <-$2 A0;
    [b, _] <-$2 (A1 s_A) _ _ O1 s;
    ret b.

  Definition G2 :=
    [s, s_A] <-$2 A0;
    [b, _] <-$2 (A1 s_A) _ _ O2 s;
    ret b.

  (* The ith oracle responds to the first (i-1) queries using O1, and the remaining queries using O2. *)
  Definition Oi (i : nat)(s : (State * nat))(a : A) : Comp (B * (State * nat)) :=
    [s_s, s_i] <-2 s;
    let O_c := if (ge_dec s_i i) then O2 else O1 in
    [b, s_s'] <-$2 O_c s_s a;
      ret (b, (s_s', (S s_i))).
      
  
  (* The ith game uses the ith oracle.  We will show that G1 is the same as (Gi q) and that G2 is the same as (Gi 0).*)
  Definition Gi i :=
    [s, s_A] <-$2 A0;
    [b, _] <-$2 (A1 s_A) _ _ (Oi i) (s, 0%nat);
    ret b.

  (* We need an assumption that each adjacent pair of games are distant by at most some constant k. *)
  Variable k : Rat.
  Hypothesis Gi_Si_close : 
    forall i,
      | Pr[Gi i] - Pr[Gi (S i)] | <= k.

  (* Step 1: show that G1 is the same as (Gi q).  This is actually the most complicated part of this proof. *)

  (* In order to show that G1 is the same as (Gi q), we need an intermediate game that is like G1 except the oracle also keeps track of how many times it was called.  We will use an "identical until bad" proof, in which the "bad" event is that the number of queries is greater than q.  The probability of this event is 0, so we end up with an equivalence. *)
  Definition O1_count (s : (State * nat))(a : A) : Comp (B * (State * nat)) :=
    [s_s, s_i] <-2 s;
    [b, s_s'] <-$2 O1 s_s a;
      ret (b, (s_s', (S s_i))).

  Definition G1_count  :=
    [s, s_A] <-$2 A0;
    [b, s] <-$2 (A1 s_A) _ _ O1_count (s, 0%nat);
    ret (b, if (gt_dec (snd s) q) then true else false).

  (* We also need a game like Gi that exposes the bad event in the same way as G1_count. Then we can show that G1_count and (Gi_count q) are "identical until bad" and the probability of the "bad" event is 0.  *)
  Definition Gi_count i :=
    [s, s_A] <-$2 A0;
    [b, s] <-$2 (A1 s_A) _ _ (Oi i) (s, 0%nat);
    ret (b, if (gt_dec (snd s) q) then true else false).

  Theorem G1_eq_G1_count : 
    Pr[G1] == Pr[x <-$ G1_count; ret (fst x)].

    unfold G1, G1_count.
    fcf_inline_first.
    fcf_to_prhl_eq.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    eapply (fcf_oracle_eq (fun x y => x = fst y)); trivial; intuition; subst.
    unfold O1_count.
    fcf_simp.
    fcf_ident_expand_l.
    fcf_skip.
    fcf_spec_ret; intuition.

    simpl in *; intuition; subst.
    fcf_simp.
    simpl.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem Gi_eq_Gi_count : 
    forall i,
      Pr[Gi i] == Pr[x <-$ Gi_count i; ret (fst x)].
    
    intuition.
    unfold Gi_count, Gi.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    simpl.
    intuition.
  Qed.

  Theorem O1_count_wf :
    forall a b,
    well_formed_comp (O1_count a b).

    intuition.
    unfold O1_count.
    fcf_well_formed.

  Qed.

  Theorem Oi_wf : 
    forall i a b,
      well_formed_comp (Oi i a b).

    intuition.
    unfold Oi.
    fcf_well_formed.
    destruct (ge_dec b0 i); fcf_well_formed.

  Qed.

  (* We will need to know that the count increases by one after each call to O1_count and Oi. *)
  Theorem O1_count_increases : 
    forall d1 b1 c1 a2 b2 c2,
      In (d1, (b1, c1)) (getSupport (O1_count (b2, c2) a2)) ->
      c1 = S c2.

    intuition.
    unfold O1_count in *.
    fcf_simp_in_support.
    destruct x.
    fcf_simp_in_support.
    trivial.
    
  Qed.

  Theorem Oi_count_increases : 
    forall i d1 b1 c1 a2 b2 c2,
      In (d1, (b1, c1)) (getSupport (Oi i (b2, c2) a2)) ->
      c1 = S c2.

    intuition.
    unfold Oi in *.
    fcf_simp_in_support.
    destruct x.
    fcf_simp_in_support.
    trivial.
    
  Qed.

  (* The relational specification on O1_count and (Oi q).  As usual, I arrived at this by attempting some of the theorems below and then factoring out this theorem. *)
  Theorem O1_count_Oi_eq_until_bad :
    forall s s_A,
    comp_spec (fun a b => ((snd (snd a) > q) <-> (snd (snd b) > q)) /\ ((snd (snd a) <= q)%nat -> (fst a = fst b /\ fst (snd a) = fst (snd b))))
              ((A1 s_A) _ _ O1_count (s, 0)%nat)
              ((A1 s_A) _ _ (Oi q) (s, 0)%nat).
    
    intuition.
    eapply comp_spec_consequence.
    eapply (fcf_oracle_eq_until_bad (fun x => if (gt_dec (snd x) q) then true else false) (fun x => if (gt_dec (snd x) q) then true else false) eq); intuition; subst.
    apply O1_count_wf.
    apply Oi_wf.
    pairInv.
    
    unfold O1_count, Oi.
    destruct (ge_dec b1 q).
    fcf_irr_l.
    fcf_irr_r.
    fcf_simp.
    fcf_spec_ret;
      simpl in H2;
      destruct (gt_dec (S b1) q);
      try discriminate;
      try omega.
    
    fcf_skip.
    fcf_spec_ret; intuition.
      
    apply  O1_count_increases in H0.
    simpl in *.
    fcf_compute.

    apply  Oi_count_increases in H0.
    simpl in *.
    fcf_compute.

    intuition; simpl in *.   
    fcf_compute.
    destruct (gt_dec b1 q); trivial.
    destruct (gt_dec (snd (snd b0)) q); intuition; discriminate.
  
    destruct (gt_dec b1 q).
    omega.
    intuition.

    destruct b0.
    destruct (gt_dec b1 q).
    omega.
    intuition.
    simpl in *.
    subst.
    trivial.
    
  Qed.

  Theorem G1_eq_Gi_q : 
    Pr[G1] == Pr[Gi q].

    (* Use the fundamental lemma, where the "bad" event is that the counter in the oracle gets a value > q.  Then use the qam_count theorem from RndInList to show that the probability of this event is 0.  *)

    rewrite G1_eq_G1_count .
    rewrite Gi_eq_Gi_count.

    eapply ratIdentityIndiscernables.
    eapply leRat_impl_eqRat.
    eapply leRat_trans.
    eapply fundamental_lemma_h.

    (* bad events the same*)
    unfold G1_count, Gi_count.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_to_prhl.
    comp_skip.

    apply O1_count_Oi_eq_until_bad.
    simpl in H1.
    intuition; subst.
    fcf_simp.
    simpl in *.
    fcf_spec_ret; fcf_compute.

    (* equal until bad *)
    intuition.
    unfold G1_count, Gi_count.
    fcf_skip.
    fcf_simp.
    fcf_to_prhl.
    comp_skip.
    eapply O1_count_Oi_eq_until_bad.
    simpl in *; intuition.
    fcf_simp.
    destruct p; simpl in *.
    fcf_spec_ret; fcf_compute;
    assert (b1 <= q)%nat by omega; intuition; subst; pairInv; trivial.
  
    (* probability of bad event is 0 *)
    unfold G1_count.
    fcf_inline_first.
    fcf_irr_l.
    fcf_simp.
    inline_first.
    fcf_irr_l.
    apply oc_comp_wf; intuition.
    eapply O1_count_wf.

    fcf_simp.
    unfold snd.
    fcf_compute.
    destruct p.
    (* The qam_count theorem takes a function that produces a "count" from the state of the oracle.  This theorem assumes this count increases by at most 1 in each call to the oracle, and that the number of queries is at most q.  Then the result is that the final count is at most q. *)
    eapply (qam_count (A1_qam s s0 _) (fun x => snd x)) in H0.
    simpl in *.
    omega.
    intuition.
    simpl.    

    apply O1_count_increases in H1.
    omega.
    trivial.

    eapply rat0_le_all.

    Grab Existential Variables.
    eauto.

  Qed.

  (* Step 2: show that G2 is the same as (Gi 0).  This is much simpler. *)
  Theorem G2_eq_Gi_0 : 
    Pr[G2] == Pr[Gi 0%nat].

    unfold G2, Gi.
    fcf_skip.
    fcf_simp.
    fcf_to_prhl_eq.
    comp_skip.
    eapply (fcf_oracle_eq (fun a b => a = fst b)); trivial; intuition; subst.
    unfold Oi.
    comp_simp.
    destruct (ge_dec n 0).
    simpl.
    fcf_ident_expand_l.
    comp_skip.
    eapply comp_spec_ret; intuition.
    omega.

    simpl in  H1.
    intuition; subst.
    comp_simp.
    simpl in *.
    intuition; subst.
    eapply comp_spec_eq_refl.

  Qed.        

  (* Step 3: rewrite using the equalities in the previous steps, and then use some arithmetic to show that the distance between G1 and G2 is small. *)
  Theorem G1_G2_close : 
    | Pr[G1] - Pr[G2] | <= (q / 1) * k.

    rewrite G1_eq_Gi_q.
    rewrite G2_eq_Gi_0.
    rewrite ratDistance_comm.
    specialize (distance_le_prod_f (fun i => Pr[Gi i])); intuition.

  Qed.

End OracleHybrid.


(* A specialization that uses OracleHybrid to produce a hybrid argument on non-adaptive oracle interactions *)
Require Import fcf.CompFold.
Require Import fcf.OracleCompFold.

(* oracleMap is defined in PRF.  We should probably find a better place for it. *)       
Require Import fcf.PRF.

Section OracleMapHybrid.

  Variable A B C State S_A : Set.

  Variable b : B.

  Hypothesis eqdA : EqDec A.
  Hypothesis eqdB : EqDec B.
  Hypothesis eqdState : EqDec State.
  Hypothesis eqdS_A : EqDec S_A.

  Variable A1 : Comp (State * (list A * S_A)).
  Variable A2 : S_A -> list B -> Comp bool.

  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : 
    forall s_A lsb, well_formed_comp (A2 s_A lsb).

  Variable q : nat.
  Variable k : Rat.

  Hypothesis max_queries : 
    forall ls s s_A,
      In (s, (ls, s_A)) (getSupport A1) ->
      (length ls <= q)%nat.
  
  Variable O1 O2 : State -> A -> Comp (B * State).

  Hypothesis O1_wf :
    forall s a,
      well_formed_comp (O1 s a).

  Hypothesis O2_wf : 
    forall s a,
      well_formed_comp (O2 s a).
  
  Definition OMH_G O :=
   [s, p] <-$2 A1;
    [lsa, s_A] <-2 p;
    [lsb, _] <-$2 oracleMap _ _ O s lsa;
    A2 s_A lsb.

  Definition OMH_G_i i :=
    [s, p] <-$2 A1;
    [lsa, s_A] <-2 p;
    [lsb1, s'] <-$2 oracleMap _ _ O1 s (firstn i lsa);
    [lsb2, _] <-$2 oracleMap _ _ O2 s' (skipn i lsa);
    A2 s_A (lsb1 ++ lsb2).

  Hypothesis adjacent_close : 
    forall i,
      | Pr[OMH_G_i i] - Pr[OMH_G_i (S i)] | <= k.

  Definition OMH_G_oc (p : list A * S_A) :=
    [lsa, s_A] <-2 p;
    lsb <--$ oc_compMap _ (fun a => OC_Query _ a) lsa;
    $ A2 s_A lsb.

  Theorem OMH_G_oc_wf : forall p,
    well_formed_oc (OMH_G_oc p).

    intuition.
    econstructor.
    apply oc_compMap_wf.
    intuition.
    econstructor.
    intuition.
    econstructor.
    auto.
  Qed.

  Theorem OMH_G_oc_equiv : 
    forall O,
      Pr[OMH_G O] == 
      Pr[
          [s, s_A] <-$2 A1;
          [b, _] <-$2 (OMH_G_oc s_A) _ _ O s; 
          ret b
        ].

    intuition.
    unfold OMH_G, OMH_G_oc.
    fcf_skip.
    fcf_simp.
    
    fcf_to_prhl_eq.
    simpl.
    fcf_inline_first.
    fcf_skip.
    apply compFold_oc_equiv.
    
    subst.
    fcf_inline_first.
    fcf_ident_expand_l.
    fcf_skip.
    fcf_simp.
    fcf_spec_ret.
  Qed.


  Definition OMH_G1 := OMH_G O1.

  Definition OMH_G2 := OMH_G O2.

  Theorem OMH_G1_equiv: 
    Pr[OMH_G1] == Pr[G1 _ O1 A1 OMH_G_oc].

    unfold OMH_G1.
    rewrite OMH_G_oc_equiv.
    unfold G1, OMH_G_oc.
    reflexivity.
    
  Qed.

  Theorem OMH_G2_equiv: 
    Pr[OMH_G2] == Pr[G2 _ O2 A1 OMH_G_oc].

    unfold OMH_G2.
    rewrite OMH_G_oc_equiv.
    unfold G2, OMH_G_oc.
    reflexivity.
    
  Qed.

  Theorem OMH_G_oc_qam :
    forall p s, 
      In (s, p) (getSupport A1) ->
      queries_at_most (OMH_G_oc p) q.

    intuition.
    unfold OMH_G_oc.
    econstructor.
    econstructor.
    eapply oc_compMap_qam.
    intuition.
    econstructor.
    intuition.
    econstructor.
    rewrite mult_1_r.
    rewrite plus_0_r.
    eapply max_queries.
    eauto.
  Qed.

  Definition Gi_oracleMap i :=
    [s, p] <-$2 A1;
    [lsa, s_A] <-2 p;
    p <-$ oracleMap _ _ (Oi _ _ O1 O2 i) (s, 0)%nat lsa;
    A2 s_A (fst p).

  Definition Gi_oracleMap' i :=
    [s, p] <-$2 A1;
    [lsa, s_A] <-2 p;
    p <-$ (
        [lsb1, s'] <-$2 oracleMap _ _ (Oi _ _ O1 O2 i) (s, 0)%nat (firstn i lsa);
        [lsb2, s''] <-$2 oracleMap _ _ (Oi _ _ O1 O2 i) s'%nat (skipn i lsa);
        ret (lsb1 ++ lsb2, s'')
      );
    A2 s_A (fst p).

  Theorem Gi_oracleMap_equiv : 
    forall i,
      Pr[Gi _ _ O1 O2 A1 OMH_G_oc i] == Pr[Gi_oracleMap i].
    
    intuition.
    unfold Gi, OMH_G_oc, Gi_oracleMap.
    fcf_skip.
    fcf_simp.
    fcf_to_prhl_eq.
    simpl.
    fcf_inline_first.
    eapply comp_spec_eq_symm.
    fcf_skip.
    eapply compFold_oc_equiv.
    subst.
    simpl.
    fcf_ident_expand_l.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_spec_ret.
    
  Qed.

  Theorem Gi_oracleMap'_equiv : 
    forall i,
      Pr[Gi_oracleMap i] == Pr[Gi_oracleMap' i].
    
    intuition.
    unfold Gi_oracleMap, Gi_oracleMap'.
    
    fcf_skip.
    fcf_simp.
    fcf_skip.    
    cutrewrite (l = (firstn i l ++ skipn i l)).
    eapply eqRat_trans.
    eapply compFold_app.
    
    fcf_skip.
    rewrite firstn_skipn.
    reflexivity.
    
    fcf_simp.
    fcf_ident_expand_l.
    fcf_to_prhl_eq.
    rewrite firstn_skipn.
    fcf_skip.
    eapply (compFold_spec' (fun a b c d => a = b /\ snd c = snd d /\ l0++ (fst d) = (fst c)));
      intuition.
    simpl.
    eapply app_nil_r.
    simpl in *.
    subst.
    destruct d.
    simpl in *.
    subst.
    unfold Oi.
    inversion H2; clear H2; subst.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_spec_ret.
    simpl.
    rewrite app_assoc.
    trivial.
    
    fcf_simp.
    simpl in H3.
    intuition.
    subst.
    fcf_spec_ret.
    rewrite firstn_skipn.
    trivial.
  Qed.
  
  Theorem OMH_G_i_equiv : 
    forall i,
      Pr[Gi_oracleMap' i] == Pr[OMH_G_i i].
    
    intuition.
    unfold Gi_oracleMap', OMH_G_i.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_to_prhl_eq.
    fcf_skip.
    eapply (compFold_spec' (fun a b c d => a = b /\ fst c = fst d /\ fst (snd c) = snd d /\ (snd (snd c) + length a = min i (length l))%nat)); intuition.
    simpl.
    apply firstn_length.
    
    fcf_simp.
    simpl in *.
    subst.
    inversion H1; clear H1; subst.
    fcf_inline_first.
    destruct (ge_dec b2 i).
    exfalso.
    destruct (le_dec i (length l)).
    rewrite min_l in H4.
    omega.
    trivial.
    rewrite min_r in H4.
    omega.
    omega.

    comp_skip.
    fcf_spec_ret.
    simpl.
    omega.
    
    simpl in H2.
    intuition.
    subst.
    fcf_inline_first.
    fcf_simp.
    
    rewrite plus_0_r in H6.
    destruct (ge_dec i (length l)).
    rewrite skipn_ge_nil; trivial.
    unfold oracleMap.
    simpl.
    fcf_simp.
    simpl.
    eapply comp_spec_eq_refl.
    
    fcf_skip.
    eapply (compFold_spec' (fun a b c d => a = b /\ fst c = fst d /\ fst (snd c) = snd d /\ (snd (snd c) >= i)%nat)); intuition.
    simpl.
    rewrite min_l; omega.
    simpl in *.
    subst.
    destruct (ge_dec b2 i); try omega.
    inversion H4; clear H4; subst.
    fcf_inline_first.
    fcf_simp.
    fcf_skip.
    simpl.
    fcf_spec_ret.
    simpl.
    omega.
    
    simpl in H5.
    intuition; subst.
    fcf_simp.
    simpl.
    eapply comp_spec_eq_refl.
    
  Qed.

  Theorem OMH_G1_G2_close : 
    | Pr[OMH_G1] - Pr[OMH_G2] | <= (q / 1) * k.

    rewrite OMH_G1_equiv.
    rewrite OMH_G2_equiv.

    eapply G1_G2_close; intuition.

    apply OMH_G_oc_wf.

    eapply OMH_G_oc_qam.
    eauto.

    repeat rewrite Gi_oracleMap_equiv, Gi_oracleMap'_equiv, OMH_G_i_equiv.
    auto.

  Qed.


End OracleMapHybrid.