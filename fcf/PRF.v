(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Definitions related to pseudoradom functions.  This file copies some items from ConstructedFunc.v, so we probably need to refactor this in the future. *)

Set Implicit Arguments.
Require Import fcf.FCF.
Require Import fcf.CompFold. 
Require Export fcf.Array.
Require Export fcf.Hybrid.

Local Open Scope list_scope.
Local Open Scope array_scope.

Definition oracleMap(D R S: Set)(eqds : EqDec S)(eqdr : EqDec R)(oracle : S  -> D -> Comp (R * S))(s : S)(ds : list D) :=
  compFold _ 
  (fun acc d => [rs, s] <-2 acc; [r, s] <-$2 oracle s d; ret (rs ++ r :: nil, s)) 
  (nil, s) ds.

Theorem oracleMap_wf : 
  forall (D R S : Set)(eqds : EqDec S)(eqdr : EqDec R) (oracle : S -> D -> Comp (R * S))ds s,
  (forall s x, well_formed_comp (oracle s x)) ->
  well_formed_comp (@oracleMap D R S _ _ oracle s ds).

  intuition.
  unfold oracleMap.
  eapply compFold_wf; intuition.
  wftac.

Qed.


Section RandomFunc.
  
  Variable D R : Set.
  Variable RndR : Comp R.

  Hypothesis EqDec_D : EqDec D.
  Instance EqDec_R : EqDec R.
    eapply comp_EqDec.
    eauto.
  Qed.

  Hypothesis RndR_wf : well_formed_comp RndR.
  
    (* A random function *)
  Definition randomFunc (f : (list (D * R))) (d : D) : Comp (R * list (D * R)) :=
      match (arrayLookup _ f d) with
        | None => (r <-$ RndR; ret (r, (d, r) :: f))
        | Some r => ret (r, f)
      end.  
  
  Lemma randomFunc_wf : forall f d, 
    well_formed_comp (randomFunc f d).
    
    intuition.
    unfold randomFunc.
    case_eq (f#d); intuition; wftac.
    
  Qed.    
  
  Hint Resolve randomFunc_wf : wftac.

  (* Eager random functions with finite domain *)
  Definition RndFunc(lsd : list D) : Comp (list (D * R)) :=
    compFold _ (fun f d => r <-$ RndR; ret (d, r)::f) nil lsd. 
  
End RandomFunc.

Local Open Scope type_scope.
Local Open Scope comp_scope.

Section PRF_concrete.
  
  Variable D R Key : Set.
  Variable RndKey : Comp Key.
  Variable RndR : Comp R.
  Variable f : Key -> D -> R.

  Hypothesis D_EqDec : EqDec D.
  Hypothesis R_EqDec : EqDec R.

  Definition RndR_func : (list (D * R) -> D -> Comp (R * list (D * R))) :=
    (randomFunc RndR _).

  Section PRF_NA_concrete.
  (* A PRF that is secure against a non-adaptive adversary. *)
      
    Variable State : Set.
    Variable A1 : Comp (list D * State).
    Variable A2 : State -> list R -> Comp bool.

    Definition PRF_NA_G_A : Comp bool := 
      [lsD, s_A] <-$2 A1; 
      lsR <-$ (k <-$ RndKey; ret (map (f k) lsD));
      A2 s_A lsR.
    
    Definition PRF_NA_G_B : Comp bool := 
      [lsD, s_A] <-$2 A1;
      [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD;
      A2 s_A lsR.
    
    Definition PRF_NA_Advantage := 
    | Pr[PRF_NA_G_A] - Pr[PRF_NA_G_B] |.  

  End PRF_NA_concrete.

  Section PRF_NAI_concrete.

    Variable A_state : Set.
    Variable A1 : Comp ((list (list D)) * A_state).
    Variable A2 : A_state -> list (list R) -> Comp bool.

    Definition PRF_NAI_G0 :=
      [lsDs, s_A] <-$2 A1;
      lsRs <-$ compMap _ (fun lsD => k <-$ RndKey; ret (map (f k) lsD)) lsDs;
      A2 s_A lsRs.

    Definition PRF_NAI_G1 :=
      [lsDs, s_A] <-$2 A1;
      lsRs <-$ compMap _ (fun lsD => [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD; ret lsR) lsDs;
      A2 s_A lsRs.

    Definition PRF_NAI_Advantage := 
    | Pr[PRF_NAI_G0] - Pr[PRF_NAI_G1] |.   
                         
  Section PRF_NA_impl_NAI.

    Variable maxLists : nat.
    Hypothesis maxLists_correct : 
      forall ls s_A, 
        In (ls, s_A) (getSupport A1) ->
        (length ls <= maxLists)%nat.

    Hypothesis A_state_EqDec : EqDec A_state.
    Hypothesis RndR_wf : well_formed_comp RndR.
    Hypothesis RndKey_wf : well_formed_comp RndKey.

    Variable maxDistance : Rat.
    Hypothesis maxDistance_correct : 
      forall i, 
      PRF_NA_Advantage (B1 nil _ _ A1 i) (B2 (fun lsD => k <-$ RndKey; ret (map (f k) lsD))
              (fun lsD => [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD; ret lsR)
              _ A2) <= maxDistance.

    Theorem PRF_NAI_Advantage_eq_Hybrid:
      PRF_NAI_Advantage == ListHybrid_Advantage 
                             (fun lsD => k <-$ RndKey; ret (map (f k) lsD))
                             (fun lsD => [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD; ret lsR)
                             _ A1 A2.

      reflexivity.

    Qed.

     
    Theorem PRF_NA_impl_NAI : 
      PRF_NAI_Advantage <= (maxLists / 1 * maxDistance)%rat.


      rewrite PRF_NAI_Advantage_eq_Hybrid.
      rewrite Single_impl_ListHybrid.
      reflexivity.
      
      intuition.
      wftac.

      intuition.
      wftac.
      eapply oracleMap_wf.
      intuition.
      eapply randomFunc_wf; intuition.
      intuition.

      intuition.

      assert (DistSingle_Adv (fun lsD : list D => k <-$ RndKey; ret map (f k) lsD)
     (fun lsD : list D =>
      z <-$
      oracleMap (list_EqDec (pair_EqDec D_EqDec R_EqDec)) R_EqDec RndR_func
        nil lsD; [lsR, _]<-2 z; ret lsR)
     (B1 nil (list_EqDec D_EqDec) A_state_EqDec A1 i)
     (B2 (fun lsD : list D => k <-$ RndKey; ret map (f k) lsD)
        (fun lsD : list D =>
         z <-$
         oracleMap (list_EqDec (pair_EqDec D_EqDec R_EqDec)) R_EqDec
           RndR_func nil lsD; [lsR, _]<-2 z; ret lsR) 
        (list_EqDec R_EqDec) A2)
     ==
     PRF_NA_Advantage
                          (B1 nil (list_EqDec D_EqDec) A_state_EqDec A1 i)
                          (B2
                             (fun lsD : list D =>
                              k <-$ RndKey; ret map (f k) lsD)
                             (fun lsD : list D =>
                              z <-$
                              oracleMap
                                (list_EqDec (pair_EqDec D_EqDec R_EqDec))
                                R_EqDec RndR_func nil lsD;
                              [lsR, _]<-2 z; ret lsR) 
                             (list_EqDec R_EqDec) A2)
                          ).
      unfold DistSingle_Adv, PRF_NA_Advantage, DistSingle_G, PRF_NA_G_A, PRF_NA_G_B.
      eapply ratDistance_eqRat_compat;
        repeat (try comp_skip; try reflexivity; comp_simp; inline_first).
      rewrite H.
      clear H.
      intuition.
    Qed.

  End PRF_NA_impl_NAI.

  End PRF_NAI_concrete.

  Section PRF_Full_concrete.
    
    Variable A : OracleComp D R bool.
    
    Definition f_oracle(k : Key)(x : unit)(d : D) :=
      ret (f k d, tt).
    
    Definition PRF_G_A : Comp bool := 
      k <-$ RndKey;
      [b, _] <-$2 A _ _ (f_oracle k) tt;
      ret b.
    
    Definition PRF_G_B : Comp bool := 
      [b, _] <-$2 A _ _ (RndR_func) nil;
      ret b.
    
    Definition PRF_Advantage := 
    | Pr[PRF_G_A] - Pr[PRF_G_B] |.  
    
  End PRF_Full_concrete.

  Section PRF_Finite_concrete.

    Variable dom : list D.
    Variable def : R.
    Variable A : (D -> R) -> Comp bool.

    Definition PRF_Fin_G_A : Comp bool := 
      k <-$ RndKey;
      A (f k).
    
    Definition PRF_Fin_G_B : Comp bool := 
      f <-$ @RndFunc D R RndR _ dom;
      A (fun d => arrayLookupDef _ f d def).

    Definition PRF_Fin_Advantage := 
    | Pr[PRF_Fin_G_A] - Pr[PRF_Fin_G_B] |.

  End PRF_Finite_concrete.
  
End PRF_concrete.

Require Import fcf.Asymptotic.
Require Import fcf.Admissibility.

Section PRF.

  Variable D R Key : DataTypeFamily.
  Variable RndKey : forall n, Comp (Key n).
  Variable RndR : forall n, Comp (R n).
  Variable f : forall n, Key n -> D n -> R n.

  Hypothesis D_EqDec : forall n, EqDec (D n).
  Hypothesis R_EqDec : forall n, EqDec (R n).

  Section PRF_NA.
    Variable admissible_A1 : pred_comp_fam.
    Variable admissible_A2 : pred_comp_func_2_fam.
    
    Definition PRF_NA :=
      forall (State : DataTypeFamily) A1 A2,
        admissible_A1 _ A1 -> 
        admissible_A2 State _ _ A2 ->
        negligible (fun n => PRF_NA_Advantage (RndKey n) (RndR n) (@f n) _ _ (A1 n) (@A2 n)).
  End PRF_NA.

  Section PRF_Full.
    Variable admissible_A : pred_oc_fam.
    
    Definition PRF :=
      forall (A : forall n, OracleComp (D n) (R n) bool),
        admissible_A _ _ _ A -> 
        negligible (fun n => PRF_Advantage (RndKey n) (RndR n) (@f n) _ _ (A n)).
  End PRF_Full.
      
End PRF.
