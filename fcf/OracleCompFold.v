(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.CompFold.

Local Open Scope list_scope.

Notation "'query' v" := (OC_Query  _ v) (at level 79) : comp_scope. 

Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
  match ls with
    | nil => $ (ret nil)
    | a :: ls' =>
      b <--$ c a;
      lsb' <--$ oc_compMap _ c ls';
      $ (ret (b :: lsb'))
  end. 

Theorem compMap_oc_spec : 
  forall (C D : Set)(P2 : C -> D -> Prop)(A B : Set)(P1 : A -> B -> Prop)(eqdc : EqDec C)(eqdd : EqDec D)(E F S: Set)(eqds : EqDec S)(ls1 : list A)(ls2 : list B)(c1 : A -> Comp C)(c2 : B -> OracleComp E F D)o (s : S),
    list_pred P1 ls1 ls2 ->
    (forall a b z, P1 a b -> comp_spec (fun x y => P2 x (fst y)) (c1 a) (c2 b _ _ o z)) -> 
    comp_spec (fun a b => list_pred P2 a (fst b))
    (compMap _ c1 ls1)
    ((oc_compMap _ c2 ls2) _ _ o s).
  
  induction ls1; inversion 1; subst; intuition; simpl in *.
  comp_simp.
  eapply comp_spec_ret; simpl; econstructor.
  
  simpl.
  comp_skip.
  comp_simp.
  comp_skip.
  comp_simp.
  eapply comp_spec_ret; intuition.
  simpl.
  econstructor; eauto.
    
Qed.

Theorem oc_compMap_eq : 
  forall (A B C D : Set){eqd : EqDec D}(f1 f2 : A -> OracleComp B C D)(ls : list A) (S : Set){eqds : EqDec S} o (s : S),
    (forall s a, comp_spec 
      eq
      ((f1 a) _ _ o s)
      ((f2 a) _ _ o s)) ->
    comp_spec 
    eq
    ((oc_compMap _ f1 ls) _ _ o s)
    ((oc_compMap _ f2 ls) _ _ o s).
  
  induction ls; intuition; simpl in *.
  comp_simp.
  eapply comp_spec_eq_refl.
  comp_skip.
  comp_skip.
  comp_simp.
  eapply comp_spec_eq_refl.
  
Qed.

Require Import fcf.PRF.

Theorem compMap_randomFunc_NoDup : 
  forall (A B C: Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}(ls : list A)(f : A -> B -> Comp C)(rndB : Comp B)(lsf : list (A * B)),
    NoDup ls ->
    (forall a, In a ls -> arrayLookup _ lsf a = None) ->
    comp_spec (fun a b => fst a = fst b)
    ((oc_compMap _ (fun x => y <--$ query x; $ f x y) ls) _ _ (@randomFunc A B rndB _) lsf)
    ((oc_compMap _ (fun x => y <--$ query x; $ f x y) ls) _ _ (fun s a => b <-$ rndB; ret (b, s)) tt).
  
  induction ls; intuition; simpl in *.
  comp_simp.
  eapply comp_spec_ret; intuition.
  inversion H; clear H; subst.
  
  simpl; inline_first.
  unfold randomFunc.
  rewrite H0.
  inline_first.
  comp_skip.
  comp_simp.
  inline_first.
  comp_skip.
  comp_simp.
  comp_skip.
  eapply IHls; intuition.
  simpl.
  case_eq (eqb a0 a); intuition.
  rewrite eqb_leibniz in H7.
  subst.
  intuition.
  comp_simp.
  simpl in *; subst.
  eapply comp_spec_ret; intuition.
  intuition.
  
Qed.

Theorem oc_compMap_wf : 
  forall (A B C D : Set)(eqd : EqDec B)(c : A -> OracleComp C D B) ls,
    (forall a, In a ls -> well_formed_oc (c a)) ->
    well_formed_oc (oc_compMap eqd c ls).
  
  induction ls; intuition; simpl in *;
  econstructor; wftac; intuition.
  
Qed.


Theorem compFold_oc_equiv_h : 
  forall (A B S : Set)(eqdb : EqDec B)(eqds : EqDec S)(O : S -> A -> Comp (B * S))(lsa : list A)(initS : S)(lsb : list B),
    comp_spec eq 
              (compFold _
                        (fun (acc : list B * S) (d : A) =>
                           [rs, s]<-2 acc; z <-$ O s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
                        (lsb, initS) lsa)
              ([lsb', s'] <-$2 ((oc_compMap _ (fun a : A => query a) lsa) S _ O initS);
              ret (lsb ++ lsb', s')).

  induction lsa; intuition; simpl.
  
  fcf_inline_first.
  fcf_simp.
  rewrite app_nil_r.
  fcf_spec_ret.

  fcf_inline_first.
  fcf_skip.
  eapply comp_spec_eq_trans.
  eapply IHlsa.
  fcf_inline_first.
  fcf_skip.
  fcf_inline_first.
  fcf_simp.
  rewrite <- app_assoc.
  simpl.
  fcf_spec_ret.

Qed.

Theorem compFold_oc_equiv : 
  forall (A B S : Set)(eqdb : EqDec B)(eqds : EqDec S)(O : S -> A -> Comp (B * S))(lsa : list A)(initS : S),
    comp_spec eq 
              (compFold _
                        (fun (acc : list B * S) (d : A) =>
                           [rs, s]<-2 acc; z <-$ O s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
                        (nil, initS) lsa)
              ((oc_compMap _ (fun a : A => query a) lsa) S _ O initS).

  intuition.
  eapply comp_spec_eq_trans.
  eapply compFold_oc_equiv_h.
  fcf_ident_expand_r.
  fcf_skip.
  simpl.
  fcf_spec_ret.

Qed.

Theorem oc_compMap_qam :
  forall (A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B ) (ls : list A)(q : nat),
    (forall a, queries_at_most (c a) q) ->
    queries_at_most (oc_compMap _ c ls) (length ls * q)%nat.

  induction ls; intuition; simpl in *.
  econstructor.

  econstructor.
  auto.

  intuition.
  econstructor.
  econstructor.
  auto.
  intuition.
  econstructor.
  omega.

Qed.