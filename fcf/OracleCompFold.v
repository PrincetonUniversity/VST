
Set Implicit Arguments.

Require Import FCF.
Require Import CompFold.

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

Require Import PRF.

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
  econstructor. eauto.
  intuition.
  econstructor.
  wftac.
  
Qed.
