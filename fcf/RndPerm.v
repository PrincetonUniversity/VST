(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.CompFold.
Require Import fcf.RndListElem.
Require Import Permutation.

Local Open Scope list_scope.

Theorem removeFirst_In_length : 
  forall (A : Set)(eqd : EqDec A)(ls : list A)(a : A),
    In a ls ->
    length (removeFirst (EqDec_dec _ ) ls a) = pred (length ls).
  
  induction ls; intuition; simpl in *.
  intuition; subst.
  destruct (EqDec_dec eqd a0 a0); intuition.
  
  destruct (EqDec_dec eqd a0 a); subst.
  trivial.
  simpl.
  rewrite IHls.
  destruct ls; simpl in *; intuition.

  trivial.
Qed.

Fixpoint addInAllLocations(A : Type)(a : A)(ls : list A) :=
  match ls with
    | nil =>  (a :: nil) :: nil
    | a' :: ls' => 
      (a :: ls) :: map (fun x => a' :: x) (addInAllLocations a ls')
  end.

Fixpoint getAllPermutations(A : Type)(ls : list A) :=
  match ls with
    | nil => nil :: nil
    | a :: ls' =>
      let perms' := getAllPermutations ls' in
        flatten (map (addInAllLocations a) perms')
  end.

Theorem addInAllLocations_not_nil : 
  forall (A : Type) l (a : A),
    addInAllLocations a l = nil -> False.

  induction l; intuition; unfold addInAllLocations in *; simpl in *.
  inversion H.
  inversion H.

Qed.

Theorem getAllPermutations_not_nil : 
  forall (A : Type)(ls : list A),
    getAllPermutations ls = nil -> False.

  induction ls; intuition; simpl in *.
  inversion H.

  case_eq (getAllPermutations ls); intuition.
  rewrite H0 in H.
  simpl in *.
  apply app_eq_nil in H.
  intuition.
  eapply addInAllLocations_not_nil; eauto.
Qed.
  

Theorem addInAllLocations_perm : 
  forall (A : Type) x0 (a : A) ls2,
    In ls2 (addInAllLocations a x0) ->
    Permutation ls2 (a :: x0).

  induction x0; intuition; simpl in *.
  intuition; subst.
  eapply Permutation_refl.
  
  intuition; subst.
  eapply Permutation_refl.

  eapply in_map_iff in H0.
  destruct H0.
  intuition; subst.
  eapply perm_trans.
  2:{
    eapply perm_swap.
  }
  eapply perm_skip.
  eapply IHx0.
  trivial.

Qed.

Theorem getAllPermutations_perms : 
  forall (A : Set)(ls1 ls2 : list A),
    In ls2 (getAllPermutations ls1) ->
    Permutation ls1 ls2.

  induction ls1; intuition; simpl in *.
  intuition.
  subst.
  econstructor.

  eapply in_flatten in H.
  destruct H.
  intuition.
  eapply in_map_iff in H0.
  destruct H0.
  intuition.
  subst.
  eapply addInAllLocations_perm in H1.
  eapply perm_trans.
  2:{
    eapply Permutation_sym.
    eauto.
  }
  eapply perm_skip.
  eapply IHls1.
  trivial.
  
Qed.

Section ShuffleList.

  Variable A : Set.
  Hypothesis A_EqDec : EqDec A.

  Definition shuffle(ls : list A) :=
    o <-$ rndListElem _ (getAllPermutations ls);
    ret 
    match o with
      | None => nil
      | Some x => x
    end.
      
  Theorem shuffle_perm : 
    forall (ls1 ls2 : list A),
      In ls2 (getSupport (shuffle ls1)) ->
      Permutation ls2 ls1.

    intuition.
    unfold shuffle in *.
    repeat simp_in_support.
    destruct x.
    eapply Permutation_sym.
    eapply getAllPermutations_perms.    
    apply rndListElem_support in H0.
    trivial.

    apply rndListElem_support_None in H0.
    exfalso.
    eapply getAllPermutations_not_nil.
    eauto.

  Qed.

   Fixpoint permute(ls : list A)(sigma : list nat) : list A :=
    match sigma with
      | nil => nil
      | n :: sigma' => 
        match (nth_error ls n) with
          | None => nil
          | Some a => a :: (permute ls sigma')
        end
  end.

   Theorem nth_error_not_None : 
     forall (ls : list A)(n : nat),
       n < length ls ->
       nth_error ls n = None -> 
       False.

     induction ls; destruct n; intuition; simpl in *.
     omega.
     omega.
     inversion H0.
     eapply IHls; eauto.
     omega.
   Qed.

   Theorem permute_length_eq : 
     forall (sigma : list nat)(ls : list A),
       (forall n, In n sigma -> n < length ls) ->
       length (permute ls sigma) = length sigma.
     
     induction sigma; intuition; simpl in *.
     case_eq (nth_error ls a); intuition.
     simpl.
     f_equal.
     eapply IHsigma; intuition.
     

     exfalso.
     eapply nth_error_not_None.
     eapply H.
     intuition.
     trivial.
   Qed.
   
   Theorem shuffle_Permutation : 
     forall (ls1 ls2 : list A),
       In ls2 (getSupport (shuffle ls1)) ->
       Permutation ls1 ls2.
     
     intuition.

     unfold shuffle in *.
     repeat simp_in_support.
     destruct x.
     eapply rndListElem_support in H0.
     eapply getAllPermutations_perms.
     trivial.

     eapply rndListElem_support_None in H0.
     exfalso.
     eapply getAllPermutations_not_nil.
     eauto.

    Qed.
  
    Theorem shuffle_wf : 
      forall ls,
        well_formed_comp (shuffle ls).

      intuition.
      unfold shuffle.
      wftac.
      eapply rndListElem_wf.

    Qed.

End ShuffleList.

Definition RndPerm(n : nat) :=
  shuffle _ (allNatsLt n).

Theorem list_pred_map_both':
  forall (A B C D : Set) (lsa : list A) (lsb : list B) 
    (P : C -> D -> Prop) (f : A -> C)(g : B -> D),
  list_pred (fun (a : A) (b : B) => P (f a) (g b)) lsa lsb ->
  list_pred P (map f lsa) (map g lsb).

  intuition.
  eapply list_pred_impl.
  eapply list_pred_map_both.
  eauto.
  intuition.
  destruct H0.
  destruct H0.
  intuition; subst.
  trivial.

Qed.

Theorem addInAllLocations_pred : 
  forall (A B : Set) (R : A -> B -> Prop) (a : list A) (b : list B),
    list_pred R a b ->
    forall a1 a2,
      R a1 a2 ->
  list_pred (list_pred R) (addInAllLocations a1 a) (addInAllLocations a2 b).
  
  induction 1; intuition; simpl in *.
  
  econstructor.
  econstructor.
  trivial.
  econstructor.
  econstructor.
  

  econstructor.
  repeat econstructor;assumption.

  eapply list_pred_map_both'.
  eapply list_pred_impl.
  eauto.
  intuition.
  econstructor; assumption.

Qed.

Theorem getAllPermutations_pred :
  forall (A B : Set)(R : A -> B -> Prop)(lsa : list A)(lsb : list B),
  list_pred R lsa lsb ->
     list_pred (list_pred R) (getAllPermutations lsa) (getAllPermutations lsb).

  induction 1; intuition; simpl in *.
  econstructor.
  econstructor.
  econstructor.

  eapply list_pred_flatten_both.
  eapply list_pred_map_both'.
  eapply list_pred_impl.
  eauto.
  intuition.
  
  eapply addInAllLocations_pred; intuition.
Qed.

Theorem nth_error_app_Some : 
  forall (A : Set)(ls : list A) n (a a' : A),
    nth_error ls n = Some a ->
    nth_error (ls ++ (a' :: nil)) n = Some a.

  induction ls; destruct n; intuition; simpl in *.
  inversion H.
  inversion H.

  eapply IHls.
  trivial.

Qed.

Theorem nth_error_app_length : 
  forall (A : Set)(ls : list A) (a : A),
    nth_error (ls ++ (a :: nil)) (length ls) = Some a.

  induction ls; intuition; simpl in *.
  
Qed.

Theorem allNats_nth_pred : 
  forall (A : Set)(ls : list A),
   list_pred (fun (a : A) (b : nat) => nth_error ls b = Some a) ls
     (allNatsLt (length ls)).

  induction ls using rev_ind; intuition; simpl in *.
  econstructor.
 
  rewrite app_length.
  simpl.
  rewrite plus_comm.
  simpl.

  eapply list_pred_app_both.
  eapply list_pred_impl.
  eapply IHls.
  intuition.


  eapply nth_error_app_Some; intuition.

  econstructor.


  eapply  nth_error_app_length .

  econstructor.
  
Qed.

Theorem permute_nth_equiv : 
  forall (A : Set)(ls : list A) a b,
  list_pred (fun (a0 : A) (b0 : nat) => nth_error ls b0 = Some a0) a b ->
  a = permute ls b.

  induction a; inversion 1; intuition; simpl in *.
  subst.
  
  rewrite H2.
  f_equal.
  eapply IHa.
  trivial.
Qed.

Theorem getAllPerms_permute_eq :
  forall (A : Set)(ls : list A),
  list_pred (fun (a : list A) (b : list nat) => a = permute ls b)
     (getAllPermutations ls) (getAllPermutations (allNatsLt (length ls))).

  intuition.

  generalize (@getAllPermutations_pred _ _ (fun a b => nth_error ls b = Some a) ls (allNatsLt (length ls))) ; intros.
  eapply list_pred_impl.
  eapply H.

  eapply allNats_nth_pred.

  intuition.

  eapply permute_nth_equiv.
  trivial.
  
Qed.

Theorem list_pred_nth_exists : 
  forall (A B : Set)(P : A -> B -> Prop) lsa lsb,
    list_pred P lsa lsb ->
    forall n a, 
      nth_option lsa n = Some a -> exists b, nth_option lsb n = Some b /\ P a b.

  induction 1; intuition; simpl in *.
  discriminate.

  destruct n.
  inversion H1; clear H1; subst.
  econstructor; intuition.

  edestruct IHlist_pred; eauto.

Qed.

Theorem rndListElem_pred : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(P : A -> B -> Prop)(lsa : list A)(lsb : list B),
    list_pred P lsa lsb ->
    comp_spec (fun a b => 
      match a with
        | None => b = None
        | Some a' => exists b', b = Some b' /\ P a' b'
      end) (rndListElem _ lsa) (rndListElem _ lsb).


  intuition.
  unfold rndListElem in *.
  case_eq (length lsa); intuition.
  erewrite <- list_pred_length_eq; eauto.
  rewrite H0.
  eapply comp_spec_ret; intuition.
  
  erewrite <- list_pred_length_eq; eauto.
  rewrite H0.
  comp_skip.
  apply None.
  apply None.
  eapply comp_spec_ret; intuition.

  case_eq (nth_option lsa b); intuition.

  edestruct list_pred_nth_exists; eauto.

  exfalso.
  eapply nth_option_not_None; eauto.
  apply RndNat_support_lt in H1.
  omega.
Qed.

Theorem shuffle_RndPerm_spec : 
  forall (A : Set)(eqd : EqDec A)(ls : list A),
    comp_spec (fun a b => a = permute ls b)
    (shuffle eqd ls)
    (shuffle _ (allNatsLt (length ls))).

  intuition.
  unfold shuffle in *.
  
  comp_skip.
  eapply rndListElem_pred.
  eapply getAllPerms_permute_eq.
  
  simpl in H1.
  eapply comp_spec_ret; intuition.
  destruct a.
  destruct H1.
  intuition.
  subst.
  trivial.

  subst.
  simpl.
  intuition.
Qed.

Theorem shuffle_RndPerm_spec_eq : 
  forall (A : Set)(eqd : EqDec A)(ls : list A),
    comp_spec eq
    (shuffle eqd ls)
    (x <-$ RndPerm (length ls); ret permute ls x).

  intuition.
  eapply comp_spec_eq_trans.
  eapply comp_spec_eq_symm.
  eapply comp_spec_right_ident.
  comp_skip.
  eapply shuffle_RndPerm_spec.
  eapply comp_spec_ret; intuition.

Qed.

Theorem RndPerm_In_support : 
  forall n ls, 
    In ls (getSupport (RndPerm n)) ->
    Permutation (allNatsLt n) ls.
  
  intuition.
  eapply shuffle_Permutation.
  eapply H.
Qed.


Theorem RndPerm_In_support_length :
  forall n ls,
    In ls (getSupport (RndPerm n)) ->
    length ls = n.

  intuition.
  erewrite Permutation_length.
  2:{
    eapply Permutation_sym.
    eapply RndPerm_In_support.
    eauto.
  }
  eapply allNatsLt_length.
Qed.

Theorem RndPerm_wf : 
  forall n,
    well_formed_comp (RndPerm n).

  intuition.
  unfold RndPerm.
  eapply shuffle_wf.

Qed.