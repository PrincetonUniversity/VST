(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* Additional facts about fold and special kinds of fold (e.g. iterated sums) *)

Set Implicit Arguments.

Require Import fcf.Rat.
Require Import List.
Require Import Permutation.
Require Import Arith.
Require Import fcf.EqDec.
Require Import fcf.StdNat.
Require Import Bool.

Local Open Scope rat_scope.

(* The traditional functional zip and unzip. *)
(* TODO: get rid of these and replace with combine and split *)
Definition unzip(A B : Set)(ls : list (A * B)) :=
  (map (@fst _ _) ls, map (@snd _ _) ls).

Fixpoint zip(A B : Set)(lsa : list A)(lsb : list B) :=
  match lsa with
    | nil => nil
    | a :: lsa' =>
      match lsb with
        | nil => nil
        | b :: lsb' =>
          (a, b) :: (zip lsa' lsb')
      end
  end.


Ltac pairInv := 
  match goal with
    | [H : (_, _) = (_, _) |- _] => 
      inversion H; clear H; subst
  end.

(* RemoveDups -- Removing duplicates from a list *)
Section RemoveDups.

  Variable A : Set.
  Variable eqd : EqDec A.

  Fixpoint removeDups(ls : list A) :=
    match ls with
      | nil => nil
      | a' :: ls' =>
        if (in_dec (EqDec_dec _) a' ls') then (removeDups ls') else (a' :: (removeDups ls'))
    end.

  Theorem removeDups_in : 
    forall (ls : list A) a,
      In a (removeDups ls) ->
      In a ls.
    
    induction ls; intuition; simpl in *.
    destruct (in_dec (EqDec_dec eqd) a ls).
    right.
    eauto.
    
    simpl in *.
    intuition.
  Qed.
  
  Theorem removeDups_NoDup :
    forall (ls : list A),
      NoDup (removeDups ls).
    
    induction ls; intuition; simpl in *.
    
    econstructor.
    
    destruct (in_dec (EqDec_dec eqd) a ls); intuition.
    econstructor; intuition.
    eapply n.
    eapply removeDups_in.
    trivial.
    
  Qed.

  Lemma in_removeDups : 
    forall (ls : list A) a,
      In a ls -> 
      In a (removeDups ls).
    
    induction ls; intuition; simpl in *.
    
    intuition; subst.
    
    destruct (in_dec (EqDec_dec eqd) a0 ls).
    eauto.
    simpl.
    intuition.
    
    destruct (in_dec (EqDec_dec eqd) a ls).
    eauto.
    simpl.
    right.
    eauto.
    
  Qed.
     

End RemoveDups.


(* ListReplace -- replace a single element in a list. *)
Section ListReplace.

  Variable A : Set.

  Fixpoint listReplace (ls : list A)(i : nat)(a def : A) :=
    match i with
      | O => 
        match ls with
        | nil => a :: nil
        | a' :: ls' => a :: ls'
        end
      | S i' => 
        match ls with
        | nil => def :: (listReplace nil i' a def)
        | a' :: ls' =>
          a' :: (listReplace ls' i' a def)
        end
    end.

End ListReplace.

Section SumList.

  Variable A : Set.

  Definition sumList(ls : list A)(f : A -> Rat) := fold_left (fun a b => a + (f b)) ls 0.

  (* Facts about sumList *)
 

  Theorem sumList_ne_0 : forall (ls : list A)(f : A -> Rat),
    ~ (sumList ls f) == 0 ->
    exists b : _,
      In b ls /\
      ~ ((f b) == 0).
  Abort.

  Theorem sumList_perm : forall (ls1 ls2 : list A)(f1 f2 : A -> Rat),
    Permutation ls1 ls2 ->
    (forall b, (f1 b) == (f2 b)) ->
    (sumList ls1 f1) == (sumList ls2 f2).
  Abort.

  
  Lemma fold_add_init : forall (ls : list A)(f : A -> Rat) init1 init2,
    fold_left (fun (r : Rat) (a : A) => r + (f a)) ls (init1 + init2) == 
    init1 + (fold_left (fun (r : Rat) (a : A) => r + (f a)) ls init2).
    
    induction ls; intuition; simpl in *.
    eapply eqRat_refl.
    
    eapply eqRat_trans.
    eapply IHls.
    eapply eqRat_trans.
    eapply ratAdd_assoc.
    eapply ratAdd_eqRat_compat.
    eapply eqRat_refl.
    eapply eqRat_symm.
    eapply IHls.
  Qed.

  Lemma fold_add_body_eq : forall (ls : list A)(f1 f2 : A -> Rat) init1 init2,
    init1 == init2 ->
    (forall a, In a ls -> f1 a == f2 a) ->
    fold_left (fun r a => r + (f1 a)) ls init1 == fold_left (fun r a => r + (f2 a)) ls init2.
    
    induction ls; intuition; simpl in *.
    
    eapply IHls; eauto.
    eapply ratAdd_eqRat_compat; eauto.
  Qed.

  Lemma fold_add_rat_perm : forall (ls1 ls2 : list A)(f1 f2 : A -> Rat),
    Permutation ls1 ls2 ->
    forall init1 init2, 
      init1 == init2 ->
      (forall (a : A), In a ls1 -> (f1 a) == (f2 a)) ->
      fold_left (fun r a => r + (f1 a)) ls1 init1 == fold_left (fun r a => r + (f2 a)) ls2 init2.
    
    induction 1; intuition; simpl in *.
    
    eapply IHPermutation; eauto.
    eapply ratAdd_eqRat_compat; eauto.
    
    eapply fold_add_body_eq.
    eapply eqRat_trans.
    eapply ratAdd_assoc.
    eapply eqRat_trans.
    2:{
      eapply eqRat_symm.
      eapply ratAdd_assoc.
    }
    eapply ratAdd_eqRat_compat; eauto.
    eapply eqRat_trans.
    eapply ratAdd_comm.
    eapply ratAdd_eqRat_compat; eauto.
    intuition.
    
    eapply eqRat_trans; eauto.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply eqRat_symm; eauto.
    intuition.
    eapply eqRat_symm.
    eapply H2.
    eapply Permutation_in.
    eapply Permutation_sym.
    eauto.
    eauto.
    
    simpl.
    eapply IHPermutation2.
    trivial.
    intuition.
    eapply H2.
    eapply Permutation_in.
    eapply Permutation_sym.
    eauto.
    eauto.
  Qed.


  Lemma fold_add_f_inverse : forall (B : Set)(ls : list A)(f : A -> B)(f_inv : B -> A) fa init1 init2,
    (init1 == init2) ->
    (forall a, In a ls -> f_inv (f a) = a) ->
    fold_left (fun r b => r + fa (f_inv b)) (map f ls) init1 ==
    fold_left (fun r a => r + (fa a)) ls init2.
    
    induction ls; intuition; simpl in *.
    
    eapply IHls; eauto.
    rewrite H0.
    eapply ratAdd_eqRat_compat; eauto.
    eapply eqRat_refl.
    intuition.
  Qed.

   Lemma sumList_0 : forall (ls : list A) f,
    (sumList ls f == 0) <-> (forall a, In a ls -> (f a) == 0).
    
    induction ls; intuition; simpl in *.
    
    intuition.
    unfold sumList.
    simpl.
    eapply eqRat_refl.
    
    intuition; subst.
    unfold sumList in *; simpl in *.
    eapply eqRat_trans.
    eapply ratAdd_0.
    eapply eqRat_trans.
    eapply ratAdd_comm.
    eapply eqRat_trans.
    eapply eqRat_symm.
    eapply fold_add_init.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    eapply H.
    eapply eqRat_refl.
    
    eapply IHls.
    unfold sumList in *; simpl in *.
    eapply ratAdd_0.
    eapply eqRat_trans.
    eapply eqRat_symm.
    eapply fold_add_init.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    eapply H.
    trivial.
    
    unfold sumList.
    simpl.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    eapply eqRat_trans.
    eapply fold_add_init.
    eapply ratAdd_0.
    intuition.
    unfold sumList in *.
    eapply IHls.
    intuition.
  Qed.

  Lemma sumList_nz : forall (ls : list A) f,
    (~sumList ls f == 0) <-> exists a : _, In a ls /\ (~f a == 0).
    
    induction ls; intuition; unfold sumList in *; simpl in *.
    
    exfalso.
    apply H.
    eapply eqRat_refl.
    
    destruct H.
    intuition.
    
    assert (f a + fold_left (fun r a => r + f a) ls 0 == 0 -> False).
    intuition.
    eapply H.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    eapply eqRat_trans.
    eapply fold_add_init.
    trivial.
    eapply ratAdd_nz in H0.
    destruct H0.
    econstructor; intuition.
    
    apply IHls in H0.
    destruct H0; intuition.
    exists x.
    intuition.
    
    assert (f a + fold_left (fun r a => r + f a) ls 0 == 0).
    eapply eqRat_trans.
    eapply eqRat_symm.
    eapply fold_add_init.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    trivial.
    apply ratAdd_0 in H1.
    intuition.
    
    destruct H.
    intuition.
    subst.
    intuition.
    
    apply IHls in H3; intuition.
    econstructor; eauto.
  Qed.

End SumList.

Lemma fold_add_init_0 : forall (A : Set)(ls : list A) f init,
  fold_left (fun r a => r + (f a)) ls init == init + fold_left (fun r a => r + (f a)) ls 0.
  intuition.
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  rewrite ratAdd_0_r.
  apply eqRat_refl.
  apply eqRat_refl.
  apply fold_add_init.
Qed.

Lemma fold_add_eq_init : forall (A : Set)(ls : list A) init,
  fold_left (fun r a => r + 0) ls init == init.
  
  induction ls; intuition; simpl in *; intuition.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_r.
  apply eqRat_refl.
  apply eqRat_refl.
  trivial.
Qed.

Lemma fold_add_eq_init_f : forall (A : Set)(ls : list A) f init,
  (forall a, In a ls -> (f a) == 0) ->
  fold_left (fun r a => r + (f a)) ls init == init.
  
  intuition.
  eapply eqRat_trans.
  eapply fold_add_body_eq.
  apply eqRat_refl.
  eapply H.
  simpl.
  eapply fold_add_eq_init.
Qed.

Lemma fold_add_eq : forall (A : Set)(ls : list A)(f1 f2 : A -> Rat) init1 init2,
  fold_left (fun r a => r + (f1 a)) ls init1 + 
  fold_left (fun r a => r + (f2 a)) ls init2 ==
  fold_left (fun r a => r + (f1 a + f2 a)) ls (init1 + init2).
        
  induction ls; intuition; simpl in *.
  eapply eqRat_refl.
  
  rewrite IHls.
  eapply fold_add_body_eq.
  
  repeat rewrite <- ratAdd_assoc.
  apply ratAdd_eqRat_compat; intuition.
  rewrite ratAdd_assoc.
  rewrite ratAdd_assoc.
  apply ratAdd_eqRat_compat; intuition.
  eapply ratAdd_comm.
  
  intuition.
Qed.

Lemma fold_add_comm : forall (A B : Set)(lsa : list A)(lsb : list B) f,
  fold_left (fun r1 a => r1 + (fold_left (fun r2 b => r2 + (f a b)) lsb 0)) lsa 0  == 
  fold_left (fun r1 b => r1 + (fold_left (fun r2 a => r2 + (f a b)) lsa 0)) lsb 0.
  induction lsa; destruct lsb; intuition; simpl in *; intuition.
  
  apply eqRat_symm.
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_r.
  apply eqRat_refl.
  apply eqRat_refl.
  apply fold_add_eq_init.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_r.
  apply eqRat_refl.
  apply eqRat_refl.
  apply fold_add_eq_init.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_l.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_l.
  apply eqRat_refl.
  apply eqRat_refl.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_l.
  apply eqRat_refl.
  apply eqRat_refl.
  simpl.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  eapply eqRat_refl.
  eapply fold_add_init_0.
  simpl.
  eapply eqRat_trans.
  eapply fold_add_init_0.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  apply eqRat_refl.
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  apply ratAdd_0_r.
  apply eqRat_refl.
  apply eqRat_symm.
  
  eapply fold_add_eq.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  apply eqRat_refl.
  apply ratAdd_eqRat_compat.
  apply eqRat_refl.
  
  eapply IHlsa.
  
  eapply eqRat_symm.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_l.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_l.
  apply eqRat_refl.
  apply eqRat_refl.
  eapply fold_add_body_eq; intuition.
  rewrite <- ratAdd_0_l.
  apply eqRat_refl.
  apply eqRat_refl.
  simpl.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  eapply eqRat_refl.
  eapply fold_add_init_0.
  simpl.
  eapply eqRat_trans.
  eapply fold_add_init_0.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  apply eqRat_refl.
  eapply eqRat_trans.
  eapply fold_add_body_eq; intuition.
  apply ratAdd_0_r.
  apply eqRat_refl.
  apply eqRat_symm.
  eapply fold_add_eq.
  
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply fold_add_init_0.
  eapply eqRat_refl.

  eapply eqRat_symm.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply fold_add_init_0.
  eapply eqRat_refl.
  
  repeat rewrite <- ratAdd_assoc.
  eapply ratAdd_eqRat_compat.
  repeat rewrite (ratAdd_assoc (f a b)).
  eapply ratAdd_eqRat_compat; intuition.
  eapply ratAdd_comm.
  eapply eqRat_refl.

Qed.

Lemma sumList_comm : forall (A B : Set)(lsa : list A)(lsb : list B) f,
  sumList lsa (fun a => sumList lsb (fun b => (f a b))) == 
  sumList lsb (fun b => sumList lsa (fun a => (f a b))).
  
  intuition.
  eapply fold_add_comm; intuition.
Qed.

Lemma sumList_body_eq : forall (A : Set)(ls : list A)(f1 f2 : A -> Rat),
  (forall a, In a ls -> f1 a == f2 a) ->
  sumList ls f1 == sumList ls f2.
  
  intuition.
  eapply fold_add_body_eq; intuition.
Qed.

Lemma fold_add_factor_constant_r : forall (A : Set)(ls : list A)(f : A -> Rat) init c,
  fold_left (fun r a => r + (f a) * c) ls (init * c) == 
  (fold_left (fun r a => r + (f a)) ls init) * c.
  
  induction ls; intuition; simpl in *.
  
  intuition.
  
  eapply eqRat_trans.
  eapply fold_add_body_eq.
  eapply eqRat_symm.
  eapply ratMult_distrib_r.
  intuition.
  eapply eqRat_refl.
  
  eapply IHls.
Qed.
    
Lemma sumList_factor_constant_r : forall (A : Set)(ls : list A)(f : A -> Rat) c,
  sumList ls (fun a => (f a) * c) == (sumList ls f) * c.
  
  intuition.
  unfold sumList.   
  
  rewrite <- fold_add_factor_constant_r.
  eapply fold_add_body_eq.
  eapply eqRat_symm.
  eapply ratMult_0_l.
  intuition.
  
Qed.
    
Lemma sumList_factor_constant_l:
  forall (A : Set) (ls : list A) (f : A -> Rat) (c : Rat),
    sumList ls (fun a : A => c * f a) == c * sumList ls f.
  
  intuition.
  eapply eqRat_trans.
  eapply sumList_body_eq; intuition.
  apply ratMult_comm.
  eapply eqRat_trans.
  eapply sumList_factor_constant_r.
  apply ratMult_comm.
Qed.

Lemma fold_add_body_const : forall (A : Set)(ls : list A) c init,
  fold_left (fun r a => r + c) ls init == c * (length ls / 1) + init.
  
  induction ls; intuition; simpl in *.
  eapply eqRat_trans.
  eapply ratAdd_0_l.
  eapply ratAdd_eqRat_compat.
  eapply eqRat_symm.
  apply ratMult_0_r.
  intuition.
  
  rewrite IHls.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  apply eqRat_refl.
  apply ratAdd_comm.
  rewrite <- (ratAdd_assoc).
  apply ratAdd_eqRat_compat; intuition.
  eapply eqRat_symm.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  apply eqRat_refl.
  apply ratS_num.
  rewrite ratMult_distrib.
  rewrite ratAdd_comm.
  apply ratAdd_eqRat_compat; intuition.
  apply ratMult_1_r.
Qed.

Lemma sumList_body_const : forall (A : Set)(ls : list A) c,
  sumList ls (fun a => c) == c * (length ls / 1).
  
  intuition.
  eapply eqRat_trans.
  apply fold_add_body_const.
  rewrite <- ratAdd_0_r.
  eapply eqRat_refl.
Qed.


Lemma fold_add_iter_le : forall (A : Set)(ls : list A) f r init,
  fold_left (fun r a => r + (f a)) ls init <= r ->
  init <= r /\ 
  (forall a, In a ls -> f a <= r).
  
  induction ls; intuition; simpl in *;
    intuition; subst.
  
  assert (init + f a <= r).
  eapply IHls.
  apply H.
  
  eapply ratAdd_any_le; eauto.
  
  assert (init + f a0 <= r).
  eapply IHls.
  eauto.
  eapply ratAdd_any_le.
  eapply leRat_trans.
  apply eqRat_impl_leRat.
  apply ratAdd_comm.
  eauto.
  
  edestruct IHls; eauto.
Qed.

Lemma sumList_iter_le : forall (A : Set)(ls : list A) f r a,
  sumList ls f <= r ->
  In a ls ->
  f a <= r.
  
  intuition.
  eapply fold_add_iter_le; eauto.
Qed.



Fixpoint removeFirst(A : Set)(eqd : eq_dec A)(ls : list A) a :=
  match ls with
    | nil => nil
    | a' :: ls' =>
      if (eqd a a') then ls' else a' :: (removeFirst eqd ls' a)
  end.

Lemma removeFirst_permutation : forall (A : Set)(eqd : eq_dec A)(ls : list A) a,
  In a ls ->
  Permutation ls (a :: (removeFirst eqd ls a)).
  
  induction ls; intuition; simpl in *;
    intuition; subst.
  
  destruct (eqd a0 a0); try congruence.
  eapply Permutation_refl.
  
  destruct (eqd a0 a); subst.
  eapply Permutation_refl.
  eapply perm_trans; [idtac | eapply perm_swap].
  eapply perm_skip.
  eauto.
Qed.

Lemma removeFirst_not_in : forall (A : Set)(eqd : eq_dec A)(ls : list A) a1 a2,
  ~In a1 ls ->
  ~In a1 (removeFirst eqd ls a2).
  
  induction ls; intuition; simpl in *.
  destruct (eqd a2 a); subst.
  intuition.
  simpl in *.
  intuition.
  eapply IHls; eauto.
Qed.

Lemma removeFirst_NoDup_not_in : forall (A : Set)(eqd : eq_dec A)(ls : list A)(a : A),
  NoDup ls ->
  ~In a (removeFirst eqd ls a).
  
  induction ls; intuition; simpl in *.
  
  inversion H; clear H; subst.
  destruct(eqd a0 a); subst.
  intuition.
  simpl in *.
  intuition; subst.
  eapply IHls; eauto.
  
Qed.

Lemma removeFirst_NoDup : forall (A : Set)(eqd : eq_dec A)(ls : list A) a,
  NoDup ls ->
  NoDup (removeFirst eqd ls a).
  
  induction ls; intuition; simpl in *.
  inversion H; clear H; subst.
  destruct (eqd a0 a); subst.
  trivial.
  
  econstructor.
  eapply removeFirst_not_in.
  intuition.
  eapply IHls; eauto.
  
Qed.

Lemma removeFirst_in : forall (A : Set)(eqd : eq_dec A)(ls : list A)(a1 a2 : A),
  In a1 ls ->
  a1 <> a2 ->
  In a1 (removeFirst eqd ls a2).
  
  induction ls; intuition; simpl in *.
  destruct (eqd a2 a); subst.
  intuition.
  congruence.
  
  simpl.
  intuition.
Qed.

Lemma removeFirst_in_iff : forall (A : Set)(eqd : eq_dec A)(ls : list A) a1 a2,
  In a1 (removeFirst eqd ls a2) ->
  In a1 ls.
  
  induction ls; intuition; simpl in *.
  destruct (eqd a2 a); subst.
  intuition.
  
  simpl in *.
  intuition.
  right.
  eapply IHls; eauto.
  
Qed.


(* ls1 is the smaller set.  This function returns a permutation of ls2 where the first elements of ls2 match the order of the elements in ls1.  This function only works if ls1 is a subset of ls2. *)
Fixpoint matchOrder (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A) :=
  match ls1 with
    | nil => ls2
    | a :: ls1' => 
      a :: (matchOrder eqd ls1' (removeFirst eqd ls2 a))
  end.

Lemma matchOrder_In : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> In a ls2) ->
  (forall a, In a ls2 <-> In a (matchOrder eqd ls1 ls2)).
  
  induction ls1; destruct ls2; intuition; simpl in *; eauto; intuition; subst.
  
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  
  destruct (eqd a a1); subst.
  intuition.
  right.
  eapply (IHls1 (a1 :: removeFirst _ ls2 a)); intuition.
  econstructor.
  
  eapply removeFirst_not_in; intuition.
  
  eapply removeFirst_NoDup; intuition.
  simpl.
  destruct (H1 a0); auto.
  right.
  
  eapply removeFirst_in; eauto.
  intuition. subst.
  intuition.
  
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  destruct (H1 a); intuition; subst.
  destruct (eqd a a); try congruence.
  right.
  eapply (IHls1 ls2); intuition.
  destruct (H1 a0); intuition; subst.
  intuition.
  
  destruct (eqd a a0); try congruence.
  
  destruct (eqd a a1); subst; auto.
  right.
  eapply (IHls1 (a0 :: removeFirst _ ls2 a)); intuition.
  econstructor.
  eapply removeFirst_not_in; trivial.
  eapply removeFirst_NoDup; trivial.
  simpl.
  destruct (H1 a2); eauto.
  destruct (eqd a0 a2); intuition.
  right.
  eapply removeFirst_in; trivial.
  
  intuition.
  subst.
  intuition.
  
  simpl.
  destruct (eqd a0 a1); intuition.
  right.
  eapply removeFirst_in; trivial.
  intuition.      
  
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  
  destruct (eqd a0 a1); subst; intuition.
  right.
  
  assert (In a1 (if eqd a a0 then ls2 else a0 :: removeFirst eqd ls2 a)).
  eapply IHls1.
  trivial.
  destruct (eqd a a0).
  trivial.
  econstructor.
  eapply removeFirst_not_in; eauto.
  eapply removeFirst_NoDup; intuition.
  intuition.
  
  destruct (eqd a a0).
  destruct (H1 a2).
  intuition.
  subst.
  intuition.
  trivial.
  simpl.
  destruct (eqd a0 a2); intuition.
  right.
  
  destruct (H1 a2).
  destruct (eqd a a2); intuition.
  subst.
  intuition.
  eapply removeFirst_in.
  trivial.
  intuition. subst.
  intuition.
  
  trivial.
  
  destruct (eqd a a0); intuition.
  simpl in *.
  intuition.
  eapply removeFirst_in_iff.
  eauto.
  
Qed.

Lemma matchOrder_not_in_h : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A) a,
  ~In a ls1 -> 
  ~In a ls2 ->
  ~In a (matchOrder eqd ls1 ls2).
  
  induction ls1; intuition; simpl in *.
  intuition; subst.
  eapply (IHls1 (removeFirst eqd ls2 a)).
  eapply H3.
  intuition.
  eapply removeFirst_not_in.
  intuition.
  eapply H0.
  eauto.
  eapply H.
  eauto.
Qed.

Lemma matchOrder_not_in : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A) a,
  (forall a, In a ls1 -> In a ls2) ->
  ~In a ls2 ->
  ~In a (matchOrder eqd ls1 ls2).
  
  induction ls1; intuition; simpl in *.
  
  destruct (eqd a a0); subst;
    intuition.
  eapply IHls1.
  intuition.
  eapply H0.
  assert (~ In a0 ls1).
  intuition.
  specialize (@matchOrder_not_in_h _ eqd ls1 (removeFirst eqd ls2 a) a0); intuition.
  exfalso.
  eapply H4; eauto.
  intuition.
  eapply removeFirst_not_in.
  intuition.
  eapply H0.
  eapply H5.
  eapply H3.
Qed.


Lemma matchOrder_NoDup : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
  (forall a, In a ls1 -> In a ls2) ->
  NoDup ls2 ->
  NoDup ls1 ->
  NoDup (matchOrder eqd ls1 ls2).
  
  induction ls1; intuition; simpl in *.
  inversion H1; clear H1; subst.
  econstructor.
  eapply matchOrder_not_in.
  intuition.
  destruct (eqd a a0); subst; intuition.
  eapply removeFirst_in.
  eapply H.
  intuition.
  intuition.
  eapply removeFirst_NoDup_not_in; eauto.
  
  eapply IHls1; intuition.
  destruct (eqd a a0); subst; intuition.
  eapply removeFirst_in; eauto.
  eapply removeFirst_NoDup; eauto.
Qed.

Require Import Permutation.

Lemma matchOrder_permutation : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> In a ls2) ->
  Permutation ls2 (matchOrder eqd ls1 ls2).
  
  intuition.
  eapply NoDup_Permutation; intuition.      
  
  eapply matchOrder_NoDup; eauto.
  
  eapply (@matchOrder_In _ eqd ls1 ls2); eauto.
  eapply (@matchOrder_In _ eqd ls1 ls2); eauto.      
  
Qed.

Lemma matchOrder_firstn : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> In a ls2) ->
  firstn (length ls1) (matchOrder eqd ls1 ls2) = ls1.
  
  induction ls1; intuition; simpl in *.
  inversion H; clear H; subst.
  f_equal.
  eapply IHls1; eauto.
  eapply removeFirst_NoDup; eauto.
  intuition.
  destruct (eqd a0 a); subst; intuition.
  eapply removeFirst_in.
  eapply H1.
  intuition.
  intuition.
Qed.

Lemma fold_add_matchOrder : forall (A : Set)(ls : list A)(f : A -> Rat) n init1 init2,
  init1 == init2 ->
  NoDup ls ->
  (forall a, In a ls -> (~In a (firstn n ls)) -> (f a) == 0) ->
  fold_left (fun r a => r + (f a)) (firstn n ls) init1 == fold_left (fun r a => r + (f a)) ls init2.
  
  induction ls; intuition; simpl in *.
  
  destruct n; simpl in *;
    trivial.
  
  inversion H0; clear H0; subst.
  
  destruct n; simpl in *.
  
  eapply eqRat_symm.
  eapply eqRat_trans.
  eapply fold_add_eq_init_f; intuition.
  rewrite (ratAdd_0_r init1).
  eapply ratAdd_eqRat_compat; intuition.
  
  eapply IHls.
  eapply ratAdd_eqRat_compat; intuition.
  trivial.
  intuition.
  eapply H1.
  intuition.
  intuition.
  subst.
  intuition.
  
Qed.

Lemma permutation_NoDup : forall (A : Type)(ls1 ls2 : list A),
  Permutation ls1 ls2 ->
  NoDup ls1 ->
  NoDup ls2.
  
  induction 1; intuition.
  inversion H0; clear H0; subst.
  econstructor.
  intuition.
  eapply H3.
  eapply Permutation_in.
  eapply Permutation_sym.
  eapply H.
  eauto.
  eauto.
  
  inversion H; clear H; subst.
  inversion H3; clear H3; subst.
  simpl in *.
  
  econstructor.
  simpl.
  intuition.
  econstructor;
    intuition.
Qed.

Lemma fold_add_subset : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A)(f : A -> Rat) init1 init2,
  init1 == init2 ->
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> In a ls2) ->
  (forall a, (~In a ls1) -> (f a) == 0) ->
  fold_left (fun r a => r + (f a)) ls1 init1 == fold_left (fun r a => r + (f a)) ls2 init2.
  
  intuition.
  
  erewrite <- matchOrder_firstn at 1.
  
  eapply eqRat_symm.
  eapply eqRat_trans.
  eapply fold_add_rat_perm.
  eapply matchOrder_permutation.
  eapply H0.
  eauto.
  intuition.
  eapply eqRat_refl.
  intuition.
  eapply eqRat_refl.
  
  eapply eqRat_symm.
  eapply fold_add_matchOrder; intuition.
  eapply permutation_NoDup.
  eapply matchOrder_permutation; eauto.
  eauto.
  eapply H3.
  intuition.      
  eapply H5.
  rewrite matchOrder_firstn; eauto.
  eauto.
  eauto.
  eauto.
  
  Grab Existential Variables.
  trivial.
Qed.

Lemma sumList_subset : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A)(f : A -> Rat),
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> In a ls2) ->
  (forall a, (~In a ls1) -> (f a) == 0) ->
  sumList ls1 f == sumList ls2 f.
  
  intuition.
  eapply fold_add_subset; intuition.
  
Qed.

Fixpoint flatten(A : Type)(ls : list (list A)) :=
  match ls with
    | nil => nil
    | a :: ls' => a ++ (flatten ls')
  end.

Theorem in_flatten : forall (A : Set)(ls : list (list A)) a,
  In a (flatten ls) <->
  exists x : _, In x ls /\ In a x.

  induction ls; simpl in *; intuition.
  
  destruct H; intuition.

  apply in_app_or in H.
  intuition.
  exists a; intuition.

  apply IHls in H0.
  destruct H0.
  intuition.
  exists x; intuition.
 
  apply in_or_app.
  destruct H; intuition.
  subst.
  intuition.

  right.
  eapply IHls.
  econstructor.
  eauto.
Qed.

Theorem length_flatten_nz : forall (A : Type)(ls : list (list A)) ls',
  In ls' ls ->
  length ls' > 0 ->
  length (flatten ls) > 0.
  
  induction ls; destruct ls'; intuition; simpl in *.
  intuition.
  
  destruct H; simpl in *; subst; intuition.
  
  destruct H; simpl in *; subst; intuition.
  rewrite app_length.
  simpl.
  omega.
  
  rewrite app_length.
  specialize (IHls (a0 :: ls') H).
  simpl in *.
  intuition.
  
Qed.

Fixpoint getUnique(A : Set)(ls : list A)(pf : eq_dec A) : list A :=
  match ls with
    | nil => nil
    | a :: ls' => 
      let ls'' := (getUnique ls' pf) in
        if (in_dec pf a ls'') 
          then ls''
          else a :: ls''
  end.

Theorem in_getUnique_if : forall (A : Set)(ls : list A)(eqd : eq_dec A) a,
  In a (getUnique ls eqd) ->
  In a ls.

  induction ls; simpl in *; intuition.

  destruct (in_dec _ a (getUnique ls _)).
  right.
  eapply IHls.
  eapply H.

  simpl in *.
  intuition.
  right.
  eapply IHls.
  eapply H0.

Qed.

Theorem in_getUnique : forall (A : Set)(ls : list A)(eqd : eq_dec A) a,
  In a ls ->
  In a (getUnique ls eqd).

  induction ls; simpl in *; intuition.

  subst.
  destruct (in_dec _ a0 (getUnique ls _)); simpl; auto.

  destruct (in_dec _ a (getUnique ls _)); simpl.
  eapply IHls. trivial.
  right.
  eapply IHls.
  trivial.

Qed.

Lemma getUnique_NoDup : forall (A : Set)(ls : list A)(eqd: eq_dec A),
  NoDup (getUnique ls eqd).

  induction ls; intuition; simpl in *.
  econstructor.

  destruct (in_dec _ a (getUnique ls _)); eauto.
  econstructor; eauto.
Qed.


Theorem length_getUnique_nz : forall (A :Set)(eqd : eq_dec A)(ls : list A),
  length ls > 0 ->
  length (getUnique ls eqd) > 0.
  
  induction ls; intuition; simpl in *.
  
  destruct (in_dec eqd a (getUnique ls eqd)).
  destruct ls; simpl in *; intuition.
  
  simpl.
  omega.
Qed.

Definition maxList(ls : list nat) : nat :=
  fold_left max ls O.

Lemma fold_left_max_ge_init : forall (ls : list nat)(n : nat),
  fold_left max ls n >= n.
  
  induction ls; intuition; simpl in *.
  eapply le_trans.
  eapply Max.max_lub_l.
  eapply le_refl.
  eapply IHls.
Qed.

Lemma maxList_correct_h : forall (ls : list nat)(n init : nat),
  In n ls ->
  fold_left max ls init >= n.
  
  induction ls; intuition.
  inversion H.
  
  simpl in *.
  intuition; subst.
  
  eapply le_trans.
  eapply Max.max_lub_r.
  eapply le_refl.
  eapply fold_left_max_ge_init.
Qed.

Theorem maxList_correct : forall (ls : list nat) n,
  In n ls ->
  maxList ls >= n.

  intuition.
  eapply maxList_correct_h.
  trivial.
Qed.

(* relational folds and other llist operations *)
Inductive pred_count(A : Type)(p : A -> Prop) : list A -> nat -> Prop :=
  | pc_nil : 
    pred_count p nil 0
  | pc_yes : 
    forall ls n a,
    pred_count p ls n ->
    p a ->
    pred_count p (a :: ls) (S n)
  | pc_no : forall ls n a,
    pred_count p ls n ->
    ~p a ->
    pred_count p (a :: ls) n.

Lemma pred_count_le_length : forall (A : Type)(P : A -> Prop) ls c,
  pred_count P ls c ->
  (c <= length ls)%nat.
  
  induction ls; intuition; simpl in *.
  inversion H; subst.
  trivial.
  
  inversion H; clear H; subst.
  eapply le_n_S.
  eapply IHls.
  trivial.
  econstructor.
  eapply IHls.
  trivial.
Qed.

(* listRepeat is used to show some interesting properties of rel_map and pred_count. *)
Fixpoint listRepeat(A : Type)(a : A) n :=
  match n with
    | 0 => nil
    | S n' => a :: (listRepeat a n')
  end.

Lemma listRepeat_length : forall n (A : Type) (a : A),
  length (listRepeat a n) = n.
  
  induction n; intuition; simpl in *.
  f_equal.
  eauto.
Qed.

Lemma pred_count_listRepeat_eq_inv : forall n (A : Type)(a : A) count,
  pred_count (eq a) (listRepeat a n) count ->
  count = n.
  
  induction n; intuition; simpl in *.
  
  inversion H. trivial.
  
  inversion H; clear H; subst.
  f_equal.
  eapply IHn; eauto.
  congruence.
Qed.

Lemma pred_count_listRepeat_ne_inv : forall n (A : Type)(a1 a2 : A) count,
  a1 <> a2 ->
  pred_count (eq a1) (listRepeat a2 n) count ->
  count = O.
  
  induction n; intuition; simpl in *.
  
  inversion H0. trivial.
  
  inversion H0; clear H0; subst.
  intuition.
  
  eapply IHn; eauto.
Qed.

Lemma pred_count_func : forall (A : Type)(P : A -> Prop)(ls : list A) n1 n2,
  pred_count P ls n1 ->
  pred_count P ls n2 ->
  n1 = n2.
  
  induction ls; intuition.
  
  inversion H. inversion H0. trivial.
  
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  f_equal.
  eapply IHls; eauto.
  intuition.
  
  inversion H0; clear H0; subst.
  intuition.
  eapply IHls; eauto.
Qed.

Lemma pred_count_eq_all_inv : forall (A : Type)(ls : list A)(P : A -> Prop) c,
  pred_count P ls c ->
  (forall a, In a ls -> P a) ->
  c = length ls.
  
  induction 1; intuition; simpl in *.
  
  f_equal.
  eauto.
  
  specialize (H1 a).
  intuition.
Qed.

Lemma pred_count_first_skip : forall (A : Type)(P : A -> Prop)(ls : list A)(c : nat),
  pred_count P ls c ->
  forall n,
    exists c1 c2,
      pred_count P (firstn n ls) c1 /\
      pred_count P (skipn n ls) c2 /\
      (c1 + c2 = c)%nat.
  
  induction 1; intuition; simpl in *.
  exists O. exists O.
  intuition;
    destruct n; simpl; econstructor.
  
  destruct n0; simpl.
  destruct (IHpred_count O).
  destruct H1.
  intuition. subst.
  exists x.
  exists (S x0).
  intuition.
  econstructor; trivial.
  
  destruct (IHpred_count n0).
  destruct H1.
  destruct H1.
  intuition. subst.
  exists (S x).
  exists x0.
  intuition.
  econstructor; trivial.
  
  destruct n0; simpl.
  destruct (IHpred_count O).
  destruct H1.
  intuition. subst.
  exists x.
  exists x0.
  intuition.
  econstructor; trivial.
  
  destruct (IHpred_count n0).
  destruct H1.
  destruct H1.
  intuition. subst.
  exists x.
  exists x0.
  intuition.
  econstructor; trivial.
  
Qed.

Lemma pred_count_eq_all : forall (A : Type)(P : A -> Prop)(ls : list A) n,
  (forall a, In a ls -> P a) ->
  n = length ls ->
  pred_count P ls n.
  
  induction ls; intuition; simpl in *; subst.
  econstructor.
  
  econstructor; eauto.
  
Qed.

Lemma pred_count_eq_none : forall (A : Type)(P : A -> Prop)(ls : list A),
  (forall a, In a ls -> ~P a) ->
  pred_count P ls 0.
  
  induction ls; intuition; simpl in *.
  econstructor.
  econstructor; eauto.
Qed.

Lemma in_listRepeat_inv : forall n (A : Type)(a1 a2 : A),
  In a1 (listRepeat a2 n) ->
  a1 = a2.
  
  induction n; intuition; simpl in *.
  intuition.
  intuition.
  
Qed.

Lemma pred_count_app : forall (A : Type)(P : A -> Prop)(ls1 ls2 : list A) n1 n2,
  pred_count P ls1 n1 ->
  pred_count P ls2 n2 ->
  pred_count P (ls1 ++ ls2) (n1 + n2).
  
  induction ls1; intuition; simpl in *.
  inversion H; subst; clear H.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  simpl.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma pred_count_permutation : forall (A : Set)(P : A -> Prop)(ls1 ls2 : list A),
  Permutation ls1 ls2 ->
  forall c, 
    pred_count P ls1 c ->
    pred_count P ls2 c.
  
  induction 1; intuition.
  inversion H0; clear H0; subst.
  econstructor; eauto.
  econstructor; eauto.
  
  inversion H; clear H; subst.
  inversion H2; clear H2; subst.
  econstructor; eauto.
  econstructor; eauto.
  eapply pc_no; eauto.
  econstructor; eauto.
  
  inversion H2; clear H2; subst.
  econstructor; eauto.
  econstructor; eauto.
  
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma pred_count_eq_none_inv : forall (A : Set)(P : A -> Prop)(ls : list A) c,
  pred_count P ls c ->
  (forall a, In a ls -> ~P a) ->
  c = O.
  
  induction 1; intuition; simpl in *.
  exfalso.
  eapply H1.
  eauto.
  trivial.
  
  eapply IHpred_count.
  intuition.
  eapply H1; eauto.
Qed.

Lemma pred_count_eq_1_inv : forall (A : Set)(eqd : eq_dec A)(P : A -> Prop)(ls : list A) c a,
  pred_count P ls c ->
  NoDup ls ->
  P a ->
  In a ls ->
  (forall a', In a' ls -> a <> a' -> ~P a') ->
  c = (S O).
  
  intuition.
  
  assert (pred_count P (a :: (removeFirst eqd ls a)) c).
  eapply pred_count_permutation.
  eapply removeFirst_permutation.
  trivial.
  trivial.
  inversion H4; clear H4; subst.
  assert (n = 0)%nat.
  eapply pred_count_eq_none_inv.
  eauto.
  intuition.
  eapply H3.
  eapply removeFirst_in_iff.
  eauto.
  assert (~In a (removeFirst eqd ls a)).
  eapply removeFirst_NoDup_not_in.
  trivial.
  intuition; subst; intuition.
  trivial.
  omega.
  
  intuition.
Qed.

Lemma pred_count_left_total : forall (A : Type)(P : A -> Prop)(ls : list A),
  (forall a, P a \/ ~P a) ->
  exists c, pred_count P ls c.
  
  induction ls; intuition.
  exists O.
  econstructor.
  
  destruct H0.
  destruct (H a).
  exists (S x).
  econstructor; eauto.
  exists x.
  econstructor; eauto.
Qed.

Inductive rel_map(A B : Type)(r : A -> B -> Prop) : list A -> list B -> Prop :=
| rm_nil : 
  rel_map r nil nil
| rm_step : 
  forall lsa lsb a b,
    rel_map r lsa lsb ->
    r a b ->
    rel_map r (a :: lsa) (b :: lsb).

Theorem rel_map_map2 : forall (A B C D : Type)(ls_c : list C)(ls_d: list D)(P : A -> B -> Prop)(f1 : C -> A)(f2 : D -> B),
  rel_map (fun a b => P (f1 a) (f2 b)) ls_c ls_d ->
  rel_map P (map f1 ls_c) (map f2 ls_d).

  induction ls_c; intuition.
  inversion H; subst.
  simpl.
  econstructor.

  inversion H; clear H; subst.
  simpl.
  econstructor; eauto.
Qed.

Lemma rel_map_length : forall (A B : Type)(lsa : list A)(P : A -> B -> Prop)(lsb : list B),
  rel_map P lsa lsb ->
  length lsa = length lsb.
  
  induction 1; intuition; simpl in *.
  f_equal.
  eauto.
  
Qed.

Lemma rel_map_unary_pred : forall (A B : Type)(P : A -> B -> Prop)(lsa : list A)(lsb : list B)(P' : B -> Prop),
  rel_map P lsa lsb ->
  (forall a b, P a b -> P' b) ->
  forall b, In b lsb -> P' b.
  
  induction 1; intuition; simpl in *.
  intuition.
  
  intuition; subst.
  eauto.

Qed.

Lemma rel_map_eq_inv : forall (A B : Type)(ls1 ls2 : list A)(rel1 rel2 : A -> B -> Prop) ls1' ls2',
  ls1 = ls2 ->
  (forall a b1 b2, rel1 a b1 -> rel2 a b2 -> b1 = b2) ->
  rel_map rel1 ls1 ls1' ->
  rel_map rel2 ls2 ls2' ->
  ls1' = ls2'.
  
  induction ls1; intuition; subst.
  
  inversion H1; clear H1; subst.
  
  inversion H2; clear H2; subst.
  trivial.
  
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  f_equal.
  eapply H0; eauto.
  eapply IHls1; eauto.
  
Qed.

Lemma rel_map_eq : forall (A B : Type)(ls1 : list A)(rel1 : A -> B -> Prop) ls',
  rel_map rel1 ls1 ls' ->
  forall ls2 (rel2 : A -> B -> Prop), 
    ls1 = ls2 ->
    (forall a b, In a ls1 -> In b ls' -> rel1 a b -> rel2 a b) ->
    rel_map rel2 ls2 ls'.
  
  induction 1; intuition; subst.
  econstructor.
  
  econstructor.
  eapply IHrel_map; eauto.
  intuition.
  eapply H2.
  simpl.
  intuition.
  simpl.
  intuition.
  trivial.     
Qed.

Theorem pred_count_eq_0 : forall (A B : Set)(ls : list B)(ls' : list A)(f : B -> A -> Prop)(P : A -> Prop) v,
  (forall a b, In b ls -> f b a -> ~ P a) ->
  rel_map f ls ls' ->
  pred_count P ls' v ->
  v = O.
  
  induction ls; intuition.
  inversion H0; subst; clear H0.
  inversion H1. trivial.
  
  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  exfalso.
  eapply H; eauto. simpl. intuition.
  
  eapply IHls; eauto.
  intuition.
  eapply H; eauto. simpl. intuition.
Qed.

Lemma rel_map_app_inv : forall (A B : Type)(rel : A -> B -> Prop)(lsa1 lsa2 : list A)(lsb : list B),
  rel_map rel (lsa1 ++ lsa2) lsb ->
  (rel_map rel lsa1 (firstn (length lsa1) lsb) /\ rel_map rel lsa2 (skipn (length lsa1) lsb)).
  
  induction lsa1; intuition; simpl in *.
  econstructor.
  
  inversion H; clear H; subst.
  econstructor.
  eapply IHlsa1; eauto.
  trivial.
  
  inversion H; clear H; subst.
  eapply IHlsa1; eauto.
Qed.

Lemma rel_map_map_inv : forall (A B C : Type)(rel : B -> C -> Prop)(f : A -> B)(lsa : list A)(lsc : list C),
  rel_map rel (map f lsa) lsc ->
  rel_map (fun a c => rel (f a) c) lsa lsc.
  
  induction lsa; intuition; simpl in *.
  inversion H; subst; clear H.
  econstructor.
  
  inversion H; clear H; subst.
  econstructor.
  eapply IHlsa; eauto.
  trivial.
Qed.

Lemma rel_map_listRepeat : forall (A B : Set)(lsa : list A)(rel : A -> B -> Prop) b,
  (forall a, In a lsa -> rel a b) ->
  rel_map rel lsa (listRepeat b (length lsa)).
  
  induction lsa; intuition; simpl in *.
  econstructor.
  
  econstructor; eauto.
    
Qed.

Lemma rel_map_app : forall (A B : Type)(rel : A -> B -> Prop)(lsa1 lsa2 : list A)(lsb1 lsb2 : list B),
  rel_map rel lsa1 lsb1 ->
  rel_map rel lsa2 lsb2 ->
  rel_map rel (lsa1 ++ lsa2) (lsb1 ++ lsb2).
  
  induction lsa1; intuition; simpl in *.
  inversion H; clear H; subst.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  rewrite <- app_comm_cons.
  econstructor; eauto.

Qed.

Lemma rel_map_map : forall (A B C : Type)(f : A -> B)(rel : B -> C -> Prop) lsa lsc,
  rel_map (fun a c => rel (f a) c) lsa lsc ->
  rel_map rel (map f lsa) lsc.
  
  induction lsa; intuition; simpl in *.
  inversion H.
  econstructor.
  
  inversion H; clear H; subst.
  econstructor; eauto.
Qed.

Lemma rel_map_inverse : forall (A B : Type)(lsa : list A)(lsb : list B) rel,
  rel_map rel lsa lsb -> 
  forall b, 
    In b lsb ->
    exists a, In a lsa /\ rel a b.
  
  induction 1; intuition; simpl in *.
  intuition.
  
  intuition;
    subst.
  
  econstructor; eauto.
  
  destruct (IHrel_map b0).
  trivial.
  intuition.
  econstructor; eauto.
  
Qed.

Lemma ne_all_not_in : forall (A : Type)(ls : list A) a,
  (forall a', In a' ls -> a <> a') ->
  ~In a ls.
  
  induction ls; intuition; simpl in *.
  intuition; subst.
  eapply H; eauto.
  
  eapply IHls; eauto.
  
Qed.

Lemma rel_map_NoDup : forall (A B : Type)(lsa : list A)(lsb : list B) rel,
  rel_map rel lsa lsb ->
  NoDup lsa ->
  (forall a1 a2 b1 b2, In a1 lsa -> In a2 lsa -> a1 <> a2 -> rel a1 b1 -> rel a2 b2 -> b1 <> b2) ->
  NoDup lsb.
  
  induction 1; intuition; simpl in *.
  econstructor.
  
  inversion H1; clear H1; subst.
  econstructor.
  
  eapply ne_all_not_in.
  intuition.
  subst.
  
  destruct (rel_map_inverse H a').
  trivial.
  intuition.
  
  eapply H2.
  left; eauto.
  right; eauto.
  intuition; subst; intuition.
  eauto.
  eauto.
  trivial.
  
  eapply IHrel_map; intuition.
  subst.
  eapply H2.
  right.
  eapply H3.
  right.
  eapply H4.
  trivial.
  eauto.
  eauto.
  trivial.
Qed.

Lemma rel_map_in : forall (A B : Type)(lsa : list A)(lsb : list B) rel,
  rel_map rel lsa lsb ->
  (forall a b1 b2, In a lsa -> rel a b1 -> rel a b2 -> b1 = b2) ->
  forall b a,
    In a lsa ->
    rel a b ->
    In b lsb.
  
  induction 1; intuition; simpl in *.
  
  intuition; subst.
  left; eauto.
  right; eauto.
  
Qed.

Lemma rel_map_left_total : forall (A B : Type)(rel : A -> B -> Prop)(lsa : list A),
  (forall a, exists b, rel a b) ->
  exists lsb, rel_map rel lsa lsb.
  
  induction lsa; intuition.
  exists nil.
  econstructor.
  
  destruct H0.
  destruct (H a).
  exists (x0 :: x).
  econstructor; eauto.
  
Qed.

Lemma rel_map_func : forall (A B : Type) (rel : A -> B -> Prop) lsa lsb1,
  rel_map rel lsa lsb1 ->
  forall lsb2,
    rel_map rel lsa lsb2 ->
    (forall a b1 b2, In a lsa -> rel a b1 -> rel a b2 -> b1 = b2) ->
    lsb1 = lsb2.
  
  induction 1; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.

  inversion H1; clear H1; subst.
  f_equal.
  eauto.
  eauto.
Qed.

Lemma rel_map_permutation : forall (A B : Type) lsa1 lsa2,
  Permutation lsa1 lsa2 ->
  forall (rel : A -> B -> Prop),
    (forall a b1 b2, rel a b1 -> rel a b2 -> b1 = b2) ->
    (forall a, exists b, rel a b) ->
    forall lsb1 lsb2,
      rel_map rel lsa1 lsb1 ->
      rel_map rel lsa2 lsb2 ->     
      Permutation lsb1 lsb2.
  
  induction 1; intuition; simpl in *.
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  econstructor.
  
  inversion H2; clear H2; subst.
  inversion H3; clear H3; subst.
  assert (b = b0).
  eapply H0; eauto.
  subst.
  eapply perm_skip.
  eauto.
  
  inversion H1; clear H1; subst.
  inversion H5; clear H5; subst.
  inversion H2; clear H2; subst.
  inversion H5; clear H5; subst.
  
  assert (b0 = b1); eauto; subst.
  assert (b = b2); eauto; subst.
  eapply perm_trans.
  eapply perm_swap.
  eapply perm_skip.
  eapply perm_skip.
  eauto.
  assert (lsb0 = lsb1).
  eapply rel_map_func; eauto.
  subst.
  eapply Permutation_refl.
  
  edestruct rel_map_left_total; eauto.
  eapply perm_trans.
  
  eapply IHPermutation1; eauto.
  eapply IHPermutation2; eauto.
Qed.

Lemma rel_map_impl : forall (A B : Type)(rel1 rel2 : A -> B -> Prop) lsa lsb,
  rel_map rel1 lsa lsb ->
  (forall a b, In a lsa -> rel1 a b -> rel2 a b) ->
  rel_map rel2 lsa lsb.
  
  induction lsa; intuition.
  inversion H; clear H; subst.
  econstructor.
  
  inversion H; clear H; subst.
  econstructor.
  eapply IHlsa; eauto.
  intuition.
  eapply H0.
  simpl.
  intuition.
  trivial.
Qed.

Lemma rel_map_in_inv : forall (A B : Type)(rel : A -> B -> Prop) lsa lsb,
  rel_map rel lsa lsb ->
  forall a, In a lsa -> exists b, In b lsb /\ rel a b.

  induction 1; intuition; simpl in *.
  intuition.

  intuition; subst.
  econstructor; eauto.
  edestruct IHrel_map; eauto.
  intuition.
  econstructor; eauto.

Qed.


(* a relational version of sumList *)
Inductive sumList_rel(A : Type)(rel : A -> Rat -> Prop) : list A -> Rat -> Prop :=
| slr_nil :
  forall r, 
    r == rat0 ->
    sumList_rel rel nil r
| slr_cons : 
  forall (ls : list A)(a : A) r1 r2 r3,
    sumList_rel rel ls r1 ->
    rel a r2 ->
    r3 == r2 + r1 ->
    sumList_rel rel (a :: ls) r3.

Lemma sumList_rel_distance : forall (A : Set)(ls : list A)(f1 f2 : A -> Rat -> Prop) r r1 r2,
  (forall a r1 r2, In a ls -> f1 a r1 -> f2 a r2 -> (ratDistance r1 r2) <= r) ->
  sumList_rel f1 ls r1 ->
  sumList_rel f2 ls r2 ->
  ratDistance r1 r2 <= (r * (length ls / 1)).
  
  induction ls; intuition; simpl in *.
  
  inversion H0. inversion H1. subst.
  rewrite H2.
  rewrite H3.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply (ratIdentityIndiscernables 0).
  intuition.
  eapply rat0_le_all.
  
  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  
  rewrite ratS_num.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply eqRat_symm.
    eapply ratMult_distrib.
  }
  rewrite H7.
  rewrite H9.
  rewrite rat_distance_of_sum.
  eapply ratAdd_leRat_compat.
  rewrite <- ratMult_1_r.
  eapply ratMult_leRat_compat.
  eapply H; eauto.
  intuition.
  
  eapply IHls; eauto.
Qed.

Lemma sumList_rel_all_0_inv : forall (A : Set)(ls : list A)(r  : Rat)(rel : A -> Rat -> Prop),
  sumList_rel rel ls r ->
  (forall a' v, In a' ls -> rel a' v -> v == 0) ->
  r == 0.
  
  induction ls; intuition; simpl in *.
  
  inversion H.
  intuition.
  
  inversion H; clear H; subst.
  rewrite H6.
  rewrite (H0 a r2); eauto.
  rewrite <- ratAdd_0_l.
  eapply IHls; eauto.
    
Qed.

Lemma sumList_rel_only_one_inv : forall (A : Set)(rel : A -> Rat -> Prop)(ls : list A)(a : A) r r',
  sumList_rel rel ls r' ->
  In a ls ->
  NoDup ls -> 
  (forall a', In a' ls -> a <> a' -> forall v, rel a' v -> v == 0) ->
  (forall v, rel a v -> v == r) ->
  r' == r.
  
  induction ls; intuition; simpl in *.
  intuition.
  
  inversion H1; clear H1; subst.
  inversion H; clear H; subst.
  intuition; subst.
  rewrite H10.
  rewrite (H3 r2); eauto.
  rewrite (sumList_rel_all_0_inv H5).
  rewrite <- ratAdd_0_r.
  intuition.
  intuition.
  eapply H2.
  right.
  eauto.
  intuition; subst.
  eauto.
  trivial.
  
  eapply eqRat_trans.
  rewrite H10.
  eapply ratAdd_eqRat_compat.
  eapply H2.
  left.
  eauto.
  intuition; subst; intuition.
  trivial.
  eauto.
  rewrite <- ratAdd_0_l.
  intuition.       
  
Qed.

Lemma sumList_rel_body_eq : forall (A : Type)(rel1 rel2 : A -> Rat -> Prop)(ls1 : list A) r1,
  sumList_rel rel1 ls1 r1 ->
  forall ls2 r2, 
    (forall a r', rel1 a r' -> rel2 a r') ->
    r1 == r2 ->
    ls1 = ls2 ->
    sumList_rel rel2 ls2 r2.
  
  induction 1; intuition; subst.
  econstructor.
  rewrite <- H1.
  trivial.
  
  econstructor.
  eapply IHsumList_rel.
  intuition.
  eapply eqRat_refl.
  trivial.
  eauto.
  rewrite <- H3.
  trivial.
Qed.

Lemma sumList_rel_plus_inv : forall (A : Type)(ls : list A) r (rel1 rel2 rel : A -> Rat -> Prop),
  sumList_rel rel ls r ->
  (forall a r, In a ls -> rel a r -> forall r1 r2, rel1 a r1 -> rel2 a r2 -> r == r1 + r2) ->
  forall r1 r2, sumList_rel rel1 ls r1 -> sumList_rel rel2 ls r2 -> r == r1 + r2.
  
  induction ls; intuition; simpl in *.
  
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  inversion H; clear H; subst.
  rewrite H3.
  rewrite H1.
  rewrite H2.
  rewrite <- ratAdd_0_l.
  intuition.
  
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  inversion H; clear H; subst.
  assert (r7 == r3 + r5).
  eauto.
  assert (r6 == r0 + r4).
  eauto.
  rewrite H12.
  rewrite H8.
  rewrite H10.
  rewrite H.
  rewrite H1.
  repeat rewrite <- ratAdd_assoc.
  eapply ratAdd_eqRat_compat; intuition.
  rewrite ratAdd_assoc.
  rewrite (ratAdd_comm r5).
  rewrite <- ratAdd_assoc.
  intuition.
Qed.

Lemma sumList_rel_left_total : forall (A : Type)(rel : A -> Rat -> Prop)(ls : list A),
  (forall a, In a ls -> exists r, rel a r) ->
  exists r, sumList_rel rel ls r.
  
  induction ls; intuition; simpl in *.
  exists 0.
  econstructor.
  intuition.
  
  edestruct H.
  left.
  eauto.
  edestruct IHls.
  intuition.
  econstructor.
  econstructor.
  eauto.
  eauto.
  eapply eqRat_refl.
Qed.

Lemma sumList_rel_factor_constant : forall (p1 p2 : posnat) (A : Type)(rel : A -> Rat -> Prop)(ls : list A) r,
  sumList_rel (fun a r' => rel a (r' * (RatIntro p1 p2))) ls (r * (RatIntro p2 p1)) ->
  sumList_rel rel ls r.
  
  induction ls; intuition.
  inversion H; subst; clear H.
  apply ratMult_0 in H0.
  destruct H0.
  econstructor; trivial.
  
  exfalso.
  eapply rat_num_nz; [idtac | eapply H].
  eapply posnat_pos.
  
  inversion H; clear H; subst.
  symmetry in H5.
  apply ratMult_inverse in H5.
  rewrite ratMult_distrib_r in H5.
  symmetry in H5.
  econstructor; eauto.
  eapply IHls.
  eapply sumList_rel_body_eq.
  eapply H2.
  intuition.
  
  rewrite ratMult_assoc.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- ratMult_num_den.
  symmetry.
  eapply num_dem_same_rat1.
  unfold posnatMult, natToPosnat, posnatToNat.
  destruct p1.
  destruct p2.
  apply mult_comm.
  trivial.
Qed.

Lemma sumList_rel_permutation : forall (A : Type)(rel : A -> Rat -> Prop)(ls1 ls2 : list A),
  Permutation ls1 ls2 ->
  forall r, 
    sumList_rel rel ls1 r ->
    sumList_rel rel ls2 r.
  
  induction 1; intuition; simpl in *.
  inversion H0; clear H0; subst.
  econstructor; eauto.
  
  inversion H; clear H; subst.
  inversion H2; clear H2; subst.
  econstructor; eauto.
  econstructor; eauto.
  eapply eqRat_refl.
  rewrite H5.
  rewrite H7.
  repeat rewrite <- ratAdd_assoc.
  eapply ratAdd_eqRat_compat; intuition.
  eapply ratAdd_comm.
Qed.    

Lemma sumList_rel_all_0 : forall (A : Type)(rel : A -> Rat -> Prop)(ls : list A),
  (forall a, In a ls -> rel a 0) ->
  sumList_rel rel ls 0.
  
  induction ls; intuition; simpl in *.
  econstructor.
  intuition.
  
  econstructor.
  eapply IHls.
  intuition.
  eauto.
  rewrite <- ratAdd_0_l.
  intuition.
Qed.

Lemma sumList_rel_ls_intersect: forall (A : Set)(rel : A -> Rat -> Prop)(ls1 : list A) r,
  sumList_rel rel ls1 r ->
  forall ls2, 
    NoDup ls1 ->
    NoDup ls2 ->
    eq_dec A ->
    (forall a r1 r2, In a ls1 -> rel a r1 -> rel a r2 -> r1 == r2) -> 
    (forall a, In a ls1 -> ~In a ls2 -> rel a 0) ->
    (forall a, In a ls2 -> ~In a ls1 -> rel a 0) ->
    sumList_rel rel ls2 r.

  induction 1; intuition; simpl in *.
  eapply sumList_rel_body_eq.
  eapply sumList_rel_all_0.
  intuition.
  eapply H5.
  eauto.
  simpl.
  intuition.
  intuition.
  intuition.
  trivial.
  
  inversion H2; clear H2; subst.
  symmetry in H1.
  eapply sumList_rel_body_eq; intuition; eauto.
  clear H1.
  clear r3.

  destruct (in_dec H4 a ls2).
  
  eapply sumList_rel_permutation.
  eapply Permutation_sym.
  eapply removeFirst_permutation.
  eauto.
  econstructor.
  eapply IHsumList_rel; intuition.
  eapply removeFirst_NoDup.
  trivial.
  eapply H5.
  right.
  eapply H1.
  trivial.
  trivial.
  eapply H6.
  intuition.
  intuition.
  eapply H2.
  eapply removeFirst_in.
  trivial.
  intuition.
  subst.
  intuition.

  destruct (H4 a a0); subst.
  eapply H6.
  intuition.
  intuition.
  eapply removeFirst_NoDup_not_in.
  eapply H3.
  eauto.

  eapply H7.
  eapply removeFirst_in_iff.
  eauto.
  simpl. intuition.
  eauto.
  intuition.

  assert (rel a 0).
  eapply H6.
  intuition.
  intuition.

  assert (r2 == 0).
  eapply H5.
  eauto.
  trivial.
  trivial.

  eapply sumList_rel_body_eq.
  3:{
    rewrite H2.
    rewrite <- ratAdd_0_l.
    eapply eqRat_refl.
  }
  2:{
    intuition.
    eauto.
  }
  2:{
    eauto.
  }
  eapply IHsumList_rel; intuition.
  eapply H5.
  right.
  eauto.
  trivial.
  trivial.
  eapply H7.
  trivial.
  intuition.
  subst.
  intuition.
  
  Grab Existential Variables.
  trivial.

Qed.

Lemma sumList_rel_sumList : forall (A : Set)(ls : list A)(f : A -> Rat),
  sumList_rel (fun a r => f a = r) ls
  (sumList ls f).
  
  induction ls; intuition.
  unfold sumList.
  simpl.
  econstructor.
  intuition.
  
  unfold sumList in *. simpl in *.
  econstructor.
  eapply IHls.
  eauto.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  eapply eqRat_refl.
  intuition.
Qed.


Lemma sumList_cons : forall (A : Set)(ls : list A) a f,
  sumList (a :: ls) f == f a + (sumList ls f).
  
  intuition.
  unfold sumList. simpl.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  eapply eqRat_refl.
  intuition.
Qed.

Lemma sumList_sum : forall (A : Set)(ls : list A)(f1 f2 : A -> Rat),
  sumList ls (fun a => f1 a + f2 a) ==
  sumList ls f1 + sumList ls f2.
  
  induction ls; intuition; unfold sumList in *; simpl in *.
  rewrite <- ratAdd_0_l.
  intuition.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  rewrite (IHls f1 f2).
  eapply eqRat_trans.
  2:{
    symmetry.
    eapply ratAdd_eqRat_compat.
    rewrite fold_add_body_eq.
    2:{
      eapply ratAdd_comm.
    }
    eapply fold_add_init.
    intuition.
    eapply eqRat_refl.
    rewrite fold_add_body_eq.
    2:{
      eapply ratAdd_comm.
    }
    eapply fold_add_init.
    intuition.
    eapply eqRat_refl.
  }
  repeat rewrite <- ratAdd_assoc.
  eapply ratAdd_eqRat_compat.
  repeat rewrite ratAdd_assoc.
  eapply ratAdd_eqRat_compat; intuition.
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat; intuition.
  eapply fold_add_body_eq; intuition.
  intuition.
Qed.

Lemma sumList_summation : forall (A B : Set) f (lsa : list A)(lsb : list B),
  sumList lsa (fun a => sumList lsb (fun b => (f a b))) ==
  sumList lsb (fun b => sumList lsa (fun a => (f a b))).
  
  induction lsa; destruct lsb; intuition.
  unfold sumList in *; simpl in *; intuition.
  assert (sumList (b :: lsb) (fun b : B => sumList nil (fun a : A => f a b)) == 0).
  eapply sumList_0.
  intuition.
  unfold sumList. simpl.
  intuition.
  rewrite H.
  unfold sumList in *; simpl in *; intuition.
  assert (sumList (a :: lsa) (fun a0 : A => sumList nil (fun b : B => f a0 b)) == 0).
  eapply sumList_0.
  intuition.
  unfold sumList in *; simpl in *; intuition.
  rewrite H.
  unfold sumList in *; simpl in *; intuition.
  
  rewrite sumList_body_eq.
  2:{
    intuition.
    eapply sumList_cons. 
  }
  rewrite sumList_sum.
  rewrite (sumList_cons lsa a (fun a0 : A => sumList lsb (f a0))).
  rewrite IHlsa.
  symmetry.
  rewrite sumList_body_eq.
  2:{
    intuition.
    eapply sumList_cons.
  }
  rewrite sumList_sum.
  repeat rewrite sumList_cons.
  repeat rewrite <- ratAdd_assoc.
  eapply ratAdd_eqRat_compat; intuition.
  repeat rewrite ratAdd_assoc.
  eapply ratAdd_eqRat_compat; intuition.
  eapply ratAdd_comm.
  
Qed.

Lemma fold_add_subset' : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A)(f : A -> Rat) init1 init2,
  init1 == init2 ->
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> In a ls2) ->
  (forall a, In a ls2 -> (~In a ls1) -> (f a) == 0) ->
  fold_left (fun r a => r + (f a)) ls1 init1 == fold_left (fun r a => r + (f a)) ls2 init2.
  
  intuition.
  
  erewrite <- matchOrder_firstn at 1.
  
  eapply eqRat_symm.
  eapply eqRat_trans.
  eapply fold_add_rat_perm.
  eapply matchOrder_permutation.
  eapply H0.
  eauto.
  intuition.
  eapply eqRat_refl.
  intuition.
  eapply eqRat_refl.
  
  eapply eqRat_symm.
  eapply fold_add_matchOrder; intuition.
  eapply permutation_NoDup.
  eapply matchOrder_permutation; eauto.
  eauto.
  eapply H3.
  eapply matchOrder_In.
  eapply H0.
  trivial.
  intuition.
  eauto.
  intuition.
  eapply H5.
  rewrite matchOrder_firstn; trivial.
  trivial.
  trivial.
  trivial.
  
  Grab Existential Variables.
  trivial.
Qed.

Lemma sumList_subset'
  : forall A : Set,
    eq_dec A ->
    forall (ls1 ls2 : list A) (f : A -> Rat),
      NoDup ls1 ->
      NoDup ls2 ->
      (forall a : A, In a ls1 -> In a ls2) ->
      (forall a : A, In a ls2 -> ~ In a ls1 -> f a == 0) ->
      sumList ls1 f == sumList ls2 f.
  
  intuition.
  eapply fold_add_subset'; eauto.
  intuition.
Qed.

Lemma sumList_exactly_one : forall (A : Set) a (ls : list A) f,
  NoDup ls ->
  In a ls ->
  (forall b, In b ls -> a <> b -> f b == 0) ->
  sumList ls f == f a.
  
  induction ls; intuition.
  inversion H0.
  
  simpl in *.
  inversion H; clear H; subst.
  intuition; subst.
  assert (sumList ls f == 0).
  eapply sumList_0.
  intuition.
  eapply H1.
  intuition.
  intuition; subst; intuition.
  unfold sumList in *; simpl.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  rewrite H.
  rewrite <- ratAdd_0_r.
  intuition.
  intuition.
  
  assert (sumList ls f == f a).
  eapply IHls; intuition.
  unfold sumList in *.
  simpl.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  rewrite H0.
  rewrite H1.
  rewrite <- ratAdd_0_l.
  intuition.
  intuition.
  intuition; subst; intuition.
  intuition.
  
Qed.

Lemma fold_add_permutation : forall (A : Set) ls1 ls2,
  Permutation ls1 ls2 ->
  forall (f : A -> Rat) init1 init2,
    init1 == init2 ->
    fold_left (fun r a => r + (f a)) ls1 init1 == fold_left (fun r a => r + (f a)) ls2 init2.
  induction 1; intuition; simpl in *.
  eapply IHPermutation.
  eapply ratAdd_eqRat_compat; intuition.
  rewrite fold_add_body_eq.
  eapply eqRat_refl.
  rewrite ratAdd_assoc.
  rewrite (ratAdd_comm (f y)).
  rewrite <- ratAdd_assoc.
  intuition.
  eapply ratAdd_eqRat_compat; intuition.
  eapply ratAdd_eqRat_compat; intuition.
  intuition.
  
  eapply eqRat_trans.
  eapply IHPermutation1.
  eapply H1.
  eapply IHPermutation2.
  intuition.
Qed.

Lemma sumList_permutation : forall (A : Set)(f : A -> Rat) ls1 ls2,
  Permutation ls1 ls2 ->
  sumList ls1 f == sumList ls2 f.
  
  intuition.
  eapply fold_add_permutation; intuition.
  
Qed.

Lemma sumList_rel_body_eq_strong : forall (A : Type)(rel1 rel2 : A -> Rat -> Prop)(ls1 : list A) r1,
  sumList_rel rel1 ls1 r1 ->
  forall ls2 r2, 
    (forall a r', In a ls1 -> rel1 a r' -> rel2 a r') ->
    r1 == r2 ->
    ls1 = ls2 ->
    sumList_rel rel2 ls2 r2.
  
  induction 1; intuition; subst.
  econstructor.
  rewrite <- H1.
  trivial.
  
  econstructor.
  eapply IHsumList_rel.
  intuition.
  eapply eqRat_refl.
  trivial.
  eapply H2.
  simpl.
  intuition.
  eauto.
  rewrite <- H3.
  trivial.
Qed.

Lemma rel_map_left_total_strong' : forall (A B : Type)(lsa : list A)(P : A -> Prop)(rel : A -> B -> Prop),
  (forall a, P a -> exists b, rel a b) ->
  (forall a, In a lsa -> P a) ->
  exists lsb, rel_map rel lsa lsb.
  
  induction lsa; intuition.
  exists nil.
  econstructor.
  
  edestruct (IHlsa _ _ H).
  intuition.
  destruct (H a).
  eapply H0.
  simpl. intuition.
  exists (x0 :: x).
  econstructor; eauto.
  
Qed.


Lemma firstn_eq_all_gen : forall (A : Type)(ls : list A) n,
  n = length ls ->
  firstn n ls = ls.
  
  induction ls; intuition; subst; simpl in *.
  trivial.
  
  f_equal.
  eauto.
Qed.

Fixpoint getNats s n :=
  match n with 
    | O => nil
    | S n' => (s + n')%nat :: (getNats s n')
  end.

Lemma ratMult_sumList_rel_distrib : forall (A : Set)(ls : list A) f (x : Rat -> Prop) x' a,
  sumList_rel f ls a ->
  (forall i v1 v2, f i v1 -> f i v2 -> v1 == v2) ->
  (forall x1 x2, x x1 -> x x2 -> x1 == x2) ->
  x x' -> 
  sumList_rel (fun i => ratMult_rel x (f i)) ls (x' * a).

  induction ls; intuition.
  inversion H; clear H; subst.
  econstructor.
  rewrite H3.
  apply ratMult_0_r.

  inversion H; clear H; subst.
  econstructor.
  eauto.
  unfold ratMult_rel.
  intuition.
  eapply ratMult_eqRat_compat; eauto.
  
  rewrite H8.
  eapply ratMult_distrib.
Qed.


Lemma series_le : forall n (f1 f2 : nat -> Rat -> Prop) r1 r2,
  (forall i v1 v2, f1 i v1 -> f2 i v2 -> v2 <= v1) ->
  sumList_rel f1 (getNats O n) r1 ->
  sumList_rel f2 (getNats O n) r2 ->
  r2 <= r1.
  
  induction n; intuition; simpl in *.
  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  rewrite H0.
  eapply rat0_le_all.
  
  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  rewrite H9.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H7.
  }
  eapply ratAdd_leRat_compat.
  eauto.
  eauto.
  
Qed.

Lemma ratSubtract_series_map : forall n f1 f2 a1 a2,
  n > 0 ->
  sumList_rel f1 (getNats O n) a1 ->
  sumList_rel f2 (getNats O n) a2 ->
  (forall i x1 x2, f1 (S i) x1 -> f2 i x2 -> x1 == x2) ->
  (forall i v1 v2, f1 i v1 -> f1 i v2 -> v1 == v2) ->
  (forall i v1 v2, f2 i v1 -> f2 i v2 -> v1 == v2) ->
  (forall i v1 v2, f1 i v1 -> f2 i v2 -> v2 <= v1) ->  
  (forall i1 i2 v1 v2, (i1 <= i2)%nat -> f1 i1 v1 -> f1 i2 v2 -> v2 <= v1) ->
  (forall i1 i2 v1 v2, (i1 <= i2)%nat -> f2 i1 v1 -> f2 i2 v2 -> v2 <= v1) ->
  forall x1 x2,
    f1 O x1 -> f2 (pred n) x2 ->
    ratSubtract a1 a2 == ratSubtract x1 x2.

  induction n; intuition; simpl in *.
  omega.

  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.

  destruct n; simpl in *.
  inversion H11; clear H11; subst.
  inversion H12; clear H12; subst.

  eapply ratSubtract_eqRat_compat.
  rewrite H15.
  rewrite H1.
  rewrite <- ratAdd_0_r.
  eauto.

  rewrite H17.
  rewrite H0.
  rewrite <- ratAdd_0_r.
  eauto.
  
  rewrite H15.
  rewrite H17.
  inversion H11; clear H11; subst.
  inversion H12; clear H12; subst.

  assert (ratSubtract r1 r0 == ratSubtract x1 r5).
  eapply IHn.
  omega.
  econstructor.
  eapply H11.
  eapply H18.
  trivial.
  econstructor.
  eapply H10.
  eapply H16.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  
  assert (r3 <= r2).
  eauto.
  assert (r0 <= r1).
  rewrite H19.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H21.
  }
  eapply ratAdd_leRat_compat.
  eauto.

  eapply series_le.
  eauto.
  eauto.
  trivial.
  
  rewrite ratSubtract_ratAdd_distr.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_assoc.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_assoc.
  rewrite H0.
  assert (r2 == r5).
  eauto.
  rewrite H20.
  assert (x2 == r3).
  eauto.
  rewrite <- H22.

  assert (x2 <= r5).
  eauto.
  assert (r5 <= x1).
  eapply leRat_trans.
  eapply H5.
  eapply H18.
  trivial.
  eapply H6.
  2:{
    eauto.
  }
  2:{
    eauto.
  }
  omega.

  symmetry.
  eapply ratSubtract_partition.
  trivial.
  trivial.
  trivial.
  trivial.

Qed.

Lemma sum_power_series : forall n (f : Rat -> Prop) a a',
  n > 0 ->
  (exists v, f v) ->
  (forall v1 v2, f v1 -> f v2 -> v1 == v2) ->
  (forall v, f v -> ~1 <= v) ->
  sumList_rel (fun i : nat => expRat_rel f i) (getNats 0 n) a ->
  ratMult_rel (ratSubtract_rel (eqRat 1) (expRat_rel f n))
         (ratInverse_rel (ratSubtract_rel (eqRat 1) f)) a' ->
         a == a'.

  intuition.
  destruct H0.
  assert (sumList_rel (fun i => ratMult_rel f (expRat_rel f i)) (getNats O n) (x * a)).
  eapply ratMult_sumList_rel_distrib.
  eapply H3.
  unfold expRat_rel.
  intuition.
  rewrite H5; eauto.
  rewrite H6; eauto.
  intuition.
  trivial.
  trivial.

  assert (ratSubtract a (x * a) == ratSubtract 1 (expRat x n)).
  eapply ratSubtract_series_map; eauto.
  intuition.
  unfold expRat_rel, ratMult_rel in *.
  simpl in *.
  rewrite H6; eauto.
  rewrite H7; eauto.
  eapply eqRat_refl.
  intuition.
  eapply expRat_eqRat_compat; eauto.
  unfold expRat_rel.
  intuition.
  simpl.
  intuition.
  unfold ratMult_rel, expRat_rel; intuition.
  rewrite H7; eauto.
  destruct n; try omega.
  simpl.
  eauto using ratMult_eqRat_compat, expRat_eqRat_compat.

  unfold ratMult_rel, expRat_rel.
  intuition.
  rewrite H6; eauto.
  rewrite H7; eauto.
  eapply eqRat_refl.
  intuition.
  eapply expRat_eqRat_compat; eauto.
  intuition.
  eapply expRat_eqRat_compat; eauto.

  unfold ratMult_rel, expRat_rel.
  intuition.
  rewrite H6; eauto.
  rewrite H7; eauto.
  eapply eqRat_refl.
  intuition.
  eapply expRat_eqRat_compat; eauto.
  intuition.
  eapply expRat_eqRat_compat; eauto.

  intuition.
  unfold expRat_rel, ratMult_rel in *.
  rewrite H7.
  2:{
    eauto.
  }
  2:{
    intuition.
  }
  rewrite ratMult_comm.
  eapply ratMult_small_le.
  case_eq (bleRat x 1); intuition.
  exfalso.
  eapply H2.
  eauto.
  eapply bleRat_total.
  trivial.
  
  unfold expRat_rel; intuition.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply H8.
  eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H7.
    eauto.
  }
  eapply expRat_le.
  case_eq (bleRat x 1); intuition.
  exfalso.
  eapply H2.
  eauto.
  eapply bleRat_total; trivial.
  omega.

  unfold ratMult_rel, expRat_rel.
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply H8.
  eauto.
  intuition.
  eapply expRat_eqRat_compat.
  eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H7.
    eauto.
    intuition.
    eapply expRat_eqRat_compat.
    eauto.
  }
  eapply ratMult_leRat_compat.
  intuition.
  eapply expRat_le.
  case_eq (bleRat x 1); intuition.
  exfalso.
  eapply H2.
  eauto.
  eapply bleRat_total; trivial.
  omega.

  unfold expRat_rel; intuition.
  simpl.
  intuition.

  unfold ratMult_rel, ratSubtract_rel, expRat_rel, ratInverse_rel in *.
  intuition.
  rewrite H7; eauto.
  destruct n; try omega.
  simpl.
  eapply ratMult_eqRat_compat; eauto.
  eapply expRat_eqRat_compat; eauto.

  unfold ratMult_rel, ratSubtract_rel, expRat_rel, ratInverse_rel in H4.
  rewrite H4.
  2:{
    intuition.
    rewrite H8.
    rewrite <- H7.
    eapply eqRat_refl.
    eauto.
  }
  2:{
    intuition.
    eapply ratInverse_eqRat_compat.
    2:{
      rewrite H7.
      eapply eqRat_refl.
      eapply eqRat_refl.
      eauto.
    }
    intuition.
    eapply H2.
    eauto.
    apply ratSubtract_0_inv.
    trivial.
  }

  rewrite <- (ratMult_1_l a) in H6 at 1.

  eapply (@eqRat_ratMult_same_r (ratSubtract 1 x)).
  intuition.
  eapply H2; eauto.
  eapply ratSubtract_0_inv; trivial.

  rewrite ratMult_assoc.
  rewrite ratInverse_prod_1.
  rewrite ratMult_1_r.
  rewrite ratMult_comm.
  rewrite ratMult_ratSubtract_distrib_r.

  trivial.

  intuition.
  eapply H2.
  eauto.
  eapply ratSubtract_0_inv; trivial.

Qed.

Lemma sumList_rel_le : forall (A : Set)(ls : list A)(f1 f2 : A -> Rat -> Prop) r1 r2,
  sumList_rel f1 ls r1 ->
  sumList_rel f2 ls r2 ->
  (forall a v1 v2, In a ls -> f1 a v1 -> f2 a v2 -> v1 <= v2) ->
  r1 <= r2.
  
  induction ls; intuition.
  inversion H; clear H; subst.
  rewrite H2.
  eapply rat0_le_all.

  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  rewrite H7.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H9.
  }
  eapply ratAdd_leRat_compat.
  eapply H1.
  simpl.
  left.
  eauto.
  trivial.
  trivial.
  eapply IHls.
  eauto.
  eauto.
  intuition.
  eapply H1.
  simpl.
  right.
  eauto.
  trivial.
  trivial.
  
Qed.


Lemma sumList_filter_le : forall (A : Set)(ls : list A)(f : A -> Rat)(P : A -> bool),
  sumList (filter P ls) f <= sumList ls f.
  
  induction ls; intuition;
    unfold sumList in *; simpl in *.
  intuition.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    rewrite fold_add_body_eq.
    2:{
      eapply ratAdd_comm.
    }
    eapply fold_add_init.
    intuition.
    eapply eqRat_refl.
  }
  
  destruct (P a); simpl.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  2:{
    intuition.
    eapply eqRat_refl.
  }
  rewrite fold_add_init.
  eapply ratAdd_leRat_compat; intuition.
  
  rewrite ratAdd_0_l.
  eapply ratAdd_leRat_compat; intuition.
  eapply rat0_le_all.
  
Qed.

Lemma sumList_filter_partition : forall (A : Set)(P : A -> bool)(ls : list A)(f : A -> Rat),
  sumList ls f == (sumList (filter P ls) f + (sumList (filter (fun a => negb (P a)) ls) f)).
  
  induction ls; intuition; simpl in *.
  unfold sumList.
  simpl.
  eapply ratAdd_0_l.
  
  unfold sumList in *.
  simpl in *.
  
  erewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  2:{
    intuition.
    eapply eqRat_refl.
  }
  rewrite fold_add_init.
  
  destruct (P a);
    simpl.
  
  erewrite (fold_add_body_eq (filter P ls)).
  2:{
    eapply ratAdd_comm.
  }
  2:{
    intuition.
    eapply eqRat_refl.
  }
  rewrite fold_add_init.
  rewrite ratAdd_assoc.
  eapply ratAdd_eqRat_compat;
    intuition.
  
  erewrite (fold_add_body_eq (filter (fun a => negb (P a)) ls)).
  2:{
    eapply ratAdd_comm.
  }
  2:{
    intuition.
    eapply eqRat_refl.
  }
  rewrite fold_add_init.
  rewrite <- ratAdd_assoc.
  rewrite (ratAdd_comm (fold_left (fun (a0 : Rat) (b : A) => a0 + f b) (filter P ls) 0 )).
  rewrite ratAdd_assoc.
  eapply ratAdd_eqRat_compat;
    intuition.
  
Qed.



Lemma sumList_rel_sumList_eqRat : forall (A : Set)(ls : list A)(f : A -> Rat),
  sumList_rel (fun a r => f a == r) ls
  (sumList ls f).
  
  induction ls; intuition.
  unfold sumList.
  simpl.
  econstructor.
  intuition.
  
  unfold sumList in *. simpl in *.
  econstructor.
  eapply IHls.
  eapply eqRat_refl.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  eapply eqRat_refl.
  intuition.
Qed.

Lemma sumList_series_incr : forall n2 n1 (f f' : nat -> Rat),
  (forall n, (f n) == (f' (S n))) ->
  sumList (getNats n1 n2) f == sumList (getNats (S n1) n2) f'.
  
  induction n2; intuition; unfold sumList; simpl in *.
  intuition.
  rewrite fold_add_body_eq.
  2:{
    eapply ratAdd_comm.
  }
  rewrite fold_add_init.
  unfold sumList in *.
  rewrite IHn2; eauto.
  eapply eqRat_trans.
  2:{
    symmetry.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    eapply fold_add_init.
  }
  eapply ratAdd_eqRat_compat.
  eauto.
  intuition.
  intuition.
Qed.

Lemma sumList_series_split_first : forall n f, 
  sumList (n :: getNats O n) f == f O + (sumList (getNats 1 n) f).
  
  induction n; intuition; unfold sumList in *; simpl in *.
  eapply ratAdd_comm.
  rewrite fold_add_body_eq.
  2:{
    rewrite ratAdd_assoc.
    rewrite ratAdd_comm.
    rewrite ratAdd_assoc.
    rewrite (ratAdd_comm (f n ) 0).
    eapply eqRat_refl.
  }
  rewrite fold_add_init.
  rewrite IHn.
  rewrite ratAdd_comm.
  eapply eqRat_trans.
  2:{
    symmetry.
    eapply ratAdd_eqRat_compat.
    eapply eqRat_refl.
    eapply eqRat_trans.
    eapply fold_add_body_eq.
    eapply ratAdd_comm.
    intuition.
    eapply eqRat_refl.
    eapply fold_add_init.
  }
  rewrite (ratAdd_comm (f (S n))).
  rewrite <- ratAdd_assoc.
  intuition.
  intuition.
Qed.

Lemma firstn_nil : forall (A : Set) n, 
  firstn n nil = (@nil A).
  
  induction n; intuition; simpl in *.
Qed.

Lemma firstn_ge_all : forall n (A : Set) (ls : list A),
  n >= length ls ->
  firstn n ls = ls.

  induction n; intuition; simpl in *.
  destruct ls; simpl in *.
  trivial.
  omega.
  destruct ls.
  trivial.
  f_equal.
  eapply IHn.
  simpl in *.
  omega.
  
Qed.

Lemma firstn_app : forall n (A : Set) (ls1 ls2 : list A),
  (n <= length ls1)%nat ->
  firstn n (ls1 ++ ls2) = firstn n ls1.
  
  induction n; intuition; simpl in *.
  destruct ls1; simpl in *.
  omega.
  
  f_equal.
  eapply IHn.
  omega.
Qed.

Lemma sumList_rel_func : forall (A : Set)(f : A -> Rat -> Prop) ls r1,
  sumList_rel f ls r1 ->
  forall r2,
  sumList_rel f ls r2 ->
  (forall a v1 v2, f a v1 -> f a v2 -> v1 == v2) ->
  r1 == r2.

  induction 1; intuition.
  inversion H0; clear H0; subst.
  rewrite H.
  rewrite H2.
  intuition.

  inversion H2; clear H2; subst.
  rewrite H1.
  rewrite H9.
  eapply ratAdd_eqRat_compat;
  eauto.
Qed.

Lemma sumList_partition : forall (A : Set)(P : A -> bool)(ls : list A)(f : A -> Rat),
  sumList ls f ==
  sumList ls (fun a => (f a) * (if (P a) then 1 else 0)) + 
  sumList ls (fun a => (f a) * (if (P a) then 0 else 1)).
  
  induction ls; intuition.
  unfold sumList; simpl in *.
  eapply ratAdd_0_l.
  
  repeat rewrite sumList_cons.
  destruct (P a);
    rewrite ratMult_0_r;
      rewrite <- ratAdd_0_l;
        rewrite ratMult_1_r;
          rewrite IHls.
  
  rewrite ratAdd_assoc.
  intuition.
  
  rewrite (ratAdd_comm (sumList ls (fun a0 : A => f a0 * (if P a0 then 1 else 0)))).
  rewrite <- ratAdd_assoc.
  rewrite <- ratAdd_comm.
  intuition.
Qed.

Lemma sumList_le : forall (A : Set)(ls : list A)(f1 f2 : A -> Rat),
  (forall a, In a ls -> f1 a <= f2 a) ->
  sumList ls f1 <= sumList ls f2.
  
  induction ls; intuition.
  
  unfold sumList; simpl in *.
  intuition.
  
  rewrite sumList_cons.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    rewrite sumList_cons.
    eapply eqRat_refl.
  }

  simpl in *.
  eapply ratAdd_leRat_compat.
  eapply H.
  intuition.
  
  eapply IHls.
  intuition.
  
Qed.

Lemma sumList_distance_prod : forall (A : Set)(ls : list A)(f f1 f2 : A -> Rat),
  | (sumList ls (fun a => (f a) * (f1 a))) - (sumList ls (fun a => (f a) * (f2 a))) | <= sumList ls (fun a => (f a) * | (f1 a) - (f2 a) |).
  
  induction ls; intuition.
  unfold sumList; simpl in *.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  
  repeat rewrite sumList_cons.
  rewrite rat_distance_of_sum.
  eapply ratAdd_leRat_compat.
  eapply eqRat_impl_leRat.
  eapply ratMult_ratDistance_factor_l.
  eapply IHls.
Qed.

Theorem sumList_all : 
  forall (A : Set)(ls : list A)(f : A -> Rat) c,
    (forall a, In a ls -> (f a) == c) ->
    sumList ls f == (length ls)/1 * c.
  
  induction ls; intuition.
  unfold sumList; simpl.
  symmetry.
  eapply ratMult_0_l.
  
  rewrite sumList_cons.
  simpl in *.
  rewrite H; intuition.
  rewrite IHls; intuition.
  rewrite ratMult_comm.
  rewrite ratMult_ratAdd_cd.
  simpl.
  eapply ratMult_comm.
Qed.


Theorem filter_app : 
  forall (A : Set)(ls1 ls2 : list A)(f : A -> bool),
    filter f (ls1 ++ ls2) = filter f ls1 ++ filter f ls2.
  
  induction ls1; intuition; simpl in *.
  case_eq (f a); intuition.
  rewrite <- app_comm_cons.
  f_equal.
  eauto.
Qed.

Theorem filter_true : 
  forall (A : Set)(ls : list A)(f : A -> bool),
    (forall a, In a ls -> (f a) = true) ->
    filter f ls = ls.
  
  induction ls; intuition; simpl in *.
  case_eq (f a); intuition.
  f_equal.
  eauto.
  rewrite H in H0.
  discriminate.
  intuition.
  
Qed.

Theorem sumList_subset_le : 
  forall (A : Set){eqd: EqDec A}(ls1 ls2 : list A)(f : A -> Rat),
    NoDup ls1 ->
    NoDup ls2 ->
    (forall a, In a ls1 -> In a ls2) ->
    sumList ls1 f <= sumList ls2 f.
  
  induction ls1; intuition; simpl in *.
  unfold sumList; simpl.
  eapply rat0_le_all.
  
  inversion H; clear H; subst.
  rewrite sumList_cons.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply (@sumList_permutation _ _ _ (a :: removeFirst (EqDec_dec _) ls2 a)%list).
    eapply removeFirst_permutation.
    eapply H1.
    intuition.
  }
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply sumList_cons.
  }
  eapply ratAdd_leRat_compat; intuition.
  eapply IHls1; intuition.
  eapply removeFirst_NoDup.
  trivial.
  destruct (EqDec_dec _ a a0).
  subst.
  intuition.
  eapply removeFirst_in.
  eapply H1; intuition.
  intuition.
Qed.

Fixpoint allNatsLt (n : nat) :=
  match n with
    | 0 => nil
    | S n' => allNatsLt n' ++ (n' :: nil)
  end.


Lemma allNatsLt_length : 
  forall n, 
    length (allNatsLt n) = n.
  
  induction n; intuition; simpl in *.
  rewrite app_length.
  rewrite IHn.
  rewrite plus_comm.
  trivial.
Qed.


Lemma allNatsLt_lt : 
  forall n v,
    In v (allNatsLt n) ->
    v < n.
  
  induction n; intuition; simpl in *.
  intuition.
  apply in_app_or in H.
  simpl in *.
  intuition.
  
Qed.


Lemma app_NoDup : forall(A : Set)(ls1 ls2 : list A),
  NoDup ls1 ->
  NoDup ls2 ->
  (forall a, In a ls1 -> ~In a ls2) ->
  (forall a, In a ls2 -> ~In a ls1) ->
  NoDup (ls1 ++ ls2).

  induction ls1; intuition.

  inversion H; clear H; subst.
  rewrite <- app_comm_cons.
  econstructor.
  intuition.
  eapply in_app_or in H.
  intuition.
  eapply H1.
  simpl.
  left.
  eauto.
  trivial.

  eapply IHls1; eauto.
  intuition.
  eapply H1.
  simpl.
  right.
  eauto.
  eauto.
  intuition.
  eapply H1.
  simpl.
  right.
  eauto.
  eauto.
Qed.

Lemma allNatsLt_NoDup : 
  forall (n : nat),
    NoDup (allNatsLt n).
  
  induction n; simpl in *; intuition.
  econstructor.

  eapply app_NoDup; intuition.
  econstructor.
  simpl; intuition.
  econstructor.
  simpl in *.
  intuition; subst.
  eapply allNatsLt_lt in H.
  omega.

  simpl in *.
  intuition; subst.
  eapply allNatsLt_lt in H0.
  omega.
  
Qed.


Lemma allNatsLt_lt_if : 
  forall (n i : nat), 
    i < n ->
    In i (allNatsLt n).
  
  induction n; intuition; simpl in *.
  omega.

  eapply in_or_app.
  destruct (lt_dec i n).
  left.
  eauto.

  right.
  simpl.
  intuition.
    
Qed.

Lemma nth_allNatsLt_lt : 
  forall k n,
    n < k ->
    nth n (allNatsLt k) n = n.

  induction k; intuition; simpl in *.
  destruct (lt_dec n k).
  rewrite app_nth1.
  eauto.
  rewrite allNatsLt_length.
  trivial.
  rewrite app_nth2.
  rewrite allNatsLt_length.
  assert (k = n).
  omega.
  rewrite H0.
  rewrite minus_diag.
  simpl.
  trivial.
  rewrite allNatsLt_length.
  omega.

Qed.

Lemma nth_allNatsLt : 
  forall k n,
    nth n (allNatsLt k) n = n.

  intuition.

  destruct (lt_dec n k).
  eapply nth_allNatsLt_lt; intuition.

  eapply nth_overflow.
  rewrite allNatsLt_length.
  omega.
Qed.


Theorem allNatsLt_filter_lt : 
  forall (p n : nat),
    (n <= p)%nat->
    filter (fun z => if (lt_dec z n) then true else false) (allNatsLt p) = 
    allNatsLt n.
  
  induction p; intuition.
  simpl.
  assert (n = 0%nat). omega.
  subst. trivial.
  simpl.
  destruct (le_dec n p).
  rewrite filter_app.    
  rewrite IHp; intuition.
  simpl.
  destruct (lt_dec p n ).
  omega.
  eapply app_nil_r.
  
  assert (n = S p).
  omega.
  subst.
  simpl.
  rewrite filter_app.  
  f_equal.
  
  eapply filter_true.
  intuition.
  destruct (lt_dec a (S p)); intuition.
  apply allNatsLt_lt in H0.
  omega.
  
  simpl.
  destruct (lt_dec p (S p)); intuition.
    
Qed.

Theorem map_eq_all : 
  forall (A B : Type)(ls : list A)(f1 f2 : A -> B),
    map f1 ls = map f2 ls ->
    (forall a, In a ls -> f1 a = f2 a).
  
  induction ls; intuition; simpl in *.
  intuition.
  intuition; subst.
  inversion H; clear H; subst.
  trivial.
  
  inversion H; clear H; subst.
  eapply IHls; intuition.
  
Qed.

Theorem map_eq_if_all : 
  forall (A B : Type)(ls : list A)(f1 f2 : A -> B),
    (forall a, In a ls -> f1 a = f2 a) ->
    map f1 ls = map f2 ls.
  
  induction ls; intuition; simpl in *.
  f_equal.
  eapply H.
  intuition.
  eapply IHls.
  intuition.
  
Qed.

Theorem map_eq_subset : 
  forall (A B : Type)(ls2 ls1 : list A)(f1 f2 : A -> B),
    map f1 ls1 = map f2 ls1 ->
    (forall a, In a ls2 -> In a ls1) ->
    map f1 ls2 = map f2 ls2.
  
  intuition.
  specialize (map_eq_all _ _ _ H); intros.
  eapply map_eq_if_all.
  intuition.
  
Qed.

Fixpoint getSomes(A : Type)(ls : list (option A)) :=
  match ls with
    | nil => nil
    | o :: ls' =>
      match o with
        | None => getSomes ls'
        | Some x => x :: (getSomes ls')
      end
  end.

Lemma nth_nil:
  forall (A : Set)(i : nat)(def : A),
    nth i nil def = def.
  
  induction i; intuition; simpl in *.
  
Qed.

Theorem listReplace_None_Permutation : 
  forall (A : Set) n ls (y : A),
    nth n ls None = None ->
    Permutation (getSomes (listReplace ls n (Some y) None)) (y :: (getSomes ls)).
  
  induction n; intuition; simpl in *.
  destruct ls; simpl in *.
  eapply Permutation_refl.
  subst.
  eapply Permutation_refl.
  
  destruct ls; simpl in *.
  eapply (IHn nil).
  eapply nth_nil.
  
  destruct o.
  eapply Permutation_sym.
  eapply perm_trans.
  eapply perm_swap.
  eapply perm_skip.
  eapply Permutation_sym.
  eapply IHn.
  trivial.
  eapply IHn.
  trivial.

Qed.

Theorem listReplace_getSomes_Permutation_h : 
  forall (A : Set) l1' l2,
    Permutation l1' l2 ->
    forall l1 n2 (y : A),
      l1' = getSomes l1 ->
      nth n2 l1 None = None ->
      Permutation
        (getSomes
           (listReplace l1 n2
                        (Some y) None))
        (y :: l2).
  
  induction 1; intuition.
  
  
  eapply perm_trans.
  eapply listReplace_None_Permutation.
  trivial.
  rewrite <- H.
  eapply Permutation_refl.
  
  eapply perm_trans.
  eapply listReplace_None_Permutation.
  trivial.
  rewrite <- H0.
  eapply perm_skip.
  eapply perm_skip.
  trivial.
  
  eapply perm_trans.
  eapply listReplace_None_Permutation.
  trivial.
  rewrite <- H.
  eapply perm_skip.
  eapply perm_swap.
  
  eapply perm_trans.
  eapply listReplace_None_Permutation.
  trivial.
  rewrite <- H1.
  eapply perm_skip.
  eapply perm_trans.
  eapply H.
  trivial.
Qed.

Theorem listReplace_getSomes_Permutation : 
  forall (A : Set) l1 l2 n2 (y : A),
    nth n2 l1 None = None ->
    Permutation (getSomes l1) l2 ->
    Permutation
      (getSomes
         (listReplace l1 n2
                      (Some y) None))
      (y :: l2).
  
  intuition.
  eapply listReplace_getSomes_Permutation_h; eauto.
  
Qed.

Lemma nth_listReplace_ne : 
  forall (i1 i2 : nat)(A : Set)(ls : list A)(a def : A),
    i1 <> i2 ->
    nth i1 (listReplace ls i2 a def) def = 
    nth i1 ls def.
  
  induction i1; destruct i2; destruct ls; intuition; simpl in *.
  destruct i1; trivial.
  
  rewrite IHi1.
  eapply nth_nil.
  omega.
  eapply IHi1.
  omega.
  
Qed.


Theorem listReplace_length :
  forall (A : Set)(ls : list A)(i : nat)(a def : A),
    i < length ls ->
    length (listReplace ls i a def) = length ls.
  
  induction ls; intuition; simpl in *.
  omega.
  
  destruct i; simpl in *.
  trivial.
  
  f_equal.
  eapply IHls.
  omega.
  
Qed.

Lemma listReplace_in_nil : 
  forall (A : Set)(i : nat)(a1 a2 def : A),
    In a1 (listReplace nil i a2 def) ->
    a1 = a2 \/ a1 = def.
  
  induction i; intuition; simpl in *.
  intuition.
  intuition.
  
Qed.

Lemma listReplace_in : 
  forall (A : Set)(ls : list A)(a1 a2 def : A)(i : nat),
    In a1 (listReplace ls i a2 def) ->
    (In a1 ls \/ a1 = a2 \/ a1 = def).

  induction ls; intuition; simpl in *.
  right.
  
  eapply listReplace_in_nil.
  eauto.
  
  destruct i; simpl in *.
  intuition.
  
  intuition.
  edestruct (IHls); eauto.
  
Qed.

Theorem firstn_map : 
  forall (A B : Set)(f : A -> B)(ls : list A) n,
    firstn n (map f ls) = map f (firstn n ls).
  
  induction ls; destruct n; intuition; simpl in *.
  f_equal.
  eauto.
Qed.


Lemma firstn_app_eq : 
  forall (A : Set)(ls1 ls2 : list A),
    firstn (length ls1) (ls1 ++ ls2) = ls1.
  
  induction ls1; intuition; simpl in *.
  f_equal.
  eauto.
  
Qed.

Theorem map_nth_in : 
  forall (A B : Set)(ls : list A)(f : A -> B) i defa defb,
    i < length ls ->
    nth i (map f ls) defb = f (nth i ls defa).
  
  induction ls; destruct i; intuition; simpl in *.
  omega.
  omega.
  eapply IHls.
  omega.

Qed.

Lemma flatten_app : 
  forall (A : Set)(ls1 ls2 : list (list A)),
    flatten (ls1 ++ ls2) = flatten ls1 ++ flatten ls2.
  
  induction ls1; intuition; simpl in *.
  rewrite <- app_assoc.
  f_equal.
  eauto.
  
Qed.

(* list_pred lifts a predicate on A and B to a predicate on list A and list B.  It is useful for reasoning about fold, map, etc. *)
Inductive list_pred(A B : Set)(pred : A -> B -> Prop) : list A -> list B -> Prop :=
| list_pred_nil : 
    list_pred pred nil nil
| list_pred_cons : 
    forall a1 a2 ls1 ls2,
      pred a1 a2 ->
      list_pred pred ls1 ls2 ->
      list_pred pred (a1 :: ls1) (a2 :: ls2).

Lemma list_pred_eq_impl_eq : 
  forall (A : Set)(ls1 ls2 : list A),
    list_pred eq ls1 ls2 ->
    ls1 = ls2.
  
  induction 1; intuition; simpl in *; subst.
  f_equal; eauto.
  
Qed.


Lemma flatten_eq : 
  forall (A : Set)(ls1 ls2 : list (list A)),
    list_pred eq ls1 ls2 ->
    flatten ls1 = flatten ls2.
  
  induction 1; intuition; simpl in *; subst.
  f_equal.
  eauto.

Qed.

Theorem app_cons_eq : 
  forall (A : Type) ls2 ls1 (a : A),
    ls2 ++ (a :: ls1) = (ls2 ++ (a :: nil)) ++ ls1.
  
  induction ls2; intuition; simpl in *.
  f_equal.
  eauto.
  
Qed.

Theorem skipn_nil : 
  forall (A : Type) n,
    skipn n (@nil A) = nil.
  
  induction n; intuition; simpl in *.
  
Qed.

Theorem nth_In_exists : 
  forall (A : Type)(ls : list A) a def,
    In a ls ->
    exists n, nth n ls def = a.
  
  induction ls; intuition; simpl in *.
  intuition.
  
  intuition; subst.
  exists O.
  trivial.
  edestruct IHls.
  eauto.
  exists (S x).
  eauto.
  
Qed.

Theorem nth_skipn_eq : 
  forall (A : Set)(y x: nat)(ls : list A)(def : A),
    nth x (skipn y ls) def = nth (x + y) ls def.
  
  induction y; intuition; simpl in *.
  rewrite plus_0_r.
  trivial.
  
  destruct ls.
  rewrite nth_nil.
  rewrite nth_nil.
  trivial.
  
  rewrite plus_comm.
  simpl.
  rewrite plus_comm.
  eapply 
    IHy.
  
Qed.

Theorem perm_flatten_listReplace_nil : 
  forall b (A : Set)(a : A),
    Permutation (flatten (listReplace nil b (a :: nil) nil)) (a :: nil).
  
  induction b; intuition; simpl in *.
  
Qed.

Theorem perm_flatten_listReplace : 
  forall b (A : Set)(ls1 : list (list A))(ls2 : list A) (a : A),
    Permutation (flatten ls1) ls2 ->
    Permutation (flatten (listReplace ls1 b (nth b ls1 nil ++ (a :: nil)) nil))
                (a :: ls2).
  
  induction b; intuition; simpl in *.
  destruct ls1.
  simpl in *.
  apply Permutation_nil in H.
  subst.
  eapply Permutation_refl.
  
  simpl in *.
  rewrite <- app_cons_eq.
  
  eapply Permutation_trans.
  eapply Permutation_app_comm.
  rewrite <- app_comm_cons.
  econstructor.
  eapply Permutation_trans.
  eapply Permutation_app_comm.
  trivial.
  
  destruct ls1.
  simpl in *.
  eapply Permutation_nil in H.
  subst.
  
  eapply perm_flatten_listReplace_nil .
  simpl in *.
  eapply Permutation_trans.
  eapply Permutation_app.
  eapply Permutation_refl.
  eapply IHb.
  eapply Permutation_refl.
  
  eapply Permutation_trans.
  eapply Permutation_app_comm.
  rewrite <- app_comm_cons.
  econstructor.
  eapply Permutation_trans.
  eapply Permutation_app_comm.
  trivial.
  
Qed.

Theorem map_cons : 
  forall (A B : Type)(f : A -> B)(ls : list A)(a : A),
    map f (a :: ls) = (f a) :: map f ls.
  
  intuition.
  
Qed.

Theorem app_eq_inv : 
  forall (A : Type)(ls1 ls2 ls3 ls4 : list A),
    length ls1 = length ls3 ->
    (ls1 ++ ls2) = (ls3 ++ ls4) ->
    ls1 = ls3 /\ ls2 = ls4.
  
  induction ls1; destruct ls3; intros; simpl in *; subst.
  intuition.
  
  omega.
  omega.
  
  inversion H0; clear H0; subst.
  
  specialize (IHls1 ls2 ls3 ls4).
  intuition.
  f_equal.
  eapply IHls1; intuition; omega.
  eapply IHls1; intuition; omega.

Qed.

Theorem NoDup_app : 
  forall (A : Type)(ls1 ls2 : list A),
    NoDup (ls1 ++ ls2) ->
    NoDup ls1 /\
    NoDup ls2 /\
    (forall a1 a2,
       In a1 ls1 ->
       In a2 ls2 ->
       a1 <> a2).
  
  induction ls1; intros; simpl in *.
           
  intuition.
  econstructor.
  
  inversion H; clear H; subst.
  eapply IHls1 in H3.
  intuition.
  econstructor.
  intuition.
  trivial.
  
  subst.
  eapply H2.
  eapply in_or_app.
  intuition.
  subst.
  
  eapply H3; eauto.
  
Qed.

Theorem firstn_In : 
  forall (A : Type) n (ls : list A)(a : A),
             In a (firstn n ls) ->
             In a ls.
  
  induction n; destruct ls; intuition; simpl in *;
  intuition.
Qed.

Theorem pred_firstn_In :
  forall (A : Set) ls1 ls2,
    list_pred (fun x0 y : list A => exists n : nat, y = firstn n x0) ls1 ls2 ->
    forall a,
      In a (flatten ls2) -> In a (flatten ls1).
  
  induction 1; intuition; simpl in *.
  destruct H.
  subst.
  eapply in_app_or in H1.
  intuition.
  eapply in_or_app.
  left.
  eapply firstn_In.
  eauto.
Qed.    


Theorem firstn_NoDup : 
  forall (A : Type) n (ls : list A),
    NoDup ls ->
    NoDup (firstn n ls).
  
  induction n; destruct ls; intuition; simpl in *.
  econstructor.
  
  inversion H; clear H; subst.
  econstructor.
  
  intuition.
  eapply H2.
  eapply firstn_In.
  eauto.
  
  eapply IHn; intuition.
  
Qed.
 
Theorem NoDup_flatten_subset : 
  forall (A : Set)(ls1 ls2 : list (list A)),
    list_pred (fun x y => exists n, y = firstn n x) ls1 ls2 ->
    NoDup (flatten ls1) ->
    NoDup (flatten ls2).
  
  induction 1; intuition; simpl in *.
  destruct H.
  subst.
  eapply NoDup_app in H1.
  intuition.
  eapply app_NoDup; intuition.
   
  eapply firstn_NoDup.
  trivial.
  
  eapply H3.
  eapply firstn_In.
  eauto.
    
  eapply pred_firstn_In.
  eauto.
  eauto.
  intuition.
  
  eapply H3.
  eapply firstn_In.
  eauto.
  eapply pred_firstn_In.
  eauto.
  eauto.
  intuition.
Qed.

Theorem allNatsLt_nil_inv :
  forall n,
    allNatsLt n = nil ->
    n = O.
  
  destruct n; intuition; simpl in *.
  eapply app_eq_nil in H.
  intuition.
  discriminate.
  
Qed.
  
Theorem firstn_allNatsLt_h : 
  forall ls n1 n2,
    n2 >= n1 ->
    ls = (allNatsLt n2) ->
    firstn n1 ls = allNatsLt n1.
  
  induction ls using rev_ind; intuition; simpl in *.
  
  symmetry in H0.
  eapply allNatsLt_nil_inv in H0.
  subst.
  assert (n1 = O).
  omega.
  subst.
  simpl.
  trivial.
  
  destruct n2; simpl in *.
  eapply app_eq_nil in H0.
  intuition.
  discriminate.
  eapply app_inj_tail in H0.
  intuition.
  subst.  
  
  destruct (le_gt_dec n1 (length (allNatsLt n2))).
  rewrite firstn_app.
  eapply (@IHls); eauto.
  rewrite allNatsLt_length.
  trivial.
  trivial.

  rewrite allNatsLt_length in g.
  assert (n1 = (S n2)).
  omega.
  subst.
  
  eapply firstn_ge_all.
  rewrite allNatsLt_length.
  intuition.
Qed.

Theorem firstn_allNatsLt : 
  forall n1 n2,
    n2 >= n1 ->
    firstn n1 (allNatsLt n2) = allNatsLt n1.
  
  intuition.
  eapply firstn_allNatsLt_h;
    eauto.
  
Qed.

Theorem NoDup_app_l : 
  forall (A : Type)(ls1 ls2 : list A),
    NoDup (ls1 ++ ls2) ->
    NoDup ls1.
  
  intuition.
  eapply NoDup_app in H.
  intuition.
  
Qed.

Theorem NoDup_map : 
  forall (A B : Type)(f : A -> B)(ls : list A),
    NoDup (map f ls) ->
    (NoDup ls /\ (forall b1 b2, In b1 ls -> In b2 ls -> f b1 = f b2 -> b1 = b2)).
  
  induction ls; intros; simpl in *.
  intuition.
  econstructor.
  inversion H; clear H; subst.
  intuition.
  econstructor.
  intuition.
  eapply H2.
  eapply in_map_iff.
  econstructor.
  intuition.
  trivial.
  
  subst.
  trivial.
  
  subst.
  exfalso.
  eapply H2.
  eapply in_map_iff.
  econstructor.
  split.
  symmetry.
  eapply H5.
  trivial.
  
  subst.
  exfalso.
  eapply H2.
  eapply in_map_iff.
  econstructor.
  split.
  eapply H5.
  trivial.
  
Qed.

Theorem map_fst_eq : 
  forall (C : Set)(lsc : list C)(A B : Set)(ls : list A)(f : A -> B),
    (length ls = length lsc) ->
    map f ls = 
    map (fun x => f (fst x)) (combine ls lsc).
  
  induction lsc; destruct ls; intuition; simpl in *.
  omega.
  f_equal.
  eauto.
Qed.

Theorem map_snd_eq : 
  forall (C : Set)(lsc : list C)(A B : Set)(ls : list A)(f : A -> B),
    (length ls = length lsc) ->
    map f ls = 
    map (fun x => f (snd x)) (combine lsc ls).
  
  induction lsc; destruct ls; intuition; simpl in *.
  omega.
  f_equal.
  eauto.
Qed.

Theorem In_combine_NoDup_eq_l : 
  forall (A B : Set)(lsa : list A)(lsb : list B) a1 a2 b,
    NoDup lsb ->
    In (a1, b) (combine lsa lsb) ->
    In (a2, b) (combine lsa lsb) ->
    a1 = a2.
  
  induction lsa; intuition; simpl in *.
  intuition.
  destruct lsb.
  simpl in *.
  intuition.
  inversion H; clear H; subst.
  simpl in *.
  intuition.
  repeat pairInv.
  trivial.
  pairInv.
  eapply in_combine_r in H0.
  intuition.
  
  pairInv.
  eapply in_combine_r in H.
  intuition.
  
  eauto.
Qed.

Theorem In_combine_NoDup_eq_r : 
  forall (A B : Set)(lsa : list A)(lsb : list B) a b1 b2,
    NoDup lsa ->
    In (a, b1) (combine lsa lsb) ->
    In (a, b2) (combine lsa lsb) ->
    b1 = b2.
  
  induction lsa; intuition; simpl in *.
  intuition.
  destruct lsb.
  simpl in *.
  intuition.
  inversion H; clear H; subst.
  simpl in *.
  intuition.
  repeat pairInv.
  trivial.
  pairInv.
  eapply in_combine_l in H0.
  intuition.
  
  pairInv.
  eapply in_combine_l in H.
  intuition.
  
  eauto.
Qed.

Theorem zip_eq_nil_l : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    zip lsa lsb = nil ->
    length lsa = length lsb ->
    lsa = nil.
  
  induction lsa; intuition; simpl in *.
  destruct lsb; simpl in *.
  omega.
  discriminate.
       
Qed.

Theorem fst_split_app_eq : 
  forall (A B : Type)(ls1 ls2 : list (A * B)),
    fst (split (ls1 ++ ls2)) = 
    fst (split ls1) ++ fst (split ls2).
  
  induction ls1; intuition; simpl in *.
  specialize (IHls1 ls2).
  remember (split (ls1 ++ ls2)) as z.
  destruct z.
  remember (split ls1) as y.
  destruct y.
  simpl in *.
  subst.
  trivial.
Qed.

Theorem fst_split_flatten_eq : 
  forall (A B : Type)(ls : list (list (A * B))),
    fst (split (flatten ls)) = 
    flatten (map (fun x => fst (split x)) ls).
  
  induction ls; intuition; simpl in *.
  rewrite  fst_split_app_eq .
  f_equal.
  trivial.
  
Qed.

Theorem fst_split_map_eq : 
  forall (A B C : Type)(ls : list A)(f : A -> B * C),
    fst (split (map f ls)) = 
    map (fun a => fst (f a)) ls.
  
  induction ls; intuition; simpl in *.
  remember (f a) as z.
  destruct z.
  remember (split (map f ls)) as y.
  destruct y.
  simpl.
  f_equal.
  assert (l = fst (split (map f ls))).
  rewrite <- Heqy.
  trivial.
  subst.
  eauto.
Qed.

Theorem in_split_l_if : 
  forall (A B : Type)(ls : list (A * B)) a,  
    In a (fst (split ls)) -> 
    exists b,
      In (a, b) ls.
  
  induction ls; intuition; simpl in *.
  intuition.
  
  remember (split ls) as z.
  destruct z.
  simpl in *.
  intuition.
  subst.
  econstructor; intuition.
  
  edestruct IHls; eauto.
  
Qed.

Theorem in_fst_split_if : 
  forall (A B : Type)(ls : list (A * B)) a b,
    In (a, b) ls ->
    In a (fst (split ls)).
  
  induction ls; intuition; simpl in *.
  intuition.
  pairInv.
  remember (split ls) as z.
  destruct z.
  simpl.
  intuition.
  
  remember (split ls) as z.
  destruct z.
  simpl in *.
  right.
  eapply IHls.
  eauto.
  
Qed.

Theorem map_pair_fst_eq : 
  forall (A B C D: Type)(f1 : B -> D)(f2 : C -> D)(ls1 : list B)(ls2 : list C)(a1 a2 : A),
    map (fun x => (a1, f1 x)) ls1 = map (fun x => (a2, f2 x)) ls2 ->
    ls1 <> nil ->
    a1 = a2.
  
  induction ls1; destruct ls2; intuition; simpl in *.
  discriminate.
  inversion H; clear H; subst.
  trivial.
  
Qed.

Theorem In_zip_strong : 
  forall (A B : Set)(ls : list A) f a (b : B),
    In (a, b) (zip ls (map f ls)) ->
    (In a ls /\ b = f a).
  
  induction ls; intuition; simpl in *.
  intuition.
  intuition.
  pairInv.
  intuition.
  
  right.
  eapply IHls.
  eauto.
  
  intuition.
  pairInv.
  trivial.
  eapply IHls; eauto.
Qed.


Lemma list_pred_impl : 
  forall (A B : Set)(lsa : list A)(lsb : list B) (P1 : A -> B -> Prop),
       list_pred P1 lsa lsb ->
       forall (P2 : A -> B -> Prop), 
         (forall a b, P1 a b -> P2 a b) ->
         list_pred P2 lsa lsb.
  
  induction 1; intuition; simpl in *.
  econstructor.
  
  econstructor; eauto.
Qed.

Theorem list_pred_eq_in : 
  forall (A : Set)(ls : list A),
    list_pred (fun a b => a = b /\ In a ls /\ In b ls) ls ls.
  
  induction ls; intuition; simpl in *.
  econstructor.
  econstructor.
  intuition.
  eapply list_pred_impl.
  eapply IHls.
  intuition.
  intuition.
  intuition.
  intuition.
Qed.

Theorem zip_combine_eq : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    zip lsa lsb = combine lsa lsb.
  
  induction lsa; intuition; simpl in *.
  destruct lsb; intuition.
  f_equal.
  eauto.
  
Qed.

Theorem list_pred_fst_split_eq : 
  forall (A B C : Set)(ls1 : list (A * B))(ls2 : list (A * C)),
    list_pred (fun a b => fst a = fst b) ls1 ls2 ->
    fst (split ls1)  = fst (split ls2).
  
  induction 1; intuition; simpl in *.
  destruct a1.
  destruct a2.
  remember (split ls1) as z.
  destruct z.
  remember (split ls2) as z.
  destruct z.
  simpl in *.
  subst.
  trivial.
  
Qed.

Theorem unzip_eq_split : 
  forall (A B : Set)(ls : list (A * B)),
    unzip ls = split ls.
  
  induction ls; intuition; simpl in *.
  remember (split ls) as z.
  destruct z.
  unfold unzip.
  simpl.
  f_equal.
  f_equal.
  
  assert (l = fst (l, l0)).
  trivial.
  rewrite H.
  rewrite <- IHls.
  trivial.
  
  assert (l0 = snd (l, l0)).
  trivial.
  rewrite H.
  rewrite <- IHls.
  f_equal.
  
Qed.

Theorem in_split_r_if:
  forall (A B : Type) (ls : list (A * B)) (b : B),
    In b (snd (split ls)) -> exists a : A, In (a, b) ls.
  
  induction ls; intuition; simpl in *.
  intuition.
  remember (split ls) as z.
  destruct z.
  simpl in *.
  intuition.
  subst.
  econstructor.
  intuition.
  
  edestruct IHls.
  eauto.
  econstructor.
  right.
  eauto.
  
Qed.

(* There is nth_error in the Coq library, but it seems to return something in Type. *)
Fixpoint nth_option(A : Set)(ls : list A)(i : nat) :=
  match ls with 
    | nil => None
    | a :: ls' =>
      match i with
        | O => Some a
        | S i' =>
          nth_option ls' i'
          end
  end.

Theorem nth_option_app_Some : 
  forall (A : Set)(ls1 ls2 : list A) i a,
    nth_option ls1 i = Some a ->
    nth_option (ls1 ++ ls2) i = Some a.
  
  induction ls1; intuition; simpl in *.
  congruence.
  destruct i; trivial.
  eauto.
Qed.

Theorem nth_option_Some_lt : 
  forall (A : Set)(ls : list A) i a,
    nth_option ls i = Some a ->
    i < length ls.
  
  induction ls; intuition; simpl in *.
  discriminate.
  destruct i.
  omega.
  eapply lt_n_S.
  eauto.
  
Qed.

Theorem nth_option_app_None : 
  forall (A : Set)(ls1 ls2 : list A) i,
    nth_option ls1 i = None ->
    nth_option (ls1 ++ ls2) i = nth_option ls2 (i - length ls1).
  
  induction ls1; intuition; simpl in *.
  
  destruct i.
  discriminate.
  eauto.
Qed.

Theorem nth_option_None_ge : 
  forall (A : Set)(ls : list A) i,
    nth_option ls i = None ->
    i >= length ls.
  
  induction ls; intuition; simpl in *.
  destruct i.
  discriminate.
  eapply le_n_S.
  eapply IHls.
  trivial.
Qed.

Theorem skipn_S_eq : 
  forall (A : Set)(ls : list A) n a,
    nth_option ls n = Some a -> 
    skipn n ls = a :: (skipn (S n) ls).
  
  induction ls; intuition; simpl in *.
  discriminate.
  destruct n; simpl in *.
  inversion H; clear H; subst.
  trivial.
  eauto.
  
Qed.

Theorem nth_option_snd_split : 
  forall (A B : Set)(ls : list (A * B)) n a b,
    nth_option ls n = Some (a, b) ->
    nth_option (snd (split ls)) n = Some b.
  
  induction ls; intuition; simpl in *.
  discriminate.
  
  destruct n.
  inversion H; clear H; subst.
  remember (split ls) as z.
  destruct z.
  simpl.
  trivial.
  
  remember (split ls) as z.
  destruct z.
  simpl in *.
  eauto.
  
Qed.

Theorem snd_split_map_eq :
  forall (A B C : Set)(ls : list A)(f : A -> B * C),
    snd (split (map f ls)) =
    map (fun p => snd (f p)) ls.
  
  induction ls; intuition; simpl in *.
  remember (f a) as z.
  destruct z.
  remember (split (map f ls)) as z.
  destruct z.
  simpl.
  f_equal.
  assert (l0 = snd (l, l0)).
  trivial.
  rewrite H.
  rewrite Heqz0.
  eapply IHls.
Qed.

Theorem cons_ne : 
  forall (A : Set)(eqda : eq_dec A)(a1 a2 : A)(ls1 ls2 : list A),
    ((a1 :: ls1) = (a2 :: ls2) -> False) ->
    (a1 <> a2) \/ (ls1 <> ls2).
  
  intuition.
  
  destruct (eqda a1 a2).
  subst.
  right.
  intuition.
  subst.
  intuition.
  
  left.
  intuition.
  
Qed.

Theorem map_ne_same_ex : 
  forall (A B : Set)(f1 f2 : A -> B)(ls : list A),
    eq_dec B ->
    map f1 ls <> map f2 ls ->
    exists a, In a ls /\ f1 a <> f2 a.
  
  induction ls; intuition; simpl in *.
  
  eapply cons_ne in H0.
  destruct H0.
  econstructor.
  intuition.
  intuition.
  destruct H2.
  intuition.
  exists x.
  intuition.
  trivial.
Qed.

Theorem list_pred_I_in : 
  forall (A B : Set)(lsa : list A)(lsb : list B),
    length lsa = length lsb ->
    list_pred (fun a b => In a lsa /\ In b lsb) lsa lsb.
  
  induction lsa; destruct lsb; intuition; simpl in *.
  econstructor.
  discriminate.
  discriminate.
  
  econstructor.
  intuition.
  eapply list_pred_impl.
  eapply IHlsa.
  omega.
  intuition.
  intuition.
  intuition.
Qed.

Theorem list_pred_fst_split_eq_l : 
  forall (A B : Set)(a : list (A * B))(b : list A),
    list_pred (fun a0 b0 => fst a0 = b0) a b ->
    b = fst (split a).

  induction a; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.
  
  inversion H; clear H; subst.
  simpl.
  remember (split a0) as z.
  destruct z.
  simpl in *.
  f_equal.
  eapply IHa.
  trivial.
  
Qed.

Theorem list_pred_fst_split_flatten_eq_l : 
  forall (A B : Set)(a : list (list (A * B)))(b : list (list A)),
    list_pred
      (list_pred
         (fun a0 b0 => fst a0 = b0)) a b ->
    flatten b = fst (split (flatten a)).
  
  induction a; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.
  
  inversion H; clear H; subst.
  simpl.
  rewrite fst_split_app_eq.
  f_equal.
  eapply list_pred_fst_split_eq_l .
  trivial.
  
  eauto.
  
Qed.

Theorem fold_add_const_mult : 
  forall (A : Type)(ls : list A)(c : nat) init,
    (fold_left (fun acc _ => acc + c) ls init = 
     (length ls) * c + init)%nat.
  
  induction ls; intuition; simpl in *.
  rewrite IHls.
  omega.
  
Qed.

Theorem list_pred_snd_split_eq_l:
  forall (A B : Set) (a : list (B * A)) (b : list A),
    list_pred (fun (a0 : B * A) (b0 : A) => snd a0 = b0) a b ->
    b = snd (split a).
  
  induction 1; intuition; simpl in *.
  subst.
  destruct a1.
  remember (split ls1) as z.
  destruct z.
  simpl. 
  trivial.
  
Qed.

Theorem NoDup_snd_split_if : 
  forall (A B : Type)(ls : list (A * B)),
    NoDup (snd (split ls)) ->
    NoDup ls.
  
  induction ls; intuition; simpl in *.
  econstructor.
  
  remember (split ls) as z.
  destruct z.
  destruct a.
  simpl in *.
  inversion H; clear H; subst.
  econstructor.
  intuition.
  eapply in_split_r in H.
  rewrite <- Heqz in H.
  simpl in *.
  intuition.
  intuition.
Qed.

Fixpoint forNats(n : nat) :=
  match n with
      | 0 => nil
      | S n' =>
        cons n' (forNats n')
  end.

Lemma forNats_In : 
  forall n i,
    i < n <->
    In i (forNats n).
  
  induction n; intuition; simpl in *.
  omega.
  intuition.
  destruct (lt_dec i n).
  right.
  eapply IHn.
  trivial.
  left.
  omega.

  intuition.
  eapply lt_trans.
  eapply IHn.
  trivial.
  omega.

Qed.

Lemma forNats_NoDup : 
  forall n,
    NoDup (forNats n).

  induction n; intuition; simpl in *;
  econstructor; intuition.
  assert (n < n).
  eapply forNats_In.
  trivial.
  omega.

Qed.

Lemma forNats_length : 
  forall n,
    length (forNats n) = n.
  
  induction n; intuition; simpl in *.
  f_equal; intuition.
  
Qed.

Lemma sumList_forNats_first_ls : 
  forall (n : nat)(f : nat -> Rat),
    n <> O ->
    f O <= sumList (forNats n) f.
  
  induction n; intuition; simpl in *.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    rewrite sumList_cons.
    eapply eqRat_refl.
  }
  destruct n.
  eapply leRat_trans.
  rewrite ratAdd_0_r.
  eapply leRat_refl.
  eapply ratAdd_leRat_compat; intuition.
  eapply rat0_le_all.
  rewrite ratAdd_0_l.
  eapply ratAdd_leRat_compat; intuition.
  eapply rat0_le_all.
Qed.

Lemma sumList_forNats_distance : 
  forall (n : nat)(f : nat -> Rat), 
    (| sumList (forNats n) f - sumList (forNats n) (fun i => f (S i)) |) == (| (f O) - (f n) |).
  
  intuition.

  destruct (eq_nat_dec n O).
  subst.
  simpl.
  unfold sumList.
  simpl.
  eapply eqRat_trans.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  symmetry.
  rewrite <- ratIdentityIndiscernables.
  intuition.

  assert (sumList (forNats n) f == (ratSubtract (sumList (forNats n) f) (f O)) + (f O)).
  induction n; intuition.
  simpl.
  repeat rewrite sumList_cons.
  destruct n.
  simpl.
  unfold sumList.
  simpl.
  rewrite <- ratAdd_0_r.
  rewrite ratSubtract_0.
  rewrite <- ratAdd_0_l.
  intuition.
  intuition.
  rewrite IHn.
  rewrite ratSubtract_ratAdd_assoc.
  rewrite ratSubtract_ratAdd_assoc; intuition.
  rewrite (@ratSubtract_0 (f O)); intuition.
  rewrite <-ratAdd_0_r.
  symmetry.
  eapply ratAdd_assoc.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply ratAdd_0_l.
  eapply ratAdd_leRat_compat; intuition.
  eapply rat0_le_all.
  intuition.

  rewrite H.
  clear H.

  assert (sumList (forNats n) (fun i : nat => f (S i)) == (ratSubtract (sumList (forNats n) f) (f O)) + (f n)).
  induction n; intuition.
  simpl.
  repeat rewrite sumList_cons.
  destruct n.
  simpl.
  unfold sumList.
  simpl.
  repeat rewrite <- ratAdd_0_r.
  rewrite ratSubtract_0; intuition.
  rewrite <- ratAdd_0_l.
  intuition.

  rewrite IHn.
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat; intuition.
  rewrite ratSubtract_ratAdd_assoc.
  rewrite ratAdd_comm.
  intuition.

  eapply sumList_forNats_first_ls;
  intuition.
  intuition.
  rewrite H.
  eapply ratDistance_add_same_l.

Qed.

Lemma flatten_map_eq : 
  forall (A B : Set)(ls : list A)(f : A -> B),
    flatten (map (fun a => (f a) :: nil) ls) =
    map f ls.
  
  induction ls; intuition; simpl in *.
  f_equal; intuition.
  
Qed.

Lemma app_NoDup_inv : 
    forall (A : Set)(ls1 ls2 : list A), 
      NoDup (ls1 ++ ls2) ->
      (forall a, In a ls1 -> In a ls2 -> False).
    
    induction ls1; intuition; simpl in *.
    intuition.
    subst.
    inversion H; clear H; subst.
    eapply H3.
    eapply in_or_app.
    intuition.

    inversion H; clear H; subst.
    eapply IHls1;
    eauto.  

  Qed.

  
Lemma flatten_NoDup : 
  forall (A : Set)(ls : list (list A)),
    NoDup ls ->
    (forall x, In x ls -> NoDup x) ->
    (forall x1 x2, In x1 ls -> In x2 ls -> x1 <> x2 -> NoDup (x1 ++ x2)) ->
    NoDup (flatten ls).
  
  induction ls; intuition; simpl in *.
  econstructor.
  
  inversion H; clear H; subst.
  eapply app_NoDup; intuition.
  
  eapply in_flatten in H3.
  destruct H3.
  intuition.
  eapply app_NoDup_inv.
  eapply H1.
  right.
  eapply H6.
  left.
  reflexivity.
  intuition.
  subst.
  intuition.
  eauto.
  trivial.
  
  eapply in_flatten in H2.
  destruct H2.
  intuition.
  eapply app_NoDup_inv.
  eapply H1.
  right.
  eapply H6.
  left.
  reflexivity.
  intuition.
  subst.
  intuition.
  eauto.
  trivial.
Qed.

Lemma map_NoDup'
: forall (A B : Set) (ls : list A) (f : A -> B),
    NoDup ls ->
    (forall a1 a2 : A, In a1 ls -> In a2 ls ->a1 <> a2 -> f a1 <> f a2) -> 
    NoDup (map f ls).
  
  induction ls; intuition; simpl in *;
  econstructor.
  
  inversion H; clear H; subst.
  intuition.
  eapply in_map_iff in H.
  destruct H.
  intuition.
  eapply H0.
  right.
  eauto.
  left.
  eauto.
  intuition.
  subst.
  intuition.
  intuition.
  
  inversion H; clear H; subst.
  eapply IHls; intuition.
  eapply H0.
  right.
  eapply H.
  right.
  eapply H1.
  intuition.
  trivial.
  
Qed.

Lemma getUnique_cons : 
  forall (A : Set)(eqd : eq_dec A)(ls2 ls1 : list A) a,
    a :: ls1 = (getUnique ls2 eqd) ->
    exists ls3 ls4, 
      ls2 = ls3 ++ (a :: ls4) /\
      ls1 = (getUnique ls4 eqd).
  
  induction ls2; intuition; simpl in *.
  inversion H.
  destruct (in_dec eqd a (getUnique ls2 eqd)).
  apply IHls2 in H.
  destruct H.
  destruct H.
  intuition.
  subst.
  econstructor.
  econstructor.
  split.
  eapply app_comm_cons.
  trivial.
  
  inversion H; clear H; subst.
  econstructor.
  econstructor.
  intuition.
  rewrite app_nil_l.
  trivial.
Qed.

Lemma getUnique_eq_inv : 
  forall (A : Set)(a : A)(eqd1 eqd2 : eq_dec A)(ls1 ls2 : list A),
    getUnique ls1 eqd1 = getUnique ls2 eqd2 ->
    In a ls1 -> 
    In a ls2.
  
  induction ls1; intuition; simpl in *; intuition; subst.
  
  destruct (in_dec eqd1 a (getUnique ls1 eqd1)).
  rewrite H in i.
  apply in_getUnique_if in i.
  trivial.
  
  apply getUnique_cons in H.
  destruct H.
  destruct H.
  intuition.
  subst.
  eapply in_or_app.
  simpl.
  intuition.
  
  destruct (in_dec eqd1 a0 (getUnique ls1 eqd1)).
  eapply IHls1; intuition.
  
  apply getUnique_cons in H.
  destruct H.
  destruct H.
  intuition.
  subst.
  apply in_or_app.
  simpl.
  right.
  right.
  eapply IHls1; intuition.
Qed.

Lemma sumList_app :
  forall (A : Set)(ls1 ls2 : list A)(f : A -> Rat),
    sumList (ls1 ++ ls2) f == (sumList ls1 f) + (sumList ls2 f).
  
  induction ls1; intuition; simpl in *.
  unfold sumList; simpl in *.
  rewrite <- ratAdd_0_l.
  intuition.
  
  repeat rewrite sumList_cons.
  rewrite IHls1.
  rewrite ratAdd_assoc.
  intuition.
Qed.

Lemma filter_all_true : 
  forall (A : Set)(ls : list A)(P : A -> bool), 
    (forall a, In a ls -> P a = true) ->
    filter P ls = ls.
  
  induction ls; intuition; simpl in *.
  
  assert (P a = true).
  eapply H; intuition.
  
  rewrite H0.
  f_equal; intuition.
  
Qed.

Lemma sumList_map : 
  forall (A B : Set)(ls : list A)(f1 : A -> B)(f : B -> Rat),
    sumList (map f1 ls) f == 
    sumList ls (fun a => f (f1 a)).
  
  induction ls; intuition; simpl in *.
  unfold sumList; simpl in *.
  intuition.

  repeat rewrite sumList_cons.
  eapply ratAdd_eqRat_compat; intuition.
  
Qed.

Lemma sumList_filter_twice : 
  forall (A B : Set)(P : A -> bool)(ls : list A)(lsf : A -> list B)(f : A * B -> Rat),
    sumList (filter (fun p => P (fst p)) (flatten (map (fun a => map (fun b => (a, b)) (lsf a)) ls))) f ==  
    sumList (filter P ls) (fun a => sumList (lsf a) (fun b => f (a, b))).
  
  induction ls; intuition; simpl in *.
  unfold sumList.
  simpl.
  intuition.
  case_eq (P a); intuition.
  rewrite sumList_cons.
  
  rewrite filter_app.
  rewrite sumList_app.
  eapply ratAdd_eqRat_compat; intuition.
  
  rewrite filter_all_true.
  eapply sumList_map.
  
  intuition.
  apply in_map_iff in H0.
  destruct H0.
  intuition.
  subst.
  simpl.
  trivial.
  
  rewrite filter_app.
  rewrite sumList_app.
  symmetry.
  
  rewrite ratAdd_0_l.
  symmetry.
  eapply ratAdd_eqRat_compat; intuition.
  eapply sumList_0; intuition.
  apply filter_In in H0.
  intuition.
  apply in_map_iff in H1.
  destruct H1.
  intuition.
  subst.
  simpl in *.
  congruence.
Qed.

Lemma filter_cons : 
  forall (A : Set)(P : A -> bool)(ls : list A) a,
    filter P (a :: ls) = 
    if (P a) then (a :: (filter P ls)) else (filter P ls).
  
  intuition.
Qed.

Theorem sumList_1_mult : 
  forall (A : Set)(ls : list A),
    sumList ls (fun _ => 1) == length ls / 1.
  
  induction ls; intuition.
  unfold sumList; simpl.
  reflexivity.
  
  rewrite sumList_cons.
  simpl.
  rewrite IHls.
  rewrite ratS_num.
  intuition.
Qed.

Theorem fold_left_orb_true_init : 
  forall (A : Type)(f : A -> bool)(ls : list A),
    fold_left (fun b x => orb b (f x)) ls true = true.
  
  induction ls; intuition.
  
Qed.

Theorem fold_left_orb_true_in : 
  forall (A : Type)(f : A -> bool)(ls : list A) a init,
    In a ls ->
    f a = true ->
    fold_left (fun b x => orb b (f x)) ls init = true.
  
  induction ls; intuition; simpl in *.
  intuition; subst.
  rewrite H0.
  rewrite orb_true_r.
  eapply fold_left_orb_true_init.
  
  eauto.
Qed.

Theorem hd_error_Some_In : 
  forall (A : Type)(ls : list A) a,
    hd_error ls = Some a ->
    In a ls.
  
  intuition.
  destruct ls; simpl in *.
  discriminate.
  inversion H; clear H; subst.
  intuition.
  
Qed.

Theorem fold_and_false_init :
  forall (A : Type)(ls : list A) P,
    fold_left (fun b z => b && negb (P z)) ls false = false.
  
  induction ls; intuition.
  
Qed.

Theorem hd_filter_false_eq_and_false : 
  forall (A : Type)(ls : list A)(P : A -> bool),
    (if hd_error (filter P ls) then false else true) =
    fold_left (fun (b : bool) (z : A) => b && negb (P z)) ls true.
  
  induction ls; intuition; simpl in *.
  destruct (P a).
  simpl.
  rewrite fold_and_false_init.
  trivial.
  
  eapply IHls.
  
Qed.

Theorem fst_split_eq_list_pred : 
  forall (A B : Set)(ls1 : list (A * B))(ls2 : list A),
    list_pred (fun a b => fst a = b) ls1 ls2 ->
    fst (split ls1) = ls2.
  
  induction 1; intuition; simpl in *.
  subst.
  destruct a1.
  remember (split ls1) as x.
  destruct x.
  simpl in *.
  f_equal.
Qed.

Theorem snd_split_eq_list_pred : 
  forall (A B : Set)(ls1 : list (B * A))(ls2 : list A),
    list_pred (fun a b => snd a = b) ls1 ls2 ->
    snd (split ls1) = ls2.
  
  induction 1; intuition; simpl in *.
  subst.
  destruct a1.
  remember (split ls1) as x.
  destruct x.
  simpl in *.
  f_equal.
Qed.

Theorem combine_map_eq : 
  forall (A B C : Type)(lsa : list A)(lsb : list B)(f : B -> C),
    combine lsa (map f lsb) = map (fun p => (fst p, f (snd p))) (combine lsa lsb).
  
  induction lsa; destruct lsb; intuition; simpl in *.
  f_equal; eauto.
  
Qed.


Theorem map_ext_pred : 
  forall (A B C : Set)(P : A -> B -> Prop)(lsa : list A)(lsb : list B)(f1 : A -> C)(f2 : B -> C),
    list_pred P lsa lsb ->
    (forall a b, P a b -> (f1 a) = (f2 b)) ->
    map f1 lsa = map f2 lsb.
  
  induction 1; intuition; simpl in *.
  f_equal; intuition.
  
Qed.

Theorem list_pred_combine_l_h : 
  forall (A C : Set)(lsa : list A)(lsc : list C) P1,
    list_pred P1 lsa lsc ->
    forall (B : Set)(lsb : list B) P2, 
      list_pred P2 lsb lsc ->
      list_pred (fun p c => P1 (fst p) c /\ P2 (snd p) c) (combine lsa lsb) lsc.
  
  induction 1; intuition; simpl in *.
  econstructor.
  inversion H1; clear H1; subst.
  econstructor.
  intuition.
    
  eauto.
  
Qed.

Theorem list_pred_combine_l : 
  forall (A B C : Set)P1 P2 (lsa : list A)(lsb : list B)(lsc : list C),
    list_pred P1 lsa lsc -> 
    list_pred P2 lsb lsc ->
    list_pred (fun p c => P1 (fst p) c /\ P2 (snd p) c) (combine lsa lsb) lsc.
  
  intuition.
  eapply list_pred_combine_l_h; eauto.
  
Qed.

Lemma list_pred_symm : 
  forall (A B : Set)(P : A -> B -> Prop) lsa lsb,
    list_pred (fun b a => P a b) lsb lsa ->
    list_pred P lsa lsb.
  
  induction lsa; inversion 1; intuition; simpl in *;
  econstructor.
  
  subst.
  trivial.
  subst.
  trivial.
  eauto.
  
Qed.

Theorem list_pred_combine_r
: forall (A B C : Set) (P1 : A -> B -> Prop) (P2 : A -> C -> Prop)
         (lsa : list A) (lsb : list B) (lsc : list C),
    list_pred P1 lsa lsb ->
    list_pred P2 lsa lsc ->
    list_pred (fun a p => P1 a (fst p) /\ P2 a (snd p))
              lsa (combine lsb lsc).
  
  intuition.
  eapply list_pred_symm.
  eapply list_pred_impl.
  eapply list_pred_combine_l.
  eapply list_pred_symm.
  eapply H.
  eapply list_pred_symm.
  eapply H0.
  intuition.
  
Qed.