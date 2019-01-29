(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* A general purpose array indexed by an arbitrary type *)

Set Implicit Arguments.
Require Import FCF.Crypto.
Require Import FCF.Fold.

Local Open Scope list_scope.

Section ListArray.

  Variable D R : Set.
  Hypothesis D_EqDec : EqDec D.

  Definition Array := list (D * R).

  Fixpoint arrayLookup(ls : list (D * R)) d :=
    match ls with
      | nil => None
      | (d', r') :: ls' =>
        if (eqb d d') 
          then Some r' 
          else (arrayLookup ls' d)
    end.

  Definition arrayEquiv(arr1 arr2 : Array) :=
    forall d, 
      (arrayLookup arr1 d) = (arrayLookup arr2 d).

  Definition arrayLookupDef(ls : list (D * R)) d def :=
    match arrayLookup ls d with
        | None => def
        | Some r => r
    end.

  Definition arrayUpdate (arr_opt : option Array) d r_opt :=
    let arr := match arr_opt with
                 | None => nil
                 | Some arr => arr
               end in
    match r_opt with
        | None => arr
        | Some r =>
          (d, r) :: arr
    end.
 
  Lemma arrayLookup_app_some_eq : forall ls d v,
    arrayLookup ls d = None ->
    arrayLookup (ls ++ (d, v) :: nil) d = Some v.
    
    induction ls; intuition; simpl in *.
    rewrite eqb_refl.
    trivial.
    
    case_eq (eqb d a0); intuition;
      rewrite H0 in H.
    discriminate.
    eauto.
    
  Qed.

  Lemma arrayLookup_app_none : forall ls d d' v',
    arrayLookup ls d = None ->
    arrayLookup (ls ++ (d, v') :: nil) d' = arrayLookup ((d, v') :: ls) d'.

    induction ls; intuition; simpl in *.

    case_eq (eqb d a0); intuition;
    rewrite H0 in H.
    discriminate.
    case_eq (eqb d' d); intuition.
    rewrite eqb_leibniz in H1.
    subst.
    case_eq (eqb d a0); intuition.
    rewrite eqb_leibniz in H1.
    subst.
    rewrite eqb_refl in H0.
    discriminate.
    
    eapply arrayLookup_app_some_eq.
    trivial.

    specialize (IHls d d').
    case_eq (eqb d' a0); intuition.
    rewrite H1 in IHls.
    eapply IHls.
    trivial.

  Qed.

  
  Lemma arrayLookup_app_ne : forall ls d r d',
    d <> d' ->
    arrayLookup (ls ++ (d, r) :: nil) d' = arrayLookup ls d'.
    
    induction ls; intuition; simpl in *.
    case_eq (eqb d' d); intuition.
    rewrite eqb_leibniz in H0.
    subst.
    intuition.
    
    case_eq (eqb d' a0); intuition.
    
  Qed.
  
  Lemma arrayLookup_app_some : forall ls d d' v v',
    arrayLookup ls d = Some v ->
    arrayLookup (ls ++ (d, v') :: nil) d' = arrayLookup ls d'.

    induction ls; intuition; simpl in *.
    discriminate.

    case_eq (eqb d a0); intuition.
    rewrite H0 in H.
    inversion H; clear H; subst.
    rewrite eqb_leibniz in H0. subst.
    case_eq (eqb d' a0); intuition.

    eapply arrayLookup_app_ne.
    intuition.
    subst.
    rewrite eqb_refl in H.
    discriminate.
    rewrite H0 in H.

    case_eq (eqb d' a0); intuition.
    eapply IHls; eauto.
  Qed.

  Theorem arrayLookup_arrayUpdate_eq : 
    forall arr p v,
      arrayLookup (arrayUpdate arr p (Some v)) p = (Some v).


    intuition.
    unfold arrayUpdate.
    destruct arr.
    simpl.
    rewrite eqb_refl.
    trivial.

    simpl.
    rewrite eqb_refl.
    trivial.
  Qed.

   Theorem arrayLookup_arrayUpdate_ne : 
    forall arr p1 p2 v,
      p1 <> p2 ->
      arrayLookup (arrayUpdate (Some arr) p1 (Some v)) p2 = arrayLookup arr p2.


    intuition.
    unfold arrayUpdate.
    simpl.
    case_eq (eqb p2 p1); intuition.
    rewrite eqb_leibniz in H0.
    subst.
    intuition.
  Qed.

   Theorem arrayLookup_arrayUpdate_None_ne : 
     forall p1 p2 v,
       p1 <> p2 ->
       arrayLookup (arrayUpdate None p1 (Some v)) p2 = None.

     intuition.
     unfold arrayUpdate.
     simpl.
     case_eq (eqb p2 p1); intuition.
     rewrite eqb_leibniz in H0.
     subst.
     intuition.
  Qed.

End ListArray.

(* Some notation for array lookups *)
Notation "f '#' i " := (arrayLookup _ f i) (at level 70) : array_scope.

Local Open Scope array_scope.

(* A special case for array lookup when the range is lists -- returns nil instead of None when not found.  This is useful for multidimensional arrays. *)
Definition arrayLookupList(A B : Set)(eqd : EqDec A)(ls : list (A * (list B)))(a : A) :=
    match (arrayLookup _ ls a) with
      | None => nil
      | Some ls => ls
    end.

Require Import FCF.CompFold.

Lemma arrayLookup_Some_In_unzip : 
  forall (A B : Set)(eqd : EqDec A)(arr : Array A B) a b,
    (arr # a) = Some b ->
    In a (fst (unzip arr)).
  
  induction arr; intuition; simpl in *.
  discriminate.
  
  case_eq (eqb a a0); intuition;
  rewrite H0 in *.
  inversion H; clear H; subst.
  rewrite eqb_leibniz in H0.
  subst.
  intuition.
  right.
  eapply IHarr.
  eauto.
  
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

Fixpoint arrayLookupOpt(A B : Set)(eqd : EqDec A)(ls : list (option (A * B)))(a : A) :=
  match ls with
    | nil => None
      | o :: ls' =>
        match o with
          | None => arrayLookupOpt _ ls' a
          | Some (a', b') =>
            if (eqb a a') then (Some b') else (arrayLookupOpt _ ls' a)
        end
  end.

Theorem list_pred_arrayLookupOpt : 
  forall (A B C : Set)(P : B -> C -> Prop)(eqda : EqDec A)(ls1 : list (option (A * B)))(ls2 : list (option (A * C))),
    list_pred (fun o1 o2 =>
                 match o1 with
                   | None => o2 = None
                   | Some x =>
                     match o2 with
                       | None => False
                       | Some y =>
                         fst x = fst y /\ P (snd x) (snd y)
                     end
                 end) ls1 ls2 ->
    forall a, 
      match (arrayLookupOpt _ ls1 a) with
        | None => (arrayLookupOpt _ ls2 a) = None
        | Some x => exists y, (arrayLookupOpt _ ls2 a) = Some y /\ P x y
      end.
  
  induction 1; intuition; simpl in *.
  trivial.
  
  destruct a1.
  destruct a2.
  destruct p.
  simpl in *.
  intuition.
  subst.
  destruct p0. simpl in *.
  case_eq (eqb a a0); intuition.
  econstructor.
  intuition.
  eapply IHlist_pred.
  destruct p.
  case_eq (eqb a a0); intuition.
  
  subst.
  eapply IHlist_pred.
  
Qed.

Theorem arrayLookupOpt_getSomes_eq : 
  forall (A B : Set)(eqda : EqDec A)(ls : list (option (A * B)))(a : A),
       arrayLookupOpt _ ls a = arrayLookup _ (getSomes ls) a.
  
  induction ls; intuition; simpl in *.
  destruct a.
  destruct p.
  simpl.
  case_eq (eqb a0 a); intuition.
  
  eapply IHls.
  
Qed.

Theorem arrayLookup_app_Some : 
  forall (A B : Set)(eqd : EqDec A)(ls1 ls2 : list (A * B))(a : A)(b : B),
    arrayLookup eqd ls1 a = Some b ->
    arrayLookup eqd (ls1 ++ ls2) a = Some b.
  
  induction ls1; intuition; simpl in *.
  discriminate.
  
  case_eq (eqb a a0); intuition.
  rewrite H0 in H.
  trivial.
  
  rewrite H0 in H.
  eauto.

Qed.

Theorem arrayLookup_app_None : 
  forall (A B : Set)(eqd : EqDec A)(ls1 ls2 : list (A * B))(a : A),
    arrayLookup eqd ls1 a = None ->
    arrayLookup eqd (ls1 ++ ls2) a =
    arrayLookup eqd ls2 a.
  
  induction ls1; intuition; simpl in *.
  case_eq (eqb a a0); intuition;
  rewrite H0 in H.
  discriminate.
  
  eauto.
  
Qed.

Theorem arrayLookupList_pred : 
  forall (A B : Set) (eqda : EqDec A)P (ls : list (A * list B)) a,
    (forall x, In x ls -> P (snd x)) ->
    P nil ->
    P (arrayLookupList _ ls a).
  
  induction ls; intuition; simpl in *.
  unfold arrayLookupList.
  simpl.
  case_eq (eqb a a0); intuition.
  specialize (X (a0, b)).
  intuition.
  
  eapply IHls; intuition.
  
Qed.

Theorem arrayLookup_Some_impl_In : 
  forall (A B : Set)(eqd : EqDec A)(ls : list (A * B)) a b,
    arrayLookup _ ls a = Some b ->
    In (a, b) ls.
  
  induction ls; intuition; simpl in *.
  discriminate.
  case_eq (eqb a a0); intuition;
  rewrite H0 in H.
  inversion H; clear H; subst.
  rewrite eqb_leibniz in H0.
  subst.
  intuition.

  right.
  eauto.
Qed.

Theorem list_pred_impl_arrayLookup : 
  forall (A B C : Set) P (eqda : EqDec A)(ls1 : list (A * B))(ls2 : list (A * C)),
    list_pred (fun x y => fst x = fst y /\ P (snd x) (snd y)) ls1 ls2 ->
    (forall v z, arrayLookup _ ls1 v = Some z -> exists z', arrayLookup _ ls2 v = Some z' /\ P z z') /\
    (forall v, arrayLookup _ ls1 v = None -> arrayLookup _ ls2 v = None).
  
  induction 1; intros; simpl in *.
  
  intuition.
  discriminate.
  
  destruct a1.
  destruct a2.
  destruct H.
  simpl in *.
  subst.
  
  intuition.
  
  case_eq (eqb v a0); intuition.
  rewrite H4 in H3.
  inversion H3; clear H3; subst.
  econstructor; eauto.
  rewrite H4 in H3.
  edestruct H.
  eauto.
  intuition.
  
  case_eq (eqb v a0); intuition.
  rewrite H4 in H3.
  discriminate.
  rewrite H4 in H3.
  eauto.
  
Qed.

Theorem arrayLookup_In_NoDup : 
  forall (A B : Set)(eqda : EqDec A)(ls : list (A * B)) a b,
    In (a, b) ls ->
    NoDup (fst (split ls)) ->
    arrayLookup _ ls a = Some b.
  
  induction ls; intuition; simpl in *.
  intuition.
  
  remember (split ls) as z.
  destruct z.
  intuition.
  pairInv.      
  simpl in *.
  inversion H0; clear H0; subst.
  rewrite eqb_refl.
  trivial.
  
  simpl in *.
  inversion H0; clear H0; subst.
  case_eq (eqb a a0); intuition.
  rewrite eqb_leibniz in H.
  subst.
  eapply in_split_l in H1.
  rewrite <- Heqz in H1.
  simpl in *.
  intuition.
  
Qed.

Theorem arrayLookup_None_not_In : 
  forall (A B : Set)(eqda : EqDec A)(ls : list (A * B)) a,
    arrayLookup _ ls a = None ->
    In a (fst (split ls)) -> False.
  
  induction ls; intuition; simpl in *.
  remember (split ls) as z.
  destruct z.
  simpl in *.
  intuition; subst.
  rewrite eqb_refl in H.
  discriminate.
  destruct (eqb a a0).
  discriminate.
  eauto.
Qed.

Theorem arrayLookup_pair_None : 
  forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B) (ls : list (A * B * C)) a b,
    (forall x, In x ls -> fst (fst x) <> a) ->
    arrayLookup _ ls (a, b) = None.
  
  induction ls; intuition; simpl in *.
  case_eq (eqbPair eqda eqdb (a0, b1) (a, b0)); intuition.
  exfalso.
  unfold eqbPair in *.
  simpl in *.
  apply andb_true_iff in H0.
  intuition.
  rewrite eqb_leibniz in H1.
  subst.
  eapply H.
  left.
  reflexivity.
  trivial.
  eauto.
  
Qed.

Theorem arrayLookup_pair_flatten_none : 
  forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B) keys (ls : list (list (A * B * C))) a b,
    list_pred (fun a b => forall x, In x b -> fst (fst x) = a) keys ls ->
    (~ In a keys) ->
    arrayLookup (pair_EqDec eqda eqdb) (flatten ls) (a, b) = None.
  
  induction keys; intuition; simpl in *.
  inversion H; clear H; subst.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  intuition.
  simpl.
  
  case_eq (arrayLookup (pair_EqDec eqda eqdb) a2 (a0, b)); intuition.
  rewrite  arrayLookup_pair_None in H0.
  discriminate.
  intuition.
  subst.
  eapply H.
  symmetry.
  eapply H3.
  trivial.
  
  rewrite arrayLookup_app_None; trivial.
  eauto.
  
Qed.

Theorem arrayLookup_flatten_eq :
  forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls : list (list (A * B * C))) keys a b,
    list_pred (fun a b => forall x, In x b -> fst (fst x) = a) keys ls ->
    NoDup keys ->
    arrayLookup _ (flatten ls) (a, b) = 
    arrayLookup _ (arrayLookupList _ (combine keys ls) a) (a, b).
  
  induction ls; intuition; simpl in *.
  inversion H; clear H; subst.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  simpl.
  unfold arrayLookupList.
  simpl.
  inversion H0; clear H0; subst.
  case_eq (eqb a0 a1); intuition.
  
  case_eq (arrayLookup (pair_EqDec eqda eqdb) a (a0, b)); intuition.
  eapply arrayLookup_app_Some.
  trivial.
  
  rewrite eqb_leibniz in H.
  subst.
  
  rewrite arrayLookup_app_None; intuition.
             
  eapply arrayLookup_pair_flatten_none.
  eauto.
  intuition.
  
  case_eq ( arrayLookup _ a (a0, b) ); intuition.
  rewrite  arrayLookup_pair_None in H0.
  discriminate.
  intuition.
  subst.
  eapply eqb_false_iff in H.
  intuition.
  rewrite arrayLookup_app_None.
  eapply IHls; intuition.
  trivial.
Qed.


Theorem arrayLookup_pair_snd : 
  forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls1 : list (A * B * C))(ls2 : list (B * C)) a b,
    list_pred (fun x y => fst (fst x) = a /\ snd (fst x) = fst y /\ snd x = snd y) ls1 ls2 ->
    arrayLookup _ ls1 (a, b) = 
    arrayLookup _ ls2 b.
  
  induction ls1; intuition; simpl in *.
  inversion H; clear H; subst.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  simpl.
  intuition.
  subst.
  simpl in *.
  subst.
  destruct a2.
  simpl in *.
  unfold eqbPair.
  simpl.
  rewrite eqb_refl.
  simpl.
  case_eq (eqb b1 b); intuition.
  
Qed.

Theorem arrayLookup_pred_2 : 
  forall (A B C: Set)(eqda : EqDec A) (P : list B -> list C -> Prop) (ls1 : list (A * list B))(ls2 : list (A * list C)) a,
    list_pred (fun x y => (fst x = a \/ fst y = a) -> (fst x = a /\ fst y = a /\ P (snd x) (snd y))) ls1 ls2 ->
    P nil nil ->
    P (arrayLookupList _ ls1 a) (arrayLookupList _ ls2 a).
  
  induction ls1; intuition; simpl in *.
  inversion H; clear H; subst.
  unfold arrayLookupList.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  unfold arrayLookupList.
  simpl.
  destruct a2.
  
  simpl in *.
  intuition.
       
  case_eq (eqb a a0); intuition.
  rewrite eqb_leibniz in H2.
  subst.
  intuition.
  subst.
  rewrite eqb_refl.
  trivial.
  
  case_eq (eqb a a1); intuition.
  rewrite eqb_leibniz in H3.
  subst.
  intuition.
  subst.
  rewrite eqb_refl in H2.
  discriminate.
  
  eapply IHls1; intuition.
Qed.

Theorem In_arrayLookupList : 
  forall (A B : Set)(eqda : EqDec A)(a : A)(b : B) ls,
    In b (arrayLookupList _ ls a) ->
    exists ls', In (a, ls') ls /\
                In b ls'.
  
  intuition.
  unfold arrayLookupList in *.
  case_eq (arrayLookup eqda ls a); intuition;
  rewrite H0 in H.
  eapply arrayLookup_Some_impl_In in H0.
  econstructor.
  split.
  eauto.
  trivial.
  
  simpl in *.
  intuition.
  
Qed.

Theorem arrayLookupList_pred'
: forall (A B : Set) (eqda : EqDec A) (P : list B -> Type)
         (ls : list (A * list B)) (a : A),
    (forall x : list B, In (a, x) ls -> P x) ->
    (arrayLookup _ ls a = None -> P nil) ->
    P (arrayLookupList eqda ls a).
  
  induction ls; intuition; simpl in *.
  unfold arrayLookupList.
  simpl.
  case_eq (eqb a a0); intuition.
  eapply X.
  rewrite eqb_leibniz in H.
  subst.
  intuition.

  case_eq (arrayLookup eqda ls a); intuition.
  specialize (IHls a).
  unfold arrayLookupList in *.
  rewrite H0 in IHls.
  eapply IHls; eauto.
  intuition.
  discriminate.
  
  rewrite H in X0.
  intuition.
Qed.
Theorem arrayLookup_allNats_eq : 
  forall (B : Set)(ls : list (nat * B)) i,
    fst (split ls) = allNatsLt (length ls) ->
    arrayLookup _ ls i =
    match nth_option ls i with
      | Some (_, v) => Some v
              | None => None
    end.
  
  induction ls using rev_ind; intuition; simpl in *.
  rewrite app_length in H.
  rewrite fst_split_app_eq in H.
  simpl in *.
  rewrite plus_comm in H.
  simpl in *.
  eapply app_inj_tail in H.
  intuition.
  subst.
  
  case_eq (nth_option ls i); intuition.
          
  erewrite nth_option_app_Some ; eauto.
  destruct p.
  
  case_eq (arrayLookup nat_EqDec ls i); intuition.
  erewrite arrayLookup_app_Some; eauto.
  rewrite IHls.
  rewrite H.
  trivial.
  trivial.
          
  eapply arrayLookup_None_not_In in H1.
  intuition.
  rewrite H0.
  eapply allNatsLt_lt_if.

  eapply nth_option_Some_lt.
  eauto.

  rewrite nth_option_app_None.
  simpl.
  case_eq (i - length ls); intuition.

  eapply nth_option_None_ge in H.
  assert (i = length ls).
  omega.
  subst.
  
  case_eq (arrayLookup _ ls (length ls)); intuition.
  exfalso.
  eapply arrayLookup_Some_impl_In in H2.
  eapply in_split_l in H2.
  simpl in *.
  rewrite H0 in H2.
  eapply allNatsLt_lt in H2.
  omega.
  rewrite arrayLookup_app_None; eauto.
  simpl.
  rewrite eqb_refl.
  trivial.
  
  case_eq (arrayLookup _ ls i); intuition.
  eapply arrayLookup_Some_impl_In in H2.
  eapply in_split_l in H2.
  simpl in *.
  rewrite H0 in H2.
  eapply allNatsLt_lt in H2.
  omega.
  
  rewrite arrayLookup_app_None; eauto.
  simpl.
  case_eq ( eqb i (length ls)); intuition.
  rewrite eqb_leibniz in H3.
  subst.
  omega.
  trivial.
  
Qed.