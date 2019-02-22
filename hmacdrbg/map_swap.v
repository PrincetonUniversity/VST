Set Implicit Arguments.

Require Import FCF.FCF.
Require Import FCF.CompFold.
Require Import FCF.HasDups.

Section Sec. 

  Variable eta : nat.

Theorem rnd_swap : forall a b,
  comp_spec (fun x y=> (x = y /\ x <> a /\ x <> b) \/ (a = x /\ b = y) \/ (b = x /\ a = y))
            ({0,1}^eta) ({0,1}^eta).

  intuition.
  eapply comp_spec_consequence.
  eapply (comp_spec_iso 
            (fun x => if (eqb a x) then b else if (eqb b x) then a else x)
            (fun x => if (eqb a x) then b else if (eqb b x) then a else x) 
); intuition.
  
  (* forward direction *)
  -
  case_eq (eqb a x); intuition.
  rewrite eqb_leibniz in H0; subst.

  case_eq (eqb x b); intuition.
  rewrite eqb_leibniz in H0; intuition.
  rewrite eqb_refl.
  trivial.
  case_eq (b ?= x); intuition.
  rewrite eqb_leibniz in H1.
  subst.
  rewrite eqb_refl.
  trivial.
 
  rewrite H1.
  rewrite H0.
  trivial.
  
  (* backward direction *)
  -
  case_eq (eqb a x); intuition.
  rewrite eqb_leibniz in H0. subst.
  case_eq (eqb x b); intuition.
  rewrite eqb_leibniz in H0.
  intuition.
  rewrite eqb_refl.
  intuition.

  case_eq (eqb b x); intuition.
  rewrite eqb_leibniz in H1.
  subst.
  rewrite eqb_refl.
  trivial.
  rewrite H1.
  rewrite H0.
  trivial.

  (* range of function is correct *)
  -
  simpl.
  apply in_getAllBvectors.

  (* probability is unchanged---follows form uniformity *)
  -
  eapply comp_spec_rnd.

  - (*result is correct after isomorphism *)
  intuition.
  case_eq (a ?= a0); intuition;
  rewrite H0 in H.
  rewrite eqb_leibniz in H0.
  intuition.

  case_eq (b ?= a0); intuition;
  rewrite H1 in H.
  rewrite eqb_leibniz in H1.
  intuition. 

  left.
  intuition; subst.
  subst.
  rewrite eqb_refl in H0.
  discriminate.
  subst.
  rewrite eqb_refl in H1.
  discriminate.
Qed.


Definition to_list (A : Type) (n : nat) (v : Vector.t A n) := Vector.to_list v.

Theorem list_pred_swap_In_eq_ex :
  forall (A : Set)(a b : A) ls1 ls2,
  list_pred
         (fun x y  =>
          (x = y /\ x <> a /\ x <> b) \/ a = x /\ b = y \/ b = x /\ a = y) ls1 ls2 ->
    (In a ls1 <-> In b ls2).

  induction 1; intuition; simpl in *; subst; intuition.
  

Qed.

Theorem list_pred_swap_In_eq :
  forall (A : Set)(a b : A) ls1 ls2,
  list_pred
         (fun x y  =>
          (x = y /\ x <> a /\ x <> b) \/ a = x /\ b = y \/ b = x /\ a = y) ls1 ls2 ->
  forall z,
    z <> a -> z <> b -> (In z ls1 <-> In z ls2).

  induction 1; intuition; simpl in *; intuition; subst; intuition.
  
  right.
  eapply IHlist_pred; intuition.
  right.
  eapply IHlist_pred; intuition.
  right.
  eapply IHlist_pred; intuition.
  right.
  eapply IHlist_pred; intuition.
  right.
  eapply IHlist_pred; intuition.  
  right.
  eapply IHlist_pred; intuition.
  

Qed.

Theorem list_pred_swap_hasDups_eq :
  forall (A : Set)(eqda : EqDec A)(a b : A) ls1 ls2,
  list_pred
         (fun x y  =>
          (x = y /\ x <> a /\ x <> b) \/ a = x /\ b = y \/ b = x /\ a = y) ls1 ls2 ->
  hasDups _ ls1 = hasDups _ ls2.

  induction 1; intuition ; simpl in *; subst.

  destruct (in_dec (EqDec_dec eqda) a2 ls1).
  destruct (in_dec (EqDec_dec eqda) a2 ls2). trivial.
  exfalso. eapply n.
  eapply (@list_pred_swap_In_eq _ a b).
  eapply list_pred_symm.
  eapply list_pred_impl.
  eapply H0. intuition. intuition; subst; intuition.
  intuition. intuition. intuition.

  destruct ( in_dec (EqDec_dec eqda) a2 ls2).
  exfalso.
  apply n.
  eapply (@list_pred_swap_In_eq _ a b).
  eapply H0. intuition. intuition; subst; intuition.
  intuition. 
  trivial.

  destruct (in_dec (EqDec_dec eqda) a1 ls1);
  destruct ( in_dec (EqDec_dec eqda) a2 ls2); trivial.
  exfalso.
  apply n.
  eapply (@list_pred_swap_In_eq_ex _ a1 a2).
  eauto.
  trivial.

  exfalso.
  eapply n.
  eapply (@list_pred_swap_In_eq_ex _ a1 a2).
  eauto.
  trivial.
  
  destruct (in_dec (EqDec_dec eqda) a1 ls1); destruct (in_dec (EqDec_dec eqda) a2 ls2); trivial; exfalso.
  apply n.
  eapply (@list_pred_swap_In_eq_ex _ a1 a2).
  eapply list_pred_impl.
  apply H0.
  intuition. intuition. trivial.

  apply n.
  eapply (@list_pred_swap_In_eq_ex _ a1 a2).
  eapply list_pred_impl.
  apply H0.
  intuition. intuition. trivial.
Qed.


Lemma compMap_v_eq_init_list_h : forall (a b : Bvector eta)  (init : list (list bool)) blocks,
     list_pred
     (fun x y : list bool =>
      x = y /\ x <> to_list a /\ x <> to_list b \/
      to_list a = x /\ to_list b = y \/ to_list b = x /\ to_list a = y)
     init init ->
   (In (to_list a) init <-> In (to_list b) init) ->
   comp_spec eq 
     (x <-$
      compMap _ (fun _ : nat => { 0 , 1 }^eta)
        (forNats blocks);
      ret hasDups _
            (((to_list a) :: (map (@to_list _ eta) x)) ++ init))
     (x <-$
      compMap _ (fun _ : nat => { 0 , 1 }^eta)
        (forNats blocks);
      ret hasDups _
            (((to_list b) :: (map (@to_list _ eta) x)) ++ init)).

  intuition.
  Unset Printing Notations.
  (* simpl. *)
  simpl in H.
  (* list_pred is like Forall but with a predicate P that relates each pair of two elements in two lists *)
  (* do we need to assume H on init init? can i prove it? *)
  (* list_pred holds on nil nil by definition, so i think i'm okay *)
  (* is the theorem in the correct form (or can it be used to prove the one in the correct form)? seems slightly different *)
  (* generate x; ret has_dups eqdbl (map to_list (b :: x) ++ map fst init *)
  (* just need to deal with the different type of init but i should be able to do it by applying this theorem inside the one i need *)

  eapply comp_spec_seq; eauto with inhabited.
  eapply compMap_spec.
  eapply list_pred_eq.
  intros.
  eapply (rnd_swap a b).
  intuition.

  eapply comp_spec_ret; intuition.
  eapply (@list_pred_swap_hasDups_eq _ _ (to_list a) (to_list b)).
  econstructor. intuition.
  apply list_pred_app_both.
  eapply list_pred_impl.
  eapply list_pred_map_both.
  eauto.
  intuition.
  destruct H5. destruct H5.
  intuition; subst;
  eauto using to_list_eq_inv.
  left; intuition; eauto using to_list_eq_inv.

  trivial.
Qed.

End Sec.