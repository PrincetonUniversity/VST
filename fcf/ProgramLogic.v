(* Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

Require Import fcf.Crypto.
Require Import fcf.Bernoulli.
Require Import fcf.NotationV1.

(* stuff that needs to go somewhere else *)

Theorem ratSubtract_leRat_same_r : 
  forall r1 r2 r3,
    r3 <= r1 ->
    r3 <= r2 ->
    ratSubtract r1 r3 <= ratSubtract r2 r3 ->
    r1 <= r2.
  
  intuition.
  apply (ratAdd_leRat_compat_l r3) in H1.
  assert (ratSubtract r1 r3 + r3 == r1).
  rewrite ratAdd_comm.
  eapply ratSubtract_ratAdd_inverse_2; intuition.
  rewrite <- H2.
  rewrite H1.
  rewrite ratAdd_comm.
  eapply eqRat_impl_leRat.
  apply ratSubtract_ratAdd_inverse_2; intuition.

Qed.

Theorem sumList_filter_complement : 
  forall (A : Set){eqd : EqDec A}(c : Comp A)(a : A),
    well_formed_comp c ->
    sumList (filter (fun x => negb (eqb a x)) (getSupport c)) (evalDist c) ==
    ratSubtract 1 (evalDist c a).

  intuition.
  eapply (eqRat_ratAdd_same_r (evalDist c a)).
  symmetry.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_inverse_2.
  rewrite <- (evalDist_lossless H).
  rewrite (sumList_filter_partition (eqb a)).
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat; intuition.
  destruct (eq_Rat_dec (evalDist c a) 0).
  rewrite e.
  eapply sumList_0; intuition.
  apply filter_In in H0.
  intuition.
  rewrite eqb_leibniz in H2; subst.
  trivial.

  rewrite (@sumList_exactly_one _ a); intuition.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply filter_In; intuition.
  eapply getSupport_In_evalDist; intuition.
  eapply eqb_refl.
  apply filter_In in H0; intuition.
  rewrite eqb_leibniz in H3; subst.
  intuition.
  
  eapply evalDist_le_1.
Qed.



Theorem evalDist_Repeat_0 : 
  forall (A : Set)(c : Comp A)(P : A -> bool) a,
    (forall x, In x (getSupport c) -> P x = true -> x <> a) ->
    evalDist (Repeat c P) a == 0.
  
  intuition.
  simpl.
  unfold indicator.
  case_eq (P a); intuition.
  rewrite ratMult_1_l.
  eapply ratMult_0.
  right.
  eapply getSupport_not_In_evalDist.
  intuition.
  eapply H;
    eauto.
  
  rewrite ratMult_0_l.
  eapply ratMult_0_l.
  
Qed.

Theorem evalDist_event_equiv : 
  forall (A : Set){eqd : EqDec A}(c : Comp A) a,
    evalDist c a == Pr[x <-$ c; ret (eqb a x)].

  intuition.

  destruct (in_dec (EqDec_dec _) a (getSupport c)).

  rewrite evalDist_seq_step.
  rewrite (@sumList_exactly_one _ a).
  dist_compute.
  eapply getSupport_NoDup.
  trivial.
  intuition.
  dist_compute.
  
  rewrite evalDist_seq_step.
  assert (evalDist c a == 0).
  eapply getSupport_not_In_evalDist; trivial.
  rewrite H.
  symmetry.
  eapply sumList_0.
  intuition.
  dist_compute.

Qed.

Theorem filter_ext : forall (A : Set)(ls : list A)(f1 f2 : A -> bool),
  (forall a, f1 a = f2 a) ->
  filter f1 ls = filter f2 ls.
  
  induction ls; intuition; simpl in *.
  rewrite H.
  destruct (f2 a); eauto.
  f_equal;
  eauto.
  
Qed.

(* definitions related to the program logic *)

Definition marginal_l(A B : Set){eqd : EqDec A}(c : Comp (A * B))(a : A) :=
  Pr[x <-$ c; ret eqb (fst x) a].

Definition marginal_r(A B : Set){eqd : EqDec B}(c : Comp (A * B))(b : B) :=
  Pr[x <-$ c; ret eqb (snd x) b].

Theorem in_support_marginal_l : 
  forall (A B : Set){eqd: EqDec A}(c1 : Comp (A * B))(c2 : Comp A),
    (forall a, evalDist c2 a == marginal_l c1 a) ->
    forall p,
      In p (getSupport c1) ->
      In (fst p) (getSupport c2).
  
  intuition.
  eapply getSupport_In_evalDist.
  intuition.
  rewrite H in H1.
  clear H.
  unfold marginal_l in *.
  simpl in *.
  eapply sumList_0 in H1; eauto.
  eapply ratMult_0 in H1.
  intuition.
  eapply getSupport_In_evalDist;
    eauto.
  dist_compute.    
  
Qed.

Theorem in_support_marginal_r : 
  forall (A B : Set){eqd: EqDec B}(c1 : Comp (A * B))(c2 : Comp B),
    (forall b, evalDist c2 b == marginal_r c1 b) ->
    forall p,
      In p (getSupport c1) ->
      In (snd p) (getSupport c2).
  
  intuition.
  eapply getSupport_In_evalDist.
  intuition.
  rewrite H in H1.
  clear H.
  unfold marginal_r in *.
  simpl in *.
  eapply sumList_0 in H1; eauto.
  eapply ratMult_0 in H1.
  intuition.
  eapply getSupport_In_evalDist;
    eauto.
  dist_compute.    
  
Qed.

Definition comp_spec (R1 R2 : Set)
  {eqd1 : EqDec R1}{eqd2 : EqDec R2}
  (post : R1 -> R2 -> Prop)(c1 : Comp R1)(c2 : Comp R2) :=
  exists c : Comp (R1 * R2),
    (forall r1, evalDist c1 r1 == marginal_l c r1) /\
    (forall r2, evalDist c2 r2 == marginal_r c r2) /\
    (forall p, In p (getSupport c) -> post (fst p) (snd p)).

Theorem list_choice : 
  forall (A B : Type)(eqd : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) P (ls : list A) (b : B),
    (forall a, In a ls -> exists (b : B), P a b) -> 
    exists (f : A -> B), (forall a, In a ls -> P a (f a)).

  induction ls; intuition.
  exists (fun a => b).
  intuition.
  simpl in *.
  intuition.

  edestruct (H a); intuition.
  edestruct (H0); intuition.
  exists (fun a0 => if (eqd a a0) then x else (x0 a0)).
  intuition.
  inversion H3; clear H3; subst.
  destruct (eqd a0 a0); intuition.
  destruct (eqd a a0); intuition.
  subst.
  trivial.
Qed.


Theorem comp_spec_seq : 
  forall {A B : Set} P' {C D : Set} P{eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}{eqdd : EqDec D}(c1 : Comp A)(c2 : Comp B) (c : C) (d : D)
    (f1 : A -> Comp C)(f2 : B -> Comp D),
    comp_spec P' c1 c2 ->
    (forall a b, In a (getSupport c1) -> In b (getSupport c2) -> P' a b -> comp_spec P (f1 a) (f2 b)) ->
    comp_spec P (Bind c1 f1) (Bind c2 f2).

  intuition.
  destruct H; intuition.

  assert (forall p, In p (getSupport x) -> comp_spec P (f1 (fst p)) (f2 (snd p))).
  intuition.
  eapply H0.
  eapply in_support_marginal_l; eauto.
  eapply in_support_marginal_r; eauto.
  eauto.
  clear H0.

  pose proof H2.
  apply (list_choice) in H2.
  destruct H2.
 
  exists (Bind x x0).
  intuition.

  rewrite evalDist_seq_step.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eauto.
  eapply eqRat_refl.
  unfold marginal_l.
  
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eapply evalDist_seq_step.
  eapply eqRat_refl.
  
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  symmetry.
  eapply sumList_factor_constant_r.
  rewrite sumList_comm.

  dist_inline_first.
  rewrite evalDist_seq_step.
  eapply sumList_body_eq.
  intros.

  rewrite (@sumList_exactly_one _ (fst a)).

  assert (Pr  [ret eqb (fst a) (fst a) ]  == 1).
  dist_compute.
  rewrite H5.
  rewrite ratMult_1_r.
  eapply ratMult_eqRat_compat; intuition.
  specialize (H2 a).
  intuition.
  rewrite H2.
  
  unfold marginal_l.
  intuition.

  eapply getSupport_NoDup.

  eapply in_support_marginal_l; eauto.
  
  intuition.
  dist_compute.

  rewrite evalDist_seq_step.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eauto.
  eapply eqRat_refl.
  unfold marginal_r.
  
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eapply evalDist_seq_step.
  eapply eqRat_refl.
  
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  symmetry.
  eapply sumList_factor_constant_r.
  rewrite sumList_comm.

  dist_inline_first.
  rewrite evalDist_seq_step.
  eapply sumList_body_eq.
  intros.

  rewrite (@sumList_exactly_one _ (snd a)).
  assert (Pr  [ret eqb (snd a) (snd a) ] == 1).
  dist_compute.
  rewrite H5.
  rewrite ratMult_1_r.
  eapply ratMult_eqRat_compat; intuition.
  specialize (H2 a); intuition.
  rewrite H6.
  unfold marginal_r; intuition.

  eapply getSupport_NoDup.
  eapply in_support_marginal_r; eauto.

  intuition.
  dist_compute.

  simp_in_support.
  specialize (H2 x1); intuition.

  unfold eq_dec; intuition.
  eapply (EqDec_dec _).
  eapply (ret (c, d)).

Qed.


Ltac despec := 
  match goal with
    | [H : comp_spec _ _ _  |- _] => destruct H
  end.

Theorem comp_spec_consequence : 
  forall (A B : Set){eqda1 eqda2 : EqDec A}{eqdb1 eqdb2 : EqDec B}(p1 p2 : A -> B -> Prop) c1 c2,
    (@comp_spec _ _ eqda1 eqdb1 p1 c1 c2) ->
    (forall a b, p1 a b -> p2 a b) ->
    (@comp_spec  _ _ eqda2 eqdb2 p2 c1 c2).

  intuition.
  despec; intuition.
  exists x; intuition.

  rewrite H1.
  unfold marginal_l.
 
  dist_skip.
  eapply evalDist_ret_eq.
  case_eq (eqb (fst x0) r1); intuition.
  rewrite eqb_leibniz in H4.
  subst.
  eapply eqb_refl.

  case_eq ( (@eqb A eqda1 (@fst A B x0) r1)); intuition.
  rewrite eqb_leibniz in H5.
  subst.
  rewrite eqb_refl in H4.
  intuition.

  rewrite H.
  unfold marginal_r.
 
  dist_skip.
  eapply evalDist_ret_eq.
  case_eq (eqb (snd x0) r2); intuition.
  rewrite eqb_leibniz in H4.
  subst.
  eapply eqb_refl.

  case_eq ( (@eqb B eqdb1 (@snd A B x0) r2)); intuition.
  rewrite eqb_leibniz in H5.
  subst.
  rewrite eqb_refl in H4.
  intuition.

Qed.

Theorem comp_spec_symm : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(p : A -> B -> Prop) c1 c2,
    comp_spec p c1 c2 ->
    comp_spec (fun b a => p a b) c2 c1.

  intuition.
  despec; intuition.
  exists (p <-$ x; ret (snd p, fst p)).
  intuition.
  eapply eqRat_trans; eauto.
  unfold marginal_r, marginal_l.
  dist_inline_first.
  dist_skip.
  dist_compute.

  eapply eqRat_trans; eauto.
  unfold marginal_r, marginal_l.
  dist_inline_first.
  dist_skip.
  dist_compute.
 
  repeat simp_in_support.
  simpl.
  eauto.
Qed.

(* completeness theorems *)
Theorem eq_impl_comp_spec : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : Comp A)(c2 : Comp B) x y,
    well_formed_comp c1 ->
    well_formed_comp c2 ->
    evalDist c1 x == evalDist c2 y ->
    comp_spec (fun a b => a = x <-> b = y) c1 c2.

  intuition.
  
  (* special case: the events have probability 0 *)
  destruct (eq_Rat_dec (evalDist c1 x) 0).

  exists (a <-$ c1;
    b <-$ c2;
    ret (a, b)).
  intuition.
  unfold marginal_l.
  dist_inline_first.
  rewrite <- evalDist_right_ident.

  dist_skip.
  dist_inline_first.
  dist_irr_r.
  dist_compute.

  unfold marginal_r.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_irr_r.
  dist_inline_first.
  dist_skip.
  dist_compute.

  repeat simp_in_support.
  simpl in *.
  exfalso.
  eapply getSupport_not_In_evalDist.
  eapply e.
  trivial.
  repeat simp_in_support.
  simpl in *.
  exfalso.
  eapply getSupport_not_In_evalDist.
  rewrite <- H1.
  trivial.
  trivial.

  (* special case: the events have probability 1 *)
  destruct (eq_Rat_dec (evalDist c1 x) 1).
  exists (a <-$ c1;
    b <-$ c2;
    ret (a, b)).

  split.
  intuition.
  unfold marginal_l.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_inline_first.
  dist_irr_r.
  dist_compute.

  split.
  intuition.
  unfold marginal_r.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_irr_r.
  dist_inline_first.
  dist_skip.
  dist_compute.

  intros.
  repeat simp_in_support; simpl in *.
  erewrite (evalDist_1) in H5; intuition.
  2:{
    rewrite <- H1.
    trivial.
  }
  simpl in *; intuition.

  erewrite (evalDist_1) in H3; eauto.
  simpl in *; intuition.
  
  (* general case *)

  exists (a <-$ c1;
    b <-$ if (eqb a x) then (ret y) else (Repeat c2 (fun b => negb (eqb b y)));
      ret (a, b)).

  split.  
  intuition.
  unfold marginal_l.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_inline_first.
  dist_irr_r.

  case_eq (eqb x0 x); intuition; wftac.
  remember (getSupport c2) as s.
  destruct s.
  specialize (getSupport_length_nz H0); intuition.
  rewrite <- Heqs in H4.
  simpl in *.
  omega.
  destruct (EqDec_dec _ b y); subst.
  destruct s.
  exfalso.
  eapply n0.
  rewrite H1.
  rewrite <- (evalDist_lossless H0).
  rewrite <- Heqs.
  rewrite sumList_cons.
  unfold sumList; simpl.
  eapply ratAdd_0_r.
  eapply (@well_formed_Repeat _ _ _ _ b).
  trivial.
  eapply filter_In; intuition.
  rewrite <- Heqs.
  simpl.
  intuition.
  case_eq (eqb b y); intuition.
  rewrite eqb_leibniz in H4.
  subst.
  specialize (getSupport_NoDup c2); intuition.
  rewrite <- Heqs in H4.
  inversion H4; clear H4; subst.
  simpl in *.
  intuition.

  eapply (@well_formed_Repeat _ _ _ _ b).
  trivial.
  eapply filter_In; intuition.
  rewrite <- Heqs; simpl; intuition.
  case_eq (eqb b y); intuition.
  rewrite eqb_leibniz in H4; subst.
  intuition.

  dist_compute.
  
  split.
  intuition.
  unfold marginal_r.
  dist_inline_first.
  rewrite evalDist_seq_step.
  rewrite (sumList_filter_partition (eqb x)).
  symmetry.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  apply filter_In in H2.
  intuition.
  rewrite eqb_leibniz in H4.
  subst.
  rewrite eqb_refl.
  dist_inline_l.
  simpl snd.
  eapply eqRat_refl.
  
  eapply sumList_body_eq; intuition.
  apply filter_In in H2.
  intuition.
  case_eq (eqb x a); intuition.
  rewrite eqb_leibniz in H2.
  subst.
  rewrite eqb_refl in H4.
  simpl in *.
  discriminate.

  rewrite evalDist_assoc at 1.
  case_eq (eqb a x); intuition.
  rewrite eqb_leibniz in H5.
  subst.
  rewrite eqb_refl in H2.
  discriminate.
  
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply evalDist_seq_eq.
  intuition.
  eapply eqRat_refl.
  intuition.
  dist_simp.
  unfold snd.
  eapply eqRat_refl.
  intuition.
  rewrite (@sumList_exactly_one _ x).
  case_eq (eqb y r2); intuition.
  rewrite eqb_leibniz in H2.
  subst.
  assert (Pr[ret true] == 1).
  dist_compute.
  rewrite H2.
  rewrite ratMult_1_r.
  clear H2.
  rewrite H1.
  symmetry.
  rewrite ratAdd_0_r at 1.
  eapply ratAdd_eqRat_compat; intuition.
  symmetry.
  eapply sumList_0.
  intuition.
  apply filter_In in H2.
  intuition.
  assert (Pr  [x0 <-$ Repeat c2 (fun b : B => negb (eqb b r2)); ret eqb x0 r2 ] ==
    Pr  [x0 <-$ Repeat c2 (fun b : B => negb (eqb b r2)); ret eqb r2 x0 ] ).
  dist_skip; dist_compute.
  rewrite H2.
  clear H2.
  rewrite <- evalDist_event_equiv.
  eapply ratMult_0.
  right.
  eapply evalDist_Repeat_0; intuition.
  subst.
  rewrite eqb_refl in H5.
  simpl in *; discriminate.
  
  assert (Pr [ret false] == 0).
  dist_compute.
  rewrite H3.
  clear H3.
  rewrite ratMult_0_r.
  rewrite <- ratAdd_0_l.
  rewrite sumList_factor_constant_r.
  rewrite sumList_filter_complement.
  rewrite H1.
  rewrite evalDist_seq_step.

  destruct (in_dec (EqDec_dec _) r2 (getSupport c2)).

  rewrite (@sumList_exactly_one _ r2).
  assert (Pr  [ret eqb r2 r2 ] == 1).
  dist_compute.
  rewrite H3.
  clear H3.
  rewrite ratMult_1_r.
  simpl.
  unfold indicator.
  case_eq (eqb r2 y); intuition.
  rewrite eqb_leibniz in H3; subst.
  rewrite eqb_refl in H2.
  discriminate.
  simpl.
  rewrite ratMult_1_l.
  symmetry.
  rewrite <- ratMult_1_l at 1.
  rewrite <- ratMult_assoc.
  eapply ratMult_eqRat_compat; intuition.
  symmetry.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply ratInverse_eqRat_compat.
  intuition.

  assert ( (filter (fun b : B => negb (eqb b y)) (getSupport c2)) = 
     (filter (fun b : B => negb (eqb y b)) (getSupport c2))).
  eapply filter_ext; intuition.
  rewrite eqb_symm.
  trivial.
  rewrite H5 in H4.
  clear H5.
  eapply n0.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  eapply ratSubtract_0_inv.
  rewrite sumList_filter_complement in H4.
  rewrite H1.
  intuition.
  trivial.

  assert ((filter (fun b : B => negb (eqb b y)) (getSupport c2)) = 
    (filter (fun b : B => negb (eqb y b)) (getSupport c2))).
  eapply filter_ext.
  intuition.
  rewrite eqb_symm.
  intuition.
  rewrite H4.
  clear H4.
  
  eapply sumList_filter_complement.
  trivial.

  rewrite ratMult_comm.
  eapply ratInverse_prod_1.
  intuition.
  eapply n0.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  eapply ratSubtract_0_inv.
  rewrite H1.
  intuition.
  
  eapply getSupport_NoDup.
  simpl.
  eapply filter_In; intuition.
  rewrite eqb_symm.
  rewrite H2.
  trivial.

  intuition.
  dist_compute.

  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply sumList_0.
  intuition.
  simpl in H3.
  apply filter_In in H3.
  intuition.
  case_eq (eqb a r2); intuition.
  rewrite eqb_leibniz in H3; subst.
  intuition.
  dist_compute.

  rewrite ratMult_0_r.
  symmetry.
  eapply getSupport_not_In_evalDist.
  trivial.

  trivial.

  eapply filter_NoDup.
  eapply getSupport_NoDup.
  
  eapply filter_In; intuition.
  eapply getSupport_In_evalDist; intuition.

  eapply eqb_refl.

  intuition.
  apply filter_In in H2.
  intuition.
  rewrite eqb_leibniz in H5.
  intuition.
  
  intros.
  repeat simp_in_support;
  simpl in *; intuition.
  rewrite eqb_refl in Heqx2.
  discriminate.

  symmetry in Heqx2.
  rewrite eqb_leibniz in Heqx2.
  trivial.

  simpl in *.
  eapply filter_In in H5.
  intuition.
  rewrite eqb_refl in H4.
  simpl in *.
  discriminate.

  Grab Existential Variables. 
  unfold eq_dec; intuition.
  eapply (EqDec_dec _).
  unfold eq_dec; intuition.
  eapply (EqDec_dec _).

  intuition.
  intuition.
  intuition.
  intuition.
  intuition.

Qed.


Theorem le_impl_comp_spec : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : Comp A)(c2 : Comp B),
    well_formed_comp c1 ->
    well_formed_comp c2 ->
    forall x y, 
      evalDist c1 x <= evalDist c2 y ->
      comp_spec (fun a b => a = x -> b = y) c1 c2.

  intuition.


  (* special case : y is a certain output of c2 *)
  destruct (eq_Rat_dec (evalDist c2 y) 1).
  exists (a <-$ c1; b <-$ c2; ret (a, b)).
  intuition.
  unfold marginal_l; intuition.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_inline_first.
  dist_irr_r.
  dist_compute.
  
  unfold marginal_l; intuition.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_irr_r.
  dist_inline_first.
  dist_skip.
  dist_compute.

  repeat simp_in_support.
  simpl in *.
  erewrite evalDist_1 in H5; eauto.
  simpl in *.
  intuition.

  (* special case : x is never an output of c1 *)
  destruct (eq_Rat_dec (evalDist c1 x) 0).
  exists (a <-$ c1; b <-$ c2; ret (a, b)).
  intuition.
  unfold marginal_l; intuition.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_inline_first.
  dist_irr_r.
  dist_compute.
  
  unfold marginal_l; intuition.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_irr_r.
  dist_inline_first.
  dist_skip.
  dist_compute.
  
  repeat simp_in_support.
  simpl in *.
  exfalso.
  eapply getSupport_In_evalDist.
  eapply H4.
  trivial.

  (* special case: the probabilities are equal *)
  destruct (eq_Rat_dec (evalDist c1 x) (evalDist c2 y)).
  eapply comp_spec_consequence.
  eapply eq_impl_comp_spec; intuition.
  eauto.
  intuition.
  subst.
  intuition.

  (* general case *)

  Local Open Scope rat_scope.

  exists (a <-$ c1;
    b <-$ if (eqb a x) then (ret y) else
      mDiff <- (ratSubtract (evalDist c2 y) (evalDist c1 x));
      c <-$ Bernoulli (mDiff * (ratInverse (ratSubtract 1 (evalDist c1 x))));
      if c then (ret y) else (Repeat c2 (fun z => negb (eqb z y)));
        ret (a, b)).

  intuition.
  unfold marginal_l.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_inline_first.
  dist_irr_r.

  remember (getSupport c2) as s.
  destruct s.
  exfalso.
  specialize (getSupport_length_nz H0); intuition.
  rewrite <- Heqs in H3.
  simpl in *.
  omega.

  destruct (EqDec_dec _ b y).
  subst.
  destruct s.
  exfalso.
  eapply n.
  rewrite <- (evalDist_lossless H0).
  rewrite <- Heqs.
  rewrite sumList_cons.
  unfold sumList. simpl.
  eapply ratAdd_0_r.

  wftac.
  eapply Bernoulli_wf.
  eapply (@well_formed_Repeat _ _ _ _ b).
  intuition.
  eapply filter_In; intuition.
  rewrite <- Heqs.
  simpl.
  intuition.
  case_eq (eqb b y); intuition.
  rewrite eqb_leibniz in H4.
  subst.
  specialize (getSupport_NoDup c2); intuition.
  rewrite <- Heqs in H4.
  inversion H4; clear H4; subst.
  simpl in *.
  intuition.

  wftac.
  eapply Bernoulli_wf.
  eapply (@well_formed_Repeat _ _ _ _ b).
  intuition.
  eapply filter_In; intuition.
  rewrite <- Heqs.
  simpl.
  intuition.
  case_eq (eqb b y); intuition.
  rewrite eqb_leibniz in H4.
  subst.
  intuition.

  dist_compute.

(*  destruct (in_dec (EqDec_dec _) r2 (getSupport c2)). *)

  symmetry.
  unfold marginal_r.
  dist_inline_first.
  rewrite evalDist_seq_step.
  rewrite (sumList_filter_partition (eqb x)).
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  apply filter_In in H2.
  intuition.
  rewrite eqb_leibniz in H4.
  subst.
  rewrite eqb_refl.
  dist_inline_l.
  simpl snd.
  eapply eqRat_refl.
  
  eapply sumList_body_eq; intuition.
  apply filter_In in H2.
  intuition.
  case_eq (eqb a x); intuition.
  rewrite eqb_leibniz in H2.
  subst.
  rewrite eqb_refl in H4.
  simpl in *.
  discriminate.

  rewrite evalDist_assoc at 1.
  rewrite evalDist_assoc at 1.
  rewrite (evalDist_seq_step) at 1.
  rewrite (sumList_filter_partition (fun z => z)) at 1.
  rewrite (@sumList_exactly_one _ true) at 1.
  rewrite (@sumList_exactly_one _ false) at 1.
  rewrite Bernoulli_correct at 1.
  rewrite Bernoulli_correct_complement at 1.
  dist_simp.

  assert (Pr  [a0 <-$ ret y; x0 <-$ ret (a, a0); ret eqb (snd x0) r2 ] ==
    Pr  [ret eqb y r2 ]).
  dist_simp.
  simpl.
  intuition.
  rewrite H5 at 1.
  clear H5.

  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply ratAdd_eqRat_compat.
  eapply eqRat_refl.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply evalDist_seq_eq.
  intuition.
  eapply eqRat_refl.
  intuition.
  dist_simp.
  unfold snd.
  eapply eqRat_refl.

  eapply ratFraction_le_1.
  eapply ratSubtract_leRat.
  eapply evalDist_le_1.
  intuition.
  
  eapply ratFraction_le_1.
  eapply ratSubtract_leRat.
  eapply evalDist_le_1.
  intuition.

  eapply filter_NoDup.
  eapply getSupport_NoDup.

  eapply filter_In; intuition.
  eapply getSupport_In_evalDist.
  intuition.
  rewrite Bernoulli_correct_complement in H5.
  apply ratSubtract_0_inv in H5.
  apply ratFraction_ge_1_inv in H5.

  eapply ratSubtract_leRat_same_r in H5.
  eapply n.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  trivial.

  eapply evalDist_le_1.
  intuition.

  eapply ratFraction_le_1.
  eapply ratSubtract_leRat.
  eapply evalDist_le_1.
  intuition.

  intuition.

  destruct b; intuition.
  apply filter_In in H5.
  intuition.
  
  eapply filter_NoDup.
  eapply getSupport_NoDup.

  eapply filter_In.
  intuition.
  eapply getSupport_In_evalDist.
  intuition.
  rewrite Bernoulli_correct in H5.
  apply ratMult_0 in H5.
  intuition.
  apply ratSubtract_0_inv in H6.
  eapply n1.
  eapply leRat_impl_eqRat; intuition.
  eapply ratInverse_nz;eauto.
  eapply ratFraction_le_1.
  eapply ratSubtract_leRat.
  eapply evalDist_le_1.
  intuition.

  intuition.
  destruct b; intuition.
  apply filter_In in H5; intuition.
  discriminate.

  intuition.
  intuition.

  rewrite (@sumList_exactly_one _ x).
  rewrite sumList_factor_constant_r.

  assert (sumList (filter (fun a : A => negb (eqb x a)) (getSupport c1))
     (evalDist c1) ==
     ratSubtract 1 (evalDist c1 x)).

  eapply sumList_filter_complement.
  trivial.
  rewrite H2.
  clear H2.
  rewrite ratMult_distrib.

  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply eqRat_refl.
  eapply ratAdd_eqRat_compat.
  rewrite <- ratMult_assoc.
  eapply ratMult_eqRat_compat.
  rewrite ratMult_comm.
  rewrite ratMult_assoc.
  rewrite ratInverse_prod_1.
  eapply ratMult_1_r.

  intuition.
  eapply n.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  intuition.
  eapply leRat_trans; eauto.
  apply ratSubtract_0_inv.
  trivial.

  eapply eqRat_refl.

  rewrite <- ratMult_assoc.
  eapply ratMult_eqRat_compat.
  rewrite ratMult_comm.
  rewrite ratMult_ratSubtract_distrib_r.
  rewrite ratMult_1_l.
  eapply ratSubtract_eqRat_compat.
  eapply eqRat_refl.
  rewrite ratMult_assoc.
  rewrite ratInverse_prod_1.
  eapply ratMult_1_r.

  intuition.
  eapply n.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  intuition.
  eapply leRat_trans; eauto.
  apply ratSubtract_0_inv.
  trivial.
  
  eapply eqRat_refl.

  case_eq (eqb y r2); intuition.
  rewrite eqb_leibniz in H2.
  subst.
  assert (Pr [ret true] == 1).
  dist_compute.
  rewrite H2.
  clear H2.
  repeat rewrite ratMult_1_r.

  assert (Pr  [x0 <-$ Repeat c2 (fun z : B => negb (eqb z r2)); ret eqb x0 r2 ] ==
    Pr  [x0 <-$ Repeat c2 (fun z : B => negb (eqb z r2)); ret eqb r2 x0 ]).

  dist_skip; dist_compute.
  rewrite H2; clear H2.
  rewrite <- evalDist_event_equiv.

  rewrite evalDist_Repeat_0.
  rewrite ratMult_0_r.
  rewrite <- ratAdd_0_r.
  eapply ratSubtract_ratAdd_inverse_2.
  trivial.

  intuition.
  subst.
  rewrite eqb_refl in H3.
  simpl in *.
  discriminate.

  assert (Pr [ret false] == 0).
  dist_compute.
  rewrite H3.
  clear H3.
  repeat rewrite ratMult_0_r.
  repeat rewrite <- ratAdd_0_l.

  rewrite <- ratSubtract_ratAdd_distr.
  rewrite ratSubtract_ratAdd_inverse_2; trivial.
  simpl.

  destruct (in_dec (EqDec_dec _) r2 (getSupport c2)).

  rewrite (@sumList_exactly_one _ r2).
  rewrite eqb_refl.
  destruct (EqDec_dec bool_EqDec true true); intuition.
  unfold indicator.
  case_eq (eqb r2 y); intuition.
  rewrite eqb_leibniz in H3.
  subst.
  rewrite eqb_refl in H2.
  discriminate.
  simpl.
  rewrite ratMult_1_l.
  rewrite ratMult_1_r.

  assert ((sumList (filter (fun z : B => negb (eqb y z)) (getSupport c2))
         (evalDist c2) ==
         (ratSubtract 1 (evalDist c2 y)))).
  eapply sumList_filter_complement.
  trivial.

  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply ratMult_eqRat_compat.
  eapply ratInverse_eqRat_compat.
  intuition.
  assert ((filter (fun z : B => negb (eqb y z)) (getSupport c2)) =
    (filter (fun z : B => negb (eqb z y)) (getSupport c2))).

  eapply filter_ext; intuition.

  rewrite eqb_symm.
  trivial.

  rewrite H6 in H4.
  clear H6.
  rewrite H4 in H5.
  eapply n.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  eapply ratSubtract_0_inv.
  trivial.
  
  assert ((filter (fun z : B => negb (eqb z y)) (getSupport c2)) = 
    (filter (fun z : B => negb (eqb y z)) (getSupport c2))).

  eapply filter_ext.
  intuition.
  rewrite eqb_symm.
  trivial.
  rewrite H5.
  clear H5.

  eapply H4.
  eapply eqRat_refl.
  clear H4.
  rewrite <- ratMult_assoc.
  symmetry.
  rewrite <- ratMult_1_l at 1.
  eapply ratMult_eqRat_compat; intuition.
  symmetry.
  rewrite ratMult_comm.
  eapply ratInverse_prod_1.

  intuition.
  eapply n.
  eapply leRat_impl_eqRat.
  eapply evalDist_le_1.
  intuition.
  eapply ratSubtract_0_inv.
  trivial.
  
  eapply filter_NoDup.
  eapply getSupport_NoDup.

  eapply filter_In; intuition.
  case_eq (eqb r2 y); intuition.
  rewrite eqb_leibniz in H3; subst.
  rewrite eqb_refl in H2.
  discriminate.

  intuition.
  apply filter_In in H3.
  intuition.
  case_eq (eqb b r2); intuition.
  rewrite eqb_leibniz in H3.
  subst.
  intuition.
  destruct (EqDec_dec bool_EqDec false true ).
  discriminate.
  rewrite ratMult_0_r.
  intuition.

  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply sumList_0.
  intuition.
  apply filter_In in H3.
  destruct ( EqDec_dec bool_EqDec (eqb a r2) true); intuition.
  rewrite eqb_leibniz in e; subst.
  intuition.
  eapply ratMult_0_r.
  rewrite ratMult_0_r.
  symmetry.
  eapply getSupport_not_In_evalDist.
  intuition.
  
  eapply filter_NoDup.
  eapply getSupport_NoDup.

  eapply filter_In; intuition.
  eapply getSupport_In_evalDist; intuition.
  apply eqb_refl.

  intuition.
  apply filter_In in H2.
  intuition.
  dist_compute.

  repeat simp_in_support;
  simpl in *; trivial.

  simpl in *.
  rewrite eqb_refl in Heqx2.
  discriminate.

  Grab Existential Variables.
  unfold eq_dec; intuition.
  eapply (EqDec_dec _).
  unfold eq_dec; intuition.
  eapply (EqDec_dec _).

  intuition.
  intuition.
  intuition.
  intuition.
  intuition.

Qed.

(* soundness theorems *)

Theorem comp_spec_impl_le : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : Comp A)(c2 : Comp B),
    forall x y, 
      comp_spec (fun a b => a = x -> b = y) c1 c2 ->
      evalDist c1 x <= evalDist c2 y.

  intuition.
  despec.
  intuition.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eauto.
  }
  unfold marginal_l, marginal_r.
  dist_skip.
  dist_compute.
  exfalso.
  eapply n.
  specialize (H2 x1).
  intuition.
  
  eapply rat0_le_all.
Qed.

Theorem comp_spec_eq_symm: 
  forall (A : Set){eqda : EqDec A}(c1 c2 : Comp A),
      comp_spec eq c1 c2 ->
      comp_spec eq c2 c1.

  intuition.
  eapply comp_spec_symm.
  eapply comp_spec_consequence; eauto.

Qed.

Theorem comp_spec_impl_eq : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : Comp A)(c2 : Comp B),
    forall x y, 
      comp_spec (fun a b => a = x <-> b = y) c1 c2 ->
      evalDist c1 x == evalDist c2 y.

  intuition.
  eapply leRat_impl_eqRat.

  eapply comp_spec_impl_le.
  eapply comp_spec_consequence.
  eauto.
  intuition.
  subst.
  intuition.

  eapply comp_spec_impl_le.
  eapply comp_spec_symm.
  eapply comp_spec_consequence.
  eauto.
  intuition.
  subst.
  intuition.
Qed.


(* facts about basic language constructs *)
Theorem comp_spec_ret : 
  forall (A B : Set){eqda1 : EqDec A}{eqdb1 : EqDec B}(eqda2 : eq_dec A)(eqdb2 : eq_dec B)(P : A -> B -> Prop) a b,
    P a b ->
    @comp_spec _ _ eqda1 eqdb1 P (Ret eqda2 a) (Ret eqdb2 b).
  
  intuition.
  exists (ret (a, b)).
  intuition.
  unfold marginal_l.
  dist_compute.
  
  unfold marginal_r.
  dist_compute.
  
  simp_in_support.
  trivial.
  
Qed.

Theorem comp_spec_rnd : 
  forall n x y,
  comp_spec (fun a b : Vector.t bool n => a = x <-> b = y) 
     ({ 0 , 1 }^n) ({ 0 , 1 }^n).

  intuition.
  eapply eq_impl_comp_spec; wftac.
  eapply uniformity.

Qed.




(* facts about equality specifications *)
Theorem eq_impl_comp_spec_eq : 
  forall (A : Set){eqd1 eqd2 : EqDec A}(c1 c2 : Comp A),
    (forall x, evalDist c1 x == evalDist c2 x) ->
    @comp_spec _ _ eqd1 eqd2 eq c1 c2.

  intuition.

  exists (x <-$ c1; ret (x, x)).
  intuition.

  unfold marginal_l.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_compute.

  unfold marginal_r.
  dist_inline_first.
  rewrite <- H.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_compute.

  repeat simp_in_support.
  trivial.

  Grab Existential Variables.
  intuition.
  intuition.
  
Qed.

Theorem comp_spec_eq_refl : 
  forall (A : Set){eqd : EqDec A}(c : Comp A),
    comp_spec eq c c.

  intuition.
  eapply eq_impl_comp_spec_eq; intuition.

Qed.

Theorem comp_spec_eq_impl_eq : 
  forall (A : Set){eqd1 eqd2 : EqDec A}(c1 c2 : Comp A),
    @comp_spec _ _ eqd1 eqd2 eq c1 c2 ->
    (forall x, evalDist c1 x == evalDist c2 x).

  intuition.
  despec.
  intuition.
  rewrite H0.
  rewrite H.
  unfold marginal_l, marginal_r.
  dist_skip.
  simpl.
  specialize (H2 x1).
  intuition.
  destruct x1.
  simpl in *.
  subst.

  destruct (EqDec_dec bool_EqDec (@eqb _ eqd1 a0 x) true); intuition.
  rewrite eqb_leibniz in e.
  subst.
  destruct (EqDec_dec bool_EqDec (@eqb _ eqd2 x x) true); intuition.
  exfalso.
  eapply n.
  eapply eqb_refl.

  destruct (EqDec_dec bool_EqDec (@eqb _ eqd2 a0 x) true); intuition.
  rewrite eqb_leibniz in e.
  subst.
  exfalso.
  eapply n.
  eapply eqb_leibniz.
  trivial.

Qed.
  
Theorem comp_spec_eq_trans_l : 
  forall (A B : Set){eqd : EqDec A}{eqd : EqDec B}(c1 c2 : Comp A)(c3 : Comp B) P,
    comp_spec eq c1 c2 ->
    comp_spec P c2 c3 ->
    comp_spec P c1 c3.

  intuition.

  despec.
  intuition.
  exists x.
  intuition.
 
  eapply comp_spec_eq_impl_eq in H; intuition.
  rewrite H.
  trivial.

Qed.

Theorem comp_spec_eq_trans : 
  forall (A : Set){eqd : EqDec A}(c1 c2 c3 : Comp A),
    comp_spec eq c1 c2 ->
    comp_spec eq c2 c3 ->
    comp_spec eq c1 c3.

  intuition.
  eapply comp_spec_eq_trans_l;
  eauto.

Qed.

Theorem comp_spec_eq_trans_r : 
  forall (A B : Set){eqd : EqDec A}{eqd : EqDec B}(c1 : Comp A)(c2 c3 : Comp B) P,
    comp_spec P c1 c2 ->
    comp_spec eq c2 c3 ->
    comp_spec P c1 c3.

  intuition.

  destruct H.
  intuition.
  exists x.
  intuition.
 
  eapply comp_spec_eq_impl_eq in H0; intuition.
  rewrite <- H0.
  trivial.

Qed.

Theorem comp_spec_seq_eq : 
  forall (A B C : Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}(c1 c2 : Comp A)(f1 : A -> Comp B)(f2 : A -> Comp C) P (b : B) (c : C),
    comp_spec eq c1 c2 ->
    (forall a, comp_spec P (f1 a) (f2 a)) ->
    comp_spec P (Bind c1 f1) (Bind c2 f2).
  
  intuition.
  eapply comp_spec_seq; trivial.
  eauto.
  intuition; subst; intuition.
  
Qed.

Theorem comp_spec_eq_swap : 
  forall (A B C : Set){eqdc : EqDec C}(c1 : Comp A)(c2 : Comp B)(f : A -> B -> Comp C),
    comp_spec eq (x <-$ c1; y <-$ c2; f x y) (y <-$ c2; x <-$ c1; f x y).
  
  intuition.
  eapply eq_impl_comp_spec_eq.
  intuition.
  eapply evalDist_commute_eq.
  
Qed.

Theorem comp_spec_right_ident : 
  forall (A : Set){eqd : EqDec A}(c1 : Comp A), 
    comp_spec eq (x <-$ c1; ret x) c1.

  intuition.
  eapply eq_impl_comp_spec_eq.
  eapply evalDist_right_ident.
Qed.

Theorem comp_spec_left_ident : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : A -> Comp B) a, 
    comp_spec eq (x <-$ ret a; c1 x) (c1 a).

  intuition.
  eapply eq_impl_comp_spec_eq.
  intuition.
  
  specialize (@evalDist_left_ident eqRat); intuition.
Qed.

Theorem comp_spec_assoc : 
  forall (A B C : Set){eqd : EqDec C}(c1 : Comp A)(c2 : A -> Comp B)(c3 : B -> Comp C), 
    comp_spec eq (x <-$ (y <-$ c1; c2 y); c3 x) (y <-$ c1; x <-$ c2 y; c3 x).

  intuition.
  eapply eq_impl_comp_spec_eq.
  intuition.
  eapply evalDist_assoc; intuition.
Qed.


(* other facts *)
Theorem comp_spec_event_equiv : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : Comp A)(c2 : Comp B)(f1 : A -> bool)(f2 : B -> bool)(P : bool -> bool -> Prop),
    comp_spec (fun a b => P (f1 a) (f2 b)) c1 c2 ->
    comp_spec P (x <-$ c1; ret (f1 x)) (x <-$ c2; ret (f2 x)).
  
  intuition.
  
  eapply comp_spec_seq.
  apply true.
  apply true.
  eauto.
  intuition.
  eapply comp_spec_ret.
  trivial.
  
Qed.

Theorem comp_spec_iso : 
  forall (A B : Set){eqda : EqDec A}{eqdb : EqDec B}(c1 : Comp A)(c2 : Comp B)(f : A -> B)(f_inv : B -> A),
    (forall x : B, In x (getSupport c2) -> f (f_inv x) = x) ->
    (forall x : A, In x (getSupport c1) -> f_inv (f x) = x) ->
    (forall x : B, In x (getSupport c2) -> In (f_inv x) (getSupport c1)) ->
    (forall x : A, In x (getSupport c1) -> comp_spec (fun a b => a = (f x) <-> b = x) c2 c1) -> 
    comp_spec (fun a b => f a = b) c1 c2.

  intuition.

  intuition.
  remember f_inv as f_inv2.
  exists (x <-$ c1; ret (x, f x)).
  intuition; subst.

  unfold marginal_l.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  dist_skip.
  dist_compute.

  unfold marginal_r.
  dist_inline_first.
  rewrite <- evalDist_right_ident.
  eapply (@distro_iso_eq _ _ _ _ f f_inv).
  intuition.
  intuition.
  intuition.
  intuition.
  
  rewrite evalDist_event_equiv.
  symmetry.
  rewrite evalDist_event_equiv.
  eapply comp_spec_impl_eq.

  eapply (@comp_spec_consequence _ _ _ _ _ _ eq).
  eapply comp_spec_event_equiv.
  eapply comp_spec_symm.
  eapply comp_spec_consequence.
  eapply H2.
  eauto.
  intuition.
  case_eq (eqb x b); intuition.
  rewrite eqb_leibniz in H5.
  subst.
  intuition.
  subst.
  repeat rewrite eqb_refl.
  intuition.
  case_eq (eqb (f x) a); intuition.
  rewrite eqb_leibniz in H4.
  subst.
  intuition.
  subst.
  repeat rewrite eqb_refl.
  intuition.
  rewrite H5.
  rewrite H4.
  intuition.
  intuition.
  subst.
  trivial.
  subst.
  trivial.

  intuition.
  dist_compute.

  repeat simp_in_support.
  trivial.

  Grab Existential Variables.
  intuition.
  intuition.

Qed.

Theorem comp_spec_irr_r : 
  forall (A B C : Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}(c1 : Comp A)(c2 : Comp B)(f2 : B -> Comp C) P,
    well_formed_comp c2 ->
    (forall b, In b (getSupport c2) -> comp_spec P c1 (f2 b)) ->
    comp_spec P c1 (Bind c2 f2).

  intuition.
  apply list_choice in H0.
  destruct H0.
  exists (y <-$ c2; x y).
  intuition.
  unfold marginal_l.
  dist_inline_first.
  dist_irr_r.
  specialize (H0 x0); intuition.
  eapply H0.
  
  unfold marginal_r.
  dist_inline_first.
  dist_skip.
  specialize (H0 x0); intuition.
  apply H2.
  repeat simp_in_support.
  specialize (H0 x0); intuition.
  intuition.
  eapply (EqDec_dec _).
  apply (x <-$ c1; y <-$ c2; z <-$ f2 y; ret (x, z)).
Qed.

Theorem comp_spec_irr_l : 
  forall (A B C : Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}(c1 : Comp A)(c2 : Comp B)(f1 : A -> Comp C) P,
    well_formed_comp c1 ->
    (forall a, In a (getSupport c1) -> comp_spec P (f1 a) c2) ->
    comp_spec P (Bind c1 f1) c2.

  intuition.
  apply list_choice in H0.
  destruct H0.
  exists (y <-$ c1; x y).
  intuition.
  unfold marginal_l.
  dist_inline_first.
  dist_skip.
  specialize (H0 x0); intuition.
  eapply H0.
  
  unfold marginal_r.
  dist_inline_first.
  dist_irr_r.
  specialize (H0 x0); intuition.
  apply H2.
  repeat simp_in_support.
  specialize (H0 x0); intuition.
  intuition.
  eapply (EqDec_dec _).
  apply (x <-$ c1; y <-$ c2; z <-$ f1 x; ret (z, y)).
Qed.


(* equational rules for computations with oracles. *)
Transparent evalDist.
Transparent getSupport.


Theorem oc_comp_spec_eq : 
  forall (A B C : Set)(c : OracleComp A B C), forall (*(eqda : EqDec A)*) (eqdb : EqDec B) (eqdc : EqDec C)(S1 S2 : Set)(o1 : S1 -> A -> Comp (B * S1))(o2 : S2 -> A -> Comp (B * S2)) eqds1 eqds2 s1 s2 (P : S1 -> S2 -> Prop),
    P s1 s2 ->
    (forall a x1 x2, P x1 x2 -> comp_spec (fun y1 y2 => fst y1 = fst y2 /\ P (snd y1) (snd y2)) (o1 x1 a) (o2 x2 a)) ->
    comp_spec (fun a b => fst a = fst b /\ P (snd a) (snd b))
    (c _ eqds1 o1 s1)
    (c _ eqds2 o2 s2).
  
  (* We have to do this by induction on the computation, since it may make an arbitary number of calls to the oracle. *)

  induction c; intuition; simpl in *.

  eapply (@comp_spec_consequence _ _ (@pair_EqDec B S1 eqdb eqds1) _ (@pair_EqDec B S2 eqdb eqds2)).
  eapply H0; intuition.
  intuition.

  (* OC_Run case *)
  assert (EqDec C).
  eapply EqDec_pair_l;
    eauto.

  eapply (@comp_spec_seq _ _ (fun a b => fst a = fst b /\ fst (snd a) = fst (snd b) /\ P (snd (snd a)) (snd (snd b)) ))
  ; eauto.
  intuition.
  eapply oc_base_exists; eauto; intuition.
  assert (B * S).
  eapply oc_base_exists.
  eauto.
  intuition.
  assert (B' * S1).
  eapply comp_base_exists.
  eauto.
  intuition.
  intuition.

  intuition.
  eapply oc_base_exists; eauto; intuition.
  assert (B * S).
  eapply oc_base_exists.
  eauto.
  intuition.
  assert (B' * S1).
  eapply comp_base_exists.
  eauto.
  intuition.
  intuition.
  
  eapply comp_spec_consequence.
  eapply (IHc _ _ _ _ _ _ _ _ _ _ (fun p1 p2 => fst p1 = fst p2 /\ P (snd p1) (snd p2))).
  simpl; intuition.
  
  intuition.
  simpl in *.
  subst.
       
  eapply comp_spec_seq.
  intuition.
  assert (B * S).
  eapply oc_base_exists.
  eauto.
  intuition.
  assert (B' * S1).
  eapply comp_base_exists.
  eapply o1; intuition.
  intuition.
  intuition.
  
  intuition.
  assert (B * S).
  eapply oc_base_exists.
  eauto.
  intuition.
  assert (B' * S1).
  eapply comp_base_exists.
  eapply o1; intuition.
  intuition.
  intuition.
  
  eapply H.
  eauto.
  intuition.
  intuition.
  eapply comp_spec_ret.
  simpl in *; intuition.
  destruct b2; simpl in *.
  destruct p; simpl in *; intuition.
  inversion H7; clear H7; subst.
  intuition.
  destruct b2; simpl in *.
  subst.
  simpl.
  intuition.
        
  intuition.
  intuition.
  simpl in *.
  subst.
  eapply comp_spec_ret.
  simpl in *.
  destruct b; simpl in *.
  intuition.

  eapply comp_spec_seq_eq; intuition.
  eapply comp_base_exists; intuition.
  eapply comp_base_exists; intuition.
  eapply comp_spec_eq_refl.
  eapply comp_spec_ret; simpl; intuition.
  
  assert (EqDec C).
  eapply oc_EqDec.
  eapply c.
  intuition.
  intuition.
  assert (B * S1).
  eapply comp_base_exists.
  eauto.
  intuition.
  intuition.

  eapply comp_spec_seq.
  
  intuition.
  eapply oc_base_exists.
  eapply o.
  eapply oc_base_exists.
  eauto.
  intuition.
  assert (B * S1).
  eapply comp_base_exists.
  eapply o1.
  intuition.
  trivial.
  intuition.
  intuition.
  assert (B * S1).
  eapply comp_base_exists.
  eapply o1; intuition.
  intuition.
  
  intuition.
  eapply oc_base_exists.
  eapply o.
  eapply oc_base_exists.
  eauto.
  intuition.
  assert (B * S1).
  eapply comp_base_exists.
  eapply o1.
  intuition.
  trivial.
  intuition.
  intuition.
  assert (B * S1).
  eapply comp_base_exists.
  eapply o1; intuition.
  intuition.
  
  eapply IHc.
  eauto.
  intuition.
  intuition.
  simpl in *.
  subst.
  destruct b0.
  simpl.
  eapply H; intuition.
  
Qed.

Opaque evalDist.

Theorem oc_comp_wf_inv
   : forall (A B C : Set) (c : OracleComp A B C),
     well_formed_oc c ->
     forall (S : Set) (P : S -> Prop)(eqds : EqDec S) (o : S -> A -> Comp (B * S)) (s : S),
     (forall (a : S) (b : A), P a -> well_formed_comp (o a b)) ->
     (forall a b s s', P s -> In (b, s') (getSupport (o s a)) -> P s') ->
     P s -> 
     well_formed_comp (c S eqds o s).

  induction 1; intuition; simpl in *.

  eapply H.
  trivial.

  wftac.
  eapply (@IHwell_formed_oc _ (fun x => P (snd x))).
  intuition.
  wftac.
  intuition.
  repeat simp_in_support.
  simpl in *.
  destruct x; simpl in *.
  eapply oc_comp_invariant.
  intuition.
  eapply H3; eauto.
  eauto.
  eauto.
  trivial.
  
  wftac.
  
  wftac.
  eapply H1; intuition.
  eapply H2; eauto.
  eapply H3; eauto.
  eapply oc_comp_invariant; intuition.
  eapply H3; eauto.
  eauto.
  eauto.

Qed.

Theorem oc_comp_spec_eq_until_bad : 
  forall (A B C : Set)(c : OracleComp A B C), 
    well_formed_oc c ->
    forall (eqdb : EqDec B) (eqdc : EqDec C)(S1 S2 : Set)(o1 : S1 -> A -> Comp (B * S1))(o2 : S2 -> A -> Comp (B * S2)) eqds1 eqds2 
    (bad1 : S1 -> bool)(bad2 : S2 -> bool)(inv : S1 -> S2 -> Prop),
    (forall a b, bad1 a = true -> well_formed_comp (o1 a b)) ->
    (forall a b, bad2 a = true -> well_formed_comp (o2 a b)) ->
    (forall x1 x2 a,
      inv x1 x2 ->
      bad1 x1 = bad2 x2 ->
      comp_spec 
      (fun y1 y2 => (bad1 (snd y1) = bad2 (snd y2)) /\ (bad1 (snd y1) = false -> (inv (snd y1) (snd y2) /\ fst y1 = fst y2)))
      (o1 x1 a) (o2 x2 a)) ->
    (forall a b c d,
      bad1 c = true ->
      In (a, b) (getSupport (o1 c d)) -> bad1 b = true) ->
    (forall a b c d,
      bad2 c = true ->
      In (a, b) (getSupport (o2 c d)) -> bad2 b = true) ->
    ((forall s1 s2, 
      inv s1 s2 ->
      bad1 s1 = bad2 s2 ->
      comp_spec
      (fun y1 y2 => (bad1 (snd y1) = bad2 (snd y2)) /\ (bad1 (snd y1) = false -> inv (snd y1) (snd y2) /\ (fst y1 = fst y2)))
      (c _ eqds1 o1 s1)
      (c _ eqds2 o2 s2))).

  induction 1; intuition; simpl in *.

  (* Query case *)
  eapply (@comp_spec_consequence _ _ (@pair_EqDec B S1 eqdb eqds1) _
    (@pair_EqDec B S2 eqdb eqds2)).
  eapply H1; intuition.
  intuition.

  (* Run case *)
  assert (EqDec C).
  eapply EqDec_pair_l; eauto.

  assert C.
  eapply oc_base_exists; eauto.
  eapply (fun a => fst (oc_base_exists (o s a) (fun a' => fst (comp_base_exists (o1 s1 a'))))).
  
  eapply (@comp_spec_seq _ _ 
    (fun x y => (bad1 (snd (snd x)) = bad2 (snd (snd y))) /\ (bad1 (snd (snd x)) = false -> (fst (snd x) = fst (snd y) /\ fst x = fst y /\ inv (snd (snd x)) (snd (snd y)))))).
  intuition.
  intuition.

  eapply comp_spec_consequence.
  eapply (@IHwell_formed_oc _ _ (S * S1) (S * S2) _ _ _ _ 
     (fun a => bad1 (snd a)) (fun a => bad2 (snd a)) (fun a b => bad1 (snd a) = false -> (inv (snd a) (snd b) /\ fst a = fst b)))%type.

  (* ---- *)

  intuition.
  simpl in *.

  wftac.
  eapply oc_comp_wf_inv;
  intuition.
  eapply H2.
  eapply H12.
  intuition.
  eapply H5; intuition.
  eauto.
  eauto.
  trivial.
  intuition.
  wftac.
  simpl in *.
  eapply oc_comp_wf_inv;
  intuition.
  eapply H3.
  eapply H12.
  intuition.
  eapply H6; intuition.
  eauto.
  eauto.
  trivial.

  intuition.
  simpl in *.

  case_eq (bad1 b); intuition.
  eapply comp_spec_irr_l; intuition.
  eapply oc_comp_wf_inv; eauto.
  eapply H2.
  intuition; simpl.
  eapply H5.
  eauto.
  eauto.
  trivial.
  eapply comp_spec_irr_r; intuition.
  eapply oc_comp_wf_inv; eauto.
  eapply H3.
  intuition; simpl.
  eapply H6.
  eauto.
  eauto.
  simpl.
  rewrite <- H12.
  trivial.

  eapply comp_spec_ret; simpl in *; intuition.

  destruct a2; simpl in *.
  assert (bad1 s0 = true). 
  eapply (oc_comp_invariant_f).
  intuition.
  eapply H5; eauto.
  eauto.
  eauto.
  destruct b1.
  simpl in *.
  rewrite H16.
  symmetry.
  eapply (@oc_comp_invariant_f).
  intuition.
  eapply H6;
  eauto.
  eauto.
  eauto.
  
  (*contradiction *)
  destruct a2.
  simpl in *.
  assert (bad1 s0 = true).
  eapply (@oc_comp_invariant_f).
  intuition.
  eapply H5; eauto.
  eauto.
  eauto.
  congruence.
  (* contradiction *)
  destruct a2; simpl in *.
  assert (bad1 s0 = true).
  eapply (@oc_comp_invariant_f).
  intuition.
  eapply H5; eauto.
  eauto.
  eauto.
  congruence.
  (* contradiction *)
  destruct a2; simpl in *.
  assert (bad1 s0 = true).
  eapply (@oc_comp_invariant_f).
  intuition.
  eapply H5; eauto.
  eauto.
  eauto.
  congruence.

  subst.
  (* IH *)
  assert B.
  assert (B * S).
  eapply oc_base_exists.
  eapply o; intuition.
  intuition.
  assert (B' * S1).
  eapply comp_base_exists.
  eapply o1; intuition.
  intuition.
  intuition.

  eapply comp_spec_seq.
  intuition.
  intuition.

  eapply H1;
  intuition.
  intuition.
  intuition.
  intuition.
  eapply comp_spec_ret.
  simpl in *; intuition.
  destruct b3. destruct p. simpl in *.
  pairInv.
  trivial.
  destruct b3.
  simpl in *.
  subst.
  trivial.

  intuition.
  repeat simp_in_support.
  simpl in *.
  destruct x; simpl in *.
  eapply oc_comp_invariant_f; intuition.
  eapply H5; eauto.
  eauto.
  eauto.

  intuition.
  repeat simp_in_support.
  simpl in *.
  destruct x; simpl in *.
  eapply oc_comp_invariant_f; intuition.
  eapply H6; eauto.
  eauto.
  eauto.

  intuition.
  intuition.
  intuition.

  intuition.
  eapply comp_spec_ret.
  simpl in *; intuition.
  subst.
  intuition.

  (* Ret case *)
  assert C.
  eapply comp_base_exists; eauto.
  eapply comp_spec_seq; intuition.
  eapply comp_spec_eq_refl.
  subst.
  eapply comp_spec_ret.
  simpl in *; intuition.

 
  (* Bind case *)
  assert (A -> B).
  intuition.
  eapply (comp_base_exists (o1 s1 H9)).

  assert C.
  eapply oc_base_exists.
  eauto.
  intuition.
  
  assert C'.
  eapply oc_base_exists.
  eapply f.
  eapply oc_base_exists; eauto.
  intuition.

  assert (EqDec C).
  eapply oc_EqDec.
  eauto.
  intuition.
  intuition.
  
  eapply comp_spec_seq;
  intuition.
  eapply (@IHwell_formed_oc _ _ _ _ _ _ _ _ bad1 bad2 inv).
  eauto.
  eauto.
  intuition.
  intuition.
  intuition.
  trivial.
  trivial.
  intuition.
  destruct b0.
  simpl in *.
  case_eq (bad1 b); intuition.

  eapply comp_spec_eq_trans_l.
  eapply comp_spec_eq_symm.
  eapply comp_spec_right_ident.
  eapply comp_spec_eq_trans_r.
  2:{
    eapply comp_spec_right_ident.
  }
  eapply comp_spec_irr_l; intuition.
  eapply oc_comp_wf_inv; eauto.
  intuition.
  eapply H2; intuition.
  eapply H15.
  intuition.
  eapply H5; intuition.
  eauto.
  eauto.
  trivial.
  eapply comp_spec_irr_r; intuition.
  eapply oc_comp_wf_inv; eauto.
  intuition.
  eapply H3; intuition.
  eapply H19.
  intuition.
  eapply H6; intuition.
  eauto.
  eauto.
  simpl.
  rewrite <- H17.
  trivial.
  
  eapply comp_spec_ret.
  simpl in *; intuition.
  destruct a. destruct b0; simpl in *.
  assert (bad1 s0 = true).
  eapply (oc_comp_invariant_f (f a0) bad1); intuition.
  eapply H5.
  eapply H21.
  eapply H20.
  eapply H16.
  eapply H15.
  rewrite H20.
  symmetry.
  assert (bad2 s = true).
  rewrite <- H17.
  trivial.
  
  eapply (oc_comp_invariant_f (f c0) bad2); intuition.
  eapply H6.
  eapply H23.
  eapply H22.
  eapply H21.
  eapply H19.

  destruct a; simpl in *.
  destruct b0; simpl in *.
  assert (bad1 s0 = true).
  eapply oc_comp_invariant_f.
  intuition.
  eapply H5.
  eapply H22.
  eapply H21.
  eapply H16.
  eapply H15.
  congruence.

  destruct a; simpl in *.
  destruct b0; simpl in *.
  assert (bad1 s0 = true).
  eapply oc_comp_invariant_f.
  intuition.
  eapply H5.
  eapply H22.
  eapply H21.
  eapply H16.
  eapply H15.
  congruence.

  subst.
  eapply H1;
  intuition.
 
Qed.

Theorem rnd_swap : forall eta a b,
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
  case_eq (eqb b x); intuition.
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
  case_eq (eqb a a0); intuition;
  rewrite H0 in H.
  rewrite eqb_leibniz in H0.
  intuition.

  case_eq (eqb b a0); intuition;
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

Require Import Setoid.

Add Parametric Relation (A : Set){eqd : EqDec A} : (Comp A) (@comp_spec A A eqd eqd eq)
  as comp_spec_eq_rel.

Global Instance comp_spec_eq_rel_Reflexive (A : Set) (eqd : EqDec A) : Reflexive (comp_spec eq)
  | 10 := @comp_spec_eq_refl A eqd.
Global Instance comp_spec_eq_rel_Symmetric (A : Set) (eqd : EqDec A) : Symmetric (comp_spec eq)
  | 10 := @comp_spec_eq_symm A eqd.
Global Instance comp_spec_eq_rel_Transitive (A : Set) (eqd : EqDec A) : Transitive (comp_spec eq)
  | 10 := @comp_spec_eq_trans A eqd.
Global Instance comp_spec_eq_rel (A : Set) (eqd : EqDec A) : Equivalence (comp_spec eq)
  | 10 := {}.