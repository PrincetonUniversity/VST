(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* A generic one-time pad that can be reused in other proofs. Also included are specializations for bit vectors and finite cyclic groups. *)

Set Implicit Arguments.

Require Import FCF.FCF.

Definition D := evalDist.
Definition dist_iso := evalDist_iso.

Ltac r_ident_r :=
  symmetry;
  rewrite <- evalDist_right_ident;
  symmetry.

Ltac xorTac_once :=
  match goal with
    | [|- context[?x xor (?x xor ?x0)] ]=> rewrite <- BVxor_assoc; rewrite BVxor_same_id; rewrite BVxor_id_l
    | [|- context[(?x xor ?x0) xor ?x] ]=> rewrite <- BVxor_comm
  end.

Ltac xorTac := repeat xorTac_once;
              simpl; try reflexivity; try eapply in_getAllBvectors.

(*
(* Simple example used for illustration *)
Section OTP.
  Variable c : nat.
  Definition OTP (x : Bvector c) : Comp (Bvector c) 
    := p <-$ {0, 1}^c; ret (BVxor c p x).

  Theorem OTP_eq_Rnd: 
    forall (x y : Bvector c),
      D (OTP x) y == D ({0, 1}^c) y.

    intuition.
    unfold OTP.
    r_ident_r.
    eapply (dist_iso (BVxor c x) (BVxor c x)); 
      intuition; xorTac.
  Qed.

End OTP.
*)

(* The actual argument is more general (and more complex) *)
Section OTP.

  Variable T : Set.
  Hypothesis T_EqDec : EqDec T.
  Variable RndT : Comp T.
  Variable T_op : T -> T -> T.
  Hypothesis op_assoc : forall x y z, T_op (T_op x y) z = T_op x (T_op y z).
  Variable T_inverse : T -> T. 
  Variable T_ident : T.
  Hypothesis inverse_l_ident : forall x, T_op (T_inverse x) x = T_ident.
  Hypothesis inverse_r_ident : forall x, T_op x (T_inverse x) = T_ident.
  Hypothesis ident_l : forall x, T_op T_ident x = x.
  Hypothesis ident_r : forall x, T_op x T_ident = x.
  Hypothesis RndT_uniform : forall x y, comp_spec (fun a b => a = x <-> b = y) RndT RndT.

  Theorem all_in_support : 
    forall y, In y (getSupport RndT) ->
    forall x, In x (getSupport RndT).

    intuition.
    eapply getSupport_In_evalDist.
    intuition.
    eapply getSupport_In_evalDist.
    eapply H.
    rewrite <- H0.
    eapply comp_spec_impl_eq.
    trivial.
    
  Qed.
 
  Theorem OTP_inf_th_sec_l : 
    forall (x : T),
      comp_spec eq RndT (r <-$ RndT; ret (T_op x r)).

    intros.

    eapply (@comp_spec_eq_trans_l _ _ _ _ RndT (x <-$ RndT; ret x)).
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
  
    eapply comp_spec_seq.
    trivial.
    trivial.
    
    eapply comp_spec_symm.
    eapply (comp_spec_iso (T_op x) (T_op (T_inverse x))); intuition.
    rewrite <- op_assoc.
    rewrite inverse_r_ident.
    eauto.
    rewrite <- op_assoc.
    rewrite inverse_l_ident.
    eauto.

    eapply all_in_support; eauto. 

    intuition.
    subst.
    eapply comp_spec_eq_refl.
    
  Qed.

  Theorem OTP_inf_th_sec_r : 
    forall (x : T),
      comp_spec eq RndT (r <-$ RndT; ret (T_op r x)).

    intros.

    eapply (@comp_spec_eq_trans_l _ _ _ _ RndT (x <-$ RndT; ret x)).
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.

    eapply comp_spec_seq.
    trivial.
    trivial.
 
    eapply comp_spec_symm.
    eapply (comp_spec_iso (fun b => T_op b x) (fun b => T_op b (T_inverse x))); intuition.
    rewrite op_assoc.
    rewrite inverse_l_ident.
    eauto.
    rewrite op_assoc.
    rewrite inverse_r_ident.
    eauto.

    eapply all_in_support; eauto.

    intuition.
    subst.
    eapply comp_spec_eq_refl.

  Qed.

End OTP.

(* OTP for bitstrings with xor *)
Section xor_OTP.

  Variable n : nat.

  Theorem xor_OTP: 
    forall (x : Bvector n),
      comp_spec eq (Rnd n) (r <-$ Rnd n; ret (BVxor n x r)).

    eapply OTP_inf_th_sec_l; intuition.
    eapply BVxor_assoc.
    eapply BVxor_same_id.
    eapply BVxor_same_id.
    eapply BVxor_id_l.

    eapply comp_spec_rnd.
   
  Qed.

  Theorem xor_OTP_eq: 
    forall (x y : Bvector n),
       evalDist (r <-$ Rnd n; ret (BVxor n x r)) y ==
       evalDist (Rnd n) y.

    intuition.
    symmetry.
    eapply comp_spec_eq_impl_eq.
    eapply xor_OTP.

  Qed.


End xor_OTP.


(* OTP for cyclic groups *)
Require Import FCF.RndNat.
Require Import FCF.RndGrpElem.

Local Open Scope group_scope.

Section Group_OTP.

  Context`{FCG : FiniteCyclicGroup}.

  Hypothesis GroupElement_EqDec : EqDec GroupElement.
 
  Theorem group_OTP_l : 
    forall (x : GroupElement),
      comp_spec eq (RndG) (r <-$ RndG; ret (groupOp x r)).

    eapply OTP_inf_th_sec_l; intuition.
    
    apply associativity.
    eapply left_inverse.
    eapply right_inverse.
    eapply left_identity.
   
    eapply RndGrpElem_spec.
  Qed.

  Theorem group_OTP_r : 
    forall (x : GroupElement),
      comp_spec eq (RndG) (r <-$ RndG; ret (groupOp r x)).

    eapply OTP_inf_th_sec_r; intuition.
    
    apply associativity.
    eapply left_inverse.
    eapply right_inverse.
    eapply right_identity.
    eapply RndGrpElem_spec.
  Qed.

End Group_OTP.

Hint Resolve RndGrpElem_wf : wftac.
