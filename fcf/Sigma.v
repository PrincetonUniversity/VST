
(* Some initial work on sigma protocols.  The goal is to prove that any sigma protocol is a proof of knowledge.  There is some interesting theory in here (e.g. the "emergency break" theorem), but it is far form complete.  

Set Implicit Arguments.

Require Import Crypto.
Require Import RndNat.

Lemma sumList_bool : forall (ls : list bool) f,
  NoDup ls ->
  (forall b, In b ls \/ (f b == 0)) ->
  sumList ls f ==
  f false + f true.
      
  intuition.

  destruct ls.
  unfold sumList.
  simpl.
  
  rewrite ratAdd_0_r.
  eapply ratAdd_eqRat_compat.
  specialize (H0 false).
  simpl in H0.
  intuition.
  specialize (H0 true).
  simpl in H0.
  intuition.
  
  inversion H; clear H; subst.
  destruct b;
    rewrite sumList_cons.
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat; intuition.
  destruct ls.
  unfold sumList. simpl.
  specialize (H0 false); intuition.
  simpl in H3, H; intuition.
  discriminate.
  inversion H4; clear H4; subst.
  destruct b.
  simpl in H3.
  intuition.
  rewrite sumList_cons.
  destruct ls.
  unfold sumList; simpl.
  rewrite <- ratAdd_0_r.
  intuition.
  destruct b; simpl in *; intuition.
  
  eapply ratAdd_eqRat_compat.
  intuition.
  destruct ls.
  unfold sumList.
  simpl.
  specialize (H0 true).
  simpl in *.
  intuition.
  discriminate.
  
  inversion H4; clear H4; subst.
  destruct b.
  rewrite sumList_cons.
  destruct ls.
  unfold sumList. simpl.
  rewrite <- ratAdd_0_r.
  intuition.
  destruct b; simpl in *; intuition.
  simpl in *; intuition.
  
Qed.

Lemma commandTwice : forall (c1 c2 : Comp bool),
  Pr [
    b1 <- c1;
    b2 <- c2;
    ret (b1 && b2)] == (Pr [c1] * Pr[c2])%rat.
  
  intuition.
  simpl.
  
  repeat rewrite sumList_bool; intuition.
  simpl.
  destruct (EqDec_dec bool_EqDec false true); try discriminate.
  destruct (EqDec_dec bool_EqDec true true); try congruence.
  repeat rewrite ratMult_0_r.
  repeat rewrite <- ratAdd_0_r.
  repeat rewrite ratMult_0_r.
  repeat rewrite <- ratAdd_0_l.
  rewrite ratMult_1_r.
  intuition.
  
  eapply getSupport_NoDup.
  Lemma in_getSupport_or_evalDist_0 : forall (A : Set)(c : Comp A) a,
    In a (getSupport c) \/ evalDist c a == 0.

    intuition.
    destruct (in_dec (comp_eq_dec c) a (getSupport c)); intuition.
    
    right.
    eapply getSupport_not_In_evalDist; intuition.
    
  Qed.
  
  Show.
  edestruct in_getSupport_or_evalDist_0.
  left.
  eauto.
  right.
  rewrite H.
  eapply ratMult_0_l.
  
  eapply getSupport_NoDup.

  edestruct in_getSupport_or_evalDist_0.
  left.
  eauto.
  right.
  rewrite H.
  eapply ratMult_0_l.

  eapply getSupport_NoDup.
  
  edestruct in_getSupport_or_evalDist_0.
  left.
  eauto.
  right.
  rewrite H.
  eapply ratMult_0_l.

Qed.

Section SigmaProtocol.

  Variable R : Blist -> Blist -> bool.
  Variable t : nat.
  Variable (Commitment Response P_State : Set) 
  (P_commit : Blist -> Blist -> Comp (P_State * Commitment))
  (V_challenge : Blist -> Commitment -> Comp (Bvector t))
  (P_respond : P_State -> Bvector t -> Comp Response)
  (V_accept :  Blist -> Commitment -> Bvector t -> Response -> bool).

  Variable extract : Blist -> Commitment -> Bvector t -> Bvector t -> Response -> Response -> Comp Blist.
  (* Also, extract must be efficient *)
  
  Variable Commitment_EqDec : EqDec Commitment.
  Variable Response_EqDec : EqDec Response.

  Definition Protocol x w :=
    [s_P, a] <--* P_commit x w;
    e <- V_challenge x a;
    z <- P_respond s_P e;
    ret (a, e, z).

  (* The ZK simulator *)
  Variable M : Blist -> Bvector t -> Comp (Commitment * Response).

  Definition G_S x :=
    e <- {0, 1}^t; 
    [a, z] <--* M x e; 
    b <- ret (V_accept x a e z);
    ret (b, (a, e, z)).

  Definition G_P x w :=
    [a, e, z] <--** Protocol x w;
    b <- ret (V_accept x a e z);
    ret (b, (a, e, z)).

  Class SigmaProtocol
    := {
      poly1 : nat -> nat;
      w_length : forall x w, R x w = true -> (length w <= poly1 (length x))%nat;
      completeness : forall x w,
          R x w = true ->
          Pr[[a, e, z] <--** Protocol x w; ret (V_accept x a e z)] == 1;
      special_soundness : forall x a e e' z z',
        e <> e' ->
        (exists w, In (a, e, z) (getSupport (Protocol x w))) ->
        (exists w, In (a, e', z') (getSupport (Protocol x w))) ->
        V_accept x a e z = true ->
        V_accept x a e' z' = true ->
        Pr[w <- extract x a e e' z z'; ret (R x w)] == 1; (* Or perhaps just non-negligible *)
      sHVZK : forall x w c,
        evalDist (G_S x) (true, c) == evalDist (G_P x w) (true,c)  
          
  }.
  
End SigmaProtocol.

Ltac destruct_exists :=
  match goal with
    | [H : exists x, _ |- _ ] =>
      destruct H
  end.

Lemma getSupport_Bind_In : forall (A B : Set) (c : Comp B)(f : B -> Comp A) a,
  In a (getSupport (Bind c f)) ->
  exists b, 
    In b (getSupport c) /\
    In a (getSupport (f b)).
  
  intuition.
  simpl in *.
  apply in_getUnique_if in H.
  eapply in_flatten in H.
  destruct H.
  intuition.
  apply in_map_iff in H0.
  destruct H0.
  intuition.
  subst.
  econstructor.
  intuition;
    eauto.
  
Qed.
  

Ltac simp_in_support := 
  match goal with
    | [H : In _ (getSupport (Bind _ _)) |- _ ] =>
      apply getSupport_Bind_In in H; destruct_exists; intuition
    | [H : In _ (getSupport (if ?t then _ else _)) |- _ ] => let x := fresh "x" in remember t as x; destruct x
    | [H : In _ (getSupport (ret _)) |- _ ] => simpl in H; intuition; try pairInv; subst
(*     | [H : false = inRange _ _ |- _] => symmetry in H *)
    | [H : true = negb ?t |- _ ] => let x := fresh "x" in remember t as x; destruct x; simpl in H; try discriminate
  end.

Lemma getSupport_In_Bind : forall (A B : Set) b (c : Comp B)(f : B -> Comp A) a,
  In b (getSupport c) ->
  In a (getSupport (f b)) ->
  In a (getSupport (Bind c f)).
  
  intuition.
  simpl.
  eapply in_getUnique.
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eapply eq_refl.
  eauto.
  trivial.
  
Qed.

(* Is this sequential or parallel? *)
(*
Section ParallelComposition.

  Context `{p : SigmaProtocol}.
  Hypothesis P_State_EqDec : EqDec P_State.

  Definition P_commit2 x w :=
    [s_P, a] <--* P_commit x w;
    [s_P', a'] <--* P_commit x w;
    ret ((s_P, s_P') , (a, a')).

  Definition V_challenge2 x (p : Commitment * Commitment) :=
    let (a, a') := p in
      e <- V_challenge x a;
      e' <- V_challenge x a';
      ret (VectorDef.append e e').

  Variable v_firstn : forall n, Bvector (n + n)%nat -> Bvector n.
  Variable v_lastn : forall n, Bvector (n + n)%nat -> Bvector n.
  Hypothesis v_firstn_correct : forall n (v1 v2 : Bvector n),  (v_firstn n (VectorDef.append v1 v2)) = v1.
  Hypothesis v_lastn_correct : forall n (v1 v2 : Bvector n),  (v_lastn n (VectorDef.append v1 v2)) = v2.
  Hypothesis firstn_lastn_correct : forall n (v : Bvector (n + n)), v = (VectorDef.append (v_firstn n v) (v_lastn n v)).

  Definition P_respond2 (p : P_State * P_State) (e : Bvector (t + t)%nat) :=
    let (s_P, s_P') := p in
    z <- P_respond s_P (v_firstn t e);
    z' <- P_respond s_P' (v_lastn t e);
    ret (z, z').

  Definition V_accept2 x (p_a : Commitment * Commitment) (e : Bvector (t + t)%nat)(p_z : Response * Response) :=
    let (a, a') := p_a in
      let (z, z') := p_z in
        b <-! V_accept x a (v_firstn t e) z;
        b' <-! V_accept x a' (v_lastn t e) z';
        (b && b').

  Definition extract2 x (p_a : Commitment * Commitment) (e1 e2 : Bvector (t + t)%nat)(p_z1 p_z2 : (Response * Response)) :=
    if (eqb (v_firstn t e1) (v_firstn t e2)) then
      extract x (snd p_a) (v_lastn t e1) (v_lastn t e2) (snd p_z1) (snd p_z2) else
        extract x (fst p_a) (v_firstn t e1) (v_firstn t e2) (fst p_z1) (fst p_z2).

  Definition M2 x (e : Bvector (t + t)%nat) : Comp ((Commitment * Commitment) * (Response * Response)) :=
    [a1, z1] <--* M x (v_firstn t e);
    [a2, z2] <--* M x (v_lastn t e);
    ret ((a1, a2), (z1, z2)).

  Theorem let_pair : forall (A B C : Type)(p : A * B)(f : A -> B -> C),
    (let (a, b) := p in f a b) = f (fst p) (snd p).

    intuition.
   
  Qed.
   
  Instance sig2 :
    SigmaProtocol R P_commit2 V_challenge2 P_respond2 V_accept2 extract2 (pair_EqDec Commitment_EqDec Commitment_EqDec) (pair_EqDec Response_EqDec Response_EqDec) M2.

  inversion p; clear p; subst.
  econstructor; intuition.
  unfold Protocol, P_commit2, V_challenge2, P_respond2, V_accept2 in *.
  specialize (completeness0 x w H).
  symmetry.
  rewrite <- ratMult_1_r.
  rewrite <- completeness0.
  rewrite <- commandTwice.
  
  symmetry.
  do 2 comp_inline O O.
  do 2 comp_inline 1%nat O.
  comp_skip.
 
  comp_inline O O.
  comp_inline 1%nat O.
  eapply eqRat_trans.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  rewrite let_pair.
  comp_ret O O.
  eapply eqRat_refl.
  comp_simp.
  do 2 comp_inline O 1%nat.
  comp_swap O O.
  comp_skip.
  comp_inline O 1%nat.
  comp_inline 1%nat O.
  eapply eqRat_trans.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  comp_ret O O.
  eapply eqRat_refl.
  comp_simp.
  do 2 comp_inline O 2%nat.

  eapply eqRat_trans.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  rewrite v_firstn_correct.
  eapply eqRat_refl.
  comp_simp.
  comp_swap O 1%nat.
  comp_swap O O.
  comp_skip.
  comp_ret 1%nat O.
  
  comp_inline O 2%nat.
  eapply eqRat_trans.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  eapply evalDist_Bind_id; intuition.
  rewrite v_lastn_correct.
  eapply eqRat_refl.
  comp_ret O O.
  comp_ret O O.
  rewrite v_firstn_correct.
  eapply evalDist_Bind_id; intuition.
  eapply eqRat_refl.
  rewrite v_lastn_correct.
  eapply eqRat_refl.
  comp_simp.

  comp_swap O 2%nat.
  comp_swap O 1%nat.
  comp_swap O O.
  comp_skip.

  do 2 comp_inline 1%nat O.
  comp_skip.
  comp_inline 1%nat O.
  comp_skip.
  comp_inline 1%nat O.
  comp_skip.
  comp_ret 1%nat O.
  unfold snd.
  comp_skip.
  

  (* second proof starts here *)
  unfold extract2.
  case_eq (eqb (v_firstn t e) (v_firstn t e')); intuition.
  apply (eqb_leibniz (v_firstn t e)) in H4.
  destruct (Bvector_eq_dec (v_lastn t e) (v_lastn t e')).
  exfalso.
  eapply H.
  rewrite firstn_lastn_correct.
  rewrite firstn_lastn_correct at 1.
  f_equal; trivial.

  unfold snd.
  eapply special_soundness0; intuition.
  destruct H0.
  exists x0.
  unfold Protocol, P_commit2, V_challenge2, P_respond2 in H0.
  unfold Protocol.
  
  repeat simp_in_support.
  destruct H0; intuition.
  repeat simp_in_support.
  destruct x2.
  repeat simp_in_support.
  destruct p.
  repeat simp_in_support.
  destruct x3.
  repeat simp_in_support.
  destruct x3.
  repeat simp_in_support.

  eapply getSupport_In_Bind.
  eapply H7.
  comp_simp.
  eapply getSupport_In_Bind.
  eapply H9.
  eapply getSupport_In_Bind.
  rewrite v_lastn_correct in H10.
  eapply H10.
  rewrite v_lastn_correct.
  simpl; intuition.

  destruct H1.
  exists x0.
  destruct z'.
  unfold Protocol, P_commit2, V_challenge2, P_respond2 in H1.
  unfold Protocol.
  repeat simp_in_support.
  destruct x1.
  repeat simp_in_support.
  destruct x2.
  destruct p.
  repeat simp_in_support.
  destruct x5.
  repeat simp_in_support.

  eapply getSupport_In_Bind.
  eapply H7.
  comp_simp.
  eapply getSupport_In_Bind.
  eapply H9.
  eapply getSupport_In_Bind.
  rewrite v_lastn_correct in H10.
  eapply H10.
  rewrite v_lastn_correct.
  simpl; intuition.
  unfold V_accept2 in *.
  destruct z'.
  rewrite commandTwice in H2.
  
 
  Lemma ratMult_r_ident : forall r1 r2,
    ~(r1 == 0) ->
    r1 * r2 == r1 ->
    r2 == 1.

    intuition.
    unfold ratMult in *.
    destruct r1.
    destruct r2.
    unfold eqRat, beqRat, ratCD in H0.
    destruct (eq_nat_dec (n * n0 * p0) (n * posnatMult p0 p1)).
    unfold posnatMult in *.
    destruct p0.
    destruct p1.
    simpl in *.
    eapply num_dem_same_rat1.
    simpl.
    rewrite (mult_comm x) in e.
    arithNormalize.
    apply mult_same_r in e; intuition.
    apply mult_same_l in e; intuition.
    assert (n = O -> False); intuition.
    eapply H.
    subst.
    eapply rat_num_0.
    congruence.
  Qed.

  Lemma ratMult_1_inverse : forall r1 r2,
    r1 * r2 == 1 ->
    r1 == ratInverse r2.

    intuition.
    unfold ratInverse.
    unfold ratMult in *.
    destruct r1.
    destruct r2.
    unfold ratCD, eqRat, beqRat in *.
    simpl in *.
    destruct (eq_nat_dec (n * n0 * 1) (posnatMult p0 p1 + 0)).
    unfold posnatMult in *.
    destruct p0.
    destruct p1.
    simpl in *.
    unfold ratCD.
    rewrite mult_1_r in *.
    rewrite plus_0_r in *.
    destruct n0.
    simpl.
    rewrite mult_0_r in *.
    symmetry in e.
    apply mult_is_O in e.
    intuition; omega.
    simpl.
    rewrite e.
    rewrite mult_comm.
    destruct (eq_nat_dec (x0 * x) (x0 * x)); congruence.
    discriminate.
  Qed.
  
  Lemma rat_prod_1 : forall r1 r2,
    r1 <= 1 ->
    r2 <= 1 ->
    r1 * r2 == 1 ->
    r1 == 1 /\ r2 == 1.

    intuition.
    
    specialize (ratMult_1_inverse _ _ H1); intuition.
    eapply leRat_impl_eqRat; intuition.
    apply ratInverse_1_swap in H0.
    rewrite H0.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H2.
    intuition.
    eapply ratMult_nz.
    intuition.
    rewrite H1 in H3.
    intuition.

    specialize (ratMult_1_inverse _ _ H1); intuition.
    eapply leRat_impl_eqRat; intuition.
    apply ratInverse_1_swap in H.
    rewrite H.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    eapply ratInverse_eqRat_compat.
    eapply ratMult_nz.
    intuition.
    rewrite ratMult_comm in H1.
    rewrite H1 in H3.
    intuition.
    eapply H2.
    rewrite ratInverse_involutive.
    intuition.
    eapply ratMult_nz; intuition.
    rewrite H1 in H3.
    intuition.
    rewrite ratMult_comm in H1.
    eapply ratMult_nz.
    intuition.
    rewrite H1 in H3.
    intuition.
  Qed.

  apply rat_prod_1 in H2.
  intuition.
  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  destruct z'.
  unfold V_accept2 in *.
  rewrite commandTwice in H3.
  apply rat_prod_1 in H3.
  intuition.

  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  (* same as above *)
  unfold fst.
  eapply special_soundness0; intuition.
  rewrite H5 in H4.
  rewrite eqb_refl in H4.
  discriminate.

  destruct H0.
  exists x0.
  unfold Protocol, P_commit2, V_challenge2, P_respond2 in H0.
  repeat simp_in_support.
  destruct H0.
  intuition.
  destruct x2.
  repeat simp_in_support.
  destruct x4.
  destruct p.
  repeat simp_in_support.
  destruct x6.
  repeat simp_in_support.

  eapply getSupport_In_Bind.
  eapply H5.
  comp_simp.
  eapply getSupport_In_Bind.
  eauto.
  eapply getSupport_In_Bind.
  rewrite v_firstn_correct in H7.
  eauto.
  rewrite v_firstn_correct.
  simpl.
  intuition.

  destruct H1.
  exists x0.
  unfold Protocol, P_commit2, V_challenge2, P_respond2 in H1.
  repeat simp_in_support.
  destruct x1.
  destruct x2.
  repeat simp_in_support.
  destruct p.
  repeat simp_in_support.
  destruct x1.
  repeat simp_in_support.
  
  eapply getSupport_In_Bind.
  eapply H5.
  comp_simp.
  eapply getSupport_In_Bind.
  eauto.
  rewrite v_firstn_correct in H9.
  eapply getSupport_In_Bind.
  eauto.
  rewrite v_firstn_correct.
  simpl. intuition.

  unfold V_accept2 in *.
  rewrite commandTwice in H2.
  apply rat_prod_1 in H2.
  intuition.
  
  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  unfold V_accept2 in *.
  destruct z'.
  rewrite commandTwice in H3.
  apply rat_prod_1 in H3.
  intuition.

  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  eapply evalDist_le_1; intuition.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).

  (* zero knowledge part starts here *)
  admit.  

  Defined.

End ParallelComposition.

*)

(*
Local Open Scope list_scope.

(* every computation is characterized by a message specification function. *)

Section EagerSampling.

  Variable v_firstn : forall n1 n2, Bvector (n1 + n2)%nat -> Bvector n1.
  Variable v_skipn : forall n1 n2, Bvector (n1 + n2)%nat -> Bvector n2.
  Hypothesis v_firstn_correct : forall n1 n2 v1 v2,  (v_firstn n1 n2 (VectorDef.append v1 v2)) = v1.
  Hypothesis v_skipn_correct : forall n1 n2 v1 v2,  (v_skipn n1 n2 (VectorDef.append v1 v2)) = v2.
  Hypothesis firstn_skipn_correct : forall n1 n2 (v : Bvector (n1 + n2)), v = (VectorDef.append (v_firstn n1 n2 v) (v_skipn n1 n2 v)).


Require Import SemEquiv.
Lemma sample_split : forall (A : Set) n1 n2 f (a : A),
  (forall v1 v2, well_formed_comp (f v1 v2)) ->
  evalDist (v <- {0, 1} ^ (n1 + n2)%nat; f (v_firstn n1 n2 v) (v_skipn n1 n2 v)) a ==
  evalDist (v1 <- {0, 1} ^ n1; v2 <- {0, 1} ^ n2; f v1 v2) a.

  intuition.
  eapply det_eq_impl_dist_sem_eq;
  wftac.
 
  unfold DetSem.evalDet_equiv.
  intuition.
  
Admitted.

Lemma evalDist_right_ident : forall (A : Set)(eqd : EqDec A)(c : Comp A) a,
  evalDist (x <- c; ret x) a == evalDist c a.
Admitted.

Lemma eager_sampling : forall (A : Set)(eqd : EqDec A)(c : Comp A),
  well_formed_comp c ->
  forall d, 
  exists t (f : Bvector t -> A), 
    (forall a,
    | evalDist (v <- {0, 1}^t; ret (f v)) a - evalDist c a | <= d) /\
    (forall a, 
      In a (getSupport (v <- {0, 1}^t; ret (f v))) -> In a (getSupport c)).

  induction 1; intuition.
  
  exists O.
  exists (fun v => a).
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  eapply evalDist_Bind_1; intuition; wftac.
  simpl.
  destruct (EqDec_dec eqd a a0); destruct (pf a a0); subst; intuition.
  eapply rat0_le_all.


  assert (nz (length (getSupport c1))).
  econstructor.
  eapply getSupport_length_nz.
  trivial.
  destruct (IHwell_formed_comp (comp_EqDec c1) (d * (1 / (length (getSupport c1))) * (1/3))).
  destruct H3.
  intuition.

  assert (forall (d : Rat) (b : B),
       In b (getSupport c1) ->
       exists (t : nat) (f : Bvector t -> A),
         (forall a : A,
          | evalDist (v <- { 0 , 1 }^t; ret f v) a - evalDist (c2 b) a | <= d) /\
         (forall a : A,
          In a (getSupport (v <- { 0 , 1 }^t; ret f v)) ->
          In a (getSupport (c2 b)))).
  intuition.
  clear H1.

  specialize (H3 (d * (1 / (length (getSupport c1))) * (1/3))).

  (*
  assert (forall b : B,
       In b (getSupport c1) ->
       exists (t : nat), forall t', t' >= t ->
         exists (f : Bvector t' -> A),
         forall a : A,
         evalDist (v <- { 0 , 1 }^t'; ret f v) a == evalDist (c2 b) a).
  intuition.
  


  Lemma maxWitness : forall (A : Set)(P_A : A -> Prop)(P : A -> nat -> Prop),
    (forall (a : A), P_A a -> exists (b : nat), forall b', b' >= b -> P a b') ->
    exists max, forall a, P_A a -> P a max.
  Admitted.
    
  *)

  assert (exists t, forall b, In b (getSupport c1) -> exists (f : Bvector t -> A),
    (forall a, | evalDist (v <- {0, 1} ^ t; ret f v) a - evalDist (c2 b) a | <= (d * (1 / (length (getSupport c1))) * (1/3))) /\
    (forall a : A,
          In a (getSupport (v <- { 0 , 1 }^t; ret f v)) ->
          In a (getSupport (c2 b)))).
  (* find max over all b in support of c1 *)
  admit.

  clear H3.
  destruct H1.
  exists (x + x1)%nat.

  Lemma witnessMap : forall (A B : Set)(P_a : A -> Prop)(P_b : A -> B -> Prop),
    (forall (a : A), P_a a -> exists (b : B), P_b a b) ->
    exists (f : A -> B),
      forall a, P_a a -> P_b a (f a).
  Admitted.

  Show.
  apply witnessMap in H1.
  destruct H1.

  exists (fun v => let b := x0 (v_firstn x x1 v) in x2 b (v_skipn x x1 v)).
  intuition.

  specialize (sample_split (fun v1 v2 => ret (x2 (x0 v1) v2))); intuition.
  rewrite H3.

  assert (forall (eqdb : eq_dec B)(eqda : eq_dec A), evalDist (v1 <- { 0 , 1 }^x; v2 <- { 0 , 1 }^x1; Ret eqda (x2 (x0 v1) v2)) a ==
     evalDist (b <- (v1 <- { 0 , 1 }^x; Ret eqdb (x0 v1)); v2 <- { 0 , 1 }^x1; Ret eqda (x2 b v2)) a).
  intuition.
  comp_inline 1%nat O.
  comp_skip.
  symmetry.
  eapply eqRat_trans.

  Theorem evalDist_left_ident' : forall (B : Set)(b : B)(eqd : eq_dec B)(A : Set)(c2 : B -> Comp A)  a,
  (evalDist (x <- Ret eqd b; (c2 x)) a) == (evalDist (c2 b) a).

    intuition.
    simpl.
    unfold sumList.
    simpl.
    destruct (eqd b b).
    rewrite <- ratAdd_0_l.
    rewrite ratMult_1_l.
    intuition.
    congruence.
    
  Qed.

  eapply evalDist_left_ident'.
  comp_simp.
  comp_ute.
  rewrite H6.

  Lemma sumList_ratDistance : forall (A : Set)(ls : list A) f1 f2 d,
    (forall a, In a ls -> | f1 a - f2 a | <= d) ->
    | sumList ls f1 - sumList ls f2 | <= (length ls / 1) * d.

    induction ls; intuition.

    unfold sumList; simpl.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    rewrite <- ratIdentityIndiscernables.
    intuition.
    eapply rat0_le_all.

    simpl in *.
    repeat rewrite sumList_cons.
    rewrite rat_distance_of_sum.
    rewrite IHls; intuition.
    assert (S (length ls) = 1 + (length ls))%nat.
    omega.
    rewrite H0.
    rewrite ratAdd_num.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    rewrite ratMult_distrib_r.
    rewrite ratMult_1_l.
    eapply eqRat_refl.
    eapply ratAdd_leRat_compat; intuition.
  
  Qed.

  Lemma evalDist_bind_distance_gen:
    forall (A B : Set) (c1 c2 : Comp B) (c3 c4 : B -> Comp A) (d : Rat),
      well_formed_comp c1 ->
      well_formed_comp c2 ->
      (forall b, well_formed_comp (c3 b)) ->
      (forall b, well_formed_comp (c4 b)) ->
      (forall b : B, | evalDist c1 b - evalDist c2 b | <= d) ->
      (forall (b : B) (a : A), In b (getSupport c1) -> | evalDist (c3 b) a - evalDist (c4 b) a | <= d) ->
      (forall a, In a (getSupport c2) -> In a (getSupport c1)) -> 
      forall a : A,
    | evalDist (x <- c1; c3 x) a - evalDist (x <- c2; c4 x) a | <= (length (getSupport c1) * 3 / 1) * d.

    intuition.
    
    simpl.

    erewrite (sumList_subset _ _ _ _ H5).

    eapply leRat_trans.
    eapply sumList_ratDistance; intuition.
    eapply ratDistance_ratMult_le.
    eapply H3.
    eapply H4.
    trivial.

    eapply evalDist_le_1; intuition.
    eapply comp_eq_dec; trivial.
    eapply evalDist_le_1; intuition.
    eapply bind_eq_dec; eauto.
    eapply evalDist_le_1; intuition.
    eapply bind_eq_dec; eauto.
    eapply evalDist_le_1; intuition.
    eapply bind_eq_dec; eauto.
    
    rewrite <- ratMult_assoc.
    rewrite <- ratMult_num_den.
    eapply ratMult_leRat_compat; intuition.
    eapply eqRat_impl_leRat.
    eapply eqRat_terms.
    omega.
    simpl.
    trivial.

    intuition.
    rewrite ratMult_0.
    left.
    eapply getSupport_not_In_evalDist.
    intuition.

    Grab Existential Variables.
    eapply getSupport_NoDup.
    eapply getSupport_NoDup.
    eapply comp_eq_dec; trivial.

  Qed.

  eapply leRat_trans.
  rewrite ratDistance_comm.

  eapply evalDist_bind_distance_gen; intuition; wftac.
  admit.
  rewrite ratDistance_comm.
  eapply H4.
  rewrite ratDistance_comm.
  eapply H1.
  trivial.

  admit.
  intuition.
  wftac.

  repeat simp_in_support.
  eapply getSupport_In_Bind.
  eapply H5.
  eapply getSupport_In_Bind.
  simpl.
  eapply in_getAllBvectors.
  simpl.
  intuition.
  eapply H1.
  eapply H5.
  eapply getSupport_In_Bind.
  simpl.
  eapply in_getAllBvectors.
  simpl.
  intuition.
  eapply getSupport_In_Bind.
  simpl.
  eapply in_getAllBvectors.
  simpl.
  intuition.

  exists n.
  exists (fun x => x).
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  eapply evalDist_right_ident.
  eapply rat0_le_all.
  simpl.
  eapply in_getAllBvectors.

  destruct (IHwell_formed_comp eqd d).
  destruct H1.
  intuition.
  
Admitted.

Inductive monte_carlo : forall (A : Set), (Comp A) -> Prop :=
| monte_carlo_ret : forall (A : Set)(eqd : eq_dec A) a,
  monte_carlo (Ret eqd a)
| monte_carlo_rnd : forall (n : nat),
  monte_carlo (Rnd n)
| monte_carlo_bind : forall (A B : Set)(c : Comp B)(f : B -> Comp A),
  monte_carlo c ->
  (forall b, In b (getSupport  c) -> monte_carlo (f b)) ->
  monte_carlo (Bind c f).

Lemma eager_sampling_strong : forall (A : Set)(eqd : EqDec A)(c : Comp A),
  monte_carlo c ->
  exists t (f : Bvector t -> A), 
    forall a,
      evalDist (v <- {0, 1}^t; ret (f v)) a == evalDist c a.

  induction c; intuition.

  exists O.
  exists (fun v => a).
  intuition.
  eapply evalDist_Bind_1; intuition.
  wftac.
  simpl.
  destruct (EqDec_dec eqd a a0); destruct (e a a0); intuition.

 
Admitted.

End EagerSampling.

*)

Section ProofOfKnowledge.

  Context `{p : SigmaProtocol}.
  
  Variable P_State_EqDec : EqDec P_State.
  Hypothesis P_commit_well_formed : forall x y, 
    well_formed_comp (P_commit x y).
  Hypothesis V_challenge_wf : forall x a,
    well_formed_comp (V_challenge x a).
  Hypothesis P_respond_well_formed : forall a b,
    well_formed_comp (P_respond a b).

  (* The definition of soundness requires us to construct a knowledge extractor that only has the public input and uses P as an oracle.  We want to make sure the knowledge extractor can't cheat by looking at the auxiliary input or the state of P.  We do this by creating an equivalent P in a monadic style that takes a function describing what to do with the information we get from P. *)

(* We need a rewindable oracle, and we create it by supplying two functions.  The first is a predicate which determines when a configuration is acceptable.  The second is a function that uses that configuration to produce some desired result.  The first function also returns some information that is used by the second function.  We can generalize this a bit by producing a list of acceptable configurations which are used by the second function.  *)

  Definition P_respond_oracle := Bvector t -> Comp Response.
  Definition rewindable_P_oracle := forall (A : Set)(eqd : EqDec A), (Commitment -> P_respond_oracle -> Comp (A * bool)) -> forall (B: Set), (A -> Commitment -> P_respond_oracle -> Comp B) -> Comp B.
  Definition mk_rewindable_P_oracle x w (A : Set)(eqd : EqDec A)(f1 : Commitment -> P_respond_oracle -> Comp (A * bool))(B : Set)(f2 : A -> Commitment -> P_respond_oracle -> Comp B)  : Comp B :=
    [p1, p2] <--* Repeat
    ([s_P, a] <--* P_commit x w; 
      p <- (f1 a (P_respond s_P));
      ret (p, (s_P, a)))
    (fun p => (snd (fst p)));
    [e, _] <-* p1;
    [s_P, a] <-* p2;
      f2 e a (P_respond s_P).

  Hypothesis unit_EqDec : EqDec unit.

  Definition P_oracle := forall (B: Set), (Commitment -> P_respond_oracle -> Comp B) -> Comp B.
  Definition mk_P_oracle x w (B : Set)(f2 : Commitment -> P_respond_oracle -> Comp B) : Comp B :=
    @mk_rewindable_P_oracle x w unit _
    (fun a b => ret (tt, true))
    _
    (fun a b c => f2 b c).

  Definition queryRow (respond_oracle : P_respond_oracle) x a :=
    e <- V_challenge x a;
    z <- respond_oracle e;
    ret (e, z).

  Definition d := 16.
  Definition emergencyBreak (x : Blist)(oracle : P_oracle) :=
    n <- [0 .. d);
    b <- oracle _ 
    (fun a resp => 
      [e, z] <--* queryRow resp x a;
      ret (V_accept x a e z));
    ret (b && eqb n O).

  Definition queryRowWithEmergencyBreak (oracle : P_oracle)(resp : P_respond_oracle)(x : Blist) a :=
    b <- emergencyBreak x oracle;
    p <- queryRow resp x a;
    ret (b, p).

  Definition to_P_oracle (o : rewindable_P_oracle)(B : Set)(f : Commitment -> P_respond_oracle -> Comp B) :=
    (@o unit _ (fun a b => ret (tt, true)) _ (fun a b c => f b c)).

  Definition acceptance_prob x y := 
    Pr[mk_P_oracle x y 
      (fun a resp => 
        [e, z] <--* queryRow resp x a;
        ret (V_accept x a e z))].

  Definition heavy (resp : P_respond_oracle) x y a :=
    (1 / 2) * acceptance_prob x y <= Pr[ [e, z] <--* queryRow resp x a; ret (V_accept x a e z) ].

  Definition isHeavy (resp : P_respond_oracle) x y a :=
    bleRat ((1 / 2) * acceptance_prob x y) (Pr[ [e, z] <--* queryRow resp x a; ret (V_accept x a e z) ]).

  Require Import Asymptotic.

  Definition knowledge_soundness(cost : forall (A : Set), A -> Rat -> Prop)(k : Blist -> Rat) :=
    forall x y (pf : nz (length x)),
      exists c, 
      let e := acceptance_prob x y in
      (~(ratSubtract e (k x)) == 0) ->
      exists (M : Blist -> rewindable_P_oracle -> Comp Blist), 
        let oracle := (mk_rewindable_P_oracle x y) in
          expected_time_at_most cost 1 (P_commit x y) ->
          (forall s c e, In (s, e) (getSupport (P_commit x y)) -> (expected_time_at_most cost 1 (P_respond s c))) ->
          expected_time_at_most cost ((expRat (length x / 1) c) * ratInverse (ratSubtract e (k x))) (M x oracle) /\
          Pr[y' <- M x oracle; ret (R x y')] == 1.
  
  (*
  Lemma evalDist_bind_case_split : forall (B : Set)(e : B -> Comp bool) v1 v2 (A : Set)(c : Comp B)(f : B -> Comp A) a,
  well_formed_comp c ->
  (forall b, (e b) = true -> (evalDist (f b) a) == v1) ->
  (forall b, (e b) = false -> (evalDist (f b) a) == v2) ->
  evalDist (Bind c f) a == Pr[Bind c e] * 
  *)

  Lemma evalDist_bind_case_split_ge : forall (B : Set)(e : B -> bool) v1 v2 (A : Set)(c : Comp B)(f : B -> Comp A) a,
  well_formed_comp c ->
  (forall b, In b (getSupport c) -> (e b) = true -> v1 <= (evalDist (f b) a)) ->
  (forall b, In b (getSupport c) -> (e b) = false -> v2 <= (evalDist (f b) a)) ->
  let v := Pr[b <- c; ret (e b)]  in
    v * v1 + (ratSubtract 1 v) * v2 <= evalDist (Bind c f) a.
  Admitted.

  Lemma evalDist_bind_spec_ge : forall (B : Set)(e : B -> bool) v (A : Set)(c : Comp B)(f : B -> Comp A) a,
    well_formed_comp c ->
    (forall b, In b (getSupport c) -> (e b) = true -> v <= (evalDist (f b) a)) ->
    Pr[b <- c; ret (e b)] * v <= evalDist (Bind c f) a.

    intuition.
    eapply leRat_trans.
    Focus 2.
    eapply (evalDist_bind_case_split_ge e); intuition.
   
    eapply rat0_le_all.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    rewrite ratMult_0_r.
    rewrite <- ratAdd_0_r.
    eapply eqRat_refl.
    intuition.
  Qed.

  Lemma filter_twice : forall (A : Set)(p1 p2 : A -> bool)(ls : list A),
    filter p1 (filter p2 ls) = filter (fun a => (p1 a) && (p2 a)) ls.
    
    induction ls; intuition; simpl in *.
    destruct (p2 a);
      simpl.
    destruct (p1 a); simpl.
    f_equal.
    intuition.
    intuition.
    
    rewrite andb_false_r.
    intuition.
  Qed.
  
  Lemma filter_pred_eq : forall (A : Set)(p1 p2 : A -> bool)(ls : list A),
    (forall a, In a ls -> p1 a = p2 a) ->
    filter p1 ls = filter p2 ls.
    
    induction ls; intuition; simpl in *.
    rewrite H.
    destruct (p2 a); intuition.
    f_equal.
    intuition.
    intuition.
  Qed.
  
  Lemma sumList_filter_prod_eq_r : forall (eqd : eq_dec bool)(A : Set)(ls : list A)(p : A -> bool) f,
    sumList (filter p ls) f ==
    sumList ls (fun a => (f a) * (if (eqd (p a) true) then 1 else 0)).
    
    intuition.
    symmetry.
    rewrite (sumList_filter_partition p0).
    eapply eqRat_trans.
    eapply ratAdd_eqRat_compat.
    eapply sumList_body_eq; intuition.
    apply filter_In in H.
    intuition.
    rewrite H1.
    destruct (eqd true true); try congruence.
    eapply ratMult_1_r.
    eapply sumList_0; intuition.
    apply filter_In in H.
    intuition.
    destruct (p0 a); simpl in *; try congruence.
    destruct (eqd false true); try congruence.
    eapply ratMult_0_r.
    symmetry.
    eapply ratAdd_0_r.
  Qed.
  
  
  Theorem emergency_break : forall (A : Set)(c : Comp A)(p1 p2 : A -> bool),
    Pr [a <- c; ret (p2 a)] <= Pr[a <-c; ret (p1 a)] ->
    (exists a, In a (getSupport c) /\ (p1 a || p2 a = true)) ->
      1 / 2 <= Pr[a <- (Repeat c (fun a => (p1 a) || (p2 a))); ret (p1 a)].
    
    intuition.
    simpl in *.

      (* first assert a fact that we'll need a few times later on. *)
    assert (~(sumList (getSupport c)
      (fun b : A =>
        evalDist c b * (if EqDec_dec bool_EqDec (p1 b) true then 1 else 0)) == 0)).
    intuition.
    assert (sumList (getSupport c)
      (fun b : A =>
        evalDist c b * (if EqDec_dec bool_EqDec (p2 b) true then 1 else 0)) ==
      0).
    eapply leRat_impl_eqRat.
    rewrite H.
    rewrite H1.
    intuition.
    eapply rat0_le_all.
    
    destruct H0.
    intuition.
    
    apply orb_true_iff in H4.
    intuition.

    eapply (sumList_0) in H1.
    assert ( evalDist c x *
      (if EqDec_dec bool_EqDec (p1 x) true then 1 else 0) == 0).
    eauto.
    rewrite H0 in H1.
    destruct (EqDec_dec bool_EqDec true true); try congruence.
    rewrite ratMult_1_r in H1.
    eapply getSupport_In_evalDist.
    eauto.
    trivial.
    trivial.
    
    eapply (sumList_0) in H2.
    assert ( evalDist c x *
      (if EqDec_dec bool_EqDec (p2 x) true then 1 else 0) == 0).
    eauto.
    rewrite H0 in H2.
    destruct (EqDec_dec bool_EqDec true true); try congruence.
    rewrite ratMult_1_r in H2.
    eapply getSupport_In_evalDist.
    eauto.
    trivial.
    trivial.
    
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    symmetry.
    eapply sumList_body_eq.
    intuition.
    apply filter_In in H2.
    intuition.
    unfold indicator.
    rewrite H4.
    rewrite ratMult_1_l at 1.
    eapply ratMult_assoc.
    
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    symmetry.
    eapply sumList_factor_constant_l.
    simpl in *.
    
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    symmetry.
    eapply ratMult_eqRat_compat.
    eapply eqRat_refl.
    rewrite (sumList_filter_partition p1).
    eapply ratAdd_eqRat_compat.
    rewrite filter_twice.
    rewrite (filter_pred_eq _ p1).
    eapply sumList_body_eq; intuition.
    apply filter_In in H2.
    intuition.
    rewrite H4.
    destruct (EqDec_dec bool_EqDec true true).
    eapply ratMult_1_r.
    congruence.
    intuition.
    destruct (p1 a); trivial.
    eapply sumList_0.
    intuition.
    apply filter_In in H2.
    intuition.
    destruct (p1 a); simpl in *; try congruence.
    destruct (EqDec_dec bool_EqDec false true); try congruence.
    eapply ratMult_0_r.
    
    eapply leRat_trans.
    Focus 2.
    eapply ratMult_leRat_compat.
    eapply ratInverse_leRat.
    destruct H0.
    eapply sumList_nz.
    exists x.
    intuition.
    eapply filter_In.
    intuition.
    eapply getSupport_In_evalDist.
    eauto.
    trivial.
    
    rewrite (sumList_filter_partition p1).
    rewrite filter_twice.
    erewrite (filter_pred_eq _ p1).
    rewrite sumList_filter_prod_eq_r.
   
    assert (sumList
      (filter (fun a : A => negb (p1 a))
        (filter (fun a : A => p1 a || p2 a) (getSupport c))) 
      (evalDist c) <= 
      (sumList (getSupport c)
        (fun b : A =>
          evalDist c b * (if EqDec_dec bool_EqDec (p2 b) true then 1 else 0)))).
    
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    eapply sumList_filter_prod_eq_r.
    
    
    assert (sumList
      (filter (fun a : A => negb (p1 a))
        (filter (fun a : A => p1 a || p2 a) (getSupport c))) 
      (evalDist c) ==
      sumList
      (filter (fun a : A => negb (p1 a))
        (filter p2 (getSupport c))) 
      (evalDist c)).
    
    repeat rewrite filter_twice.
    erewrite filter_pred_eq.
    eapply eqRat_refl.
    intuition.
    destruct (p1 a); destruct (p2 a); trivial.

    rewrite H2.
    clear H2.
    
    eapply sumList_filter_le.
    rewrite H2.
    rewrite H.
    rewrite ratMult_2.
    eapply leRat_refl.
    intuition.
    destruct (p1 a); trivial.
    
    eapply eqRat_impl_leRat.
    eapply ratAdd_0_r.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    rewrite ratInverse_ratMult.
    rewrite ratMult_comm.
    rewrite <- ratMult_assoc.
    symmetry.
    eapply ratMult_eqRat_compat.
    eapply eqRat_trans.
    eapply ratMult_eqRat_compat.
    eapply eqRat_refl.
    eapply ratInverse_eqRat_compat.
    
    trivial.
    
    symmetry.
    eapply sumList_filter_prod_eq_r.
    rewrite ratMult_comm.
    eapply ratInverse_prod_1.
    
    rewrite sumList_filter_prod_eq_r.
    eauto.
    
    simpl.
    eapply eqRat_refl.
    
    trivial.
    
    intuition.
    eapply eqRat_impl_leRat.
    rewrite ratMult_1_l.
    intuition.
  Qed.
  
  Lemma getSupport_Repeat_In : forall (A : Set)(c : Comp A) p a,
    In a (getSupport (Repeat c p)) ->
    In a (filter p (getSupport c)).
    
    intuition.
  Qed.

  Definition knowledgeExtractor_h(x : Blist)(oracle : rewindable_P_oracle)(rowQuery : (Bvector t * Response) -> Commitment -> P_respond_oracle -> Comp Blist) :=
    (oracle _ _
      (fun a respond_oracle =>
        [e, z] <--* queryRow respond_oracle x a;
        ret ((e, z), V_accept x a e z))
      _
      rowQuery).

  (* The following knowledge extractor works with probability 1/4 when acceptance_prob is "large" and the first hit is in a "heavy" row (which happens with probability at least 1/2. *)
  Definition largeRowQuery x oracle :=
    (fun p a respond_oracle =>
        [e, z] <-* p;
        p' <- Repeat 
        (queryRowWithEmergencyBreak (to_P_oracle oracle) respond_oracle x a) 
        (fun p => let (e', z') := snd p in 
          (V_accept x a e' z' && negb (eqb e e')) || fst p);
        [e', z'] <-* (snd p');
        extract x a e e' z z').

  Definition knowledgeExtractor_large_h(x : Blist)(oracle : rewindable_P_oracle) :=
    knowledgeExtractor_h x oracle (largeRowQuery x oracle).


  Definition knowledgeExtractor_large(x : Blist)(oracle : rewindable_P_oracle) :=
    Repeat (knowledgeExtractor_large_h x oracle) (fun y => R x y).
  
  Fixpoint BoundedRepeat (A : Set)(eqd : EqDec A)(n : nat)(c : Comp A)(P : A -> bool)(def : A) :=
    match n with
      | O => ret (def)
      | S n' => 
        (Bind c (fun x => if (P x) then (ret x) else (BoundedRepeat _ n' c P def)))
    end.

  Variable cost : forall (A: Set), A -> Rat -> Prop.
  Hypothesis cost_respects_equality : forall (A : Set)(a : A) r1 r2,
    cost a r1 ->
    r1 == r2 ->
    cost a r2.

  Hypothesis pair_cost : forall (A B : Set)(a : A)(b : B) r1 r2,
    cost a r1 ->
    cost b r2 ->
    cost (a, b) (r1 + r2).

  Hypothesis pair_extract_cost : forall (A B : Set)(a : A)(b : B),
    cost (a, b) 0 ->
    cost a 0 /\
    cost b 0.

  (*
  Variable t1 : Rat.
  Hypothesis P_commit_time_t1 : forall x y,
    expected_time_at_most cost t1 (P_commit x y).
  Variable t2 : Rat.
  Hypothesis V_challenge_time_t2 : forall x y,
    expected_time_at_most cost t2 (V_challenge x y).
  Variable t3 : Rat.
  Hypothesis P_respond_time_t3 : forall x y,
    expected_time_at_most cost t3 (P_respond x y).
    *)

  Hypothesis V_accept_cost : forall a b c d,
    cost (V_accept a b c d) 1.


  Lemma BoundedRepeat_cost : forall (n : nat)(A : Set)(eqd : EqDec A)(c : Comp A)(P : A -> bool) def v,
    expected_time_at_most cost v c ->
    cost def 0 ->
    let c1 :=  (ratInverse (Pr  [v <- c; ret P v ])) in
      let c2 :=  (n / 1) in
    expected_time_at_most cost (v * c2) (BoundedRepeat eqd n c P def) .

    induction n; intuition; simpl in *.
    econstructor.
    
    eapply cost_respects_equality.
    eapply H0.
    rewrite ratMult_0_r.
    intuition.
    
    econstructor.
    econstructor.
    eauto.
    intuition.
    case_eq (P a); intuition.
    eapply expected_time_R_R.
    econstructor.
    eauto.
    eapply rat0_le_all.
    eapply IHn.
    eauto.
    trivial.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.

    Lemma ratMult_S : forall r n,
      r * (S n / 1) == r + r * (n / 1).
    Admitted.

    symmetry.
    eapply ratMult_S.
    intuition.
  Qed.


  Definition smallRowQuery x :=
    (fun p a respond_oracle =>
        [e, z] <-* p;
        p' <- BoundedRepeat _ (expnat 2 (t - 2))
        (queryRow respond_oracle x a) 
        (fun p => let (e', z') := p in 
          (V_accept x a e' z' && negb (eqb e e'))) p;
        [e', z'] <-* p';
        extract x a e e' z z').

  Definition knowledgeExtractor_small_h(x : Blist)(oracle : rewindable_P_oracle) :=
    knowledgeExtractor_h x oracle (smallRowQuery x).

  Definition knowledgeExtractor_small(x : Blist)(oracle : rewindable_P_oracle) :=
    Repeat (knowledgeExtractor_small_h x oracle) (fun y => R x y).
  
  Definition sigma x y :=
    (ratSubtract ((acceptance_prob x y) * (expnat 2 t / 1)) 1).

  Hypothesis V_challenge_efficient : forall (x : Blist),
    exists v, forall a, 
    expected_time_at_most cost v (V_challenge x a) /\
    at_most_polynomial (length x / 1) v.


  (*
  Theorem knowledgeExtractor_small_h_efficient : forall x y,
    expected_time_at_most cost
     (ratInverse
        (ratSubtract (acceptance_prob x y) (1 / expnat 2 t)))
     (knowledgeExtractor_small_h x (mk_rewindable_P_oracle x y)).

    intuition.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply P_commit_time_t1.
    intuition.
    destruct a.
    econstructor.
    econstructor.
    econstructor.
    eapply V_challenge_time_t2.
    intuition.
    econstructor.
    eapply P_respond_time_t3.
    intuition.
    econstructor.
    eauto.
    intuition.
    destruct a.
    econstructor.
    eapply pair_cost.
    eauto.
    eauto.
    intuition.
    econstructor.
    eauto.
    intuition.
    destruct a.
    destruct p0.
    destruct p1.
    unfold smallRowQuery.
    destruct p0.
    econstructor.
    eapply BoundedRepeat_cost.
    unfold queryRow.
    econstructor.
    eapply V_challenge_time_t2.
    intuition.
    econstructor.
    eapply P_respond_time_t3.
    intuition.
    econstructor.
    eauto.
    
    apply pair_extract_cost in H0; intuition.
    apply pair_extract_cost in H1; intuition.

    intuition.
    destruct a.

    Focus 2.
    
    
    unfold extract.

    here
    eapply pair_cost

  Admitted.
  *)

  Check mk_rewindable_P_oracle.

  
  Theorem knowledgeExtractor_small_h_effective : forall x y,
    expnat 2 t / 1 * ratInverse (sigma x y) <=
    Pr 
    [v <- knowledgeExtractor_small_h x (mk_rewindable_P_oracle x y); ret R x v].
  Abort.

  Theorem knowledgeExtractor_small_efficient : forall x y,
    (~(4 / expnat 2 t) <= (acceptance_prob x y)) -> 
    (~ (acceptance_prob x y) <= (1 / expnat 2 t)) ->
    expected_time_at_most_polynomial cost
    ((expnat 2 t / 1) * (2 / 1 + sigma x y) * (ratInverse (sigma x y)))
    (knowledgeExtractor_small x (mk_rewindable_P_oracle x y)).

    (*
    intuition.
 
    econstructor.
  (*   eapply (@expected_time_R_Repeat _ (((expnat 2 t) / 1) * (ratInverse (sigma x y)))). *)
    econstructor.
    eapply knowledgeExtractor_small_h_efficient.
    rewrite <- ratInverse_ratMult.
    eapply ratInverse_leRat.
    intuition.
    eapply H0.
    eapply ratSubtract_0_inv.
    trivial.
    eapply leRat_trans.
    Focus 2.
    eapply ratMult_leRat_compat.
    eapply leRat_refl.
    eapply knowledgeExtractor_small_h_effective.
    unfold sigma.
    SearchAbout leRat ratSubtract 0.
    
    continue here

    apply knowledgeExtractor_small_h_effective.

    assert (expnat 2 t / 1 == (ratInverse (1 / expnat 2 t))).
    simpl.
    intuition.

    unfold sigma.
    unfold at_least_polynomial.
    exists 1%nat.
    
    simpl.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    rewrite ratMult_1_r.
    symmetry.
    eapply eqRat_trans.
    eapply ratMult_eqRat_compat.
    eapply H1.
    eapply eqRat_refl.
    rewrite <- ratInverse_ratMult.
    eapply eqRat_refl.
    intuition.
    intuition.
    admit.
    eapply ratInverse_leRat.
    intuition.
    admit.
    rewrite ratMult_comm.
    
    rewrite ratMult_ratSubtract_distrib_r.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    eapply ratSubtract_eqRat_compat.
    rewrite ratMult_assoc.
    rewrite ratMult_eq_rat1.
    eapply ratMult_1_r.
    eapply ratMult_1_l.
    intuition.
    *)

  Admitted.

  Hypothesis bvToNat_cost : forall (n : nat)(v : Bvector n) t,
    cost v t ->
    cost (bvToNat v) (t + n/1).

  Theorem knowledgeExtractor_large_h_efficient : forall x y,
    expected_time_at_most cost 1 (P_commit x y) ->
       (forall (s : P_State) (c0 : Bvector t) (e : Commitment),
        In (s, e) (getSupport (P_commit x y)) ->
        expected_time_at_most cost 1 (P_respond s c0)) ->
    expected_time_at_most cost
    (5 / 1 * (ratInverse (acceptance_prob x y)))
    (knowledgeExtractor_large_h x (mk_rewindable_P_oracle x y)).

    intuition.

    destruct (V_challenge_efficient x).

    unfold knowledgeExtractor_large_h, knowledgeExtractor_h.

    unfold mk_rewindable_P_oracle.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    intuition.
    destruct a.
    econstructor.
    econstructor.
    econstructor.
    eapply H1.
    intuition.
    econstructor.
    eapply H0.
    eapply H2.
    intuition.
    econstructor.
    eauto.
    intuition.
    destruct a.
    econstructor.
    eauto.
    intuition.
    econstructor.
    eauto.
    intuition.
    
    destruct a.
    destruct p0.
    destruct p1.
    
    unfold largeRowQuery.
    destruct p0.
    econstructor.
    unfold queryRowWithEmergencyBreak, emergencyBreak, to_P_oracle.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply RndNat_expected_time; intuition.
    unfold d.
    omega.
    intros.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eapply H.
    intros.
    destruct a0.
    econstructor.
    econstructor.
    

    here
    

  Qed.

  Theorem knowledgeExtractor_large_h_effective : forall x y,
    1 / 8 <= Pr[y' <- knowledgeExtractor_large_h x (mk_rewindable_P_oracle x y); ret (R x y')].
  Admitted.

  Theorem knowledgeExtractor_large_efficient : forall x y,
    expected_time_at_most cost 1 (P_commit x y) ->
       (forall (s : P_State) (c0 : Bvector t) (e : Commitment),
        In (s, e) (getSupport (P_commit x y)) ->
        expected_time_at_most cost 1 (P_respond s c0)) ->
    expected_time_at_most cost
    (40 / 1 * (ratInverse (acceptance_prob x y)))
    (knowledgeExtractor_large x (mk_rewindable_P_oracle x y)).

    intuition.
    econstructor.
    econstructor.
    eapply knowledgeExtractor_large_h_efficient.
    cbv beta.
    eapply leRat_trans.
    eapply ratMult_leRat_compat.
    eapply leRat_refl.
    eapply ratInverse_leRat.
    Focus 2.
    eapply knowledgeExtractor_large_h_effective.
    intuition.
    simpl.
    rewrite ratMult_comm.
    rewrite <- ratMult_assoc.
    eapply ratMult_leRat_compat; intuition.
    rewrite <- ratMult_num_den.
    simpl.
    eapply leRat_terms; intuition.
  Qed.

  Theorem knowledgeExtractor_small_wf : forall x y ,
    well_formed_comp (knowledgeExtractor_small x (mk_rewindable_P_oracle x y)).
  Admitted.

  Theorem knowledgeExtractor_large_wf : forall x y ,
    well_formed_comp (knowledgeExtractor_large x (mk_rewindable_P_oracle x y)).
  Admitted.
    
  Theorem sigma_knowledge_soundness : knowledge_soundness cost (fun x => 1 / expnat 2 t).

    unfold knowledge_soundness.
    intuition.

    (* start by splitting on acceptance_prob -- we use a different knowledge extractor when acceptance_prob is large/small *)
    destruct (le_Rat_dec (4 / expnat 2 t) (acceptance_prob x y)).
    
    (* acceptance probability is "large" *)
    exists knowledgeExtractor_large.
    intuition.

    apply knowledgeExtractor_large_efficient.
      
    eapply eqRat_trans.
    eapply evalDist_Bind_1.
    eapply knowledgeExtractor_large_wf.
    intuition.
    apply getSupport_Repeat_In in H0.
    apply filter_In in H0.
    destruct H0.
    rewrite H1.
    simpl.
    eapply eqRat_refl.
    destruct (EqDec_dec bool_EqDec true true); intuition.

    exists knowledgeExtractor_small.
    intuition.

    specialize knowledgeExtractor_small_efficient.
    intuition.
    intuition.
    eapply H.
    eapply ratSubtract_0.
    intuition.

    eapply eqRat_trans.
    eapply evalDist_Bind_1.
    eapply knowledgeExtractor_small_wf.
    intuition.
    apply getSupport_Repeat_In in H0.
    apply filter_In in H0.
    destruct H0.
    rewrite H1.
    simpl.
    eapply eqRat_refl.
    destruct (EqDec_dec bool_EqDec true true); intuition.
  Qed.







    exists knowledge

    (* we'll come back to running time *)
    admit.

    unfold knowledgeExtractor.

    unfold knowledgeExtractor, mk_rewindable_P_oracle.

    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    comp_inline 1%nat O.
    eapply eqRat_refl.

    eapply leRat_trans.
    Focus 2.

    (* Run the initial query, then case split on whether we end up in a "heavy" row. *)
    eapply (@evalDist_bind_case_split_ge _
      (fun (p : (Bvector t * Response * bool) * (P_State * Commitment)) => let (s_P, a) := (snd p) in (isHeavy (P_respond s_P) x y a))
       (1/2) (1/2) _
      (Repeat
      (z <- P_commit x y;
       [s_P, a]<-* z;
       p0 <-
       (z0 <- queryRow (P_respond s_P) x a;
        [e, z1]<-* z0; ret (e, z1, V_accept x a e z1)); 
       ret (p0, (s_P, a)))
      (fun p0 : Bvector t * Response * bool * (P_State * Commitment) =>
       [_, b]<-* fst p0; eqb b true)
      )).

    (* This is true when acceptance_prob is non-zero, which should be implied by the first case split. *)
    admit.
    intuition.
    comp_simp.

    simpl in H0.
    
    

    apply getSupport_Repeat_In in H.
    apply filter_In in H.
    destruct H.
    apply getSupport_Bind_In in H.
    destruct H.
    destruct H.
    destruct x0.
    apply getSupport_Bind_In in H2.
    destruct H2.
    destruct H2.
    apply getSupport_Bind_In in H2.
    destruct H2.
    destruct H2.
    destruct x1.
    simpl in H4.
    destruct H4.
    Focus 2.
    inversion H4.
    simpl in H3.
    destruct H3.
    Focus 2.
    inversion H3.
    inversion H3; clear H3; subst.
    inversion H4; clear H4; subst.
    simpl in H1.
    

    (* The row is heavy, so we expect to get an accepting conversation before the emergency break kicks in. *)
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    comp_inline 1%nat O.
    eapply eqRat_refl.

    eapply leRat_trans.
    Focus 2.

    eapply (evalDist_bind_spec_ge (fun p0 : bool * (Bvector t * Response) =>
       let (e', z') := snd p0 in
       V_accept x c e' z' && negb (eqb b0 e'))); intros.
    admit.
      
    destruct b.
    unfold snd in H4.
    destruct p0.
    apply andb_true_iff in H4.
    destruct H4.

    apply getSupport_Repeat_In in H3.
    apply filter_In in H3.
    destruct H3.
    simpl in H6.

    apply getSupport_Bind_In in H3.
    destruct H3.
    destruct H3.
    (* The emergency break did not fire in this case, so that part of the computation is irrelvant*)
    clear H3.

    apply getSupport_Bind_In in H2.
    destruct H2.
    destruct H2.
    apply getSupport_Bind_In in H3.
    destruct H3.
    destruct H3.
    simpl in H8.
    destruct H8; inversion H8; clear H8; subst.

    apply getSupport_Bind_In in H7.
    destruct H7.
    destruct H7.
    apply getSupport_Bind_In in H7.
    destruct H7.
    destruct H7.
    apply getSupport_Bind_In in H9.
    destruct H9.
    destruct H9.
    simpl in H8.
    destruct H8; inversion H8; clear H8; subst.
    simpl in H10.
    destruct H10.
    Focus 2.
    inversion H8.
    inversion H8; clear H8; subst.

    eapply eqRat_impl_leRat.
    symmetry.
    unfold snd.
    
    eapply special_soundness.
    eapply p.
    unfold not.
    intro.
    subst.
    rewrite (eqb_refl) in H5.
    simpl in H5.
    inversion H5.

    exists y.
    eapply getSupport_In_Bind.
    eapply H.
    comp_simp.
    eapply getSupport_In_Bind.
    eapply H2.
    eapply getSupport_In_Bind.
    eapply H3.
    simpl.
    left.
    eapply refl_equal.
    
    exists y.
    eapply getSupport_In_Bind.
    eapply H.
    comp_simp.
    eapply getSupport_In_Bind.
    eapply H7.
    eapply getSupport_In_Bind.
    eapply H9.
    simpl.
    left.
    eapply refl_equal.

    eapply eqb_true_iff.
    trivial.
    trivial.

    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    rewrite ratMult_1_r.
    eapply eqRat_refl.

    remember (queryRowWithEmergencyBreak
         (to_P_oracle
            (fun (A : Set) (eqd : EqDec A)
               (f1 : Commitment -> P_respond_oracle -> Comp (A * bool))
               (B : Set) (f2 : A -> Commitment -> P_respond_oracle -> Comp B) =>
             z <-
             Repeat
               (z <- P_commit x y;
                [s_P, a]<-* z; p0 <- f1 a (P_respond s_P); ret (p0, (s_P, a)))
               (fun p0 : A * bool * (P_State * Commitment) =>
                [_, b]<-* fst p0; eqb b true);
             (let '(e, _, (s_P, a)) := z in f2 e a (P_respond s_P))))
         (P_respond p1) x c) as exp.
    remember (fun p0 : bool * (Bvector t * Response) =>
       let (e', z') := snd p0 in
       V_accept x c e' z' && negb (eqb b0 e')) as pred1.
    remember (fun p0 : bool * (Bvector t * Response) =>
       fst p0) as pred2.

    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.

    Lemma evalDist_Repeat_pred_eq : forall (A : Set)(p1 p2 : A -> bool)(c : Comp A) a,
      (forall x, In x (getSupport c) -> p1 x = p2 x) ->
      evalDist (Repeat c p1) a == evalDist (Repeat c p2) a.
    Admitted.

    Show.
    eapply evalDist_Bind_id; intuition.
    eapply (evalDist_Repeat_pred_eq (fun x => pred1 x || pred2 x)).
    intuition.
    subst.
    destruct x0.
    unfold snd.
    destruct p0.
    
    eapply refl_equal.

    assert (evalDist (ret (pred1 x0)) true ==
   Pr 
   [ret (let (e', z') := snd x0 in V_accept x c e' z' && negb (eqb b0 e')) ]).
    subst.
    eapply eqRat_refl.
    eapply H4.

    eapply emergency_break.
    subst.

    

    Lemma eb_le_accept : forall x y c p1 b0, 
      isHeavy (P_respond p1) x y c = true ->
      Pr 
   [a <-
    queryRowWithEmergencyBreak
      (to_P_oracle
         (fun (A : Set) (eqd : EqDec A)
            (f1 : Commitment -> P_respond_oracle -> Comp (A * bool))
            (B : Set) (f2 : A -> Commitment -> P_respond_oracle -> Comp B) =>
          z <-
          Repeat
            (z <- P_commit x y;
             [s_P, a]<-* z; p0 <- f1 a (P_respond s_P); ret (p0, (s_P, a)))
            (fun p0 : A * bool * (P_State * Commitment) =>
             [_, b]<-* fst p0; eqb b true);
          (let '(e, _, (s_P, a)) := z in f2 e a (P_respond s_P))))
      (P_respond p1) x c; ret fst a ] <=
   Pr 
   [a <-
    queryRowWithEmergencyBreak
      (to_P_oracle
         (fun (A : Set) (eqd : EqDec A)
            (f1 : Commitment -> P_respond_oracle -> Comp (A * bool))
            (B : Set) (f2 : A -> Commitment -> P_respond_oracle -> Comp B) =>
          z <-
          Repeat
            (z <- P_commit x y;
             [s_P, a]<-* z; p0 <- f1 a (P_respond s_P); ret (p0, (s_P, a)))
            (fun p0 : A * bool * (P_State * Commitment) =>
             [_, b]<-* fst p0; eqb b true);
          (let '(e, _, (s_P, a)) := z in f2 e a (P_respond s_P))))
      (P_respond p1) x c;
    ret (let (e', z') := snd a in V_accept x c e' z' && negb (eqb b0 e')) ].

      intuition.
      unfold queryRowWithEmergencyBreak, to_P_oracle.
      
      remember (emergencyBreak x
      (fun (B : Set) (f : Commitment -> P_respond_oracle -> Comp B) =>
       z <-
       Repeat
         (z <- P_commit x y;
          [s_P, a]<-* z; p0 <- ret (tt, true); ret (p0, (s_P, a)))
         (fun p0 : unit * bool * (P_State * Commitment) =>
          [_, b]<-* fst p0; eqb b true);
       (let '(_, _, (s_P, a)) := z in f a (P_respond s_P)))) as c1.
      remember (queryRow (P_respond p1) x c) as c2.
      eapply leRat_trans.
      eapply eqRat_impl_leRat.
      comp_inline O O.
      comp_inline O 1%nat.
      comp_swap O O.
      eapply eqRat_refl.

      eapply leRat_trans.
      Focus 2.
      eapply eqRat_impl_leRat.
      symmetry.
      comp_inline O O.
      comp_inline O 1%nat.
      eapply eqRat_refl.

      eapply evalDist_Bind_1_le_l; intuition.
      admit.
      eapply evalDist_Bind_1_le_r; intuition.
      admit.
      
      (* The loop executes exactly once *)
      rewrite Heqc1.
      eapply leRat_trans.
      eapply eqRat_impl_leRat.
      unfold emergencyBreak.
      comp_inline O O.
      eapply evalDist_Bind_id; intros.
      eapply eqRat_refl.
      comp_inline O O.
      comp_inline O O.
      eapply evalDist_Bind_id; intros.

      Lemma evalDist_right_ident' : forall (A : Set)(eqd : EqDec A)(c : Comp A) a,
        evalDist (x <- c; ret x) a == evalDist c a.
      Admitted.

      Lemma repeat_once : forall (A : Set)(eqd : EqDec A)(c : Comp A)(P : A -> bool) a,
        (well_formed_comp c) ->
        (exists x : A, In x (filter P (getSupport c))) ->
        (forall x, In x (getSupport c) -> P x = true) ->
        evalDist (Repeat c P) a == evalDist c a.

        intuition.
        eapply eqRat_trans.
        eapply repeat_unroll.
        trivial.
        trivial.
        
        eapply eqRat_trans.
        Focus 2.
        eapply evalDist_right_ident'.
        comp_skip.
        rewrite H1; trivial.
        intuition.
      Qed.

      eapply repeat_once.
      eapply pair_EqDec.
      eapply pair_EqDec.
      eapply unit_EqDec.
      eapply bool_EqDec.
      eapply pair_EqDec.
      eapply P_State_EqDec.
      eapply Commitment_EqDec.

      eapply well_formed_Bind.
      eapply P_commit_well_formed.
      intros.
      destruct b.
      apply well_formed_Bind.
      eapply well_formed_Ret.
      intros.
      apply well_formed_Ret.

      specialize (P_commit_well_formed x y).
      apply getSupport_length_nz in P_commit_well_formed.
      remember (getSupport (P_commit x y)) as ls.
      destruct ls.
      simpl in P_commit_well_formed.
      omega.
      destruct p0.
      exists (tt, true, (p0, c0)).
      apply filter_In.
      split.
      apply (getSupport_In_Bind (p0, c0)).
      rewrite <- Heqls.
      simpl.
      left.
      eapply refl_equal.
      eapply getSupport_In_Bind.
      simpl.
      left.
      eapply refl_equal.
      simpl.
      left.
      eapply refl_equal.
      simpl.
      eapply refl_equal.
      
      intros.
      apply getSupport_Bind_In in H3.
      destruct H3.
      destruct H3.
      destruct x5.
      apply getSupport_Bind_In in H4.
      destruct H4.
      destruct H4.
      simpl in H4.
      destruct H4; inversion H4; clear H4.
      simpl in H5.
      destruct H5.
      Focus 2.
      inversion H4.
      rewrite <- H4.
      simpl.
      rewrite <- H6.
      simpl.
      eapply refl_equal.
      
      eapply eqRat_refl.
      comp_simp.
      subst.
      unfold isHeavy in *.
      
      eapply leRat_trans.
      Focus 2.
      eapply leRat_trans.
      eapply H.
      eapply eqRat_impl_leRat.
      eapply evalDist_Bind_id; intros.
      eapply eqRat_refl.
      destruct x2.
      
      symmetry.
      eapply eqRat_trans.
      eapply evalDist_left_ident.
      cbv beta.
      unfold snd.
      (* these are close *)
      
      comp_simp.
      unfold queryRow.
      
      
      SearchAbout evalDist Repeat.
      
      

      subst.
      unfold emergencyBreak, queryRow.
      clear H0.
      clear H1.
      
      

      
      eapply leRat_trans.
      eapply eqRat
      
      eapply eqRat_trans.
      eapply evalDist_Bind_id; intuition.
      eapply eqRat_refl.
      comp_inline O O.
      eapply eqRat_refl.
      eapply eqRat_refl.
      comp_simp.
      eapply eqRat_refl.
      eapply eqRat_trans.
      eapply evalDist_Bind_id; intuition.
      eapply eqRat_refl.
      eapply evalDist_Bind_id; intuition.
      eapply eqRat_refl.

      specialize (evalDist_left_ident _ (x0, x1) (fun p => ret (fst p))); intuition.
      eapply H2.
      comp_simp.
      unfold fst.
      eapply eqRat_refl.
      eapply eqRat_refl.
      eapply evalDist_Bind_id; intuition.
      eapply eqRat_refl.
      comp_ret O O.
      Qed.
   
    
continue here

    eapply evalDist_Bind_id_le;
    intuition.
    


    symmetry.
    rewrite <- Heqpred1 at 1.
    eapply eqRat_refl.
    

    Check evalDist_Repeat.

    eapply emergency_break.
    
    (* Why did I have to do this twice? *)
    eapply eqRat_impl_leRat.
    symmetry.
    comp_simp.
    
    repeat simp_in_support.
    apply getSupport_Bind_In in H3.
    destruct H3.
    destruct H3.
    clear H3.
    repeat simp_in_support.
    unfold queryRow in *.
    repeat simp_in_support.




    eapply special_soundness.
    eapply p.
    apply orb_true_iff in H6.
    intuition.
    apply andb_true_iff in H9.
    intuition.
    subst.
    rewrite eqb_refl in H11.
    simpl in H11.
    discriminate.
    
    exists y.
    eapply getSupport_In_Bind.
    eapply H.
    comp_simp.
    eapply getSupport_In_Bind.
    eapply H3.
    eapply getSupport_In_Bind.
    eapply H10.
    simpl.
    intuition.

    exists y.
    eapply getSupport_In_Bind.
    eapply H.
    comp_simp.
    eapply getSupport_In_Bind.
    eapply H3.
    eapply getSupport_In_Bind.
    eapply H10.
    simpl.
    intuition.
    

    apply getSupport_Bind_In in H2.
    destruct H2.
    destruct H2.
    apply getSupport_Bind_In in H7.
    destruct H7.
    destruct H7.
    simpl in H8.
    destruct H8; inversion H8; clear H8; subst.
    apply getSupport_Bind_In in H3.
    destruct H3.
    destruct H3.
    clear H3.
    simp_in_support.
    apply getSupport_Bind_In in H8.
    destruct H8.
    simp_in_support.
    destruct H8.
    

here

    rewrite <- ratMult_1_r.
    eapply ratMult_leRat_compat; intuition.
    
    here

    eapply emergency_break.

    Theorem repeat_disj : forall (A : Set)(c : Comp A)(p1 p2 : A -> bool)(p : A -> Comp bool),
      (forall a, p1 a = true -> Pr[p a] == 1) ->
      Pr[v <- Repeat c (fun a => p1 a || p2 a); p v] == 
      Pr[a <- c; ret (p1 a && negb (p2 a))].
      
      intuition.
      simpl.
      unfold indicator.
      rewrite sumList_body_eq.
      Focus 2.
      intuition.
      apply filter_In in H0.
      intuition.
      rewrite H2.
      rewrite ratMult_1_l at 1.
      eapply eqRat_refl.

      rewrite (sumList_filter_partition p1).

      

      repeat rewrite filter_twice.
      rewrite sumList_body_eq.
      Focus 2.
      intuition.
      rewrite H at 1.
      eapply ratMult_1_r.
      apply filter_In in H0.
      intuition.
      apply andb_true_iff in H2.
      intuition.
      

      SearchAbout filter.

  Qed.

End ProofOfKnowledge.


Section ProofOfKnowledge.

  Context `{p : SigmaProtocol}.

  Variable r_commit_length : nat.
  Variable P_commit_f : Bvector r_commit_length -> Blist -> Blist -> (P_State * Commitment).
  Variable r_respond_length : nat.
  Variable P_respond_f : Bvector r_respond_length -> P_State -> Bvector t -> Response.

  (*
  Hypothesis P_correct : forall x y e resp,
    evalDist (v <- {0, 1}^r_length; ret (P x y v e)) resp == evalDist (P_respond e) resp.
    *)

  (* completeness (non-triviality) is the same as in SigmaProtocol *)

  Variable v_firstn : forall n1 n2, Bvector (n1 + n2)%nat -> Bvector n1.
  Variable v_skipn : forall n1 n2, Bvector (n1 + n2)%nat -> Bvector n2.
  Hypothesis v_firstn_correct : forall n1 n2 v1 v2,  (v_firstn n1 n2 (VectorDef.append v1 v2)) = v1.
  Hypothesis v_skipn_correct : forall n1 n2 v1 v2,  (v_skipn n1 n2 (VectorDef.append v1 v2)) = v2.
  Hypothesis firstn_skipn_correct : forall n1 n2 (v : Bvector (n1 + n2)), v = (VectorDef.append (v_firstn n1 n2 v) (v_skipn n1 n2 v)).

  Definition Protocol_f x w r :=
    r1 <-! v_firstn r_commit_length r_respond_length r;
    r2 <-! v_skipn r_commit_length r_respond_length r;
    [s_P, a] <-* P_commit_f r1 x w;
    e <- V_challenge x a;
    z <-! P_respond_f r2 s_P e;
    ret (a, e, z).

  Definition little_p x w r := Pr[[a, e, z] <--** Protocol_f x w r; V_accept x a e z].

  Local Open Scope list_scope.
  Definition knowledgeExtractor (x : Blist)(P : Bvector t -> Response) := ret (false :: nil).

  Definition knowledge_soundness(k : nat -> Rat) :=
    forall x y r,
      let r1 := v_firstn r_commit_length r_respond_length r in
      let r2 := v_skipn r_commit_length r_respond_length r in
      let (s_P, a) := P_commit_f r1 x y in
      (ratSubtract (little_p x y r) (k (length x))) <= Pr[y' <- knowledgeExtractor x (P_respond_f r2 s_P); ret (R x y')].

  Theorem sigma_knowledge_soundness : knowledge_soundness (fun x => 1 / expnat 2 x).

    unfold knowledge_soundness.
    intuition.
    

  Qed.

End ProofOfKnowledge.






Section SigmaProtocolDefs.

  Context`{p : SigmaProtocol}.

  

End SigmaProtocolDefs.

Class SigmaProtocol`(p : SigmaProtocolProcs) := {

  completeness : forall x w,
    R x w = true ->
    Pr[[a, e, z] <--** Protocol x w; V_accept x a e z] == 1

  }.

  Definition completeness := forall x w,
    R x w = true ->
    Pr[[a, e, z] <--** Protocol x w; V_accept x a e z] == 1.

  

  Definition special_soundness := forall x a e e' z z',
    e <> e' ->
    (exists w, In (a, e, z) (getSupport (Protocol x w))) ->
    (exists w, In (a, e', z') (getSupport (Protocol x w))) ->
    Pr[V_accept x a e z] == 1 ->
    Pr[V_accept x a e' z'] == 1 ->
    Pr[w <- extract x a e e' z z'; ret (R x w)] == 1. (* Or perhaps just non-negligible *)

  (* The ZK simulator *)
  Variable M : Blist -> Bvector t -> Comp (Commitment * Response).

  Definition G_S x :=
    e <- {0, 1}^t; 
    [a, z] <--* M x e; 
    b <- V_accept x a e z;
    ret (b, (a, e, z)).

  Definition G_P x w :=
    [a, e, z] <--** Protocol x w;
    b <- V_accept x a e z;
    ret (b, (a, e, z)).

  (* special honest verifier zero knowledge *)
  Definition sHVZK := forall x w c,
    evalDist (G_S x) (true, c) == evalDist (G_P x w) (true,c).  

End SigmaProtocolDefs.

Section SigmaPar.
  
  Context`{p : SigmaProtocol}.

End SigmaPar.

Section Sigma.

  Variable R : Blist -> Blist -> bool.
  Variable poly1 : nat -> nat.
  Hypothesis w_length : forall x w,
    R x w = true -> (length w <= poly1 (length x))%nat.
  Variable t : nat. (* Challenge length *)

  Variable Commitment : Set.
  Variable Response : Set.
  Hypothesis Commitment_EqDec : EqDec Commitment.
  Hypothesis Response_EqDec : EqDec Response.

  Variable P_State : Set.

  Variable P_commit : Blist -> Blist -> Comp (P_State * Commitment).
  Variable V_challenge : Blist -> Commitment -> Comp (Bvector t).
  Variable P_respond : P_State -> Bvector t -> Comp Response.
  Variable V_accept :  Blist -> Commitment -> Bvector t -> Response -> Comp bool.

  Definition Protocol x w :=
    [s_P, a] <--* P_commit x w;
    e <- V_challenge x a;
    z <- P_respond s_P e;
    ret (a, e, z).

  Hypothesis completeness : forall x w,
    R x w = true ->
    Pr[[a, e, z] <--** Protocol x w; V_accept x a e z] == 1.

  Variable extract : Blist -> Commitment -> Bvector t -> Bvector t -> Response -> Response -> Comp Blist.
  (* Also, extract must be efficient *)

  Hypothesis special_soundness : forall x a e e' z z',
    e <> e' ->
    (exists w, In (a, e, z) (getSupport (Protocol x w))) ->
    (exists w, In (a, e', z') (getSupport (Protocol x w))) ->
    Pr[V_accept x a e z] == 1 ->
    Pr[V_accept x a e' z'] == 1 ->
    Pr[w <- extract x a e e' z z'; ret (R x w)] == 1. (* Or perhaps just non-negligible *)

  (* The ZK simulator *)
  Variable M : Blist -> Bvector t -> Comp (Commitment * Response).

  Definition G_S x :=
    e <- {0, 1}^t; 
    [a, z] <--* M x e; 
    b <- V_accept x a e z;
    ret (b, (a, e, z)).

  Definition G_P x w :=
    [a, e, z] <--** Protocol x w;
    b <- V_accept x a e z;
    ret (b, (a, e, z)).

  (* special honest verifier zero knowledge *)
  Hypothesis sHVZK : forall x w c,
    evalDist (G_S x) (true, c) == evalDist (G_P x w) (true,c).  

End Sigma.

Section SigmaPar.

  Variable R : Blist -> Blist -> bool.
  Variable poly1 : nat -> nat.
  Hypothesis w_length : forall x w,
    R x w = true -> (length w <= poly1 (length x))%nat.
  Variable t : nat. (* Challenge length *)

  Variable Commitment : Set.
  Variable Response : Set.
  Hypothesis Commitment_EqDec : EqDec Commitment.
  Hypothesis Response_EqDec : EqDec Response.

  Variable P_State : Set.

  Variable P_commit : Blist -> Blist -> Comp (P_State * Commitment).
  Variable V_challenge : Blist -> Commitment -> Comp (Bvector t).
  Variable P_respond : P_State -> Bvector t -> Comp Response.
  Variable V_accept :  Blist -> Commitment -> Bvector t -> Response -> Comp bool.

  Definition proto_par_2 x w :=
    c <- (Protocol Commitment_EqDec Response_EqDec P_commit V_challenge P_respond) x w;
    c' <- (Protocol Commitment_EqDec Response_EqDec P_commit V_challenge P_respond) x w;
    ret (c, c').
    
  

End SigmaPar.