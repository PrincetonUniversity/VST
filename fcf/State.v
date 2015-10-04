(* This file contains an earlier version of state-related definitions.  The theory from this file should be moved to Procedure.v *)

Set Implicit Arguments.

Require Import Crypto.
Require Import ProgramLogic_old.


Definition stateful_comp_spec (S D R: Set)(inv : S -> S -> Prop)(pre : (S * D) -> (S * D) -> Prop)(post : (S * R) -> (S * R) -> Prop)(c1 c2 : (S * D) -> Comp (S * R)):=
  comp_spec_old (fun a1 a2 => pre a1 a2 /\ inv (fst a1) (fst a2)) (fun b1 b2 => post b1 b2 /\ inv (fst b1) (fst b2)) c1 c2 .


Section CompLoop.

  Variable D R State : Set.
  Hypothesis S_EqDec : EqDec State.

  Fixpoint compLoop (c : (State * D) -> Comp (State * R))(count : nat)(s : State)(d : D) : Comp State :=
    match count with
      | 0 => ret s
      | S count' => 
        [s', _] <-$2 c (s, d);
        compLoop c count' s' d
    end.

  Lemma compLoop_wf : forall (o : (State * D) -> Comp (State * R)) count (s : State) (d : D),
    (forall x y, well_formed_comp (o (x, y))) ->
    well_formed_comp (compLoop o count s d).
    
    induction count; intuition;
      unfold compLoop; wftac.
    
  Qed.
  
  
  Lemma compLoop_inv : forall (c : (State * D) -> Comp (State * R)) (inv : State -> Prop) d,
    (forall s s' r,  In (s', r) (getSupport (c (s, d))) -> inv s -> inv s') ->
    forall count s s',
    inv s ->
    In s' (getSupport (compLoop c count s d)) -> inv s'.
    
    induction count; intuition; simpl in *.
    intuition; subst.
    trivial.
    
    eapply in_getUnique_if in H1.
    apply in_flatten in H1.
    destruct H1.
    intuition.
    apply in_map_iff in H2.
    destruct H2.
    intuition.
    subst.
    destruct x0.
    eapply IHcount.
    eapply H.
    eauto.
    trivial.
    trivial.

  Qed.

End CompLoop.

Class AdversaryWithOracle_concrete 
  (D_A R_A D_O R_O : Set) 
  (S_A : Set)
  (A1 : D_A -> Comp (S_A * D_O))
  (A2 : S_A -> R_O -> Comp (S_A * D_O))
  (A3 : S_A -> Comp R_A) := {
  
  S_A_EqDec : EqDec S_A;

  A1_wf : forall x, well_formed_comp (A1 x);
  A2_wf : forall x y, well_formed_comp (A2 x y);
  A3_wf : forall x, well_formed_comp (A3 x)
  
}.

Definition StatefulProc (S D R : Set) :=
  S * D -> Comp (S * R).

Section AdversaryWithOracle_concrete.

  Context `{A : AdversaryWithOracle_concrete }.
  Variable S_O : Set.
 (*  Definition Oracle := StatefulProc S_O D_O R_O. *)

  Instance eqd_S_A : EqDec S_A.
  eapply S_A_EqDec.
  Defined.

  Hypothesis R_A_EqDec : EqDec R_A.
  Hypothesis D_A_EqDec : EqDec D_A.
  Hypothesis S_O_EqDec : EqDec S_O.
  Hypothesis D_O_EqDec : EqDec D_O.
  Hypothesis R_O_EqDec : EqDec R_O.

 
  Fixpoint loopA (oracleF : StatefulProc S_O D_O R_O)(count : nat)(s_A : S_A)(s_O : S_O)(d_O : D_O) : Comp (S_A * S_O) :=
    match count with
      | 0 => ret (s_A, s_O)
      | S count' => 
        [s_O', r_O] <-$2 oracleF (s_O, d_O);
        [s_A', d_O'] <-$2 (A2 s_A r_O);
        loopA oracleF count' s_A' s_O' d_O'
    end.

  Lemma loopA_wf_inv : forall oracleF inv count s_A s_O d_O,
    inv s_O ->
    (forall s d s' r, In (s', r) (getSupport (oracleF (s, d))) -> inv s -> inv s') ->
    (forall s d, inv s -> well_formed_comp (oracleF (s, d))) ->
    well_formed_comp (loopA oracleF count s_A s_O d_O).

    induction count; intuition; simpl in *; wftac.
    eapply A2_wf.
  Qed.

  Lemma loopA_wf : forall oracleF count s_A s_O d_O,
    (forall s d, well_formed_comp (oracleF (s, d))) ->
    well_formed_comp (loopA oracleF count s_A s_O d_O).

    intuition.
    eapply (loopA_wf_inv oracleF (fun x => True)); intuition.
    
  Qed.

  Definition runA oracleF (count : nat)(s_O : S_O)(d_A : D_A) :=
    p <-$ A1 d_A;
    p' <-$ loopA oracleF count (fst p) s_O (snd p); 
    r <-$ A3 (fst p');
    ret (r, (snd p')).

  Lemma loopA_eq_compLoop : forall inv o,
    stateful_comp_spec inv (fun a b => True) (fun s b => True) o o -> 
    forall count s_O1 s_O2 s_A d_O1 d_O2 (C : Set) f1 f2 (x1 x2 : C),
    inv s_O1 s_O2 ->
    (forall s_O1' s_A s_O2', inv s_O1' s_O2' -> eqRat (evalDist (f1 (s_A, s_O1')) x1) (evalDist (f2 s_O2') x2)) ->
    eqRat (evalDist (p <-$ loopA o count s_A s_O1 d_O1; f1 p) x1) (evalDist (p <-$ compLoop _ o count s_O2 d_O2; f2 p) x2).

    induction count; intuition;
    unfold loopA, compLoop.

    comp_simp.
    eauto.

    fold loopA.
    inline_first.

    eapply H; intuition.

    inline_first.
    comp_irr_l.
    eapply A2_wf.

    comp_simp.
    eapply IHcount; intuition.
  Qed.

  Lemma runA_eq_compLoop : forall o inv,
    stateful_comp_spec inv (fun a b => True) (fun s b => True) o o -> 
    forall count s_O1 s_O2 d_A d_O (C : Set) f1 f2 (x : C),
    inv s_O1 s_O2 ->
    (forall s_O1' s_O2' s_A, inv s_O1' s_O2' -> evalDist (f1 (s_A, s_O1')) x == evalDist (f2 s_O2') x) ->
    evalDist (p <-$ runA o count s_O1 d_A; f1 p) x == evalDist (p <-$ compLoop _ o count s_O2 d_O; f2 p) x.


    intuition.
    unfold runA.
    inline_first.
    comp_irr_l.
    eapply A1_wf.
    inline_first.
    eapply (loopA_eq_compLoop H); intuition.
    inline_first.
    comp_irr_l; wftac.
    eapply A3_wf.
  Qed.

  Lemma loopA_spec_eq : forall (A : Set)(inv : S_O -> S_O -> Prop)(o1 o2 : StatefulProc S_O D_O R_O)(count : nat)(s_O1 s_O2 : S_O)(s_A : S_A)(d_O : D_O) f1 f2 (x : A),
    inv s_O1 s_O2 ->
    stateful_comp_spec inv (fun p1 p2 => snd p1 = snd p2) (fun p1 p2 => snd p1 = snd p2) o1 o2 ->
    (forall r1 r2 o1 o2 y, inv o1 o2 -> eq r1 r2 ->evalDist (f1 (r1, o1)) y == evalDist (f2 (r2, o2)) y) ->
    evalDist (p <-$ loopA o1 count s_A s_O1 d_O; f1 p) x == evalDist (p <-$ loopA o2 count s_A s_O2 d_O; f2 p) x.

    induction count; intuition.
    
    comp_ute.
    
    unfold loopA.
    fold loopA.
    inline_first.

    eapply H0;
    intuition.
    inline_first.
    
    simpl in H5.
    subst.
    comp_simp.
    inline_first.
    comp_skip.
    simpl.
    intuition.
  
  Qed.

  Lemma loopA_spec : 
    forall (A : Set)(inv : S_O -> S_O -> Prop)(o1 o2 : StatefulProc S_O D_O R_O)(count : nat)(s_O1 s_O2 : S_O)(s_A : S_A)(d_O : D_O) f1 f2 rel (x : A),
      SpecRel rel ->
      inv s_O1 s_O2 ->
      stateful_comp_spec inv (fun p1 p2 => snd p1 = snd p2) (fun p1 p2 => snd p1 = snd p2) o1 o2 ->
      (forall r1 r2 o1 o2, inv o1 o2 -> eq r1 r2 -> rel (evalDist (f1 (r1, o1)) x) (evalDist (f2 (r2, o2)) x)) ->
      rel (evalDist (p <-$ loopA o1 count s_A s_O1 d_O; f1 p) x) (evalDist (p <-$ loopA o2 count s_A s_O2 d_O; f2 p) x).

    induction count; intuition.
    comp_ute.
    eapply add_proper.
    comp_ute.
    eapply mult_proper; comp_ute.
    
    unfold loopA.
    fold loopA.
    inline_first.
    
    eapply H1; intuition.
    inline_first.
    simpl in H6.
    subst.
    comp_simp.
    inline_first.
    comp_skip.
    simpl; intuition.
    eapply IHcount; intuition.
  Qed.

  (*
  Lemma loopA_spec : forall (A : Set)(inv : S_O -> S_O -> Prop)(o1 o2 : Oracle)(count : nat)(s_O1 s_O2 : S_O)(s_A : S_A)(d_O : D_O) f1 f2 (x : A),
    inv s_O1 s_O2 ->
    stateful_comp_spec inv (fun p1 p2 => snd p1 = snd p2) (fun p1 p2 => snd p1 = snd p2) o1 o2 ->
    (forall r1 r2 o1 o2, inv o1 o2 -> eq r1 r2 ->evalDist (f1 (r1, o1)) x <= evalDist (f2 (r2, o2)) x) ->
    evalDist (p <-$ loopA o1 count s_A s_O1 d_O; f1 p) x <= evalDist (p <-$ loopA o2 count s_A s_O2 d_O; f2 p) x.

    induction count; intuition.
    comp_ute.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    eapply ratAdd_0_l.
    repeat pairInv.
    eapply H1; intuition.
    
    unfold loopA.
    fold loopA.

    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    comp_inline O O.
    eapply eqRat_refl.

    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    comp_inline 1%nat O.
    eapply eqRat_refl.

    eapply H0;
    intuition.

    simpl in H3.
    subst.

    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    comp_inline O O.
    eapply eqRat_refl.

    comp_simp.
    eapply leRat_trans.
    Focus 2.
    eapply eqRat_impl_leRat.
    comp_inline 1%nat O.
    eapply eqRat_refl.

    eapply evalDist_Bind_id_le; intuition.
    simpl. intuition.
  Qed.
*)

  Lemma loopA_spec_irr : 
    forall rel (A : Set)(pre : (S_O * D_O) -> (S_O * D_O) -> Prop) post (o1 o2 : StatefulProc S_O D_O R_O),
      SpecRel rel ->
      comp_spec_old pre post o1 o2 ->
      (forall s1 s2 r1 r2 d1 d2, post (s1, r1) (s2, r2) -> pre (s1, d1) (s2, d2)) ->
      forall (count : nat)(s_O1 s_O2 : S_O)(s_A1 s_A2 : S_A)(d_O1 d_O2 : D_O) f1 f2 (x : A),
        pre (s_O1, d_O1) (s_O2, d_O2) ->
        (forall s_O1' s_O2' r1 r2 d1 d2 s_A1' s_A2' s_A1'' s_A2'',
           post (s_O1', r1) (s_O2', r2) ->
        In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
        In (s_A2'', d2) (getSupport (A2 s_A2' r2)) ->
        pre (s_O1', d1) (s_O2', d2)) ->
        (forall s_O1' s_O2' d_O1' d_O2' s_A1' s_A2', 
           pre (s_O1', d_O1') (s_O2', d_O2') ->
           rel (evalDist (f1 (s_A1', s_O1')) x) (evalDist (f2 (s_A2', s_O2')) x)) ->
        rel (evalDist (p <-$ loopA o1 count s_A1 s_O1 d_O1; f1 p) x) (evalDist (p <-$ loopA o2 count s_A2 s_O2 d_O2; f2 p) x).

    induction count; intuition.

    comp_ute.
    repeat pairInv.
    eapply add_proper.
    eapply refl.
    intuition.
    eapply mult_proper.
    eapply refl;intuition.
    eapply H4; eauto.

    unfold loopA.  fold loopA.

    inline_first.
    eapply H0;
    intuition.
    inline_first.

    comp_irr_l.
    eapply A2_wf.
    comp_simp.
    inline_first.
    comp_irr_r.
    eapply A2_wf.
    
    comp_simp.
    eapply IHcount; intuition; eauto.
  Qed.

  Lemma loopA_spec_irr_eq : 
    forall (A : Set)(pre : (S_O * D_O) -> (S_O * D_O) -> Prop) post (o1 o2 : StatefulProc S_O D_O R_O),
      comp_spec_old pre post o1 o2 ->
      (forall s1 s2 r1 r2 d1 d2, 
         post (s1, r1) (s2, r2) -> pre (s1, d1) (s2, d2)) ->
      forall (count : nat)(s_O1 s_O2 : S_O)(s_A1 s_A2 : S_A)(d_O1 d_O2 : D_O) f1 f2 (x : A),
        pre (s_O1, d_O1) (s_O2, d_O2) ->
        (forall s_O1' s_O2' r1 r2 d1 d2 s_A1' s_A2' s_A1'' s_A2'',
           post (s_O1', r1) (s_O2', r2) ->
        In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
        In (s_A2'', d2) (getSupport (A2 s_A2' r2)) ->
        pre (s_O1', d1) (s_O2', d2)) ->
        (forall s_O1' s_O2' d_O1' d_O2' s_A1' s_A2', 
           pre (s_O1', d_O1') (s_O2', d_O2') ->
           eqRat (evalDist (f1 (s_A1', s_O1')) x) (evalDist (f2 (s_A2', s_O2')) x)) ->
        eqRat (evalDist (p <-$ loopA o1 count s_A1 s_O1 d_O1; f1 p) x) (evalDist (p <-$ loopA o2 count s_A2 s_O2 d_O2; f2 p) x).

    intuition.
    eapply loopA_spec_irr; intuition; eauto.
    eauto.
    eauto.
  Qed.

  Lemma loopA_spec_2 : 
    forall rel (A : Set)(pre1 pre2 : (S_O * D_O) -> (S_O * D_O) -> Prop) post1 post2 post3 (o1 o2 : StatefulProc S_O D_O R_O),
      SpecRel rel ->
      comp_spec_old pre1 (fun p1 p2 => (post1 p1 p2) \/ (post2 p1 p2)) o1 o2 ->
      comp_spec_old pre2 post3 o1 o2 ->
      (forall s1 s2 r1 r2, post1 (s1, r1) (s2, r2) -> r1 = r2) ->
      (forall s1 s2 r1 r2 d, post1 (s1, r1) (s2, r2) -> pre1 (s1, d) (s2, d)) ->
      (forall s1 s2 r1 r2 d1 d2, post2 (s1, r1) (s2, r2) -> pre2 (s1, d1) (s2, d2)) ->
      forall (count : nat)(s_O1 s_O2 : S_O)(s_A1 s_A2 : S_A)(d_O1 d_O2 : D_O) f1 f2 (x : A),
        (pre1 (s_O1, d_O1) (s_O2, d_O2) /\ s_A1 = s_A2) \/ pre2 (s_O1, d_O1) (s_O2, d_O2) ->
        (forall s_O1' s_O2' r1 r2 d1 d2 s_A1' s_A2' s_A1'' s_A2'',
        post3 (s_O1', r1) (s_O2', r2) ->
        In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
        In (s_A2'', d2) (getSupport (A2 s_A2' r2)) ->
        pre2 (s_O1', d1) (s_O2', d2)) ->
        (forall s_O1' s_O2' d_O1' d_O2' s_A', 
           pre1 (s_O1', d_O1') (s_O2', d_O2') ->
           rel (evalDist (f1 (s_A', s_O1')) x) (evalDist (f2 (s_A', s_O2')) x)) ->
        (forall s_O1' s_O2' d_O1' d_O2' s_A1' s_A2', 
           pre2 (s_O1', d_O1') (s_O2', d_O2') ->
           rel (evalDist (f1 (s_A1', s_O1')) x) (evalDist (f2 (s_A2', s_O2')) x)) ->
        rel (evalDist (p <-$ loopA o1 count s_A1 s_O1 d_O1; f1 p) x) (evalDist (p <-$ loopA o2 count s_A2 s_O2 d_O2; f2 p) x).
    
    induction count; intros.

    comp_ute.
    repeat pairInv.
    eapply add_proper.
    eapply refl; intuition.
    eapply mult_proper.
    eapply refl; intuition.
    eauto.

    repeat pairInv.
    eapply add_proper.
    eapply refl; intuition.
    eapply mult_proper.
    eapply refl; intuition.
    eauto.
    
    unfold loopA.
    fold loopA.
    inline_first.

    destruct H5; intuition.
    subst.
    eapply H0;
      intuition.
    comp_simp.
    inline_first.
    assert (b = r).
    eauto.
    subst.
    comp_skip.
 
    eapply IHcount; intuition.
    left.
    intuition.
    eauto.

    comp_simp.
    inline_first.
    comp_irr_l.
    eapply A2_wf.
    comp_irr_r.
    eapply A2_wf.
    comp_simp.
    eapply IHcount; intuition.
    right.
    eauto.

    eapply H1; intuition.
    comp_simp.
    inline_first.
    comp_irr_l.
    eapply A2_wf.
    comp_irr_r.
    eapply A2_wf.
    comp_simp.
    eapply IHcount; intuition.
    right.
    eauto.
  Qed.
   
    
  Lemma loopA_inv_eq : 
    forall rel (inv : S_O -> Prop)(o1 o2 : StatefulProc S_O D_O R_O)(count : nat) s_O s_A d_A x,
      SpecRel rel ->
      inv s_O ->
      (forall s d p, inv s -> In p (getSupport (o1 (s, d))) -> inv (fst p)) ->
      (forall s d p, inv s -> In p (getSupport (o2 (s, d))) -> inv (fst p)) ->
      (forall s d x, inv s -> (evalDist (o1 (s, d)) x) == (evalDist (o2 (s, d)) x)) ->
      rel (evalDist (loopA o1 count s_A s_O d_A) x) (evalDist (loopA o2 count s_A s_O d_A) x).
    
    induction count; intuition.
    comp_ute.
    
    unfold loopA.
    fold loopA.
    comp_skip.
    comp_skip.
    eapply IHcount; intuition.
    specialize (H1 s_O d_A (a0, b0)).
    simpl in H1.
    eapply H1; intuition.
  Qed.

  Lemma A_query_spec_eq : forall (inv : S_O -> S_O -> Prop)(o1 o2 : StatefulProc S_O D_O R_O),
    stateful_comp_spec inv (fun p1 p2 => (snd p1) = (snd p2)) (fun p1 p2 => (snd p1) = (snd p2)) o1 o2 ->
    forall (count : nat) s_O1 s_O2 d_A (C : Set) f1 f2 (x : C),
    inv s_O1 s_O2 ->
    (forall r1 r2 o1 o2 y, inv o1 o2 -> eq r1 r2 ->evalDist (f1 (r1, o1)) y == evalDist (f2 (r2, o2)) y) ->
    evalDist (p <-$ runA o1 count s_O1 d_A; f1 p) x == evalDist (p <-$ runA o2 count s_O2 d_A; f2 p) x.

    intuition.
    unfold runA.
    inline_first.
    comp_skip.
    inline_first.
    eapply loopA_spec_eq; eauto; intuition.
    subst.
    inline_first.
    comp_skip.
    simpl.
    intuition.
    comp_simp.
    simpl.
    intuition.
  Qed.

  Lemma A_query_spec : 
    forall rel (inv : S_O -> S_O -> Prop)(o1 o2 : StatefulProc S_O D_O R_O),
      SpecRel rel ->
      stateful_comp_spec inv (fun p1 p2 => (snd p1) = (snd p2)) (fun p1 p2 => (snd p1) = (snd p2)) o1 o2 ->
      forall (count : nat) s_O1 s_O2 d_A (C : Set) f1 f2 (x : C),
        inv s_O1 s_O2 ->
        (forall r1 r2 o1 o2, inv o1 o2 -> eq r1 r2 -> rel (evalDist (f1 (r1, o1)) x) (evalDist (f2 (r2, o2)) x)) ->
        rel (evalDist (p <-$ runA o1 count s_O1 d_A; f1 p) x) (evalDist (p <-$ runA o2 count s_O2 d_A; f2 p) x).
    
    intuition.
    unfold runA.
    inline_first.
    comp_skip.
    inline_first.
    eapply loopA_spec; eauto; intuition.
    subst.
    inline_first.
    comp_skip.
    simpl.
    intuition.
    comp_simp.
    simpl.
    intuition.
  Qed.

  Lemma A_query_spec_irr_eq : forall (inv : S_O -> S_O -> Prop) (pre : (S_O * D_O) -> (S_O * D_O) -> Prop) post (o1 o2 : StatefulProc S_O D_O R_O),
    stateful_comp_spec inv pre post o1 o2 ->
    forall (count : nat) s_O1 s_O2 d_A (C : Set) f1 f2 (x : C),
    inv s_O1 s_O2 ->
    (forall d, pre (s_O1, d) (s_O2, d)) ->
    (forall s_O1' s_O2' r1 r2 d1 d2 (* s_A1' s_A2' s_A1'' s_A2'' *),
      inv s_O1' s_O2' ->
      post (s_O1', r1) (s_O2', r2) ->
 (*     In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
      In (s_A2'', d2) (getSupport (A2 s_A2' r2)) -> *)
      pre (s_O1', d1) (s_O2', d2)) ->
    (forall s_O1' s_O2' x1 x2 z, inv s_O1' s_O2' -> evalDist (f1 (x1, s_O1')) z == evalDist (f2 (x2, s_O2')) z) ->
    evalDist (p <-$ runA o1 count s_O1 d_A; f1 p) x == evalDist (p <-$ runA o2 count s_O2 d_A; f2 p) x.

    intuition.
    unfold runA.
    inline_first.
    comp_skip.
    
    
    unfold fst, snd.
    inline_first.
    eapply loopA_spec_irr_eq; intuition.
    eapply H.
    intuition.
    intuition.
    eapply H2.
    simpl in H8.
    trivial.
    eapply H7.

    intuition.
    intuition.
    intuition.
    eapply H2.
    simpl in H10.
    trivial.
    eapply H9.

    inline_first.
    comp_irr_l.
    eapply A3_wf.
    comp_irr_r.
    eapply A3_wf.
    comp_simp.
    intuition.
  Qed.

  Lemma A_query_spec_irr : 
    forall rel (A : Set)(pre : (S_O * D_O) -> (S_O * D_O) -> Prop) post (o1 o2 : StatefulProc S_O D_O R_O),
      SpecRel rel ->
      comp_spec_old pre post o1 o2 ->
      (forall s1 s2 r1 r2 d1 d2, post (s1, r1) (s2, r2) -> pre (s1, d1) (s2, d2)) ->
      forall count (s_O1 s_O2 : S_O) d_A f1 f2 (x : A),
        (forall d, pre (s_O1, d) (s_O2, d)) ->
        (forall s_O1' s_O2' r1 r2 d1 d2 (* s_A1' s_A2' s_A1'' s_A2'' *),
           post (s_O1', r1) (s_O2', r2) ->
    (*     In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
        In (s_A2'', d2) (getSupport (A2 s_A2' r2)) -> *)
        pre (s_O1', d1) (s_O2', d2)) ->
        (forall s_O1' s_O2' d_O1' d_O2' s_A1' s_A2', 
           pre (s_O1', d_O1') (s_O2', d_O2') ->
           rel (evalDist (f1 (s_A1', s_O1')) x) (evalDist (f2 (s_A2', s_O2')) x)) ->
        rel (evalDist (p <-$ runA o1 count s_O1 d_A; f1 p) x)  (evalDist (p <-$ runA o2 count s_O2 d_A; f2 p) x).
    
    intuition.
    unfold runA.
    inline_first.
    comp_skip.
    
    unfold fst, snd.
    inline_first.
    eapply loopA_spec_irr; intuition.
    eapply H0.
    eapply H3.
    eauto.
    intuition.
    eauto.

    inline_first.
    comp_irr_l.
    eapply A3_wf.
    comp_irr_r.
    eapply A3_wf.
    comp_simp.
    eauto.
  Qed.

  Lemma A_query_inv : 
    forall rel (o1 o2 : StatefulProc S_O D_O R_O)(inv : S_O -> Prop)(count : nat) s_O d_A x,
      SpecRel rel ->
      inv s_O ->
      (forall s d p, inv s -> In p (getSupport (o1 (s, d))) -> inv (fst p)) ->
      (forall s d p, inv s -> In p (getSupport (o2 (s, d))) -> inv (fst p)) ->
      (forall s d x, inv s -> eqRat (evalDist (o1 (s, d)) x) (evalDist (o2 (s, d)) x)) ->
      rel (evalDist (p <-$ runA o1 count s_O d_A; ret fst p) x) (evalDist (p <-$ runA o2 count s_O d_A; ret fst p) x).

    intuition.
    unfold runA.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    simpl.
    eapply loopA_inv_eq; intuition; eauto.
    eauto.
    eauto.
    
    inline_first.
    comp_skip.
    comp_simp.
    comp_ute.
  Qed.

  (* This is a two-specification version of the "adversary with oracle" specification.  The first specification shows that the outputs of the oracle are the same when the inputs are the same, and the state hasn't gone bad yet.  The second specification corresponds to the case when the computation has gone "bad," and shows that badness is preserved as an invariant.  *)

  Lemma A_query_spec_2_eq : forall (A : Set)(pre1 pre2 : (S_O * D_O) -> (S_O * D_O) -> Prop) post1 post2 post3 (o1 o2 : StatefulProc S_O D_O R_O),
    comp_spec_old pre1 (fun p1 p2 => (post1 p1 p2) \/ (post2 p1 p2)) o1 o2 ->
    comp_spec_old pre2 post3 o1 o2 ->
    (forall s1 s2 r1 r2, post1 (s1, r1) (s2, r2) -> r1 = r2) ->
    (forall s1 s2 r1 r2 d, post1 (s1, r1) (s2, r2) -> pre1 (s1, d) (s2, d)) ->
    (forall s1 s2 r1 r2 d1 d2, post2 (s1, r1) (s2, r2) -> pre2 (s1, d1) (s2, d2)) ->
    forall (count : nat)(s_O1 s_O2 : S_O) d_A f1 f2 (x : A),
      (forall d, pre1 (s_O1, d) (s_O2, d)) -> 
      (forall s_O1' s_O2' r1 r2 d1 d2 (* s_A1' s_A2' s_A1'' s_A2'' *),
        post3 (s_O1', r1) (s_O2', r2) ->
      (*   In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
        In (s_A2'', d2) (getSupport (A2 s_A2' r2)) -> *)
        pre2 (s_O1', d1) (s_O2', d2)) ->
      (forall s_O1' s_O2' d_O1' d_O2' s_A', 
        pre1 (s_O1', d_O1') (s_O2', d_O2') ->
        evalDist (f1 (s_A', s_O1')) x == evalDist (f2 (s_A', s_O2')) x) ->
      (forall s_O1' s_O2' d_O1' d_O2' s_A1' s_A2', 
        pre2 (s_O1', d_O1') (s_O2', d_O2') ->
        evalDist (f1 (s_A1', s_O1')) x == evalDist (f2 (s_A2', s_O2')) x) ->
    evalDist (p <-$ runA o1 count s_O1 d_A; f1 p) x == evalDist (p <-$ runA o2 count s_O2 d_A; f2 p) x.

    intros.
    unfold runA.
    inline_first.
    comp_skip.

    inline_first.
    eapply (loopA_spec_2 _ _ _ H H0); intuition.
    eapply H5; eauto.

    inline_first.
    comp_skip.
    simpl.
    intuition.

    comp_simp.
    simpl.
    eauto.
    
    inline_first.
    comp_irr_l.
    eapply A3_wf.
    comp_irr_r.
    eapply A3_wf.
    comp_simp.
    simpl.
    eauto.
  Qed.

  Lemma A_query_spec_2 : 
    forall rel (A : Set)(pre1 pre2 : (S_O * D_O) -> (S_O * D_O) -> Prop) post1 post2 post3 (o1 o2 : StatefulProc S_O D_O R_O),
      SpecRel rel ->
      comp_spec_old pre1 (fun p1 p2 => (post1 p1 p2) \/ (post2 p1 p2)) o1 o2 ->
      comp_spec_old pre2 post3 o1 o2 ->
      (forall s1 s2 r1 r2, post1 (s1, r1) (s2, r2) -> r1 = r2) ->
      (forall s1 s2 r1 r2 d, post1 (s1, r1) (s2, r2) -> pre1 (s1, d) (s2, d)) ->
      (forall s1 s2 r1 r2 d1 d2, post2 (s1, r1) (s2, r2) -> pre2 (s1, d1) (s2, d2)) ->
      forall (count : nat)(s_O1 s_O2 : S_O) d_A f1 f2 (x : A),
      (forall d, pre1 (s_O1, d) (s_O2, d)) -> 
      (forall s_O1' s_O2' r1 r2 d1 d2 (* s_A1' s_A2' s_A1'' s_A2'' *),
         post3 (s_O1', r1) (s_O2', r2) ->
         (*   In (s_A1'', d1) (getSupport (A2 s_A1' r1)) ->
        In (s_A2'', d2) (getSupport (A2 s_A2' r2)) -> *)
         pre2 (s_O1', d1) (s_O2', d2)) ->
      (forall s_O1' s_O2' d_O1' d_O2' s_A', 
         pre1 (s_O1', d_O1') (s_O2', d_O2') ->
         rel (evalDist (f1 (s_A', s_O1')) x) (evalDist (f2 (s_A', s_O2')) x)) ->
      (forall s_O1' s_O2' d_O1' d_O2' s_A1' s_A2', 
         pre2 (s_O1', d_O1') (s_O2', d_O2') ->
         rel (evalDist (f1 (s_A1', s_O1')) x) (evalDist (f2 (s_A2', s_O2')) x)) ->
      rel (evalDist (p <-$ runA o1 count s_O1 d_A; f1 p) x) (evalDist (p <-$ runA o2 count s_O2 d_A; f2 p) x).
    
    intros.
    unfold runA.
    inline_first.
    comp_skip.

    inline_first.
    eapply (loopA_spec_2 _ _ _ H0 H1); intuition.
    eapply H6; eauto.

    inline_first.
    comp_skip.
    simpl.
    intuition.

    comp_simp.
    simpl.
    eauto.

    inline_first.
    comp_irr_l.
    eapply A3_wf.
    comp_irr_r.
    eapply A3_wf.

    comp_simp.
    simpl.
    eauto.
  Qed.
    
    
End AdversaryWithOracle_concrete.

Notation "A 'queries' f" := (@runA _ _ _ _ _ A _ _ f)
  (at level 75) : comp_scope.
