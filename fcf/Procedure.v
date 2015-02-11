
(* Definitions and theory related to "procedures" -- functions that return computations and special forms of the same.  
*)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import MCF.
Require Import CompFold.
(* Require Import ProgramLogic_old. *)

Local Open Scope type_scope.

Record ProcedureWithOracle
  (D_P R_P D_O R_O : Set) := {
    q : nat;
    S_P : Set;
    P1 : D_P -> Comp (D_O * S_P);
    P2 : S_P -> R_O -> Comp (D_O * S_P);
    P3 : S_P -> R_O -> Comp R_P;

    P1_wf : forall x, well_formed_comp (P1 x);
    P2_wf : forall x y, well_formed_comp (P2 x y);
    P3_wf : forall x y, well_formed_comp (P3 x y);

    S_P_EqDec : EqDec S_P;
    D_O_EqDec : EqDec D_O;
    R_O_EqDec : EqDec R_O;
    R_P_EqDec : EqDec R_P

      }.


Section CompLoop.

  Variable A : Set.
  Hypothesis eqd : EqDec A.
  
  Variable c : A -> Comp A.
  Hypothesis c_wf : forall a, well_formed_comp (c a).

  Definition compLoop n (a : A) : Comp A :=
    compFold _ (fun a n => c a) a (allNatsLt n).

  Theorem compLoop_wf : forall n a,
    well_formed_comp (compLoop n a).

    intuition.
    eapply compFold_wf; intuition.
  Qed.

End CompLoop.

Theorem compLoop_O : 
  forall (A : Set)(eqda : EqDec A)(c : A -> Comp A) a,
    (compLoop _ c O a) = ret a.

  intuition.
 
Qed.

Theorem compLoop_S : 
  forall (A : Set)(eqda : EqDec A)(c : A -> Comp A) n a x,
    evalDist (compLoop _ c (S n) a) x == 
    evalDist (a0 <-$ c a; compLoop eqda c n a0) x.

  induction n; intuition.
  unfold compLoop, allNatsLt.
  rewrite app_nil_l.
  unfold compFold.
  intuition.

  unfold compLoop, allNatsLt.
  fold allNatsLt.

  eapply eqRat_trans.
  rewrite compFold_app.
  eapply evalDist_seq_eq.
  intros.
  eapply IHn.
  intros.
  eapply eqRat_refl.
  dist_inline_first.
  comp_skip.
  unfold compLoop.
  eapply eqRat_trans.
  symmetry.
  eapply compFold_app.

  eapply comp_spec_eq_impl_eq.
  eapply (@compFold_eq _ _ (fun x y => True)).
  eapply list_pred_I.
  repeat rewrite app_length.
  simpl; intuition.

  intuition.
  eapply eq_impl_comp_spec_eq.
  intuition.
Qed.


Theorem compLoop_spec : 
  forall (A B : Set){e1 : EqDec A}{e2 : EqDec B}(P : A -> B -> Prop)(c1 : A -> Comp A)(c2 : B -> Comp B) n a b,
    (forall x y, P x y -> comp_spec P (c1 x) (c2 y)) ->
    P a b ->
    comp_spec P (compLoop e1 c1 n a) (compLoop e2 c2 n b).

  induction n; intuition.
  unfold compLoop.
  simpl.
  eapply comp_spec_ret; intuition.

  unfold compLoop in *.
  simpl.
  eapply comp_spec_eq_trans.
  eapply eq_impl_comp_spec_eq.
  intros.
  eapply compFold_app.
  eapply comp_spec_eq_trans_r.
  Focus 2.
  eapply comp_spec_eq_symm.
  eapply eq_impl_comp_spec_eq.
  intros.
  eapply compFold_app.
  eapply comp_spec_seq; intuition.
  simpl.
  eapply comp_spec_seq; intuition.
  eapply comp_spec_ret; intuition.
Qed.

Theorem compLoop_eq : 
  forall (A : Set){e1 e2 : EqDec A}(c1 c2 : A -> Comp A) n a x,
    (forall x y, evalDist (c1 x) y == evalDist (c2 x) y) ->
    evalDist (compLoop e1 c1 n a) x == evalDist (compLoop e2 c2 n a) x.

  intuition.
  eapply (@comp_spec_eq_impl_eq _ e1 e2).
  eapply compLoop_spec; intuition.
  subst.
  eapply eq_impl_comp_spec_eq.
  eapply H.

Qed.

Section RunP2.

  Variable S_P D_O R_O : Set.
  Variable P2 : S_P -> R_O -> Comp (D_O * S_P).
  Variable S_O : Set. 
  Variable P_O : S_O -> D_O -> Comp (R_O * S_O).  

  Hypothesis S_O_EqDec : EqDec S_O.
  Hypothesis S_P_EqDec : EqDec S_P.
  Hypothesis D_O_EqDec : EqDec D_O.

  Definition runP2_once (p : S_O * S_P * D_O) :=
    [s_O, s_P, d] <-3 p;
    [r, s_O] <-$2 P_O s_O d;
    [d, s_P] <-$2 P2 s_P r;
    ret (s_O, s_P, d).
  
  Definition runP2 q s_O s_P d := compLoop _ runP2_once q (s_O, s_P, d).

End RunP2.

Section RunWithOracle.
  
  Variable D_P R_P D_O R_O : Set.
  Variable (P : ProcedureWithOracle D_P R_P D_O R_O).
  Variable (d_P : D_P).

  Variable S_O : Set.
  Hypothesis S_O_EqDec : EqDec S_O.
  Variable P_O : S_O -> D_O -> Comp (R_O * S_O).

  Hint Resolve P.(S_P_EqDec) : typeclass_instances.
  Hint Resolve P.(D_O_EqDec) : typeclass_instances.
  Hint Resolve P.(R_P_EqDec) : typeclass_instances.

  Definition runPWO s_O :=
    [d, s_P] <-$2 P.(P1) d_P;
    [s_O, s_P, d] <-$3 runP2 (@P2 _ _ _ _ P) P_O _ _ _ P.(q) s_O s_P d;
    [r, s_O] <-$2 P_O s_O d;
    r_P <-$ P3 s_P r;
    ret (s_O, r_P).

End RunWithOracle.

Arguments runPWO {D_P R_P D_O R_O} P d_P {S_O S_O_EqDec} P_O s_O.

(*
Definition runPWO(R_P D_O R_O : Set)(q : nat)(P: ProcedureWithOracle R_P D_O R_O q) 
  (S_O : Set)(eqd_S_O : EqDec S_O)(oracle : S_O -> D_O -> Comp (R_O * S_O)) :=
  runProcedureWithOracle P _ oracle.
*)

Coercion runPWO : ProcedureWithOracle >-> Funclass.

Definition oracleWrap
  (D_O R_O S_O D_O' R_O' S_W : Set)
  (eqd_R_O' : EqDec R_O')
  (eqd_S_O : EqDec S_O)
  (oracle : S_O -> D_O -> Comp (R_O * S_O))
  (WD : D_O' -> Comp (D_O * S_W))
  (WR : S_W -> R_O -> Comp R_O') : S_O -> D_O' -> Comp (R_O' * S_O) :=
  fun s_O d_O' =>
    [d_O, s_W] <-$2 WD d_O';
    [r_O, s_O] <-$2 oracle s_O d_O;
    r_O' <-$ WR s_W r_O;
    ret (r_O', s_O).

Section PWO_Wrap.

  Variable D_P R_P D_O R_O : Set.
  Variable (P : ProcedureWithOracle D_P R_P D_O R_O).

  Hint Resolve P.(S_P_EqDec) : typeclass_instances.
  Hint Resolve P.(R_O_EqDec) : typeclass_instances.

  Variable D_O' R_O' S_W : Set.
  Variable WD : D_O -> Comp (D_O' * S_W).
  Variable WR : S_W -> R_O' -> Comp R_O.

  Hypothesis WD_wf : forall x, well_formed_comp (WD x).
  Hypothesis WR_wf : forall x y, well_formed_comp (WR x y).

  Hypothesis D_O'_EqDec : EqDec D_O'.
  Hypothesis R_O'_EqDec : EqDec R_O'.
  Hypothesis S_W_EqDec : EqDec S_W.

  Definition PWO_Wrap_P1 d_P :=
    [d_O, s_P] <-$2 P.(P1) d_P;
    [d_O', s_W] <-$2 WD d_O;
    ret (d_O', (s_P, s_W)).

  Theorem PWO_Wrap_P1_wf :
    forall x, well_formed_comp (PWO_Wrap_P1 x).

    intuition.
    unfold PWO_Wrap_P1.
    wftac.
    eapply P1_wf.
    
  Qed.

  Definition PWO_Wrap_P2 s_Ps r_O' :=
    [s_P, s_W] <-2 s_Ps;
    r_O <-$ WR s_W r_O';
    [d_O, s_P] <-$2 P2 s_P r_O;
    [d_O', s_W] <-$2 WD d_O;
    ret (d_O', (s_P, s_W)).

  Theorem PWO_Wrap_P2_wf :
    forall x y, well_formed_comp (PWO_Wrap_P2 x y).

    intuition.
    unfold PWO_Wrap_P2.
    wftac.
    eapply P2_wf.
  Qed.

  Definition PWO_Wrap_P3 (s_Ps : P.(S_P) * S_W) r_O' :=
    [s_P, s_W] <-2 s_Ps;
    r_O <-$ WR s_W r_O';
    P3 s_P r_O.

  Theorem PWO_Wrap_P3_wf :
    forall x y, well_formed_comp (PWO_Wrap_P3 x y).

    intuition.
    unfold PWO_Wrap_P3.
    wftac.
    intuition.
    eapply P3_wf.
  Qed.

  Definition PWO_Wrap : ProcedureWithOracle D_P R_P D_O' R_O'.

    econstructor.
    eapply P.(q).

    eapply PWO_Wrap_P1_wf.
    eapply PWO_Wrap_P2_wf.
    eapply PWO_Wrap_P3_wf.

    intuition.
    intuition.
    intuition.
    eapply P.(R_P_EqDec).
  Defined.

  Variable S_O : Set.
  Variable S_O_EqDec : EqDec S_O.
  Variable O : S_O -> D_O' -> Comp (R_O' * S_O).

  (*
  Theorem PWO_Wrap_equiv : 
    forall d_P s_O x e1 e2 e3 e4, 
    evalDist (P _ e1 (oracleWrap e2 e3 O WD WR) d_P s_O) x ==
    evalDist (PWO_Wrap _ e4 O d_P s_O) x.
  Admitted.
  *)

End PWO_Wrap.

Theorem sum_eq_dec : forall (A B : Set),
    eq_dec A ->
    eq_dec B ->
    eq_dec (A + B).

  intuition.
  unfold eq_dec in *.
  intuition.
  destruct (H a a0); subst; intuition.
  right.
  intuition.
  inversion H1; clear H1; subst.
  intuition.

  right.
  intuition.
  inversion H1.

  right. 
  intuition.
  inversion H1.

  destruct (H0 b b0).
  subst; intuition.

  right.
  intuition.
  inversion H1; clear H1; subst.
  intuition.
Qed.

Instance sum_EqDec : forall (A B : Set),
    EqDec A ->
    EqDec B ->
    EqDec (A + B).

  intuition.
  eapply dec_EqDec.

  eapply sum_eq_dec.
  specialize (EqDec_dec H); intuition.
  specialize (EqDec_dec H0); intuition.
Qed.

Section PWO_Seq.

  Variable D1 R1 DO RO : Set.
  Variable (PWO_P1 : ProcedureWithOracle D1 R1 DO RO).
  Variable R2 : Set.
  Variable (PWO_P2 : ProcedureWithOracle R1 R2 DO RO).

  Hint Resolve PWO_P1.(S_P_EqDec) : typeclass_instances.
  Hint Resolve PWO_P2.(S_P_EqDec) : typeclass_instances.
  Hint Resolve PWO_P1.(D_O_EqDec) : typeclass_instances.
  Hint Resolve PWO_P2.(R_P_EqDec) : typeclass_instances.
  
  Definition S_P' := (nat * (PWO_P1.(S_P) + PWO_P2.(S_P))).

  Definition PWO_Seq_P1 (d : D1) : Comp (DO * S_P') :=
    [d, s] <-$2 PWO_P1.(P1) d;
    ret (d, (PWO_P1.(q), inl s)).

  Theorem PWO_Seq_P1_wf : 
    forall x,
      well_formed_comp (PWO_Seq_P1 x).

    intuition.
    unfold PWO_Seq_P1.
    wftac.
    eapply P1_wf.

  Qed.

  Definition PWO_Seq_P2 (s : S_P') (r : RO)  : Comp (DO * S_P') :=
    match (snd s) with
      | inl s' =>
        match (fst s) with
          | O => 
            r <-$ P3 s' r;
            [d', s'] <-$2 PWO_P2.(P1) r;
            ret (d', (O, inr s'))
          | S q' =>
            [d', s'] <-$2 P2 s' r;
            ret (d', (q', inl s'))
        end
      | inr s' =>
        [d', s'] <-$2 P2 s' r;
        ret (d', (O, inr s'))
    end.

  Theorem PWO_Seq_P2_wf : 
    forall x y,
      well_formed_comp (PWO_Seq_P2 x y).

    intuition.
    unfold PWO_Seq_P2.
    destruct (snd x); destruct (fst x); wftac.
    eapply P3_wf.
    eapply P1_wf.
    eapply P2_wf.
    eapply P2_wf.
    eapply P2_wf.

  Qed.

  Variable R2_def : R2.

  Definition PWO_Seq_P3 (s : S_P') r : Comp R2 :=
    match (snd s) return (Comp R2) with
      | inl s' => ret R2_def
      | inr s' => P3 s' r
    end.

  Theorem PWO_Seq_P3_wf : 
    forall x y,
      well_formed_comp (PWO_Seq_P3 x y).

    intuition.
    unfold PWO_Seq_P3.
    destruct (snd x); wftac.
    eapply P3_wf.

  Qed.

        
  Definition PWO_Seq : ProcedureWithOracle D1 R2 DO RO.

  econstructor.
  eapply (S (PWO_P1.(q) + PWO_P2.(q)))%nat.
  eapply PWO_Seq_P1_wf.
  eapply PWO_Seq_P2_wf.
  eapply PWO_Seq_P3_wf.
  unfold S_P'.
  intuition.
  intuition.
  eapply PWO_P1.(R_O_EqDec).
  intuition.

  Defined.

  (*
  Theorem PWO_Seq_runP2 : 
    forall n (S_O : Set) (s_O : S_O)(S_O_EqDec : EqDec S_O)(RO_EqDec : EqDec RO)
      m s_P d_O o x, 
      evalDist 
      (
        [s_O, s_P, d_O] <-$3 runP2 (@P2 _ _ _ _ PWO_P1) o _ _ _ n s_O s_P d_O;
        [r_O, s_O] <-$2 o s_O d_O;
        r_P1 <-$ P3 s_P r_O;
        [d_O, s_P] <-$2 PWO_P2.(P1) r_P1;
        [s_O, s_P, d_O] <-$3 runP2 (@P2 _ _ _ _ PWO_P2) o _ _ _ m s_O s_P d_O;
      ret (s_O, (0%nat, inr s_P), d_O)) x == 
      evalDist (runP2 (PWO_Seq_P2) o _ _ _ (S (n + m)) s_O (n, inl s_P) d_O) x.

    induction n; intros.

    rewrite plus_0_l.
    unfold runP2.
    rewrite compLoop_O.
    dist_ret_l.
    unfold setLet.
    rewrite compLoop_S.
    unfold runP2_once.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.
    destruct x0.
    
    unfold PWO_Seq_P2.    
    unfold snd, fst.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.
    destruct x1.
    dist_ret_r.
    unfold setLet.
    dist_ret_r.

    symmetry.
    rewrite <- evalDist_right_ident.
    symmetry.

    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; intuition.
    admit.
    admit.
    eapply (@compLoop_spec _ _ _ _
      (fun (x : S_O * S_P PWO_P2 * DO) (y :  S_O * S_P' * DO) => snd x = snd y /\ fst (fst x) = fst (fst y) /\ (0, inr (snd (fst x))) = snd (fst y)))%nat; intros.
    intuition.
    

    destruct x.
    destruct y.
    destruct p.
    destruct p0.
    simpl in H2.
    simpl in H5.
    simpl in H3.
    subst.
    comp_skip.
    admit.

    eapply comp_spec_symm.
    eapply comp_spec_eq_trans.
    
    specialize (@comp_spec_assoc _ _ _ _ (P2 (p:=PWO_P2) s2 a3) (fun z => [d', s']<-2 z; ret (d', (0, inr s'))) (fun z => [d0, s_P0]<-2 z; ret (b0, s_P0, d0))); intuition.
    

    (*
    Ltac prog_inline_r :=
  match goal with
    | [ |- comp_spec _ _ _ ] => 
          eapply comp_spec_eq_trans_r; [idtac | eapply comp_spec_symm;
  eapply comp_spec_consequence; [
  eapply comp_spec_assoc |
  intuition] ]
  end.
  *)
  
       Ltac prog_inline_r :=
  match goal with
    | [ |- comp_spec _ _ _ ] => 
          eapply comp_spec_eq_trans_r; [idtac | eapply comp_spec_symm;
  eapply comp_spec_consequence; [
  eapply comp_spec_assoc |
  intuition] ]
  end.
  
       Show.
       eapply comp_spec_eq_trans_r.
       Focus 2.
       eapply comp_spec_symm.
       eapply comp_spec_consequence.

       assert (EqDec DO).
       admit.
       specialize (@comp_spec_assoc _ _ _ _ (P2 (p:=PWO_P2) s2 a3) (fun z => [d', s']<-2 z; ret (d', (0, inr s')))); intros.
       eapply H4.
       
       eapply comp_spec_assoc.

    Show.
    prog_inline_r.

    inline_first.
    eapply comp_spec_seq.
    admit.
    admit.
    eapply comp_spec_eq_refl.
    intuition.
    subst.
    
    comp_skip.

    unfold comp_spec_post; intros.
    destruct H2.
    destruct H5.
    destruct y.
    destruct x1.
    simpl in H2.
    simpl in H5.
    destruct p0.
    destruct p.
    simpl in H5.
    subst.
    comp_simp.
    inline_first.
    eapply evalDist_seq.
    intuition.
    intuition.
    intros.
    subst.
    comp_simp.
    simpl in H6.
    inversion H6; clear H6; subst.
    inline_first.
    eapply evalDist_seq.
    intuition.
    intuition.
    intros.
    subst.
    comp_simp.
    eapply H4.
    simpl.
    intuition.

    eapply getSupport_In_Seq; eauto.
    comp_simp.
    eapply getSupport_In_Seq; eauto.
    comp_simp.
    simpl. intuition.

    eapply getSupport_In_Seq; eauto.
    comp_simp.
    eapply getSupport_In_Seq; eauto.
    eapply getSupport_In_Seq; eauto.
    comp_simp.
    simpl. intuition.
    comp_simp.
    simpl. intuition.

    simpl.
    intuition.
    intuition.

    comp_simp.
    destruct r2.
    destruct p.
    intuition;
    simpl in H5;
    simpl in H2;
    simpl in H7;
    subst;
    eapply eqRat_refl.

    unfold runP2 in *.
    rewrite compLoop_S.
    eapply eqRat_trans.
    eapply evalDist_seq_eq.
    intros.
    eapply compLoop_S.
    intros.
    eapply eqRat_refl.

    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.
    comp_simp.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.
    comp_simp.

    rewrite Nat.add_succ_l.
    eapply IHn.

  Qed.


  (* running the two PWOs in sequence is equivalent to running PWO_Seq *)
  Theorem PWO_Seq_equiv : 
    forall (S_O : Set) o x d_P (s_O : S_O) e1 e2 e3,
      evalDist ([s_O, r_P1] <-$2 PWO_P1 _ e1 o d_P s_O;
        PWO_P2 _ e2 o r_P1 s_O) x ==
      evalDist (PWO_Seq _ e3 o d_P s_O) x.

    intuition.
    unfold PWO_Seq, PWO_Seq_P1, runPWO.
    inline_first.
    comp_skip.
    comp_ret_r.
    unfold setLet.
    
    eapply eqRat_trans.
    Focus 2.
    eapply evalDist_seq_eq.
    intros.
    eapply PWO_Seq_runP2.

    intros.
    eapply eqRat_refl.

    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    unfold runP2.
    eapply compLoop_eq.
    intros.
    unfold runP2_once.
    comp_simp.
    comp_skip.
    comp_skip.
    eapply evalDist_ret_eq.
    trivial.
    
    intros.
    destruct x.
    destruct p.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.

    destruct x.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.
    
    comp_ret_l.
    unfold setLet.
    inline_first.
    eapply evalDist_seq_eq.
    intuition.
    intros.

    destruct x0.
    inline_first.
    unfold runP2.
    eapply (@compLoop_spec _ _ eq).
    intros.
    subst.
    unfold comp_spec_post.
    intros.
    eapply evalDist_seq.
    intros.
    unfold runP2_once.
    comp_simp.
    comp_skip.
    comp_skip.
    eapply evalDist_ret_eq.
    intuition.
    intuition.

    intros.
    subst.
    eapply H6; trivial.
    intuition.
    intuition.
    
    intros.
    subst.
    
    destruct r2.
    destruct p.
    comp_ret_r.
    unfold setLet.
    eapply evalDist_seq_eq.
    intuition.
    intros.

    destruct x0.
    unfold P3, PWO_Seq_P3.
    unfold snd.
    eapply evalDist_seq_eq.
    intuition.
    unfold P3.
    intuition.

    intros.
    eapply evalDist_ret_eq.
    intuition.
 
  Qed.

  *)

End PWO_Seq.

Definition DataTypeFamily := nat -> Set.
Definition ProcedureFamily(A B : nat -> Type) := forall n, A n -> B n.
Definition EfficiencyPredicate := forall (A B : nat -> Type), ProcedureFamily A B -> Prop.

Require Import Asymptotic.

Record Adversary_2_concrete
  (D1 : Type)(R1 : Set)(D2 : Type)(R2 : Set) :={
    A2_SA : Set;
    A2_SA_EqDec : EqDec A2_SA;
    A2_A1 : D1 -> Comp (R1 * A2_SA);
    A2_A2 : (A2_SA * D2) -> Comp R2; 
    Adversary_2_concrete_A1_wf : forall x, well_formed_comp (A2_A1 x);
    Adversary_2_concrete_A2_wf : forall x, well_formed_comp (A2_A2 x)
  }.

Definition Adversary_2_concrete_prod D1 R1 D2 R2 (A : Adversary_2_concrete D1 R1 D2 R2)  
  := (A.(A2_A1), (fun s x => (@A2_A2 _ _ _ _ A (s, x)))).

Coercion Adversary_2_concrete_prod : 
  Adversary_2_concrete >-> prod.

Notation "x <-${ A } c1 ; c2" := 
  (Bind (let A := (fst A) in c1) (fun z => [x, state] <-2 z; let A := (snd A) state in c2))
(right associativity, at level 81, c1 at next level) : comp_scope.

Notation "[ x1 , x2 ] <-$2{ A } c1 ; c2" := 
  (Bind (let A := (fst A) in c1) (fun z => [x1, x2, state] <-3 z; let A := (snd A) state in c2))
(right associativity, at level 81, c1 at next level) : comp_scope.


Record Adversary_2_O_O_concrete
  (DA1 RA1 DA2 RA2 DO RO : Set) :=
  {
    A2OO_SA : Set;
    A2OO_SA_EqDec : EqDec A2OO_SA;
    RA1_EqDec : EqDec RA1;
    A2OO_A1 : ProcedureWithOracle DA1 (RA1 * A2OO_SA) DO RO;
    A2OO_A2 : ProcedureWithOracle (A2OO_SA * DA2) RA2 DO RO
  }.

Definition Adversary_2_O_O_concrete_prod {D1 R1 D2 R2 DO RO} (A : Adversary_2_O_O_concrete D1 R1 D2 R2 DO RO) 
  := (fun {SO : Set}{eqdSO : EqDec SO} (O : SO -> DO -> Comp (RO * SO)) d1 so =>
    [s_O, p] <-$2 runPWO A.(A2OO_A1) d1 O so;
    [d_A, s_A] <-2 p;
    Ret (EqDec_dec (pair_EqDec (pair_EqDec eqdSO (RA1_EqDec A)) (A2OO_SA_EqDec _)) ) (s_O, d_A, s_A)
, 
    (fun {SO : Set}{eqdSO : EqDec SO}(s : A2OO_SA A) (x : D2) (O : SO -> DO -> Comp (RO * SO)) => runPWO (A2OO_A2 A) (s, x) O)).


    Coercion Adversary_2_O_O_concrete_prod : 
      Adversary_2_O_O_concrete >-> prod.


    Notation "[ x1 , x2 ] <-$2{{ A }} c1 ; c2" := 
  (Bind (let A := (fst A) _ _ in c1) (fun z => [x1, x2, state] <-3 z; let A := (snd A) _ _ state in c2))
(right associativity, at level 81, c1 at next level) : comp_scope.


Record Adversary_2
  (efficient : EfficiencyPredicate)
  (D1 : nat -> Type)(R1 : DataTypeFamily)(D2 : nat -> Type)(R2 : DataTypeFamily) :={
    
    Adversary_2_to_concrete : 
    forall n, Adversary_2_concrete (D1 n) (R1 n) (D2 n) (R2 n);
 
    A2_A1_efficient : 
      efficient _ _ (fun n => (Adversary_2_to_concrete n).(A2_A1));
 

    (* Why doesn't this one work? 
    A2_A2_efficient : 
      efficient _ (fun n => (Adversary_2_to_concrete n).(A2_A2))
      *)

    A2_A2_efficient:
    efficient _ _ (fun n => @A2_A2 _ _ _ _ (Adversary_2_to_concrete n))
    
  }.

Coercion Adversary_2_to_concrete : Adversary_2 >-> Funclass.

Definition efficientPWO
  (efficient : EfficiencyPredicate)
  (DP RP DO RO : DataTypeFamily)
  (P : forall n, ProcedureWithOracle (DP n) (RP n) (DO n) (RO n)) : Prop :=

  efficient _ _ (fun n => (P n).(P1)) /\
    efficient _ _ (fun n => fun p => @P2 _ _ _ _ (P n) (fst p) (snd p)) /\
    efficient _ _ (fun n => fun p => @P3 _ _ _ _ (P n) (fst p) (snd p)) /\
    polynomial (fun n => (P n).(q)).

(*
Definition efficientPWO_fun
  (efficient : EfficiencyPredicate)
  (DP RP DO RO SP : DataTypeFamily)
  (P : forall n, (SP n) -> ProcedureWithOracle (DP n) (RP n) (DO n) (RO n)) : Prop :=

    efficient _ _ (fun n sp => @P1 _ _ _ _ (P n sp)) /\
    efficient _ _ (fun n sp => @P2 _ _ _ _ (P n sp)) /\
    efficient _ _ (fun n sp => @P3 _ _ _ _ (P n sp)) /\
    (forall x, polynomial (fun n => (P n (x n)).(q))).
*)


Record EfficientProcedureWithOracle
  (efficient : EfficiencyPredicate)
  (DP RP DO RO : DataTypeFamily) :={

    EPWO_to_concrete : forall n, ProcedureWithOracle (DP n) (RP n) (DO n) (RO n);
    EPWO_efficient : efficientPWO efficient EPWO_to_concrete

  }.

Coercion EPWO_to_concrete : EfficientProcedureWithOracle >-> Funclass.

Record Adversary_2_O_O
  (efficient : EfficiencyPredicate)
  (D1 R1 D2 R2 DO RO : DataTypeFamily) :={

    Adversary_2_O_O_to_concrete : 
    forall n, Adversary_2_O_O_concrete (D1 n) (R1 n) (D2 n) (R2 n) (DO n) (RO n);

    A2OO_A1_efficient : efficientPWO efficient (fun n => @A2OO_A1 _ _ _ _ _ _ (Adversary_2_O_O_to_concrete n));
    A2OO_A2_efficient : efficientPWO efficient (fun n => @A2OO_A2 _ _ _ _ _ _ (Adversary_2_O_O_to_concrete n))
      
  }.

Coercion Adversary_2_O_O_to_concrete : Adversary_2_O_O >-> Funclass.

