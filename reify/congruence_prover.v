Require Import List.
Require Import MirrorShard.Expr MirrorShard.Env.
Require Import Prover.
Require Import types.
Require Import expr_equality.
Require Import ExtLib.Tactics.
Require Import UnionFind.
Set Implicit Arguments.
Set Strict Implicit.




(*TODO, this should be a module over a map, so the map can be changed out *)
Module CONGRUENCE_PROVER (X: UnionFind.MAP with Definition elt := tvar) 
(Y: UnionFind.UNIONFIND with Definition elt := expr).

Import Y.
Section CongruenceProver.
  Variable types : list type.
  Variable fs : functions types.

  Definition congruence_summary : Type := X.t (Y.t).
  
  Definition congruenceLearnOne (hyp : expr) (sum : congruence_summary)  : congruence_summary :=
   match hyp with
   | Equal tv a b => 
     match (X.get tv sum) with
       | Some uf => X.set tv (union uf a b) sum
       | None => X.set tv (union empty a b) sum
     end
   | _ => sum
   end.

   Definition congruenceLearn (sum : congruence_summary) (hyps : exprs) : congruence_summary :=
   fold_right (congruenceLearnOne) sum hyps.

  Definition congruenceSummarize (hyps : exprs) : congruence_summary := 
   fold_right (congruenceLearnOne) (X.empty t) hyps.

  Definition congruenceProve (sum : congruence_summary)
    (goal : expr) : bool :=
    match goal with
    | Equal t a b =>
        match (X.get t sum) with
          | Some uf =>
            let (arepr, newsum) := find uf a in
            let (brepr, newsum) := find newsum b in
            eq_expr arepr brepr
          | None => false
        end
    | _ => false
end.

  Definition congruenceValid (uvars vars : env types) (sum : congruence_summary) : Prop :=
   forall tv a b uf, 
     a <> b ->
     X.get tv sum = Some uf ->
     sameclass uf a b -> 
     Provable fs uvars vars (Equal tv a b).

  Lemma congruenceValid_extensible : forall u g f ue ge,
    congruenceValid u g f -> congruenceValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold congruenceValid.
    intros.
    (specialize (H tv a b uf)).
    intuition.
    intuition. destruct H1.
    eapply Provable_weaken. eauto.
  Qed.

Lemma Provable_trans :
forall {types} (fs : functions types) uvars vars t a b c
(P1 : Provable fs uvars vars (Equal t a b))
(P2 : Provable fs uvars vars (Equal t b c)),
Provable fs uvars vars (Equal t a c). 
intros.
unfold Provable in *. simpl in *.
consider (exprD fs0 uvars vars a t0); intros;
consider (exprD fs0 uvars vars c t0); intros;
consider (exprD fs0 uvars vars b t0); intros; subst; auto; contradiction.
Qed.

Lemma Provable_sym :
forall {types} (fs : functions types) uvars vars t a b 
(P1 : Provable fs uvars vars (Equal t a b)),
Provable fs uvars vars (Equal t b a).
Proof.
  intros.
  unfold Provable in *. simpl in *.
  consider (exprD fs0 uvars vars a t0); intros;
  consider (exprD fs0 uvars vars b t0); intros; subst; auto; contradiction.
Qed.


Lemma congruenceLearnCorrect : 
  forall uvars vars hyps sum
  (All_Prov : AllProvable fs uvars vars hyps)
  (CV : congruenceValid uvars vars sum),
    congruenceValid uvars vars (congruenceLearn sum hyps).
Proof.
  intros.
  unfold congruenceValid in *. intros ? ? ? ? ABNe Map.
  unfold congruenceLearn in *.
  generalize dependent uf.
  generalize dependent a.
  generalize dependent b.
  induction hyps as [ | hd_hyp tl_hyp]. 
  + intros. vm_compute in Map. eapply CV; eauto.
  + intros b a Ne uf SC Lrn.
    simpl in *. destruct All_Prov as [PHd AP].
    unfold congruenceLearnOne at 1 in SC. 
    destruct hd_hyp; 
      try solve [eapply IHtl_hyp; eauto].
    consider ( X.get t0 (fold_right congruenceLearnOne sum tl_hyp)).
    - intros ? TlLrn NewMap.
      rewrite X.gsspec in NewMap.
      consider (X.elt_eq tv t0); intros TvEq.
        * subst. inversion TvEq; subst; clear TvEq.
          assert (Lrn2 := Lrn).
          apply sameclass_union_3 in Lrn.
          destruct Lrn as [ S | [[S1 S2] | [S1 S2]]]; 
            try solve [eapply IHtl_hyp; eauto].
          {
            destruct (expr_eq_dec a hd_hyp1) as [  | ANE]; subst;
            destruct (expr_eq_dec b hd_hyp2) as [ | BNE]; subst. 
            * auto.
            * eapply IHtl_hyp in S2; eauto.
              eapply Provable_trans. apply PHd. apply Provable_sym. auto.
            * eapply IHtl_hyp in S1; eauto. eapply Provable_trans; eauto.
            * eapply IHtl_hyp in S1; eauto. 
              eapply IHtl_hyp in S2; eauto. eapply Provable_trans; eauto.
              eapply Provable_trans; eauto.
              apply Provable_sym; auto.
          }
          
          {
            destruct (expr_eq_dec a hd_hyp2) as [  | ANE]; subst;
            destruct (expr_eq_dec b hd_hyp1) as [ | BNE]; subst. 
            * apply Provable_sym; auto.
            * eapply IHtl_hyp in S2; eauto.
              eapply Provable_trans. apply Provable_sym; eauto.
              apply Provable_sym; auto.
            * eapply IHtl_hyp in S1; eauto. 
              eapply Provable_trans; eauto. apply Provable_sym; auto.
            * eapply IHtl_hyp in S1; eauto. 
              eapply IHtl_hyp in S2; eauto. eapply Provable_trans; eauto.
              apply Provable_sym.
              eapply Provable_trans; eauto.
          }
        * eapply IHtl_hyp; eauto.
    - rewrite X.gsspec in *. consider (X.elt_eq tv t0); subst.
      * intros. inversion H0; subst; clear H0.
        apply sameclass_union_3 in Lrn.
        destruct Lrn as [ S | [[S1 S2] | [S1 S2]]]; 
          try solve [eapply IHtl_hyp; eauto];
          try solve [ try apply sameclass_empty in S1; try apply sameclass_empty in S2; try apply sameclass_empty in S; 
                      try subst; intuition].
        
        apply sameclass_empty in S1. apply sameclass_empty in S2.
        subst. apply Provable_sym. auto.
      * intros FR FR2. 
        eapply IHtl_hyp; eauto.
Qed.

Lemma congruenceSummarizeCorrect : forall uvars vars hyps
                                          (All_Prov : AllProvable fs uvars vars hyps),
                                     congruenceValid uvars vars (congruenceSummarize hyps).
Proof.
  intros.

apply congruenceLearnCorrect; auto.
unfold congruenceValid. intros. 
rewrite X.gempty in H0.
 congruence.
Qed.
      
Theorem congruenceProverCorrect : ProverCorrect fs congruenceValid congruenceProve.
Proof.
unfold ProverCorrect, ProverCorrect'. 
intros ? ? ? CV ? CP VP.
destruct goal; try solve [inversion CP].
destruct (expr_eq_dec goal1 goal2). subst.
t.
unfold congruenceValid in CV.
unfold congruenceProve in CP.
consider (X.get t0 sum).
  + intros t1 S CP.
    consider (find t1 goal1). intros ? ? F1 CP.
    consider (find t2 goal2). intros ? ? F2 CP.
    eapply CV; eauto. 
    unfold sameclass. 
    assert (fst (find t1 goal1) = e) as F1_. rewrite F1; auto.
    rewrite find_repr in F1_.
    assert (repr t2 goal2 = e0) as F2_. rewrite <- find_repr. 
    rewrite F2. auto.
    unfold eq_expr in CP.
    consider (expr_comp e e0); intros CPr; try congruence.
    apply expr_comp_eq_iff in CPr. subst. 
    assert (repr t1 goal2 = repr t2 goal2).
      assert (t2 = snd (find t1 goal1)). rewrite F1. auto.
      assert (F2_ := F2).
    rewrite H in F2 at 2. rewrite find_unchanged in F2. 
    rewrite F2_ in F2. inversion F2; auto. rewrite H in *; auto.
Qed.


  Definition congruenceProver : ProverT :=
  {| Facts := congruence_summary
   ; Summarize := congruenceSummarize
   ; Learn := congruenceLearn
   ; Prove := congruenceProve
   |}.

  Definition congruenceProver_correct : ProverT_correct congruenceProver fs.
  eapply Build_ProverT_correct with (Valid := congruenceValid);
    eauto using congruenceSummarizeCorrect, congruenceLearnCorrect, congruenceProverCorrect. intros. apply congruenceValid_extensible; auto.
  Qed.

End CongruenceProver.

Definition CongruenceProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => congruenceProver_correct fs
|}.

End CONGRUENCE_PROVER.

Module VST_CONGRUENCE_PROVER := CONGRUENCE_PROVER TVAR_MAP EXPR_UF.




    

    