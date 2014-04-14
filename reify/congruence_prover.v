Require Import List.
Require Import MirrorShard.Expr MirrorShard.Env.
Require Import Prover.
Require Import types.
Require Import expr_equality.
Require Import ExtLib.Tactics.
Set Implicit Arguments.
Set Strict Implicit.
Require Import djsets.DisjointSets.
Require Import djsets.Numbers.
Require Import BinPos.


Module CONGRUENCE_PROVER 
       (TMap: UnionFind.MAP with Definition elt := tvar) 
       (EMap : UnionFind.MAP with Definition elt := expr)
       (DS : DISJOINTSETS Positive).

Section CongruenceProver.
  Variable types : list type.
  Variable fs : functions types.

  Record congruence_summary'  := 
    {
      emap : EMap.t positive;
      tmap : TMap.t (DS.T);
      ct : positive
    }.


  Definition congruence_summary : Type := congruence_summary'.

  Definition increment_pos (sum : congruence_summary) (e : expr) : (congruence_summary) :=
    match sum with
      | {| emap := emap0; tmap := tmap0; ct := ct0 |} =>
        {|
          emap := EMap.set e (Pos.succ ct0) emap0;
          tmap := tmap0;
          ct := Pos.succ ct0 |}
    end.

  Definition do_union' (tm : TMap.t (DS.T)) (t : tvar) (p1 p2 : positive) :=
    let uf := TMap.get t tm in
    let new_uf := 
        match uf with
          | Some uf' => DS.union uf' p1 p2  
          | None => DS.union DS.empty p1 p2
        end
    in 
    TMap.set t new_uf tm.

  Definition do_union ( sum : congruence_summary) (t: tvar) (p1 p2 : positive) : congruence_summary :=
    match sum with
      | {| emap := emap0; tmap := tmap0; ct := ct0 |} =>
        {|
          emap := emap0;
          tmap := do_union' tmap0 t p1 p2;
          ct := ct0 |}
    end.

  Definition get_add (sum : congruence_summary) (e : expr) : (congruence_summary' * positive) := 
    let r := EMap.get e (emap sum) in
    match r with
      | Some pos => (sum, pos)
      | None => ((increment_pos sum e), (Pos.succ (ct sum)))
    end.
        
  
  Definition congruenceLearnOne (hyp : expr) (sum : congruence_summary)  : congruence_summary :=
   match hyp with
   | Equal tv a b =>
     let (sum', p1) := get_add sum a in
     let (sum', p2) := get_add sum' b in
     do_union sum' tv p1 p2
   | _ => sum
   end.

   Definition congruenceLearn (sum : congruence_summary) (hyps : exprs) : congruence_summary :=
   fold_right (congruenceLearnOne) sum hyps.

   Definition empty_t : congruence_summary := 
     Build_congruence_summary' 
       (EMap.empty _)
       (TMap.empty _)
       1%positive.

  Definition congruenceSummarize (hyps : exprs) : congruence_summary := 
   fold_right (congruenceLearnOne) (empty_t) hyps.

  Definition equiv uf tm e1 e2 :=
    match (EMap.get e1 tm) with
        | Some p1 => 
          match (EMap.get e2 tm) with 
              Some p2 => fst (DS.equiv uf p1 p2)
            | None => false
          end
        | None => false
    end.

  Definition congruenceProve (sum : congruence_summary)
    (goal : expr) : bool :=
    match goal with
    | Equal t a b =>
      match (TMap.get t (tmap sum)) with
        | Some uf => equiv uf (emap sum) a b
        | None => false
      end
    | _ => false
    end.

  Definition congruenceValid (uvars vars : env types) (sum : congruence_summary) : Prop :=
   forall tv e1 e2 a b uf, 
     TMap.get tv (tmap sum) = Some uf ->
     EMap.get e1 (emap sum) = Some a ->
     EMap.get e2 (emap sum) = Some b -> 
     DS.sameclass uf a b -> 
     Provable fs uvars vars (Equal tv e1 e2). (*And succ ct = none??*)

  Lemma congruenceValid_extensible : forall u g f ue ge,
    congruenceValid u g f -> congruenceValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold congruenceValid.
    intros.
    (specialize (H tv e1 e2 a b uf)).
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
consider (exprD fs0 uvars vars a t); intros;
consider (exprD fs0 uvars vars c t); intros;
consider (exprD fs0 uvars vars b t); intros; subst; auto; contradiction.
Qed.

Lemma Provable_sym :
forall {types} (fs : functions types) uvars vars t a b 
(P1 : Provable fs uvars vars (Equal t a b)),
Provable fs uvars vars (Equal t b a).
Proof.
  intros.
  unfold Provable in *. simpl in *.
  consider (exprD fs0 uvars vars a t); intros;
  consider (exprD fs0 uvars vars b t); intros; subst; auto; contradiction.
Qed.

Lemma congruenceLearnCorrect : 
  forall uvars vars hyps sum
  (All_Prov : AllProvable fs uvars vars hyps)
  (CV : congruenceValid uvars vars sum),
    congruenceValid uvars vars (congruenceLearn sum hyps).
Proof.
Admitted.
(*
intros ? ? ? ? AP CV. unfold congruenceValid.
intros ? ? ? ? ? ? TG EG1 EG2 SC.
generalize dependent uf. generalize dependent a. generalize dependent b.
induction hyps as [ | hd_hyp tl_hyp].
  + intros. simpl in *. eapply CV; eauto.
  + intros ? EG2 ? EG1 ? TG SC.
    simpl in *. destruct AP as [PHd AP].
    destruct hd_hyp; try solve [eapply IHtl_hyp; eauto]. 
    simpl in *. 
   
unfold get_add in *. simpl in *.
    consider (EMap.get hd_hyp1 (emap (congruenceLearn sum tl_hyp))).
    Focus 2. simpl in *.
      -  intros ? ES EG2 EG1 TG. 
         
    destruct sum as [emap tmap ct]. simpl in *.
      consider (
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



(*
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
Qed. *)*)

Lemma congruenceSummarizeCorrect : forall uvars vars hyps
                                          (All_Prov : AllProvable fs uvars vars hyps),
                                     congruenceValid uvars vars (congruenceSummarize hyps).
Proof. Admitted. 
(*
  intros.

apply congruenceLearnCorrect; auto.
unfold congruenceValid. intros. 
rewrite X.gempty in H0.
 congruence.
Qed.
*)
      
Theorem congruenceProverCorrect : ProverCorrect fs congruenceValid congruenceProve.
Proof.
Admitted.
(*
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
*)

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

Module VST_CONGRUENCE_PROVER := CONGRUENCE_PROVER TVAR_MAP EXPR_MAP PosDisjointSets.



    

    