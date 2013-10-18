Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.

Require Import Globalenvs.

Require Import Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.StructuredInjections.
  
Inductive reach (m:mem) (B:block -> Prop): list (block * Z) -> block -> Prop :=
  reach_nil: forall b, B b -> reach m B nil b
| reach_cons: forall b L b' z off n,
                     reach m B L b' ->
                     Mem.perm m b' z Cur Readable ->
                     ZMap.get z (PMap.get b' (Mem.mem_contents m)) = 
                        Pointer b off n ->
              reach m B ((b',z)::L) b.

Fixpoint reach' (m:mem) (B:block -> Prop) (L:list (block * Z)): block -> Prop:=
  match L with
    nil => B
  | l::L => match l with 
             (b',z) => match ZMap.get z (PMap.get b' (Mem.mem_contents m))
                       with Pointer b off n => fun bb => bb = b /\
                                               Mem.perm m b' z Cur Readable /\
                                               reach' m B L b'
                           | _ => fun bb => False
                       end
            end
  end.

Lemma reach_reach': forall m B L b1, reach m B L b1 <-> reach' m B L b1.
Proof. intros m B L.
  induction L; simpl; split; intros.
    inv H. trivial. constructor. trivial.
  destruct a as [b' z]. destruct (IHL b') as [IHa IHb]; clear IHL.
    inv H. rewrite H6.
    destruct (Mem.perm_dec m b' z Cur Readable); try contradiction; simpl.
    split; trivial. eauto.
  destruct a as [b' z]. 
    remember (ZMap.get z (Mem.mem_contents m) !! b') as v.
    destruct v; try inv H. apply eq_sym in Heqv.
    destruct H1. apply IHL in H0.
      econstructor; try eassumption.
Qed.

(*Fixpoint reach'' (m:mem) (B:block -> bool) (L:list (block * Z)): block -> bool:=
  match L with
    nil => B
  | l::L => match l with 
             (b',z) => match ZMap.get z (PMap.get b' (Mem.mem_contents m))
                       with Pointer b off n => fun bb => eq_block bb b &&
                                               Mem.perm_dec m b' z Cur Readable  &&
                                               reach' m B L b'
                           | _ => fun bb => false
                       end
            end
  end.

Lemma reach_reach': forall m L B b1, reach m (fun b => B b = true) L b1 <-> reach' m B L b1 = true.
Proof. intros m L.
  induction L; simpl; split; intros.
    inv H. trivial. constructor. trivial.
  destruct a as [b' z]. destruct (IHL B b') as [IHa IHb]; clear IHL.
    inv H. rewrite H6.
    destruct (Mem.perm_dec m b' z Cur Readable); try contradiction; simpl.
    destruct (eq_block b1 b1); simpl. apply IHa. apply H3.
    exfalso. apply n0; trivial. 
  destruct a as [b' z]. 
    remember (ZMap.get z (Mem.mem_contents m) !! b') as v.
    specialize (IHL (fun bb=> B bb = Mem.perm_dec m b' z Cur Readable && reach' m B L b') b').
    destruct v; try inv H. apply eq_sym in Heqv.
    destruct (eq_block b1 b); simpl in *; try inv H1.
      econstructor; try eassumption. 
      destruct IHL. clear H.
        apply (IHL (Mem.perm_dec m b' z Cur Readable && reach' m B L b')). b').
      apply andb_true_iff in H1; destruct H1. 
      apply IHb in H0. clear IHa IHb.
      econstructor; try eassumption.
Qed.    
*)

Lemma reach_inject: forall m1 m2 j (J: Mem.inject j m1 m2)
                 L1 b1 B1 (R: reach m1 B1 L1 b1) B2
                 (HB: forall b, B1 b -> exists jb d, j b = Some(jb,d) /\ B2 jb),
                 exists b2 L2 d2, j b1 = Some(b2,d2) /\ reach m2 B2 L2 b2.
Proof. intros.
  induction R.
    destruct (HB _ H) as [jb [d [Jb B]]].
    exists jb, nil, d. split; trivial. constructor. assumption.
  destruct IHR as [b2' [L2' [d2' [J' R2']]]].
    clear R HB.         
    specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ J) _ _ _ _ J' H).
    intros. rewrite H0 in H1.
    inv H1.
    exists b2, ((b2',(z + d2'))::L2'), delta.
    split. assumption.
    eapply reach_cons. apply R2'.
       eapply Mem.perm_inject. apply J'. apply J. apply H.
       apply eq_sym. apply H6.
Qed.

Lemma reach_mono: forall B1 B2 (HB : forall b, B1 b = true -> B2 b = true)
                         m b L1 (R : reach m (fun bb : block => B1 bb = true) L1 b),
                  exists L, reach m (fun bb : block => B2 bb = true) L b.
Proof. intros.
  induction R; simpl in *.
    exists nil. constructor.  eauto. 
  destruct IHR as [L2 R2]. 
    eexists. eapply reach_cons; eassumption.
Qed.

(*
Parameter reachable : mem -> list block -> block -> bool.
Axioms reachAX: forall m B b, reachable m B b = true 
                    <-> exists L, reach m (fun bb => In bb B) L b.

Lemma reachable_inject: forall m1 m2 j (J: Mem.inject j m1 m2) B1 B2
                 (HB: forall b, In b B1 -> exists jb d, j b = Some(jb,d) /\ In jb B2)
                 b1 (R: reachable m1 B1 b1 = true),
                 exists b2 d, j b1 = Some(b2,d) /\ reachable m2 B2 b2 = true.
Proof.
  intros. apply reachAX in R. destruct R as [L1 R].
  destruct (reach_inject _ _ _ J _ _ _ R _ HB) as [b2 [L2 [off [J2 R2]]]].
  exists b2, off. split; trivial.
    apply reachAX. exists L2; assumption.
Qed.
*)

Parameter REACH : mem -> (block -> bool) -> block -> bool.
Axioms REACHAX: forall m B b, REACH m B b = true 
                    <-> exists L, reach m (fun bb => B bb = true) L b.

Lemma REACH_increasing: forall m B b, B b = true -> REACH m B b = true.
Proof. intros.
  apply REACHAX. exists nil. constructor. assumption.
Qed.

Lemma REACH_inject: forall m1 m2 j (J: Mem.inject j m1 m2) B1 B2
                 (HB: forall b, B1 b = true -> exists jb d, j b = Some(jb,d) /\ B2 jb = true)
                 b1 (R: REACH m1 B1 b1 = true),
                 exists b2 d, j b1 = Some(b2,d) /\ REACH m2 B2 b2 = true.
Proof.
  intros. apply REACHAX in R. destruct R as [L1 R].
  destruct (reach_inject _ _ _ J _ _ _ R _ HB) as [b2 [L2 [off [J2 R2]]]].
  exists b2, off. split; trivial.
    apply REACHAX. exists L2; assumption.
Qed.
           
Lemma REACH_mono: forall B1 B2 (HB: forall b, B1 b = true -> B2 b = true) m b
                  (R: REACH m B1 b = true), REACH m B2 b = true.
Proof. intros. rewrite REACHAX in *.
  destruct R as [L1 R].
  apply (reach_mono _ _ HB _ _ _ R).
Qed.

Definition replace_locals (mu:SM_Injection) pSrc' pTgt': SM_Injection :=
  match mu with 
    Build_SM_Injection DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local =>
    Build_SM_Injection DomS DomT myblocksSrc myblocksTgt pSrc' pTgt' fSrc fTgt extern local 
  end.
(*typically, we have forall b, pSrc b -> pSrc' b and forall b, pTgt b -> pTgt' b,
  i.e. only reclassify private entries as public*)

Lemma replace_locals_wd: forall mu (WD: SM_wd mu) pSrc' pTgt'
         (SRC: forall b1, pSrc' b1 = true -> 
               exists b2 d, local_of mu b1 = Some(b2,d) /\ pTgt' b2=true)
         (TGT: forall b, pTgt' b = true -> myBlocksTgt mu b = true),
      SM_wd (replace_locals mu pSrc' pTgt'). 
Proof. intros.
  destruct mu as [DomS DomT mySrc myTgt pSrc pTgt fSrc fTgt extern local]; simpl in *. 
  constructor; simpl; try apply WD.
    intros. rewrite H. apply (SRC _ H).
    assumption.
Qed.

Lemma replace_locals_extern: forall mu pubSrc' pubTgt',
      extern_of (replace_locals mu pubSrc' pubTgt') = extern_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_local: forall mu pubSrc' pubTgt',
      local_of (replace_locals mu pubSrc' pubTgt') = local_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_unknown: forall mu pubSrc' pubTgt',
      unknown_of (replace_locals mu pubSrc' pubTgt') = unknown_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_foreign: forall mu pubSrc' pubTgt',
      foreign_of (replace_locals mu pubSrc' pubTgt') = foreign_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_pub: forall mu pubSrc' pubTgt',
      pub_of (replace_locals mu pubSrc' pubTgt') = 
          (fun b => if pubSrc' b then local_of mu b else None).
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_pub': forall mu pubSrc' pubTgt'
      (P: forall b, pubBlocksSrc mu b = true -> pubSrc' b = true)
      b (B: pubBlocksSrc mu b = true),
      pub_of (replace_locals mu pubSrc' pubTgt') b = pub_of mu b.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
rewrite B, (P _ B). trivial.
Qed.

Lemma replace_locals_as_inj: forall mu pubSrc' pubTgt',
      as_inj (replace_locals mu pubSrc' pubTgt') = as_inj mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_shared: forall mu pubSrc' pubTgt',
      shared_of (replace_locals mu pubSrc' pubTgt') = 
      join (foreign_of mu) (fun b => if pubSrc' b then local_of mu b else None).
Proof. intros. unfold shared_of, join; simpl.
rewrite replace_locals_foreign.
rewrite replace_locals_pub.
trivial.
Qed.

Lemma replace_locals_DOM: forall mu pubSrc' pubTgt',
      DOM (replace_locals mu pubSrc' pubTgt') = DOM mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_RNG: forall mu pubSrc' pubTgt',
      RNG (replace_locals mu pubSrc' pubTgt') = RNG mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed. 

Lemma replace_locals_DomSrc: forall mu pubSrc' pubTgt',
      DomSrc (replace_locals mu pubSrc' pubTgt') = DomSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_DomTgt: forall mu pubSrc' pubTgt',
      DomTgt (replace_locals mu pubSrc' pubTgt') = DomTgt mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed. 

Lemma replace_locals_myBlocksSrc: forall mu pubSrc' pubTgt',
      myBlocksSrc (replace_locals mu pubSrc' pubTgt') = myBlocksSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_myBlocksTgt: forall mu pubSrc' pubTgt',
      myBlocksTgt (replace_locals mu pubSrc' pubTgt') = myBlocksTgt mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_frgnBlocksSrc: forall mu pubSrc' pubTgt',
      frgnBlocksSrc (replace_locals mu pubSrc' pubTgt') = frgnBlocksSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_frgnBlocksTgt: forall mu pubSrc' pubTgt',
      frgnBlocksTgt (replace_locals mu pubSrc' pubTgt') = frgnBlocksTgt mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_pubBlocksSrc: forall mu pubSrc' pubTgt',
      pubBlocksSrc (replace_locals mu pubSrc' pubTgt') = pubSrc'.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_pubBlocksTgt: forall mu pubSrc' pubTgt',
      pubBlocksTgt (replace_locals mu pubSrc' pubTgt') = pubTgt'.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Definition replace_externs (mu:SM_Injection) fSrc' fTgt': SM_Injection :=
  match mu with 
    Build_SM_Injection DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local =>
    Build_SM_Injection DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc' fTgt' extern local 
  end.
(*typically, we have forall b, fSrc b -> fSrc' b and forall b, fTgt b -> fTgt' b,
  i.e. only reclassify unknown entries as foreign*)

Lemma replace_externs_wd: forall mu (WD: SM_wd mu) fSrc' fTgt'
         (SRC: forall b1, fSrc' b1 = true -> 
               exists b2 d, extern_of mu b1 = Some(b2,d) /\ fTgt' b2=true)
         (TGT: forall b, fTgt' b = true -> 
               myBlocksTgt mu b = false /\ DomTgt mu b = true),
      SM_wd (replace_externs mu fSrc' fTgt'). 
Proof. intros.
  destruct mu as [DomS DomT mySrc myTgt pSrc pTgt fSrc fTgt extern local]; simpl in *. 
  constructor; simpl; try apply WD.
    intros. rewrite H. apply (SRC _ H).
    assumption.
Qed.

Lemma replace_externs_extern: forall mu frgSrc' frgTgt',
      extern_of (replace_externs mu frgSrc' frgTgt') = extern_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_local: forall mu frgSrc' frgTgt',
      local_of (replace_externs mu frgSrc' frgTgt') = local_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_priv: forall mu frgSrc' frgTgt',
      priv_of (replace_externs mu frgSrc' frgTgt') = priv_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_pub: forall mu frgSrc' frgTgt',
      pub_of (replace_externs mu frgSrc' frgTgt') = pub_of mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_as_inj: forall mu frgSrc' frgTgt',
      as_inj (replace_externs mu frgSrc' frgTgt') = as_inj mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_DOM: forall mu frgSrc' frgTgt',
      DOM (replace_externs mu frgSrc' frgTgt') = DOM mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_RNG: forall mu frgSrc' frgTgt',
      RNG (replace_externs mu frgSrc' frgTgt') = RNG mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed. 

Lemma replace_externs_DomSrc: forall mu frgSrc' frgTgt',
      DomSrc (replace_externs mu frgSrc' frgTgt') = DomSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_DomTgt: forall mu frgSrc' frgTgt',
      DomTgt (replace_externs mu frgSrc' frgTgt') = DomTgt mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed. 

Lemma replace_externs_myBlocksSrc: forall mu frgSrc' frgTgt',
      myBlocksSrc (replace_externs mu frgSrc' frgTgt') = myBlocksSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_myBlocksTgt: forall mu frgSrc' frgTgt',
      myBlocksTgt (replace_externs mu frgSrc' frgTgt') = myBlocksTgt mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_frgnBlocksSrc: forall mu fSrc' fTgt',
      frgnBlocksSrc (replace_externs mu fSrc' fTgt') = fSrc'.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_frgnBlocksTgt: forall mu fSrc' fTgt',
      frgnBlocksTgt (replace_externs mu fSrc' fTgt') = fTgt'.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_pubBlocksSrc: forall mu frgSrc' frgTgt',
      pubBlocksSrc (replace_externs mu frgSrc' frgTgt') = pubBlocksSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_pubBlocksTgt: forall mu frgSrc' frgTgt',
      pubBlocksTgt (replace_externs mu frgSrc' frgTgt') = pubBlocksTgt mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Definition getBlocks (V:list val) (b: block): bool :=
   in_dec eq_block b 
    (fold_right (fun v L => match v with Vptr b' z => b'::L | _ => L end) nil V).

Lemma getBlocksD: forall v V b, 
  getBlocks (v:: V) b = 
    match v with
      Vptr b' _  => orb (eq_block b' b) (getBlocks V b)
    | _ => getBlocks V b
   end.
Proof. intros.
  destruct v; simpl; try reflexivity.
  unfold getBlocks. simpl.
  destruct (eq_block b0 b); simpl. trivial.
  destruct (in_dec eq_block b
    (fold_right
       (fun (v : val) (L : list block) =>
        match v with
        | Vundef => L
        | Vint _ => L
        | Vlong _ => L
        | Vfloat _ => L
        | Vptr b' _ => b' :: L
        end) nil V)). trivial. trivial.  
Qed.

Lemma getBlocks_char: forall V b, getBlocks V b = true <-> 
   exists off, In (Vptr b off) V.
Proof.
  intros V. induction V; simpl; intros.
     unfold getBlocks; simpl. split; intros. inv H. destruct H. contradiction.
  rewrite getBlocksD.
  destruct a; simpl in *; destruct (IHV b); clear IHV.
      split; intros. destruct (H H1). exists x; right; trivial.
         apply H0. destruct H1 as [n [X | X]]. inv X. exists n; trivial.
      split; intros. destruct (H H1). exists x; right; trivial.
         apply H0. destruct H1 as [n [X | X]]. inv X. exists n; trivial.
      split; intros. destruct (H H1). exists x; right; trivial.
         apply H0. destruct H1 as [n [X | X]]. inv X. exists n; trivial.
      split; intros. destruct (H H1). exists x; right; trivial.
         apply H0. destruct H1 as [n [X | X]]. inv X. exists n; trivial.
      split; intros. 
         apply orb_true_iff in H1. 
           destruct H1. exists i; left. clear H H0.
             destruct (eq_block b0 b); subst. trivial. inv H1.
           destruct (H H1). exists x; right; trivial. 
         apply orb_true_iff. destruct H1 as [n [X | X]].
            left. inv X. destruct (eq_block b b); subst. trivial. exfalso. apply n0; trivial.
            right. apply H0. exists n; trivial.
Qed. 

Lemma getBlocks_inject: forall j vals1 vals2
                       (ValInjMu : Forall2 (val_inject j) vals1 vals2)
                       b (B: getBlocks vals1 b = true),
      exists jb d, j b = Some (jb, d) /\ getBlocks vals2 jb = true.
Proof. intros. apply getBlocks_char in B. destruct B as [off INN].
   destruct (forall2_val_inject_D _ _ _ ValInjMu _ INN) as [v2 [ValInj INN2]].
   inv ValInj.
   exists b2, delta. split; trivial.
   apply getBlocks_char. eexists. apply INN2.
Qed.

(*The blocks explicitly exported via call arguments, plus the already shared blocks*)
Definition exportedSrc mu vals b := orb (getBlocks vals b) (sharedSrc mu b).
Definition exportedTgt mu vals b := orb (getBlocks vals b) (sharedTgt mu b).

Lemma sm_extern_normalize_exportedTgt: forall mu12 mu23
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
   exportedTgt (sm_extern_normalize mu12 mu23) = exportedTgt mu12.
Proof. intros. unfold exportedTgt.
  rewrite sm_extern_normalize_sharedTgt; trivial.
Qed.

Lemma sm_extern_normalize_exportedSrc: forall mu12 mu23
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
   exportedSrc (sm_extern_normalize mu12 mu23) = exportedSrc mu12.
Proof. intros. unfold exportedSrc.
  rewrite sm_extern_normalize_sharedSrc; trivial.
Qed.

Lemma exported_inject: forall mu (WD: SM_wd mu) vals1 vals2
          (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b
          (SRC: exportedSrc mu vals1 b = true ),
        exists jb d, as_inj mu b = Some (jb, d)
                  /\ exportedTgt mu vals2 jb = true.
Proof. intros. unfold exportedSrc in SRC. unfold exportedTgt.
  apply orb_true_iff in SRC.
  destruct SRC as [SRC | SRC].
   destruct (getBlocks_inject _ _ _ ValInjMu _ SRC) as [b2 [d [J G]]].
   exists b2, d. rewrite J, G. intuition.
  destruct (shared_SrcTgt _ WD _ SRC) as [b2 [d [J G]]].
   exists b2, d. rewrite (shared_in_all _ WD _ _ _ J).
      rewrite G. intuition.
Qed.

Lemma REACH_shared_of: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (shared_of mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (shared_of mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
        B (HB: forall b b2 d, shared_of mu b = Some(b2,d) -> B b2 = true),
      exists b2 d, shared_of mu b1 = Some (b2, d) /\ 
                   REACH m2 (fun b => orb (getBlocks vals2 b) (B b)) b2 = true.
Proof. intros.
 eapply (REACH_inject _ _ _ MemInjMu); try eassumption.
 clear R. simpl; intros.
 apply orb_true_iff in H.
 destruct H.
   destruct (getBlocks_inject _ _ _ ValInjMu _ H) as [b2 [d [J G]]].
   exists b2, d. rewrite J, G. intuition.
 apply sharedSrc_iff in H. destruct H as [jb [delta SH]].
   specialize (HB _ _ _ SH).
   exists jb, delta. 
   intuition.
Qed.

Lemma REACH_as_inj: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
        B (HB: forall b b2 d, shared_of mu b = Some(b2,d) -> B b2 = true),
      exists b2 d, as_inj mu b1 = Some (b2, d) /\ 
                   REACH m2 (fun b => orb (getBlocks vals2 b) (B b)) b2 = true.
Proof. intros.
 eapply (REACH_inject _ _ _ MemInjMu); try eassumption.
 clear R. simpl; intros.
 apply orb_true_iff in H.
 destruct H.
   destruct (getBlocks_inject _ _ _ ValInjMu _ H) as [b2 [d [J G]]].
   exists b2, d. rewrite J, G. intuition.
 apply sharedSrc_iff in H. destruct H as [jb [delta SH]].
   specialize (HB _ _ _ SH).
   apply shared_in_all in SH; trivial.
   exists jb, delta. 
   intuition.
Qed.

Lemma REACH_local: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
         (myBSrc : myBlocksSrc mu b1 = true),
      exists b2 d, local_of mu b1 = Some (b2, d).
Proof. intros.
  destruct (REACH_as_inj _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R (fun b => true)) as [b2 [d [ASINJ RR]]].
    trivial.
  exists b2, d.
  destruct (joinD_Some _ _ _ _ _ ASINJ).
    destruct (extern_DomRng _ WD _ _ _ H) as [ZZ _]; rewrite ZZ in myBSrc.
    intuition.
  apply H.
Qed.
 
Lemma REACH_extern: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1 
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
         (myBSrc : myBlocksSrc mu b1 = false),
      exists b2 d, extern_of mu b1 = Some (b2, d).
Proof. intros.
  destruct (REACH_as_inj _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R (fun b => true)) as [b2 [d [ASINJ RR]]].
    trivial.
  exists b2, d.
  destruct (joinD_Some _ _ _ _ _ ASINJ). assumption.
  destruct H.
  destruct (local_DomRng _ WD _ _ _ H0) as [ZZ _]; rewrite ZZ in myBSrc.
  intuition.
Qed.

(*The following six or so results are key lemmas about REACH - they say
  that blocks exported in SRC are injected, to blocks exported by TGT,
  preserving the myBlocks-structure, ie distinction betwene public and
  foreign*)
Lemma REACH_as_inj_REACH: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true),
      exists b2 d, as_inj mu b1 = Some (b2, d) /\ 
                   REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_as_inj _ WD _ _ _ _ MemInjMu ValInjMu _ R (fun b => true))
       as [b2 [d [ASI _]]]. trivial.
  exists b2, d. split; trivial.
  destruct (REACH_inject _ _ _ MemInjMu _ _ 
      (exported_inject _ WD _ _ ValInjMu) _ R)
   as [bb2 [dd [ASI' RR]]].
  rewrite ASI' in ASI. inv ASI.
  assumption.
Qed.

Lemma REACH_local_REACH: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
         (myBSrc : myBlocksSrc mu b1 = true),
      exists b2 d, local_of mu b1 = Some (b2, d) /\ 
                   REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_as_inj_REACH _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R) as [b2 [d [ASINJ RR]]].
  exists b2, d. split; trivial.
  destruct (joinD_Some _ _ _ _ _ ASINJ).
    destruct (extern_DomRng _ WD _ _ _ H) as [ZZ _]; rewrite ZZ in myBSrc.
    intuition.
  apply H.
Qed.

Lemma REACH_local_REACH': forall mu m1 vals1  b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
        (WD: SM_wd mu) m2 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2)
        (myBSrc : myBlocksSrc mu b1 = true) b2 d
        (LOC: local_of mu b1 = Some (b2, d)), 
     REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_local_REACH _ WD _ _ _ _ MemInjMu ValInjMu _ R myBSrc)
  as [bb [dd [LL RR]]]. rewrite LL in LOC. inv LOC. trivial.
Qed.

Lemma REACH_extern_REACH: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
         (myBSrc : myBlocksSrc mu b1 = false),
      exists b2 d, extern_of mu b1 = Some (b2, d) /\ 
                   REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_as_inj_REACH _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R) as [b2 [d [ASINJ RR]]].
  exists b2, d. split; trivial.
  destruct (joinD_Some _ _ _ _ _ ASINJ).
    apply H.
  destruct H as [_ H]. 
    destruct (local_DomRng _ WD _ _ _ H) as [ZZ _]; rewrite ZZ in myBSrc.
    intuition.
Qed.

Goal forall m1 mu (WD: SM_wd mu) vals b, pubBlocksSrc mu b = true ->
           REACH m1 (exportedSrc mu vals) b = true.
Proof. intros. apply REACH_increasing.
  apply orb_true_iff. right. apply pubSrc_shared; trivial. 
Qed.

Lemma eff_after_check1: 
      forall mu m1 vals1 m2 
        (*selected standard assumptions:*)
        (MemInjMu: Mem.inject (as_inj mu) m1 m2)
        vals2 (ValInjMu: Forall2 (val_inject (as_inj mu)) vals1 vals2) 

        pubSrc' (pubSrcHyp: pubSrc' = fun b => andb (myBlocksSrc mu b)
                                                    (REACH m1 (exportedSrc mu vals1) b))

        pubTgt' (pubTgtHyp: pubTgt' = fun b => andb (myBlocksTgt mu b)
                                                    (REACH m2 (exportedTgt mu vals2) b))

        nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
        (WD: SM_wd mu) (SMValMu: sm_valid mu m1 m2),
(*follows:*) SM_wd nu /\ sm_valid nu m1 m2 /\
(*follows: *) Mem.inject (as_inj nu) m1 m2 /\
(*follows: *) Forall2 (val_inject (as_inj nu)) vals1 vals2.
Proof. intros. subst.
split. eapply replace_locals_wd; trivial.
      intros. apply andb_true_iff in H. destruct H as [myBSrc ReachSrc].
        destruct (REACH_local_REACH _ WD _ _ _ _  MemInjMu ValInjMu _ ReachSrc myBSrc)
            as [b2 [d [Loc ReachTgt]]]; clear ReachSrc.
        exists b2, d; split; trivial. 
        destruct (local_DomRng _ WD _ _ _ Loc). rewrite H0, ReachTgt. trivial.
      intros. apply andb_true_iff in H. apply H. 
split. 
  split; intros.
    rewrite replace_locals_DOM in H. 
    eapply SMValMu; apply H.
  rewrite replace_locals_RNG in H. 
    eapply SMValMu; apply H.
rewrite replace_locals_as_inj. split; assumption.
Qed.  

Lemma eff_after_check2: 
      forall nu' ret1 m1' m2' ret2
         (MemInjNu': Mem.inject (as_inj nu') m1' m2')
         (RValInjNu': val_inject (as_inj nu') ret1 ret2)

         frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                  (andb (negb (myBlocksSrc nu' b)) 
                                                        (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

         frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                  (andb (negb (myBlocksTgt nu' b))
                                                        (REACH m2' (exportedTgt nu' (ret2::nil)) b)))
   
         mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
         (WD: SM_wd nu') (SMValid: sm_valid nu' m1' m2'),

      SM_wd mu' /\ sm_valid mu' m1' m2'. 
Proof. intros. subst.
split.
eapply replace_externs_wd. assumption.
  intros. do 2 rewrite andb_true_iff in H.
          destruct H as [DomB1 [notMyB1 ReachB1]].
          assert (VALS: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
            constructor. assumption. constructor. 
          apply negb_true_iff in notMyB1.
          destruct (REACH_extern_REACH _ WD _ _ _ _ MemInjNu' VALS _ 
                    ReachB1 notMyB1) as [b2 [d [EXT ReachB2]]].
          exists b2, d; split; trivial.
          do 2 rewrite andb_true_iff. rewrite negb_true_iff.
          destruct (extern_DomRng _ WD _ _ _ EXT) as [? [? [? ?]]].
          intuition.
  intros. do 2 rewrite andb_true_iff in H. rewrite negb_true_iff in H.
          intuition. 
split; intros.
  rewrite replace_externs_DOM in H. apply SMValid. apply H.
  rewrite replace_externs_RNG in H. apply SMValid. apply H.
Qed.
         
Lemma eff_after_check3: 
      forall nu' ret1 m1' m2' ret2
        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)


        frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (myBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

        frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (myBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt'),

     Mem.inject (as_inj mu') m1' m2' /\ val_inject (as_inj mu') ret1 ret2.
Proof. intros. subst. rewrite replace_externs_as_inj. split; assumption. Qed.  

Lemma eff_after_check4: 
      forall mu pubSrc' pubTgt'
             nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             nu' (INC: extern_incr nu nu')  
             mu' frgnSrc' frgnTgt'
            (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
            (SMwdNu': SM_wd nu'),
      inject_incr (as_inj mu) (as_inj mu').
Proof. intros. subst.
  rewrite replace_externs_as_inj.
  intros b; intros.
    eapply extern_incr_as_inj. apply INC. assumption.
    rewrite replace_locals_as_inj. apply H.
Qed.

Lemma eff_after_check5a: 
      forall mu pubSrc' pubTgt' nu
             (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             kappa m1 m2
            (SEP: sm_inject_separated nu kappa m1 m2),
      sm_inject_separated mu kappa m1 m2.
Proof. intros. subst.
destruct SEP as [SEPa [SEPb SEPc]].
rewrite replace_locals_as_inj, 
        replace_locals_DomSrc, 
        replace_locals_DomTgt in *.
split; intros; eauto.
Qed.

Lemma eff_after_check5b: 
      forall nu' mu' frgnSrc' frgnTgt'
             (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
             kappa m1 m2 (SEP: sm_inject_separated kappa nu' m1 m2),
      sm_inject_separated kappa mu' m1 m2.
Proof. intros. subst.
destruct SEP as [SEPa [SEPb SEPc]].
split; intros. 
  rewrite replace_externs_as_inj in H0.
  apply (SEPa _ _ _ H H0).
split; intros.
  rewrite replace_externs_DomSrc in *.
  apply (SEPb _ H H0).
rewrite replace_externs_DomTgt in *.
  apply (SEPc _ H H0).
Qed.

Lemma eff_after_check5: 
      forall mu pubSrc' pubTgt' nu
             (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             nu' mu' frgnSrc' frgnTgt'
             (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
             m1 m2 (SEP: sm_inject_separated nu nu' m1 m2),
      sm_inject_separated mu mu' m1 m2.
Proof. intros.
eapply eff_after_check5b; try eassumption.
eapply eff_after_check5a; try eassumption.
Qed.

Lemma eff_after_check5_explicitProof: 
      forall mu pubSrc' pubTgt' nu
             (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
             nu' mu' frgnSrc' frgnTgt'
             (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
             m1 m2 (SEP: sm_inject_separated nu nu' m1 m2),
      sm_inject_separated mu mu' m1 m2.
Proof. intros. subst.
destruct SEP as [SEPa [SEPb SEPc]].
rewrite replace_locals_as_inj in *.
rewrite replace_locals_DomSrc, replace_locals_DomTgt in *.
split; intros. 
  rewrite replace_externs_as_inj in H0.
  apply (SEPa _ _ _ H H0).
split; intros.
  rewrite replace_externs_DomSrc in *.
  apply (SEPb _ H H0).
rewrite replace_externs_DomTgt in *.
  apply (SEPc _ H H0).
Qed.

Definition local_out_of_reach mu (m : mem) (b : block) (ofs : Z): Prop := 
  myBlocksTgt mu b = true /\ 
  forall b0 delta, local_of mu b0 = Some (b, delta) -> 
                  (~ Mem.perm m b0 (ofs - delta) Max Nonempty \/
                   pubBlocksSrc mu b0 = false).

Goal forall mu (WD: SM_wd mu) m1 m2 m2' 
(U: Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'),
Mem.unchanged_on (fun b ofs => pubBlocksTgt mu b = true /\ 
                  loc_out_of_reach (pub_of mu) m1 b ofs) m2 m2'.
Proof.
intros.
eapply mem_unchanged_on_sub; try eassumption.
intros. destruct H.
unfold local_out_of_reach.
split. apply (pubBlocksLocalTgt _ WD _ H). 
intros.
remember (pubBlocksSrc mu b0) as d.
destruct d; try (right; reflexivity).
left.
eapply H0. unfold pub_of.
destruct mu; simpl in *. rewrite <- Heqd. assumption.
Qed. 

Goal forall mu (WD: SM_wd mu) m1 m2 m2'
(U: Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'),
Mem.unchanged_on (fun b ofs => myBlocksTgt mu b = true /\ 
                    pubBlocksTgt mu b = false) m2 m2'.
intros.
eapply mem_unchanged_on_sub; try eassumption.
intros. unfold local_out_of_reach. destruct H. 
split; trivial. intros.
remember (pubBlocksSrc mu b0) as d.
destruct d; try (right; reflexivity).
apply eq_sym in Heqd.
destruct (pubSrc _ WD _ Heqd) as [b2 [dd [PUB TGT]]].
apply pub_in_local in PUB. rewrite PUB in H1. inv H1.
rewrite TGT in H0. discriminate.
Qed.

Goal forall mu m1 m2 m2' (WD:SM_wd mu)
  (U1: Mem.unchanged_on (fun b ofs => myBlocksTgt mu b = true /\ 
                    pubBlocksTgt mu b = false) m2 m2')
  (U2: Mem.unchanged_on (fun b ofs => pubBlocksTgt mu b = true /\ 
                  loc_out_of_reach (pub_of mu) m1 b ofs) m2 m2'),
Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'.
intros.
destruct U1 as [P1 C1]. destruct U2 as [P2 C2].
split; intros.
  clear C1 C2.
  specialize (P1 b ofs k p). specialize (P2 b ofs k p).
  remember (myBlocksTgt mu b) as d.
  destruct d; apply eq_sym in Heqd; simpl in *.
    remember (pubBlocksTgt mu b) as q.
    destruct q; apply eq_sym in Heqq; simpl in *.
      clear P1.
      apply P2; trivial. split; trivial. 
      intros b0; intros.
      destruct H. destruct (H2 b0 delta).
        apply pub_in_local; trivial.
        assumption.
        unfold pub_of in H1. destruct mu. simpl in *.  rewrite H3 in H1.  discriminate.
    apply P1; trivial. split; trivial.
  clear P1.
  remember (pubBlocksTgt mu b) as q.
    destruct q; apply eq_sym in Heqq; simpl in *.
      assert (myBlocksTgt mu b = true). eapply (pubBlocksLocalTgt _ WD). eassumption.
      rewrite H1 in Heqd. discriminate.
  destruct H. rewrite H in Heqd. discriminate. 
destruct H.
  clear P1 P2.
  specialize (C1 b ofs). specialize (C2 b ofs).
  rewrite H in *.
  remember (pubBlocksTgt mu b) as d.
  destruct d; apply eq_sym in Heqd.
    clear C1. apply C2; trivial; clear C2.
    split; trivial. intros b1; intros.
     destruct (pub_myBlocks _ WD _ _ _ H2).
     apply pub_in_local in H2.
     destruct (H1 _ _ H2). assumption. rewrite H5 in *. inv H3.
  clear C2. apply C1; eauto.
Qed.

Lemma core_initial_wd : forall vals1 m1 j vals2 m2 DomS DomT,
          Mem.inject j m1 m2 -> 
          Forall2 (val_inject j) vals1 vals2 ->
          (forall b1 b2 d, j b1 = Some (b2, d) -> DomS b1 = true /\ DomT b2 = true) ->
(*follows  (forall b, REACH m1 (getBlocks vals1) b = true -> DomS b = true) ->
*)         (forall b, REACH m2 (getBlocks vals2) b = true -> DomT b = true) ->
       SM_wd (initial_SM DomS
                         DomT 
                         (REACH m1 (getBlocks vals1)) 
                         (REACH m2 (getBlocks vals2)) j).
Proof. intros.
  specialize (getBlocks_inject _ _ _ H0). intros.
  specialize (REACH_inject _ _ _ H (getBlocks vals1) (getBlocks vals2) H3). intros.
  eapply initial_SM_wd; try eassumption.
    intros. destruct (H4 _ H5) as [b2 [d1 [J R]]]. eapply (H1 _ _ _ J).
Qed.   

Lemma halted_check_aux: forall mu m1 v1 b1 b2 delta (WD: SM_wd mu),
      join (foreign_of mu)
           (fun b =>
              if myBlocksSrc mu b && REACH m1 (exportedSrc mu (v1 :: nil)) b
              then local_of mu b
              else None) b1 = Some (b2, delta) ->
      as_inj mu b1= Some (b2, delta).
Proof. intros; apply joinI.
  destruct (joinD_Some _ _ _ _ _ H) as [FRG | [FRG LOC]]; clear H.
    left. apply foreign_in_extern; eassumption.
    right. 
    remember (myBlocksSrc mu b1 && REACH m1 (exportedSrc mu (v1 :: nil)) b1) as d.
    destruct d; inv LOC; apply eq_sym in Heqd. rewrite H0.
    destruct (disjoint_extern_local _ WD b1). rewrite H. split; trivial.
    rewrite H in H0; discriminate.
Qed.

Goal (*Lemma halted_check:*) forall mu m1 m2 v1 v2
      (MInj: Mem.inject (as_inj mu) m1 m2)
      (VInj: val_inject (locvisible_of mu) v1 v2) (WD: SM_wd mu),
      exists pubSrc' pubTgt' nu, 
        (pubSrc' = fun b => (myBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (myBlocksTgt mu b) &&
                            (REACH m2 (exportedTgt mu (v2::nil)) b))
        /\
        (nu = replace_locals mu pubSrc' pubTgt')
         /\ SM_wd nu /\
        val_inject (shared_of nu) v1 v2 /\
        Mem.inject (shared_of nu) m1 m2. (*/\ val_valid v2 m2*)
Proof. intros. eexists; eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. 
      apply replace_locals_wd; trivial.
      intros. rewrite andb_true_iff in H. destruct H. 
      assert (VALS12: Forall2 (val_inject (as_inj mu)) (v1 :: nil) (v2 :: nil)).
        constructor. eapply val_inject_incr; try eassumption.
                      unfold locvisible_of, join; simpl.
                      intros b; intros. remember (foreign_of mu b). 
                      destruct o; apply eq_sym in Heqo.
                         destruct p. inv H1. apply foreign_in_all; eassumption.
                      apply local_in_all; eassumption.
        constructor.
      destruct (REACH_local_REACH _ WD _ _ (v1::nil) (v2::nil) MInj VALS12 _ H0 H)
        as [b2 [d1 [LOC12 R2]]].
      exists b2, d1. rewrite LOC12, R2.
      destruct (local_myBlocks _ WD _ _ _ LOC12) as [_ [? _]].
      rewrite H1. intuition.
      intros. apply andb_true_iff in H. intuition.
  rewrite replace_locals_shared. 
  split. inv VInj; try constructor.
         econstructor.
         unfold locvisible_of in H.
         apply joinI.
         destruct (joinD_Some _ _ _ _ _ H); clear H.
            left; eassumption.
         destruct H0. right. split; trivial.
         remember (myBlocksSrc mu b1 && REACH m1 (exportedSrc mu (Vptr b1 ofs1 :: nil)) b1) as d. 
              destruct d; apply eq_sym in Heqd. assumption.
         apply andb_false_iff in Heqd. 
              destruct (local_myBlocks _ WD _ _ _ H0) as [? [? [? [? ?]]]].
              rewrite H1 in *.
              destruct Heqd; try discriminate.
              assert (REACH m1 (exportedSrc mu (Vptr b1 ofs1 :: nil)) b1 = true).
                apply REACHAX. exists nil. constructor.
                unfold exportedSrc, sharedSrc, getBlocks. simpl.
                 destruct (eq_block b1 b1). simpl. trivial.
                 exfalso. apply n; trivial.
              rewrite H7 in H6. inv H6.
           reflexivity.
    split.
         (*goal Mem.mem_inj*) 
           split; intros. 
           (*subgoal mi_perm*)
             apply halted_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_align*)
             apply halted_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_memval*)
             assert (X:= halted_check_aux _ _ _ _ _ _ WD H); trivial.
             assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MInj) _ _ _ _ X H0). clear X.
             inv MV; try econstructor; try reflexivity.
                   apply joinI.
                   remember (foreign_of mu b0) as f.
                   destruct f; apply eq_sym in Heqf.
                      destruct p. rewrite (foreign_in_all _ _ _ _ Heqf) in H3. left; trivial.
                   right. split; trivial.
                  admit. (*ok -- it's in a GOAL*; claim need not hold -- b0 might only be mapped by unknown_of mu*) 
 admit. admit. admit. admit.
(*THIS Need not hold - if we want to enforce that there are no
pointers to unknown, we can probbaly do so by adding
 the match_inject_clause: 
    match_validblocks: forall d j c1 m1 c2 m2, 
          match_state d j c1 m1 c2 m2 ->
          mem_inject (as_inj mu) m1 m2 /\
          mem_inject (locvisible mu) m1 m2,

and /or tweaking match_norm. cf the Lemma halted_loc_check below.
*)
Qed.

Lemma halted_loc_check_aux: forall mu m1 v1 b1 b2 delta (WD: SM_wd mu),
      join (foreign_of mu)
           (fun b =>
              if myBlocksSrc mu b && REACH m1 (exportedSrc mu (v1 :: nil)) b
              then local_of mu b
              else None) b1 = Some (b2, delta) ->
      locvisible_of mu b1= Some (b2, delta).
Proof. intros; apply joinI.
  destruct (joinD_Some _ _ _ _ _ H) as [FRG | [FRG LOC]]; 
     rewrite FRG; clear H.
    left; trivial.
    right; split; trivial. 
    remember (myBlocksSrc mu b1 && REACH m1 (exportedSrc mu (v1 :: nil)) b1) as d.
    destruct d; inv LOC; apply eq_sym in Heqd. trivial.
Qed.

Lemma halted_loc_check: forall mu m1 m2 v1 v2
      (MInj: Mem.inject (locvisible_of mu)  m1 m2)
      (VInj: val_inject (locvisible_of mu) v1 v2) (WD: SM_wd mu),
      exists pubSrc' pubTgt' nu, 
        (pubSrc' = fun b => (myBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (myBlocksTgt mu b) &&
                            (REACH m2 (exportedTgt mu (v2::nil)) b))
        /\
        (nu = replace_locals mu pubSrc' pubTgt')
         /\ SM_wd nu /\
        val_inject (shared_of nu) v1 v2 /\
        Mem.inject (shared_of nu) m1 m2. (*/\ val_valid v2 m2*)
Proof. intros. eexists; eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. 
      apply replace_locals_wd; trivial.
      intros. rewrite andb_true_iff in H. destruct H.
      assert (X: forall b, exportedSrc mu (v1 :: nil) b = true ->
                 exists jb d, locvisible_of mu b = Some (jb, d) /\ 
                              exportedTgt mu (v2 :: nil) jb = true).
          intros. unfold exportedSrc in H1. unfold exportedTgt. 
          apply orb_true_iff in H1. 
          destruct H1. unfold getBlocks in H1; simpl in H1. destruct v1; inv H1. 
               destruct (eq_block b0 b); inv H3. 
               inv VInj.  exists b2, delta. split; trivial. 
                    simpl. apply orb_true_iff. left. unfold getBlocks; simpl.
                  destruct (eq_block b2 b2); trivial. exfalso. apply n; trivial.
               rewrite locvisible_sharedprivate.
                unfold join.
                destruct (shared_SrcTgt _ WD _ H1) as [b2 [d1 [SH TGT]]].
                rewrite SH. exists b2, d1; split; trivial.
                rewrite TGT. destruct (getBlocks (v2 :: nil) b2); trivial.
 
      destruct (REACH_inject _ _ _ MInj _ (exportedTgt mu (v2 :: nil)) X _ H0)
           as [b2 [d1 [lv exp]]].
        clear X. destruct (joinD_Some _ _ _ _ _ lv).
            destruct (foreign_DomRng _ WD _ _ _ H1) as [? [? [? ?]]].
            rewrite H in H4. inv H4.
         destruct H1. rewrite H2. exists b2, d1. rewrite exp.
            destruct (local_myBlocks _ WD _ _ _ H2) as [? [? [? [? ?]]]].
             rewrite H4. intuition.
     intros. apply andb_true_iff in H. destruct H; trivial.
   split. rewrite replace_locals_shared.
          inv VInj; try econstructor; trivial.
          apply joinI. 
          destruct (joinD_Some _ _ _ _ _ H); clear H.
             left; trivial.
          destruct H0 as [FRG LOC]. rewrite FRG, LOC.
          right; split; trivial.
          destruct (local_myBlocks _ WD _ _ _ LOC) as [? [? [? [? [? ?]]]]].
          rewrite H. simpl.
          assert (R: REACH m1 (exportedSrc mu (Vptr b1 ofs1:: nil)) b1 = true).
            apply REACHAX. exists nil.
            constructor. unfold exportedSrc, getBlocks; simpl.
            apply orb_true_iff; left.
            destruct (eq_block b1 b1); trivial. exfalso. apply n; trivial.              
          rewrite R. trivial.
    split. rewrite replace_locals_shared.
         (*goal Mem.mem_inj*) 
           split; intros. 
           (*subgoal mi_perm*) apply halted_loc_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_align*) apply halted_loc_check_aux in H; trivial. 
             eapply MInj; try eassumption.
           (*subgoal mi_memval*)
             assert (X:= halted_loc_check_aux _ _ _ _ _ _ WD H); trivial.
             assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MInj) _ _ _ _ X H0). clear X.
             inv MV; try econstructor; try reflexivity.
                   apply joinI.
                   destruct (joinD_Some _ _ _ _ _ H3) as [FRG | [FRG LOC]]; clear H3; rewrite FRG.
                     left; reflexivity.
                     right; split; trivial.
                      destruct (local_myBlocks _ WD _ _ _ LOC) as [? [? [? [? [? ?]]]]]. 
                      rewrite H3, LOC. simpl.
                      destruct (joinD_Some _ _ _ _ _ H) as [FRG1 | [FRG1 LOC1]]; clear H.
                        assert (REACH m1 (exportedSrc mu (v1 :: nil)) b0 = true).
                        apply REACHAX. exists ((b1,ofs)::nil).
                          apply eq_sym in H1.
                          econstructor. constructor.
                            unfold exportedSrc. apply orb_true_iff; right.  
                            apply sharedSrc_iff. unfold shared_of, join; simpl. rewrite FRG1. exists b2, delta; trivial.
                            assumption. apply H1. rewrite H. trivial. 
                      remember (myBlocksSrc mu b1 && REACH m1 (exportedSrc mu (v1 :: nil)) b1) as d.
                        destruct d; apply eq_sym in Heqd; inv LOC1.
                          apply andb_true_iff in Heqd. destruct Heqd.
                          assert (REACH m1 (exportedSrc mu (v1 :: nil)) b0 = true).
                          apply REACHAX. apply REACHAX in H10. destruct H10 as [L RL].
                          eexists. eapply reach_cons. apply RL. 
                          eassumption. rewrite <- H1. reflexivity.
                          rewrite H11. trivial.
    intros. rewrite replace_locals_shared.
            assert (LV:= Mem.mi_freeblocks _ _ _ MInj _ H).
            apply joinD_None in LV. destruct LV as [FRG LOC].
            apply joinI_None. trivial.
            rewrite LOC.
            destruct (myBlocksSrc mu b && REACH m1 (exportedSrc mu (v1 :: nil)) b); trivial.
    intros. rewrite replace_locals_shared in H.
            eapply (Mem.mi_mappedblocks _ _ _ MInj b b' delta).
            apply halted_loc_check_aux in H; trivial.
    rewrite replace_locals_shared. intros b1; intros. 
            apply halted_loc_check_aux in H0; trivial.
            apply halted_loc_check_aux in H1; trivial.
            eapply MInj; eassumption.
    rewrite replace_locals_shared; intros.
            apply halted_loc_check_aux in H; trivial.
            eapply MInj; eassumption. 
Qed.

Module SM_simulation. Section SharedMemory_simulation_inject. 
  Context {F1 V1 C1 G2 C2:Type}
          (Sem1 : @EffectSem (Genv.t F1 V1) C1)
          (Sem2 : @EffectSem G2 C2)
          (ge1: Genv.t F1 V1)
          (ge2: G2)
          (entry_points : list (val * val * signature)).

  Record SM_simulation_inject := 
  { core_data : Type;
    match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    match_sm_wd: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          SM_wd mu;

    (*match-state is closed wrt all normalization wrt potential downstream 
      structured injections. This is our current way of saying that the core 
      doesn't care about blocks in "unknown" region*)
    match_norm: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          forall mu23, (SM_wd mu23 /\ DomTgt mu = DomSrc mu23 /\
                        myBlocksTgt mu = myBlocksSrc mu23 /\
                       (forall b, pubBlocksTgt mu b = true -> pubBlocksSrc mu23 b = true) /\
                       (forall b, frgnBlocksTgt mu b = true -> frgnBlocksSrc mu23 b = true)) ->
          match_state d (sm_extern_normalize mu mu23) c1 m1 c2 m2;

   (*an alternative to match_norm might be this, but it does not 
     seem to be transitive:
    match_TrimUnknown: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          match_state d (TrimUnknown mu) c1 m1 c2 m2;*)

   (*another alternative to match_norm might be this, but it does not seem
     to work in the transitivity proof of afterExternal:
    match_EeraseUnknown: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          match_state d (TrimUnknown mu) c1 m1 c2 m2;*)

    match_validblocks: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          sm_valid mu m1 m2;               

    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2 DomS DomT,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 

          Forall2 (val_inject j) vals1 vals2 ->
         (* Forall2 (Val.has_type) vals2 (sig_args sig) ->*)

        (*the next two conditions are required to guarantee intialSM_wd*)
         (forall b1 b2 d, j b1 = Some (b2, d) -> 
                          DomS b1 = true /\ DomT b2 = true) ->
         (forall b, REACH m2 (getBlocks vals2) b = true -> DomT b = true) ->

       exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            (*Lemma StructuredInjections.initial_SM_as_inj implies 
              that Mem.inject (initial_SM DomS
                                       DomT 
                                       (REACH m1 (getBlocks vals1)) 
                                       (REACH m2 (getBlocks vals2)) j)
                              m1 m2 holds*)
            match_state cd (initial_SM DomS
                                       DomT 
                                       (REACH m1 (getBlocks vals1)) 
                                       (REACH m2 (getBlocks vals2)) j)
                           c1 m1 c2 m2;

    core_diagram : 
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 mu m2,
        match_state cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
          match_state cd' mu' st1' m1' st2' m2' /\

          (*formally, the following 2 conditions already follow
            from match_state_wd and match_state_sm_valid, but we
            temporarily duplicate them here in order to check that 
            the constructions in the transitivity proof are ok:*)
          SM_wd mu' /\ sm_valid mu' m1' m2' /\

          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    effcore_diagram : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall cd st2 mu m2,
        match_state cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_state cd' mu' st1' m1' st2' m2' /\

          (*could add the following 2 assertions here, too, but 
             we checked already that they're satisfied in the previous
             clause SM_wd mu' /\ sm_valid mu' m1' m2' /\*)

          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
              (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
               core_ord cd' cd)) /\ 

             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (myBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true)));

    (*additionally requires U1 to be disjoint from unknown etc, in UHyp*)
    effcore_diagram_strong : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall cd st2 mu m2
        (UHyp: forall b ofs, U1 b ofs = true -> 
                  (myBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true)),
        match_state cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 

          match_state cd' mu' st1' m1' st2' m2' /\

          (*could add the following 2 assertions here, too, but 
             we checked already that they're satisfied in the previous
             clause SM_wd mu' /\ sm_valid mu' m1' m2' /\*)

          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
              (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
               core_ord cd' cd)) /\

             forall b ofs, U2 b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (myBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true)));

    core_halted : forall cd mu c1 m1 c2 m2 v1,
      match_state cd mu c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->

      exists v2, 
             Mem.inject (as_inj mu) m1 m2 /\
             val_inject (as_inj mu) v1 v2 /\
             halted Sem2 c2 = Some v2;

    (*One might consider variants that require Mem.inject j ma m2 on smaller 
        injections j than as_inj mu, omething like this: 
    core_halted : forall cd mu c1 m1 c2 m2 v1,
      match_state cd mu c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->

      exists v2, 
             Mem.inject (locvisible_of mu) m1 m2 /\
             val_inject (locvisible_of mu) v1 v2;

     (-follows from halted_loc_check:-) 
      /\
      exists pubSrc' pubTgt' nu, 
        (pubSrc' = fun b => (myBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (myBlocksTgt mu b) &&
                            (REACH m2 (exportedTgt mu (v2::nil)) b))
        /\
        (nu = replace_locals mu pubSrc' pubTgt')
         /\
        val_inject (shared_of nu) v1 v2 /\
        halted Sem2 c2 = Some v2 /\
        Mem.inject (shared_of nu) m1 m2; (*/\ val_valid v2 m2*)
     But this would mean to carry the invariant Mem.inject (locvisible_of mu) m1 m2
         around, ie through corediagram, afterexternal etc (ie require match_state 
         to imply Mem.inject loc_visible ... 
       This maybe possible, but is maybe not required.
    *)
 
    core_at_external : 
      forall cd mu c1 m1 c2 m2 e vals1 ef_sig,
        match_state cd mu c1 m1 c2 m2 ->
        at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
        ( 
          Mem.inject (as_inj mu) m1 m2 /\ 
         (*add back later: meminj_preserves_globals ge1 (as_inj mu) /\ *)

         exists vals2, 
            Forall2 (val_inject (as_inj mu)) vals1 vals2 /\ 

            (*Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\*)
            at_external Sem2 c2 = Some (e,ef_sig,vals2)); 
          (*Like in coreHalted, one might consider a variant that
             asserts Mem.inject m1 m2 and val_inject vals1 vals2
             w.r.t. shared_of mu instead of as_inj mu.
            Again this might be possible, but probably only at the price of
               pushing such an invariant through corediagram etc.*)

    eff_after_external: (*we don't duplicate the claims
            that follow from the checks above*)
      forall cd mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
        (*standard assumptions:*)
        (MemInjMu: Mem.inject (as_inj mu) m1 m2)
        (MatchMu: match_state cd mu st1 m1 st2 m2)
        (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals1))

        (*We include the clause AtExtTgt to ensure that vals2 is 
         uniquely determined. We have e=e' and ef_sig=ef_sig' by the
         at_external clause, but omitting the hypothesis AtExtTgt would
         result in in 2 not necesssarily equal target argument lists
         in language 3 in the transitivity, as val_inject is not functional
         (in the case where the left value is Vundef) *)
        (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals2)) 

        (*maybe reactivate later: meminj_preserves_globals ge1 (as_inj mu) -> *)

        (ValInjMu: Forall2 (val_inject (as_inj mu)) vals1 vals2)  
        (*maybe reactivate later: meminj_preserves_globals ge1 (shared_of mu) ->*)

        pubSrc' (pubSrcHyp: pubSrc' = fun b => andb (myBlocksSrc mu b)
                                                    (REACH m1 (exportedSrc mu vals1) b))

        pubTgt' (pubTgtHyp: pubTgt' = fun b => andb (myBlocksTgt mu b)
                                                    (REACH m2 (exportedTgt mu vals2) b))

        nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),

      (*follows, as proven by Lemma eff_after_check1: SM_wd nu /\ sm_valid nu m1 m2 /\*)
      (*follows, as proven by Lemma eff_after_check1: Mem.inject (as_inj nu) m1 m2 /\*)
      (*follows, as proven by Lemma eff_after_check1: Forall2 (val_inject (as_inj nu)) vals1 vals2 /\*)
      forall nu' ret1 m1' ret2 m2'
        (INC: extern_incr nu nu')  
        (SEP: sm_inject_separated nu nu' m1 m2)

        (WDnu': SM_wd nu') (SMvalNu': sm_valid nu' m1' m2')

        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (*(RetTypeTgt: Val.has_type ret2 (proj_sig_res ef_sig))*)

        frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (myBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

        frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (myBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')

        (*follows, as proven by Lemma eff_after_check2: SM_wd mu' /\ sm_valid mu' m1' m2' /\*)
        (*follows, as proven by Lemma eff_after_check3: Mem.inject (as_inj mu') m1' m2' /\*)
        (*follows, as proven by Lemma eff_after_check3: val_inject (as_inj mu') ret1 ret2 /\*)

        (*follows, as proven by Lemma eff_after_check4: inject_incr (as_inj mu) (as_inj mu') /\*)
        (*follows, as proven by Lemma eff_after_check5: sm_inject_separated mu mu' m1 m2 /\*)
 
         (UnchPrivSrc: Mem.unchanged_on (fun b ofs => myBlocksSrc nu b = true /\ 
                                                      pubBlocksSrc nu b = false) m1 m1') 

         (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' mu' st1' m1' st2' m2'
}.

(*End SharedMemory_simulation_inject. *)

(*End SM_simulation.*)

(*The following lemma shows that the incoming memories are injected not only
by initial_SM, but by locvisible(initial_SM). The
above lemma halted_loc_check is the counterpart of this. *)
Lemma initial_locvisible: forall (I:SM_simulation_inject) v1 v2 sig,
  In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2 DomS DomT,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 

          Forall2 (val_inject j) vals1 vals2 ->
          (*Forall2 (Val.has_type) vals2 (sig_args sig) ->*)

        (*the next two conditions are required to guarantee intialSM_wd*)
         (forall b1 b2 d, j b1 = Some (b2, d) -> 
                          DomS b1 = true /\ DomT b2 = true) ->
         (forall b, REACH m2 (getBlocks vals2) b = true -> DomT b = true) ->

       exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state I cd (initial_SM DomS
                                       DomT 
                                       (REACH m1 (getBlocks vals1)) 
                                       (REACH m2 (getBlocks vals2)) j)
                           c1 m1 c2 m2 /\
           Mem.inject (locvisible_of (initial_SM DomS
                                       DomT 
                                       (REACH m1 (getBlocks vals1)) 
                                       (REACH m2 (getBlocks vals2)) j)) m1 m2.
Proof. intros.
  destruct (core_initial I _ _ _ H _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4)
    as [cd [c2 [IC MS]]].
  exists cd, c2.
  split; trivial.
  split. trivial.
  specialize (match_validblocks I _ _ _ _ _ _ MS). intros VB.
  unfold locvisible_of. simpl.
  split; intros.
    split; intros.
       apply joinD_Some in H5. 
       destruct H5; simpl.
       remember (REACH m1 (getBlocks vals1) b1).
       destruct b; try inv H5.
         eapply H1. apply H8. apply H6.
       destruct H5; discriminate. 
    apply joinD_Some in H5. 
       destruct H5; simpl.
       remember (REACH m1 (getBlocks vals1) b1).
       destruct b; try inv H5.
         eapply H1. apply H8. apply H6.
       destruct H5; discriminate.
    apply joinD_Some in H5. 
       destruct H5; simpl.
       remember (REACH m1 (getBlocks vals1) b1).
       destruct b; try inv H5.
         specialize (Mem.mi_memval  _ _ _ (Mem.mi_inj _ _ _ H1) _ _ _ _ H8 H6).
         intros. inv H5; try econstructor.
           apply joinI. left. 
           assert (R: REACH m1 (getBlocks vals1) b0 = true).
             apply REACHAX. apply eq_sym in Heqb. apply REACHAX in Heqb.
             destruct Heqb as [L HL].
             eexists. eapply reach_cons. apply HL. apply H6. rewrite <- H7. reflexivity.
           rewrite R. eassumption.
           trivial.
       destruct H5; discriminate.

    unfold join. remember (REACH m1 (getBlocks vals1) b).
      destruct b0; trivial.
      remember (j b). destruct o; trivial. destruct p; apply eq_sym in Heqo.
       exfalso. apply H5. eapply VB. apply (H3 _ _ _ Heqo).
    apply joinD_Some in H5. 
       destruct H5; simpl.
       remember (REACH m1 (getBlocks vals1) b).
       destruct b0; try inv H5. eapply VB. apply (H3 _ _ _ H7).
       destruct H5; discriminate.

   intros b1; intros. 
    apply joinD_Some in H6. 
      destruct H6; simpl.
      remember (REACH m1 (getBlocks vals1) b1).
       destruct b; try inv H6.
       apply joinD_Some in H7. 
         destruct H7; simpl.
         remember (REACH m1 (getBlocks vals1) b2).
          destruct b; try inv H6.
          eapply H1; eassumption.
       destruct H6; discriminate. 
     destruct H6; discriminate.

     apply joinD_Some in H5. 
       destruct H5; simpl.
       remember (REACH m1 (getBlocks vals1) b).
       destruct b0; try inv H5.
         eapply H1; eassumption.
       destruct H5; discriminate.
Qed.

End SharedMemory_simulation_inject. 

End SM_simulation.

Definition FLIP mu := 
  match mu with
    Build_SM_Injection DomS DomT mySrc myTgt pSrc pTgt fSrc fTgt extern local =>
    Build_SM_Injection DomS DomT
                      (fun b => DomS b && negb (mySrc b))
                      (fun b => DomT b && negb (myTgt b))
                       fSrc fTgt pSrc pTgt local extern
  end.

Lemma SAWP_wd: forall mu (WD: SM_wd mu), SM_wd (FLIP mu).
intros.
destruct mu; simpl in *.
destruct WD.
split; intros; simpl in *.
  destruct (extern_DomRng _ _ _ H) as [? [? [? ?]]].
    rewrite H0, H1, H2, H3. simpl. intuition.
  destruct (local_DomRng _ _ _ H) as [? ?].
    rewrite H0, H1. simpl.
    rewrite (myBlocksDomSrc _ H0).
    rewrite (myBlocksDomTgt _ H1).
    simpl. intuition.
  eapply frgnSrc. apply H. 
  eapply pubSrc. apply H.
  apply andb_true_iff in H. apply H.
  apply andb_true_iff in H. apply H.
  destruct (frgnBlocksDomTgt _ H).
    rewrite H0, H1. intuition.
  specialize (myBlocksDomTgt b). 
    rewrite (pubBlocksLocalTgt _ H) in *.
    rewrite myBlocksDomTgt; intuition.
Qed.

Lemma FLIPmyBlocksSrc: forall mu,
  myBlocksSrc (FLIP mu) = 
  fun b => DomSrc mu b && negb (myBlocksSrc mu b).
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPmyBlocksTgt: forall mu,
  myBlocksTgt (FLIP mu) = 
  fun b => DomTgt mu b && negb (myBlocksTgt mu b).
Proof. intros. destruct mu; reflexivity. Qed.

Lemma FLIPpubBlocksSrc: forall mu,
  pubBlocksSrc (FLIP mu) = frgnBlocksSrc mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPpubBlocksTgt: forall mu,
  pubBlocksTgt (FLIP mu) = frgnBlocksTgt mu.
Proof. intros. destruct mu; reflexivity. Qed.

Lemma FLIPfrgnBlocksSrc: forall mu,
  frgnBlocksSrc (FLIP mu) = pubBlocksSrc mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPfrgnBlocksTgt: forall mu,
  frgnBlocksTgt (FLIP mu) = pubBlocksTgt mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPlocal: forall mu,
  local_of (FLIP mu) = extern_of mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPextern: forall mu,
  extern_of (FLIP mu) = local_of mu.
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma RelyGuaranteeSrc: forall mu Esrc m m'
              (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (myBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
               (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m'),
         Mem.unchanged_on (fun b ofs => myBlocksSrc (FLIP mu) b = true /\ 
                                        pubBlocksSrc (FLIP mu) b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros. simpl.
  rewrite FLIPmyBlocksSrc, FLIPpubBlocksSrc in H.
  case_eq (Esrc b ofs); intros; trivial; simpl in *.
  destruct H.
  destruct (SrcHyp _ _ H0); clear Unch SrcHyp.
    rewrite H2 in *. simpl in *.
    apply andb_true_iff in H. intuition.
  rewrite H2 in *. intuition.
Qed.

Lemma RelyGuaranteeTgt: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu)
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (myBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (myBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
            m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty),
            Mem.unchanged_on (local_out_of_reach (FLIP mu) m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  rewrite FLIPmyBlocksTgt in H. apply andb_true_iff in H.
  destruct H. 
  destruct F as [b1 [d1 [Frg ES]]].
    clear -H2.
    destruct (myBlocksTgt mu b2); intuition.
  rewrite FLIPlocal in H1.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  destruct (SrcHyp _ _ ES); clear SrcHyp.
    rewrite H3 in *. inv CC.
  destruct (H1 b1 d1); clear H1.
     apply foreign_in_extern; assumption.
     exfalso. apply H4; clear H4.
     apply (SrcPerm _ _ ES).
  rewrite FLIPpubBlocksSrc in H4. rewrite H4 in H3. inv H3.
Qed.

Lemma unchanged_on_perm: forall (P:block -> Z -> Prop) m m'
      (Unch: Mem.unchanged_on P m m'),
      Mem.unchanged_on (fun b z => P b z /\ Mem.perm m b z Max Nonempty) m m'.
Proof. intros.
split; intros; eapply Unch; eauto.
apply H. apply H.
Qed.

Lemma unchanged_on_perm': forall (P:block -> Z -> Prop) m m'
      (Unch: Mem.unchanged_on (fun b z => P b z \/ ~ Mem.perm m b z Max Nonempty) m m'),
      Mem.unchanged_on P m m'.
Proof. intros.
split; intros; eapply Unch; eauto.
Qed.

Lemma RGSrc_multicore: forall mu Esrc m m'
              (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (myBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
               (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m')
          nu, 
         (forall b, myBlocksSrc nu b = true -> myBlocksSrc mu b = false) ->
         (forall b, pubBlocksSrc nu b = true <-> 
                   (frgnBlocksSrc mu b && myBlocksSrc nu b) = true) ->
         (forall b1 b2 d, pub_of nu b1 = Some(b2, d) -> foreign_of mu b1 = Some(b2,d)) ->
         Mem.unchanged_on (fun b ofs => myBlocksSrc nu b = true /\ 
                                        pubBlocksSrc nu b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros. simpl.
  destruct H2. rename b into b1. specialize (H _ H2).
  case_eq (Esrc b1 ofs); intros; trivial; simpl in *.
  destruct (SrcHyp _ _ H4); clear Unch SrcHyp.
    rewrite H in *. intuition.
  destruct (H0 b1) as [_ ?].
    rewrite H5, H2 in H6.
    rewrite H6 in H3; intuition.
Qed.

Lemma RGTgt_multicore: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu)
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (myBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (myBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
            m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty)
            nu
         (X1: forall b, myBlocksTgt nu b = true -> myBlocksTgt mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              myBlocksTgt nu b1 || myBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
            Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  specialize (X1 _ H). 
  destruct (F X1) as [b1 [d1 [Frg ES]]]; clear F.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  clear DD.
  destruct (SrcHyp _ _ ES); clear SrcHyp.
    rewrite H2 in *. inv CC.
  clear H2.
  specialize (X2 _ _ _ Frg). rewrite H in X2.
  rewrite orb_true_r in X2. specialize (X2 (eq_refl _)). 
  destruct (H1 b1 d1).
    apply pub_in_local. apply X2.
    exfalso. apply H2. apply (SrcPerm _ _ ES).
  rewrite (pubSrcContra _ _ H2) in X2. inv X2. 
Qed.