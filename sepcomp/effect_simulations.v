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
         (TGT: forall b, pTgt' b = true -> locBlocksTgt mu b = true),
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

Lemma replace_locals_locBlocksSrc: forall mu pubSrc' pubTgt',
      locBlocksSrc (replace_locals mu pubSrc' pubTgt') = locBlocksSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_locals_locBlocksTgt: forall mu pubSrc' pubTgt',
      locBlocksTgt (replace_locals mu pubSrc' pubTgt') = locBlocksTgt mu.
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
               locBlocksTgt mu b = false /\ DomTgt mu b = true),
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

Lemma replace_externs_foreign: forall mu frgSrc' frgTgt',
      foreign_of (replace_externs mu frgSrc' frgTgt') = 
      fun b : block => if frgSrc' b then extern_of mu b else None.
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

Lemma replace_externs_locBlocksSrc: forall mu frgSrc' frgTgt',
      locBlocksSrc (replace_externs mu frgSrc' frgTgt') = locBlocksSrc mu.
Proof. intros. 
destruct mu as [DomS DomT myblocksSrc myblocksTgt pSrc pTgt fSrc fTgt extern local]; simpl in *.
reflexivity.
Qed.

Lemma replace_externs_locBlocksTgt: forall mu frgSrc' frgTgt',
      locBlocksTgt (replace_externs mu frgSrc' frgTgt') = locBlocksTgt mu.
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

Definition reach_closed m (X: Values.block -> bool) : Prop :=
  (forall b, REACH m X b = true <-> X b = true).

Lemma sm_normalize_inject: forall mu12 mu23 
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true)
          (HypMyblocks: locBlocksTgt mu12 = locBlocksSrc mu23)
          m1
          (RC: reach_closed m1 (fun b => locBlocksSrc mu12 b || frgnBlocksSrc mu12 b))
          m2 (Inj12: Mem.inject (as_inj mu12) m1 m2)
          m3 (Inj23: Mem.inject (as_inj mu23) m2 m3),
      Mem.inject (as_inj (sm_extern_normalize mu12 mu23)) m1 m2.
Proof. intros.
split; intros.
  split; intros.
    apply (sm_extern_normalize_as_inj_norm _ _ WD12) in H.
     eapply Inj12; eassumption.
    apply (sm_extern_normalize_as_inj_norm _ _ WD12) in H.
     eapply Inj12; eassumption.
    destruct (joinD_Some _ _ _ _ _ H) as [NEXT12 | [NEXT12 LOC12]].
    (*extern*) rewrite sm_extern_normalize_extern in NEXT12.
       apply normalize_norm in NEXT12. destruct NEXT12 as [EXT12 [[b3 d2] EXT23]].
       assert (AsInj12 := extern_in_all _ _ _ _ EXT12).
       specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Inj12) _ _ _ _ AsInj12 H0). intros.
       inv H1; try constructor.
       assert (Perm2: Mem.perm m2 b2 (ofs+delta) Cur Readable).
         eapply Inj12; eassumption.
       assert (AsInj23 := extern_in_all _ _ _ _ EXT23).
       specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Inj23) _ _ _ _ AsInj23 Perm2). intros.
       rewrite <- H3 in H1. clear H3.
       inv H1.
       econstructor. eapply sm_extern_normalize_as_inj_norm2; try eassumption. reflexivity.
    (*local*) rewrite sm_extern_normalize_extern in NEXT12.
       rewrite sm_extern_normalize_local in LOC12.
       assert (AsInj12 := local_in_all _ WD12 _ _ _ LOC12).
       specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Inj12) _ _ _ _ AsInj12 H0). intros.
       inv H1; try constructor.
       rename b3 into b2'. rename b0 into b1'.
       rename delta into d1. rename delta0 into delta'.
       assert (local_of mu12 b1' = Some (b2', delta') \/ foreign_of mu12 b1' = Some (b2', delta')).
         destruct (joinD_Some _ _ _ _ _ H4) as [EXT | [EXT LOC]]; clear H4.
           destruct (RC b1') as [A _]; clear RC.
             apply orb_true_iff in A.
             destruct A.
               destruct (extern_DomRng _ WD12 _ _ _ EXT). congruence.
             right. destruct (frgnSrc _ WD12 _ H1) as [bb2 [dd2 [F2 FT3]]].
               rewrite (foreign_in_extern _ _ _ _ F2) in EXT. inv EXT. assumption.
           apply REACHAX. clear A.
             eexists. apply eq_sym in H2.
             eapply reach_cons; try eassumption. 
             apply reach_nil. destruct (local_DomRng _ WD12 _ _ _ LOC12).
                rewrite H1; trivial. 
         left; assumption. 
       eapply memval_inject_ptr with (delta:=delta').
         destruct H1. apply joinI; right.
              rewrite sm_extern_normalize_local, sm_extern_normalize_extern. split; trivial.
              destruct (disjoint_extern_local _ WD12 b1').
                  unfold normalize. rewrite H5; trivial.
              rewrite H5 in H1; discriminate.
         apply joinI; left. 
           destruct (foreign_DomRng _ WD12 _ _ _ H1) as [? [? [? [? [? [? ?]]]]]].
           rewrite sm_extern_normalize_extern.
           eapply normalize_norm. 
           split. apply foreign_in_extern; assumption.
           apply HypFrgn in H10.
           destruct (frgnSrc _ WD23 _ H10) as [b3 [d2 [F23 T3]]].
           rewrite (foreign_in_extern _ _ _ _  F23). exists (b3,d2); trivial. reflexivity.
   assert (as_inj mu12 b = None). eapply Inj12; assumption.
     remember (as_inj (sm_extern_normalize mu12 mu23) b) as d.
     destruct d; trivial. apply eq_sym in Heqd. destruct p.
     apply sm_extern_normalize_as_inj_norm in Heqd; trivial. rewrite Heqd in H0; discriminate.
   apply sm_extern_normalize_as_inj_norm in H; trivial.
     eapply Inj12; eassumption.
   intros b1 b1'; intros. 
     apply sm_extern_normalize_as_inj_norm in H0; trivial.
     apply sm_extern_normalize_as_inj_norm in H1; trivial.
     eapply Inj12; eassumption.
   apply sm_extern_normalize_as_inj_norm in H; trivial.
     eapply Inj12; eassumption.
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
         (locBSrc : locBlocksSrc mu b1 = true),
      exists b2 d, local_of mu b1 = Some (b2, d).
Proof. intros.
  destruct (REACH_as_inj _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R (fun b => true)) as [b2 [d [ASINJ RR]]].
    trivial.
  exists b2, d.
  destruct (joinD_Some _ _ _ _ _ ASINJ).
    destruct (extern_DomRng _ WD _ _ _ H) as [ZZ _]; rewrite ZZ in locBSrc.
    intuition.
  apply H.
Qed.
 
Lemma REACH_extern: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1 
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
         (locBSrc : locBlocksSrc mu b1 = false),
      exists b2 d, extern_of mu b1 = Some (b2, d).
Proof. intros.
  destruct (REACH_as_inj _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R (fun b => true)) as [b2 [d [ASINJ RR]]].
    trivial.
  exists b2, d.
  destruct (joinD_Some _ _ _ _ _ ASINJ). assumption.
  destruct H.
  destruct (local_DomRng _ WD _ _ _ H0) as [ZZ _]; rewrite ZZ in locBSrc.
  intuition.
Qed.

(*The following six or so results are key lemmas about REACH - they say
  that blocks exported in SRC are injected, to blocks exported by TGT,
  preserving the locBlocks-structure, ie distinction betwene public and
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
         (locBSrc : locBlocksSrc mu b1 = true),
      exists b2 d, local_of mu b1 = Some (b2, d) /\ 
                   REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_as_inj_REACH _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R) as [b2 [d [ASINJ RR]]].
  exists b2, d. split; trivial.
  destruct (joinD_Some _ _ _ _ _ ASINJ).
    destruct (extern_DomRng _ WD _ _ _ H) as [ZZ _]; rewrite ZZ in locBSrc.
    intuition.
  apply H.
Qed.

Lemma REACH_local_REACH': forall mu m1 vals1  b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
        (WD: SM_wd mu) m2 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2)
        (locBSrc : locBlocksSrc mu b1 = true) b2 d
        (LOC: local_of mu b1 = Some (b2, d)), 
     REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_local_REACH _ WD _ _ _ _ MemInjMu ValInjMu _ R locBSrc)
  as [bb [dd [LL RR]]]. rewrite LL in LOC. inv LOC. trivial.
Qed.

Lemma REACH_extern_REACH: forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (exportedSrc mu vals1) b1 = true)
         (locBSrc : locBlocksSrc mu b1 = false),
      exists b2 d, extern_of mu b1 = Some (b2, d) /\ 
                   REACH m2 (exportedTgt mu vals2) b2 = true.
Proof. intros.
  destruct (REACH_as_inj_REACH _ WD _ _ _ _ MemInjMu ValInjMu 
            _ R) as [b2 [d [ASINJ RR]]].
  exists b2, d. split; trivial.
  destruct (joinD_Some _ _ _ _ _ ASINJ).
    apply H.
  destruct H as [_ H]. 
    destruct (local_DomRng _ WD _ _ _ H) as [ZZ _]; rewrite ZZ in locBSrc.
    intuition.
Qed.

Goal forall m1 mu (WD: SM_wd mu) vals b, pubBlocksSrc mu b = true ->
           REACH m1 (exportedSrc mu vals) b = true.
Proof. intros. apply REACH_increasing.
  apply orb_true_iff. right. apply pubSrc_shared; trivial. 
Qed.

Definition local_out_of_reach mu (m : mem) (b : block) (ofs : Z): Prop := 
  locBlocksTgt mu b = true /\ 
  forall b0 delta, local_of mu b0 = Some (b, delta) -> 
                  (~ Mem.perm m b0 (ofs - delta) Max Nonempty \/
                   pubBlocksSrc mu b0 = false).

Definition genv2blocksBool {F V : Type} (ge : Genv.t F V):= 
  (fun b =>
      match Genv.invert_symbol ge b with
        Some id => true
      | None => false
      end,
   fun b => match Genv.find_var_info ge b with
                  Some gv => true
                | None => false
            end).

Lemma genvblocksBool_char1: forall F V (ge : Genv.t F V) b,
     (fst (genv2blocksBool ge)) b = true <-> fst (genv2blocks ge) b.
Proof. intros.
  remember (genv2blocksBool ge) as X.
  destruct X as [f g]; simpl. 
  remember (genv2blocks ge) as Y.
  destruct Y as [f' g']; simpl.
  unfold genv2blocksBool in HeqX. inv HeqX.
  unfold genv2blocks in HeqY. inv HeqY.
  remember (Genv.invert_symbol ge b) as d.
  destruct d; apply eq_sym in Heqd.
    split; intros; trivial.  
    exists i. rewrite (Genv.invert_find_symbol _ _ Heqd). trivial.
  split; intros; try congruence.
    destruct H.
    apply Genv.find_invert_symbol in H. congruence.
Qed.

Lemma genvblocksBool_char2: forall F V (ge : Genv.t F V) b,
     (snd (genv2blocksBool ge)) b = true <-> snd (genv2blocks ge) b.
Proof. intros.
  remember (genv2blocksBool ge) as X.
  destruct X as [f g]; simpl. 
  remember (genv2blocks ge) as Y.
  destruct Y as [f' g']; simpl.
  unfold genv2blocksBool in HeqX. inv HeqX.
  unfold genv2blocks in HeqY. inv HeqY.
  remember (Genv.find_var_info ge b) as d.
  destruct d; apply eq_sym in Heqd.
    split; intros; trivial.  
    exists g; trivial.
  split; intros; try congruence.
    destruct H. congruence.
Qed.

Lemma genvblocksBool_char1': forall F V (ge : Genv.t F V) b,
     (fst (genv2blocksBool ge)) b = false <-> ~ fst (genv2blocks ge) b.
Proof. intros.
  split; intros.
    intros N. apply genvblocksBool_char1 in N. congruence.
  remember (fst (genv2blocksBool ge) b) as d.
  destruct d; trivial. apply eq_sym in Heqd.
    apply genvblocksBool_char1 in Heqd. congruence.
Qed.

Lemma genvblocksBool_char2': forall F V (ge : Genv.t F V) b,
     (snd (genv2blocksBool ge)) b = false <-> ~ snd (genv2blocks ge) b.
Proof. intros.
  split; intros.
    intros N. apply genvblocksBool_char2 in N. congruence.
  remember (snd (genv2blocksBool ge) b) as d.
  destruct d; trivial. apply eq_sym in Heqd.
    apply genvblocksBool_char2 in Heqd. congruence.
Qed.

Definition isGlobalBlock {F V : Type} (ge : Genv.t F V) :=
  fun b => (fst (genv2blocksBool ge)) b || (snd (genv2blocksBool ge)) b.

Lemma genvs_domain_eq_isGlobal: forall {F1 V1 F2 V2} ge1 ge2
                       (DomainEQ: @genvs_domain_eq F1 V1 F2 V2 ge1 ge2),
       isGlobalBlock ge1 = isGlobalBlock ge2.
Proof. intros.
  destruct DomainEQ.
  extensionality b. unfold isGlobalBlock.
  remember (fst (genv2blocksBool ge1) b) as d.
  destruct d; apply eq_sym in Heqd.
    apply genvblocksBool_char1 in Heqd. 
    apply H in Heqd.
    apply genvblocksBool_char1 in Heqd.
    rewrite Heqd. trivial.
  apply genvblocksBool_char1' in Heqd.
    remember (fst (genv2blocksBool ge2) b) as q.
    destruct q; apply eq_sym in Heqq.  
      apply genvblocksBool_char1 in Heqq.
      apply H in Heqq. contradiction.
  clear Heqd Heqq.
  remember (snd (genv2blocksBool ge1) b) as d.
  destruct d; apply eq_sym in Heqd.
    apply genvblocksBool_char2 in Heqd. 
    apply H0 in Heqd.
    apply genvblocksBool_char2 in Heqd.
    rewrite Heqd. trivial.
  apply genvblocksBool_char2' in Heqd.
    remember (snd (genv2blocksBool ge2) b) as q.
    destruct q; apply eq_sym in Heqq.  
      apply genvblocksBool_char2 in Heqq.
      apply H0 in Heqq. contradiction.
   trivial.
Qed.
    
Lemma meminj_preserves_globals_isGlobalBlock: forall {F V} (g: Genv.t F V)
               j (PG: meminj_preserves_globals g j)
               b (GB: isGlobalBlock g b = true),
      j b = Some (b, 0).
Proof. intros.
  unfold isGlobalBlock in GB.
  apply meminj_preserves_genv2blocks in PG.
  destruct PG as [PGa [PGb PGc]].
  apply orb_true_iff in GB.
  destruct GB.
    apply genvblocksBool_char1 in H. apply (PGa _ H).
    apply genvblocksBool_char2 in H. apply (PGb _ H).
Qed.

(*version of Lemma meminj_preserves_globals_initSM below,
  for the (old) definition of clause match_genv that uses foriegn_of*)
Lemma meminj_preserves_globals_initSM_frgn: forall {F1 V1} (ge: Genv.t F1 V1) j
                  (PG : meminj_preserves_globals ge j) DomS DomT m R Y
                  (HR: forall b, isGlobalBlock ge b = true -> R b = true),
      meminj_preserves_globals ge (foreign_of (initial_SM DomS DomT (REACH m R) Y j)).
Proof. intros. 
    apply meminj_preserves_genv2blocks.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    unfold initial_SM; split; intros; simpl in *.
       specialize (PGa _ H). rewrite PGa.
       assert (REACH m R b = true).
         apply REACH_increasing. apply HR. 
         unfold isGlobalBlock, genv2blocksBool; simpl.
         destruct H as [id ID].
         apply Genv.find_invert_symbol in ID. rewrite ID. reflexivity.
       rewrite H0; trivial.
    split; intros; simpl in *.
       specialize (PGb _ H). rewrite PGb.
       assert (REACH m R b = true).
         apply REACH_increasing. apply HR. 
         unfold isGlobalBlock, genv2blocksBool; simpl.
         destruct H as [id ID]. rewrite ID. intuition.
       rewrite H0; trivial.
     apply (PGc _ _ delta H).
       remember (REACH m R b1) as d.
       destruct d; congruence.
Qed.

Lemma meminj_preserves_globals_initSM: forall {F1 V1} (ge: Genv.t F1 V1) j
                  (PG : meminj_preserves_globals ge j) DomS DomT X Y,
      meminj_preserves_globals ge (extern_of (initial_SM DomS DomT X Y j)).
Proof. intros. apply PG. Qed.

Lemma meminj_preserves_globals_init_REACH_frgn:
      forall {F1 V1} (ge: Genv.t F1 V1) j
             (PG : meminj_preserves_globals ge j) DomS DomT m R Y
             (HR: forall b, isGlobalBlock ge b = true -> R b = true),
      (forall b, isGlobalBlock ge b = true -> 
                 frgnBlocksSrc (initial_SM DomS DomT (REACH m R) Y j) b = true).
Proof. intros.
  unfold initial_SM; simpl.
  apply REACH_increasing. apply (HR _ H).
Qed.

Lemma core_initial_wd : forall {F1 V1 F2 V2} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) 
                               vals1 m1 j vals2 m2 DomS DomT
          (MInj: Mem.inject j m1 m2)
          (VInj: Forall2 (val_inject j) vals1 vals2)
          (HypJ: forall b1 b2 d, j b1 = Some (b2, d) -> DomS b1 = true /\ DomT b2 = true)
          (R: forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> 
                        DomT b = true)
          (PG: meminj_preserves_globals ge1 j)
          (GenvsDomEQ: genvs_domain_eq ge1 ge2)
          (HS: forall b, DomS b = true -> Mem.valid_block m1 b)
          (HT: forall b, DomT b = true -> Mem.valid_block m2 b)
          mu (Hmu: mu = initial_SM DomS DomT
                         (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
                         (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j),
       (forall b, REACH m1 (fun b' => isGlobalBlock ge1 b' || getBlocks vals1 b') b = true -> 
                  DomS b = true) /\
       SM_wd mu /\ sm_valid mu m1 m2 /\ 
       meminj_preserves_globals ge1 (extern_of mu) /\
       (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true).
Proof. intros.
  specialize (getBlocks_inject _ _ _ VInj); intros.
  assert (HR: forall b1, REACH m1 (fun b : block => isGlobalBlock ge1 b || getBlocks vals1 b) b1 = true ->
            exists b2 z, j b1 = Some (b2, z) /\
                         REACH m2 (fun b : block => isGlobalBlock ge2 b || getBlocks vals2 b) b2 = true).
         eapply (REACH_inject _ _ _ MInj).
              intros. clear R mu Hmu HS HT.
              apply orb_true_iff in H0.
              destruct H0. 
                rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG _ H0).
                exists b, 0. rewrite <- (genvs_domain_eq_isGlobal _ _ GenvsDomEQ).
                intuition.
              destruct (H _ H0) as [b2 [d [J GB2]]]. exists b2, d; intuition.
  split. intros. 
         destruct (HR _ H0) as [b2 [d [J R2]]].
         apply (HypJ _ _ _ J).
  subst.
  split. eapply initial_SM_wd; try eassumption.
           intros. destruct (HR _ H0) as [b2 [d [J R2]]].
             apply (HypJ _ _ _ J).
  split. split; intros. apply (HS _ H0). apply (HT _ H0). 
  split. eapply meminj_preserves_globals_initSM; intuition.
  apply meminj_preserves_globals_init_REACH_frgn; try eassumption.
    intuition.
Qed.

Lemma intern_incr_meminj_preserves_globals_frgn: 
      forall {F V} (ge: Genv.t F V) mu
             (PG: meminj_preserves_globals ge (foreign_of mu))
             mu' (Inc: intern_incr mu mu'),
      meminj_preserves_globals ge (foreign_of mu').
Proof. intros.
  rewrite (intern_incr_foreign _ _ Inc) in PG. trivial.
Qed.

Lemma intern_incr_meminj_preserves_globals: 
      forall {F V} (ge: Genv.t F V) mu
             (PG: meminj_preserves_globals ge (extern_of mu) /\
                  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true))
             mu' (Inc: intern_incr mu mu'),
      meminj_preserves_globals ge (extern_of mu') /\
      (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu' b = true).
Proof. intros.
  assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by apply Inc.
  rewrite (intern_incr_extern _ _ Inc), FF in PG.
  assumption. 
Qed.

Lemma replace_externs_meminj_preserves_globals:
      forall {F V} (ge: Genv.t F V) nu
          (PG: meminj_preserves_globals ge (extern_of nu) /\
               (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc nu b = true))
          mu  fSrc fTgt (Hyp: mu = replace_externs nu fSrc fTgt)
          (FRG: forall b, frgnBlocksSrc nu b = true -> fSrc b = true),
      meminj_preserves_globals ge (extern_of mu) /\
      (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof. intros. destruct PG as [PG FF]; subst.
split.
    rewrite replace_externs_extern.
    apply PG.
intros. destruct nu; simpl in *. 
  apply (FRG _ (FF _ H)). 
Qed.

Lemma after_external_meminj_preserves_globals: 
      forall {F V} (ge: Genv.t F V) mu (WDmu : SM_wd mu)
             (PG: meminj_preserves_globals ge (extern_of mu) /\
                 (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true))
             nu pubSrc' pubTgt' vals1 m1
             (pubSrcHyp: pubSrc' = fun b => andb (locBlocksSrc mu b)
                                                (REACH m1 (exportedSrc mu vals1) b))

      
             (Hnu: nu = replace_locals mu pubSrc' pubTgt')
             nu' (WDnu' : SM_wd nu') (INC: extern_incr nu nu')  
             m2 (SMV: sm_valid mu m1 m2) (SEP: sm_inject_separated nu nu' m1 m2)
             frgnSrc' ret1 m1'
             (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (locBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

             frgnTgt' ret2 m2'
             (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (locBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

             mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt'),
      meminj_preserves_globals ge (extern_of mu') /\
     (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu' b = true).
Proof. intros. subst.
destruct PG as [PG FF].
assert (Fincr:= extern_incr_extern _ _ INC).
rewrite replace_locals_extern in Fincr. 
split.
  rewrite replace_externs_extern.
  apply meminj_preserves_genv2blocks.
  apply meminj_preserves_genv2blocks in PG.
  destruct PG as [PGa [PGb PGc]].
  split; intros.
    specialize (PGa _ H). clear PGb PGc. 
    apply (Fincr _ _ _ PGa). 
  split; intros. 
    specialize (PGb _ H). clear PGa PGc.
    apply (Fincr _ _ _ PGb).
  remember (extern_of mu b1) as d.
    destruct d; apply eq_sym in Heqd.
      destruct p. 
      rewrite (Fincr _ _ _ Heqd) in H0.
      inv H0. apply (PGc _ _ _ H Heqd).
    destruct SEP as [SEPa [SEPb SEPc]].
      rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in *. 
      remember (local_of mu b1) as q.
      destruct q; apply eq_sym in Heqq.
        destruct p. destruct INC as [_ [? _]]. 
        rewrite replace_locals_local in H1. rewrite H1 in Heqq.
        destruct (disjoint_extern_local _ WDnu' b1); congruence.
      assert (as_inj mu b1 = None).
        apply joinI_None; assumption.
      destruct (SEPa b1 b2 delta H1 (extern_in_all _ _ _ _ H0)).
      specialize (PGb _ H).
         assert (DomTgt mu b2 = true).
            apply (extern_DomRng _ WDmu _ _ _ PGb).
         congruence.
intros. 
  specialize (FF _ H). subst. 
  assert (F': frgnBlocksSrc nu' b = true).
    eapply INC. rewrite replace_locals_frgnBlocksSrc. assumption.
  rewrite replace_externs_frgnBlocksSrc.
  destruct (frgnBlocksDomSrc _ WDnu' _ F').
    rewrite H1, H0. simpl.
    apply (frgnSrc_shared _ WDnu') in F'.
    apply REACH_increasing. unfold exportedSrc.
    rewrite F'. intuition.
Qed.

Module SM_simulation. Section SharedMemory_simulation_inject. 
  Context {F1 V1 C1 F2 V2 C2:Type}
          (Sem1 : @EffectSem (Genv.t F1 V1) C1)
          (Sem2 : @EffectSem (Genv.t F2 V2) C2)
          (ge1: Genv.t F1 V1)
          (ge2: Genv.t F2 V2)
          (entry_points : list (val * val * signature)).

  Record SM_simulation_inject := 
  { core_data : Type;
    match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    match_sm_wd: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          SM_wd mu;

    genvs_dom_eq: genvs_domain_eq ge1 ge2;

(*
    match_genv: forall d mu c1 m1 c2 m2,  match_state d mu c1 m1 c2 m2 -> 
          meminj_preserves_globals ge1 (foreign_of mu); 
    The following formulation using extern_of is slightly stronger, since it requires
    that the third condition of mem-inj_preserves_globals be satisfied
    for all of extern_of, bit just foreign_of, so is preserved by
    extern_incr and the adaptation of frgSrc by replaces_externs in 
    rule afterExternal*)
    match_genv: forall d mu c1 m1 c2 m2 (MC:match_state d mu c1 m1 c2 m2),
          meminj_preserves_globals ge1 (extern_of mu) /\
          (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true); 

    (*match-state is closed wrt all normalization wrt potential downstream 
      structured injections. This is our current way of saying that the core 
      doesn't care about blocks in "unknown" region*)
    match_norm: forall d mu c1 m1 c2 m2, 
          match_state d mu c1 m1 c2 m2 ->
          forall mu23, (SM_wd mu23 /\ DomTgt mu = DomSrc mu23 /\
                        locBlocksTgt mu = locBlocksSrc mu23 /\
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
          meminj_preserves_globals ge1 j ->

        (*the next two conditions are required to guarantee intialSM_wd*)
         (forall b1 b2 d, j b1 = Some (b2, d) -> 
                          DomS b1 = true /\ DomT b2 = true) ->
         (forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> DomT b = true) ->

        (*the next two conditions ensure the initialSM satisfies sm_valid*)
         (forall b, DomS b = true -> Mem.valid_block m1 b) ->
         (forall b, DomT b = true -> Mem.valid_block m2 b) ->

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
                                       (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
                                       (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
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
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Mem.valid_block m1 b1 /\ U1 b1 (ofs-delta1) = true)));

    (*additionally requires U1 to be disjoint from unknown etc, in UHyp*)
    effcore_diagram_strong : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall cd st2 mu m2
        (UHyp: forall b1 z, U1 b1 z = true -> 
                  (locBlocksSrc mu b1 = true \/ frgnBlocksSrc mu b1 = true)),
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
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true)));

      effcore_diagram_strong_perm : 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

      forall cd st2 mu m2
        (UHyp: forall b1 z, U1 b1 z = true -> 
                  (locBlocksSrc mu b1 = true \/ frgnBlocksSrc mu b1 = true)),
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
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           U1 b1 (ofs-delta1) = true /\ 
                           Mem.perm m1 b1 (ofs-delta1) Max Nonempty)));

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
        (pubSrc' = fun b => (locBlocksSrc mu b) &&
                            (REACH m1 (exportedSrc mu (v1::nil)) b))
        /\
        (pubTgt' = fun b => (locBlocksTgt mu b) &&
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
        ( Mem.inject (as_inj mu) m1 m2 /\ 

         exists vals2, 
            Forall2 (val_inject (as_inj mu)) vals1 vals2 /\ 
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

        pubSrc' (pubSrcHyp: pubSrc' = fun b => andb (locBlocksSrc mu b)
                                                    (REACH m1 (exportedSrc mu vals1) b))

        pubTgt' (pubTgtHyp: pubTgt' = fun b => andb (locBlocksTgt mu b)
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

        frgnSrc' (frgnSrcHyp: frgnSrc' = fun b => andb (DomSrc nu' b)
                                                 (andb (negb (locBlocksSrc nu' b)) 
                                                       (REACH m1' (exportedSrc nu' (ret1::nil)) b)))

        frgnTgt' (frgnTgtHyp: frgnTgt' = fun b => andb (DomTgt nu' b)
                                                 (andb (negb (locBlocksTgt nu' b))
                                                       (REACH m2' (exportedTgt nu' (ret2::nil)) b)))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')

        (*follows, as proven by Lemma eff_after_check2: SM_wd mu' /\ sm_valid mu' m1' m2' /\*)
        (*follows, as proven by Lemma eff_after_check3: Mem.inject (as_inj mu') m1' m2' /\*)
        (*follows, as proven by Lemma eff_after_check3: val_inject (as_inj mu') ret1 ret2 /\*)

        (*follows, as proven by Lemma eff_after_check4: inject_incr (as_inj mu) (as_inj mu') /\*)
        (*follows, as proven by Lemma eff_after_check5: sm_inject_separated mu mu' m1 m2 /\*)
 
         (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
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
          meminj_preserves_globals ge1 j ->
          (*Forall2 (Val.has_type) vals2 (sig_args sig) ->*)

        (*the next two conditions are required to guarantee intialSM_wd*)
         (forall b1 b2 d, j b1 = Some (b2, d) -> 
                          DomS b1 = true /\ DomT b2 = true) ->
         (forall b, REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b = true -> DomT b = true) ->

        (*the next two conditions ensure the initialSM satisfies sm_valid*)
         (forall b, DomS b = true -> Mem.valid_block m1 b) ->
         (forall b, DomT b = true -> Mem.valid_block m2 b) ->

       exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state I cd (initial_SM DomS
                                       DomT 
                                       (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))
                                       (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
                           c1 m1 c2 m2 /\
           Mem.inject (locvisible_of (initial_SM DomS
                                       DomT 
                                       (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
                                       (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)) m1 m2.
Proof. intros.
  destruct (core_initial I _ _ _ H _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4 H5 H6 H7)
    as [cd [c2 [IC MS]]].
  clear H6 H7.
  exists cd, c2.
  split; trivial.
  split. trivial.
  specialize (match_validblocks I _ _ _ _ _ _ MS). intros VB.
  unfold locvisible_of. simpl.
  split; intros.
    split; intros.
       apply joinD_Some in H6. 
       destruct H6; simpl.
       remember (REACH m1 (fun b : block => isGlobalBlock ge1 b || 
                                             getBlocks vals1 b) b1).
       destruct b; try inv H6.
         solve [eapply H1; eassumption].
       destruct H6; discriminate. 
    apply joinD_Some in H6. 
       destruct H6; simpl.
       remember (REACH m1 (fun b : block => isGlobalBlock ge1 b || 
                                             getBlocks vals1 b) b1).
       destruct b; try inv H6.
         solve [eapply H1; eassumption].
       destruct H6; discriminate.
    apply joinD_Some in H6. 
       destruct H6; simpl.
       remember (REACH m1 (fun b : block => isGlobalBlock ge1 b || 
                                             getBlocks vals1 b) b1).
       destruct b; try inv H6.
         specialize (Mem.mi_memval  _ _ _ (Mem.mi_inj _ _ _ H1) _ _ _ _ H9 H7).
         intros. inv H6; try econstructor.
           apply joinI. left. 
           assert (R: REACH m1 (fun b : block => isGlobalBlock ge1 b || 
                                             getBlocks vals1 b) b0 = true).
             apply REACHAX. apply eq_sym in Heqb. apply REACHAX in Heqb.
             destruct Heqb as [L HL].
             eexists. eapply reach_cons. apply HL. apply H7. rewrite <- H8. reflexivity.
           rewrite R. eassumption.
           trivial.
       destruct H6; discriminate.

    unfold join. 
      remember (REACH m1 (fun b' : block => isGlobalBlock ge1 b' || 
                                            getBlocks vals1 b') b).
      destruct b0; trivial.
      remember (j b). destruct o; trivial. destruct p; apply eq_sym in Heqo.
       exfalso. apply H6. eapply VB. apply (H4 _ _ _ Heqo).
    apply joinD_Some in H6. 
       destruct H6; simpl.
       remember (REACH m1 (fun b' : block => isGlobalBlock ge1 b' || 
                                             getBlocks vals1 b') b).
       destruct b0; try inv H6. eapply VB. apply (H4 _ _ _ H8).
       destruct H6; discriminate.

   intros b1; intros. 
    apply joinD_Some in H7. 
      destruct H7; simpl.
      remember (REACH m1 (fun b : block => isGlobalBlock ge1 b || 
                                            getBlocks vals1 b) b1).
       destruct b; try inv H7.
       apply joinD_Some in H8. 
         destruct H8; simpl.
         remember (REACH m1 (fun b : block => isGlobalBlock ge1 b || 
                                              getBlocks vals1 b) b2).
          destruct b; try inv H7.
          eapply H1; eassumption.
       destruct H7; discriminate. 
     destruct H7; discriminate.

     apply joinD_Some in H6. 
       destruct H6; simpl.
       remember (REACH m1 (fun b' : block => isGlobalBlock ge1 b' || 
                                             getBlocks vals1 b') b).
       destruct b0; try inv H6.
         eapply H1; eassumption.
       destruct H6; discriminate.
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
    rewrite (locBlocksDomSrc _ H0).
    rewrite (locBlocksDomTgt _ H1).
    simpl. intuition.
  eapply frgnSrc. apply H. 
  eapply pubSrc. apply H.
  apply andb_true_iff in H. apply H.
  apply andb_true_iff in H. apply H.
  destruct (frgnBlocksDomTgt _ H).
    rewrite H0, H1. intuition.
  specialize (locBlocksDomTgt b). 
    rewrite (pubBlocksLocalTgt _ H) in *.
    rewrite locBlocksDomTgt; intuition.
Qed.

Lemma FLIPlocBlocksSrc: forall mu,
  locBlocksSrc (FLIP mu) = 
  fun b => DomSrc mu b && negb (locBlocksSrc mu b).
Proof. intros. destruct mu; reflexivity. Qed. 

Lemma FLIPlocBlocksTgt: forall mu,
  locBlocksTgt (FLIP mu) = 
  fun b => DomTgt mu b && negb (locBlocksTgt mu b).
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
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
               (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m'),
         Mem.unchanged_on (fun b ofs => locBlocksSrc (FLIP mu) b = true /\ 
                                        pubBlocksSrc (FLIP mu) b = false) m m'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption.
  intros. simpl.
  rewrite FLIPlocBlocksSrc, FLIPpubBlocksSrc in H.
  case_eq (Esrc b ofs); intros; trivial; simpl in *.
  destruct H.
  destruct (SrcHyp _ _ H0); clear Unch SrcHyp.
    rewrite H2 in *. simpl in *.
    apply andb_true_iff in H. intuition.
  rewrite H2 in *. intuition.
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

Lemma RelyGuaranteeTgtPerm: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
            (*m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty)*),
            Mem.unchanged_on (local_out_of_reach (FLIP mu) m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl.
  case_eq (Etgt b ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  rewrite FLIPlocBlocksTgt in H. apply andb_true_iff in H.
  destruct H. 
  destruct F as [b1 [d1 [Frg [ES P]]]].
    clear -H2.
    destruct (locBlocksTgt mu b); intuition.
  rewrite FLIPlocal in H1.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  destruct (SrcHyp _ _ ES); clear SrcHyp.
    rewrite H3 in *. inv CC.
  destruct (H1 b1 d1); clear H1.
     apply foreign_in_extern; assumption.
     exfalso. apply H4; clear H4.
     assumption.
  rewrite FLIPpubBlocksSrc in H4. rewrite H4 in H3. inv H3.
Qed.

Lemma RelyGuaranteeTgt: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu)
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
            m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty),
            Mem.unchanged_on (local_out_of_reach (FLIP mu) m1) m2 m2'.
Proof. intros. 
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  rewrite FLIPlocBlocksTgt in H. apply andb_true_iff in H.
  destruct H. 
  destruct F as [b1 [d1 [Frg ES]]].
    clear -H2.
    destruct (locBlocksTgt mu b2); intuition.
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


Lemma RGSrc_multicore: forall mu Esrc m m'
              (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
               (Unch: Mem.unchanged_on (fun b z => Esrc b z = false) m m')
          nu, 
         (forall b, locBlocksSrc nu b = true -> locBlocksSrc mu b = false) ->
         (forall b, pubBlocksSrc nu b = true <-> 
                   (frgnBlocksSrc mu b && locBlocksSrc nu b) = true) ->
         (forall b1 b2 d, pub_of nu b1 = Some(b2, d) -> foreign_of mu b1 = Some(b2,d)) ->
         Mem.unchanged_on (fun b ofs => locBlocksSrc nu b = true /\ 
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
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
            m1 (SrcPerm: forall b1 z, Esrc b1 z = true -> Mem.perm m1 b1 z Max Nonempty)
            nu
         (X1: forall b, locBlocksTgt nu b = true -> locBlocksTgt mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksTgt nu b1 || locBlocksTgt nu b2 = true ->
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

Lemma RGTgt_multicorePerm: forall mu Etgt Esrc m2 m2' (WD: SM_wd mu) m1
            (TgtHyp: forall b ofs, Etgt b ofs = true -> 
                       (Mem.valid_block m2 b /\
                         (locBlocksTgt mu b = false ->
                           exists b1 delta1, foreign_of mu b1 = Some(b,delta1) /\
                           Esrc b1 (ofs-delta1) = true /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty)))
            (Unch2: Mem.unchanged_on (fun b z => Etgt b z = false) m2 m2')
            (SrcHyp: forall b ofs, Esrc b ofs = true -> 
                  (locBlocksSrc mu b = true \/ frgnBlocksSrc mu b = true))
            nu
         (X1: forall b, locBlocksTgt nu b = true -> locBlocksTgt mu b = false)
         (X2: forall b1 b2 d, foreign_of mu b1 = Some(b2, d) -> 
                              locBlocksTgt nu b1 || locBlocksTgt nu b2 = true ->
                              pub_of nu b1 = Some(b2,d)),
            Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'.
Proof. intros.
  eapply mem_unchanged_on_sub; try eassumption; clear Unch2.
  intros. simpl. rename b into b2.
  case_eq (Etgt b2 ofs); intros; trivial.
  destruct (TgtHyp _ _ H0) as [VB2 F]; clear TgtHyp.
  destruct H.
  specialize (X1 _ H). 
  destruct (F X1) as [b1 [d1 [Frg [ES P]]]]; clear F.
  destruct (foreign_DomRng _ WD _ _ _ Frg) as [AA [BB [CC [DD [EE [FF [GG HH]]]]]]].
  clear DD.
  destruct (SrcHyp _ _ ES); clear SrcHyp.
    rewrite H2 in *. inv CC.
  clear H2.
  specialize (X2 _ _ _ Frg). rewrite H in X2.
  rewrite orb_true_r in X2. specialize (X2 (eq_refl _)). 
  destruct (H1 b1 d1).
    apply pub_in_local. apply X2.
    contradiction.
  rewrite (pubSrcContra _ _ H2) in X2. inv X2. 
Qed.