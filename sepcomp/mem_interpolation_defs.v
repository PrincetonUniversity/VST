Require Import Events. (*needed for standard definitions of 
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Maps.
Require Import msl.Axioms.

Require Import sepcomp.mem_lemmas.

Goal forall m b ofs p (H: ~ Mem.perm m b ofs p Nonempty), PMap.get b (Mem.mem_access m) ofs p = None.
intros. unfold Mem.perm in *.
remember (PMap.get b (Mem.mem_access m) ofs p) as pp.
destruct pp; simpl in *. exfalso. apply H. apply perm_any_N.
trivial.
Qed.

Definition isSource j m1 (b2:block) (ofs2:Z) b : option Z :=
  match j b with None => None
         | Some (bb,delta) => if eq_block b2 bb 
                                             then if Mem.perm_dec m1 b (ofs2 - delta) Max Nonempty 
                                                     then Some (ofs2 - delta)  else None
                                             else None
  end.

Lemma isSource_NoneE: forall j m b2 ofs2 b1, None = isSource j m b2 ofs2 b1 ->
    j b1 = None \/ (exists b, exists delta, j b1 = Some (b,delta) /\ b<>b2) \/
    (exists delta, j b1 = Some(b2,delta) /\ ~ Mem.perm m b1 (ofs2-delta) Max Nonempty).
Proof. intros. unfold isSource in H.
  remember (j b1) as zz.
  destruct zz. destruct p.
     destruct (eq_block b2 p). subst.
       remember (Mem.perm_dec m b1 (ofs2 - z) Max Nonempty) as d.
       destruct d; inv H. right. right. exists z. split; trivial. 
     right. left. exists p. exists z. split; auto. 
  left; trivial. 
Qed.

Lemma isSource_SomeE: forall j m b2 ofs2 b1 ofs1, Some ofs1 = isSource j m b2 ofs2 b1 ->
    exists delta, j b1 = Some(b2,delta) /\ Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros. unfold isSource in H.
  remember (j b1) as zz.
  destruct zz. destruct p.
     destruct (eq_block b2 p). subst.
       remember (Mem.perm_dec m b1 (ofs2 - z) Max Nonempty) as d.
       destruct d; inv H. exists z. split; trivial. split; trivial. omega.
    inv H.
  inv H.
Qed.

Lemma isSource_SomeI: forall j m b2 ofs2 b1 delta, 
       j b1 = Some(b2,delta) -> Mem.perm m b1 (ofs2 - delta) Max Nonempty ->
        isSource j m b2 ofs2 b1 = Some (ofs2-delta).
Proof. intros. unfold isSource. rewrite H.
     destruct (eq_block b2 b2). subst.
       remember (Mem.perm_dec m b1 (ofs2 - delta) Max Nonempty) as d.
       destruct d. trivial.  exfalso. apply (n H0).
     exfalso. apply n. trivial.
Qed.

Lemma isSource_SomeI': forall j m b2 ofs1 b1 delta, 
       j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
        isSource j m b2 (ofs1+delta) b1 = Some ofs1.
Proof. intros. unfold isSource. rewrite H.
     destruct (eq_block b2 b2). subst.
       assert (ofs1 = ofs1 + delta - delta). omega. rewrite <- H1.
       remember (Mem.perm_dec m b1 ofs1 Max Nonempty) as d.
       destruct d. trivial.  exfalso. apply (n H0).
     exfalso. apply n. trivial.
Qed.
Require Import Coq.PArith.BinPos.

Definition sourceN (n:block) (j:meminj) (m:mem)
                   (b2:block) (ofs2:Z): option(block * Z) :=
Pos.peano_rect
            (fun p => option(block * Z))
            (match isSource j m b2 ofs2 1%positive
             with Some ofs1 => Some(1%positive, ofs1)
                | None => None
             end)
            (fun p Hp => match isSource j m b2 ofs2 (Pos.succ p)
             with Some ofs1 => Some (Pos.succ p, ofs1)
                | None => Hp
             end) 
            n.

Lemma sourceN_SomeE: forall j m b2 ofs2 n b1 ofs1, 
    sourceN n j m b2 ofs2 = Some(b1,ofs1) ->
    exists delta, (b1 <= n)%positive /\ j b1 = Some(b2,delta) /\ 
                  Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros j m b2 ofs. 
apply (Pos.peano_ind 
         (fun p => forall (b1 : block) (ofs1 : Z),
              sourceN p j m b2 ofs = Some (b1, ofs1) ->
              exists delta : Z,
              (b1 <= p)%positive /\
              j b1 = Some (b2, delta) /\
              Mem.perm m b1 ofs1 Max Nonempty /\ ofs = ofs1 + delta)).
intros.
  unfold sourceN in H. rewrite Pos.peano_rect_base in H.
  remember (isSource j m b2 ofs 1%positive) as d.
  destruct d; inv H.
     apply isSource_SomeE in Heqd.
     destruct Heqd as [delta [J [P Off]]].
     exists delta.
     repeat split; auto; xomega.
intros.
  unfold sourceN in H0.
  rewrite Pos.peano_rect_succ in H0.
  remember (isSource j m b2 ofs (Pos.succ p)) as d.
  destruct d. inv H0. clear H.
     apply isSource_SomeE in Heqd.
     destruct Heqd as [delta [J [P Off]]].
     exists delta.
     repeat split; auto; xomega.
  specialize (H _ _ H0). clear H0.
     destruct H as [delta [D [J [P Off]]]].
     exists delta.
     repeat split; auto; xomega.
Qed.

Lemma sourceN_NoneE: forall j m b2 ofs2 n, 
    sourceN n j m b2 ofs2 = None -> 
    forall b1 delta, (b1 <= n)%positive -> j b1 = Some(b2,delta) ->
                     ~ Mem.perm m b1 (ofs2-delta) Max Nonempty.
Proof. intros j m b2 ofs2.
apply (Pos.peano_ind 
         (fun p => sourceN p j m b2 ofs2 = None ->
              forall (b1 : positive) (delta : Z),
              (b1 <= p)%positive ->
              j b1 = Some (b2, delta) ->
              ~ Mem.perm m b1 (ofs2 - delta) Max Nonempty)).
intros. assert (b1 = 1%positive). xomega. subst. clear H0. 
  unfold sourceN in H. rewrite Pos.peano_rect_base in H.
  remember (isSource j m b2 ofs2 1%positive) as d.
  destruct d. inv H.
  apply isSource_NoneE in Heqd.
  destruct Heqd. congruence. 
  destruct H0. destruct H0 as [b [delta1 [J P]]]. 
                rewrite J in H1. inv H1. exfalso. apply P. trivial. 
    destruct H0 as [ddelta [J P]]. rewrite J in H1. inv H1. assumption. 
intros.
  unfold sourceN in H0.
  rewrite Pos.peano_rect_succ in H0.
  remember (isSource j m b2 ofs2 (Pos.succ p)) as d.
  destruct d. inv H0. 
  specialize (H H0). clear H0.
  apply isSource_NoneE in Heqd.
  destruct Heqd.
    apply H; trivial. 
    destruct (peq b1 (Pos.succ p)). 
      subst. congruence.
      xomega. 
  destruct H0. destruct H0 as [b [delta1 [J P]]]. 
    apply H; trivial. 
    destruct (peq b1 (Pos.succ p)). 
      subst. congruence.
      xomega. 
   destruct H0 as [ddelta [J P]].
    destruct (peq b1 (Pos.succ p)). 
      subst. rewrite J in H2. inv H2. assumption.
    apply H; trivial. xomega.
Qed.  

Lemma sourceN_SomeI: forall n j m b2 b1 ofs1 delta (OV:Mem.meminj_no_overlap j m),
   j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
   (b1 <= n)%positive ->
   sourceN n j m b2 (ofs1+delta) = Some(b1,ofs1).
Proof. intros. 
  remember (sourceN n j m b2 (ofs1 + delta)) as src.
  destruct src; apply eq_sym in Heqsrc. 
  Focus 2. assert (ZZ:= sourceN_NoneE _ _ _ _ _ Heqsrc _ _ H1 H).
           exfalso. assert (ofs1 + delta - delta = ofs1). omega.
                    rewrite H2 in ZZ. apply (ZZ H0).
  (*Some*) destruct p as [b off].
       apply sourceN_SomeE in Heqsrc.
       destruct Heqsrc as [d [Hd [J [P X]]]].
       destruct (eq_block b1 b).
          subst. rewrite H in J. inv J.
          assert (ofs1 = off). omega. subst. trivial.
       destruct (OV _ _ _ _ _ _ _ _ n0 H J H0 P).
          exfalso. apply H2; trivial.
       rewrite X in H2. exfalso. apply H2. trivial.
Qed.  

Definition  source j m (b2:block) (ofs2:Z) : option(block * Z) :=
   if plt 1%positive (Mem.nextblock m) 
   then sourceN (Pos.pred (Mem.nextblock m)) j m b2 ofs2
   else None.

Lemma perm_nextblock_gt_1: forall m b ofs k p (P: Mem.perm m b ofs k p),
  Plt 1 (Mem.nextblock m).
Proof.
  intros. apply Mem.perm_valid_block in P. 
  unfold Mem.valid_block in P. xomega.
Qed.

Lemma source_SomeE: forall j m (b2:block) (ofs2:Z) p, 
  Some p = source j m b2 ofs2 -> 
    exists b1, exists delta, exists ofs1, 
                  p = (b1,ofs1) /\
                  (b1 < Mem.nextblock m)%positive /\ j b1 = Some(b2,delta) /\ 
                  Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros.
  unfold source in H. destruct p as [b1 ofs1]; subst. apply eq_sym in H.
  destruct (plt 1 (Mem.nextblock m)).
    apply sourceN_SomeE in H. 
    destruct H as [delta [Bounds [J [P Off]]]]; subst. 
    exists b1; exists delta; exists ofs1. split; trivial. 
    split. specialize (Ppred_Plt (Mem.nextblock m)). xomega.
    repeat split; auto.
  inv H.
Qed.
  
Lemma source_NoneE: forall j m b2 ofs2, 
    None = source j m b2 ofs2 -> 
    forall b1 delta, (b1 < Mem.nextblock m)%positive -> j b1 = Some(b2,delta) ->
                     ~ Mem.perm m b1 (ofs2-delta) Max Nonempty. 
Proof. intros. apply eq_sym in H. unfold source in H.     
  destruct (plt 1 (Mem.nextblock m)).
    eapply (sourceN_NoneE _ _ _ _ _ H b1 delta); trivial. 
    destruct (Pos.succ_pred_or (Mem.nextblock m)); xomega.
  exfalso. xomega.
Qed.  

Lemma source_SomeI: forall j m b2 b1 ofs1 delta (OV:Mem.meminj_no_overlap j m),
   j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
   source j m b2 (ofs1+delta) = Some(b1,ofs1).
Proof. intros. unfold source.
  destruct (plt 1 (Mem.nextblock m)).
    unfold Coqlib.Plt in p.
    eapply sourceN_SomeI. apply OV. apply H. apply H0.
    apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0.
    remember (Mem.nextblock m) as b. clear H OV Heqb m ofs1 j b2 delta.
      destruct (Pos.succ_pred_or b); xomega.
  specialize (perm_nextblock_gt_1 _ _ _ _ _ H0). contradiction.
Qed.

Lemma sourceNone_LOOR: forall j m1 b2 ofs2 (N: None = source j m1 b2 ofs2) m2
              (Inj12: Mem.inject j m1 m2), loc_out_of_reach j m1 b2 ofs2.
Proof. intros. intros b1; intros.
   eapply source_NoneE; try eassumption.
     apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H Inj12).
Qed.

Lemma memvalUnchOnR: forall m1 m2 m3 m3' b ofs 
  (n : ~ Mem.perm m1 b ofs Max Nonempty)
  (UnchOn13 : Mem.unchanged_on (loc_out_of_bounds m1) m3 m3')
  (MV : memval_inject inject_id
                (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)))
                (ZMap.get ofs (PMap.get b (Mem.mem_contents m3))))
   (Rd: Mem.perm m3 b ofs Cur Readable),
   memval_inject inject_id (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)))
     (ZMap.get ofs (PMap.get b (Mem.mem_contents m3'))).
Proof. intros.
  destruct UnchOn13 as [_ U].
  rewrite (U _ _ n Rd).
  apply MV.
Qed.

Lemma perm_order_total: forall p1 p2, perm_order p1 p2 \/ perm_order p2 p1.
Proof. intros. 
  destruct p1; destruct p2; try (left; constructor) ; try (right; constructor).
Qed.

Lemma perm_order_antisym: forall p1 p2, perm_order p1 p2 -> perm_order p2 p1 -> p1=p2.
Proof. intros. inv H; inv H0; trivial.  Qed.

Lemma po'_E: forall p q, Mem.perm_order' p q -> exists pp, p=Some pp.
Proof. intros. destruct p; simpl in H. exists p; trivial. contradiction. Qed.

Lemma  perm_refl_1: forall p1 p1'  (HP:forall p, perm_order p1' p -> perm_order p1 p), perm_order p1 p1'.
Proof. intros. apply HP. apply perm_refl. Qed.

Lemma free_E: forall p, perm_order p Freeable -> p = Freeable.
Proof. intros. inv H; trivial. Qed.

Lemma  write_E: forall p, perm_order p Writable -> p=Freeable \/ p=Writable.
Proof. intros. inv H. right; trivial. left; trivial. Qed.

Lemma perm_split: forall m b ofs (A B: Prop) k p 
              (SPLIT: (Mem.perm m b ofs k p -> A) /\ (~Mem.perm m b ofs k p -> B)) 
              (P:Prop)
              (HA: Mem.perm m b ofs k p -> A -> P)
              (HB: ~Mem.perm m b ofs k p -> B -> P), P.
Proof. intros. destruct SPLIT.
   destruct (Mem.perm_dec m b ofs k p); auto.
Qed.

Lemma perm_splitA: forall m b ofs k' p m2' m2 m3' k b3 ofs3
              (SPLIT: (Mem.perm m b ofs k' p-> PMap.get b (Mem.mem_access m2') ofs k = PMap.get b (Mem.mem_access m2) ofs k) /\
                             (~Mem.perm m b ofs k' p -> PMap.get b (Mem.mem_access m2') ofs k = PMap.get b3 (Mem.mem_access m3') ofs3 k)) 
              (P:Prop)
              (HA: Mem.perm m b ofs k' p -> Mem.perm m2' b ofs k = Mem.perm m2 b ofs k -> P)
              (HB: ~Mem.perm m b ofs k' p -> Mem.perm m2' b ofs k = Mem.perm m3' b3 ofs3 k  -> P), P.
Proof. intros. destruct SPLIT.
   destruct (Mem.perm_dec m b ofs k' p).
          apply (HA p0). unfold Mem.perm. rewrite (H p0). reflexivity . 
          apply (HB n). unfold Mem.perm. rewrite (H0 n). reflexivity . 
Qed.

Lemma valid_splitA: forall (m m2' m2 m1':mem) (b:block) ofs k
              (SPLIT: if plt b (Mem.nextblock m) 
                             then PMap.get b (Mem.mem_access m2') ofs k = PMap.get b (Mem.mem_access m2) ofs k 
                             else PMap.get b (Mem.mem_access m2') ofs k = PMap.get b (Mem.mem_access m1') ofs k)
               P
              (HA: Mem.valid_block m b -> Mem.perm m2' b ofs k = Mem.perm m2 b ofs k -> P)
              (HB: ~Mem.valid_block m b -> Mem.perm m2' b ofs k = Mem.perm m1' b ofs k -> P), P.
Proof. intros.
   remember (plt b (Mem.nextblock m)) as d. unfold Mem.perm in *.
   destruct d; clear Heqd; rewrite SPLIT in *; auto.
Qed.

Lemma valid_splitC: forall (T:Type)(m:mem) (b:block) X (A B:T)
              (SPLIT: if plt b (Mem.nextblock m) 
                             then X = A
                             else X = B)
               P
              (HA: Mem.valid_block m b -> X=A -> P)
              (HB: ~Mem.valid_block m b -> X=B -> P), P.
Proof. intros.
   remember (plt b (Mem.nextblock m)) as d.
   destruct d; clear Heqd; rewrite SPLIT in *; auto.
Qed.

Lemma dec_split: forall {C} (dec: C \/ ~ C) (A B: Prop)
              (SPLIT: (C -> A) /\ (~C -> B)) 
              (P:Prop)
              (HA: C -> A -> P)
              (HB: ~C -> B -> P), P.
Proof. intros. destruct SPLIT.
   destruct dec; auto.
Qed.

Lemma valid_split: forall m b (A B: Prop)
              (SPLIT: (Mem.valid_block m b  -> A) /\ (~Mem.valid_block m b -> B)) 
              (P:Prop)
              (HA: Mem.valid_block m b -> A -> P)
              (HB: ~Mem.valid_block m b -> B -> P), P.
Proof. intros. eapply dec_split; try eassumption. unfold Mem.valid_block. xomega. Qed.

Lemma perm_subst: forall b1 b2 m1 m2 ofs1 ofs2 k
     (H: PMap.get b1 (Mem.mem_access m1) ofs1 k = PMap.get b2 (Mem.mem_access m2) ofs2 k),
     Mem.perm m1 b1 ofs1 k = Mem.perm m2 b2 ofs2 k.
Proof. intros. unfold Mem.perm. rewrite H. reflexivity. Qed.
