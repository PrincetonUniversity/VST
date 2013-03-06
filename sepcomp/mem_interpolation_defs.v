Load loadpath.

Require Import Events. (*needed for standard definitions of 
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.

Require Import sepcomp.mem_lemmas.

Axiom VALIDBLOCK: forall m b, Mem.valid_block m b -> 0 <= b < Mem.nextblock m.

Definition my_mem_unchanged_on (P : block -> Z -> Prop) (m_before m_after : mem) :=
(forall (b : block) (ofs : Z) (k : perm_kind) (HP: P b ofs), 
        Mem.valid_block m_before b -> Mem.perm m_before b ofs k = Mem.perm m_after b ofs k) /\
(forall (b : block) (ofs : Z) (HP: P b ofs) 
  (HMeperm: Mem.perm m_before b ofs Cur Readable)
  (v : memval),
  ZMap.get ofs (ZMap.get b m_before.(Mem.mem_contents)) = v ->
  ZMap.get ofs (ZMap.get b m_after.(Mem.mem_contents)) = v).

Axiom unchAx: forall P m m', my_mem_unchanged_on P m m' = mem_unchanged_on P m m'. 

Goal forall m b ofs p (H: ~ Mem.perm m b ofs p Nonempty),  ZMap.get b (Mem.mem_access m) ofs p = None.
intros. unfold Mem.perm in *.
remember (ZMap.get b (Mem.mem_access m) ofs p) as pp.
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
     destruct (eq_block b2 z). subst.
       remember (Mem.perm_dec m b1 (ofs2 - z0) Max Nonempty) as d.
       destruct d; inv H. right. right. exists z0. split; trivial. 
     right. left. exists z. exists z0. split; auto. 
  left; trivial. 
Qed.

Lemma isSource_SomeE: forall j m b2 ofs2 b1 ofs1, Some ofs1 = isSource j m b2 ofs2 b1 ->
    exists delta, j b1 = Some(b2,delta) /\ Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros. unfold isSource in H.
  remember (j b1) as zz.
  destruct zz. destruct p.
     destruct (eq_block b2 z). subst.
       remember (Mem.perm_dec m b1 (ofs2 - z0) Max Nonempty) as d.
       destruct d; inv H. exists z0. split; trivial. split; trivial. omega.
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

Fixpoint sourceN  (n:nat)  j m (b2:block) (ofs2:Z): option(block * Z) :=
  match isSource j m b2 ofs2 (Z_of_nat n) with 
         Some ofs1 => Some (Z_of_nat n, ofs1)
       | None => match n with O => None | S k => sourceN k j m b2 ofs2 end
  end.

Lemma sourceN_SomeE: forall n j m b2 ofs2 b1 ofs1, 
    sourceN n j m b2 ofs2 = Some(b1,ofs1) ->
    exists delta, 0 <= b1 <= (Z_of_nat n) /\ j b1 = Some(b2,delta) /\ 
                  Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros n.
  induction n; simpl; intros.
     remember (isSource j m b2 ofs2 0) as d.
     destruct d; inv H.  
           apply isSource_SomeE in Heqd. destruct Heqd as [delta [J [P Off]]]. 
           exists delta; repeat split; auto; omega. 
  remember (isSource j m b2 ofs2 (Zpos (P_of_succ_nat n)) ) as d.
  destruct d. inv H. clear IHn.
           apply isSource_SomeE in Heqd. destruct Heqd as [delta [J [P Off]]]. 
           exists delta; repeat split; auto. apply Zle_0_pos. omega.
   apply IHn in H. destruct H as [delta [Bounds [J [P Off]]]]. 
       exists delta; repeat split; auto. omega.
       eapply Zle_trans. apply Bounds. rewrite Zpos_P_of_succ_nat. omega. 
Qed.

Lemma sourceN_NoneE: forall n j m b2 ofs2, 
    sourceN n j m b2 ofs2 = None -> 
    forall b1 delta, 0 <= b1 <= (Z_of_nat n) -> j b1 = Some(b2,delta) ->
                     ~ Mem.perm m b1 (ofs2-delta) Max Nonempty.
Proof. intros n.
  induction n; simpl; intros. assert (b1=0). omega. subst. clear H0.
     remember (isSource j m b2 ofs2 0) as d.
     destruct d; inv H.  
           apply isSource_NoneE in Heqd. destruct Heqd. congruence. 
           destruct H. destruct H as [b [delta1 [J P]]]. 
                rewrite J in H1. inv H1. exfalso. apply P. trivial. 
           destruct H as [ddelta [J P]]. rewrite J in H1. inv H1. assumption. 
  remember (isSource j m b2 ofs2 (Zpos (P_of_succ_nat n)) ) as d.
  destruct d. inv H. specialize (IHn _ _ _ _ H).
           destruct H0. rewrite Zpos_P_of_succ_nat in H2. apply Z_le_lt_eq_dec in H2. 
           destruct H2. assert (0 <= b1 <= Z_of_nat n). omega. 
               apply (IHn _ _ H2 H1). 
           subst.  
           apply isSource_NoneE in Heqd.
           destruct Heqd.
           (*1/3*) rewrite Zpos_P_of_succ_nat in H2.  rewrite H1 in H2. inv H2. 
           destruct H2. 
            (*2/3*) destruct H2 as [b [d [J NEQ]]]. rewrite Zpos_P_of_succ_nat in J. 
                    rewrite H1 in J. inv J. exfalso. apply NEQ. trivial. 
           (*3.3*) destruct H2 as [d [J NP]]. rewrite Zpos_P_of_succ_nat in *. 
                    rewrite H1 in J. inv J. apply NP. 
Qed.

Lemma sourceN_SomeI: forall n j m b2 b1 ofs1 delta (OV:Mem.meminj_no_overlap j m),
   j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
   (0 <= b1 <= Z_of_nat n) ->
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
   sourceN (Zabs_nat ((Mem.nextblock m) - 1))  j m b2 ofs2.

Lemma source_SomeE: forall j m (b2:block) (ofs2:Z) p, 
  Some p = source j m b2 ofs2 -> 
    exists b1, exists delta, exists ofs1, 
                  p = (b1,ofs1) /\
                  0 <= b1 < Mem.nextblock m /\ j b1 = Some(b2,delta) /\ 
                  Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros. unfold source in H. destruct p as [b1 ofs1]; subst. apply eq_sym in H.      
  apply sourceN_SomeE in H. 
  destruct H as [delta [Bounds [J [P Off]]]]; subst. 
  exists b1; exists delta; exists ofs1. split; trivial. 
  split. rewrite inj_Zabs_nat in Bounds. 
         destruct Bounds; split; trivial. 
         assert (NB:= Mem.nextblock_pos m).
         destruct (Zabs_spec (Mem.nextblock m - 1)).
           destruct H1.  rewrite H2 in H0. omega.
         destruct H1. exfalso. omega.
  repeat split; auto.
Qed.
  
Lemma source_NoneE: forall j m b2 ofs2, 
    None = source j m b2 ofs2 -> 
    forall b1 delta, 0 <= b1 < Mem.nextblock m -> j b1 = Some(b2,delta) ->
                     ~ Mem.perm m b1 (ofs2-delta) Max Nonempty. 
Proof. intros. apply eq_sym in H. unfold source in H.      
  eapply (sourceN_NoneE _ _ _ _ _ H b1 delta); trivial. 
  clear H H1. rewrite inj_Zabs_nat.
  split. apply H0.
  destruct (Zabs_spec (Mem.nextblock m - 1)); destruct H; rewrite H1; omega. 
Qed.  

Lemma source_SomeI: forall j m b2 b1 ofs1 delta (OV:Mem.meminj_no_overlap j m),
   j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
   source j m b2 (ofs1+delta) = Some(b1,ofs1).
Proof. intros. unfold source.
  eapply sourceN_SomeI. apply OV. apply H. apply H0.
  destruct (VALIDBLOCK _ _ (Mem.perm_valid_block _ _ _ _ _ H0)). 
  clear H OV. rewrite inj_Zabs_nat.
  destruct (Zabs_spec (Mem.nextblock m - 1)); destruct H; rewrite H3; omega. 
Qed.

Lemma sourceNone_LOOR: forall j m1 b2 ofs2 (N: None = source j m1 b2 ofs2) m2
              (Inj12: Mem.inject j m1 m2), loc_out_of_reach j m1 b2 ofs2.
Proof. intros. intros b1; intros.
   eapply source_NoneE.
     apply N. 
     apply VALIDBLOCK. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H Inj12).
     apply H.
Qed.

Lemma mymemvalUnchOnR: forall m1 m2 m3 m3' b ofs 
  (n : ~ Mem.perm m1 b ofs Max Nonempty)
  (UnchOn13 : my_mem_unchanged_on (loc_out_of_bounds m1) m3 m3')
  (MV : memval_inject inject_id
                (ZMap.get ofs (ZMap.get b (Mem.mem_contents m2)))
                (ZMap.get ofs (ZMap.get b (Mem.mem_contents m3))))
   (Rd: Mem.perm m3 b ofs Cur Readable)
   (ValB: Mem.valid_block m1 b),
   memval_inject inject_id (ZMap.get ofs (ZMap.get b (Mem.mem_contents m2)))
     (ZMap.get ofs (ZMap.get b (Mem.mem_contents m3'))).
Proof. intros.
  destruct UnchOn13 as [_ U].
  specialize (U _ _ n Rd).
  inv MV. 
      apply eq_sym in H. rewrite (U _ H).  constructor. 
      apply eq_sym in H0. rewrite (U _ H0). econstructor. apply H1. trivial.
      constructor. 
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
              (SPLIT: (Mem.perm m b ofs k' p-> ZMap.get b (Mem.mem_access m2') ofs k = ZMap.get b (Mem.mem_access m2) ofs k) /\
                             (~Mem.perm m b ofs k' p -> ZMap.get b (Mem.mem_access m2') ofs k = ZMap.get b3 (Mem.mem_access m3') ofs3 k)) 
              (P:Prop)
              (HA: Mem.perm m b ofs k' p -> Mem.perm m2' b ofs k = Mem.perm m2 b ofs k -> P)
              (HB: ~Mem.perm m b ofs k' p -> Mem.perm m2' b ofs k = Mem.perm m3' b3 ofs3 k  -> P), P.
Proof. intros. destruct SPLIT.
   destruct (Mem.perm_dec m b ofs k' p).
          apply (HA p0). unfold Mem.perm. rewrite (H p0). reflexivity . 
          apply (HB n). unfold Mem.perm. rewrite (H0 n). reflexivity . 
Qed.

Lemma valid_splitA: forall (m m2' m2 m1':mem) (b:block) ofs k
              (SPLIT: if zlt b (Mem.nextblock m) 
                             then ZMap.get b (Mem.mem_access m2') ofs k = ZMap.get b (Mem.mem_access m2) ofs k 
                             else ZMap.get b (Mem.mem_access m2') ofs k = ZMap.get b (Mem.mem_access m1') ofs k)
               P
              (HA: Mem.valid_block m b -> Mem.perm m2' b ofs k = Mem.perm m2 b ofs k -> P)
              (HB: ~Mem.valid_block m b -> Mem.perm m2' b ofs k = Mem.perm m1' b ofs k -> P), P.
Proof. intros.
   remember (zlt b (Mem.nextblock m)) as d. unfold Mem.perm in *.
   destruct d; clear Heqd; rewrite SPLIT in *; auto.
Qed.

Lemma valid_splitC: forall (T:Type)(m:mem) (b:block) X (A B:T)
              (SPLIT: if zlt b (Mem.nextblock m) 
                             then X = A
                             else X = B)
               P
              (HA: Mem.valid_block m b -> X=A -> P)
              (HB: ~Mem.valid_block m b -> X=B -> P), P.
Proof. intros.
   remember (zlt b (Mem.nextblock m)) as d.
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
Proof. intros. eapply dec_split; try eassumption. unfold Mem.valid_block. omega. Qed.

Lemma perm_subst: forall b1 b2 m1 m2 ofs1 ofs2 k
     (H: ZMap.get b1 (Mem.mem_access m1) ofs1 k = ZMap.get b2 (Mem.mem_access m2) ofs2 k),
     Mem.perm m1 b1 ofs1 k = Mem.perm m2 b2 ofs2 k.
Proof. intros. unfold Mem.perm. rewrite H. reflexivity. Qed.


(*
Definition inject_aligned (j:meminj) := forall b b' ofs (H:j b = Some(b',ofs)), 
                   0 <= ofs /\ forall ch, Zdivide (size_chunk ch) ofs.

Lemma inject_aligned_ofs: forall j (J:inject_aligned j) b b' delta ofs (H:j b = Some(b',delta)) ch, Zdivide (align_chunk ch) ofs ->
                          Zdivide (align_chunk ch) (ofs + delta).
Proof. intros. apply Zdivide_plus_r. apply H0. destruct (J _ _ _ H). 
           eapply Zdivides_trans. apply align_size_chunk_divides. apply H2.
Qed.

Lemma compose_aligned_2: forall j k (Ij: inject_aligned j) (Ik: inject_aligned k), inject_aligned (compose_meminj j k).
Proof. intros. intros b; intros.
           destruct (compose_meminjD_Some _ _ _ _ _ H) as [B1 [O1 [Q1 [? [? ?]]]]]. subst.
           destruct (Ij _ _ _ H0). destruct (Ik _ _ _ H1). 
           split. omega. 
           intros. apply Zdivide_plus_r. apply H3. apply H5.
Qed.    
*)
Definition inject_aligned (j:meminj) := forall b b' ofs (H:j b = Some(b',ofs)) ch, Zdivide (size_chunk ch) ofs.

Axiom inj_implies_inject_aligned: forall j m1 m2 (Inj12: Mem.inject j m1 m2), inject_aligned j.

Lemma inject_aligned_ofs: forall j (J:inject_aligned j) b b' delta ofs (H:j b = Some(b',delta))
                                                ch (D:Zdivide (align_chunk ch) ofs), Zdivide (align_chunk ch) (ofs + delta).
Proof. intros. apply Zdivide_plus_r. apply D. 
           specialize (J _ _ _ H).  
             eapply Zdivides_trans. apply align_size_chunk_divides. apply J.
Qed.

Lemma compose_aligned_2: forall j k (Ij: inject_aligned j) (Ik: inject_aligned k), inject_aligned (compose_meminj j k).
Proof. intros. intros b; intros.
           destruct (compose_meminjD_Some _ _ _ _ _ H) as [B1 [O1 [Q1 [? [? ?]]]]]. subst.
           specialize (Ij _ _ _ H0). specialize (Ik _ _ _ H1).
           apply Zdivide_plus_r. apply Ij. apply Ik.
Qed.    
