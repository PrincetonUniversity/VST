Require Import sepcomp.Events. (*is needed for some definitions (loc_unmapped etc, and
  also at the very end of this file, in order to convert between the 
  tweaked and the standard definitions of mem_unchanged_on etc*)
Require Import sepcomp.Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.
Require Import Axioms.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolation_defs.

Fixpoint mkInjectionsN (N:nat)(n1 n2:block)(j k l: meminj) 
                     :  meminj * meminj * Z * Z:= 
   match N with O => (j,k,n1,n2)
    | S M => mkInjectionsN M (n1+1) (n2 + 1)
                             (fun b => if eq_block b n1 
                                       then Some (n2,0) 
                                       else j b)
                             (fun b => if eq_block b n2 then l n1 else k b)
                             l
   end.

Lemma mkInjectionsN_0: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')),
    n1 + Z_of_nat N = n1' /\ n2 + Z_of_nat N = n2'.
Proof. intros N.
  induction N; simpl; intros. 
     inv HI. repeat rewrite Zplus_0_r. split; trivial.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI). clear HI.
     rewrite Zpos_P_of_succ_nat. omega.
Qed.

Lemma mkInjectionsN_1: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')),
    forall b1 b2 ofs2 (Jb: j b1 = Some(b2,ofs2)), 
    b1 < n1 -> j' b1 = Some (b2,ofs2).
Proof. intros N.
  induction N; simpl; intros. 
     inv HI. apply Jb.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI). clear HI.
        apply (IHN b1 b2 ofs2). clear IHN.
        remember (eq_block b1 n1) as d.
        destruct d; clear Heqd. exfalso. subst. clear -H. omega.
        assumption.
     omega.
Qed.

Lemma mkInjectionsN_2: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')),
    forall b2 b3 ofs3 (Jb: k b2 = Some(b3,ofs3)), 
    b2 < n2 -> k' b2 = Some (b3,ofs3).
Proof. intros N.
  induction N; simpl; intros. 
     inv HI. apply Jb.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI). clear HI.
        apply (IHN b2 b3 ofs3). clear IHN.
        remember (eq_block b2 n2) as d.
        destruct d; clear Heqd. exfalso. subst. clear -H. omega.
        assumption.
      omega.
Qed.

Lemma mkInjectionsN_3: forall N n1 n2 j k l j' k' n1' n2'
        (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) b1 b2 ofs2,
        j' b1 = Some(b2,ofs2) -> 
     (j b1 = Some (b2,ofs2)) \/ 
     (exists m, 0 <= m /\ b1 = n1 + m /\ b2=n2 + m /\ ofs2=0).
Proof. intros N.
  induction N; simpl; intros. 
      inv HI. left. trivial.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI _ _ _ H).  clear HI H.
  destruct IHN.  
      remember (eq_block b1 n1) as d.
      destruct d; clear Heqd. inv H. right. exists Z0. 
      repeat rewrite Zplus_0_r. split. omega. auto.
      left; trivial.
 destruct H as [m [? [? [? ?]]]]. right. subst. 
   exists (1+m). unfold block in *. omega.
Qed.

Lemma mkInjectionsN_3V: forall N n1 n2 j k l j' k' n1' n2'
     (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) 
     (HJ: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> b1 < n1 /\ b2 < n2)
     (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> b2 < n2)
     b1 b2 ofs2,
     j' b1 = Some(b2,ofs2) -> 
          (j b1 = Some (b2,ofs2) /\ b1 < n1 /\ b2 < n2) \/ 
          (exists m, 0 <= m /\ b1 = n1 + m /\ b2=n2 + m /\ 
                     ofs2=0 /\ b1 < n1' /\ b2<n2').
Proof. intros N.
  induction N; simpl; intros. 
      inv HI. left. split; trivial. eapply HJ. apply H.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI).
  assert (HJ': forall (b1 b2 : block) (ofs2 : Z),
          (fun b : block => if eq_block b n1 then Some (n2, 0) else j b) b1 =
            Some (b2, ofs2) 
          -> b1 < n1 + 1 /\ b2 < n2 + 1). 
      clear IHN. intros.
      destruct (eq_block b0 n1); subst. inv H0. omega. 
      specialize (HJ _ _ _ H0). omega.
  assert (HK': forall (b2 b3 : block) (ofs3 : Z),
       (fun b : block => if eq_block b n2 then l n1 else k b) b2 =
           Some (b3, ofs3)
       -> b2 < n2 + 1).
     clear IHN. intros.
     destruct (eq_block b0 n2); subst. omega. 
     specialize (HK _ _ _ H0). omega.
  specialize (IHN HJ' HK' _ _ _ H).  
  apply mkInjectionsN_0 in HI.
  destruct IHN.  
     remember (eq_block b1 n1) as d.
     destruct d; clear Heqd. subst. destruct H0 as [? [? ?]]. inv H0. right.
           exists Z0. repeat rewrite Zplus_0_r. 
           repeat (split; (try omega ; try auto)).
     destruct H0 as [? [? ?]]. left. split. trivial.  apply HJ in H0. trivial.
  destruct H0 as [m [? [? [? ?]]]]. right. subst. 
    exists (1+m). unfold block in *. omega.
Qed.

Lemma mkInjectionsN_4: forall N n1 n2 j k l j' k' n1' n2' 
       (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) b2 b3 ofs3,
       k' b2 = Some(b3,ofs3) -> 
                k b2 = Some (b3,ofs3) \/
                (exists m, 0 <= m /\ b2 = n2 + m /\ l (n1+m) = Some(b3,ofs3)).
Proof. intros N. 
  induction N; simpl. intros. 
     inv HI. left; trivial.
  intros.
  specialize (IHN (n1+1) (n2+1) _ _ _ _ _ _ _ HI _ _ _ H).  clear HI H.
  destruct IHN.  
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd. 
          subst. right. exists Z0. repeat rewrite Zplus_0_r. 
          split. omega. auto.
     left; trivial.
  destruct H as [m [? [? ?]]]. subst. 
    right. exists (1+m). unfold block in *. 
      split. omega.
      split. omega. 
      assert (n1 + (1 + m) = n1 + 1 + m). omega. 
      rewrite H0. trivial.
Qed.

Lemma mkInjectionsN_4Val: forall N n1 n2 j k l j' k' n1' n2' 
       (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) 
       (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> b2 < n2) b2 b3 ofs3,
       k' b2 = Some(b3,ofs3) -> 
            (k b2 = Some (b3,ofs3) /\ b2 < n2) \/
            (exists m, 0 <= m /\ b2 = n2 + m /\ 
                       l (n1+m) = Some(b3,ofs3) /\ b2 < n2').
Proof. intros N. 
  induction N; simpl. intros. 
     inv HI. left. split. trivial. apply HK in H. trivial.
  intros.
  assert (HK': (forall (b2 b3 : block) (ofs3 : Z),
           (fun b : block => if eq_block b n2 then l n1 else k b) b2 =
           Some (b3, ofs3) -> b2 < n2 + 1)). 
      clear IHN HI. intros.
      destruct (eq_block b0 n2); subst. omega. apply HK in H0. omega.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI HK' _ _ _ H).  
  apply mkInjectionsN_0 in HI.
  destruct IHN.  
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd. destruct H0. subst.
          right. exists Z0. repeat rewrite Zplus_0_r. 
          repeat (split ; (try omega ; try auto)).
     destruct H0. left. split. trivial. omega.
  destruct H0 as [m [? [? ?]]]. subst.  right.
  exists (1+m). unfold block in *. 
    split. omega.
    split. omega. 
    assert (n1 + (1 + m) = n1 + 1 + m). omega. 
    rewrite H1. trivial.
Qed.

Lemma mkInjectionsN_5: forall N n1 n2 j k l j' k' n1' n2'
       (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) 
       (HJ1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> b1 < n1)
       (HJ2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) ->b2 < n2)
       (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> b2 < n2)
       (HL: forall b1 b3 ofs3, l b1 = Some(b3,ofs3) -> b1 < n1')
       b2 (HB: b2 < n2'),
       k' b2 = None -> 
             (b2 < n2 /\ k b2 = None) \/
             (exists m, 0<=m /\ b2 = n2+m /\  l (n1+m) = None).
Proof. intros N. 
  induction N; simpl. intros. 
     inv HI. left. split; trivial.
  intros.
  assert (HJ1': forall (b1 b2 : block) (ofs2 : Z),
          (fun b : block => if eq_block b n1 then Some (n2, 0) else j b) b1 =
          Some (b2, ofs2) -> b1 < n1 + 1).
     clear IHN. intros.
     destruct (eq_block b1 n1); subst. inv H0. omega. 
     specialize (HJ1 _ _ _ H0). omega.
  assert (HJ2': forall (b1 b2 : block) (ofs2 : Z),
          (fun b : block => if eq_block b n1 then Some (n2, 0) else j b) b1 =
           Some (b2, ofs2) -> b2 < n2 + 1). 
     clear IHN. intros.
     destruct (eq_block b1 n1); subst. inv H0. omega. 
     specialize (HJ2 _ _ _ H0). omega.
  assert (HK': forall (b2 b3 : block) (ofs3 : Z),
          (fun b : block => if eq_block b n2 then l n1 else k b) b2 =
          Some (b3, ofs3) -> b2 < n2 + 1).
     clear IHN. intros.
     destruct (eq_block b0 n2); subst. omega. 
     specialize (HK _ _ _ H0). omega.
  destruct (IHN _ _ _ _ _ _ _ _ _ HI HJ1' HJ2' HK' HL _ HB H).
     destruct H0.
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd.
          subst. right. exists Z0. repeat rewrite Zplus_0_r.
              repeat (split; trivial). omega.
     left. split; trivial. omega.
  destruct H0 as [m [ HM [HBB HLL]]]. subst.
    right. exists (1 + m). 
    split. omega. 
    assert (n1 + (1 + m) = n1 + 1 + m). omega. 
    rewrite H0. split. omega. trivial.
Qed.

Lemma mkInjectionsN_6: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) b (J': j' b = None), 
     j b = None.
Proof. intros N.
  induction N; simpl; intros. 
     inv HI. trivial.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI _ J'). clear HI. simpl in IHN.
     destruct (eq_block b n1); subst. inv IHN. trivial.
Qed.

Lemma mkInjectionsN_7: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
    b (HB: b < n1'),
    (n1 <= b -> j' b  <> None) /\ (b < n1 -> j' b = j b).
Proof. intros N.
  induction N; intros; simpl.
      intros. inv HI. split; intros.  exfalso. omega. trivial.
  intros.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI _ HB). clear HI.
     destruct IHN.
     split; intros. 
       apply Z_le_lt_eq_dec in H1. 
       destruct H1. apply H. omega.
       subst. remember (eq_block b b) as d. destruct d; clear Heqd. 
              assert (b < b + 1). omega.
              rewrite (H0 H1). intros Q. discriminate.
         exfalso. apply n. trivial.
   remember (eq_block b n1) as d.
     destruct d; clear Heqd. subst. exfalso. omega.
     apply H0. omega.
Qed.

Lemma mkInjectionsN_8: forall j' k' l n1' n2'  M N j  k n1 n2
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
    (Hj: forall b, j b = None -> b < M \/ n1' <= b) b,
    j' b = None -> b < M \/ n1' <= b. 
Proof. intros j' k' l n1' n2' M N.
  induction N; simpl; intros. 
     inv HI. apply (Hj _ H).
  specialize (IHN _ _ _ _ HI). clear HI.
  apply IHN. intros.
     remember (eq_block b0 n1) as d.
    destruct d; clear Heqd; subst. inv H0.
     apply Hj. apply H0.
  apply H.
Qed.

Lemma mkInjectionsN_9: forall M j' k' l n1' n2'  N j  k n1 n2
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
    (Hj: forall b, j b = None -> b < n1' -> b < M) b,
    j' b = None -> b < n1' -> b < M.
Proof. intros M j' k' l n1' n2' N.
  induction N; simpl; intros. 
     inv HI. apply (Hj _ H H0).
  specialize (IHN _ _ _ _ HI). clear HI.
  apply IHN. intros.
     remember (eq_block b0 n1) as d.
     destruct d; clear Heqd; subst. inv H1.
       apply Hj. apply H1.
    apply H2.
 apply H.
apply H0.
Qed.

Lemma mkInjectionsN_10: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
    (HL: forall b1 b3 ofs3, l b1 = Some(b3,ofs3) -> b1 < n1' - Z_of_nat N)
    b b2 ofs2,
    l b = Some(b2,ofs2) -> j' b = Some(b2,ofs2) \/ b < n1  + Z_of_nat N.
Proof. intros N.
  induction N; simpl; intros. 
     inv HI. specialize (HL _ _ _ H). 
     repeat rewrite Zminus_0_r in HL. rewrite Zplus_0_r. right; trivial.
  assert (HN: forall (b1 b3 : block) (ofs3 : Z),
       l b1 = Some (b3, ofs3) -> b1 < n1' - Z_of_nat N). 
     intros. specialize (HL _ _ _ H0). rewrite Zpos_P_of_succ_nat in HL. omega. 
 specialize (IHN _ _ _ _ _ _ _ _ _ HI HN _ _ _ H). clear HI.
 destruct IHN.
    left; trivial. 
    rewrite Zpos_P_of_succ_nat. right. omega.
Qed.

Definition mkInjections (m1 m1' m2:mem) (j k l: meminj)
                     :  meminj * meminj * Z * Z:= 
  mkInjectionsN (nat_of_Z ((Mem.nextblock m1') - (Mem.nextblock m1)))
                (Mem.nextblock m1)
                (Mem.nextblock m2) j k l.

Lemma mkInjections_1_injinc: forall m1 m1' m2 j k l j' k' n1' n2' 
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
    (VB: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1),
    inject_incr j j'.
Proof. unfold inject_incr, mkInjections; intros.
   apply (mkInjectionsN_1 _ _ _ _ _ _ _ _ _ _ HI). apply H. eapply VB. apply H.
Qed.

Lemma mkInjections_1_injsep: forall m1 m1' m2 j k l j' k' n1' n2' 
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')),
    inject_separated j j' m1 m2.
Proof. unfold inject_separated, mkInjections; intros.
       specialize (mkInjectionsN_3 _ _ _ _ _ _ _ _ _ _ HI _ _ _ H0). intros.
       destruct H1. rewrite H1 in H. discriminate.
       destruct H1 as [m [? [? [? ?]]]]. subst.
       clear HI H H0. unfold Mem.valid_block. omega.
Qed.

Lemma mkInjections_2_injinc: forall m1 m1' m2 j k l j' k' n1' n2' 
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) 
        (VB: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1),
      inject_incr k k'.
Proof. 
  unfold inject_incr, mkInjections; intros.
  apply (mkInjectionsN_2 _ _ _ _ _ _ _ _ _ _ HI). apply H. eapply VB. apply H.
Qed.

Lemma mkInjections_2_injsep: forall m1 m1' m2 j k l j' k' n1' n2' 
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (VB: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
         m3 (Sep:inject_separated (compose_meminj j k) l m1 m3),
       inject_separated k k' m2 m3.
Proof. 
  unfold inject_separated, mkInjections; intros.
  specialize (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ H0). intros.
  destruct H1. rewrite H1 in H. discriminate.
  destruct H1 as [m [? [? ?]]]. subst. 
  split. unfold Mem.valid_block. omega.
  eapply (Sep (Mem.nextblock m1 + m)).
     assert (HJ: j (Mem.nextblock m1 + m) = None).
           remember (j (Mem.nextblock m1 + m)) as d. destruct d; trivial.
           apply eq_sym in Heqd. destruct p. specialize (VB _ _ _ Heqd).
           exfalso. clear - H1 VB. unfold Mem.valid_block in VB. omega.
     unfold compose_meminj. rewrite HJ. trivial.
  apply H3.
Qed.

Lemma mkInjections_6: forall m1 m1' m2 j k l j' k' n1' n2' 
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) b (J': j' b = None),
     j b = None.
Proof. intros. apply (mkInjectionsN_6 _ _ _ _ _ _ _ _ _ _ HI _ J'). Qed.

Lemma mkInjections_5: forall m1 m1' m2 j k l j' k' n1' n2' 
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (VBj1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
        (VBj2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m2 b2)
        (VBk2: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1)
        (VBl1: forall b1 b2 ofs2, l b1 = Some(b2,ofs2) -> b1 < n1')
        b2 (HB: b2 < n2'),
        k' b2 = None -> 
        (Mem.valid_block m2 b2 /\ k b2 = None) \/
        (exists m, 0<=m /\ b2 = Mem.nextblock m2 + m /\ 
                   l (Mem.nextblock m1+m) = None).
Proof. intros. unfold mkInjections in HI.
  apply  (mkInjectionsN_5 _ _ _ _ _ _ _ _ _ _ HI VBj1 VBj2 VBk2 VBl1 _ HB H).
Qed.

Lemma J12'_no_overlap: forall m1 m2 j12 
        (MInj12 : Mem.inject j12 m1 m2) m1' (Fwd1: mem_forward m1 m1') j23 m3
        (MInj23 : Mem.inject j23 m2 m3) j' j12' j23' n1' n2'
        (HeqMKI: mkInjections m1 m1' m2 j12 j23 j' = (j12', j23',n1',n2')),
      Mem.meminj_no_overlap j12' m1'.
Proof. intros. intros b b'; intros.
  assert (Val1: (forall (b1 b2 : block) (ofs2 : Z),
        j12 b1 = Some (b2, ofs2) ->
        b1 < Mem.nextblock m1 /\ b2 < Mem.nextblock m2)).
    intros; split.
       eapply Mem.valid_block_inject_1. apply H4. eassumption.
       eapply Mem.valid_block_inject_2. apply H4. eassumption.
  assert (Val2: (forall (b2 b3 : block) (ofs3 : Z),
        j23 b2 = Some (b3, ofs3) -> b2 < Mem.nextblock m2)).
    intros.
       eapply Mem.valid_block_inject_1. apply H4. eassumption.
  assert (ZZ:= mkInjectionsN_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI Val1 Val2 _ _ _ H0).
  assert (ZZ':= mkInjectionsN_3V  _ _ _ _ _ _ _ _ _ _ 
                HeqMKI Val1 Val2 _ _ _ H1).
  destruct ZZ; destruct ZZ'.
  (*j - j*) destruct H4 as [J [valJ1 valJ2]].
            destruct H5 as [J' [valJ1' valJ2']].
            eapply MInj12. apply H. assumption. assumption.
                eapply Fwd1. apply valJ1. assumption.
                eapply Fwd1. apply valJ1'. assumption.
  (*j - fresh*) destruct H4 as [J [valJ1 valJ2]].
                destruct H5 as [M [ZM [valJ1' [valJ2' [DD [leq1 leq2]]]]]].
                subst.
                left. intros ZZ; subst. omega.
  (*fresh - j*) destruct H4 as [M [ZM [valJ1 [valJ2 [DD [leq1 leq2]]]]]].
                subst.
                destruct H5 as [J [valJ1' valJ2']].
                left. intros ZZ; subst. omega.
  (*fresh - fresh*)
          destruct H4 as [M [ZM [valJ1 [valJ2 [DD [leq1 leq2]]]]]].
          subst.
          destruct H5 as [M' [ZM' [valJ1' [valJ2' [DD' [leq1' leq2']]]]]].
          subst.
          left. intros ZZ.
          assert( M = M'). eapply Zplus_reg_l. apply ZZ.
          subst. apply H. trivial.
Qed.

Lemma mkInjections_composememinj: forall m1 m1' m2 j k l j' k' n1' n2' 
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (InjIncr: inject_incr (compose_meminj j k) l) m3
        (InjSep: inject_separated (compose_meminj j k) l m1 m3)
        (VBj1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
        (VBj2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m2 b2)
        (VBk2: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1)
        (VBL1': forall b1 b3 ofs3, l b1 = Some (b3, ofs3) -> b1 < n1'),
      l = compose_meminj j' k'.
Proof. intros.
  extensionality b. 
  remember (compose_meminj j' k' b) as z. 
  destruct z; apply eq_sym in Heqz.
     destruct p. apply  compose_meminjD_Some in Heqz. 
     destruct Heqz as [b1 [ofs1 [ofs [J' [K' ZZ]]]]]. subst. 
     unfold mkInjections in HI.
     destruct (mkInjectionsN_3 _ _ _ _ _ _ _ _ _ _ HI _ _ _ J').
         destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ K').
            apply InjIncr. unfold compose_meminj. rewrite H. 
                           rewrite H0. reflexivity.
         destruct H0 as [m [NonNeg [B2 _]]]. subst. 
              exfalso. specialize (VBj2 _ _ _ H).
              clear - NonNeg VBj2. unfold Mem.valid_block in VBj2. omega.
     destruct H as [m [NonNeg [B1 [B2 XX]]]]. subst.
         destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ K'). 
         exfalso. specialize (VBk2 _ _ _ H).
         clear - NonNeg VBk2. unfold Mem.valid_block in VBk2. omega.
     destruct H as [m' [NonNeg' [B2 ZZ]]].
            assert (m=m'). clear - B2 NonNeg' NonNeg. 
               apply Zplus_minus_eq in B2. subst. omega. 
            subst. apply ZZ.
  remember (l b) as lb. 
  destruct lb; trivial. 
  apply eq_sym in Heqlb. destruct p as [b2 ofs2]. 
  unfold compose_meminj in Heqz.
  remember (j' b) as j'b.
  destruct j'b; apply eq_sym in Heqj'b.
  (*J' b = Some*)
      destruct p.
      assert (K'None: k' b0 = None).
          remember (k' b0) as kb.
          destruct kb; apply eq_sym in Heqkb; inv Heqz; trivial. 
             destruct p. inv H0.
          rewrite K'None in Heqz. clear Heqz.
      assert (KNone:k b0 = None).
          remember (k b0) as d. destruct d; trivial. 
             apply eq_sym in Heqd. destruct p.
             apply (mkInjections_2_injinc _ _ _ _ _ _ _ _ _ _ HI VBk2) in Heqd. 
             rewrite Heqd in K'None. discriminate.
      assert (VBj : forall b1 b3 ofs3, j b1 = Some (b3, ofs3) -> 
                     b1 < Mem.nextblock m1 /\ b3 < Mem.nextblock m2).
             intros. split. eapply VBj1. apply H.  eapply VBj2. apply H.
      destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _ HI VBj VBk2 _ _ _ Heqj'b).
      (*j b = Some*) destruct H as [? [? ?]].
           assert (JKNone: compose_meminj j k b = None).
               unfold compose_meminj. rewrite H. rewrite KNone. reflexivity.
           destruct (InjSep _ _ _ JKNone Heqlb). exfalso. apply (H2 H0).
      (*other case*) 
           destruct H as [m [Nonneg [B1 [B2 [? [? ?]]]]]]; subst.
           destruct (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HI VBj1 
                       VBj2 VBk2 VBL1' _ H1 K'None).
           (*case 1 valid in m2 - contradiction*)
               destruct H as [XX _]. clear -XX Nonneg. 
               unfold Mem.valid_block in XX. exfalso. omega.
           (*case 2 - l undefined - contradiction*)
                         destruct H as [mm [MMnoneg [MM LL]]].
                         assert (mm= m). clear - MM. omega. subst.
                         rewrite LL in Heqlb. discriminate.
     (*J' b = None*)
           assert (Jb:= mkInjections_6  _ _ _ _ _ _ _ _ _ _ HI _ Heqj'b).
           assert (CMN: compose_meminj j k b = None).
                   unfold compose_meminj. rewrite Jb. trivial.
           destruct (InjSep _ _ _ CMN Heqlb) as [NV1 _].
           apply VBL1' in Heqlb. 
           destruct (mkInjectionsN_7 _ _ _ _ _ _ _ _ _ _ HI _ Heqlb) as [X _].
           rewrite Heqj'b in X. exfalso.
           apply X. 
              clear - NV1. unfold Mem.valid_block in NV1. omega.
              trivial.
Qed. 

Definition removeUndefs (j l j':meminj):meminj := 
   fun b => match j b with 
              None => match l b with 
                         None => None | Some (b1,delta1) => j' b 
                      end
            | Some(b2,delta2) => Some(b2, delta2)
            end.

Lemma RU_composememinj: forall m1 m1' m2 j k l j' k' n1' n2' 
       (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
       (InjIncr: inject_incr (compose_meminj j k) l) m3
       (InjSep: inject_separated (compose_meminj j k) l m1 m3)
       (VBj1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
       (VBj2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m2 b2)
       (VBk2: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1)
       (VBL1': forall b1 b3 ofs3, l b1 = Some (b3, ofs3) -> b1 < n1'),
      l = compose_meminj (removeUndefs j l j') k'.
Proof. intros.
  assert (INC:= mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HI VBj1). 
  subst.
  rewrite (mkInjections_composememinj _ _ _ _ _ _ _ _ _ _ HI InjIncr _ 
                 InjSep VBj1 VBj2 VBk2 VBL1').
  extensionality b. unfold removeUndefs. 
  remember (compose_meminj j' k' b) as V.
  destruct V; apply eq_sym in HeqV.
    destruct p. unfold compose_meminj in *.
      remember (j' b) as v1.
      destruct v1; apply eq_sym in Heqv1; inv HeqV.
        destruct p.
        remember (k' b1) as v2.
        destruct v2; apply eq_sym in Heqv2; inv H0.
          destruct p. inv H1.
          remember (j b) as v3. 
          destruct v3; apply eq_sym in Heqv3.
             destruct p. 
             rewrite (INC _ _ _ Heqv3) in Heqv1. inv Heqv1. 
             rewrite Heqv2.  trivial.
         rewrite Heqv2. trivial.
   unfold compose_meminj in *.
      remember (j b) as v1.
      destruct v1; apply eq_sym in Heqv1.
          destruct p. apply INC in Heqv1. 
                      rewrite Heqv1 in *. rewrite HeqV. trivial.
      rewrite HeqV. trivial.
Qed. 

Lemma RU_D: forall j j' (I: inject_incr j j') l, 
            inject_incr (removeUndefs j l j') j'.
Proof. intros. intros b; intros.
  unfold removeUndefs in H.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd.
      destruct p. inv H. apply (I _ _ _  Heqd).
  remember (l b) as d.
  destruct d; apply eq_sym in Heqd; try inv H.
      destruct p. trivial. 
Qed.

Lemma inc_RU: forall j j' (I: inject_incr j j') l, 
              inject_incr j (removeUndefs j l j').
Proof. intros. intros b; intros.
  unfold removeUndefs. rewrite H. trivial.
Qed.

Lemma meminij_no_overlap_inject_incr: 
   forall j m (NOV: Mem.meminj_no_overlap j m) k (K:inject_incr k j),
  Mem.meminj_no_overlap k m.
Proof. intros.
  intros b; intros.
  apply K in H0. apply K in H1.
  eapply (NOV _ _ _ _ _ _ _ _  H H0 H1 H2 H3).
Qed.

Lemma RU_no_overlap: 
     forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
            (Fwd1: mem_forward m1 m1') j23 m3
            (MInj23 : Mem.inject j23 m2 m3) j' j12' j23' n1' n2'
            (HeqMKI: mkInjections m1 m1' m2 j12 j23 j' = (j12',j23',n1',n2')),
            Mem.meminj_no_overlap (removeUndefs j12 j' j12') m1'.
Proof. 
intros.
specialize (J12'_no_overlap _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ _ _ _ _ HeqMKI). 
intros.
  eapply (meminij_no_overlap_inject_incr _ _ H).
  apply RU_D.
  eapply (mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI).
  intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H0 MInj12).
Qed.

Definition inject_memval (j:meminj) (v:memval): memval := 
     match v with 
         Pointer b ofs n =>
             match j b with 
                None => Undef
              | Some(b',delta) => Pointer b' (Int.add ofs (Int.repr delta)) n 
             end
       | _ => v
     end.

Lemma inject_memval_memval_inject: forall j v v' 
  (IM: inject_memval j v = v') (U: v' <> Undef), memval_inject j v v'.
Proof.
  intros.
  destruct v; destruct v'; simpl in *; try inv IM; try constructor. 
     exfalso. apply U. trivial.
     rewrite H0.
        remember (j b) as d. destruct d. destruct p. inv H0. inv H0.
     rewrite H0. 
        remember (j b) as d.
        destruct d. 
          destruct p. inv H0.
            eapply memval_inject_ptr. rewrite <- Heqd. reflexivity. 
          trivial. 
        inv H0.
Qed.

Lemma inject_memval_memval_inject1: forall j v 
               (H: forall b ofs n, v = Pointer b ofs n -> 
                                   exists p, j b = Some p),
               memval_inject j v (inject_memval j v). 
Proof.
  intros.
  destruct v; simpl in *; try constructor.
  specialize (H _ _ _ (eq_refl _)). 
  destruct H. rewrite H. destruct x. econstructor. apply H. trivial.
Qed.

Lemma noperm_dec : forall m k p (b : block) (ofs : Z),
  {~ Mem.perm m b ofs k p} + {~ ~ Mem.perm m b ofs k p}.
Proof. intros.
  case_eq(Mem.perm_dec m b ofs k p).
  intros. right. intros N. apply (N p0). 
  intros. left; assumption. 
Qed.

Definition AccessMap_II_Property  (j12 j23 j12' :meminj) (m1 m1' m2 : mem)
           (NB:Z) (AM:ZMap.t (Z -> perm_kind -> option permission)) :Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> forall k ofs2,
      match k with Res => ZMap.get b2 AM ofs2 k  = 
                          ZMap.get b2 m2.(Mem.mem_access) ofs2 k
      | _ =>
       match j23 b2 with 
         None => ZMap.get b2 AM ofs2 k = ZMap.get b2 m2.(Mem.mem_access) ofs2 k
       | Some (b3,d3) => 
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) =>  ZMap.get b2 AM ofs2 k = 
                               ZMap.get b1 m1'.(Mem.mem_access) ofs1 k
           | None =>  ZMap.get b2 AM ofs2 k = 
                      ZMap.get b2 m2.(Mem.mem_access) ofs2 k
           end
        end
       end)
     /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
         match k with
           Res => match sourceP (fun b ofs => ~Mem.perm m1' b ofs Res Nonempty) 
                                (noperm_dec m1' Res Nonempty) j12' m1' b2 ofs2
                  with Some(b1, ofs1) => ZMap.get b2 AM ofs2 Res = None
                     | None => if zlt b2 NB 
                               then ZMap.get b2 AM ofs2 Res = Some Nonempty (*if b2 is not mapped by j23' any value greater than Nonempty should also work.
                                  if b2 is mapped by j23' then taking the Res-perm of j23'(b2,ofs2) should also work*)
                               else ZMap.get b2 AM ofs2 Res = None
                  end
         | _ => 
           match source j12' m1' b2 ofs2 with 
              Some(b1,ofs1) => ZMap.get b2 AM ofs2 k =
                               ZMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None =>  ZMap.get b2 AM ofs2 k = None
           end
          end).

Definition Content_II_Property (j12 j12' j23':meminj) (m1 m1' m2:Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2, 
      (Mem.valid_block m2 b2 -> forall ofs2,
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) =>
                 match j23' b2 with
                    None => ZMap.get ofs2 (ZMap.get b2 CM) =
                            ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents))
                 | Some(b3,ofs3) => 
                      ZMap.get ofs2 (ZMap.get b2 CM) = 
                        inject_memval j12' 
                            (ZMap.get ofs1 (ZMap.get b1 m1'.(Mem.mem_contents)))
                 end
           | None => ZMap.get ofs2 (ZMap.get b2 CM) =
                     ZMap.get ofs2 (ZMap.get b2 m2.(Mem.mem_contents))
         end)
  /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
         match source j12' m1' b2 ofs2 with
                None => ZMap.get ofs2 (ZMap.get b2 CM) =Undef
              | Some(b1,ofs1) =>
                   ZMap.get ofs2 (ZMap.get b2 CM) =
                     inject_memval j12' 
                       (ZMap.get ofs1 (ZMap.get b1 m1'.(Mem.mem_contents)))
         end).

(*
Lemma mkInjections_aligned_1: forall m1 m1' m2 j k l j' k' n1' n2' 
                   (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) 
                   (A: inject_aligned j), inject_aligned j'.
Proof. intros. intros b; intros.
  destruct (mkInjectionsN_3  _ _ _ _ _ _ _ _ _ _ HI _ _ _ H).
        apply (A _ _ _ H0).
  destruct H0 as [? [? [? [? ?]]]]. subst. 
  split. omega. intros. apply Zdivide_0.
Qed.

Lemma mkInjections_aligned_2: forall m1 m1' m2 j k l j' k' n1' n2' 
                 (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) 
                 (Ik: inject_aligned k) (Il: inject_aligned l), 
                 inject_aligned k'.
Proof. intros. intros b; intros.
  destruct (mkInjectionsN_4  _ _ _ _ _ _ _ _ _ _ HI _ _ _ H).
        apply (Ik _ _ _ H0).
  destruct H0 as [? [? [? ?]]]. subst. 
        apply (Il _ _ _ H2).
Qed.*)

Lemma mkInjections_aligned_1: forall m1 m1' m2 j k l j' k' n1' n2' 
                       (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) 
                       (A: inject_aligned j), inject_aligned j'.
Proof. intros. intros b; intros.
  destruct (mkInjectionsN_3  _ _ _ _ _ _ _ _ _ _ HI _ _ _ H).
     apply (A _ _  _ H0).
  destruct H0 as [? [? [? [? ?]]]]. subst.  apply Zdivide_0.
Qed.

Lemma mkInjections_aligned_2: forall m1 m1' m2 j k l j' k' n1' n2' 
                       (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) 
                       (Ik: inject_aligned k) (Il: inject_aligned l),
                       inject_aligned k'.
Proof. intros. intros b; intros.
  destruct (mkInjectionsN_4  _ _ _ _ _ _ _ _ _ _ HI _ _ _ H).
        apply (Ik _ _ _ H0).
  destruct H0 as [? [? [? ?]]]. subst. 
        apply (Il _ _ _ H2).
Qed.

Lemma Cur_isMaxCur: isMaxCur Cur = true.
Proof. reflexivity. Qed.

Lemma Max_isMaxCur: isMaxCur Max = true.
Proof. reflexivity. Qed.

Lemma II_ok: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                   (Fwd1: mem_forward m1 m1') j23 m3
                   (MInj23 : Mem.inject j23 m2 m3) m3'
                   (Fwd3: mem_forward m3 m3')
                   j' (MInj13': Mem.inject j' m1' m3')
                   (InjIncr: inject_incr (compose_meminj j12 j23) j')
                   (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                   (Unch11': my_mem_unchanged_on 
                             (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                   (Unch33': my_mem_unchanged_on
                         (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
                   (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2)
                   (WD3: mem_wd m3) (WD3' : mem_wd m3')
                   prej12' j23' n1' n2'
                   (HeqMKI: mkInjections m1 m1' m2 j12 j23 j' = 
                            (prej12', j23', n1', n2'))
                   j12' (Hj12': j12'= removeUndefs j12 j' prej12')
                   m2'
                   (NB: m2'.(Mem.nextblock)=n2')
                   (CONT:  Content_II_Property j12 j12' j23' m1 m1' m2 
                                               (m2'.(Mem.mem_contents)))
                   (ACCESS: AccessMap_II_Property j12 j23 j12' m1 m1' m2 
                                                  n2' (m2'.(Mem.mem_access)))
                   (AL12: inject_aligned j12) (AL23: inject_aligned j23)
                   (AL13': inject_aligned j'), 
                j'=compose_meminj j12' j23' /\
                     inject_aligned j12'  /\ inject_aligned j23' /\
                     inject_incr j12 j12' /\ inject_incr j23 j23' /\
                     Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ 
                     Mem.inject j23' m2' m3' /\
                     my_mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                     inject_separated j12 j12' m1 m2 /\
                     inject_separated j23 j23' m2 m3 /\
                     my_mem_unchanged_on (loc_unmapped j23) m2 m2' /\ 
                     my_mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                     (mem_wd m2 -> mem_wd m2').
Proof. intros.  
  assert (VBj12_1: forall (b1 b2 : block) (ofs2 : Z),
                   j12 b1 = Some (b2, ofs2) -> Mem.valid_block m1 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12).
  assert (VBj12_2: forall (b1 b2 : block) (ofs2 : Z),
                   j12 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  assert (VBj23_1: forall (b1 b2 : block) (ofs2 : Z),
                   j23 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23).
  assert (VBj23_2: forall (b1 b2 : block) (ofs2 : Z),
                   j23 b1 = Some (b2, ofs2) -> Mem.valid_block m3 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
  assert (VB12: forall (b3 b4 : block) (ofs3 : Z), 
                 j12 b3 = Some (b4, ofs3) -> 
                b3 < Mem.nextblock m1 /\ b4 < Mem.nextblock m2).
      intros. split. apply (VBj12_1 _ _ _ H). apply (VBj12_2 _ _ _ H).
  assert (preinc12:= mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1).
  assert (inc12:= inc_RU _ _ preinc12 j').
  assert (presep12:= mkInjections_1_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI).
  assert (sep12: inject_separated j12 (removeUndefs j12 j' prej12') m1 m2).
       intros b; intros. eapply presep12. apply H. 
       eapply RU_D. apply preinc12. apply H0.
  assert (inc23:= mkInjections_2_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1).
  assert (sep23:= mkInjections_2_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI 
                  VBj12_1 _ InjSep).
  assert (NB1: Mem.nextblock m1' - Mem.nextblock m1 >= 0).
       assert (B: forall b, b <= Mem.nextblock m1 -> b <= Mem.nextblock m1'). 
           intros. destruct (Fwd1 (b -1)).  unfold Mem.valid_block. omega. 
                 unfold Mem.valid_block in H0. omega. 
       clear -B. specialize (B (Mem.nextblock m1)). omega. 
  destruct (mkInjectionsN_0  _ _ _ _ _ _ _ _ _ _ HeqMKI) as [N1 N2].
       rewrite (nat_of_Z_eq _ NB1) in N1. 
       rewrite (nat_of_Z_eq _ NB1) in N2. 
       rewrite Zplus_minus in N1. subst.
  assert (VBj': forall b1 b3 ofs3, j' b1 = Some (b3, ofs3) -> 
                b1 < Mem.nextblock m1').
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj13').
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI 
               InjIncr _ InjSep VBj12_1 VBj12_2 VBj23_1 VBj').
  assert (preAL12' := mkInjections_aligned_1 _ _ _ _ _ _ _ _ _ _ HeqMKI AL12).
  assert (AL12' : inject_aligned  (removeUndefs j12 j' prej12')).
          intros b; intros. apply RU_D in H.  
          eapply preAL12'. apply H. assumption.
  assert (AL23' := mkInjections_aligned_2 _ _ _ _ _ _ _ _ _ _ 
                   HeqMKI AL23 AL13').
split. assumption.
split. assumption.
split. assumption.
split. assumption.
split. assumption.
assert (IDextensional: forall b,  
            j' b = compose_meminj (removeUndefs j12 j' prej12') j23' b).
   intros. rewrite <- ID. trivial.
clear ID.
assert (Fwd2: mem_forward m2 m2').
  split; intros; rename b into b2.
  (*valid_block*)
     clear - N2 H NB1. unfold Mem.valid_block in *. omega. 
  split; intros.
  (*max*)
     destruct (ACCESS b2) as [Val2 _].
     specialize (Val2 H Max ofs). 
     remember (j23 b2) as jb.
     destruct jb; apply eq_sym in Heqjb.
         destruct p0. 
         remember (source j12 m1 b2 ofs) as src.
         destruct src.
           apply source_SomeE in Heqsrc.
           destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
           subst.
           rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2.
           eapply MInj12. apply J1. reflexivity. 
             eapply Fwd1.
                apply (Mem.perm_valid_block _ _  _ _ _ P1).
                apply H0. 
        rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2. apply H0.
    rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2. apply H0.
  (*Res*)
     destruct (ACCESS b2) as [Val2 _].
     specialize (Val2 H Res ofs). simpl in Val2. 
     rewrite (perm_subst _ _ _ _ _ _ _ Val2); clear Val2.
     split; auto.
assert (Unch2: my_mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2').
  split; intros.
     apply (valid_split _ _ _ _ (ACCESS b)); intros; clear ACCESS.
     (* case Mem.valid_block m2 b*)
        specialize (H1 k ofs).
        case_eq (isMaxCur k); intros MCk.
        (*case MaxOrCur*)
          assert (HH:match j23 b with
           | Some (_, _) =>
               match source j12 m1 b ofs with
               | Some (b1, ofs1) =>
                   ZMap.get b (Mem.mem_access m2') ofs k =
                   ZMap.get b1 (Mem.mem_access m1') ofs1 k
               | None =>
                   ZMap.get b (Mem.mem_access m2') ofs k =
                   ZMap.get b (Mem.mem_access m2) ofs k
               end
           | None =>
               ZMap.get b (Mem.mem_access m2') ofs k =
               ZMap.get b (Mem.mem_access m2) ofs k
           end).
            destruct k; simpl in *; try assumption. inv MCk.
          clear H1 MCk.
          unfold loc_out_of_reach in HP.
          remember (j23  b) as jb.
          destruct jb; apply eq_sym in Heqjb.
            destruct p.
            remember (source j12 m1 b ofs) as d.
            destruct d.
             destruct p. 
             rewrite (perm_subst _ _ _ _ _ _ _ HH). clear HH.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
             subst. apply eq_sym in PP. inv PP.
             specialize (HP _ _ JJ). assert (z0 + dd1 - dd1 = z0). omega. 
             rewrite H1 in HP.
             exfalso. apply (HP PERM).
          rewrite (perm_subst _ _ _ _ _ _ _ HH). trivial.
          rewrite (perm_subst _ _ _ _ _ _ _ HH). trivial.
        (*case Res*)
            destruct k; simpl in *; inv MCk.
            rewrite (perm_subst _ _ _ _ _ _ _ H1). trivial.
      (*invalid*)
           exfalso. apply (H0 H).
  apply (valid_split _ _ _ _ (CONT b)); intros; clear CONT.
      (* case Mem.valid_block m2 b*)
          specialize (H1 ofs).
          remember (source j12 m1 b ofs) as d.
          destruct d.
            destruct p.
            destruct (source_SomeE _ _ _ _ _ Heqd)
               as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
            subst. apply eq_sym in PP. inv PP.
            assert (NonPerm: ~Mem.perm m1 b0 (z + dd1 - dd1) Max Nonempty).
                eapply HP. apply JJ.
            assert (z + dd1 - dd1 = z). omega. 
            rewrite H in NonPerm.
            exfalso. apply (NonPerm  PERM).
         rewrite  H1. trivial.
       (*invalid*)
          exfalso. (* apply Mem.load_valid_access in H0. apply H1. 
               apply Mem.valid_access_perm with (k:=Max) in H0.
              apply (Mem.perm_valid_block _ _ _ _ _  H0).*)
              apply Mem.perm_valid_block in HMeperm. apply (H0 HMeperm).
assert (UnchLOM2: my_mem_unchanged_on (loc_unmapped j23) m2 m2').
  unfold loc_unmapped.
  split; intros.
        destruct (ACCESS b) as [Val _].
        specialize (Val H k ofs).
        rewrite HP in Val.
        destruct k; simpl in Val.
        (*case Res*)
            rewrite (perm_subst _ _ _ _ _ _ _ Val). clear Val. trivial.
        (*case max*)
(*          remember (source j12 m1 b ofs) as d.
          destruct d.
            destruct p0. *)
            rewrite (perm_subst _ _ _ _ _ _ _ Val). clear Val. trivial.
        (*case Cur*)
            rewrite (perm_subst _ _ _ _ _ _ _ Val). clear Val. trivial.
  apply (valid_split _ _ _ _ (CONT b)); intros; clear CONT.
      (*case Mem.valid_block m2 b*)
          specialize (H1 ofs).
          assert (j23' b = None).
               remember (j23' b) as d.
               destruct d; trivial. apply eq_sym in Heqd. destruct p.
               destruct (sep23 _ _ _ HP Heqd). exfalso. apply (H2 H0).
          remember (source j12 m1 b ofs) as d.
          destruct d.
             destruct p. subst. rewrite H2 in H1. apply H1. 
          (* destruct (source_SomeE _ _ _ _ _ Heqd) 
                   as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. 
                 clear Heqd.
                 subst. apply eq_sym in PP. inv PP. 
                 unfold compose_meminj in H1. rewrite (inc12 _ _ _ JJ) in H1.
                 rewrite H2 in H1. apply H1.*)
          rewrite H1. apply H.
      (*case invalid*)
          exfalso. apply Mem.perm_valid_block in HMeperm. apply (H0 HMeperm).

assert (UnchLOOR3: my_mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3').
   unfold loc_out_of_reach.
   split; intros.
      eapply Unch33'. 
        unfold loc_out_of_reach, compose_meminj. intros.
           remember (j12 b0) as d.
           destruct d. 
              apply eq_sym in Heqd. destruct p.
              remember (j23 b1) as dd.
              destruct dd; inv H0. apply eq_sym in Heqdd. destruct p. inv H2.
              specialize (HP _ _ Heqdd). 
              intros N. apply HP.
              assert (ofs - (z + z0) + z = ofs - z0). omega.
              rewrite <- H0.
              eapply MInj12. apply Heqd. reflexivity. apply N.
           inv H0.
        apply H. 
   eapply Unch33'. 
        unfold loc_out_of_reach, compose_meminj. intros.
           remember (j12 b0) as d.
           destruct d.
              apply eq_sym in Heqd. destruct p.
              remember (j23 b1) as dd.
              destruct dd; inv H0. apply eq_sym in Heqdd. destruct p. inv H2.
              intros N. eapply (HP _  _ Heqdd). 
              assert (ofs - (z + z0) + z = ofs - z0). omega.
              rewrite <- H. eapply MInj12. apply Heqd. reflexivity. apply N.
           inv H0.
        apply HMeperm.
      apply H.
assert (NOVj12':= RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ 
                  MInj23 _ _ _ _ _ HeqMKI).
assert (Inj12': Mem.inject (removeUndefs j12 j' prej12') m1' m2').
    assert (Perm12': forall b1 b2 delta ofs k p,
             (removeUndefs j12 j' prej12') b1 = Some (b2, delta) ->
             isMaxCur k = true ->
             Mem.perm m1' b1 ofs k p -> Mem.perm m2' b2 (ofs + delta) k p).
        intros. rename H0 into MCk. rename H1 into H0.
        apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
           specialize (H2 k (ofs+delta)).
             assert (HH:match j23 b2 with
               | Some (_, _) =>
                   match source j12 m1 b2 (ofs + delta) with
                   | Some (b1, ofs1) =>
                       ZMap.get b2 (Mem.mem_access m2') (ofs + delta) k =
                       ZMap.get b1 (Mem.mem_access m1') ofs1 k
                   | None =>
                       ZMap.get b2 (Mem.mem_access m2') (ofs + delta) k =
                       ZMap.get b2 (Mem.mem_access m2) (ofs + delta) k
                   end
               | None =>
                   ZMap.get b2 (Mem.mem_access m2') (ofs + delta) k =
                   ZMap.get b2 (Mem.mem_access m2) (ofs + delta) k
               end).
               destruct k; simpl in *; try assumption. inv MCk.
             assert (MAX: Mem.perm m1' b1 ofs Max Nonempty).
               assert (X: Mem.perm m1' b1 ofs Max p).
                 destruct k; try inv MCk.
                 assumption.
                 eapply Mem.perm_cur_max; eassumption.
               eapply Mem.perm_implies; try eassumption.
                  constructor.
           clear H2.
             remember (j23 b2) as d.
             destruct d; apply eq_sym in Heqd.
               destruct p0 as [b3 d3].
               remember (j12 b1) as dd.
               destruct dd; apply eq_sym in Heqdd.
                 destruct p0.
                 rewrite (inc12 _ _ _ Heqdd) in H. inv H.
                 rewrite (source_SomeI j12 _  _ b1) in HH.
                 rewrite (perm_subst _ _ _ _ _ _ _ HH). apply H0.
                 apply MInj12.
                    assumption.
                    apply Fwd1. apply (VBj12_1 _ _ _ Heqdd).
                                apply MAX.
               destruct (sep12 _ _ _ Heqdd H) as [_ NV2]. exfalso. apply (NV2 H1).
             rewrite (perm_subst _ _ _ _ _ _ _ HH). clear HH.
                 destruct Unch11' as [UP _].
                 remember (j12 b1) as dd.
                 destruct dd; apply eq_sym in Heqdd.
                   destruct p0.
                   rewrite (inc12 _ _ _ Heqdd) in H. inv H.
                   eapply MInj12. apply Heqdd. assumption.
                   rewrite UP. apply H0.
                      unfold loc_unmapped, compose_meminj. 
                          rewrite Heqdd. rewrite Heqd. trivial.
                      apply (VBj12_1 _ _ _ Heqdd).
             destruct (sep12 _ _ _ Heqdd H) as [_ NV2]. exfalso. apply (NV2 H1).
        (*case ~ valid_block m2 b2*)
          specialize (H2 k (ofs+delta)).   
            assert (HH: 
             match source (removeUndefs j12 j' prej12') m1' b2 (ofs + delta) 
             with
              | Some (b1, ofs1) =>
                  ZMap.get b2 (Mem.mem_access m2') (ofs + delta) k =
                  ZMap.get b1 (Mem.mem_access m1') ofs1 k
              | None => ZMap.get b2 (Mem.mem_access m2') (ofs + delta) k = None
              end).
              destruct k; simpl in *; try inv MCk; assumption.
            assert (MAX: Mem.perm m1' b1 ofs Max Nonempty).
               assert (X: Mem.perm m1' b1 ofs Max p).
                 destruct k; try inv MCk.
                 assumption.
                 eapply Mem.perm_cur_max; eassumption.
               eapply Mem.perm_implies; try eassumption.
                  constructor.
            clear H2.
            rewrite (source_SomeI (removeUndefs j12 j' prej12') _  _ b1) in HH.
            rewrite (perm_subst _ _ _ _ _ _ _ HH). apply H0.
            apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ 
                    MInj23 _ _ _ _ _ HeqMKI).
               assumption.
               assumption.
    assert (INJ:Mem.mem_inj  (removeUndefs j12 j' prej12') m1' m2'). 
      split. apply Perm12'.
      (*valid_access*) 
          intros. destruct H0.
          split.
              intros off; intros.
              assert (Hoff: ofs <= off-delta < ofs + size_chunk chunk). omega. 
              specialize (Perm12' _ _ _ _ _ _ H Cur_isMaxCur (H0 _ Hoff)).
              assert (off - delta + delta = off). omega. 
              rewrite H3 in Perm12'. apply Perm12'.
              (*we can't use Mem.aligned_area_inject because we want to 
                PROVE Mem.inject (removeUndefs j12 j' prej12')  m1' m2').*)
                (*assert (RP : Mem.range_perm m1' b1 ofs 
                              (ofs + size_chunk chunk) Cur Nonempty).
                  intros off Hoff. eapply Mem.perm_implies.
                    apply (H0 _ Hoff). apply perm_any_N. 
                   eapply Mem.aligned_area_inject with
                    (sz:=size_chunk chunk). Focus 5. apply RP. 
                        Focus 6. apply H. 
                            apply H1. Focus 4. apply H1.
                  THIS IS ONE OF THE PLACES WHERE 
                       inject_aligned_of IS REQUIRED*)
                   eapply (inject_aligned_ofs _ AL12' _ _ _ _ H _ H1). 
      (*memval  j12' m1' m2'.*)
          intros. 
          apply (valid_split _ _ _ _ (CONT b2)); intros; clear CONT.
         (*case Mem.valid_block m2 b2*)
             specialize (H2 (ofs + delta)).
             assert (J12:  j12 b1 = Some (b2, delta)).
                 remember (j12 b1) as d. 
                 destruct d; apply eq_sym in Heqd.
                      destruct p. rewrite (inc12 _ _ _ Heqd) in H. apply H.
                      destruct (sep12 _ _ _ Heqd H). exfalso. apply (H4 H1).
             assert (Val1:= VBj12_1 _ _ _ J12).
             assert (Perm1: Mem.perm m1 b1 ofs Max Nonempty).
                   apply (Fwd1 _ Val1). 
                      eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                        apply H0. apply perm_any_N.
             remember (source j12 m1 b2 (ofs + delta)) as ss.
             destruct ss.
             (*source  j12 m1 b2 (ofs + delta)  = Some p *)
                 destruct (source_SomeE _ _ _ _ _ Heqss)
                    as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
                 clear Heqss. subst.     
                 destruct (eq_block bb1 b1); subst.
                 (*case bb1 = b1*)
                     rewrite J12 in JJ. apply eq_sym in JJ. inv JJ. 
                     assert (ofs11 = ofs). omega. 
                     subst. clear Off2. 
                     remember (j23' b2) as j23'b2.
                     destruct j23'b2; apply eq_sym in Heqj23'b2.
                     (*j23' b2 = Some p*)
                         destruct p. rewrite H2. clear H2.
                         assert (COMP: compose_meminj 
                                   (removeUndefs j12 j' prej12') j23' b1 = 
                                 Some(b, delta+z)).
                            unfold compose_meminj. rewrite H. 
                            rewrite Heqj23'b2. trivial.
                         assert (COMP': j' b1 = Some(b, delta+z)). 
                            rewrite IDextensional. apply COMP.
                         assert (MV:= Mem.mi_memval _ _ _
                            (Mem.mi_inj _ _ _ MInj13') _ _  _ _ COMP' H0).
                         inv MV; try constructor. 
                           simpl. 
                           rewrite IDextensional in H4.
                           apply compose_meminjD_Some in H4.
                           destruct H4 as [bb1 [off1 [off [JJ1 [JJ2 Delta]]]]].
                           subst. 
                           rewrite JJ1. econstructor. apply JJ1. trivial.
                     (*j23' b2 = None*)
                         rewrite H2. clear H2.
                         assert (J23: j23 b2 = None).
                            remember (j23 b2) as d; 
                            destruct d; trivial; apply eq_sym in Heqd.
                            destruct p. 
                            rewrite (inc23 _ _ _ Heqd) in Heqj23'b2. 
                            discriminate.
                         destruct Unch11' as [Uperm Uval]. 
                         assert (UNMAPPED: loc_unmapped 
                                       (compose_meminj j12 j23) b1 ofs).
                            unfold compose_meminj, loc_unmapped. 
                            rewrite J12. rewrite J23. trivial.
                         assert (RD: Mem.perm m1 b1 ofs Cur Readable). 
                            rewrite Uperm. assumption. assumption. assumption.
                         rewrite (Uval b1 ofs UNMAPPED RD _ (eq_refl _)).
                         apply (memval_inject_incr j12).
                            apply (Mem.mi_memval _ _ _ 
                               (Mem.mi_inj _ _ _ MInj12) _ _  _ _ J12 RD).
                            assumption.
                 (* case bb1 <> b1*)   
                      exfalso. 
                      destruct (Mem.mi_no_overlap _ _ _ MInj12
                             bb1 _ _ _ _ _ _ _ n JJ J12 PERM  Perm1).
                        apply H3; trivial.
                        apply H3. rewrite Off2. trivial.
             (*source  j12 m1 b2 (ofs + delta)  = None *)
                 exfalso.
                 apply (source_NoneE _ _ _ _ Heqss _ _  
                        (VALIDBLOCK _ _ Val1) J12). 
                 assert (ofs + delta - delta = ofs). omega.
                 rewrite H3. apply Perm1.  
         (*case ~ Mem.valid_block m2 b2*)
            specialize (H2 (ofs + delta)).
            assert (J12:  j12 b1 = None).
               remember (j12 b1) as d. 
               destruct d; apply eq_sym in Heqd; trivial.
                     destruct p. rewrite (inc12 _ _ _ Heqd) in H. inv H.
                     exfalso. apply H1. apply (VBj12_2 _ _ _ Heqd).
            remember (source  (removeUndefs j12 j' prej12')
                   m1' b2 (ofs + delta)) as ss.
            destruct ss.
            (*source  j12' m1' b2 (ofs + delta)  = Some p *)
                destruct p. rewrite H2. clear H2.
                remember (ZMap.get ofs (ZMap.get b1 (Mem.mem_contents m1'))) 
                          as v.
                destruct (source_SomeE _ _ _ _ _ Heqss)
                      as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
                clear Heqss.
                apply eq_sym in PP. inv PP.
                assert (MX: Mem.perm m1' b1 ofs Max Nonempty).
                    eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                    apply H0. apply perm_any_N.
                destruct (eq_block b b1); subst.
                (*case b = b1*)
                   rewrite H in JJ. apply eq_sym in JJ. inv JJ. 
                   assert (z = ofs). omega. 
                   subst.  clear Off2. 
                   remember (ZMap.get ofs (ZMap.get b1 (Mem.mem_contents m1')))
                              as v.
                   remember (j23' b2) as j23'b2.
                   destruct j23'b2; apply eq_sym in Heqj23'b2.
                   (*j23' b2 = Some p*)
                       destruct p as [b3 delta3].
                       assert (COMP: compose_meminj 
                                  (removeUndefs j12 j' prej12') j23' b1
                                  = Some(b3, delta+delta3)).
                           unfold compose_meminj. 
                           rewrite H. rewrite Heqj23'b2. trivial.
                       assert (COMP': j' b1 = Some(b3, delta+delta3)).
                            rewrite IDextensional. apply COMP.
                       assert (MV:= Mem.mi_memval _ _ _ 
                           (Mem.mi_inj _ _ _ MInj13') _ _  _ _ COMP' H0).
                       subst. (*revert the abbreviation v that was
                            introduced for "self-didactic" purpose*)
                       inv MV; try constructor. 
                       simpl. rewrite IDextensional in H4. 
                       apply compose_meminjD_Some in H4.
                       destruct H4 as [bb1 [off1 [off [JJ1 [JJ2 Delta]]]]].
                       subst. 
                       rewrite JJ1. econstructor. apply JJ1. trivial.
                   (*j23' b2 = None -- the following 5 lines are where the
                         removeUndefs definition comes into play
                         (compare to MemoryPsuhout_II_Wrong!)
                         probably the is can be cleaned up a bit...!*)
                       clear - IDextensional H J12 Heqj23'b2.
                       unfold removeUndefs in H. rewrite J12 in H.
                       remember (j' b1) as d.
                       destruct d; try inv H. 
                       destruct p. rewrite IDextensional in Heqd.
                       unfold compose_meminj, removeUndefs in Heqd. 
                       rewrite J12 in Heqd. 
                       remember ( j' b1) as d.
                       destruct d. 
                         destruct p. rewrite H1 in Heqd. 
                         rewrite Heqj23'b2 in Heqd.  inv Heqd.
                       inv Heqd.
                (* case b <> b1*)  exfalso. 
                    destruct (NOVj12' b  _ _ _ _ _ _ _ n JJ H PERM MX).
                         apply H2; trivial.
                         apply H2. rewrite Off2. trivial.
            (*source  j12' m1' b2 (ofs + delta)  = None *) exfalso.
               apply (source_NoneE _ _ _ _ Heqss _ _ 
                    (VALIDBLOCK _ _  (Mem.perm_valid_block _ _ _ _ _ H0)) H). 
               assert (ofs + delta - delta = ofs). omega.
               rewrite H3.
               eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                    apply H0. apply perm_any_N.
       (*mi_reserved*) intros.
            
   split. apply INJ.
   (* mi_freeblocks*)  intros. 
        remember (removeUndefs j12 j' prej12'  b) as d.
        destruct d; apply eq_sym in Heqd; trivial. destruct p.
        unfold removeUndefs in Heqd.
        remember (j12 b) as dd.
        destruct dd; apply eq_sym in Heqdd.
            destruct p.
            exfalso. apply H. apply Fwd1. apply (VBj12_1 _ _ _ Heqdd).
        remember (j' b) as ddd.
        destruct ddd; apply eq_sym in Heqddd.
            destruct p. exfalso. apply H. apply (VBj' _ _ _ Heqddd).
        inv Heqd.
  (*mi_mappedblock*) intros.
     assert (ValJ12: forall b1 b2 ofs2,  j12 b1 = Some (b2, ofs2) ->
                     b1 < Mem.nextblock m1 /\ b2 < Mem.nextblock m2).
         intros. split. apply (VBj12_1 _ _ _ H0). apply (VBj12_2 _ _ _ H0).
     remember (removeUndefs j12 j' prej12'  b) as d.
     destruct d; apply eq_sym in Heqd.
        inv H.
        unfold removeUndefs in Heqd.
        remember (j12 b) as dd.
        destruct dd; apply eq_sym in Heqdd.
            destruct p. inv Heqd. apply Fwd2. apply (VBj12_2 _ _ _ Heqdd).
        remember (j' b) as ddd.
        destruct ddd; apply eq_sym in Heqddd.
          destruct p. 
          destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _ 
                      HeqMKI ValJ12  VBj23_1 _ _ _ Heqd).
            destruct H as [J12 [Val1 Val2]]. apply Fwd2. apply Val2.
            destruct H as [? [_ [_ [_ [_ [_ D]]]]]]. apply D.
        inv Heqd.
     inv H.
  (*no_overlap*)
       apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ _ _ _ _ HeqMKI).
  (*representable*)
       intros. 
       unfold removeUndefs in H.
       remember (j12 b) as d.
admit.  (* weak_valid_pointer...
       destruct d; apply eq_sym in Heqd.
          destruct p. inv H.
          eapply MInj12. apply Heqd. 
          apply Fwd1. apply (VBj12_1 _ _ _ Heqd). eapply Mem.perm_max. apply H0.
       remember (j' b) as dd.
       destruct dd; apply eq_sym in Heqdd.
          destruct p0.
          destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _ 
                     HeqMKI VB12  VBj23_1 _ _ _ H).
              destruct H1. rewrite H1 in Heqd. discriminate.
              destruct H1 as [M [ZM [A [B [C [D E]]]]]]. 
                 rewrite C in *.
                 split. omega. 
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
       inv H.  *)
   (*unmappedreserved*)
     intros. unfold removeUndefs in H.
     remember (j12 b) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p. inv H.
     remember (j' b) as o.
     destruct o; apply eq_sym in Heqo.
       destruct p.
         assert (compose_meminj (removeUndefs j12 j' prej12') j23' b = Some(b0,z)).
           rewrite IDextensional in Heqo. assumption.
         destruct (compose_meminjD_Some _ _ _ _ _ H0) 
           as [b2 [delta2 [delta3 [J1' [J2' D]]]]].
         subst; clear H0. rename b0 into b3.
         unfold removeUndefs in J1'.
         rewrite Heqd in J1'. rewrite Heqo in J1'. 
         rewrite H in J1'. inv J1'.
     clear H. eapply MInj13'. apply Heqo.
   (*reserved*) intros.
      split; intros. unfold Mem.reserved in *.
         destruct H as [p Hp].
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
           specialize (H1 Res ofs). simpl in *.
           assert (J: j12 b1 = Some(b2, delta)).
             remember (j12 b1) as d.
               destruct d; apply eq_sym in Heqd.
                 destruct p0. rewrite (inc12 _ _ _ Heqd) in H0.
                 assumption.
               destruct (sep12 _ _ _ Heqd H0).
                 contradiction.
           rewrite (perm_subst _ _ _ _ _ _ _ H1) in Hp. clear H1. 
           destruct (Mem.mi_reserved _ _ _ MInj12 b2 ofs) as [X _].
           destruct X with (b1:=b1)(delta:=delta).
              exists p. apply Hp.
              apply J.
           exists x. eapply Fwd1; trivial.
              apply (VBj12_1 _ _ _ J).
        (*case ~ valid_block m2 b2*)
          specialize (H1 Res ofs); simpl in *.   
          remember (sourceP
             (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
             (noperm_dec m1' Res Nonempty) (removeUndefs j12 j' prej12') m1' b2
             ofs) as src.
          destruct src.
            destruct (sourceP_SomeE _ _ _ _ _ _ _ Heqsrc)
                    as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc. subst.
            unfold Mem.perm in Hp. rewrite H1 in Hp.
            simpl in Hp. contradiction.
          destruct (zlt b2 (Mem.nextblock m2')).
            specialize (sourceP_NoneE _ _ _ _ _ _ Heqsrc). 
            clear Heqsrc; intros SRC.
            assert (VB: 0 <= b1 < Mem.nextblock m1').
               apply VALIDBLOCK. 
               unfold removeUndefs in H0.
                remember (j12 b1).
                destruct o; apply eq_sym in Heqo.
                   destruct p0. inv H0.
                   apply Fwd1. apply (VBj12_1 _ _ _ Heqo).
                remember (j' b1).
                destruct o; apply eq_sym in Heqo0.
                   destruct p0. 
                   eapply VBj'. apply Heqo0.
                inv H0.
            specialize (SRC b1 delta VB H0).
             apply Classical_Prop.NNPP in SRC.
             exists Nonempty. assumption.
          unfold Mem.perm in Hp. rewrite H1 in Hp.
            simpl in Hp. contradiction.
      (*reverse implication*)
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
           specialize (H1 Res ofs). simpl in *.
           cut (Mem.reserved m2 b2 ofs).
              unfold Mem.reserved, Mem.perm. rewrite H1. trivial. 
           clear H1.
           eapply MInj12. intros.
           specialize (H _ _ (inc12 _ _ _ H1)).
           assert (VB1:= VBj12_1 _ _ _ H1).
           destruct (Fwd1 _ VB1) as [_ [_ ?]].
           destruct H as [p Hp].
           apply H2 in Hp. exists p. apply Hp.
        (*case ~ valid_block m2 b2*)
          specialize (H1 Res ofs); simpl in *.   
          remember (sourceP
             (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
             (noperm_dec m1' Res Nonempty) (removeUndefs j12 j' prej12') m1' b2
             ofs) as src.
          destruct src.
            destruct (sourceP_SomeE _ _ _ _ _ _ _ Heqsrc)
                    as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc. subst.
             specialize (H _ _ JJ).
             destruct H as [p Hp].
             exfalso. apply PERM. 
             assert (ofs11 + dd1 - dd1 = ofs11) by omega.
             rewrite H in Hp; clear H.
             eapply Mem.perm_implies. apply Hp. apply perm_any_N.
          specialize (sourceP_NoneE _ _ _ _ _ _ Heqsrc). 
            clear Heqsrc; intros SRC.
            destruct (zlt b2 (Mem.nextblock m2')).
              exists Nonempty. unfold Mem.perm. rewrite H1.
               constructor.
            admit. (*TODO - maybe add valid-block condition in inject'?*)
split; trivial.
split; trivial.
assert (Inj23': Mem.inject j23' m2' m3').
   assert (Perm23': forall b1 b2 delta ofs k p,
                j23' b1 = Some (b2, delta) -> 
                isMaxCur k = true ->
                Mem.perm m2' b1 ofs k p -> Mem.perm m3' b2 (ofs + delta) k p).
      intros b2 b3; intros. rename H0 into iMC. rename H1 into H0. 
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
      (*valid*)
          specialize (H2 k ofs).
          assert (FF: j23 b2 = Some (b3, delta)).
             remember (j23 b2) as dd.
             destruct dd; apply eq_sym in Heqdd.
               destruct p0. apply inc23 in Heqdd. rewrite Heqdd in H. apply H.
             destruct (sep23 _ _ _ Heqdd H). exfalso. apply (H3 H1).
          rewrite FF in H2.
          assert (HH: match source j12 m1 b2 ofs with
              | Some (b1, ofs1) =>
                  ZMap.get b2 (Mem.mem_access m2') ofs k =
                  ZMap.get b1 (Mem.mem_access m1') ofs1 k
              | None =>
                  ZMap.get b2 (Mem.mem_access m2') ofs k =
                  ZMap.get b2 (Mem.mem_access m2) ofs k
              end).
              destruct k; simpl in *; try inv iMC; assumption.
          clear H2.
          remember (source j12 m1 b2 ofs) as d.
          destruct d. 
          (*source  j12 m1 b2 ofs = Some p0*)
              destruct p0. 
              destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
              subst. apply eq_sym in PP. inv PP.
              rewrite (perm_subst _ _ _ _ _ _ _ HH) in H0. clear HH.
              rewrite <- Zplus_assoc.
              assert (J: j' b = Some (b3, dd1 + delta)).
                  apply InjIncr. unfold compose_meminj.
                     rewrite JJ. rewrite FF. trivial. 
              eapply MInj13'. apply J. assumption. 
                 apply H0.
          (*source  j12 m1 b2 ofs = None*)
              rewrite (perm_subst _ _ _ _ _ _ _ HH) in H0. clear HH.
              assert (MX: Mem.perm m2 b2 ofs Max Nonempty).
                  destruct k; simpl in *; try inv iMC; trivial.
                     eapply Mem.perm_implies.
                       apply H0. apply perm_any_N.
                  eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                     apply H0. apply perm_any_N.
              assert (SRC:= source_NoneE _ _ _ _ Heqd). clear Heqd.
              assert (UNCH: loc_out_of_reach 
                          (compose_meminj j12 j23) m1 b3 (ofs + delta)).
                  unfold loc_out_of_reach, compose_meminj. intros.
                  remember (j12 b0) as dd.
                  destruct dd; inv H2. 
                  destruct p0. apply eq_sym in Heqdd.   
                  remember (j23 b) as ddd.
                  destruct ddd; inv H4. 
                  destruct p0. apply eq_sym in Heqddd. inv H3.
                  destruct (eq_block b2 b); subst.
                  (*case b2=b*)
                     rewrite (inc23 _ _ _ Heqddd) in H. inv H. 
                     assert (ofs + delta - (z + delta) = ofs - z). omega. 
                     rewrite H.
                     apply (SRC _ _ (VALIDBLOCK _ _  
                                          (VBj12_1 _ _ _ Heqdd)) Heqdd).
                  (*case b2 <> b*)
                     intros N. 
                     assert (PX: Mem.perm m2 b (ofs + delta - z0) Max Nonempty).
                        assert (ofs+delta-(z+z0)+z = ofs+delta-z0). omega. 
                        rewrite <- H2.
                        eapply MInj12. apply Heqdd. reflexivity. apply N.
                     assert (NOV := Mem.mi_no_overlap _ _ _ 
                            MInj23 b2 _ _ b _ _ _ _ n FF Heqddd MX PX).
                     destruct NOV.
                           apply H2. trivial.
                           apply H2. omega.
              destruct Unch33' as [U33P _]. 
              rewrite <- U33P.  
                    eapply MInj23. apply FF. assumption. apply H0.
                    apply UNCH. 
                    apply (VBj23_2 _ _ _ FF).
      (*invalid*)
          assert (MX: Mem.perm m2' b2 ofs Max Nonempty).
                  destruct k; simpl in *; try inv iMC; trivial.
                     eapply Mem.perm_implies.
                       apply H0. apply perm_any_N.
                  eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                     apply H0. apply perm_any_N.
          assert (Max2':= H2 Max ofs). simpl in Max2'.
          specialize (H2 k ofs).
          assert (HH: match source (removeUndefs j12 j' prej12') m1' b2 ofs with
              | Some (b1, ofs1) =>
                  ZMap.get b2 (Mem.mem_access m2') ofs k =
                  ZMap.get b1 (Mem.mem_access m1') ofs1 k
              | None => ZMap.get b2 (Mem.mem_access m2') ofs k = None
              end).
             destruct k; try inv iMC; trivial.
          clear H2.

          assert (J12: j23 b2 = None).
              remember (j23 b2) as d.
              destruct d; trivial. apply eq_sym in Heqd. destruct p0.
              assert (X:= VBj23_1 _ _ _ Heqd).
              exfalso.  apply (H1 X).
          remember (source (removeUndefs j12 j' prej12') m1' b2 ofs) as d.
          destruct d. destruct p0.
              rewrite (perm_subst _ _ _ _ _ _ _ HH) in *. clear HH.
              rewrite (perm_subst _ _ _ _ _ _ _ Max2') in*. clear Max2'.
              destruct (source_SomeE _ _ _ _ _ Heqd)
                as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off2]]]]]]]. clear Heqd.
              subst. apply eq_sym in PP. inv PP.
              rewrite <- Zplus_assoc.
              assert (Jb: j' b= Some (b3, dd1 + delta)).
                  rewrite IDextensional. unfold compose_meminj.
                           rewrite JJ'. rewrite H. trivial.
              eapply MInj13'. apply Jb. assumption. apply H0.  
          unfold Mem.perm in MX. rewrite Max2' in MX.  inv MX. 
                      (*specialize (source_NoneE _ _ _ _ Heqd). intros SRC. clear Heqd.
                        rewrite H in *.
                        rewrite (perm_subst _ _ _ _ _ _ _ H2) in*. clear H2. trivial.*)
   assert (MI: Mem.mem_inj j23' m2' m3').
      split.
      (*mi_perm *) apply Perm23'.
      (*valid_access*)
          intros. destruct H0.
          split. intros off; intros. 
                 assert (ofs <= off - delta < ofs + size_chunk chunk). omega.
                 specialize (H0 _ H3).
                 specialize (Perm23' _ _ _ _ _ _ H Cur_isMaxCur H0).
                 assert (off - delta + delta = off). omega. 
               rewrite H4 in Perm23'. apply Perm23'.
          eapply (inject_aligned_ofs _ AL23' _ _ _ _ H _ H1). 
      (*memval j23' m2' m3'*) intros b2 ofs2 b3 delta3 Jb2 Perm2.
          assert (Perm2Max: Mem.perm m2' b2 ofs2  Max Nonempty).
             eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                        apply Perm2. constructor.
          destruct (ACCESS b2) as [Valid Invalid].
          apply (valid_split _ _ _ _ (CONT b2)); intros; clear CONT.
          (*case Mem.valid_block m2 b2*)
             specialize (Valid H Cur ofs2). clear Invalid.
             specialize (H0 ofs2).
             assert (J23:  j23 b2 = Some (b3, delta3)).
                 remember (j23 b2) as d. destruct d; apply eq_sym in Heqd.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. apply Jb2.
                    destruct (sep23 _ _ _ Heqd Jb2). exfalso. apply (H1 H).
             rewrite J23 in Valid. rewrite Jb2 in H0.
             remember (source j12 m1 b2 ofs2) as ss.
             destruct ss.
             (*source  j12 m1 b2 ofs2  = Some p *)
                destruct (source_SomeE _ _ _ _ _ Heqss)
                    as [b1 [delta2 [ofs1 [PP [Valb1 [ Jb1 [Perm1 Off]]]]]]].
                clear Heqss; subst.
                rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid.
                rewrite H0 in *. clear H0. simpl in *.
                assert (Perm1'Max: Mem.perm m1' b1 ofs1 Max Nonempty).
                   eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                      apply Perm2. constructor.
                assert (J': j' b1 = Some (b3, delta2 + delta3)).
                    rewrite IDextensional. unfold compose_meminj. 
                    rewrite (inc12 _ _ _ Jb1). rewrite Jb2. trivial.
                specialize (Mem.mi_memval j' m1' m3'
                    (Mem.mi_inj _ _ _ MInj13') _ _  _ _ J' Perm2). 
                intros MemVal13'. 
                rewrite IDextensional in J'.                   
                destruct (compose_meminjD_Some _ _ _ _ _ J') 
                    as [bb2 [dd2 [dd3 [RR [JJ23  DD]]]]]; subst.
                assert (XX:= inc12 _ _ _ Jb1). rewrite RR in XX. inv XX. 
                assert (dd3 = delta3). omega. 
                rewrite H0 in *. clear H0 DD.
                rewrite <- Zplus_assoc.
                inv MemVal13'; simpl in *; try econstructor.
                rewrite IDextensional in H2.                     
                destruct (compose_meminjD_Some _ _ _ _ _ H2)
                    as [bb2 [dd2 [ddd3 [RRR [JJJ23  DD]]]]]; subst.
                rewrite RRR. econstructor. apply JJJ23.
                rewrite Int.add_assoc. decEq. unfold Int.add. 
                    apply Int.eqm_samerepr. auto with ints.
             (*case source  j12 m1 b2 ofs2  = None *)
                rewrite H0. clear H0.
                rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid. 
                assert (MX : Mem.perm m2 b2 ofs2 Max Nonempty).
                     eapply Mem.perm_cur_max. eapply Mem.perm_implies. 
                     apply Perm2. constructor.
                assert (LOOR: loc_out_of_reach 
                             (compose_meminj j12 j23) m1 b3 (ofs2+delta3)).
                     unfold loc_out_of_reach, compose_meminj. intros.
                     remember (j12 b0) as q.
                     destruct q; apply eq_sym in Heqq; inv H0.
                     destruct p.
                     remember (j23 b) as qq.
                     destruct qq; apply eq_sym in Heqqq; inv H2. 
                     destruct p. inv H1.
                     destruct (eq_block b2 b); subst.
                     (*case b2=b*)
                         rewrite J23  in Heqqq. inv Heqqq. 
                         assert (ofs2 + z0 - (z + z0) = ofs2 - z). omega. 
                         rewrite H0.
                         apply (source_NoneE _ _ _ _ Heqss). 
                             apply (VALIDBLOCK _ _  (VBj12_1 _ _ _ Heqq)).
                             apply Heqq.
                     (*case b2<>b*)
                         intros N.
                         assert (NN2: Mem.perm m2 b
                                     (ofs2 + (delta3 - z0)) Max Nonempty).
                             assert (ofs2 + delta3 - (z + z0) + z = 
                                      ofs2 + (delta3 - z0)). omega. 
                             rewrite <- H0.
                             eapply MInj12. apply Heqq. reflexivity. apply N.
                         destruct (Mem.mi_no_overlap _ _ _ 
                                 MInj23 b2 _ _ b _ _ _ _ n J23 Heqqq MX NN2).
                                     apply H0; trivial.
                                     apply H0. omega.
                assert (Perm3: Mem.perm m3 b3 (ofs2+delta3) Cur Readable).
                   eapply MInj23. apply J23. reflexivity. apply Perm2.
                destruct Unch33' as [Uperm UVal]. 
                rewrite (UVal _ _ LOOR Perm3 _ (eq_refl _)).
                eapply memval_inject_incr. 
                  apply (Mem.mi_memval _ _ _ 
                            (Mem.mi_inj _ _ _  MInj23) _ _ _ _ J23 Perm2). 
                  apply inc23.
          (*case ~ Mem.valid_block m2 b2*)
             specialize (H0 ofs2). clear Valid.
             assert (InvalidMax := Invalid H Max ofs2). 
             specialize (Invalid H Cur ofs2).
             assert (J23:  j23 b2 = None).
                 remember (j23 b2) as d. 
                 destruct d; apply eq_sym in Heqd; trivial.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. inv Jb2.
                          exfalso. apply H. apply (VBj23_1 _ _ _ Heqd).
             remember (source (removeUndefs j12 j' prej12') m1' b2 ofs2) as ss.
             destruct ss.
             (*source  j12' m1' b2 ofs2  = Some p *)
                 destruct p. rewrite H0 in *. clear H0.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid) in Perm2. 
                 clear Invalid. 
                 destruct (source_SomeE _ _ _ _ _ Heqss)
                    as [b1 [delta2 [ofs1 [PP [VB [RR1 [Perm1' Off2]]]]]]].
                 clear Heqss.
                 inv PP.
                 assert (Perm1'Max: Mem.perm m1' b1 ofs1 Max Nonempty).
                   eapply Mem.perm_cur_max. eapply Mem.perm_implies.
                       apply Perm2. apply perm_any_N.
                 assert (JB: j' b1 = Some (b3, delta2 + delta3)).
                       rewrite IDextensional. unfold compose_meminj.
                       rewrite RR1. rewrite Jb2. trivial.

                 specialize (Mem.mi_memval _ _ _ 
                       (Mem.mi_inj _ _ _  MInj13') _ _  _ _ JB Perm2). 
                 intros MemVal13'.                    
                 rewrite <- Zplus_assoc. 
                 inv MemVal13'; simpl in *; try econstructor.
                 rewrite IDextensional in H2.                     
                 destruct (compose_meminjD_Some _ _ _ _ _ H2)
                       as [bb2 [dd2 [ddd3 [RRR [JJJ23  DD]]]]]; subst.
                    rewrite RRR. econstructor. apply JJJ23.
                    rewrite Int.add_assoc. decEq. unfold Int.add. 
                       apply Int.eqm_samerepr. auto with ints.  
             (*source  j12' m1' b1 ofs  = None *) 
                 unfold Mem.perm in Perm2. rewrite Invalid in Perm2. inv Perm2.
   split; trivial.
   (*mi_freeblocks*)
       intros. remember (j23' b) as d.
       destruct d; apply eq_sym in Heqd; trivial.
       destruct p. exfalso.
       specialize (mkInjectionsN_0 _ _ _ _ _ _ _ _ _ _ HeqMKI).
       intros. destruct H0. clear H0.
       rewrite nat_of_Z_eq in H1.
         destruct (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ 
             HeqMKI VBj23_1 _ _ _ Heqd).
                      destruct H0. apply H. unfold Mem.valid_block. omega. 
                      destruct H0 as [M [ZM [BM [J' B']]]].  apply (H B').
         assumption.
   (*mi_mappedblocks*)
      intros. 
      destruct (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H).
           destruct H0. apply Fwd3. apply (VBj23_2 _ _ _  H0).
           destruct H0 as [M [ZM [BM [J' B']]]].  eapply MInj13'. apply J'.
   (*no_overlap*) intros b; intros.
      destruct (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H0).
         destruct H4 as [j23b vbb].
         destruct (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ 
               HeqMKI VBj23_1 _ _ _ H1).
            destruct H4 as [j23b2 vbb2]. 
            eapply MInj23. 
               apply H. 
               apply j23b. 
               apply j23b2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b). apply H2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b2). apply H3.
            destruct H4 as [M [ZM [BM [J' B']]]].
            left. assert ( j23 b2 = None).
                     remember (j23 b2) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1 BM ZM.
                     unfold Mem.valid_block in VBj23_1. exfalso. subst. omega.
                  intros N; subst. 
                  destruct (sep23 _ _ _ H4 H1). apply H6. 
                  eapply MInj23. apply j23b.
         destruct H4 as [M [ZM [NBb [j'b NBb']]]].
           destruct (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ 
                HeqMKI VBj23_1 _ _ _ H1).
             destruct H4 as [j23b2 vbb2].  
             left. assert ( j23 b = None).
                      remember (j23 b) as d. 
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1 NBb ZM.
                      unfold Mem.valid_block in VBj23_1. exfalso. subst. omega.
                   intros N; subst.
                   destruct (sep23 _ _ _ H4 H0).
                   apply H6. eapply MInj23. apply j23b2.
      (*case where both blocks are in m2' but not in m2*)
          destruct H4 as [M2 [ZM2 [NBb2 [j'b2 NBb2']]]]. subst.
              assert (j23_None1: j23 (Mem.nextblock m2 + M) = None).
                 remember (j23 (Mem.nextblock m2 + M)) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1 ZM.
                 exfalso. unfold Mem.valid_block in VBj23_1.  omega.
              assert (j23_None2: j23 (Mem.nextblock m2 + M2) = None).
                 remember (j23 (Mem.nextblock m2 + M2)) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1 ZM2.
                 exfalso. unfold Mem.valid_block in VBj23_1.  omega.      
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 Max_isMaxCur H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 Max_isMaxCur H3).
              assert (NEQ : Mem.nextblock m1 + M <> Mem.nextblock m1 + M2). 
                 clear - H. intros N. apply H. 
                 clear H. assert (M = M2). omega. 
                          subst; trivial.
              destruct (ACCESS  (Mem.nextblock m2 + M)) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).
                           
              remember (source (removeUndefs j12 j' prej12') 
                    m1' (Mem.nextblock m2 + M) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p. 
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2 + M2)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs j12 j' prej12') m1'
                         (Mem.nextblock m2 + M2) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p. 
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3. 
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2. rename M into M1.

                     destruct (source_SomeE _ _ _ _ _ Heqd) 
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (j12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1. 
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (j' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p. 
                     destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _ 
                              HeqMKI VB12 VBj23_1 _ _ _ H5).
                       destruct H4 as [? [? ?]]. clear -ZM H7. 
                             exfalso. omega.
                     destruct H4 as [MM1 [ZMM1 [BB1 [nbm [zz [X Y]]]]]]. 
                     subst. apply Zplus_reg_l in nbm.
                     apply eq_sym in nbm. subst. clear ZMM1 Y H2.
                     destruct (source_SomeE _ _ _ _ _ Heqd0) as 
                         [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                     clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                     unfold removeUndefs in JJ2'.
                     remember (j12 b2) as r.
                     destruct r; apply eq_sym in Heqr.
                          destruct p. inv JJ2'. 
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                     remember (j' b2) as rr.
                     destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                     destruct p. 
                     destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H4).
                       destruct H2 as [? [? ?]]. clear -ZM2 H7.
                                          exfalso. omega.
                     destruct H2 as [MM2 [ZMM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]]. subst.
                     apply Zplus_reg_l in nbm. apply eq_sym in nbm.  subst. 
                     clear ZMM2 Y2 H3.

                     eapply MInj13'. 
                        apply NEQ. 
                        assumption.
                        assumption. 
                        rewrite Zplus_0_r; trivial.
                        rewrite Zplus_0_r; trivial.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3. 
              (*source j12' ofs1 = Some*)
                  unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2. 
   (*mi_representable*) intros. rename b into b2.
       destruct (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H).
       (*first case*)
         destruct H1 as [j23b2 Val2].
         destruct (ACCESS b2) as [Valid _]. 
admit.  (* weak_valid_pointer...
         specialize (Valid Val2 k (Int.unsigned ofs)).
         rewrite j23b2 in Valid.
         remember (source  j12 m1 b2 (Int.unsigned ofs)) as d.
         destruct d. 
         (*source  j12 m1 b2 (Int.unsigned ofs) = Some p0*)
            destruct p0.
            rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0. clear Valid.
            destruct (source_SomeE _ _ _ _ _ Heqd) 
                as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
            clear Heqd. subst. apply eq_sym in PP. inv PP.
            assert (Val1 := Mem.perm_valid_block _ _ _ _ _ PERM).
            assert (Perm2: Mem.perm m2 b2 (z+delta1) Max Nonempty).
                eapply MInj12. apply J12. apply PERM.
             eapply MInj23. apply j23b2. 
             rewrite Off1. apply Perm2.
         (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
            rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0. clear Valid.
            eapply MInj23. apply j23b2. apply H0. *)
       (*second case*)
admit. (* weak_valid_pointer...
         destruct H1 as [M [ZM [B2 [J' X]]]]. subst.
         destruct (ACCESS (Mem.nextblock m2 + M)) as [_ Invalid].
         assert (Inval2: ~ Mem.valid_block m2 (Mem.nextblock m2 + M)).
                clear - ZM. unfold Mem.valid_block. omega.
         assert (MX: Mem.perm m2' (Mem.nextblock m2 + M) 
                  (Int.unsigned ofs) Max Nonempty).
                eapply Mem.perm_max. eapply Mem.perm_implies.
                    apply H0. apply perm_any_N.
         assert (InvMax:= Invalid Inval2 Max  (Int.unsigned ofs)).
         specialize (Invalid Inval2 k (Int.unsigned ofs)).
         remember (source (removeUndefs j12 j' prej12') m1'
                        (Mem.nextblock m2 + M) (Int.unsigned ofs)) as d.
         destruct d.
         (*source (removeUndefs j12 j' prej12') ... = Some p0*) 
             destruct p0.
             rewrite (perm_subst _ _ _ _ _ _ _ Invalid) in *. clear Invalid.
             rewrite (perm_subst _ _ _ _ _ _ _ InvMax) in *. clear InvMax.
             destruct (source_SomeE _ _ _ _ _ Heqd) 
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             remember (j12 b) as r.
             destruct r; apply eq_sym in Heqr.
             (*case j12 = Some p0*)
               destruct p0. inv J12. exfalso. 
               apply Inval2. apply (VBj12_2 _ _ _ Heqr).
             (*case j12 = None*)
               remember (j' b) as rr.
               destruct rr; inv J12. apply eq_sym in Heqrr.
               destruct p0.  
               destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _ 
                     HeqMKI VB12 VBj23_1 _ _ _ H2).
               (*first case*)
                  destruct H1 as [? [? ?]]. clear -ZM H4. exfalso. omega.
               (*second case*)
                  destruct H1 as [MM1 [ZMM1 [BB1 [nbm [zz [XX Y]]]]]]. subst. 
                  rewrite Zplus_0_r in *. subst.
                  apply Zplus_reg_l in nbm. apply eq_sym in nbm. subst.  
                  clear ZMM1 Y.
                  rewrite Heqrr in J'. inv J'.
                  eapply (Mem.mi_representable _ _ _ MInj13'
                             (Mem.nextblock m1 + M) ).
                      apply Heqrr.
                      apply H0.
         (*source (removeUndefs j12 j' prej12') ... = None*) 
            unfold Mem.perm in MX. rewrite InvMax in MX. inv MX. *)
    (*mi_unmappedeserved*)
       intros b2 J2' ofs.
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
           specialize (H0 Res ofs). simpl in *.
           unfold Mem.reserved. 
           rewrite (perm_subst _ _ _ _ _ _ _ H0). clear H0.
           eapply MInj23.
           remember (j23 b2) as d.
               destruct d; apply eq_sym in Heqd.
                 destruct p. rewrite (inc23 _ _ _ Heqd) in J2'.
                 inv J2'.
               trivial.
        (*case ~ valid_block m2 b2*)
          specialize (H0 Res ofs); simpl in *.   
          remember (sourceP
             (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
             (noperm_dec m1' Res Nonempty) (removeUndefs j12 j' prej12') m1' b2
             ofs) as src.
          destruct src.
            destruct (sourceP_SomeE _ _ _ _ _ _ _ Heqsrc)
                    as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc. subst.
            remember (j12 bb1) as d.
            destruct d; apply eq_sym in Heqd. 
              destruct p. rewrite (inc12 _ _ _ Heqd) in JJ. inv JJ.
              apply VBj12_2 in Heqd. contradiction.
            remember (j' bb1) as o.
            destruct o; apply eq_sym in Heqo. 
              destruct p. rewrite IDextensional in Heqo.
              unfold compose_meminj in Heqo.
              rewrite JJ in Heqo. rewrite J2' in Heqo.
              inv Heqo.
            unfold removeUndefs in JJ.
              rewrite Heqd in JJ.
              rewrite Heqo in JJ. 
              inv JJ.   
          specialize (sourceP_NoneE _ _ _ _ _ _ Heqsrc). 
            clear Heqsrc; intros SRC.
            destruct (zlt b2 (Mem.nextblock m2')).
              exists Nonempty. unfold Mem.perm.
              rewrite H0. constructor.
            admit. (*TODO - maybe add valid-block condition in inject'?*)
    (*reserved*) intros b3 ofs.
      split. intros R3 b2 delta3 J2'. unfold Mem.reserved in *.
         destruct R3 as [p Hp].
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
           specialize (H0 Res (ofs-delta3)). simpl in *.
           rewrite (perm_subst _ _ _ _ _ _ _ H0). clear H0.
           assert (J: j23 b2 = Some(b3, delta3)).
             remember (j23 b2) as d.
               destruct d; apply eq_sym in Heqd.
                 destruct p0. rewrite (inc23 _ _ _ Heqd) in J2'.
                 assumption.
               destruct (sep23 _ _ _ Heqd J2').
                 contradiction.
           apply (Fwd3 _ (VBj23_2 _ _ _ J)) in Hp.
           destruct (Mem.mi_reserved _ _ _ MInj23 b3 ofs)
              as [X _].
           destruct X with (b1:=b2)(delta:=delta3).
              exists p. apply Hp.
              apply J.
           exists x. apply H0. 
        (*case ~ valid_block m2 b2*)
          specialize (H0 Res (ofs-delta3)); simpl in *.   
          remember (sourceP
             (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
             (noperm_dec m1' Res Nonempty) (removeUndefs j12 j' prej12') m1' b2
             (ofs-delta3)) as src.
          destruct src.
            destruct (sourceP_SomeE _ _ _ _ _ _ _ Heqsrc)
                    as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc. subst.
            destruct (Mem.mi_reserved _ _ _ MInj13' b3 ofs) as [X _].
            destruct X with (b1:=bb1)(delta:=dd1+delta3).
              exists p. apply Hp.
              rewrite IDextensional. unfold compose_meminj.
                rewrite JJ. rewrite J2'. trivial.
            exfalso. apply PERM; clear PERM X.
            assert (ofs - (dd1 + delta3) = ofs11) by omega.
            rewrite H2 in H1. 
            eapply Mem.perm_implies. apply H1. apply perm_any_N.
          specialize (sourceP_NoneE _ _ _ _ _ _ Heqsrc). 
            clear Heqsrc; intros SRC.
            destruct (zlt b2 (Mem.nextblock m2')).
              exists Nonempty. unfold Mem.perm.
              rewrite H0. constructor.
            destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ 
                HeqMKI _ _ _ J2').
              apply VBj23_1 in H1. contradiction.
            destruct H1 as [m [Hm [MM J']]]. subst.  
            admit. (*TODO - maybe add valid-block condition in inject'?*)
    (*reverse direction*)
      intros.
      eapply MInj13'. intros.
      rewrite IDextensional in H0.
      destruct (compose_meminjD_Some _ _ _ _ _ H0)
        as [b2 [delta2 [delta3 [J1' [J2' D]]]]].
      subst; clear H0.
      specialize (H _ _ J2').
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
           specialize (H1 Res (ofs-delta3)). simpl in *.
           destruct H as [p Hp]. 
           rewrite (perm_subst _ _ _ _ _ _ _ H1) in Hp. clear H1.
           assert (J: j12 b1 = Some(b2, delta2)).
             remember (j12 b1) as d.
               destruct d; apply eq_sym in Heqd.
                 destruct p0. 
                 rewrite (inc12 _ _ _ Heqd) in J1'.
                 trivial.
               destruct (sep12 _ _ _ Heqd J1').
                 contradiction.
           destruct (Mem.mi_reserved _ _ _ MInj12 b2 (ofs - delta3)) as [X _].
           destruct X with (b1:=b1)(delta:=delta2).
              exists p. apply Hp.
              apply J.
           exists x.
           eapply (Fwd1 _ (VBj12_1 _ _ _ J)).
           assert (ofs - (delta2 + delta3) = ofs - delta3 - delta2) as -> by omega.
           assumption.
        (*case ~ valid_block m2 b2*)
          specialize (H1 Res (ofs-delta3)); simpl in *.   
          remember (sourceP
             (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
             (noperm_dec m1' Res Nonempty) (removeUndefs j12 j' prej12') m1' b2
             (ofs-delta3)) as src.
          destruct src.
            destruct (sourceP_SomeE _ _ _ _ _ _ _ Heqsrc)
                    as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc. subst.
            unfold Mem.reserved in H. destruct H as [p Hp].
            unfold Mem.perm in Hp. rewrite H1 in Hp.
            contradiction.
          specialize (sourceP_NoneE _ _ _ _ _ _ Heqsrc). 
            clear Heqsrc; intros SRC.
            exists Nonempty.
            assert (VB: 0 <= b1 < Mem.nextblock m1').
               apply VALIDBLOCK.
               eapply VBj'.
               rewrite IDextensional. 
               unfold compose_meminj.
               rewrite J1'. rewrite J2'. reflexivity.
            specialize (SRC _ _ VB J1').
            apply Classical_Prop.NNPP in SRC.
            assert (ofs - (delta2 + delta3) = ofs - delta3 - delta2) as -> by omega.
            assumption.
split. trivial.
split; trivial.           
split; trivial.           
split; trivial.           
split; trivial.           
split; trivial.            
intros.  
  (*mem_wd m2'*)
   apply mem_wdI. intros.
   destruct (CONT b) as [ValidCONT InvalidCONT].
   apply (valid_split _ _ _ _ (ACCESS b)); intros; clear ACCESS.
   (*valid*)
      clear InvalidCONT.
      specialize (H1 Cur ofs). specialize (ValidCONT H0 ofs).
      remember (source j12 m1 b ofs) as d.
      destruct d. 
      (*source  j12 m1 b ofs = Some p0*) 
          destruct p. 
          destruct (source_SomeE _ _ _ _ _ Heqd) 
             as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
          subst. apply eq_sym in PP. inv PP.
          remember (j23' b) as q.
          destruct q; apply eq_sym in Heqq.
          (*j23' b = Some p*)
             destruct p. rewrite ValidCONT. clear ValidCONT.
             (*The following 19 lines are essentially repated below,
               in the case INVALID - extract as ausiliary lemma?*)
             remember (ZMap.get z (ZMap.get b0 (Mem.mem_contents m1'))) as v.
             destruct v; simpl. constructor. constructor. unfold removeUndefs.
             remember (j12 b2) as d.
             destruct d; apply eq_sym in Heqd.
                destruct p. econstructor. eapply flatinj_I.
                    eapply Fwd2. apply (VBj12_2 _ _ _ Heqd).
                    rewrite Int.add_zero. trivial.             
             remember (j' b2) as r.
             destruct r; apply eq_sym in Heqr.
                destruct p. rewrite IDextensional in Heqr. 
                destruct (compose_meminjD_Some _ _ _ _ _ Heqr)
                    as [bb1 [off1 [off [A [B C]]]]]. subst. clear Heqr.
                 unfold removeUndefs in A.  
                 rewrite Heqd in A.
                 remember (j' b2) as u. 
                 destruct u; inv A. 
                   destruct p. rewrite H3.  econstructor. 
                   eapply flatinj_I. eapply Mem.valid_block_inject_1. 
                      apply B. apply Inj23'. rewrite Int.add_zero. trivial.
                    constructor.
          (*j23' b = None*) rewrite ValidCONT. clear ValidCONT.
             assert (J23: j23 b = None). 
                remember (j23 b) as dd.
                destruct dd; apply eq_sym in Heqdd. 
                   destruct p. rewrite (inc23 _ _ _ Heqdd) in Heqq.
                                inv Heqq. trivial.
                   eapply memval_inject_incr. apply mem_wd_E in WD2. 
             rewrite J23 in H1. 
                 rewrite (perm_subst _ _ _ _ _ _ _ H1) in R. clear H1.
                 assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ WD2)
                           b (z+dd1)).
                 rewrite (flatinj_I _ _ H0) in MV.
                 specialize (MV _ _ (eq_refl _)).
                 rewrite Zplus_0_r in MV. apply (MV R).
                 intros bb; intros. apply flatinj_E in H2. 
                   destruct H2 as [? [? ?]]; subst. 
                   apply flatinj_I. apply Fwd2. apply H4.
      (*source  j12 m1 b ofs = None*) 
          assert (ZMap.get b (Mem.mem_access m2') ofs Cur =
                      ZMap.get b (Mem.mem_access m2) ofs Cur).
             remember (j23 b) as e.
             destruct e; trivial. destruct p; trivial.
          rewrite (perm_subst _ _ _ _ _ _ _ H2) in R. clear H1 H2.
          rewrite ValidCONT. clear ValidCONT.
          assert (SRC:= source_NoneE _ _ _ _ Heqd). clear Heqd.
          eapply memval_inject_incr. apply mem_wd_E in WD2. 
            assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ WD2) b ofs). 
            rewrite (flatinj_I _ _ H0) in MV. 
            specialize (MV _ _ (eq_refl _) R). 
            rewrite Zplus_0_r in MV. apply MV.
         intros bb; intros. apply flatinj_E in H1. 
             destruct H1 as [? [? ?]]; subst. apply flatinj_I. 
                 apply Fwd2. apply H3.
   (*valid*)
       clear ValidCONT.
       specialize (H1 Cur ofs). specialize (InvalidCONT H0 ofs).
       remember (source (removeUndefs j12 j' prej12') m1' b ofs) as d.
       destruct d. 
       (*source (removeUndefs j12 j' prej12') m1' b ofs  = Some p*)
           destruct p. 
           destruct (source_SomeE _ _ _ _ _ Heqd)
               as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
           subst. apply eq_sym in PP. inv PP.
           rewrite (perm_subst _ _ _ _ _ _ _ H1) in R. clear H1.
           rewrite InvalidCONT. clear InvalidCONT.
            (*HERE's the repetition of those 19 lines, for b1 instead of b2*)
             remember (ZMap.get z (ZMap.get b0 (Mem.mem_contents m1'))) as v.
             destruct v; simpl. constructor. constructor. unfold removeUndefs.
             remember (j12 b1) as d.
             destruct d; apply eq_sym in Heqd.
                destruct p. econstructor. eapply flatinj_I.
                    eapply Fwd2. apply (VBj12_2 _ _ _ Heqd).
                    rewrite Int.add_zero. trivial.
             remember (j' b1) as r.
             destruct r; apply eq_sym in Heqr.
                destruct p. rewrite IDextensional in Heqr. 
                destruct (compose_meminjD_Some _ _ _ _ _ Heqr)
                    as [bb1 [off1 [off [A [B C]]]]]. subst. clear Heqr.
                 unfold removeUndefs in A.  
                 rewrite Heqd in A.
                 remember (j' b1) as u. 
                 destruct u; inv A. 
                   destruct p. rewrite H2.  econstructor. 
                   eapply flatinj_I. eapply Mem.valid_block_inject_1. 
                      apply B. apply Inj23'. rewrite Int.add_zero. trivial.
                    constructor.

       (*source (removeUndefs j12 j' prej12') m1' b ofs = None*)
            unfold Mem.perm in R. rewrite H1 in R. inv R.
Qed.

Parameter mkAccessMap_II_exists: forall (j12 j23 j12':meminj) 
                                 (m1 m1' m2: mem) (NB:Z),
                           ZMap.t (Z -> perm_kind -> option permission).
Axiom mkAccessMap_II_ok: forall j12 j23 j12' m1 m1' m2 NB, 
      AccessMap_II_Property j12 j23 j12' m1 m1' m2 NB
                   (mkAccessMap_II_exists  j12 j23 j12' m1 m1' m2 NB).

Parameter mkContentsMap_II_exists: forall ( j12 j12' j23':meminj)
             (m1 m1' m2:Mem.mem), ZMap.t (ZMap.t memval).
Axiom mkContentsMap_II_ok: forall j12 j12' j23' m1 m1' m2, 
      Content_II_Property  j12 j12' j23' m1 m1' m2
                 (mkContentsMap_II_exists  j12 j12' j23' m1 m1' m2).

Definition mkII m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1' 
                   (Fwd1: mem_forward m1 m1') j23 m3
                   (MInj23 : Mem.inject j23 m2 m3) m3'
                   (Fwd3: mem_forward m3 m3')
                   j' (MInj13': Mem.inject j' m1' m3')
                   (InjIncr: inject_incr (compose_meminj j12 j23) j')
                   (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                   (Unch11': my_mem_unchanged_on
                             (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                   (Unch33': my_mem_unchanged_on 
                        (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
                   (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2)
                   (WD3: mem_wd m3) (WD3' : mem_wd m3')

                   prej12' j23' n1' n2'
                   (HeqMKI: mkInjections m1 m1' m2 j12 j23 j' = 
                           (prej12', j23', n1', n2'))
                   j12' (Hj12': j12'= removeUndefs j12 j' prej12')
                   (AL12: inject_aligned j12) (AL23: inject_aligned j23)
                   (AL13': inject_aligned j')
                 : Mem.mem'.
assert (VBj12_1: forall (b1 b2 : block) (ofs2 : Z),
               j12 b1 = Some (b2, ofs2) -> Mem.valid_block m1 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12).
  assert (VBj12_2: forall (b1 b2 : block) (ofs2 : Z),
               j12 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  assert (VBj23_1: forall (b1 b2 : block) (ofs2 : Z),
               j23 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23).
  assert (VBj23_2: forall (b1 b2 : block) (ofs2 : Z),
               j23 b1 = Some (b2, ofs2) -> Mem.valid_block m3 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
  assert (VB12: forall b3 b4 ofs3, j12 b3 = Some (b4, ofs3) -> 
              b3 < Mem.nextblock m1 /\ b4 < Mem.nextblock m2).
      intros. split. apply (VBj12_1 _ _ _ H). apply (VBj12_2 _ _ _ H).
eapply Mem.mkmem with  (nextblock:=n2')
                      (mem_access:=mkAccessMap_II_exists j12 j23 j12' m1 m1' m2 n2').
(*1/5*)
  apply (mkContentsMap_II_exists  j12 j12' j23' m1 m1' m2).
(*2/5*)
  destruct (mkInjectionsN_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [_ A]; subst.
         assert ( Mem.nextblock m2 > 0). apply m2.
         omega.
(*3/5: access_max*)
    intros.
    specialize (mkAccessMap_II_ok j12 j23 j12' m1 m1' m2 n2' b). intros.
    apply (valid_split _ _ _ _ H); clear H; intros.
    (*valid m2 b*) 
           assert (CUR:= H0 Cur ofs).
           specialize (H0 Max ofs).
           remember (j23 b) as d.
           destruct d.
              destruct p.
              remember (source j12 m1 b ofs) as e.
              destruct e.
                 destruct p. rewrite H0. rewrite CUR. apply m1'.
              rewrite H0. rewrite CUR. apply m2.
           rewrite H0. rewrite CUR. apply m2.
    (*invalid m2 b*)
           assert (CUR:= H0 Cur ofs).
           specialize (H0 Max ofs).
           remember (source j12' m1' b ofs) as d.
           destruct d.
               destruct p. rewrite H0. rewrite CUR. apply m1'.
            rewrite H0. rewrite CUR. constructor.
(*4/5: nextblock_noaccess*)
  intros. 
  specialize (mkAccessMap_II_ok j12 j23 j12' m1 m1' m2 n2' b). intros AM.
  apply (valid_split _ _ _ _ AM); clear AM; intros.
  (*valid m2 b*) 
      destruct (mkInjectionsN_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [_ A]; subst. 
      unfold Mem.valid_block in H0.
      exfalso. clear - H H0. omega.
  (*invalid m2 b*)
    specialize (H1 k ofs).
    case_eq (isMaxCur k); intros iMC.
    (*case MaxCur*)
       assert (HH: match source j12' m1' b ofs with
            | Some (b1, ofs1) =>
                ZMap.get b (mkAccessMap_II_exists j12 j23 j12' m1 m1' m2 n2') ofs k =
                ZMap.get b1 (Mem.mem_access m1') ofs1 k
            | None =>
                ZMap.get b (mkAccessMap_II_exists j12 j23 j12' m1 m1' m2 n2') ofs k =
                None
            end).
          destruct k; inv iMC; trivial.
      clear H1. 
      remember (source j12' m1' b ofs) as d.
      destruct d.
         destruct p. rewrite HH. clear HH. 
         destruct (source_SomeE _ _ _ _ _ Heqd)
             as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
         subst. apply eq_sym in PP. inv PP.
         exfalso. unfold removeUndefs in JJ.
         remember (j12 b0) as d.
         destruct d. 
             destruct p. inv JJ. apply eq_sym in Heqd. 
             apply H0. eapply Mem.valid_block_inject_2.
                     apply Heqd. apply MInj12.
         remember (j' b0) as d.
         destruct d.
           destruct p.
           destruct (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _
                 HeqMKI VB12 VBj23_1 _ _ _ JJ).
               destruct H1 as [? [? ?]]. apply H0. apply (VBj12_2 _ _ _ H1).
               destruct H1 as [M [ZM [B0 [B2 [D [A B]]]]]]. subst. 
                  clear - H B. omega.
         inv JJ.
       apply HH.
     (*case Res*) destruct k; inv iMC.
      remember (sourceP
         (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
         (noperm_dec m1' Res Nonempty) (removeUndefs j12 j' prej12') m1' b
         ofs) as d.
      destruct d.
         destruct p. apply H1.
      intros. clear Heqd.
        rewrite (zlt_false _ _ _ _ _ H) in H1. assumption.
(*5/5: MaxRes
  intros.
  specialize (mkAccessMap_II_ok j12 j23 j12' m1 m1' m2 n2' b). intros AM.
  apply (valid_split _ _ _ _ AM); clear AM; intros.
  (*valid m2 b*) 
      assert (HMax:= H2 Max ofs).
      specialize (H2 Res ofs).
      simpl in *.
      rewrite H2. clear H2.
      remember (j23 b) as d.
      destruct d.
        destruct p.
        remember (source j12 m1 b ofs) as src.
        destruct src.
          destruct p. rewrite HMax in H0. clear HMax.
          destruct (source_SomeE _ _ _ _ _ Heqsrc)
              as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqsrc.
          subst. apply eq_sym in PP. inv PP.
             admit.TODO code not needed
        rewrite HMax in H0.
          apply Mem.nomax_reserved in H0. apply H0.
        apply VALIDBLOCK. apply H1.
      rewrite HMax in H0.
        apply Mem.nomax_reserved in H0. apply H0.
        apply VALIDBLOCK. apply H1.
  (*invalid m2 b*)
      assert (HMax:= H2 Max ofs).
      specialize (H2 Res ofs).
      simpl in *.
      remember (source j12' m1' b ofs) as src.
      destruct src.
        destruct p. rewrite HMax in H0. clear HMax.
        destruct (source_SomeE _ _ _ _ _ Heqsrc)
              as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqsrc.
          subst. apply eq_sym in PP. inv PP.
          exfalso.
          unfold Mem.perm in PERM. rewrite H0 in PERM.
          simpl in PERM. trivial.
        specialize (source_NoneE _ _ _ _ Heqsrc). intros.  
        remember (sourceP
         (fun (b : block) (ofs : Z) => ~ Mem.perm m1' b ofs Res Nonempty)
         (noperm_dec m1' Res Nonempty) j12' m1' b ofs) as d.
        destruct d.
          destruct p.           
          destruct (sourceP_SomeE _ _ _ _ _ _ _ Heqd)
              as [bbb1 [ddd1 [oofs11 [PPP [VBB [ JJJ [PPERM Off2]]]]]]]. clear Heqd.
          subst. inv PPP. rewrite H2. clear HMax.
          unfold removeUndefs in JJJ.
          remember (j12 bbb1).
          destruct o.
             destruct p. inv JJJ.
             exfalso. apply H1. apply eq_sym in Heqo.
              apply (VBj12_2 _ _ _ Heqo).
          remember (j' bbb1).
          destruct o; apply eq_sym in Heqo.
            destruct p.  admit. code not needed
        inv JJJ.
    remember (zlt b n2').
    destruct s. rewrite H2. exists Nonempty; trivial.
    exfalso. clear - H g. omega.*)
Defined.

Lemma my_interpolate_II: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
              (Fwd1: mem_forward m1 m1') j23 m3
              (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
              j' (MInj13': Mem.inject j' m1' m3')
              (InjIncr: inject_incr (compose_meminj j12 j23) j')
              (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
              (Unch11': my_mem_unchanged_on
                          (loc_unmapped (compose_meminj j12 j23)) m1 m1')
              (Unch33': my_mem_unchanged_on
                     (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
              (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2)
              (WD3: mem_wd m3) (WD3' : mem_wd m3'),
         exists m2', exists j12', exists j23', 
                j'=compose_meminj j12' j23' /\
                inject_incr j12 j12' /\ inject_incr j23 j23' /\
                Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\
                Mem.inject j23' m2' m3' /\
                my_mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                inject_separated j12 j12' m1 m2 /\
                inject_separated j23 j23' m2 m3 /\
                my_mem_unchanged_on (loc_unmapped j23) m2 m2' /\ 
                my_mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                (mem_wd m2 -> mem_wd m2').                             
Proof. intros.
  remember (mkInjections m1 m1' m2 j12 j23 j') as MKI.
  apply eq_sym in HeqMKI. destruct MKI as [[[j12' j23'] n1'] n2'].
  assert (VBj12_1: forall (b1 b2 : block) (ofs2 : Z),
                j12 b1 = Some (b2, ofs2) -> Mem.valid_block m1 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12).
  assert (VBj12_2: forall (b1 b2 : block) (ofs2 : Z),
                j12 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  assert (VBj23: forall (b1 b2 : block) (ofs2 : Z),
                j23 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23).
  assert (inc12:= mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1).
  assert (sep12:= mkInjections_1_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI).
  assert (inc23:= mkInjections_2_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23).
  assert (sep23:= mkInjections_2_injsep _ _ _ _ _ _ _ _ _ _ 
                   HeqMKI VBj12_1 _ InjSep).
  assert (NB1: Mem.nextblock m1' - Mem.nextblock m1 >= 0).
     assert (B: forall b, b <= Mem.nextblock m1 -> b <= Mem.nextblock m1'). 
         intros. destruct (Fwd1 (b -1)).  unfold Mem.valid_block. omega. 
                   unfold Mem.valid_block in H0. omega. 
     clear -B. specialize (B (Mem.nextblock m1)). omega. 
  destruct (mkInjectionsN_0  _ _ _ _ _ _ _ _ _ _ HeqMKI) as [N1 _].
       rewrite (nat_of_Z_eq _ NB1) in N1. 
       rewrite Zplus_minus in N1. subst.
  assert (VBj': forall b1 b3 ofs3, j' b1 = Some (b3, ofs3) ->
             b1 < Mem.nextblock m1').
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj13').
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _ 
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').
  assert (AL12:= inj_implies_inject_aligned _ _ _  MInj12). 
  assert (AL23:= inj_implies_inject_aligned _ _ _  MInj23). 
  assert (AL13':= inj_implies_inject_aligned _ _ _  MInj13').
  assert (XX: Mem.nextblock  
                    (mkII m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33'
                             WD1 WD1' WD2 WD3 WD3'  _ _ _ _
                             HeqMKI _ (eq_refl _) AL12 AL23 AL13') 
                  = n2').
           reflexivity.
   assert (YY:Content_II_Property j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
                  (Mem.mem_contents
                       (mkII m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33'
                             WD1 WD1' WD2 WD3 WD3' _ _ _ _ 
                             HeqMKI _ (eq_refl _) AL12 AL23 AL13') )).
                     simpl. apply mkContentsMap_II_ok.
  assert (ZZ: AccessMap_II_Property j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
               n2' (Mem.mem_access
                       (mkII m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33'
                             WD1 WD1' WD2 WD3 WD3' _ _ _ _ 
                             HeqMKI _ (eq_refl _) AL12 AL23 AL13') )).
                     simpl. apply mkAccessMap_II_ok.
  destruct (II_ok m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33'
                             WD1 WD1' WD2 WD3 WD3' _ _ _ _ 
                             HeqMKI _ (eq_refl _) _ XX YY ZZ AL12 AL23 AL13')
       as [A [B [C [D [E [F [G [H [I [J [K [L [M N]]]]]]]]]]]]].
  eexists.  exists (removeUndefs j12 j' j12') . exists j23'.
  split; trivial.
  split; trivial.
  split; trivial.
  split; simpl. eassumption.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
Qed.

Lemma interpolate_II: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                  (Fwd1: mem_forward m1 m1') j23 m3
                  (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                  j' (MInj13': Mem.inject j' m1' m3')
                  (InjIncr: inject_incr (compose_meminj j12 j23) j')
                  (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                  (Unch11': mem_unchanged_on 
                            (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                  (Unch33': mem_unchanged_on
                        (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
                  (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2)
                  (WD3: mem_wd m3) (WD3' : mem_wd m3'),
         exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                   inject_incr j12 j12' /\ inject_incr j23 j23' /\
                   Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ 
                   Mem.inject j23' m2' m3' /\
                   mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                   inject_separated j12 j12' m1 m2 /\ 
                   inject_separated j23 j23' m2 m3 /\
                   mem_unchanged_on (loc_unmapped j23) m2 m2' /\ 
                   mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                   (mem_wd m2 -> mem_wd m2').                             
Proof. intros.
  rewrite <- unchAx in Unch11', Unch33'.
  destruct (my_interpolate_II m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33'
                             WD1 WD1' WD2 WD3 WD3') 
       as [m2' [j12' [j23' [A [B [C [D [E [F [G [H [I [J [K L]]]]]]]]]]]]]].
  exists m2'. exists j12'. exists j23'.
  rewrite unchAx in G, J, K. repeat (split; trivial).
Qed.
