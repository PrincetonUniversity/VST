Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Axioms.

Require Import FiniteMaps.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolation_defs.

Fixpoint mkInjectionsN (N:nat)(n1 n2:block)(j k l: meminj)
                     :  meminj * meminj * block * block :=
   match N with O => (j,k,n1,n2)
    | S M => mkInjectionsN M (Pos.succ n1) (Pos.succ n2)
                             (fun b => if eq_block b n1
                                       then Some (n2,0)
                                       else j b)
                             (fun b => if eq_block b n2 then l n1 else k b)
                             l
   end.

Lemma mkInjectionsN_0: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')),
    match N with O => (n1 = n1' /\ n2 = n2' /\ j' = j /\ k' = k)
      | S n => (n1 + (Pos.of_nat N) = n1')%positive /\
               (n2 + (Pos.of_nat N) = n2')%positive
    end.
Proof. intros N.
  induction N; simpl; intros. inv HI. repeat (split; trivial).
  specialize (IHN _ _ _ _ _ _ _ _ _ HI). clear HI.
  destruct N. destruct IHN as [? [? [? ?]]].
    subst. repeat rewrite Pplus_one_succ_r in *. split; trivial.
  repeat rewrite pos_succ_plus_assoc in IHN. assumption.
Qed.

Lemma mkInjectionsN_1: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')),
    forall b1 b2 ofs2 (Jb: j b1 = Some(b2,ofs2)),
    (b1 < n1)%positive -> j' b1 = Some (b2,ofs2).
Proof. intros N.
  induction N; simpl; intros.
     inv HI. apply Jb.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI). clear HI.
        apply (IHN b1 b2 ofs2). clear IHN.
        remember (eq_block b1 n1) as d.
        destruct d; clear Heqd. exfalso. subst. clear -H. xomega.
        assumption.
     xomega.
Qed.

Lemma mkInjectionsN_2: forall N n1 n2 j k l j' k' n1' n2'
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')),
    forall b2 b3 ofs3 (Jb: k b2 = Some(b3,ofs3)),
    (b2 < n2)%positive -> k' b2 = Some (b3,ofs3).
Proof. intros N.
  induction N; simpl; intros.
     inv HI. apply Jb.
     specialize (IHN _ _ _ _ _ _ _ _ _ HI). clear HI.
        apply (IHN b2 b3 ofs3). clear IHN.
        remember (eq_block b2 n2) as d.
        destruct d; clear Heqd. exfalso. subst. clear -H. xomega.
        assumption.
      xomega.
Qed.

Lemma mkInjectionsN_3: forall N n1 n2 j k l j' k' n1' n2'
        (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
        b1 b2 ofs2,
        j' b1 = Some(b2,ofs2) ->
     (j b1 = Some (b2,ofs2)) \/
     (b1 = n1 /\ b2 = n2 /\ ofs2 = 0) \/
     (exists m, (b1 = n1 + m /\ b2=n2 + m)%positive /\ ofs2=0).
Proof.
  intros N.
  induction N; simpl; intros. inv HI. left; trivial.
  destruct N; simpl in *. inv HI.
      remember (eq_block b1 n1) as d.
      destruct d; clear Heqd; subst.
        inv H. right. left. auto.
      left; trivial.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI _ _ _ H).  clear HI H.
  destruct IHN.
      remember (eq_block b1 n1) as d.
      destruct d; clear Heqd.
        inv H. right. left. auto.
      left; trivial.
 destruct H as [[? [? ?]] | H].
    subst. right. right. exists 1%positive.
      do 2 rewrite Pplus_one_succ_r. auto.
 destruct H as [m [[? ?] ?]]. subst. right. right.
   exists (Pos.succ m).
    do 2 rewrite pos_succ_plus_assoc.
    repeat split; trivial.
Qed.

Lemma mkInjectionsN_3V: forall N n1 n2 j k l j' k' n1' n2'
     (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
     (HJ: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> (b1 < n1 /\ b2 < n2)%positive)
     (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> (b2 < n2)%positive)
     b1 b2 ofs2,
     j' b1 = Some(b2,ofs2) ->
          (j b1 = Some (b2,ofs2) /\ (b1 < n1 /\ b2 < n2)%positive) \/
          (b1 = n1 /\ b2=n2 /\ ofs2=0 /\ (b1 < n1' /\ b2<n2')%positive) \/
          (exists m, (b1 = n1 + m)%positive /\ (b2=n2 + m)%positive /\
                     ofs2=0 /\ (b1 < n1' /\ b2<n2')%positive).
Proof. intros N.
  induction N; simpl; intros.
      inv HI. left. split; trivial. eapply HJ. apply H.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI).
  assert (HJ': forall (b1 b2 : block) (ofs2 : Z),
          (fun b : block => if eq_block b n1 then Some (n2, 0) else j b) b1 =
            Some (b2, ofs2)
          -> (b1 < Pos.succ n1 /\ b2 < Pos.succ n2)%positive).
      clear IHN. intros.
      destruct (eq_block b0 n1); subst. inv H0. xomega.
      specialize (HJ _ _ _ H0). xomega.
  assert (HK': forall (b2 b3 : block) (ofs3 : Z),
       (fun b : block => if eq_block b n2 then l n1 else k b) b2 =
           Some (b3, ofs3)
       -> (b2 < Pos.succ n2)%positive).
     clear IHN. intros.
     destruct (eq_block b0 n2); subst. xomega.
     specialize (HK _ _ _ H0). xomega.
  specialize (IHN HJ' HK' _ _ _ H).
destruct N.
  simpl in *. inv HI.
  destruct (eq_block b1 n1).
    inv H. right; left. repeat (split; trivial); apply Plt_succ.
  left. split. assumption.
    apply (HJ _ _ _ H).

apply mkInjectionsN_0 in HI.
  destruct IHN.
     remember (eq_block b1 n1) as d.
     destruct d; clear Heqd. subst. destruct H0 as [? [? ?]]. inv H0. right.
        left.
           repeat (split; (try xomega ; try auto)).
     destruct H0 as [? [? ?]]. left. split. trivial.  apply HJ in H0. trivial.
  destruct H0 as [H0 | H0].
    destruct H0 as [? [? [? [? ?]]]]. subst.
    right. right. exists 1%positive.
      do 2 rewrite Pplus_one_succ_r.
      repeat (split; trivial; try xomega).
  destruct H0 as [m [? [? [? ?]]]]. subst. right. right.
   exists (Pos.succ m).
    do 2 rewrite pos_succ_plus_assoc.
    repeat split; try trivial; xomega.
Qed.

Lemma mkInjectionsN_4: forall N n1 n2 j k l j' k' n1' n2'
       (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2')) b2 b3 ofs3,
       k' b2 = Some(b3,ofs3) ->
                k b2 = Some (b3,ofs3) \/
                (b2 = n2 /\ l n1 = Some(b3,ofs3)) \/
                (exists m, (b2 = n2 + m)%positive /\ l ((n1+m)%positive) = Some(b3,ofs3)).
Proof. intros N.
  induction N; simpl. intros.
     inv HI. left; trivial.
  intros.
  specialize (IHN (Pos.succ n1) (Pos.succ n2) _ _ _ _ _ _ _ HI _ _ _ H).  clear HI H.
  destruct IHN.
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd.
          subst. right. left. split; trivial.
     left; trivial.
  destruct H as [H | H].
    destruct H; subst.
    right. right. exists 1%positive.
       rewrite Pplus_one_succ_r in *. split; trivial.
  destruct H as [m [? ?]]. subst.
    right. right.
      exists (Pos.succ m).
      rewrite pos_succ_plus_assoc in *.
      split; try trivial.
Qed.

Lemma mkInjectionsN_4Val: forall N n1 n2 j k l j' k' n1' n2'
       (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
       (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> (b2 < n2)%positive) b2 b3 ofs3,
       k' b2 = Some(b3,ofs3) ->
            (k b2 = Some (b3,ofs3) /\ (b2 < n2)%positive) \/
            (b2 = n2 /\ l n1 = Some(b3, ofs3) /\ (b2 < n2')%positive) \/
            (exists m, (b2 = n2 + m)%positive /\
                       l ((n1+m)%positive) = Some(b3,ofs3) /\ (b2 < n2')%positive).
Proof. intros N.
  induction N; simpl; intros.
    inv HI. left.
    specialize (HK _ _ _ H).
    split; assumption.
  assert (HK': (forall (b2 b3 : block) (ofs3 : Z),
           (fun b : block => if eq_block b n2 then l n1 else k b) b2 =
           Some (b3, ofs3) -> (b2 < Pos.succ n2)%positive)).
      clear IHN HI. intros.
      destruct (eq_block b0 n2); subst. xomega. apply HK in H0. xomega.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI HK' _ _ _ H).

  destruct N.
     simpl in *. inv HI.
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd.
          right. left. subst.
          split; trivial. split; trivial. xomega.
     specialize (HK _ _ _ H). left. split; trivial.
  apply mkInjectionsN_0 in HI; try omega.
  destruct HI; subst.
  destruct IHN as [IH | [IH | IH]].
  destruct IH.
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd. subst.
          right. left. split. trivial.
          split. assumption. xomega.
     left. specialize (HK _ _ _ H0). split; trivial.
  destruct IH as [? [? ?]]. subst.
     right. right. exists 1%positive.
     rewrite Pplus_one_succ_r in *. auto.
  destruct IH as [m [? [? ?]]]. subst.
     right. right. exists (Pos.succ m).
     rewrite pos_succ_plus_assoc in *.
     split; try trivial.
     split; try trivial.
Qed.


Lemma mkInjectionsN_5: forall N n1 n2 j k l j' k' n1' n2'
       (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
       (HJ1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> (b1 < n1)%positive)
       (HJ2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> (b2 < n2)%positive)
       (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> (b2 < n2)%positive)
       (HL: forall b1 b3 ofs3, l b1 = Some(b3,ofs3) -> (b1 < n1')%positive)
       b2 (HB: (b2 < n2')%positive),
       k' b2 = None ->
             ((b2 < n2)%positive /\ k b2 = None) \/
             (b2 = n2 /\ l n1 = None) \/
             (exists m, b2 = (n2+m)%positive /\  l ((n1+m)%positive) = None).
Proof. intros N.
  induction N; simpl; intros.
     inv HI. left. split; trivial.
  assert (HJ1': forall (b1 b2 : block) (ofs2 : Z),
          (fun b : block => if eq_block b n1 then Some (n2, 0) else j b) b1 =
          Some (b2, ofs2) -> (b1 < Pos.succ n1)%positive).
     clear IHN. intros.
     destruct (eq_block b1 n1); subst. inv H0. xomega.
     specialize (HJ1 _ _ _ H0). xomega.
  assert (HJ2': forall (b1 b2 : block) (ofs2 : Z),
          (fun b : block => if eq_block b n1 then Some (n2, 0) else j b) b1 =
           Some (b2, ofs2) -> (b2 < Pos.succ n2)%positive).
     clear IHN. intros.
     destruct (eq_block b1 n1); subst. inv H0. xomega.
     specialize (HJ2 _ _ _ H0). xomega.
  assert (HK': forall (b2 b3 : block) (ofs3 : Z),
          (fun b : block => if eq_block b n2 then l n1 else k b) b2 =
          Some (b3, ofs3) -> (b2 < Pos.succ n2)%positive).
     clear IHN. intros.
     destruct (eq_block b0 n2); subst. xomega.
     specialize (HK _ _ _ H0). xomega.
  destruct (IHN _ _ _ _ _ _ _ _ _ HI HJ1' HJ2' HK' HL _ HB H)
  as [HH | [HH | HH]].
     destruct HH.
     remember (eq_block b2 n2) as d.
     destruct d; clear Heqd.
          subst. right. left. split; trivial.
     left. split; trivial. xomega.
  destruct HH; subst.
    right. right. exists 1%positive.
    rewrite Pplus_one_succ_r in *.
    split; trivial.
  destruct HH as [m [HBB HLL]]. subst.
    right. right. exists (Pos.succ m).
     rewrite pos_succ_plus_assoc in *.
     split; try trivial.
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
    b (HB: (b < n1')%positive),
    ((n1 <= b)%positive -> j' b  <> None) /\ ((b < n1)%positive -> j' b = j b).
Proof. intros N.
  induction N; intros; simpl in *.
      inv HI. split; intros.  exfalso. xomega. trivial.
  specialize (IHN _ _ _ _ _ _ _ _ _ HI _ HB). clear HI.
     destruct IHN.
     split; intros.
     remember (plt b (Pos.succ n1)) as p.
       destruct p. rewrite (H0 p); clear H0.
       destruct (eq_block b n1); subst. discriminate.
       exfalso. clear H HB Heqp.
       destruct (Plt_succ_inv _ _ p). clear p. xomega.
       apply (n H).
      apply H. clear -n. xomega.
   rewrite H0. clear H0 H.
       destruct (eq_block b n1); subst; trivial.
         exfalso. xomega.
       xomega.
Qed.

Lemma mkInjectionsN_8: forall j' k' l n1' n2'  M N j  k n1 n2
    (HI: mkInjectionsN N n1 n2 j k l = (j',k',n1',n2'))
    (Hj: forall b, j b = None -> (b < M \/ n1' <= b)%positive) b,
    j' b = None -> (b < M \/ n1' <= b)%positive.
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
    (Hj: forall b, j b = None -> (b < n1' -> b < M)%positive) b,
    j' b = None -> (b < n1' -> b < M)%positive.
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

Definition mkInjections (m1 m1' m2:mem) (j k l: meminj)
                     :  meminj * meminj * block * block :=
  if plt (Mem.nextblock m1) (Mem.nextblock m1')
  then mkInjectionsN (Pos.to_nat (Mem.nextblock m1') - Pos.to_nat(Mem.nextblock m1))
                (Mem.nextblock m1)
                (Mem.nextblock m2) j k l
  else (j,k,Mem.nextblock m1,Mem.nextblock m2).

Lemma mkInjections_0: forall m1 m1' m2 j k l j' k' n1' n2'
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')),
     ( Pos.le (Mem.nextblock m1') (Mem.nextblock m1)  /\
        Mem.nextblock  m1 = n1' /\ Mem.nextblock  m2 = n2' /\
        j' = j /\ k' = k) \/
     (exists N, (N > 0)%nat /\
               (Mem.nextblock  m1 + (Pos.of_nat N) = n1')%positive /\
               (n1' = Mem.nextblock  m1') /\
               (Mem.nextblock  m2 + (Pos.of_nat N) = n2')%positive).
Proof. unfold  mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
   apply mkInjectionsN_0 in HI.
   remember ((Pos.to_nat (Mem.nextblock m1') - Pos.to_nat (Mem.nextblock m1))%nat).
   destruct n. left. split. xomega. trivial.
   right. exists (S n). split. omega. destruct HI.
     split. assumption.
     split; trivial. subst. rewrite Heqn. clear Heqn.
       rewrite Nat2Pos.inj_sub. do 2 rewrite Pos2Nat.id.
       apply Pplus_minus. xomega.
     specialize (Pos2Nat.is_pos (Mem.nextblock m1)). xomega.
 inv HI. left. split. xomega. repeat (split; trivial).
Qed.

Lemma mkInjections_1_injinc: forall m1 m1' m2 j k l j' k' n1' n2'
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
    (VB: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1),
    inject_incr j j'.
Proof. unfold inject_incr, mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_1 _ _ _ _ _ _ _ _ _ _ HI _ _ _ H).
    apply (VB _ _ _ H).
  inv HI. trivial.
Qed.

Lemma mkInjections_1_injsep: forall m1 m1' m2 j k l j' k' n1' n2'
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')),
    inject_separated j j' m1 m2.
Proof. unfold inject_separated, mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
     destruct (mkInjectionsN_3 _ _ _ _ _ _ _ _ _ _ HI _ _ _ H0).
       rewrite H1 in H. discriminate.
     destruct H1 as [HH | HH].
       destruct HH as [? [? ?]]; subst.
         unfold Mem.valid_block. xomega.
      destruct HH as [m [[? ?] ?]]. subst.
       clear HI H H0. unfold Mem.valid_block. xomega.
  inv HI. rewrite H in H0; discriminate.
Qed.

Lemma mkInjections_2_injinc: forall m1 m1' m2 j k l j' k' n1' n2'
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (VB: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1),
      inject_incr k k'.
Proof.
  unfold inject_incr, mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_2 _ _ _ _ _ _ _ _ _ _ HI _ _ _ H).
      apply (VB _ _ _ H).
  inv HI. trivial.
Qed.

Lemma mkInjections_2_injsep: forall m1 m1' m2 j k l j' k' n1' n2'
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (VB: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
         m3 (Sep:inject_separated (compose_meminj j k) l m1 m3),
       inject_separated k k' m2 m3.
Proof.
  unfold inject_separated, mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ H0).
      rewrite H1 in H. discriminate.
    destruct H1 as [HH | HH].
      destruct HH; subst.
        split. unfold Mem.valid_block. xomega.
        eapply (Sep (Mem.nextblock m1)).
        assert (HJ: j (Mem.nextblock m1) = None).
           remember (j (Mem.nextblock m1)) as d.
           destruct d; trivial.
           apply eq_sym in Heqd. destruct p0.
             specialize (VB _ _ _ Heqd).
             exfalso. clear - VB. unfold Mem.valid_block in VB. xomega.
        unfold compose_meminj. rewrite HJ. trivial.
        eassumption.
     destruct HH as [m [? ?]]. subst.
       split. unfold Mem.valid_block. xomega.
       eapply (Sep (Mem.nextblock m1 + m)%positive).
       assert (HJ: j ((Mem.nextblock m1 + m)%positive) = None).
           remember (j ((Mem.nextblock m1 + m)%positive)) as d.
           destruct d; trivial.
           apply eq_sym in Heqd. destruct p0.
             specialize (VB _ _ _ Heqd).
             exfalso. clear - VB. unfold Mem.valid_block in VB. xomega.
       unfold compose_meminj. rewrite HJ. trivial.
     eassumption.
  inv HI. rewrite H in H0; discriminate.
Qed.

Lemma mkInjections_3: forall m1 m1' m2 j k l j' k' n1' n2'
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        b1 b2 ofs2,
        j' b1 = Some(b2,ofs2) ->
     (j b1 = Some (b2,ofs2)) \/
     (b1 = Mem.nextblock m1 /\ b2 = Mem.nextblock m2 /\ ofs2 = 0) \/
     (exists m, (b1 = Mem.nextblock m1 + m /\ b2=Mem.nextblock m2 + m)%positive /\ ofs2=0).
Proof.
  unfold mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_3 _ _ _ _ _ _ _ _ _ _ HI); assumption.
  inv HI. left. trivial.
Qed.

Lemma mkInjections_3V: forall m1 m1' m2 j k l j' k' n1' n2'
     (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
     (HJ: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> (b1 < Mem.nextblock m1 /\ b2 < Mem.nextblock m2)%positive)
     (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> (b2 < Mem.nextblock m2)%positive)
     b1 b2 ofs2,
     j' b1 = Some(b2,ofs2) ->
          (j b1 = Some (b2,ofs2) /\ (b1 < Mem.nextblock m1 /\ b2 < Mem.nextblock m2)%positive) \/
          (b1 = Mem.nextblock m1 /\ b2=Mem.nextblock m2 /\ ofs2=0 /\ (b1 < n1' /\ b2<n2')%positive) \/
          (exists m, (b1 = Mem.nextblock m1 + m)%positive /\ (b2=Mem.nextblock m2 + m)%positive /\
                     ofs2=0 /\ (b1 < n1' /\ b2<n2')%positive).
Proof.
  unfold mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_3V _ _ _ _ _ _ _ _ _ _ HI); assumption.
  inv HI. destruct (HJ _ _ _ H).  left. repeat (split; trivial).
 Qed.

Lemma mkInjections_4: forall m1 m1' m2 j k l j' k' n1' n2'
       (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) b2 b3 ofs3,
       k' b2 = Some(b3,ofs3) ->
                k b2 = Some (b3,ofs3) \/
                (b2 = Mem.nextblock m2 /\ l (Mem.nextblock m1) = Some(b3,ofs3)) \/
                (exists m, (b2 = Mem.nextblock m2 + m)%positive /\
                            l ((Mem.nextblock m1+m)%positive) = Some(b3,ofs3)).
Proof.
  unfold mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI); assumption.
  inv HI. left. trivial.
Qed.

Lemma mkInjections_4Val: forall m1 m1' m2  j k l j' k' n1' n2'
       (HI: mkInjections m1 m1' m2  j k l = (j',k',n1',n2'))
       (HK: forall b2 b3 ofs3, k b2 = Some(b3,ofs3) -> (b2 < Mem.nextblock m2)%positive) b2 b3 ofs3,
       k' b2 = Some(b3,ofs3) ->
            (k b2 = Some (b3,ofs3) /\ (b2 < Mem.nextblock m2)%positive) \/
            (b2 = Mem.nextblock m2 /\ l (Mem.nextblock m1) = Some(b3, ofs3) /\ (b2 < n2')%positive) \/
            (exists m, (b2 = Mem.nextblock m2 + m)%positive /\
                       l ((Mem.nextblock m1+m)%positive) = Some(b3,ofs3) /\ (b2 < n2')%positive).
Proof.
  unfold mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_4Val _ _ _ _ _ _ _ _ _ _ HI); assumption.
  inv HI. left. split. trivial. apply (HK _ _ _ H).
Qed.

Lemma mkInjections_7: forall m1 m1' m2 j k l j' k' n1' n2'
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
    b (HB: (b < n1')%positive),
    ((Mem.nextblock m1 <= b)%positive -> j' b  <> None) /\
    ((b < Mem.nextblock m1)%positive -> j' b = j b).
Proof.
  unfold mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_7 _ _ _ _ _ _ _ _ _ _ HI); assumption.
  inv HI.
    split; intros. xomega. trivial.
Qed.

Lemma mkInjections_6: forall m1 m1' m2 j k l j' k' n1' n2'
    (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2')) b (J': j' b = None),
     j b = None.
Proof.
  unfold mkInjections; intros.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply (mkInjectionsN_6 _ _ _ _ _ _ _ _ _ _ HI _ J').
  inv HI. trivial.
 Qed.

Lemma mkInjections_5: forall m1 m1' m2 j k l j' k' n1' n2'
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (VBj1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
        (VBj2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m2 b2)
        (VBk2: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1)
        (VBl1: forall b1 b2 ofs2, l b1 = Some(b2,ofs2) -> (b1 < n1')%positive)
        b2 (HB: (b2 < n2')%positive),
        k' b2 = None ->
        (Mem.valid_block m2 b2 /\ k b2 = None) \/
        (b2 = Mem.nextblock m2 /\ l (Mem.nextblock m1) = None) \/
        (exists m, b2 = ((Mem.nextblock m2) + m)%positive /\
                   l ((Mem.nextblock m1+m)%positive) = None).
Proof. intros. unfold mkInjections in HI.
  destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
    apply  (mkInjectionsN_5 _ _ _ _ _ _ _ _ _ _ HI VBj1 VBj2 VBk2 VBl1 _ HB H).
  inv HI. left. split; assumption.
Qed.

Lemma J12'_no_overlap: forall m1 m2 j12
        (MInj12 : Mem.inject j12 m1 m2) m1' (Fwd1: mem_forward m1 m1') j23 m3
        (MInj23 : Mem.inject j23 m2 m3) j' j12' j23' n1' n2'
        (HeqMKI: mkInjections m1 m1' m2 j12 j23 j' = (j12', j23',n1',n2')),
      Mem.meminj_no_overlap j12' m1'.
Proof. intros. intros b b'; intros.
  assert (Val1: forall (b1 b2 : block) (ofs2 : Z),
        j12 b1 = Some (b2, ofs2) ->
        (b1 < Mem.nextblock m1 /\ b2 < Mem.nextblock m2)%positive).
    intros; split.
       eapply Mem.valid_block_inject_1. apply H4. eassumption.
       eapply Mem.valid_block_inject_2. apply H4. eassumption.
  assert (Val2: forall (b2 b3 : block) (ofs3 : Z),
        j23 b2 = Some (b3, ofs3) -> (b2 < Mem.nextblock m2)%positive).
    intros.
       eapply Mem.valid_block_inject_1. apply H4. eassumption.
unfold mkInjections in HeqMKI.
destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
  assert (ZZ:= mkInjectionsN_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI Val1 Val2 _ _ _ H0).
  assert (ZZ':= mkInjectionsN_3V  _ _ _ _ _ _ _ _ _ _
                HeqMKI Val1 Val2 _ _ _ H1).
  destruct ZZ as [HH | [HH | HH]]; destruct ZZ' as [HH' | [HH' | HH']].
  (*j - j*) destruct HH as [J [valJ1 valJ2]].
            destruct HH' as [J' [valJ1' valJ2']].
            eapply MInj12. apply H. assumption. assumption.
                eapply Fwd1. apply valJ1. assumption.
                eapply Fwd1. apply valJ1'. assumption.
  (*j - fresh0*) destruct HH as [J [valJ1 valJ2]].
                destruct HH' as [B1 [B2 [DD [leq1 leq2]]]].
                subst.
                left. intros N.  subst. clear - valJ2. xomega.
  (*j - fresh*) destruct HH as [J [valJ1 valJ2]].
                destruct HH' as [M [valJ1' [valJ2' [DD [leq1 leq2]]]]].
                subst.
                left. intros ZZ; subst. xomega.
  (*fresh0 - j*) destruct HH as [valJ1 [valJ2 [DD [leq1 leq2]]]].
                subst.
                destruct HH' as [J [valJ1' valJ2']].
                left. intros ZZ; subst. xomega.
  (*fresh0 - fresh0*) destruct HH as [B1 [B2 [DD [leq1 leq2]]]].
                destruct HH' as [B3 [B4 [DDD [leq3 leq4]]]].
                subst.
                exfalso. apply H; trivial.
  (*fresh0 - fresh*)
          destruct HH as [B1 [B2 [DD [leq1 leq2]]]].
          subst.
          destruct HH' as [M' [valJ1' [valJ2' [DD' [leq1' leq2']]]]].
          subst.
          left. clear. intros ZZ.
          apply (Pos.add_no_neutral (Mem.nextblock m2) M').
          rewrite Pos.add_comm.
          rewrite <- ZZ. trivial.
  (*fresh - j*) destruct HH as [M [valJ1 [valJ2 [DD [leq1 leq2]]]]].
                subst.
                destruct HH' as [J [valJ1' valJ2']].
                left. intros ZZ; subst. xomega.
  (*fresh - fresh0*) destruct HH as [M [valJ1 [valJ2 [DD [leq1 leq2]]]]].
                destruct HH' as [B3 [B4 [DDD [leq3 leq4]]]].
                subst.
                left. clear. intros ZZ.
                apply (Pos.add_no_neutral (Mem.nextblock m2) M).
                rewrite Pos.add_comm.
                apply ZZ.
  (*fresh - fresh*)
          destruct HH as [M [valJ1 [valJ2 [DD [leq1 leq2]]]]].
          destruct HH' as [M' [valJ1' [valJ2' [DD' [leq1' leq2']]]]].
          subst.
          left. intros ZZ.
          assert( M = M'). clear -ZZ. eapply Pos.add_reg_l; eassumption.
          subst. apply H. trivial.
inv HeqMKI.
  destruct (eq_block b' b2'); subst.
     apply Fwd1 in H2. apply Fwd1 in H3.
     apply (Mem.mi_no_overlap _ _ _ MInj12 _ _ _ _ _ _ _ _ H H0 H1 H2 H3).
     apply (Val1 _ _ _ H1). apply (Val1 _ _ _ H0).
  left; assumption.
Qed.

Lemma mkInjections_composememinj: forall m1 m1' m2 j k l j' k' n1' n2'
        (HI: mkInjections m1 m1' m2 j k l = (j',k',n1',n2'))
        (InjIncr: inject_incr (compose_meminj j k) l) m3
        (InjSep: inject_separated (compose_meminj j k) l m1 m3)
        (VBj1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
        (VBj2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m2 b2)
        (VBk2: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1)
        (VBL1': forall b1 b3 ofs3, l b1 = Some (b3, ofs3) -> (b1 < n1')%positive),
      l = compose_meminj j' k'.
Proof. intros.
extensionality b.
(*unfold mkInjections in HI.
destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
  *)remember (compose_meminj j' k' b) as z.
  destruct z; apply eq_sym in Heqz.
     destruct p. apply  compose_meminjD_Some in Heqz.
     destruct Heqz as [b1 [ofs1 [ofs [J' [K' ZZ]]]]]. subst.
     unfold mkInjections in HI.
    destruct (plt (Mem.nextblock m1) (Mem.nextblock m1')).
     destruct (mkInjectionsN_3 _ _ _ _ _ _ _ _ _ _ HI _ _ _ J').
         destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ K')
         as [HH | [HH | HH]].

            apply InjIncr. unfold compose_meminj. rewrite H.
                           rewrite HH. reflexivity.

         destruct HH as [B1 B2]. subst.
              exfalso. specialize (VBj2 _ _ _ H).
              clear - VBj2. unfold Mem.valid_block in VBj2. xomega.

         destruct HH as [m [B1 B2]]. subst.
              exfalso. specialize (VBj2 _ _ _ H).
              clear - VBj2. unfold Mem.valid_block in VBj2. xomega.

     destruct H as [H | H].

     destruct H as [B1 [B2 XX]]. subst.
         destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ K').
         exfalso. specialize (VBk2 _ _ _ H).
           clear - VBk2. unfold Mem.valid_block in VBk2. xomega.
       destruct H as [H | H].
         apply H.
         destruct H as [m [B1 B2]].
         exfalso. clear - B1.
                  apply (Pos.add_no_neutral (Mem.nextblock m2) m).
                  rewrite Pos.add_comm. rewrite <- B1. trivial.

     destruct H as [m [[B1 B2] XX]]. subst. simpl.
         destruct (mkInjectionsN_4 _ _ _ _ _ _ _ _ _ _ HI _ _ _ K').
           exfalso. specialize (VBk2 _ _ _ H).
           clear - VBk2. unfold Mem.valid_block in VBk2. xomega.
       destruct H as [H | H].
         destruct H.
         exfalso. clear - H.
                  apply (Pos.add_no_neutral (Mem.nextblock m2) m).
                  rewrite Pos.add_comm. rewrite H. trivial.
       destruct H as [mm [B1 B2]]. subst.
          assert(m = mm). clear - B1. eapply Pos.add_reg_l; eassumption.
          subst. apply B2.
     inv HI. apply InjIncr. unfold compose_meminj. rewrite J'.
          rewrite K'. trivial.
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
                     (b1 < Mem.nextblock m1 /\ b3 < Mem.nextblock m2)%positive).
             intros. split. eapply VBj1. apply H.  eapply VBj2. apply H.
      destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HI VBj VBk2 _ _ _ Heqj'b)
       as [H | [H | H]].
       (*j b = Some*) destruct H as [? [? ?]].
            assert (JKNone: compose_meminj j k b = None).
                unfold compose_meminj. rewrite H. rewrite KNone. reflexivity.
            destruct (InjSep _ _ _ JKNone Heqlb). exfalso. apply (H2 H0).
       (*second case*)
            destruct H as [B1 [B2 [? [? ?]]]]; subst.
            destruct (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HI VBj1
                        VBj2 VBk2 VBL1' _ H1 K'None)
            as [H | [H | H]].
            (*case 1 valid in m2 - contradiction*)
                destruct H as [XX _]. clear -XX.
                unfold Mem.valid_block in XX. exfalso. xomega.
            (*case 2 - l undefined - contradiction*)
                          destruct H as [_ LL].
                          rewrite LL in Heqlb. discriminate.
            (*case 2 - l undefined - contradiction*)
                          destruct H as [mm [MM LL]].
                          exfalso. clear - MM.
                            apply eq_sym in MM. rewrite Pos.add_comm in MM.
                            eapply Pos.add_no_neutral. apply MM.

       (*third case*)
            destruct H as [m [B1 [B2 [? [? ?]]]]]; subst.
            destruct (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HI VBj1
                        VBj2 VBk2 VBL1' _ H1 K'None)
            as [H | [H | H]].
            (*case 1 valid in m2 - contradiction*)
                destruct H as [XX _]. clear -XX.
                unfold Mem.valid_block in XX. exfalso. xomega.
            (*case 2 - contradiction*)
                destruct H as [MM _].
                exfalso. clear - MM.
                eapply Pos.add_no_neutral.
                rewrite Pos.add_comm. apply MM.
            (*case 3 - l undefined - contradiction*)
                destruct H as [mm [MM LL]].
                assert (mm= m). clear - MM. xomega. subst.
                rewrite LL in Heqlb. discriminate.
     (*J' b = None*)
           assert (Jb:= mkInjections_6  _ _ _ _ _ _ _ _ _ _ HI _ Heqj'b).
           assert (CMN: compose_meminj j k b = None).
                   unfold compose_meminj. rewrite Jb. trivial.
           destruct (InjSep _ _ _ CMN Heqlb) as [NV1 _].
           apply VBL1' in Heqlb.
           destruct (mkInjections_7 _ _ _ _ _ _ _ _ _ _ HI _ Heqlb) as [X _].
           rewrite Heqj'b in X. exfalso.
           apply X.
              clear - NV1. unfold Mem.valid_block in NV1. xomega.
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
       (VBL1': forall b1 b3 ofs3, l b1 = Some (b3, ofs3) -> (b1 < n1')%positive),
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

Definition AccessMap_II_Property  (j12 j23 j12' :meminj) (m1 m1' m2 : mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2,
    (Mem.valid_block m2 b2 -> forall k ofs2,
       match j23 b2 with
         None => PMap.get b2 AM ofs2 k  = PMap.get b2 m2.(Mem.mem_access) ofs2 k
       | Some (b3,d3) =>
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) =>  PMap.get b2 AM ofs2 k =
                               PMap.get b1 m1'.(Mem.mem_access) ofs1 k
           | None =>  PMap.get b2 AM ofs2 k =
                      PMap.get b2 m2.(Mem.mem_access) ofs2 k
           end
        end)
     /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
           match source j12' m1' b2 ofs2 with
              Some(b1,ofs1) => PMap.get b2 AM ofs2 k =
                               PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None =>  PMap.get b2 AM ofs2 k = None
          end).

Definition Content_II_Property (j12 j12' j23':meminj) (m1 m1' m2:Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2,
      (Mem.valid_block m2 b2 -> forall ofs2,
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) =>
                 match j23' b2 with
                    None => ZMap.get ofs2 (PMap.get b2 CM) =
                            ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
                 | Some(b3,ofs3) =>
                      ZMap.get ofs2 (PMap.get b2 CM) =
                        inject_memval j12'
                            (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
                 end
           | None => ZMap.get ofs2 (PMap.get b2 CM) =
                     ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
         end)
  /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
         match source j12' m1' b2 ofs2 with
                None => ZMap.get ofs2 (PMap.get b2 CM) =Undef
              | Some(b1,ofs1) =>
                   ZMap.get ofs2 (PMap.get b2 CM) =
                     inject_memval j12'
                       (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
         end)
   /\ fst CM !! b2 = Undef.

Lemma add_no_neutral2: forall (p q:positive), (p <> p + q)%positive.
Proof. intros.
  specialize (Pos.add_no_neutral p q).
  intros. rewrite Pos.add_comm. xomega.
Qed.

Lemma cont_split: forall m b (A B Q: Prop)
              (SPLIT: (Mem.valid_block m b  -> A) /\ (~Mem.valid_block m b -> B) /\ Q)
              (P:Prop)
              (HA: Mem.valid_block m b -> A -> Q -> P)
              (HB: ~Mem.valid_block m b -> B -> Q -> P), P.
Proof. intros.
 destruct SPLIT as [KA [KB KC]].
 destruct (valid_block_dec m b); auto.
Qed.

Lemma II_ok: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                   (Fwd1: mem_forward m1 m1') j23 m3
                   (MInj23 : Mem.inject j23 m2 m3) m3'
                   (Fwd3: mem_forward m3 m3')
                   j' (MInj13': Mem.inject j' m1' m3')
                   (InjIncr: inject_incr (compose_meminj j12 j23) j')
                   (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                   (Unch11': Mem.unchanged_on
                             (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                   (Unch33': Mem.unchanged_on
                         (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
                   prej12' j23' n1' n2'
                   (HeqMKI: mkInjections m1 m1' m2 j12 j23 j' =
                            (prej12', j23', n1', n2'))
                   j12' (Hj12': j12'= removeUndefs j12 j' prej12')
                   m2'
                   (NB: m2'.(Mem.nextblock)=n2')
                   (CONT:  Content_II_Property j12 j12' j23' m1 m1' m2
                                               (m2'.(Mem.mem_contents)))
                   (ACCESS: AccessMap_II_Property j12 j23 j12' m1 m1' m2
                                                  (m2'.(Mem.mem_access))),
                j'=compose_meminj j12' j23' /\
                     inject_incr j12 j12' /\ inject_incr j23 j23' /\
                     Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\
                     Mem.inject j23' m2' m3' /\
                     Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                     inject_separated j12 j12' m1 m2 /\
                     inject_separated j23 j23' m2 m3 /\
                     Mem.unchanged_on (loc_unmapped j23) m2 m2' /\
                     Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'.
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
                (b3 < Mem.nextblock m1 /\ b4 < Mem.nextblock m2)%positive).
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
(*  assert (NB1: Mem.nextblock m1' - Mem.nextblock m1 >= 0).
       assert (B: forall b, b <= Mem.nextblock m1 -> b <= Mem.nextblock m1').
           intros. destruct (Fwd1 (b -1)).  unfold Mem.valid_block. omega.
                 unfold Mem.valid_block in H0. omega.
       clear -B. specialize (B (Mem.nextblock m1)). omega. *)
  assert (NB1:= forward_nextblock _ _ Fwd1).
  assert (XX: n1' = Mem.nextblock m1'). (* /\
              (Mem.nextblock m2 + (Mem.nextblock m1' - Mem.nextblock m1) = n2')%positive ).*)
    destruct (mkInjections_0  _ _ _ _ _ _ _ _ _ _ HeqMKI)
      as [[NN [N1 [N2 [JJ1 JJ2]]]] | [n [NN [N1 [N2 N3]]]]].
    subst. eapply Pos.le_antisym; assumption. assumption.
 subst.
  assert (VBj': forall b1 b3 ofs3, j' b1 = Some (b3, ofs3) ->
                (b1 < Mem.nextblock m1')%positive).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj13').
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI
               InjIncr _ InjSep VBj12_1 VBj12_2 VBj23_1 VBj').
(*  assert (preAL12' := mkInjections_aligned_1 _ _ _ _ _ _ _ _ _ _ HeqMKI AL12).
  assert (AL12' : inject_aligned  (removeUndefs j12 j' prej12')).
          intros b; intros. apply RU_D in H.
          eapply preAL12'. apply H. assumption.
  assert (AL23' := mkInjections_aligned_2 _ _ _ _ _ _ _ _ _ _
                   HeqMKI AL23 AL13').*)
split. assumption.
split. assumption.
split. assumption.
(*split. assumption.
split. assumption.*)
assert (IDextensional: forall b,
            j' b = compose_meminj (removeUndefs j12 j' prej12') j23' b).
   intros. rewrite <- ID. trivial.
clear ID.
assert (Fwd2: mem_forward m2 m2').
  split; intros; rename b into b2.
  (*valid_block*)
     clear - H NB1 HeqMKI. unfold Mem.valid_block in *.
     destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI)
     as [HH | HH].
       destruct HH as [_ [_ [XX _]]]. rewrite XX in H. assumption.
       destruct HH as [n [NN [_ [_ X]]]]. rewrite <- X.
        xomega.
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
           eapply MInj12. apply J1.
             eapply Fwd1.
                apply (Mem.perm_valid_block _ _  _ _ _ P1).
                apply H0.
        rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2. apply H0.
    rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2. apply H0.
assert (Unch2: Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2').
  split; intros.
     rename H into HP.
     apply (valid_split _ _ _ _ (ACCESS b)); intros; clear ACCESS.
     (* case Mem.valid_block m2 b*)
        specialize (H1 k ofs).
        unfold loc_out_of_reach in HP.
        remember (j23  b) as jb.
        destruct jb; apply eq_sym in Heqjb.
          destruct p0.
          remember (source j12 m1 b ofs) as d.
          destruct d.
             destruct p0.
             rewrite (perm_subst _ _ _ _ _ _ _ H1). clear H1.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
             subst. apply eq_sym in PP. inv PP.
             specialize (HP _ _ JJ). assert (z0 + dd1 - dd1 = z0). omega.
             rewrite H1 in HP.
             exfalso. apply (HP PERM).
          rewrite (perm_subst _ _ _ _ _ _ _ H1). split; auto.
        rewrite (perm_subst _ _ _ _ _ _ _ H1). split; auto.
      (*invalid*)
           contradiction.
  rename H into HP.
  apply (cont_split _ _ _ _ _ (CONT b)); intros; clear CONT.
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
            assert (Arith : z + dd1 - dd1 = z) by omega.
            rewrite Arith in NonPerm.
            contradiction.
         apply H1.
       (*invalid*)
          exfalso.
          apply Mem.perm_valid_block in H0. contradiction.
assert (UnchLOM2: Mem.unchanged_on (loc_unmapped j23) m2 m2').
  unfold loc_unmapped.
  split; intros. rename H into HP.
        destruct (ACCESS b) as [Val _].
        specialize (Val H0 k ofs).
        rewrite HP in Val.
        rewrite (perm_subst _ _ _ _ _ _ _ Val). clear Val. split; auto.
  apply (cont_split _ _ _ _ _ (CONT b)); intros; clear CONT.
      (*case Mem.valid_block m2 b*)
          specialize (H2 ofs).
          assert (j23' b = None).
               remember (j23' b) as d.
               destruct d; trivial. apply eq_sym in Heqd. destruct p.
               destruct (sep23 _ _ _ H Heqd). exfalso. apply (H4 H1).
          remember (source j12 m1 b ofs) as d.
          destruct d.
             destruct p. subst. rewrite H4 in H2. apply H2.
          apply H2.
      (*case invalid*)
          apply Mem.perm_valid_block in H0. contradiction.

assert (UnchLOOR3: Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3').
   unfold loc_out_of_reach.
   split; intros.
      eapply Unch33'.
        unfold loc_out_of_reach, compose_meminj. intros.
           remember (j12 b0) as d.
           destruct d.
              apply eq_sym in Heqd. destruct p0.
              remember (j23 b1) as dd.
              destruct dd; inv H1. apply eq_sym in Heqdd. destruct p0. inv H3.
              specialize (H _ _ Heqdd).
              intros N. apply H.
              assert (Arith : ofs - (z + z0) + z = ofs - z0) by omega.
              rewrite <- Arith.
              eapply MInj12. apply Heqd. apply N.
           inv H1.
        apply H0.
   eapply Unch33'.
        unfold loc_out_of_reach, compose_meminj. intros.
           remember (j12 b0) as d.
           destruct d.
              apply eq_sym in Heqd. destruct p.
              remember (j23 b1) as dd.
              destruct dd; inv H1. apply eq_sym in Heqdd. destruct p. inv H3.
              intros N. eapply (H _  _ Heqdd).
              assert (Arith: ofs - (z + z0) + z = ofs - z0) by omega.
              rewrite <- Arith. eapply MInj12. apply Heqd. apply N.
           inv H1.
        apply H0.
assert (NOVj12':= RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _
                  MInj23 _ _ _ _ _ HeqMKI).
assert (Inj12': Mem.inject (removeUndefs j12 j' prej12')  m1' m2').
    assert (Perm12': forall b1 b2 delta ofs k p,
             (removeUndefs j12 j' prej12') b1 = Some (b2, delta) ->
             Mem.perm m1' b1 ofs k p -> Mem.perm m2' b2 (ofs + delta) k p).
        intros.
        apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
            specialize (H2 k (ofs+delta)).
            remember (j23 b2) as d.
            destruct d; apply eq_sym in Heqd.
               destruct p0 as [b3 d3].
               remember (j12 b1) as dd.
               destruct dd; apply eq_sym in Heqdd.
                 destruct p0.
                 rewrite (inc12 _ _ _ Heqdd) in H. inv H.
                 rewrite (source_SomeI j12 _  _ b1) in H2.
                 rewrite (perm_subst _ _ _ _ _ _ _ H2). apply H0.
                 apply MInj12.
                    assumption.
                    apply Fwd1. apply (VBj12_1 _ _ _ Heqdd).
                           eapply Mem.perm_implies. eapply Mem.perm_max.
                               apply H0. apply perm_any_N.
               destruct (sep12 _ _ _ Heqdd H) as [_ NV2]. exfalso. apply (NV2 H1).
            rewrite (perm_subst _ _ _ _ _ _ _ H2). clear H2.
                 destruct Unch11' as [UP _].
                 remember (j12 b1) as dd.
                 destruct dd; apply eq_sym in Heqdd.
                   destruct p0.
                   rewrite (inc12 _ _ _ Heqdd) in H. inv H.
                   eapply MInj12. apply Heqdd.
                   rewrite UP. apply H0.
                      unfold loc_unmapped, compose_meminj.
                          rewrite Heqdd. rewrite Heqd. trivial.
                      apply (VBj12_1 _ _ _ Heqdd).
            destruct (sep12 _ _ _ Heqdd H) as [_ NV2]. exfalso. apply (NV2 H1).
        (*case ~ valid_block m2 b2*)
            specialize (H2 k (ofs+delta)).
            rewrite (source_SomeI (removeUndefs j12 j' prej12') _  _ b1) in H2.
            rewrite (perm_subst _ _ _ _ _ _ _ H2). apply H0.
            apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _
                    MInj23 _ _ _ _ _ HeqMKI).
               assumption.
               eapply Mem.perm_implies. eapply Mem.perm_max.
                    apply H0. apply perm_any_N.
    assert (INJ:Mem.mem_inj  (removeUndefs j12 j' prej12') m1' m2').
      split. apply Perm12'.
      (*mi_align*)
          intros. unfold removeUndefs in H.
          remember (j12 b1) as d.
          destruct d; apply eq_sym in Heqd.
            destruct p0 as [bb2 deta2].
            inv H.
            eapply MInj12. eassumption.
            assert (MR: Mem.range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p).
               intros z. intros. specialize (H0 _ H).
               eapply Fwd1. eapply VBj12_1. apply Heqd. apply H0.
            eassumption.
          remember (j' b1) as q.
          destruct q; apply eq_sym in Heqq. destruct p0.
            destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                        HeqMKI VB12 VBj23_1 _ _ _ H)
              as [HX | [HX | HX]].
            destruct HX as [J12 [Val1 Val2]]. rewrite J12 in Heqd. inv Heqd.
            destruct HX as [? [? [? [? D]]]]. subst. apply Z.divide_0_r.
            destruct HX as [? [? [? [? [? D]]]]]. subst.  apply Z.divide_0_r.
          inv H.
      (*memval  j12' m1' m2'.*)
          intros.
          apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
         (*case Mem.valid_block m2 b2*)
             specialize (H2 (ofs + delta)).
             assert (J12:  j12 b1 = Some (b2, delta)).
                 remember (j12 b1) as d.
                 destruct d; apply eq_sym in Heqd.
                      destruct p. rewrite (inc12 _ _ _ Heqd) in H. apply H.
                      destruct (sep12 _ _ _ Heqd H). exfalso. apply (H5 H1).
             assert (Val1:= VBj12_1 _ _ _ J12).
             assert (Perm1: Mem.perm m1 b1 ofs Max Nonempty).
                   apply (Fwd1 _ Val1).
                      eapply Mem.perm_max. eapply Mem.perm_implies.
                        apply H0. apply perm_any_N.
             rewrite (source_SomeI j12 _  _ b1) in H2; trivial.
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
                           rewrite IDextensional in H5.
                           apply compose_meminjD_Some in H5.
                           destruct H5 as [bb1 [off1 [off [JJ1 [JJ2 Delta]]]]].
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
                         rewrite (Uval b1 ofs UNMAPPED RD).
                         apply (memval_inject_incr j12).
                            apply (Mem.mi_memval _ _ _
                               (Mem.mi_inj _ _ _ MInj12) _ _  _ _ J12 RD).
                            assumption.
                   apply MInj12.
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
                remember (ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1')))
                          as v.
                destruct (source_SomeE _ _ _ _ _ Heqss)
                      as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
                clear Heqss.
                apply eq_sym in PP. inv PP.
                assert (MX: Mem.perm m1' b1 ofs Max Nonempty).
                    eapply Mem.perm_max. eapply Mem.perm_implies.
                    apply H0. apply perm_any_N.
                destruct (eq_block b b1); subst.
                (*case b = b1*)
                   rewrite H in JJ. apply eq_sym in JJ. inv JJ.
                   assert (z = ofs). omega.
                   subst.  clear Off2.
                   remember (ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1')))
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
                       simpl. rewrite IDextensional in H5.
                       apply compose_meminjD_Some in H5.
                       destruct H5 as [bb1 [off1 [off [JJ1 [JJ2 Delta]]]]].
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
                    (Mem.perm_valid_block _ _ _ _ _ H0) H).
               assert (ofs + delta - delta = ofs). omega.
               rewrite H4.
               eapply Mem.perm_max. eapply Mem.perm_implies.
                    apply H0. apply perm_any_N.
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
                     (b1 < Mem.nextblock m1 /\ b2 < Mem.nextblock m2)%positive).
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
          destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                      HeqMKI ValJ12  VBj23_1 _ _ _ Heqd)
          as [H | [H | H]].
            destruct H as [J12 [Val1 Val2]]. apply Fwd2. apply Val2.
            destruct H as [_ [_ [_ [_ D]]]]. apply D.
            destruct H as [? [_ [_ [_ [_ D]]]]]. apply D.
        inv Heqd.
     inv H.
  (*no_overlap*)
       apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ _ _ _ _ HeqMKI).
  (*representable*)
       intros.
       unfold removeUndefs in H.
       remember (j12 b) as d.
       destruct d; apply eq_sym in Heqd.
          destruct p. inv H.
          destruct H0.
          (*location ofs*)
            eapply MInj12. apply Heqd.
            left. apply Fwd1. apply (VBj12_1 _ _ _ Heqd). apply H.
          (*location ofs -1*)
            eapply MInj12. apply Heqd.
            right. apply Fwd1. apply (VBj12_1 _ _ _ Heqd). apply H.
       remember (j' b) as dd.
       destruct dd; apply eq_sym in Heqdd.
          destruct p.
          destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                     HeqMKI VB12  VBj23_1 _ _ _ H).
              destruct H1. rewrite H1 in Heqd. discriminate.
              destruct H1 as [HH | HH].
              destruct HH as [A [B [C [D E]]]]; subst.
                 split. omega.
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
              destruct HH as [M [A [B [C [D E]]]]]; subst.
                 split. omega.
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
       inv H.
split; trivial.
split; trivial.
assert (Inj23': Mem.inject j23' m2' m3').
   assert (Perm23': forall b1 b2 delta ofs k p,
                j23' b1 = Some (b2, delta) ->
                Mem.perm m2' b1 ofs k p -> Mem.perm m3' b2 (ofs + delta) k p).
      intros b2 b3; intros.
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
      (*valid*)
          specialize (H2 k ofs).
          assert (FF: j23 b2 = Some (b3, delta)).
             remember (j23 b2) as dd.
             destruct dd; apply eq_sym in Heqdd.
               destruct p0. apply inc23 in Heqdd. rewrite Heqdd in H. apply H.
             destruct (sep23 _ _ _ Heqdd H). exfalso. apply (H3 H1).
          rewrite FF in H2.
          remember (source j12 m1 b2 ofs) as d.
          destruct d.
          (*source  j12 m1 b2 ofs = Some p0*)
              destruct p0.
              destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
              subst. apply eq_sym in PP. inv PP.
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0. clear H2.
              rewrite <- Zplus_assoc.
              assert (J: j' b = Some (b3, dd1 + delta)).
                  apply InjIncr. unfold compose_meminj.
                     rewrite JJ. rewrite FF. trivial.
              eapply MInj13'. apply J.
                 apply H0.
          (*source  j12 m1 b2 ofs = None*)
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0. clear H2.
              assert (MX: Mem.perm m2 b2 ofs Max Nonempty).
                  eapply Mem.perm_max. eapply Mem.perm_implies.
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
                     apply (SRC _ _ (VBj12_1 _ _ _ Heqdd) Heqdd).
                  (*case b2 <> b*)
                     intros N.
                     assert (PX: Mem.perm m2 b (ofs + delta - z0) Max Nonempty).
                        assert (ofs+delta-(z+z0)+z = ofs+delta-z0). omega.
                        rewrite <- H2.
                        eapply MInj12. apply Heqdd. apply N.
                     assert (NOV := Mem.mi_no_overlap _ _ _
                            MInj23 b2 _ _ b _ _ _ _ n FF Heqddd MX PX).
                     destruct NOV.
                           apply H2. trivial.
                           apply H2. omega.
              destruct Unch33' as [U33P _].
              rewrite <- U33P.
                    eapply MInj23. apply FF. apply H0.
                    apply UNCH.
                    apply (VBj23_2 _ _ _ FF).
      (*invalid*)
          assert (MX: Mem.perm m2' b2 ofs Max Nonempty).
              eapply Mem.perm_max. eapply Mem.perm_implies.
                apply H0. apply perm_any_N.
          assert (Max2':= H2 Max ofs).
          specialize (H2 k ofs).
          assert (J12: j23 b2 = None).
              remember (j23 b2) as d.
              destruct d; trivial. apply eq_sym in Heqd. destruct p0.
              assert (X:= VBj23_1 _ _ _ Heqd).
              exfalso.  apply (H1 X).
          remember (source (removeUndefs j12 j' prej12') m1' b2 ofs) as d.
          destruct d. destruct p0.
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in*. clear H2.
              rewrite (perm_subst _ _ _ _ _ _ _ Max2') in*. clear Max2'.
              destruct (source_SomeE _ _ _ _ _ Heqd)
                as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off2]]]]]]]. clear Heqd.
              subst. apply eq_sym in PP. inv PP.
              rewrite <- Zplus_assoc.
              assert (Jb: j' b= Some (b3, dd1 + delta)).
                  rewrite IDextensional. unfold compose_meminj.
                           rewrite JJ'. rewrite H. trivial.
              eapply MInj13'. apply Jb. apply H0.
          unfold Mem.perm in MX. rewrite Max2' in MX.  inv MX.
                      (*specialize (source_NoneE _ _ _ _ Heqd). intros SRC. clear Heqd.
                        rewrite H in *.
                        rewrite (perm_subst _ _ _ _ _ _ _ H2) in*. clear H2. trivial.*)
   assert (MI: Mem.mem_inj j23' m2' m3').
      split.
      (*mi_perm *) apply Perm23'.
      (*mi_align*) intros.
          destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H)
            as [HH | [HH | HH]].
          destruct HH. eapply MInj23. apply H1.
             intros z; intros. specialize (H0 _ H3).
              eapply Fwd2; try eassumption.
          destruct HH as [? [? ?]]. subst. rename b2 into b3. clear H3.
            assert (ZZ: compose_meminj (removeUndefs j12 j' prej12') j23'  (Mem.nextblock m1) = Some (b3, delta)).
                   rewrite IDextensional in H2; trivial.
               destruct (compose_meminjD_Some _ _ _ _ _ ZZ) as
                  [b2 [dd1 [dd2 [JJ1 [JJ2 XX]]]]]. subst; clear ZZ.
            assert (J12': prej12' (Mem.nextblock m1) = Some(Mem.nextblock m2, 0)).
               remember (j12 (Mem.nextblock m1)) as q.
               destruct q; apply eq_sym in Heqq.
                 destruct p0. rewrite (inc12 _ _ _ Heqq) in JJ1. inv JJ1.
                   apply VBj12_1 in Heqq. exfalso. unfold Mem.valid_block in Heqq. xomega.
                 unfold removeUndefs in JJ1. rewrite Heqq in JJ1. rewrite H2 in JJ1.
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ JJ1).
                   destruct H1. rewrite H1 in Heqq. discriminate.
                   destruct H1. destruct H1 as [_ [? [? [? ?]]]]. subst. assumption.
                   destruct H1 as [mm [? [? [? [? ?]]]]]; subst.
                     apply eq_sym in H1. rewrite Pos.add_comm in H1.
                     apply Pos.add_no_neutral in H1. intuition.
            assert (prej12' (Mem.nextblock m1) = Some (b2, dd1)).
              unfold removeUndefs in JJ1.
              remember (j12 (Mem.nextblock m1)).
              destruct o; apply eq_sym in Heqo.
                destruct p0. apply VBj12_1 in Heqo. exfalso. unfold Mem.valid_block in Heqo. xomega.
              rewrite H2 in JJ1. assumption.
            rewrite J12' in H1. inv H1. simpl in *. clear H.
            destruct (ACCESS (Mem.nextblock m2)) as [_ ZZ].
            assert (NVB2: ~ Mem.valid_block m2 (Mem.nextblock m2)).
                       unfold Mem.valid_block. xomega.
            assert (MR: Mem.range_perm m1' (Mem.nextblock m1) ofs (ofs + size_chunk chunk) Max p).
               intros z; intros.
               specialize (ZZ NVB2 Max z).
               remember (source (removeUndefs j12 j' prej12') m1' (Mem.nextblock m2) z).
               destruct o.
               Focus 2. specialize (H0 _ H). unfold Mem.perm in H0. rewrite ZZ in H0. simpl in H0. intuition.
               destruct (source_SomeE _ _ _ _ _ Heqo)
                        as [bb1 [dd1 [ofs11 [PPP [VB [ JJ' [PERM Off2]]]]]]]. clear Heqo.
               subst. specialize (H0 _ H).
               rewrite (perm_subst _ _ _ _ _ _ _ ZZ) in H0. clear ZZ.
               assert (prej12'  bb1 = Some (Mem.nextblock m2, dd1)).
                 unfold removeUndefs in JJ'.
                 remember (j12 bb1).
                 destruct o; apply eq_sym in Heqo.
                   destruct p0. inv JJ'. apply VBj12_2 in Heqo. contradiction.
                 remember (j' bb1).
                 destruct o. destruct p0. assumption. inv JJ'.
               assert (bb1 = Mem.nextblock m1).
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ H1).
                 destruct H3. apply VBj12_2 in H3. contradiction.
                 destruct H3. destruct H3; trivial.
                 destruct H3 as [mm1 [? [? [? [? ?]]]]]. subst.
                   apply eq_sym in H4. rewrite Pos.add_comm in H4.
                   apply Pos.add_no_neutral in H4. intuition.
               subst. rewrite J12' in H1. inv H1. rewrite Zplus_0_r. assumption.
             eapply MInj13'. apply H2. apply MR.
          destruct HH as [mm [? [? ?]]]. subst. rename b2 into b3. clear H3.
            assert (ZZ: compose_meminj (removeUndefs j12 j' prej12') j23' ((Mem.nextblock m1+ mm)%positive) = Some (b3, delta)).
                   rewrite IDextensional in H2; trivial.
               destruct (compose_meminjD_Some _ _ _ _ _ ZZ) as
                  [b2 [dd1 [dd2 [JJ1 [JJ2 XX]]]]]. subst; clear ZZ.
            assert (J12': prej12' ((Mem.nextblock m1+ mm)%positive) = Some((Mem.nextblock m2+ mm)%positive, 0)).
               remember (j12 ((Mem.nextblock m1+ mm)%positive)) as q.
               destruct q; apply eq_sym in Heqq.
                 destruct p0. rewrite (inc12 _ _ _ Heqq) in JJ1. inv JJ1.
                   apply VBj12_1 in Heqq. exfalso. unfold Mem.valid_block in Heqq. xomega.
                 unfold removeUndefs in JJ1. rewrite Heqq in JJ1. rewrite H2 in JJ1.
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ JJ1).
                   destruct H1. rewrite H1 in Heqq. discriminate.
                   destruct H1. destruct H1 as [? [? [? [? ?]]]]. subst.
                     rewrite Pos.add_comm in H1.
                     apply Pos.add_no_neutral in H1. intuition.
                   destruct H1 as [mm2 [? [? [? [? ?]]]]]; subst.
                     apply Pos.add_reg_l in H1. subst.
                   assumption.
            assert (prej12' ((Mem.nextblock m1+ mm)%positive) = Some (b2, dd1)).
              unfold removeUndefs in JJ1.
              remember (j12 ((Mem.nextblock m1+ mm)%positive)).
              destruct o; apply eq_sym in Heqo.
                destruct p0. apply VBj12_1 in Heqo. exfalso. unfold Mem.valid_block in Heqo. xomega.
              rewrite H2 in JJ1. assumption.
            rewrite J12' in H1. inv H1. simpl in *. clear H.
            destruct (ACCESS ((Mem.nextblock m2+ mm)%positive)) as [_ ZZ].
            assert (NVB2: ~ Mem.valid_block m2 ((Mem.nextblock m2+ mm)%positive)).
                       unfold Mem.valid_block. xomega.
            assert (MR: Mem.range_perm m1' ((Mem.nextblock m1+ mm)%positive) ofs (ofs + size_chunk chunk) Max p).
               intros z; intros.
               specialize (ZZ NVB2 Max z).
               remember (source (removeUndefs j12 j' prej12') m1'
                      (Mem.nextblock m2 + mm)%positive z).
               destruct o.
               Focus 2. specialize (H0 _ H). unfold Mem.perm in H0. rewrite ZZ in H0. simpl in H0. intuition.
               destruct (source_SomeE _ _ _ _ _ Heqo)
                        as [bb1 [dd1 [ofs11 [PPP [VB [ JJ' [PERM Off2]]]]]]]. clear Heqo.
               subst. specialize (H0 _ H).
               rewrite (perm_subst _ _ _ _ _ _ _ ZZ) in H0. clear ZZ.
               assert (prej12'  bb1 = Some ((Mem.nextblock m2+ mm)%positive, dd1)).
                 unfold removeUndefs in JJ'.
                 remember (j12 bb1).
                 destruct o; apply eq_sym in Heqo.
                   destruct p0. inv JJ'. apply VBj12_2 in Heqo. contradiction.
                 remember (j' bb1).
                 destruct o. destruct p0. assumption. inv JJ'.
               assert (bb1 = (Mem.nextblock m1+ mm)%positive).
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ H1).
                 destruct H3. apply VBj12_2 in H3. contradiction.
                 destruct H3. destruct H3 as [? [? ?]]; subst.
                   rewrite Pos.add_comm in H4.
                   apply Pos.add_no_neutral in H4. intuition.
                 destruct H3 as [mm1 [? [? [? [? ?]]]]]. subst.
                   apply Pos.add_reg_l in H4. subst. trivial.
               subst. rewrite J12' in H1. inv H1. rewrite Zplus_0_r. assumption.
             eapply MInj13'. apply H2. apply MR.
      (*memval j23' m2' m3'*) intros b2 ofs2 b3 delta3 Jb2 Perm2.
          assert (Perm2Max: Mem.perm m2' b2 ofs2  Max Nonempty).
             eapply Mem.perm_max. eapply Mem.perm_implies.
                        apply Perm2. constructor.
          destruct (ACCESS b2) as [Valid Invalid].
          apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
          (*case Mem.valid_block m2 b2*)
             specialize (Valid H Cur ofs2). clear Invalid.
             specialize (H0 ofs2).
             assert (J23:  j23 b2 = Some (b3, delta3)).
                 remember (j23 b2) as d. destruct d; apply eq_sym in Heqd.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. apply Jb2.
                    destruct (sep23 _ _ _ Heqd Jb2). exfalso. apply (H2 H).
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
                   eapply Mem.perm_max. eapply Mem.perm_implies.
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
                rewrite IDextensional in H3.
                destruct (compose_meminjD_Some _ _ _ _ _ H3)
                    as [bb2 [dd2 [ddd3 [RRR [JJJ23  DD]]]]]; subst.
                rewrite RRR. econstructor. apply JJJ23.
                rewrite Int.add_assoc. decEq. unfold Int.add.
                    apply Int.eqm_samerepr. auto with ints.
             (*case source  j12 m1 b2 ofs2  = None *)
                rewrite H0. clear H0.
                rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid.
                assert (MX : Mem.perm m2 b2 ofs2 Max Nonempty).
                     eapply Mem.perm_max. eapply Mem.perm_implies.
                     apply Perm2. constructor.
                assert (LOOR: loc_out_of_reach
                             (compose_meminj j12 j23) m1 b3 (ofs2+delta3)).
                     unfold loc_out_of_reach, compose_meminj. intros.
                     remember (j12 b0) as q.
                     destruct q; apply eq_sym in Heqq; inv H0.
                     destruct p.
                     remember (j23 b) as qq.
                     destruct qq; apply eq_sym in Heqqq; inv H3.
                     destruct p. inv H2.
                     destruct (eq_block b2 b); subst.
                     (*case b2=b*)
                         rewrite J23  in Heqqq. inv Heqqq.
                         assert (ofs2 + z0 - (z + z0) = ofs2 - z). omega.
                         rewrite H0.
                         apply (source_NoneE _ _ _ _ Heqss).
                             apply (VBj12_1 _ _ _ Heqq).
                             apply Heqq.
                     (*case b2<>b*)
                         intros N.
                         assert (NN2: Mem.perm m2 b
                                     (ofs2 + (delta3 - z0)) Max Nonempty).
                             assert (ofs2 + delta3 - (z + z0) + z =
                                      ofs2 + (delta3 - z0)). omega.
                             rewrite <- H0.
                             eapply MInj12. apply Heqq. apply N.
                         destruct (Mem.mi_no_overlap _ _ _
                                 MInj23 b2 _ _ b _ _ _ _ n J23 Heqqq MX NN2).
                                     apply H0; trivial.
                                     apply H0. omega.
                assert (Perm3: Mem.perm m3 b3 (ofs2+delta3) Cur Readable).
                   eapply MInj23. apply J23. apply Perm2.
                destruct Unch33' as [Uperm UVal].
                rewrite (UVal _ _ LOOR Perm3).
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
                   eapply Mem.perm_max. eapply Mem.perm_implies.
                       apply Perm2. apply perm_any_N.
                 assert (JB: j' b1 = Some (b3, delta2 + delta3)).
                       rewrite IDextensional. unfold compose_meminj.
                       rewrite RR1. rewrite Jb2. trivial.

                 specialize (Mem.mi_memval _ _ _
                       (Mem.mi_inj _ _ _  MInj13') _ _  _ _ JB Perm2).
                 intros MemVal13'.
                 rewrite <- Zplus_assoc.
                 inv MemVal13'; simpl in *; try econstructor.
                 rewrite IDextensional in H3.
                 destruct (compose_meminjD_Some _ _ _ _ _ H3)
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

       destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI)
        as [HH | HH].
       destruct HH as [? [? [? [?  ?]]]]; subst.
         apply H. apply Fwd2. apply (VBj23_1 _ _ _ Heqd).
       destruct HH as [N [? [? [? ?]]]].
         destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ Heqd)
            as [HH | [HH | HH]].
         destruct HH. apply H. apply Fwd2. apply H5.
         destruct HH as [? [? ?]]; subst.
            apply (H H6).
         destruct HH as [M [BM [J' B]]]; subst.
            apply (H B).
   (*mi_mappedblocks*)
      intros.
      destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI
        VBj23_1 _ _ _ H)as [HH | [HH | HH]].
      destruct HH. apply Fwd3. apply (VBj23_2 _ _ _  H0).
      destruct HH as [? [? ?]]; subst.
        eapply MInj13'. apply H1.
         destruct HH as [M [BM [J' B]]]; subst.
           eapply MInj13'. apply J'.
   (*no_overlap*)
      intros b; intros.
      destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI
        VBj23_1 _ _ _ H0) as [HH | [HH | HH]].
      destruct HH as [j23b vbb].
         destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _
               HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].
            eapply MInj23.
               apply H.
               apply j23b.
               apply j23b2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b). apply H2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b2). apply H3.
            destruct KK as [BM [J' B']]; subst.
              left. assert (j23 (Mem.nextblock m2) = None).
                     remember (j23 (Mem.nextblock m2)) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                    destruct (sep23 _ _ _ H4 H1). apply H6.
                    eapply MInj23. apply j23b.
            destruct KK as [M [BM [J' B']]].
            left. assert ( j23 b2 = None).
                     remember (j23 b2) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd).
                     clear - VBj23_1 BM. subst.
                     unfold Mem.valid_block in VBj23_1. xomega.
                  intros N; subst.
                    destruct (sep23 _ _ _ H4 H1). apply H6.
                    eapply MInj23. apply j23b.
         destruct HH as [NBb [j'b NBb']]; subst.
           destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _
                HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].
             left. assert (j23 (Mem.nextblock m2) = None).
                      remember (j23 (Mem.nextblock m2)) as d.
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                     destruct (sep23 _ _ _ H4 H0).
                     apply H6. eapply MInj23. apply j23b2.
            destruct KK as [BM [J' B']]; subst.
              exfalso. apply H; trivial.
            destruct KK as [M [BM [J' B']]]. subst.
          (*first case where both blocks are in m2' but not in m2*)
              assert (j23_None1: j23 (Mem.nextblock m2) = None).
                 remember (j23 (Mem.nextblock m2)) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2: j23 ((Mem.nextblock m2 + M)%positive) = None).
                 remember (j23 ((Mem.nextblock m2 + M)%positive)) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 exfalso. unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : Mem.nextblock m1 <> (Mem.nextblock m1 + M)%positive).
                 apply add_no_neutral2.
              destruct (ACCESS (Mem.nextblock m2)) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).

              remember (source (removeUndefs j12 j' prej12')
                    m1' (Mem.nextblock m2) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2 + M)%positive) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs j12 j' prej12') m1'
                         (Mem.nextblock m2 + M)%positive ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p.
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3.
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

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
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst.
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
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H7)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                              exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) M).
                                 rewrite Pos.add_comm. apply H10.
                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           apply Pos.add_reg_l in nbm. apply eq_sym in nbm.  subst.
                           eapply MInj13'.
                              apply NEQ.
                              assumption.
                              assumption.
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       exfalso. apply (add_no_neutral2 (Mem.nextblock m2) MM1).
                         apply H6.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.
         destruct HH as [M1 [? [j'b1 NBb1]]]; subst.
           destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _
                HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].
             left. assert (j23 (Mem.nextblock m2 + M1)%positive = None).
                      remember (j23 (Mem.nextblock m2 + M1)%positive) as d.
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                     destruct (sep23 _ _ _ H4 H0).
                     apply H6. eapply MInj23. apply j23b2.
            destruct KK as [BM [J' B']]; subst.
          (*second case where both blocks are in m2' but not in m2*)
              assert (j23_None1: j23 (Mem.nextblock m2 + M1)%positive = None).
                 remember (j23 (Mem.nextblock m2 + M1)%positive) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2: j23 (Mem.nextblock m2) = None).
                 remember (j23 (Mem.nextblock m2)) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 exfalso. unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : (Mem.nextblock m1 + M1)%positive <> Mem.nextblock m1).
                rewrite Pos.add_comm. apply Pos.add_no_neutral.
              destruct (ACCESS (Mem.nextblock m2 + M1)%positive) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).

              remember (source (removeUndefs j12 j' prej12')
                    m1' ((Mem.nextblock m2 +M1)%positive) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs j12 j' prej12') m1'
                         (Mem.nextblock m2) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p.
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3.
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

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
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst.
                       exfalso. rewrite Pos.add_comm in H6.
                        apply Pos.add_no_neutral in H6. apply H6.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       apply Pos.add_reg_l in H6. apply eq_sym in H6. subst.
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
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H6)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                           eapply MInj13'.
                              apply NEQ.
                              assumption.
                              assumption.
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.

                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) MM2).
                                 rewrite Pos.add_comm. rewrite <- nbm. trivial.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.
            destruct KK as [M2 [BM [J2' B2']]]; subst.
          (*third case where both blocks are in m2' but not in m2*)
              assert (j23_None1: j23 (Mem.nextblock m2 + M1)%positive = None).
                 remember (j23 (Mem.nextblock m2 + M1)%positive) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2:  j23 (Mem.nextblock m2 + M2)%positive = None).
                 remember (j23 (Mem.nextblock m2 + M2)%positive) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : (Mem.nextblock m1 + M1)%positive <> (Mem.nextblock m1 + M2)%positive).
                intros NN. apply Pos.add_cancel_l in NN. subst.
                apply H; trivial.
              destruct (ACCESS (Mem.nextblock m2 + M1)%positive) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).

              remember (source (removeUndefs j12 j' prej12')
                    m1' ((Mem.nextblock m2 +M1)%positive) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  ((Mem.nextblock m2 + M2)%positive)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs j12 j' prej12') m1'
                         ((Mem.nextblock m2 + M2)%positive) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p.
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3.
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

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
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst.
                       exfalso. rewrite Pos.add_comm in H6.
                        apply Pos.add_no_neutral in H6. apply H6.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       apply Pos.add_reg_l in H6. apply eq_sym in H6. subst.
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
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H6)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                           exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) M2).
                                 rewrite Pos.add_comm. trivial.

                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           apply Pos.add_cancel_l in nbm. subst.
                           eapply MInj13'.
                              apply NEQ.
                              assumption.
                              assumption.
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.

   (*mi_representable*) intros. rename b into b2.
       destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H)
       as [HH | [ HH | HH]].
       (*first case*)
         destruct HH as [j23b2 Val2].
         destruct (ACCESS b2) as [Valid _].
         rewrite j23b2 in Valid.
         destruct H0.
         (*location ofs*)
           specialize (Valid Val2 Max (Int.unsigned ofs)).
           remember (source  j12 m1 b2 (Int.unsigned ofs)) as d.
           destruct d.
           (*source  j12 m1 b2 (Int.unsigned ofs) = Some p*)
             destruct p.
             rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0. clear Valid.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             assert (Val1 := Mem.perm_valid_block _ _ _ _ _ PERM).
             assert (Perm2: Mem.perm m2 b2 (z+delta1) Max Nonempty).
                 eapply MInj12. apply J12. apply PERM.
              eapply MInj23. apply j23b2.
              left. rewrite Off1. apply Perm2.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0. clear Valid.
             eapply MInj23. apply j23b2.
             left. apply H0.
         (*location ofs -1*)
           specialize (Valid Val2 Max (Int.unsigned ofs -1)).
           remember (source  j12 m1 b2 (Int.unsigned ofs -1)) as d.
           destruct d.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = Some p*)
             destruct p.
             rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0. clear Valid.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             assert (Val1 := Mem.perm_valid_block _ _ _ _ _ PERM).
             assert (Perm2: Mem.perm m2 b2 (z+delta1) Max Nonempty).
                 eapply MInj12. apply J12. apply PERM.
              eapply MInj23. apply j23b2.
              right. rewrite Off1. apply Perm2.
           (*source  j12 m1 b2 (Int.unsigned ofs -1 ) = None0*)
             rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0. clear Valid.
             eapply MInj23. apply j23b2.
             right. apply H0.
       (*second case*)
         destruct HH as [? [j'b2 Val2']]. subst.
         destruct (ACCESS (Mem.nextblock m2)) as [_ InValid].
         assert (NVB2: ~Mem.valid_block m2 (Mem.nextblock m2)).
            unfold Mem.valid_block; xomega.
         destruct H0.
         (*location ofs*)
           specialize (InValid NVB2 Max (Int.unsigned ofs)).
           remember (source (removeUndefs j12 j' prej12') m1' (Mem.nextblock m2)
                            (Int.unsigned ofs)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (j12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (j' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [_ [? [? ?]]]]; subst.
                    rewrite Zplus_0_r in *. subst.
                    eapply MInj13'. apply j'b2. left; apply PERM.
                destruct KK as [m [_ [? _]]].
                    exfalso. clear -H3. apply (add_no_neutral2 _ _ H3).
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
         (*location ofs -1*)
           specialize (InValid NVB2 Max (Int.unsigned ofs-1)).
           remember (source (removeUndefs j12 j' prej12') m1' (Mem.nextblock m2)
                            (Int.unsigned ofs-1)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (j12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (j' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [_ [? [? ?]]]]; subst.
                    rewrite Zplus_0_r in *. subst.
                    eapply MInj13'. apply j'b2. right; apply PERM.
                destruct KK as [m [_ [? _]]].
                    exfalso. clear -H3. apply (add_no_neutral2 _ _ H3).
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
       (*third case*)
         destruct HH as [m [? [j'b2 Val2']]]; subst.
         destruct (ACCESS ((Mem.nextblock m2+m)%positive)) as [_ InValid].
         assert (NVB2: ~Mem.valid_block m2 ((Mem.nextblock m2+m)%positive)).
            unfold Mem.valid_block; xomega.
         destruct H0.
         (*location ofs*)
           specialize (InValid NVB2 Max (Int.unsigned ofs)).
           remember (source (removeUndefs j12 j' prej12') m1'
                            ((Mem.nextblock m2+m)%positive)
                            (Int.unsigned ofs)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (j12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (j' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [? [? [? ?]]]]; subst.
                    exfalso. clear -H4. apply eq_sym in H4.
                    apply (add_no_neutral2 _ _ H4).
                destruct KK as [mm [? [? [? [? ?]]]]]. subst.
                   assert (mm = m).
                      clear -H4.
                      apply Pos.add_reg_l in H4.
                      subst; trivial.
                   rewrite Zplus_0_r in *. subst.
                   eapply MInj13'. apply j'b2. left. apply PERM.
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
         (*location ofs -1*)
           specialize (InValid NVB2 Max (Int.unsigned ofs-1)).
           remember (source (removeUndefs j12 j' prej12') m1'
                            ((Mem.nextblock m2+m)%positive)
                            (Int.unsigned ofs-1)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (j12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (j' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [? [? [? ?]]]]; subst.
                    exfalso. clear -H4. apply eq_sym in H4.
                    apply (add_no_neutral2 _ _ H4).
                destruct KK as [mm [? [? [? [? ?]]]]]. subst.
                   assert (mm = m).
                      clear -H4.
                      apply Pos.add_reg_l in H4.
                      subst; trivial.
                   rewrite Zplus_0_r in *. subst.
                   eapply MInj13'. apply j'b2. right. apply PERM.
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
split. trivial.
split; trivial.
split; trivial.
split; trivial.
split; trivial.
Qed.

Section MEMORY_CONSTRUCTION_II.
Variable j12 j23 j12' j23':meminj.
Variable m1 m1' m2 : mem.

Definition AccessMap_II_FUN (b2:block):
           Z -> perm_kind -> option permission :=
  if plt b2 (Mem.nextblock m2)
  then (fun ofs2 k =>
       match j23 b2 with
         None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
       | Some (b3,d3) =>
         match source j12 m1 b2 ofs2 with
             Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
           | None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
           end
        end)
  else (fun ofs2 k =>
           match source j12' m1' b2 ofs2 with
              Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None => None
          end).

Lemma mkAccessMap_II_existsT: forall N
       (VB : (Mem.nextblock m2 <= N)%positive)
       (VBJ12': forall b1 b2 delta, j12' b1 = Some (b2,delta) ->
                                   (b2 < N)%positive),
      { M : PMap.t (Z -> perm_kind -> option permission) |
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = AccessMap_II_FUN b}.
Proof. intros.
  apply (pmap_construct_c _ AccessMap_II_FUN
              N (fun ofs k => None)).
    intros. unfold AccessMap_II_FUN.
    remember (plt n (Mem.nextblock m2)) as d.
    destruct d; clear Heqd; trivial.
       exfalso. xomega.
    extensionality ofs. extensionality k.
      remember (source j12' m1' n ofs) as src.
      destruct src; trivial.
        destruct p.
        destruct (source_SomeE _ _ _ _ _ Heqsrc)
          as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
        clear Heqsrc; subst. apply eq_sym in PP. inv PP.
        apply VBJ12' in JJ.
        exfalso. xomega.
Qed.

Definition ContentMap_II_ValidBlock_FUN b2 ofs2: memval :=
   match source j12 m1 b2 ofs2 with
     Some(b1,ofs1) =>
                 match j23' b2 with
                    None => ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
                 | Some(b3,ofs3) =>
                      inject_memval j12'
                            (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
                 end
   | None => ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
   end.

Definition ContentMap_II_InvalidBlock_FUN b2 ofs2: memval :=
   match source j12' m1' b2 ofs2 with
       None => Undef
     | Some(b1,ofs1) =>
               inject_memval j12'
               (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
   end.

Definition ContentMap_II_Block_FUN b ofs : memval:=
  if plt b (Mem.nextblock m2)
  then ContentMap_II_ValidBlock_FUN b ofs
  else ContentMap_II_InvalidBlock_FUN b ofs.

Variable MINMAX_Offset: block -> option (Z * Z).
Hypothesis MINMAX: forall b2 ,
                   match MINMAX_Offset b2 with
                    Some(mn,mx) =>
                      (forall ofs, ofs < mn \/ ofs > mx ->
                        Plt b2 (Mem.nextblock m2) ->
                        ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef) /\
                      forall b1 delta, j12 b1 = Some(b2,delta) \/ j12' b1 = Some(b2,delta)->
                       forall z, z + delta < mn \/ z + delta > mx ->
                                 ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
                   | None =>
                      (Plt b2 (Mem.nextblock m2) ->
                          forall ofs, ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef)
                      /\
                       forall b1 delta, j12 b1 = Some(b2,delta) \/ j12' b1 = Some(b2,delta)->
                       forall z, ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
                    end.

Lemma CM_block_II_existsT: forall b,
      { M : ZMap.t memval |
          fst M = Undef /\
          forall ofs, ZMap.get ofs M =
                      ContentMap_II_Block_FUN b ofs}.
Proof. intros.
(*  remember (zmap_finite_c _ (PMap.get b m1'.(Mem.mem_contents))) as LH1.
  apply eq_sym in HeqLH1. destruct LH1 as [lo1 hi1]. *)
(*  specialize (zmap_finite_sound_c _ _ _ _ HeqLH1).
  intros Bounds1; clear HeqLH1.*)
  remember (zmap_finite_c _ (PMap.get b m2.(Mem.mem_contents))) as LH2.
  apply eq_sym in HeqLH2. destruct LH2 as [lo2 hi2].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH2).
  intros Bounds2; clear HeqLH2.
   assert (Undef2: fst (Mem.mem_contents m2) !! b = Undef). apply m2.
   rewrite Undef2 in *. clear Undef2.
(*assert (Undef1: fst (Mem.mem_contents m1') !! b = Undef). apply m1'.
   rewrite Undef1 in *. clear Undef1 Undef2.
*)

  specialize (MINMAX b).
  remember (MINMAX_Offset b) as MM.
  destruct MM; apply eq_sym in HeqMM.
    destruct p as [mn mx].
    destruct MINMAX as [MINMAX_A MINMAX_B]; clear MINMAX.
    destruct (zmap_construct_c _
              (ContentMap_II_Block_FUN b)
              (Z.min mn lo2)
              (Z.max mx hi2)
            Undef) as [M PM].
    intros. unfold ContentMap_II_Block_FUN; simpl.
        unfold ContentMap_II_ValidBlock_FUN.
        unfold ContentMap_II_InvalidBlock_FUN.
   destruct (plt b (Mem.nextblock m2)).
   (*validblock m2 b*)
       remember (source j12 m1 b n) as src.
       destruct src; trivial.
         destruct p0.
         destruct (source_SomeE _ _ _ _ _ Heqsrc)
           as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
          clear Heqsrc; subst. apply eq_sym in PP. inv PP.
         assert (j12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
            left; trivial.
         destruct (j23' b); trivial.
           destruct p0.
           rewrite (MINMAX_B _ _ H0 z). simpl. trivial.
           clear -H.
           destruct H.
             apply Z.min_glb_lt_iff in H. left. omega.
             assert (Z.max mx hi2 < z + dd1) by omega.
               apply Z.max_lub_lt_iff in H0. right; omega.
         apply MINMAX_A.
           clear -H. xomega.
           apply p.
        apply Bounds2.
           clear -H.
           destruct H.
             apply Z.min_glb_lt_iff in H. left. omega.
             assert (Z.max mx hi2 < n) by omega.
               apply Z.max_lub_lt_iff in H0. right; omega.

   (*invalidblock m2 b*)
       remember (source j12' m1' b n) as src.
       destruct src; trivial.
       destruct p.
         destruct (source_SomeE _ _ _ _ _ Heqsrc)
           as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
          clear Heqsrc; subst. apply eq_sym in PP. inv PP.
         assert (j12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
            right; trivial.
         rewrite (MINMAX_B _ _ H0 z). simpl. trivial.

         clear -H.
         destruct H.
           apply Z.min_glb_lt_iff in H. left. omega.
           assert (Z.max mx hi2 < z + dd1) by omega.
             apply Z.max_lub_lt_iff in H0. right; omega.

  exists M. apply PM.

(*case MINMAX_Offset b = None*)
  exists (ZMap.init Undef).
    split. reflexivity.
    destruct MINMAX as [MINMAX_A MINMAX_B]; clear MINMAX.
    intros. rewrite ZMap.gi.
    unfold ContentMap_II_Block_FUN.
    destruct (plt b (Mem.nextblock m2)).
      unfold ContentMap_II_ValidBlock_FUN.
      rewrite (MINMAX_A p).
      remember (source j12 m1 b ofs) as src.
      destruct src; trivial.
        destruct p0.
        destruct (source_SomeE _ _ _ _ _ Heqsrc)
           as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
          clear Heqsrc; subst. apply eq_sym in PP. inv PP.
         assert (j12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
            left; trivial.
        rewrite (MINMAX_B _ _ H z). simpl.
        destruct (j23' b); trivial.
           destruct p0; trivial.

    unfold ContentMap_II_InvalidBlock_FUN.
      remember (source j12' m1' b ofs) as src.
      destruct src; trivial.
        destruct p.
        destruct (source_SomeE _ _ _ _ _ Heqsrc)
           as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
          clear Heqsrc; subst. apply eq_sym in PP. inv PP.
         assert (j12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
            right; trivial.
        rewrite (MINMAX_B _ _ H z). simpl. trivial.
Qed.

Definition ContentsMap_II_FUN
           (NB2':block)
            (b:block):
            ZMap.t memval.
destruct (plt b NB2').
  apply (CM_block_II_existsT b).
apply (ZMap.init Undef).
Defined.


Lemma ContentsMap_II_existsT:
      forall (NB2':block) ,
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M =
           ContentsMap_II_FUN NB2' b}.
Proof. intros.
  apply (pmap_construct_c _ (ContentsMap_II_FUN NB2')
              NB2' (ZMap.init Undef)).
    intros. unfold ContentsMap_II_FUN. simpl.
    remember (plt n NB2') as d.
    destruct d; clear Heqd; trivial.
      exfalso. xomega.
Qed.

Definition mkII
            (NB2':block)
            (Hyp1: (Mem.nextblock m2 <= NB2')%positive)
            (Hyp2: forall (b1 b2 : block) (delta : Z),
                       j12' b1 = Some (b2, delta) -> (b2 < NB2')%positive)
           : Mem.mem'.
destruct (mkAccessMap_II_existsT NB2' Hyp1 Hyp2) as [AM [ADefault PAM]].
destruct (ContentsMap_II_existsT NB2') as [CM [CDefault PCM]].
eapply Mem.mkmem with (nextblock:=NB2')
                      (mem_access:=AM)
                      (mem_contents:=CM).
  (*access_max*)
  intros. rewrite PAM. unfold AccessMap_II_FUN.
     destruct (plt b (Mem.nextblock m2)).
     (*valid_block m2 b*)
        destruct (j23 b).
          destruct p0.
          remember (source j12 m1 b ofs) as src.
          destruct src.
             destruct p0. apply m1'.
          apply m2.
        apply m2.
     (*invalid_block m2 b*)
        remember (source j12' m1' b ofs) as src.
        destruct src.
          destruct p. apply m1'.
        reflexivity.
  (*nextblock_noaccess*)
    intros. rewrite PAM.
    unfold AccessMap_II_FUN.
    destruct (plt b (Mem.nextblock m2)).
      exfalso. apply H; clear - Hyp1 p. xomega.
    remember (source j12' m1' b ofs) as src.
    destruct src; trivial.
      destruct p.
      exfalso. apply H. clear - Heqsrc Hyp2.
      apply source_SomeE in Heqsrc.
      destruct Heqsrc as [b1 [delta [ofs1
          [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
        apply (Hyp2 _ _ _ J1).
  (*contents_default*)
    intros.
    rewrite PCM; clear PCM.
    unfold ContentsMap_II_FUN.
    destruct (plt b NB2').
     remember (CM_block_II_existsT b).
     destruct s. apply a.
    reflexivity.
Defined.

End MEMORY_CONSTRUCTION_II.

Definition minmax_at (m:mem) (j:meminj) (b2 b1: block) : option(Z * Z) :=
  match j b1
  with Some (b,delta) =>
            if peq b b2
            then match (zmap_finite_c _ (PMap.get b1 m.(Mem.mem_contents)))
                 with (mn,mx) => Some(mn+delta,mx+delta)
                 end
            else None
     | None => None
  end.

Lemma minmax_at_sound1: forall m j b2 b1 mn mx,
      Some (mn, mx) = minmax_at m j b2 b1 ->
      exists delta, j b1 = Some(b2,delta) /\
          forall z, z + delta < mn \/ z + delta > mx ->
          ZMap.get z (Mem.mem_contents m) !! b1 = Undef.
Proof. intros.
  unfold minmax_at in H.
  remember (j b1) as d.
  destruct d.
    destruct p.
    destruct (peq b b2).
      remember (zmap_finite_c memval (Mem.mem_contents m) !! b1).
      destruct p. inv H.
      exists z. split; trivial.
      intros. apply eq_sym in Heqp.
      rewrite (zmap_finite_sound_c _ _ _ _ Heqp).
      apply m. xomega.
    inv H.
   inv H.
Qed.

Lemma minmax_at_sound2: forall m j b2 b1,
      None = minmax_at m j b2 b1 ->
      forall delta, j b1 = Some(b2,delta) ->
          forall z,
          ZMap.get z (Mem.mem_contents m) !! b1 = Undef.
Proof. intros.
  unfold minmax_at in H.
  remember (j b1) as d.
  destruct d.
    destruct p. inv H0.
    destruct (peq b2 b2).
      remember (zmap_finite_c memval (Mem.mem_contents m) !! b1).
      destruct p. inv H.
    intuition.
   inv H0.
Qed.

Definition minmaxN (n:block) (m:mem) (j:meminj) (b2:block) : option (Z * Z):=
Pos.peano_rect
            (fun p => option(Z * Z))
            (minmax_at m j b2 (1%positive))
            (fun p Hp =>
               match minmax_at m j b2 (Pos.succ p)
               with Some(min1,max1) =>
                       match Hp with
                         Some(min2, max2) => Some (Zmin min1 min2, Zmax max1 max2)
                       | None => Some(min1,max1)
                       end
                  | None => Hp
               end)
            n.

Lemma minmaxN_sound: forall m j b2 n,
      match minmaxN n m j b2
      with Some(mn,mx) =>
             forall b1 delta, (b1 <= n)%positive -> j b1 = Some(b2,delta) ->
             forall z, z + delta < mn \/ z + delta > mx ->
                       ZMap.get z (Mem.mem_contents m)!!b1 = Undef
         | None => forall b1 delta, (b1 <= n)%positive -> j b1 = Some(b2,delta) ->
                   forall z, ZMap.get z (Mem.mem_contents m)!!b1 = Undef
      end.
Proof.
  intros m j b2.
apply Pos.peano_rect.
(*Base case: n = 1%positive*)
  unfold minmaxN (*, minmax_at*); simpl.
  remember (j 1%positive) as J.
  destruct J.
    destruct p.
    remember (minmax_at m j b2 1%positive) as MM.
    destruct MM.
      destruct p as [mn mx].
      intros. assert (b1 = 1%positive). xomega.
      subst. rewrite H0 in HeqJ. inv HeqJ.
      apply minmax_at_sound1 in HeqMM.
      destruct HeqMM as [dd [JJ ZZ]].
      rewrite JJ in H0. inv H0.
      apply ZZ. apply H1.
    intros. assert (b1 = 1%positive). xomega.
      subst. rewrite H0 in HeqJ. inv HeqJ.
      eapply minmax_at_sound2. apply HeqMM. apply H0.

  remember (minmax_at m j b2 1%positive) as MM.
    destruct MM.
      destruct p as [mn mx].
      apply minmax_at_sound1 in HeqMM.
      destruct HeqMM as [dd [JJ ZZ]].
      rewrite JJ in HeqJ. inv HeqJ.
    intros.
      assert (b1 = 1%positive). xomega.
      subst. rewrite H0 in HeqJ. inv HeqJ.
(*Step case*)
intros.
unfold minmaxN.
rewrite Pos.peano_rect_succ.
  remember (minmaxN p m j b2) as a.
  unfold minmaxN in Heqa. rewrite <- Heqa.
  clear Heqa.
  destruct a.
    destruct p0.
    remember (minmax_at m j b2 (Pos.succ p)) as d.
    destruct d.
      destruct p0.
      intros.
      apply Pos.le_lteq in H0.
      destruct H0; subst.
        apply (H b1 delta); trivial.
          xomega. xomega.
      apply minmax_at_sound1 in Heqd.
        destruct Heqd as [? [? ?]]; subst.
        rewrite H1 in H0. inv H0.
        apply H3. xomega.
    intros.
      apply Pos.le_lteq in H0.
      destruct H0; subst.
        apply (H b1 delta); trivial.
          xomega.
      eapply minmax_at_sound2. apply Heqd. apply H1.
  remember (minmax_at m j b2 (Pos.succ p)) as d.
    destruct d.
      destruct p0.
      intros.
      apply Pos.le_lteq in H0.
      destruct H0; subst.
        apply (H b1 delta); trivial.
          xomega.
      apply minmax_at_sound1 in Heqd.
        destruct Heqd as [? [? ?]]; subst.
        rewrite H1 in H0. inv H0.
        apply H3. xomega.
    intros.
      apply Pos.le_lteq in H0.
      destruct H0; subst.
        apply (H b1 delta); trivial.
          xomega.
      eapply minmax_at_sound2. apply Heqd. apply H1.
Qed.

Definition minmax m j (b2:block): option(Z * Z) :=
   if plt 1%positive (Mem.nextblock m)
   then minmaxN (Pos.pred (Mem.nextblock m)) m j b2
   else None.

Lemma minmax_sound: forall m j b2,
      match minmax m j b2
      with Some(mn,mx) =>
             forall b1 delta, (b1 < Mem.nextblock m)%positive ->
                    j b1 = Some(b2,delta) ->
             forall z, z + delta < mn \/ z + delta > mx ->
                       ZMap.get z (Mem.mem_contents m)!!b1 = Undef
         | None => forall b1 delta, (b1 < Mem.nextblock m)%positive ->
                   j b1 = Some(b2,delta) ->
                   forall z, ZMap.get z (Mem.mem_contents m)!!b1 = Undef
      end.
Proof. intros.
  unfold minmax.
  destruct (plt 1 (Mem.nextblock m)).
  specialize (minmaxN_sound m j b2 (Pos.pred (Mem.nextblock m))).
  intros.
  remember (minmaxN (Pos.pred (Mem.nextblock m)) m j b2) as d.
  destruct d.
    destruct p0.
    intros. apply (H b1 delta); trivial. clear - p H0.
    destruct (Pos.succ_pred_or (Mem.nextblock m)).
       rewrite H in p. xomega.
       rewrite <- H in H0. clear H.
       destruct (Plt_succ_inv _ _ H0); xomega.
  intros. apply (H b1 delta); trivial.
     clear H Heqd.
     destruct (Pos.succ_pred_or (Mem.nextblock m)).
       rewrite H in p. xomega.
       rewrite <- H in H0. clear H.
       destruct (Plt_succ_inv _ _ H0); xomega.

intros.
 xomega.
Qed.

Section MINMAX_II.
Variable j12 j12' :meminj.
Variable m1' m2: mem.

Definition MINMAX_Offset (b2:block) : option (Z * Z) :=
  if plt b2 (Mem.nextblock m2)
  then match (zmap_finite_c _ (PMap.get b2 m2.(Mem.mem_contents)))
       with (min2, max2) =>
          match minmax m1' j12 b2 with
             Some(min1, max1) =>
                  Some(Z.min min1 min2, Z.max max1 max2)
           | None => Some(min2,max2)
          end
       end
  else minmax m1' j12' b2.

Hypothesis inc12: inject_incr j12 j12'.
Hypothesis VBj12'_1: forall b1 b2 delta,
                     j12' b1 = Some (b2, delta) ->
                     Mem.valid_block m1' b1.
Hypothesis JJ: forall b1 b2 delta,
                       j12' b1 = Some (b2, delta) ->
                       Mem.valid_block m2 b2 ->
                       j12 b1 = Some (b2, delta).

Lemma MINMAX: forall b2 ,
        match MINMAX_Offset b2 with
          Some(mn,mx) =>
              (forall ofs, ofs < mn \/ ofs > mx ->
                  Plt b2 (Mem.nextblock m2) ->
                  ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef) /\
              forall b1 delta, j12 b1 = Some(b2,delta) \/
                               j12' b1 = Some(b2,delta)->
                forall z, z + delta < mn \/ z + delta > mx ->
                       ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
        | None =>
             (Plt b2 (Mem.nextblock m2) ->
                forall ofs, ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef)
             /\ forall b1 delta,
                     j12 b1 = Some(b2,delta) \/ j12' b1 = Some(b2,delta)->
                 forall z, ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
         end.
Proof. intros.
unfold MINMAX_Offset.
remember (zmap_finite_c memval (Mem.mem_contents m2) !! b2) as MM2.
destruct MM2 as [min2 max2]. apply eq_sym in HeqMM2.
destruct (plt b2 (Mem.nextblock m2)).
  specialize (minmax_sound m1' j12 b2).
  remember (minmax m1' j12 b2) as MM; intros.
  destruct MM.
    destruct p0 as [mn mx].
    split; intros.
       apply zmap_finite_sound_c with (n:=ofs) in HeqMM2.
       rewrite HeqMM2. apply m2.
       clear - H0. xomega.
    intros. assert (j12 b1 = Some(b2,delta)).
              destruct H0. trivial. apply (JJ _ _ _ H0 p).
            apply (H b1 delta); trivial.
              apply inc12 in H2. apply (VBj12'_1 _ _ _ H2).
            clear - H1. xomega.
  split; intros.
       apply zmap_finite_sound_c with (n:=ofs) in HeqMM2.
       rewrite HeqMM2. apply m2.
       clear - H0. xomega.
     assert (j12 b1 = Some(b2,delta)).
              destruct H0. trivial. apply (JJ _ _ _ H0 p).
     apply (H b1 delta); trivial.
       apply inc12 in H2. apply (VBj12'_1 _ _ _ H2).
specialize (minmax_sound m1' j12' b2).
  remember (minmax m1' j12' b2) as MM; intros.
  destruct MM.
    destruct p as [mn mx].
    split; intros. contradiction.
    assert (j12' b1 = Some(b2,delta)).
      destruct H0. apply inc12; assumption. assumption.
    apply (H b1 delta); trivial.
      apply (VBj12'_1 _ _ _ H2).
  split; intros. contradiction.
     assert (j12' b1 = Some(b2,delta)).
       destruct H0. apply inc12; assumption. assumption.
     apply (H b1 delta); trivial.
       apply (VBj12'_1 _ _ _ H1).
Qed.

End MINMAX_II.

(*prooves the claim of interpolate_II, plus properties on j12' and j23'
  corresponding to mkInjections_3 and mkInjections_4. This is usefule for
  proving Forward_simulations_trans.initial_inject_split in the sufficiently
  strong form needed to prove that memninj_preserves splits, as required for
  transitivity_II.*)
Lemma interpolate_II_HeqMKI: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                  (Fwd1: mem_forward m1 m1') j23 m3
                  (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                  j' (MInj13': Mem.inject j' m1' m3')
                  (InjIncr: inject_incr (compose_meminj j12 j23) j')
                  (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                  (Unch11': Mem.unchanged_on
                            (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                  (Unch33': Mem.unchanged_on
                        (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3'),
         exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                   inject_incr j12 j12' /\ inject_incr j23 j23' /\
                   Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\
                   Mem.inject j23' m2' m3' /\
                   Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                   inject_separated j12 j12' m1 m2 /\
                   inject_separated j23 j23' m2 m3 /\
                   Mem.unchanged_on (loc_unmapped j23) m2 m2' /\
                   Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                   (forall b1 b2 ofs2, j12' b1 = Some(b2,ofs2) ->
                     (j12 b1 = Some (b2,ofs2)) \/
                     (b1 = Mem.nextblock m1 /\ b2 = Mem.nextblock m2 /\ ofs2 = 0) \/
                     (exists m, (b1 = Mem.nextblock m1 + m /\ b2=Mem.nextblock m2 + m)%positive /\ ofs2=0)) /\
                   (forall b2 b3 ofs3, j23' b2 = Some(b3,ofs3) ->
                     (j23 b2 = Some (b3,ofs3)) \/
                     (b2 = Mem.nextblock m2 /\ j' (Mem.nextblock m1) = Some(b3,ofs3)) \/
                     (exists m, (b2 = Mem.nextblock m2 + m)%positive /\
                            j' ((Mem.nextblock m1+m)%positive) = Some(b3,ofs3))).
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
  assert (VBj': forall b1 b3 ofs3, j' b1 = Some (b3, ofs3) ->
             (b1 < Mem.nextblock m1')%positive).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj13').

destruct (mkInjections_0  _ _ _ _ _ _ _ _ _ _ HeqMKI)
   as [HH | HH].
destruct HH as [? [? [? [? ?]]]]. subst.
  assert (Mem.nextblock m1' = Mem.nextblock m1).
      apply forward_nextblock in Fwd1. eapply Pos.le_antisym; assumption.
  rewrite H0 in *.
  assert (VB1': forall (b1 b2 : block) (delta : Z),
             j12 b1 = Some (b2, delta) -> Mem.valid_block m1' b1).
     intros. unfold Mem.valid_block. rewrite H0. apply (VBj12_1 _ _ _ H1).
  assert (JJ12: forall (b1 b2 : block) (delta : Z),
                j12 b1 = Some (b2, delta) ->
                Mem.valid_block m2 b2 -> j12 b1 = Some (b2, delta)).
     auto.
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').
  exists (mkII j12 j23 j12 j23 m1 m1' m2
               (MINMAX_Offset j12 j12 m1' m2)
               (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12) _ (Pos.le_refl _) VBj12_2).
  exists (removeUndefs j12 j' j12) . exists j23.
  assert (RUD: removeUndefs j12 j' j12 = j12).
    extensionality b.
    unfold removeUndefs.
    remember (j12 b) as d.
    destruct d.
      destruct p. trivial.
    destruct (j' b); trivial.
      destruct p; trivial.
  rewrite RUD in *.
  destruct (II_ok m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33' _ _ _ _
                             HeqMKI _ (eq_refl _)
             (mkII j12 j23 j12 j23 m1 m1' m2
               (MINMAX_Offset j12 j12 m1' m2)
               (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12) _ (Pos.le_refl _) VBj12_2))
     as [A [B [C [D [E [F [G [I [J [K L]]]]]]]]]]; trivial.
   (*nextblock*)
     unfold mkII.
     destruct (mkAccessMap_II_existsT j12 j23 j12 m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 j12 j23 m1 m1' m2
                (MINMAX_Offset j12 j12 m1' m2)
                (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                (Mem.nextblock m2))
       as [CM [CDefault PCM]].
     simpl. reflexivity.
   (*ContentMapOK*)
     rewrite RUD in *.
     unfold Content_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 j12 m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 j12 j23 m1 m1' m2
                 (MINMAX_Offset j12 j12 m1' m2)
                 (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                 (Mem.nextblock m2))
               as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PCM; clear PCM.
        unfold ContentsMap_II_FUN.
        destruct (CM_block_II_existsT j12 j12 j23 m1 m1' m2
                    (MINMAX_Offset j12 j12 m1' m2)
                    (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                    b2)
                 as [B [FB HB]].
        simpl in *.
        destruct (plt b2 (Mem.nextblock m2)).
           split; intros.
             remember (source j12 m1 b2 ofs2) as src.
             destruct src.
               destruct p0. rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc.
               destruct (j23 b2); trivial.
                 destruct p1. trivial.
             rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc. trivial.
          split; intros. contradiction.
          apply FB.
        (*invalid m2 b2*)
          split; intros; try contradiction.
          split; intros.
             remember (source j12 m1' b2 ofs2) as src.
             destruct src.
               destruct p.
               apply source_SomeE in Heqsrc.
               destruct Heqsrc as [b1 [delta [ofs1
                  [PBO [Bounds [J1 [P1 Off2]]]]]]].
               clear ID RUD. inv PBO.
               exfalso. apply (H1 (VBj12_2 _ _ _ J1)).
             rewrite ZMap.gi. trivial.
           reflexivity.
   (*AccessMapOK*)
     rewrite RUD in *.
     unfold AccessMap_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 j12 m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 j12 j23 m1 m1' m2
                  (MINMAX_Offset j12 j12 m1' m2)
                  (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                  (Mem.nextblock m2))
              as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PAM; clear PAM.
        unfold AccessMap_II_FUN.
        simpl in *.
        destruct (plt b2 (Mem.nextblock m2)).
           split; intros; try contradiction.
             remember (source j12 m1 b2 ofs2) as src.
             destruct src.
               destruct p0.
               destruct (j23 b2); trivial.
                 destruct p0. trivial.
             destruct (j23 b2); trivial.
                 destruct p0. trivial.
         split; intros; try contradiction.
             remember (source j12 m1' b2 ofs2) as src.
             destruct src; trivial.
               destruct p; trivial.
  rewrite RUD in *.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split. apply (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI).
  apply (mkInjections_4 _ _ _ _ _ _ _ _ _ _ HeqMKI).
(*CASE WHERE m2' actually has additional blocks*)
destruct HH as [N [? [? [? ?]]]]. subst.
  rewrite <- H1 in *.
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').
  assert (VB2: (Mem.nextblock m2 <= Mem.nextblock m2 + Pos.of_nat N)%positive).
    xomega.
  assert (VBj12: forall (b1 b2 : block) (ofs2 : Z),
                 j12 b1 = Some (b2, ofs2) ->
                 (b1 < Mem.nextblock m1)%positive /\ (b2 < Mem.nextblock m2)%positive).
     intros; split. apply (VBj12_1 _ _ _ H0). apply (VBj12_2 _ _ _ H0).
  assert (RUD:= RU_D _ _ inc12 j').
  assert (VBj12'_2: forall (b1 b2 : block) (delta : Z),
        (removeUndefs j12 j' j12') b1 = Some (b2, delta) ->
        (b2 < Mem.nextblock m2 + Pos.of_nat N)%positive).
    intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]].  xomega.
       destruct KK as [? [? [? [? U]]]]; apply U.
       destruct KK as [M [? [? [? [? U]]]]]; apply U.
  assert (INC12RU: inject_incr j12 (removeUndefs j12 j' j12')).
     unfold removeUndefs. intros b; intros.
     rewrite H0. trivial.
  assert (VBj12'_1: forall (b1 b2 : block) (delta : Z),
        (removeUndefs j12 j' j12') b1 = Some (b2, delta) ->
        (b1 < Mem.nextblock m1 + Pos.of_nat N)%positive).
    intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]].  xomega.
       destruct KK as [? [? [? [U ?]]]]; apply U.
       destruct KK as [M [? [? [? [U ?]]]]]; apply U.
  assert (VB1': forall (b1 b2 : block) (delta : Z),
               removeUndefs j12 j' j12' b1 = Some (b2, delta) ->
               Mem.valid_block m1' b1).
    intros. unfold Mem.valid_block. rewrite <- H1.
            eapply VBj12'_1; eassumption.
  assert (JJ12: forall (b1 b2 : block) (delta : Z),
                removeUndefs j12 j' j12' b1 = Some (b2, delta) ->
                Mem.valid_block m2 b2 -> j12 b1 = Some (b2, delta)).
     intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]]. assumption.
       destruct KK as [? [? [? [U ?]]]]. clear ID; subst.
         unfold Mem.valid_block in H2. xomega.
       destruct KK as [M [? [? [? [U ?]]]]]. clear ID; subst.
         unfold Mem.valid_block in H2. xomega.
 exists (mkII j12 j23 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
                 _ VB2 VBj12'_2).
  exists (removeUndefs j12 j' j12') . exists j23'.

  destruct (II_ok m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33' _ _ _ _
                             HeqMKI _ (eq_refl _)
               (mkII j12 j23 (removeUndefs j12 j' j12') j23' m1 m1' m2
                     (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
                     (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
                      _ VB2 VBj12'_2))
     as [A [B [C [D [E [F [G [I [J [K L]]]]]]]]]]; trivial.
   (*nextblock*)
     unfold mkII.
     destruct (mkAccessMap_II_existsT j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2)
         as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
               (Mem.nextblock m2 + Pos.of_nat N)%positive)
           as [CM [CDefault PCM]].
     simpl. reflexivity.
   (*ContentMapOK*)
     unfold Content_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2)
         as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
               (Mem.nextblock m2 + Pos.of_nat N)%positive)
           as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PCM; clear PCM.
        unfold ContentsMap_II_FUN.
        destruct (CM_block_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
                b2) as [B [FB HB]].
        simpl in *.
        destruct (plt b2 ((Mem.nextblock m2 + Pos.of_nat N)%positive)).
           split; intros.
             remember (source j12 m1 b2 ofs2) as src.
             destruct src.
               destruct p0. rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc.
               destruct (source_SomeE _ _ _ _ _ Heqsrc)
                  as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
                 clear Heqsrc; clear ID. subst. apply eq_sym in PP. inv PP.
               destruct (j23' b2); trivial.
                 destruct p1. simpl. trivial.
             rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc. trivial.
          split; intros.
             remember (source (removeUndefs j12 j' j12') m1' b2 ofs2) as src.
             destruct src.
               destruct p0. rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_InvalidBlock_FUN.
               rewrite <- Heqsrc. trivial.
             rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_InvalidBlock_FUN.
               rewrite <- Heqsrc. trivial.
          apply FB.
        (*invalid m2' b2*)
          split; intros. exfalso. clear - H0 n VB2. unfold Mem.valid_block in H0. xomega.
          split; intros.
             remember (source (removeUndefs j12 j' j12') m1' b2 ofs2) as src.
             destruct src.
               destruct p.
               apply source_SomeE in Heqsrc.
               destruct Heqsrc as [b1 [delta [ofs1
                  [PBO [Bounds [J1 [P1 Off2]]]]]]].
               clear ID. inv PBO.
               exfalso. apply (n (VBj12'_2 _ _ _ J1)).
             rewrite ZMap.gi. trivial.
           reflexivity.
   (*AccessMapOK*)
     unfold AccessMap_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2)
         as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
               (Mem.nextblock m2 + Pos.of_nat N)%positive)
           as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PAM; clear PAM.
        unfold AccessMap_II_FUN.
        simpl in *.
        destruct (plt b2 (Mem.nextblock m2)).
           split; intros; try contradiction.
             destruct (j23 b2); trivial.
               destruct p0.
               remember (source j12 m1 b2 ofs2) as src.
               destruct src; trivial.
               destruct p0; trivial.
         split; intros; try contradiction.
             remember (source (removeUndefs j12 j' j12') m1' b2 ofs2) as src.
             destruct src; trivial.
               destruct p; trivial.

  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split. intros. eapply (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI).
                 apply RUD. apply H0.
  apply (mkInjections_4 _ _ _ _ _ _ _ _ _ _ HeqMKI).
Qed.

Lemma interpolate_II: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                  (Fwd1: mem_forward m1 m1') j23 m3
                  (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                  j' (MInj13': Mem.inject j' m1' m3')
                  (InjIncr: inject_incr (compose_meminj j12 j23) j')
                  (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                  (Unch11': Mem.unchanged_on
                            (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                  (Unch33': Mem.unchanged_on
                        (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3'),
         exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                   inject_incr j12 j12' /\ inject_incr j23 j23' /\
                   Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\
                   Mem.inject j23' m2' m3' /\
                   Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                   inject_separated j12 j12' m1 m2 /\
                   inject_separated j23 j23' m2 m3 /\
                   Mem.unchanged_on (loc_unmapped j23) m2 m2' /\
                   Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'.
Proof. intros.
  destruct (interpolate_II_HeqMKI _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ Fwd3 _ MInj13'
                    InjIncr InjSep Unch11' Unch33')
  as [m2' [j12' [j23' [A [B [C [D [E [F [G [H [I [J [K _]]]]]]]]]]]]]].
  exists m2', j12', j23'. intuition.
Qed.

(*Another variant, needed in effect_simulations_trans.*)
Lemma interpolate_II_strong: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                  (Fwd1: mem_forward m1 m1') j23 m3
                  (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                  j' (MInj13': Mem.inject j' m1' m3')
                  (InjIncr: inject_incr (compose_meminj j12 j23) j')
                  (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                  (Unch11': Mem.unchanged_on
                            (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                  (Unch33': Mem.unchanged_on
                        (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3'),
         exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                   (forall b1 b2 d1, j12' b1 = Some(b2,d1) ->
                       j12 b1 = Some(b2,d1) \/
                       exists b3 d, j' b1 = Some(b3,d)) /\
                   (forall b2 b3 d2, j23' b2 = Some(b3,d2) ->
                       j23 b2 = Some(b3,d2) \/
                       exists b1 d, j' b1 = Some(b3,d)) /\
                   inject_incr j12 j12' /\ inject_incr j23 j23' /\
                   Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\
                   Mem.inject j23' m2' m3' /\
                   Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                   inject_separated j12 j12' m1 m2 /\
                   inject_separated j23 j23' m2 m3 /\
                   Mem.unchanged_on (loc_unmapped j23) m2 m2' /\
                   Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'.
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
  assert (VBj': forall b1 b3 ofs3, j' b1 = Some (b3, ofs3) ->
             (b1 < Mem.nextblock m1')%positive).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj13').

destruct (mkInjections_0  _ _ _ _ _ _ _ _ _ _ HeqMKI)
   as [HH | HH].
destruct HH as [? [? [? [? ?]]]]. subst.
  assert (Mem.nextblock m1' = Mem.nextblock m1).
      apply forward_nextblock in Fwd1. eapply Pos.le_antisym; assumption.
  rewrite H0 in *.
  assert (VB1': forall (b1 b2 : block) (delta : Z),
             j12 b1 = Some (b2, delta) -> Mem.valid_block m1' b1).
     intros. unfold Mem.valid_block. rewrite H0. apply (VBj12_1 _ _ _ H1).
  assert (JJ12: forall (b1 b2 : block) (delta : Z),
                j12 b1 = Some (b2, delta) ->
                Mem.valid_block m2 b2 -> j12 b1 = Some (b2, delta)).
     auto.
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').
  exists (mkII j12 j23 j12 j23 m1 m1' m2
               (MINMAX_Offset j12 j12 m1' m2)
               (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12) _ (Pos.le_refl _) VBj12_2).
  exists (removeUndefs j12 j' j12) . exists j23.
  assert (RUD: removeUndefs j12 j' j12 = j12).
    extensionality b.
    unfold removeUndefs.
    remember (j12 b) as d.
    destruct d.
      destruct p. trivial.
    destruct (j' b); trivial.
      destruct p; trivial.
  rewrite RUD in *.
  destruct (II_ok m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33' _ _ _ _
                             HeqMKI _ (eq_refl _)
             (mkII j12 j23 j12 j23 m1 m1' m2
               (MINMAX_Offset j12 j12 m1' m2)
               (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12) _ (Pos.le_refl _) VBj12_2))
     as [A [B [C [D [E [F [G [I [J [K L]]]]]]]]]]; trivial.
   (*nextblock*)
     unfold mkII.
     destruct (mkAccessMap_II_existsT j12 j23 j12 m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 j12 j23 m1 m1' m2
                (MINMAX_Offset j12 j12 m1' m2)
                (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                (Mem.nextblock m2))
       as [CM [CDefault PCM]].
     simpl. reflexivity.
   (*ContentMapOK*)
     rewrite RUD in *.
     unfold Content_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 j12 m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 j12 j23 m1 m1' m2
                 (MINMAX_Offset j12 j12 m1' m2)
                 (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                 (Mem.nextblock m2))
               as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PCM; clear PCM.
        unfold ContentsMap_II_FUN.
        destruct (CM_block_II_existsT j12 j12 j23 m1 m1' m2
                    (MINMAX_Offset j12 j12 m1' m2)
                    (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                    b2)
                 as [B [FB HB]].
        simpl in *.
        destruct (plt b2 (Mem.nextblock m2)).
           split; intros.
             remember (source j12 m1 b2 ofs2) as src.
             destruct src.
               destruct p0. rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc.
               destruct (j23 b2); trivial.
                 destruct p1. trivial.
             rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc. trivial.
          split; intros. contradiction.
          apply FB.
        (*invalid m2 b2*)
          split; intros; try contradiction.
          split; intros.
             remember (source j12 m1' b2 ofs2) as src.
             destruct src.
               destruct p.
               apply source_SomeE in Heqsrc.
               destruct Heqsrc as [b1 [delta [ofs1
                  [PBO [Bounds [J1 [P1 Off2]]]]]]].
               clear ID RUD. inv PBO.
               exfalso. apply (H1 (VBj12_2 _ _ _ J1)).
             rewrite ZMap.gi. trivial.
           reflexivity.
   (*AccessMapOK*)
     rewrite RUD in *.
     unfold AccessMap_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 j12 m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 j12 j23 m1 m1' m2
                  (MINMAX_Offset j12 j12 m1' m2)
                  (MINMAX j12 j12 m1' m2 inc12 VB1' JJ12)
                  (Mem.nextblock m2))
              as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PAM; clear PAM.
        unfold AccessMap_II_FUN.
        simpl in *.
        destruct (plt b2 (Mem.nextblock m2)).
           split; intros; try contradiction.
             remember (source j12 m1 b2 ofs2) as src.
             destruct src.
               destruct p0.
               destruct (j23 b2); trivial.
                 destruct p0. trivial.
             destruct (j23 b2); trivial.
                 destruct p0. trivial.
         split; intros; try contradiction.
             remember (source j12 m1' b2 ofs2) as src.
             destruct src; trivial.
               destruct p; trivial.
  rewrite RUD in *.
  split; trivial.
  split. intros. left; trivial.
  split. intros. left; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
(*CASE WHERE m2' actually has additional blocks*)
destruct HH as [N [? [? [? ?]]]]. subst.
  rewrite <- H1 in *.
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').
  assert (VB2: (Mem.nextblock m2 <= Mem.nextblock m2 + Pos.of_nat N)%positive).
    xomega.
  assert (VBj12: forall (b1 b2 : block) (ofs2 : Z),
                 j12 b1 = Some (b2, ofs2) ->
                 (b1 < Mem.nextblock m1)%positive /\ (b2 < Mem.nextblock m2)%positive).
     intros; split. apply (VBj12_1 _ _ _ H0). apply (VBj12_2 _ _ _ H0).
  assert (RUD:= RU_D _ _ inc12 j').
  assert (VBj12'_2: forall (b1 b2 : block) (delta : Z),
        (removeUndefs j12 j' j12') b1 = Some (b2, delta) ->
        (b2 < Mem.nextblock m2 + Pos.of_nat N)%positive).
    intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]].  xomega.
       destruct KK as [? [? [? [? U]]]]; apply U.
       destruct KK as [M [? [? [? [? U]]]]]; apply U.
  assert (INC12RU: inject_incr j12 (removeUndefs j12 j' j12')).
     unfold removeUndefs. intros b; intros.
     rewrite H0. trivial.
  assert (VBj12'_1: forall (b1 b2 : block) (delta : Z),
        (removeUndefs j12 j' j12') b1 = Some (b2, delta) ->
        (b1 < Mem.nextblock m1 + Pos.of_nat N)%positive).
    intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]].  xomega.
       destruct KK as [? [? [? [U ?]]]]; apply U.
       destruct KK as [M [? [? [? [U ?]]]]]; apply U.
  assert (VB1': forall (b1 b2 : block) (delta : Z),
               removeUndefs j12 j' j12' b1 = Some (b2, delta) ->
               Mem.valid_block m1' b1).
    intros. unfold Mem.valid_block. rewrite <- H1.
            eapply VBj12'_1; eassumption.
  assert (JJ12: forall (b1 b2 : block) (delta : Z),
                removeUndefs j12 j' j12' b1 = Some (b2, delta) ->
                Mem.valid_block m2 b2 -> j12 b1 = Some (b2, delta)).
     intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]]. assumption.
       destruct KK as [? [? [? [U ?]]]]. clear ID; subst.
         unfold Mem.valid_block in H2. xomega.
       destruct KK as [M [? [? [? [U ?]]]]]. clear ID; subst.
         unfold Mem.valid_block in H2. xomega.
 exists (mkII j12 j23 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
                 _ VB2 VBj12'_2).
  exists (removeUndefs j12 j' j12') . exists j23'.

  destruct (II_ok m1 m2 j12 MInj12 m1' Fwd1 j23 m3
                             MInj23 m3' Fwd3
                             j' MInj13'
                             InjIncr
                             InjSep
                             Unch11'
                             Unch33' _ _ _ _
                             HeqMKI _ (eq_refl _)
               (mkII j12 j23 (removeUndefs j12 j' j12') j23' m1 m1' m2
                     (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
                     (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
                      _ VB2 VBj12'_2))
     as [A [B [C [D [E [F [G [I [J [K L]]]]]]]]]]; trivial.
   (*nextblock*)
     unfold mkII.
     destruct (mkAccessMap_II_existsT j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2)
         as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
               (Mem.nextblock m2 + Pos.of_nat N)%positive)
           as [CM [CDefault PCM]].
     simpl. reflexivity.
   (*ContentMapOK*)
     unfold Content_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2)
         as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
               (Mem.nextblock m2 + Pos.of_nat N)%positive)
           as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PCM; clear PCM.
        unfold ContentsMap_II_FUN.
        destruct (CM_block_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
                b2) as [B [FB HB]].
        simpl in *.
        destruct (plt b2 ((Mem.nextblock m2 + Pos.of_nat N)%positive)).
           split; intros.
             remember (source j12 m1 b2 ofs2) as src.
             destruct src.
               destruct p0. rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc.
               destruct (source_SomeE _ _ _ _ _ Heqsrc)
                  as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
                 clear Heqsrc; clear ID. subst. apply eq_sym in PP. inv PP.
               destruct (j23' b2); trivial.
                 destruct p1. simpl. trivial.
             rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_ValidBlock_FUN.
               rewrite <- Heqsrc. trivial.
          split; intros.
             remember (source (removeUndefs j12 j' j12') m1' b2 ofs2) as src.
             destruct src.
               destruct p0. rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_InvalidBlock_FUN.
               rewrite <- Heqsrc. trivial.
             rewrite HB.
               unfold ContentMap_II_Block_FUN.
               destruct (plt b2 (Mem.nextblock m2)); try contradiction.
               unfold ContentMap_II_InvalidBlock_FUN.
               rewrite <- Heqsrc. trivial.
          apply FB.
        (*invalid m2' b2*)
          split; intros. exfalso. clear - H0 n VB2. unfold Mem.valid_block in H0. xomega.
          split; intros.
             remember (source (removeUndefs j12 j' j12') m1' b2 ofs2) as src.
             destruct src.
               destruct p.
               apply source_SomeE in Heqsrc.
               destruct Heqsrc as [b1 [delta [ofs1
                  [PBO [Bounds [J1 [P1 Off2]]]]]]].
               clear ID. inv PBO.
               exfalso. apply (n (VBj12'_2 _ _ _ J1)).
             rewrite ZMap.gi. trivial.
           reflexivity.
   (*AccessMapOK*)
     unfold AccessMap_II_Property, mkII.
     destruct (mkAccessMap_II_existsT j12 j23 (removeUndefs j12 j' j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2)
         as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_II_existsT j12 (removeUndefs j12 j' j12') j23' m1 m1' m2
               (MINMAX_Offset j12 (removeUndefs j12 j' j12') m1' m2)
               (MINMAX j12 (removeUndefs j12 j' j12') m1' m2 INC12RU VB1' JJ12)
               (Mem.nextblock m2 + Pos.of_nat N)%positive)
           as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PAM; clear PAM.
        unfold AccessMap_II_FUN.
        simpl in *.
        destruct (plt b2 (Mem.nextblock m2)).
           split; intros; try contradiction.
             destruct (j23 b2); trivial.
               destruct p0.
               remember (source j12 m1 b2 ofs2) as src.
               destruct src; trivial.
               destruct p0; trivial.
         split; intros; try contradiction.
             remember (source (removeUndefs j12 j' j12') m1' b2 ofs2) as src.
             destruct src; trivial.
               destruct p; trivial.

  split; trivial.
  split. intros. unfold removeUndefs in H0.
     remember (j12 b1)  as d.
     destruct d; apply eq_sym in Heqd.
       destruct p. left; trivial.
     right. destruct (j' b1). destruct p. exists b, z; trivial. inv H0.
  split. intros.
     remember (j23 b2) as d. rewrite A in *; clear A.
     destruct d; try (left; reflexivity); apply eq_sym in Heqd.
     destruct p. rewrite (C _ _ _ Heqd) in H0. left; trivial.
     right. destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23 _ _ _ H0) as [[J23 _] | [HEQ |HEQ]].
        rewrite J23 in Heqd. inv Heqd.
        destruct HEQ as [? [? ?]]; subst. eexists; eexists; eassumption.
        destruct HEQ as [mm [? [? ?]]]; subst. eexists; eexists; eassumption.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
Qed.


