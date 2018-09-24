Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.
(* Require Export compcert.lib.Coqlib. *)

Require Import VST.concurrency.sepcomp. Import SepComp.

Require Import VST.concurrency.pos.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.TheSchedule.
Require Import VST.concurrency.konig.
Require Import VST.concurrency.addressFiniteMap. (*The finite maps*)
Require Import VST.concurrency.pos.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permjoin_def.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import VST.concurrency.ssromega. (*omega in ssrnat *)

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.permissions.
Require Import VST.concurrency.threadPool.

Require Import compcert.common.Memory. (*for Mem.perm_order'' *)
Set Bullet Behavior "Strict Subproofs".


Definition map_leq {A B} (m1: PTree.t A)(m2: PTree.t B): Prop :=
  forall p, m1 ! p -> m2 ! p.

Lemma map_leq_apply:
  forall {A B} (m1: PTree.t A)(m2: PTree.t B) p f1,
    map_leq m1 m2 ->
    m1 ! p = Some f1 -> exists f2, m2 ! p = Some f2.
Proof.
  move => A B m1 m2 p f1.
  rewrite /map_leq => /(_ p) Mle AA.
  rewrite AA in Mle. specialize (Mle ltac:(auto)).
  destruct (m2 ! p) as [f2|]; try solve[inversion Mle].
  exists f2; auto.
Qed.

Lemma treemap_sub_map: forall {A B} (f: positive -> B -> A) m2,
    map_leq (PTree.map f m2) m2.
Proof.
  move => A B f m2 p.
  rewrite PTree.gmap.
  destruct (m2 ! p) eqn:m2p; auto; intros HH; inversion HH.
Qed.

Definition map_empty_def {A} (m1: PMap.t (Z -> option A)):=
  m1.1 = fun _ => None.

Definition fun_leq' {A B} (f1: Z -> option A) (f2: Z -> option B): Prop :=
  forall p, f1 p -> f2 p.

Definition fun_leq {A B} (o1: option (Z -> option A)) (o2: option (Z -> option B)): Prop :=
  match o1, o2 with
  | Some f1, Some f2 => fun_leq' f1 f2
  | None, None => True
  | _, _ => False
  end.

Definition option_eq {A B} (a:option A) (b: option B): Prop :=
  match a, b with
  | Some _ , Some _ => True
  | None, None => True
  | _, _ => False
  end.

Definition bounded_nat_func_aux {A} (f: nat -> option A) hi: Prop :=
  (forall p, (p >= hi )%nat -> f p = None).

Definition bounded_nat_func' {A} (f: nat -> option A) hi: Prop :=
  (forall p, (p > hi )%nat -> f p = None).

Definition bounded_func' {A} (f: Z -> option A) hi lo: Prop :=
  (forall p, (p > hi )%Z -> f p = None) /\
  (forall p, (p < lo)%Z -> f p = None).

Definition bounded_func_op {A} (f: option (Z -> option A)) hi lo: Prop :=
  match f with
  | Some f' => bounded_func' f' hi lo
  | None => True
  end.

Definition bounded_func {A} (f: Z -> option A): Prop :=
  exists hi lo,
  bounded_func' f hi lo.

Definition bounded_map {A} (m: PTree.t (Z -> option A)):=
  forall p f, m ! p = Some f -> bounded_func f.

Fixpoint strong_tree_leq {A B}
         (t1: PTree.t A) (t2: PTree.t B)
         (leq: option A -> option B -> Prop):=
  match t1, t2 with
  | PTree.Leaf, PTree.Leaf => True
  | PTree.Node l1 o1 r1, PTree.Node l2 o2 r2 =>
    leq o1 o2 /\
    strong_tree_leq l1 l2 leq /\
    strong_tree_leq r1 r2 leq
  | _, _ => False
  end.

Definition same_shape {A B} (m1: PTree.t (Z -> option A))(m2: PTree.t (Z -> option B)):=
  strong_tree_leq m1 m2 option_eq.

Definition sub_map' {A B} (m1: PTree.t (Z -> option A))(m2: PTree.t (Z -> option B)):=
  forall p f1, m1 ! p = Some f1 ->
          exists f2, m2 ! p = Some f2 /\ fun_leq' f1 f2.

Definition sub_map {A B} (m1: PTree.t (Z -> option A))(m2: PTree.t (Z -> option B)):=
  strong_tree_leq m1 m2 fun_leq.

Lemma sub_map_and_shape:
  forall { A B} m1 m2,
  @same_shape A B m1 m2 ->
  sub_map' m1 m2 ->
  sub_map m1 m2.
Proof.
  induction m1.
  - intros.
    destruct m2; inversion H.
    auto.
  - intros.
    rewrite /sub_map /=.
    destruct m2; try inversion H.
    split; [|split].
    + destruct o as [o|].
      2: destruct o0; inversion H1; auto.
      specialize (H0 1%positive o ltac:(auto)).
      destruct o0; try solve [inversion H1].
      destruct H0 as [f [ISo LEQ]].
      inversion ISo.
      auto.
    + destruct H as [AA [BB CC]].
      eapply IHm1_1; eauto.
      move => b f HH.
      move: H0 => /(_  (b~0)%positive f HH) //.
    + destruct H as [AA [BB CC]].
      eapply IHm1_2; eauto.
      move => b f HH.
      move: H0 => /(_  (b~1)%positive f HH) //.
Qed.

Definition nat_to_perm (i:nat) :=
  (match i with
  | 0 => Some None
  | 1 => Some (Some Nonempty)
  | 2 => Some (Some Readable)
  | 3 => Some (Some Writable)
  | 4 => Some (Some Freeable)
  | _ => None
  end)%nat.

Definition perm_to_nat (p: option (option permission)) :=
  match p with
  | Some (None) => 0
  | Some (Some Nonempty) => 1
  | Some (Some Readable) => 2
  | Some (Some Writable) => 3
  | Some (Some Freeable) => 4
  | None => 5
  end.

Definition nat_to_perm_simpl (i:nat) :=
  (match i with
  | 0 => None
  | 1 => Some Nonempty
  | 2 => Some Readable
  | 3 => Some Writable
  | 4 => Some Freeable
  | _ => None
  end)%nat.

Definition perm_to_nat_simpl (p: option permission) :=
  match p with
  | None => 0
  | Some Nonempty => 1
  | Some Readable => 2
  | Some Writable => 3
  | Some Freeable => 4
  end.
Lemma perm_to_nat_bound:
  forall p,
    perm_to_nat p < 6.
Proof.
  intros p.
  destruct p as [p|];
    try destruct p as [p|]; try destruct p; compute; auto.
Qed.

Lemma perm_to_nat_bound_simpl:
  forall p,
    perm_to_nat_simpl p < 5.
Proof.
  intros p.
  destruct p as [p|];
    try destruct p; compute; auto.
Qed.

Lemma nat_to_perm_perm_to_nat:
  forall p,
    nat_to_perm (perm_to_nat p) = p.
Proof.
  intros p.
  destruct p as [p|];
    try destruct p as [p|];
    try destruct p;
    reflexivity.
Qed.

Lemma nat_to_perm_perm_to_nat_simpl:
  forall p,
    nat_to_perm_simpl (perm_to_nat_simpl p) = p.
Proof.
  intros p.
  destruct p as [p|];
    try destruct p;
    reflexivity.
Qed.

Lemma finite_bounded_nat_aux_func:
  forall hi ,
    konig.finite
      ( fun f:nat -> option (option permission) => bounded_nat_func_aux f hi).
Proof.

   intros hi.
   pose (K:= perm_to_nat).
   induction hi.
   - exists 1%nat.
     exists (fun x _ => None).
     intros.
     exists 0%nat.
     split; auto.

     extensionality b.
     symmetry.
     apply H.
     apply /leP. omega.

   - destruct IHhi as [N [FN H]].
     exists (6*N)%nat.
     exists (fun x i => if (Nat.eq_dec i hi) then
                       nat_to_perm (Nat.modulo x 6)
                else FN (Nat.div x 6) i).
     move=> f HH.
     specialize (H (fun n => if (Nat.eq_dec n hi) then
                            None
                          else f n) ).
     destruct H as [i [ineq f_spec]].
     + intros pp pphi.
       destruct (Nat.eq_dec pp hi).
       * auto.
       * simpl; eapply HH.
         move: pphi=> /leP pphi.
         apply /ltP.
         omega.

     + exists ((6 * i) + (perm_to_nat (f hi))).
       split.
       * replace (6 * N) with
         (6 * (N - 1) + 6 ).
         { eapply (NPeano.Nat.lt_le_trans _ (6 * i  + 6)).
           - apply /leP.
             rewrite ltn_add2l.
             destruct (f hi) as [p|];
               [destruct p; try destruct p|]; simpl; apply /leP; try omega.
           - apply /leP.
             rewrite leq_add2r.
             rewrite leq_pmul2l.
             + apply / leP. clear -ineq.
               replace N with (S (N - 1)) in ineq.
               apply /leP.
               by rewrite - ltnS; apply /leP.
               rewrite -addn1.
               apply subnK.
               destruct N; apply /ltP; try omega.
             + compute; auto.
         }
         rewrite - mulnSr.
         replace (N -1).+1 with N; auto.
         rewrite -addn1.
         symmetry; apply subnK.
         destruct N; apply /ltP; try omega.
       * { extensionality i0.
           destruct (Nat.eq_dec i0 hi).
           - subst.
             rewrite addnC.
             rewrite mulnC.
             rewrite NPeano.Nat.mod_add; try omega.
             rewrite NPeano.Nat.mod_small;
               try (apply /ltP; eapply perm_to_nat_bound).
             rewrite nat_to_perm_perm_to_nat.
             reflexivity.

           - replace ((6 * i + perm_to_nat (f hi)) / 6) with i.
             + rewrite f_spec.
               simpl.
               destruct (Nat.eq_dec i0 hi);
                 try solve [exfalso; apply n; auto].
               reflexivity.
             + eapply NPeano.Nat.div_unique;
               try (apply /ltP; eapply perm_to_nat_bound).
               reflexivity.
         }
Qed.


Lemma finite_bounded_nat_aux_func_simpl:
  forall hi ,
    konig.finite
      ( fun f:nat -> option permission => bounded_nat_func_aux f hi).
Proof.

   intros hi.
   pose (K:= perm_to_nat_simpl).
   induction hi.
   - exists 1%nat.
     exists (fun x _ => None).
     intros.
     exists 0%nat.
     split; auto.

     extensionality b.
     symmetry.
     apply H.
     apply /leP. omega.

   - destruct IHhi as [N [FN H]].
     exists (5*N)%nat.
     exists (fun x i => if (Nat.eq_dec i hi) then
                       nat_to_perm_simpl (Nat.modulo x 5)
                else FN (Nat.div x 5) i).
     move=> f HH.
     specialize (H (fun n => if (Nat.eq_dec n hi) then
                            None
                          else f n) ).
     destruct H as [i [ineq f_spec]].
     + intros pp pphi.
       destruct (Nat.eq_dec pp hi).
       * auto.
       * simpl; eapply HH.
         move: pphi=> /leP pphi.
         apply /ltP.
         omega.

     + exists ((5 * i) + (perm_to_nat_simpl (f hi))).
       split.
       * replace (5 * N) with
         (5 * (N - 1) + 5 ).
         { eapply (NPeano.Nat.lt_le_trans _ (5 * i  + 5)).
           - apply /leP.
             rewrite ltn_add2l.
             destruct (f hi) as [p|]; [destruct p|]; simpl; apply /leP; try omega.
           - apply /leP.
             rewrite leq_add2r.
             rewrite leq_pmul2l.
             + apply / leP. clear -ineq.
               replace N with (S (N - 1)) in ineq.
               apply /leP.
               by rewrite - ltnS; apply /leP.
               rewrite -addn1.
               apply subnK.
               destruct N; apply /ltP; try omega.
             + compute; auto.
         }
         rewrite - mulnSr.
         replace (N -1).+1 with N; auto.
         rewrite -addn1.
         symmetry; apply subnK.
         destruct N; apply /ltP; try omega.
       * { extensionality i0.
           destruct (Nat.eq_dec i0 hi).
           - subst.
             rewrite addnC.
             rewrite mulnC.
             rewrite NPeano.Nat.mod_add; try omega.
             rewrite NPeano.Nat.mod_small;
               try (apply /ltP; eapply perm_to_nat_bound_simpl).
             rewrite nat_to_perm_perm_to_nat_simpl.
             reflexivity.

           - replace ((5 * i + perm_to_nat_simpl (f hi)) / 5) with i.
             + rewrite f_spec.
               simpl.
               destruct (Nat.eq_dec i0 hi);
                 try solve [exfalso; apply n; auto].
               reflexivity.
             + eapply NPeano.Nat.div_unique;
               try (apply /ltP; eapply perm_to_nat_bound_simpl).
               reflexivity.
         }
Qed.

Lemma finite_bounded_nat_func:
  forall hi ,
    konig.finite
      ( fun f:nat -> option (option permission) => bounded_nat_func' f hi).
Proof.
  intros.
  destruct (finite_bounded_nat_aux_func (S hi)) as [x [f HH]].
  exists x, f.
  move=> x0 BND.
  cut (bounded_nat_func_aux x0 hi.+1).
  2:{ intros b ineq; eapply BND; auto. }
  move=> /HH [] i [] A B.
  exists i; split; eauto.
Qed.


Lemma finite_bounded_nat_func_simpl:
  forall hi ,
    konig.finite
      ( fun f:nat -> option permission => bounded_nat_func' f hi).
Proof.
  intros.
  destruct (finite_bounded_nat_aux_func_simpl (S hi)) as [x [f HH]].
  exists x, f.
  move=> x0 BND.
  cut (bounded_nat_func_aux x0 hi.+1).
  2:{ intros b ineq; eapply BND; auto. }
  move=> /HH [] i [] A B.
  exists i; split; eauto.
Qed.

Lemma finite_bounded_func:
  forall hi lo,
    konig.finite
      ( fun f:Z -> option (option permission) => bounded_func' f hi lo).
Proof.
  intros hi lo.
  destruct (Coqlib.zlt hi lo).
  - exists 1%N.
    exists (fun _ _ => None).
    intros.
    exists 0%nat; split; auto.
    extensionality b.
    destruct H as[H1 H2].
    symmetry.
    destruct (Coqlib.zle b hi).
    + eapply H2.
      eapply Z.le_lt_trans; eauto.
    + eapply H1; assumption.
  - assert (0 <= hi - lo)%Z by omega.
    pose (n:= Z.to_nat (hi - lo)).
    destruct (finite_bounded_nat_func n) as [N [FN HN]].
    exists N.
    exists (fun n z => (if (Z_lt_ge_dec z lo)
                then None
                else FN n (Z.to_nat (z-lo)))).
    intros f [BOUND1 BOUND2].
    pose (f':= fun n => f (Z.of_nat n + lo)%Z).
    assert (bounded_nat_func' f' n).
    { intros b ineq.
      unfold f'.
      eapply BOUND1.
      unfold n in ineq.
      cut (Z.of_nat b > hi - lo)%Z.
      omega.
      move: ineq => /ltP /inj_lt /Z.gt_lt_iff.
      rewrite Z2Nat.id => //.
    }
    apply HN in H0.
    destruct H0 as [i [ineq FN_spec]].
    exists i; split; auto.
    extensionality z.
    rewrite FN_spec.
    unfold f'.
    destruct (Z_lt_ge_dec z lo).
    + simpl.
      symmetry.
        by apply BOUND2.
    + simpl.
      rewrite Z2Nat.id.
      * f_equal; omega.
      * omega.
Qed.


Lemma finite_bounded_func_simpl:
  forall hi lo,
    konig.finite
      ( fun f:Z -> option permission => bounded_func' f hi lo).
Proof.
  intros hi lo.
  destruct (Coqlib.zlt hi lo).
  - exists 1%N.
    exists (fun _ _ => None).
    intros.
    exists 0%nat; split; auto.
    extensionality b.
    destruct H as[H1 H2].
    symmetry.
    destruct (Coqlib.zle b hi).
    + eapply H2.
      eapply Z.le_lt_trans; eauto.
    + eapply H1; assumption.
  - assert (0 <= hi - lo)%Z by omega.
    pose (n:= Z.to_nat (hi - lo)).
    destruct (finite_bounded_nat_func_simpl n) as [N [FN HN]].
    exists N.
    exists (fun n z => (if (Z_lt_ge_dec z lo)
                then None
                else FN n (Z.to_nat (z-lo)))).
    intros f [BOUND1 BOUND2].
    pose (f':= fun n => f (Z.of_nat n + lo)%Z).
    assert (bounded_nat_func' f' n).
    { intros b ineq.
      unfold f'.
      eapply BOUND1.
      unfold n in ineq.
      cut (Z.of_nat b > hi - lo)%Z.
      omega.
      move: ineq => /ltP /inj_lt /Z.gt_lt_iff.
      rewrite Z2Nat.id => //.
    }
    apply HN in H0.
    destruct H0 as [i [ineq FN_spec]].
    exists i; split; auto.
    extensionality z.
    rewrite FN_spec.
    unfold f'.
    destruct (Z_lt_ge_dec z lo).
    + simpl.
      symmetry.
        by apply BOUND2.
    + simpl.
      rewrite Z2Nat.id.
      * f_equal; omega.
      * omega.
Qed.

Lemma finite_bounded_op_func_simpl:
  forall hi lo,
    konig.finite
      ( fun f: option (Z -> option permission) => bounded_func_op f hi lo).
Proof.
  move => hi lo.
  move: (finite_bounded_func_simpl hi lo) => [] N [] FN FN_spec.

  exists (S N).
  exists (fun n => if n == 0 then None
           else Some (FN (n -1)) ).
  move => f H.
  destruct f.
  - move: FN_spec => /(_ _ H) [] i [] ineqi speci.
    exists (S i); split.
    + omega.
    + rewrite - speci.
      simpl; repeat f_equal.
      rewrite - addn1 - addnBA=> //.
  - exists 0; split; auto.
    + omega.
Qed.

Lemma finite_bounded_op_func:
  forall hi lo,
    konig.finite
      ( fun f: option (Z -> option (option permission)) => bounded_func_op f hi lo).
Proof.
  move => hi lo.
  move: (finite_bounded_func hi lo) => [] N [] FN FN_spec.

  exists (S N).
  exists (fun n => if n == 0 then None
           else Some (FN (n -1)) ).
  move => f H.
  destruct f.
  - move: FN_spec => /(_ _ H) [] i [] ineqi speci.
    exists (S i); split.
    + omega.
    + rewrite - speci.
      simpl; repeat f_equal.
      rewrite - addn1 - addnBA=> //.
  - exists 0; split; auto.
    + omega.
Qed.

Lemma finite_sub_maps:
  forall m2,
    @bounded_map permission m2 ->
    konig.finite
      (fun m1 => @sub_map (option permission) permission m1 m2).
Proof.
  induction m2.
  - move => _.
    exists 1%nat.
    exists (fun _ => PTree.Leaf).
    intros .
    exists 0%nat.
    split; auto.
    destruct x; auto.
    unfold strong_tree_leq in H;
      simpl in H.
    destruct o; inversion H.
  - move => H.
    assert (HH1:
              forall (p : positive) (f : Z -> option permission),
                m2_1 ! p = Some f ->
                exists hi lo : Z,
                  (forall p0 : Z, (p0 > hi)%Z -> f p0 = None) /\
                  (forall p0 : Z, (p0 < lo)%Z -> f p0 = None)).
    { clear - H.
      move=> p f Hget.
      move : H => /(_ (p~0)%positive f ltac:(simpl;auto)) [] hi [] lo BOUND.
      exists hi, lo; assumption.
    }
    move: IHm2_1=> /(_ HH1) [] N1 [] F1 spec_F1.
    assert (HH2:
              forall (p : positive) (f : Z -> option permission),
                m2_2 ! p = Some f ->
                exists hi lo : Z,
                  (forall p0 : Z, (p0 > hi)%Z -> f p0 = None) /\
                  (forall p0 : Z, (p0 < lo)%Z -> f p0 = None)).
    { clear - H.
      move=> p f Hget.
      move : H => /(_ (p~1)%positive f ltac:(simpl;auto)) [] hi [] lo BOUND.
      exists hi, lo; assumption.
    }
    move: IHm2_2=> /(_ HH2) [] N2 [] F2 spec_F2.
    destruct o as [f1|].
    + move : H => /(_ 1%positive f1 ltac:(reflexivity)) [] hi [] lo BNDD.
      move : (finite_bounded_op_func hi lo) => [] N [] F F_spec.
      exists (S( N * N1 * N2)).
      exists (fun n => if n == 0
               then PTree.Leaf
               else
                 PTree.Node
                   (F1 ( (n-1) mod N1))
                   (F ((n-1) / (N1 * N2)))
                   (F2 (((n-1) / N1 ) mod N2))).
      intros x spec.
      destruct x.
      * exists 0%nat; split; auto.
        omega.
      * move: spec .
        rewrite /sub_map /= => [] [] FUN_lq [] tree1 tree2.
        assert (bounded_func_op o hi lo).
        { Lemma fun_le_bounded_func_op:
            forall {A} o f hi lo,
              @bounded_func' A f hi lo ->
              fun_leq o (Some f) ->
              @bounded_func_op (option A) o hi lo.
          Proof.
            intros.
            destruct o; [|constructor].
            simpl.
            simpl in H0.
            split; intros p.
            - intros HH. apply H in HH.
              unfold fun_leq' in H0.
              specialize (H0 p).
              destruct (o p); try solve [auto].
              specialize (H0 ltac:(auto)).
              rewrite HH in H0; inversion H0.
            - intros HH. apply H in HH.
              unfold fun_leq' in H0.
              specialize (H0 p).
              destruct (o p); try solve [auto].
              specialize (H0 ltac:(auto)).
              rewrite HH in H0; inversion H0.
          Qed.
          eapply fun_le_bounded_func_op ; eauto.
          }
        move: F_spec => /(_ _ H) []i [] ineq fi.
        move : spec_F1 => /(_ _ tree1) [] i1 [] ineq1 fi1.
        move : spec_F2 => /(_ _ tree2) [] i2 [] ineq2 fi2.
        exists (S(i1 + (i2 * N1) + (i * N1 * N2))); split.
        { apply lt_n_S.
          replace (N * N1 * N2) with
          (N1 + N1 * (N2 * N -1)).
          - eapply (NPeano.Nat.lt_le_trans).
            + instantiate (1:= (N1 + i2 * N1 + i * N1 * N2)).
              apply /ltP.
              rewrite ltn_add2r;
                rewrite ltn_add2r;
                apply /ltP; auto.
            + apply /leP.
              rewrite -addnA.
              rewrite leq_add2l.
              apply /leP.
              replace (i * N1 * N2) with
              ((i * N2) * N1).
              *
                rewrite -mulnDl.
                rewrite mulnC.
                apply /leP.
                rewrite leq_pmul2l; try (apply /ltP; omega).
                apply /leP.
                eapply lt_n_Sm_le.
                rewrite - addn1.
                rewrite subnK.
                2:
                  rewrite muln_gt0;
                  apply /andP; split;
                  try (apply /ltP; omega).
                eapply (NPeano.Nat.lt_le_trans).
                -- instantiate (1:= N2 + i * N2).
                   apply /ltP.
                   rewrite ltn_add2r.
                   apply /leP; auto.
                -- replace (N2 + i * N2) with
                   (N2 * (1 + i)).
                   apply /leP.
                   rewrite leq_pmul2l.
                   rewrite add1n.
                   apply /ltP; auto.
                   apply /ltP; omega.
                   rewrite mulnDr.
                   rewrite mulnC.
                   f_equal.
                   compute; auto.
                   rewrite mulnC; auto.
              * do 2 rewrite - mulnA.
                f_equal. rewrite mulnC; auto.
          - replace (N1 + N1 * (N2 * N - 1))
            with (N1 * 1 + N1 * (N2 * N - 1)).
            + rewrite -mulnDr.
              rewrite addnC.
              rewrite subnK.

              2:
                rewrite muln_gt0;
                apply /andP; split;
                try (apply /ltP; omega).
              rewrite -mulnA.
              rewrite mulnA.
              rewrite mulnC; auto.
            + f_equal.
              rewrite mulnC.
              compute; auto. }
      -- simpl; f_equal.
         ++ rewrite - fi1.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2 + (1 - 1)) with
            (i1 + i2 * N1 + i * N1 * N2) by ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2) with
            (i1 + (i2  + i *  N2) * N1).
            2:
            rewrite mulnDl addnA; f_equal;
            do 2 rewrite -mulnA; f_equal; rewrite mulnC; auto.
            rewrite NPeano.Nat.mod_add.
            apply NPeano.Nat.mod_small; auto.
            destruct N1; omega.
         ++ rewrite - fi.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2 + (1 - 1)) with
            (i1 + i2 * N1 + i * N1 * N2) by ssromega.
            assert (i1 + i2 * N1 + i * N1 * N2 =
                    ((N1 * N2) * i) + (i1 + i2 * N1)).
            { rewrite addnC. f_equal.
              rewrite - mulnA mulnC; auto. }
            eapply NPeano.Nat.div_unique in H0; auto.
            eapply (NPeano.Nat.lt_le_trans).
            ** instantiate (1:= N1 + i2 * N1).
               apply /ltP; rewrite ltn_add2r.
               apply /ltP; auto.
            ** replace (N1 + i2 * N1) with ( (1 + i2) * N1).
               rewrite add1n.
               rewrite mulnC.
               apply /leP; rewrite leq_pmul2l.
               apply /ltP; auto.
               destruct N1; ssromega.
               rewrite mulnDl; f_equal.
               ssromega.

         ++ rewrite - fi2.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2 + (1 - 1)) with
            (i1 + i2 * N1 + i * N1 * N2) by ssromega.
            assert (i1 + i2 * N1 + i * N1 * N2 =
                    (N1 * (i2 + i * N2)) + i1).
            { rewrite -addnA.
              replace (i * N1 * N2) with
              (i  * N2 * N1).
              rewrite - mulnDl.
              rewrite mulnC addnC; auto.
              do 2 rewrite -mulnA; f_equal.
              rewrite mulnC. auto. }
            eapply NPeano.Nat.div_unique in H0; auto.
            rewrite - H0.
            rewrite NPeano.Nat.mod_add.
            apply NPeano.Nat.mod_small; auto.
            destruct N2; omega.
    + exists (S( N1 * N2)).
      exists (fun n => if n == 0
               then PTree.Leaf
               else
                 PTree.Node
                   (F1 ( (n-1) mod N1))
                   (None )
                   (F2 (((n-1) / N1 ) mod N2))).
      intros x spec.
      destruct x.
      * exists 0%nat; split; auto.
        omega.
      * move: spec .
        rewrite /sub_map /= => [] [] FUN_lq [] tree1 tree2.
        move : spec_F1 => /(_ _ tree1) [] i1 [] ineq1 fi1.
        move : spec_F2 => /(_ _ tree2) [] i2 [] ineq2 fi2.
        exists (S(i1 + (i2 * N1))); split.
        { apply lt_n_S.
          replace (N1 * N2) with
          (N1 + N1 * (N2 -1)).
          - eapply (NPeano.Nat.lt_le_trans).
            + instantiate (1:= (N1 + i2 * N1)).
              apply /ltP.
              rewrite ltn_add2r;
                apply /ltP; auto.
            + apply /leP.
              rewrite leq_add2l.
              apply /leP.
              rewrite mulnC.
              apply /leP.
              rewrite leq_pmul2l; try (apply /ltP; omega).
              apply /leP.
              eapply lt_n_Sm_le.
              rewrite - addn1.
              rewrite subnK; auto.
              destruct N2; ssromega.

          - replace (N1 + N1 * (N2 - 1))
            with (N1 * 1 + N1 * (N2 - 1)).
            + rewrite -mulnDr.
              rewrite addnC.
              rewrite subnK.
              2: ssromega.
              rewrite mulnC; auto.
            + f_equal.
              rewrite mulnC.
              compute; auto. }
      -- simpl; f_equal.
         ++ rewrite - fi1.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + (1 - 1)) with
            (i1 + i2 * N1) by ssromega.
            rewrite NPeano.Nat.mod_add.
            apply NPeano.Nat.mod_small; auto.
            destruct N1; omega.
         ++ destruct o; auto; inversion FUN_lq.
         ++ rewrite - fi2.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + (1 - 1)) with
            (i1 + i2 * N1 ) by ssromega.
            assert (i1 + i2 * N1 =
                    (N1 * (i2) + i1)).
            { rewrite mulnC addnC; auto. }
            eapply NPeano.Nat.div_unique in H0; auto.
            rewrite - H0.
            apply NPeano.Nat.mod_small; auto.
Qed.

Lemma finite_sub_maps_simpl:
  forall m2,
    @bounded_map permission m2 ->
    konig.finite
      (fun m1 => @sub_map permission permission m1 m2).
Proof.

  induction m2.
  - move => _.
    exists 1%nat.
    exists (fun _ => PTree.Leaf).
    intros .
    exists 0%nat.
    split; auto.
    destruct x; auto.
    unfold strong_tree_leq in H;
      simpl in H.
    destruct o; inversion H.
  - move => H.
    assert (HH1:
              forall (p : positive) (f : Z -> option permission),
                m2_1 ! p = Some f ->
                exists hi lo : Z,
                  (forall p0 : Z, (p0 > hi)%Z -> f p0 = None) /\
                  (forall p0 : Z, (p0 < lo)%Z -> f p0 = None)).
    { clear - H.
      move=> p f Hget.
      move : H => /(_ (p~0)%positive f ltac:(simpl;auto)) [] hi [] lo BOUND.
      exists hi, lo; assumption.
    }
    move: IHm2_1=> /(_ HH1) [] N1 [] F1 spec_F1.
    assert (HH2:
              forall (p : positive) (f : Z -> option permission),
                m2_2 ! p = Some f ->
                exists hi lo : Z,
                  (forall p0 : Z, (p0 > hi)%Z -> f p0 = None) /\
                  (forall p0 : Z, (p0 < lo)%Z -> f p0 = None)).
    { clear - H.
      move=> p f Hget.
      move : H => /(_ (p~1)%positive f ltac:(simpl;auto)) [] hi [] lo BOUND.
      exists hi, lo; assumption.
    }
    move: IHm2_2=> /(_ HH2) [] N2 [] F2 spec_F2.
    destruct o as [f1|].
    + move : H => /(_ 1%positive f1 ltac:(reflexivity)) [] hi [] lo BNDD.
      move : (finite_bounded_op_func_simpl hi lo) => [] N [] F F_spec.
      exists (S( N * N1 * N2)).
      exists (fun n => if n == 0
               then PTree.Leaf
               else
                 PTree.Node
                   (F1 ( (n-1) mod N1))
                   (F ((n-1) / (N1 * N2)))
                   (F2 (((n-1) / N1 ) mod N2))).
      intros x spec.
      destruct x.
      * exists 0%nat; split; auto.
        omega.
      * move: spec .
        rewrite /sub_map /= => [] [] FUN_lq [] tree1 tree2.
        assert (bounded_func_op o hi lo).
        { Lemma fun_le_bounded_func_op_simpl:
            forall {A} o f hi lo,
              @bounded_func' A f hi lo ->
              fun_leq o (Some f) ->
              @bounded_func_op A o hi lo.
          Proof.
            intros.
            destruct o; [|constructor].
            simpl.
            simpl in H0.
            split; intros p.
            - intros HH. apply H in HH.
              unfold fun_leq' in H0.
              specialize (H0 p).
              destruct (o p); try solve [auto].
              specialize (H0 ltac:(auto)).
              rewrite HH in H0; inversion H0.
            - intros HH. apply H in HH.
              unfold fun_leq' in H0.
              specialize (H0 p).
              destruct (o p); try solve [auto].
              specialize (H0 ltac:(auto)).
              rewrite HH in H0; inversion H0.
          Qed.
          eapply fun_le_bounded_func_op_simpl ; eauto.
          }
        move: F_spec => /(_ _ H) []i [] ineq fi.
        move : spec_F1 => /(_ _ tree1) [] i1 [] ineq1 fi1.
        move : spec_F2 => /(_ _ tree2) [] i2 [] ineq2 fi2.
        exists (S(i1 + (i2 * N1) + (i * N1 * N2))); split.
        { apply lt_n_S.
          replace (N * N1 * N2) with
          (N1 + N1 * (N2 * N -1)).
          - eapply (NPeano.Nat.lt_le_trans).
            + instantiate (1:= (N1 + i2 * N1 + i * N1 * N2)).
              apply /ltP.
              rewrite ltn_add2r;
                rewrite ltn_add2r;
                apply /ltP; auto.
            + apply /leP.
              rewrite -addnA.
              rewrite leq_add2l.
              apply /leP.
              replace (i * N1 * N2) with
              ((i * N2) * N1).
              *
                rewrite -mulnDl.
                rewrite mulnC.
                apply /leP.
                rewrite leq_pmul2l; try (apply /ltP; omega).
                apply /leP.
                eapply lt_n_Sm_le.
                rewrite - addn1.
                rewrite subnK.
                2:
                  rewrite muln_gt0;
                  apply /andP; split;
                  try (apply /ltP; omega).
                eapply (NPeano.Nat.lt_le_trans).
                -- instantiate (1:= N2 + i * N2).
                   apply /ltP.
                   rewrite ltn_add2r.
                   apply /leP; auto.
                -- replace (N2 + i * N2) with
                   (N2 * (1 + i)).
                   apply /leP.
                   rewrite leq_pmul2l.
                   rewrite add1n.
                   apply /ltP; auto.
                   apply /ltP; omega.
                   rewrite mulnDr.
                   rewrite mulnC.
                   f_equal.
                   compute; auto.
                   rewrite mulnC; auto.
              * do 2 rewrite - mulnA.
                f_equal. rewrite mulnC; auto.
          - replace (N1 + N1 * (N2 * N - 1))
            with (N1 * 1 + N1 * (N2 * N - 1)).
            + rewrite -mulnDr.
              rewrite addnC.
              rewrite subnK.

              2:
                rewrite muln_gt0;
                apply /andP; split;
                try (apply /ltP; omega).
              rewrite -mulnA.
              rewrite mulnA.
              rewrite mulnC; auto.
            + f_equal.
              rewrite mulnC.
              compute; auto. }
      -- simpl; f_equal.
         ++ rewrite - fi1.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2 + (1 - 1)) with
            (i1 + i2 * N1 + i * N1 * N2) by ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2) with
            (i1 + (i2  + i *  N2) * N1).
            2:
            rewrite mulnDl addnA; f_equal;
            do 2 rewrite -mulnA; f_equal; rewrite mulnC; auto.
            rewrite NPeano.Nat.mod_add.
            apply NPeano.Nat.mod_small; auto.
            destruct N1; omega.
         ++ rewrite - fi.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2 + (1 - 1)) with
            (i1 + i2 * N1 + i * N1 * N2) by ssromega.
            assert (i1 + i2 * N1 + i * N1 * N2 =
                    ((N1 * N2) * i) + (i1 + i2 * N1)).
            { rewrite addnC. f_equal.
              rewrite - mulnA mulnC; auto. }
            eapply NPeano.Nat.div_unique in H0; auto.
            eapply (NPeano.Nat.lt_le_trans).
            ** instantiate (1:= N1 + i2 * N1).
               apply /ltP; rewrite ltn_add2r.
               apply /ltP; auto.
            ** replace (N1 + i2 * N1) with ( (1 + i2) * N1).
               rewrite add1n.
               rewrite mulnC.
               apply /leP; rewrite leq_pmul2l.
               apply /ltP; auto.
               destruct N1; ssromega.
               rewrite mulnDl; f_equal.
               ssromega.

         ++ rewrite - fi2.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + i * N1 * N2 + (1 - 1)) with
            (i1 + i2 * N1 + i * N1 * N2) by ssromega.
            assert (i1 + i2 * N1 + i * N1 * N2 =
                    (N1 * (i2 + i * N2)) + i1).
            { rewrite -addnA.
              replace (i * N1 * N2) with
              (i  * N2 * N1).
              rewrite - mulnDl.
              rewrite mulnC addnC; auto.
              do 2 rewrite -mulnA; f_equal.
              rewrite mulnC. auto. }
            eapply NPeano.Nat.div_unique in H0; auto.
            rewrite - H0.
            rewrite NPeano.Nat.mod_add.
            apply NPeano.Nat.mod_small; auto.
            destruct N2; omega.
    + exists (S( N1 * N2)).
      exists (fun n => if n == 0
               then PTree.Leaf
               else
                 PTree.Node
                   (F1 ( (n-1) mod N1))
                   (None )
                   (F2 (((n-1) / N1 ) mod N2))).
      intros x spec.
      destruct x.
      * exists 0%nat; split; auto.
        omega.
      * move: spec .
        rewrite /sub_map /= => [] [] FUN_lq [] tree1 tree2.
        move : spec_F1 => /(_ _ tree1) [] i1 [] ineq1 fi1.
        move : spec_F2 => /(_ _ tree2) [] i2 [] ineq2 fi2.
        exists (S(i1 + (i2 * N1))); split.
        { apply lt_n_S.
          replace (N1 * N2) with
          (N1 + N1 * (N2 -1)).
          - eapply (NPeano.Nat.lt_le_trans).
            + instantiate (1:= (N1 + i2 * N1)).
              apply /ltP.
              rewrite ltn_add2r;
                apply /ltP; auto.
            + apply /leP.
              rewrite leq_add2l.
              apply /leP.
              rewrite mulnC.
              apply /leP.
              rewrite leq_pmul2l; try (apply /ltP; omega).
              apply /leP.
              eapply lt_n_Sm_le.
              rewrite - addn1.
              rewrite subnK; auto.
              destruct N2; ssromega.

          - replace (N1 + N1 * (N2 - 1))
            with (N1 * 1 + N1 * (N2 - 1)).
            + rewrite -mulnDr.
              rewrite addnC.
              rewrite subnK.
              2: ssromega.
              rewrite mulnC; auto.
            + f_equal.
              rewrite mulnC.
              compute; auto. }
      -- simpl; f_equal.
         ++ rewrite - fi1.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + (1 - 1)) with
            (i1 + i2 * N1) by ssromega.
            rewrite NPeano.Nat.mod_add.
            apply NPeano.Nat.mod_small; auto.
            destruct N1; omega.
         ++ destruct o; auto; inversion FUN_lq.
         ++ rewrite - fi2.
            f_equal.
            rewrite -addn1.
            rewrite -addnBA. 2: ssromega.
            replace (i1 + i2 * N1 + (1 - 1)) with
            (i1 + i2 * N1 ) by ssromega.
            assert (i1 + i2 * N1 =
                    (N1 * (i2) + i1)).
            { rewrite mulnC addnC; auto. }
            eapply NPeano.Nat.div_unique in H0; auto.
            rewrite - H0.
            apply NPeano.Nat.mod_small; auto.
Qed.
