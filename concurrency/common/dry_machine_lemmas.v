(** * Lemmas about the Dry Machine*)
Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
(* Require Import compcert.common.Events. *)
Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.tactics.

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).

(** This file holds various results about the dry machine*)
(* Find other lemmas in dry_machine_step_lemmas.v        *)

Module ThreadPoolWF.
  Import HybridMachine ThreadPool DryHybridMachine HybridMachineSig.
  Section ThreadPoolWF.
    Context {Sem : Semantics}.
    
    Existing Instance DryHybridMachine.dryResources.
    Existing Instance OrdinalPool.OrdinalThreadPool.   
    (** Take an instance of the Dry Machine *)
    Existing Instance DryHybridMachine.DryHybridMachineSig.

    
  Lemma unlift_m_inv :
    forall tp tid (Htid : tid < (OrdinalPool.num_threads tp).+1) ord
      (Hunlift: unlift (ordinal_pos_incr (OrdinalPool.num_threads tp))
                       (Ordinal (n:=(OrdinalPool.num_threads tp).+1)
                                (m:=tid) Htid)=Some ord),
      nat_of_ord ord = tid.
  Proof.
    intros.
    assert (Hcontra: unlift_spec (ordinal_pos_incr (OrdinalPool.num_threads tp))
                                 (Ordinal (n:=(OrdinalPool.num_threads tp).+1)
                                          (m:=tid) Htid) (Some ord)).
    rewrite <- Hunlift.
    apply/unliftP.
    inversion Hcontra; subst.
    inversion H0.
    unfold bump.
    assert (pf: ord < (OrdinalPool.num_threads tp))
      by (by rewrite ltn_ord).
    assert (H: (OrdinalPool.num_threads tp) <= ord = false).
    rewrite ltnNge in pf.
    rewrite <- Bool.negb_true_iff. auto.
    rewrite H. simpl. rewrite add0n. reflexivity.
  Defined.

  (* TODO: seems to be deprecated. Delete if so*)
  (*
  (** Well-formed predicate on new permission map*)
  Definition newPermMap_wf tp pmap :=
    forall k,
      permMapsDisjoint (Resources.get k (allDataRes tp)) pmap.1 /\
      permMapsDisjoint (Resources.get k (allLockRes tp)) pmap.2.

  Definition permMap_wf tp pmap i :=
    forall j (cntj : containsThread tp j) (Hneq: i <> j),
      permMapsDisjoint (getThreadR cntj) pmap.


 Opaque pos_incr.
  Lemma addThread_racefree :
    forall tp vf arg p (Hwf: newPermMap_wf tp p) (Hrace: race_free tp),
      race_free (addThread tp vf arg p).
  Proof.
    unfold race_free in *. intros.
    simpl.
    match goal with
    | [ |- context[ match ?Expr with _ => _ end]] =>
      destruct Expr as [ordi|] eqn:Hgeti
    end;
      match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ordj|] eqn:Hgetj
      end.
    unfold containsThread in *; simpl in *.
    - unfold getThreadR in Hrace.
      apply unlift_m_inv in Hgeti.
      apply unlift_m_inv in Hgetj.
      destruct ordi as [i' pfi], ordj as [j' pfj]; subst.
      simpl in *.
      eapply Hrace; eauto.
    - apply unlift_m_inv in Hgeti.
      subst. unfold newPermMap_wf in Hwf.
      destruct ordi. eapply Hwf; eauto.
    - apply unlift_m_inv in Hgetj.
      subst. unfold newPermMap_wf in Hwf.
      destruct ordj. apply permMapsDisjoint_comm. eapply Hwf; eauto.
    - destruct (i == (num_threads tp)) eqn:Heqi.
      + move/eqP:Heqi=>Heqi. subst.
        assert (Hcontra: (ordinal_pos_incr (num_threads tp))
                           != (Ordinal (n:=(num_threads tp).+1) (m:=j) cntj)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra.
          inversion Hcontra; auto.
        }
        exfalso. apply unlift_some in Hcontra. rewrite Hgetj in Hcontra.
        destruct Hcontra. discriminate.
      + move/eqP:Heqi=>Heqi.
        assert (
            Hcontra: (ordinal_pos_incr (num_threads tp))
                       !=
                       (Ordinal (n:=(num_threads tp).+1) (m:=i) cnti)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra. inversion Hcontra. subst. auto. }
        exfalso. apply unlift_some in Hcontra.
        rewrite Hgeti in Hcontra. destruct Hcontra.
        discriminate.
  Defined. *)

  Lemma initial_invariant0: forall pmap c,
      DryHybridMachine.invariant (mkPool c (pmap, empty_map)).
  Proof.
    intros pmap c.
    pose (IM:=mkPool c (pmap,empty_map)); fold IM.
    assert (isZ: forall i, OrdinalPool.containsThread IM i -> (i = 0)%N).
    { rewrite /containsThread /IM /=.
      move => i; destruct i; first[reflexivity | intros HH; inversion HH].
    }
    assert (noLock: forall l rm,
               OrdinalPool.lockRes IM l = Some rm -> False).
    { rewrite /OrdinalPool.lockRes /IM /=.
      move => l rm.
      rewrite /lockRes
              /OrdinalPool.mkPool
              /OrdinalPool.empty_lset /= OrdinalPool.find_empty => HH.
      inversion HH.
    }

    constructor.
    + move => i j0 cnti cntj HH.
      exfalso; apply HH.
      move: cnti cntj => /isZ -> /isZ ->; reflexivity.
    + move=> l1 l2 rm1 rm2 neq /noLock contra; exfalso; now eauto.
    + move => i l cnt rm /noLock contra; exfalso; now eauto.
    + move=> i cnti; split.
      * move => j0 cntj.
        move: (cnti) (cntj) => cnti0 cntj0;
                                move: cnti cntj => /isZ Hi /isZ Hj.
        subst.
        simpl in IM.
        unfold OrdinalPool.mkPool in IM.
        unfold getThreadR.
        simpl.
        eapply permCoh_empty'.
      * move => l rm /noLock contra; exfalso; now eauto.
    + move => l mr /noLock contra; exfalso; now eauto.
    + move => b ofs.
      rewrite / IM /= //.
  Qed.

  Lemma updThread_inv: forall ds i (cnt: containsThread ds i) c pmap,
      invariant ds ->
      (forall j (cnt: containsThread ds j),
          i<>j -> permMapsDisjoint pmap.1 (getThreadR cnt).1 /\
                permMapsDisjoint pmap.2 (getThreadR cnt).2) ->
      (forall j (cnt: containsThread ds j),
          i<>j ->
          permMapCoherence (getThreadR cnt).1 pmap.2)->
      (forall j (cnt: containsThread ds j),
          i<>j ->
          permMapCoherence pmap.1 (getThreadR cnt).2)->
      (forall l pmap0, lockRes ds l = Some pmap0 ->
                  permMapsDisjoint pmap0.1 pmap.1 /\
                  permMapsDisjoint pmap0.2 pmap.2  ) ->
      (forall l pmap0, lockRes ds l = Some pmap0 ->
                  permMapCoherence pmap0.1 pmap.2 /\
                  permMapCoherence pmap.1 pmap0.2) ->
      (permMapCoherence pmap#1 pmap#2) ->
      invariant (updThread cnt c pmap).
  Proof.
    intros ds x cnt c pmap INV A A' A'' B B' C.
    constructor.
    - intros.
      destruct (scheduler.NatTID.eq_tid_dec x i); [|destruct (scheduler.NatTID.eq_tid_dec x j)].
      + subst i.
        rewrite gssThreadRes.
        rewrite gsoThreadRes; try solve[assumption].
        assert (cntj':=cntj).
        apply cntUpdate' in cntj'.
        eapply (A); assumption.
      + subst j.
        apply permMapsDisjoint2_comm.
        rewrite gssThreadRes.
        rewrite gsoThreadRes; try solve[assumption].
        apply A; assumption.
      + rewrite gsoThreadRes; try solve[assumption].
        rewrite gsoThreadRes; try solve[assumption].
        inversion INV. apply no_race_thr; assumption.
    -  intros.
       rewrite gsoThreadLPool in Hres1.
       rewrite gsoThreadLPool in Hres2.
       inversion INV. eapply no_race_lr; eauto.
    - intros i laddr cnti rmap.
      rewrite gsoThreadLPool; intros Hres.
      destruct (scheduler.NatTID.eq_tid_dec x i).
      + subst x. rewrite gssThreadRes.
        apply permMapsDisjoint2_comm.
        eapply B; eassumption.
      + rewrite gsoThreadRes; auto.
        inversion INV. eapply no_race; eassumption.
    - intros i cnti.
      destruct (scheduler.NatTID.eq_tid_dec x i).
      + subst x; rewrite gssThreadRes; split; intros.
        * { destruct (scheduler.NatTID.eq_tid_dec i j).
            - subst i. rewrite gssThreadRes. assumption.
            - rewrite gsoThreadRes; auto. }
        * rewrite gsoThreadLPool in H.
          apply B' with (l:= laddr); assumption.
      + rewrite gsoThreadRes; auto; split ; intros.
        *
          { destruct (scheduler.NatTID.eq_tid_dec x j).
            - subst j. rewrite gssThreadRes; apply A''; auto.
            - rewrite gsoThreadRes; auto.
              inversion INV. destruct (thread_data_lock_coh0 i cnti) as [H1 H2].
              apply H1.
          }
        * rewrite gsoThreadLPool in H.
          inversion INV. destruct (thread_data_lock_coh0 i cnti) as [H1 H2].
          eapply H2; eauto.
    - move => laddr rmap;
               rewrite gsoThreadLPool => isLock; split.
      + move => j cntj .
        { destruct (scheduler.NatTID.eq_tid_dec x j).
          - subst j. rewrite gssThreadRes.
            destruct (B' laddr rmap ltac:(assumption)).  assumption.
          - rewrite gsoThreadRes; auto.
            inversion INV. destruct (locks_data_lock_coh0 laddr rmap ltac:(auto)) as [H1 H2].
            apply H1.
        }
      + move => laddr' rmap';
                 rewrite gsoThreadLPool => isLock'.
        inversion INV. destruct (locks_data_lock_coh0 laddr rmap ltac:(auto)) as [H1 H2].
        eapply H2; eauto.
    - move => b' ofs'; rewrite gsoThreadLPool.
      inversion INV. apply lockRes_valid0.
  Qed.

  Lemma invariant_decr:
    forall tp c pmap i (cnti: containsThread tp i)
      (Hinv: invariant tp)
      (Hdecr1: forall b ofs,
          Mem.perm_order'' ((getThreadR cnti).1 # b ofs)
                           (pmap.1 # b ofs))
      (Hdecr2: forall b ofs,
          Mem.perm_order'' ((getThreadR cnti).2 # b ofs)
                           (pmap.2 # b ofs)),
      invariant (updThread cnti c pmap).
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    constructor.
    - intros k j cntk cntj Hkj.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
      + subst k.
        rewrite gssThreadRes.
        rewrite gsoThreadRes; auto.
        specialize (no_race_thr0 _ _ cnti cntj Hkj).
        unfold permMapsDisjoint2, permMapsDisjoint in *.
        erewrite <- forall2_and.
        erewrite <- forall2_and in no_race_thr0.
        intros b ofs.
        destruct (no_race_thr0 b ofs) as [H1 H2].
        split; rewrite perm_union_comm;
          erewrite perm_union_comm in H1, H2;
          eapply perm_union_lower;
            by eauto.
      + rewrite gsoThreadRes; auto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        subst j.
        rewrite gssThreadRes.
        specialize (no_race_thr0 _ _ cntk cnti Hkj).
        unfold permMapsDisjoint2, permMapsDisjoint in *.
        erewrite <- forall2_and.
        erewrite <- forall2_and in no_race_thr0.
        intros b ofs.
        destruct (no_race_thr0 b ofs) as [H1 H2].
        split;
          eapply perm_union_lower;
            by eauto.
        rewrite gsoThreadRes;
          by auto.
    - intros.
      erewrite gsoThreadLPool in Hres1, Hres2.
        by eauto.
    - intros.
      erewrite gsoThreadLPool in Hres.
      destruct (i == i0) eqn:Heq; move/eqP:Heq=>Heq.
      + subst.
        rewrite gssThreadRes.
        specialize (no_race0 _ _ cnti _ Hres).
        unfold permMapsDisjoint2, permMapsDisjoint in *.
        erewrite <- forall2_and.
        erewrite <- forall2_and in no_race0.
        intros b ofs.
        destruct (no_race0 b ofs) as [H1 H2].
        erewrite perm_union_comm in H1, H2.
        split;
          erewrite perm_union_comm;
          eapply perm_union_lower;
            by eauto.
      + rewrite gsoThreadRes; auto.
        eauto.
    - intros k cntk.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
      + subst.
        rewrite gssThreadRes.
        split.
        * intros j cntj b ofs.
          destruct (k == j) eqn:Hkj; move/eqP:Hkj=>Hkj.
          subst.
          rewrite gssThreadRes.
          pose proof ((thread_data_lock_coh0 _ cnti).1 _ cnti b ofs).
          eauto using perm_coh_lower.
          rewrite gsoThreadRes; auto.
          pose proof ((thread_data_lock_coh0 _ cnti).1 _ cntj b ofs).
          eauto using perm_coh_lower, po_refl.
        * intros laddr rmap Hres b ofs.
          rewrite gsoThreadLPool in Hres.
          eapply perm_coh_lower; eauto.
          eapply thread_data_lock_coh0; eauto.
          now eapply po_refl.
      + rewrite gsoThreadRes; auto.
        split.
        * intros j cntj b ofs.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst.
          rewrite gssThreadRes.
          destruct (thread_data_lock_coh0 k cntk).
          eapply perm_coh_lower; eauto.
          eapply H.
          eapply po_refl.
          rewrite gsoThreadRes; auto.
          destruct (thread_data_lock_coh0 k cntk);
            now eapply H.
        * intros laddr rmap Hres.
          rewrite gsoThreadLPool in Hres.
          eapply thread_data_lock_coh0; eauto.
    - intros laddr rmap Hres.
      rewrite gsoThreadLPool in Hres.
      destruct (locks_data_lock_coh0 laddr rmap Hres) as [H1 H2].
      split.
      + intros j cntj b ofs.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        * subst.
          rewrite gssThreadRes.
          eapply perm_coh_lower; eauto.
          now apply H1.
          now apply po_refl.
        * rewrite gsoThreadRes; auto.
          eapply H1.
      + intros laddr' rmap' Hres'.
        rewrite gsoThreadLPool in Hres'.
        eauto.
    - intros b ofs.
      rewrite gsoThreadLPool.
      specialize (lockRes_valid0 b ofs).
      destruct (lockRes tp (b, ofs));
        by auto.
  Qed.

  (** [invariant] is preserved by [updThreadC]*)
  Lemma updThreadC_invariant:
    forall (tp : t) i c
      (ctn : containsThread tp i)
      (Hinv : invariant tp),
      invariant (updThreadC ctn c).
  Proof.
    intros.
    inversion Hinv;
      constructor;
      simpl in *;
        by auto.
  Qed.

  Lemma updLock_inv:
    forall tp b ofs rmap
      (Hinv: invariant tp)
      (Hdisjoint_res: forall laddr rmap',
          laddr <> (b, ofs) ->
          lockRes tp laddr = Some rmap' ->
          permMapsDisjoint2 rmap rmap')
      (Hdisjoint_thr: forall i (cnti: containsThread tp i),
          permMapsDisjoint2 (getThreadR cnti) rmap)
      (Hcoh_res: forall laddr rmap',
          laddr <> (b, ofs) ->
          lockRes tp laddr = Some rmap' ->
          permMapCoherence rmap.1 rmap'.2 /\
          permMapCoherence rmap'.1 rmap.2)
      (Hcoh_rmap: permMapCoherence rmap.1 rmap.2)
      (Hcoh_thr: forall i (cnti: containsThread tp i),
          permMapCoherence rmap.1 (getThreadR cnti).2 /\
          permMapCoherence (getThreadR cnti).1 rmap.2)
      (Hvalid1: forall ofs0,
          (ofs < ofs0 < ofs + lksize.LKSIZE)%Z -> lockRes tp (b, ofs0) = None)
      (Hvalid2: forall ofs0 : Z,
          (ofs0 < ofs < ofs0 + lksize.LKSIZE)%Z -> lockRes tp (b, ofs0) = None),
      invariant (updLockSet tp (b, ofs) rmap).
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    constructor.
    - intros. rewrite! gLockSetRes.
      now auto.
    - intros.
      destruct (EqDec_address (b, ofs) laddr1).
      + subst.
        erewrite gssLockRes in Hres1. inversion Hres1; subst.
        erewrite gsoLockRes in Hres2 by eauto.
        eapply Hdisjoint_res;
          now eauto.
      + erewrite gsoLockRes in Hres1 by eauto.
        destruct (EqDec_address (b, ofs) laddr2).
        * subst.
          erewrite gssLockRes in Hres2.
          inversion Hres2; subst.
          eapply permMapsDisjoint2_comm.
          now eauto.
        * erewrite gsoLockRes in Hres2 by eauto.
          now eauto.
    - intros.
      destruct (EqDec_address (b, ofs) laddr).
      + subst.
        erewrite gssLockRes in Hres.
        inversion Hres; subst.
        now eapply Hdisjoint_thr.
      + erewrite gsoLockRes in Hres by eauto.
        rewrite gLockSetRes.
        now eauto.
    - intros.
      rewrite gLockSetRes.
      split; intros; [rewrite gLockSetRes;
                      eapply (thread_data_lock_coh0 _ cnti).1|].
      destruct (EqDec_address (b, ofs) laddr).
      + subst.
        rewrite gssLockRes in H.
        inversion H; subst.
        eapply Hcoh_thr.
      + erewrite gsoLockRes in H by eauto.
        eapply thread_data_lock_coh0; eauto.
    - intros.
      destruct (EqDec_address (b, ofs) laddr).
      + subst. erewrite gssLockRes in Hres.
        inversion Hres; subst.
        split; intros;
          [rewrite gLockSetRes; eapply Hcoh_thr|].
        destruct (EqDec_address (b, ofs) laddr').
        * subst.
          erewrite gssLockRes in H.
          inversion H; subst.
          eauto.
        * erewrite gsoLockRes in H by eauto.
          eapply Hcoh_res; eauto.
      + erewrite gsoLockRes in Hres by eauto.
        split; [intros; rewrite gLockSetRes;
                eapply (locks_data_lock_coh0 _ _ Hres).1 |].
        intros.
        destruct (EqDec_address (b, ofs) laddr').
        * subst.
          erewrite gssLockRes in H.
          inversion H; subst.
          eapply Hcoh_res;
            now eauto.
        * erewrite gsoLockRes in H by eauto.
          eapply locks_data_lock_coh0;
            now eauto.
    - intros b' ofs'.
      destruct (EqDec_address (b,ofs) (b', ofs')).
      + inversion e; subst.
        rewrite gsslockResUpdLock.
        intros ofs0 HH.
        erewrite gsolockResUpdLock.
        apply Hvalid1 || apply Hvalid2; auto.
        intros Hcontra; inversion Hcontra; subst.
        now omega.
      + rewrite gsolockResUpdLock; auto.
        specialize (lockRes_valid0 b' ofs').
        destruct (lockRes tp (b', ofs')) eqn:Hres;
          auto.
        intros ofs0 ineq.
        destruct (EqDec_address (b, ofs) (b',ofs0)).
        * inversion e; subst.
          apply Hvalid1 in ineq || apply Hvalid2 in ineq.
          rewrite ineq in Hres; inversion Hres.
        * rewrite gsolockResUpdLock;
            now eauto.
  Qed.

 (** [mem_compatible] is preserved by [addThread]*)
  (* NOTE: Strange statement, updThread doesn't need to be here probably*)
  Lemma mem_compatible_add:
    forall tp i (cnti: containsThread tp i) c pmap vf arg pmap2 m
      (Hcomp: mem_compatible
                (addThread
                   (updThread cnti c pmap) vf arg pmap2) m),
      mem_compatible (updThread cnti c pmap) m.
  Proof.
    intros.
    split.
    - intros j cntj.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      specialize (compat_th _ _ Hcomp cntj').
      erewrite gsoAddRes;
        by eauto.
    - intros l pmap' Hres.
      erewrite <- @gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres;
        by pose proof ((compat_lp _ _ Hcomp _ _ Hres)).
    - intros l rmap Hres.
      erewrite <- @gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres;
        by pose proof ((lockRes_blocks _ _ Hcomp _ _ Hres)).
  Qed.

  (** [mem_compatible] is preserved by [remLockSet] *)
  Lemma mem_compatible_remlock:
    forall tp m addr
      (Hinv: lr_valid (lockRes tp))
      (Hcomp: mem_compatible tp m),
      mem_compatible (remLockSet tp addr) m.
  Proof.
    intros.
    constructor.
    - eapply Hcomp.
    - intros.
      destruct (EqDec_address addr l).
      subst. rewrite gsslockResRemLock in H. discriminate.
      rewrite gsolockResRemLock in H; auto.
      eapply Hcomp; eauto.
    - intros l rmap Hres.
      destruct (EqDec_address addr l).
      subst. rewrite gsslockResRemLock in Hres. discriminate.
      rewrite gsolockResRemLock in Hres; auto.
      eapply Hcomp; eauto.
  Qed.

  (** [invariant] is preserved by [remLockSet]*)
  Lemma remLock_inv: forall ds a,
           invariant ds ->
           invariant (remLockSet ds a).
  Proof.
    intros.
    inversion H as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    econstructor; eauto.
    - intros.
      destruct (EqDec_address a laddr1), (EqDec_address a laddr2); subst;
        try (subst; by exfalso);
      try (erewrite gsslockResRemLock in Hres1);
        try (erewrite gsslockResRemLock in Hres2);
        try (discriminate);
      try (erewrite gsolockResRemLock in Hres1 by eauto);
      try (erewrite gsolockResRemLock in Hres2 by eauto);
      now eauto.
    - intros.
      destruct (EqDec_address a laddr); subst;
              try (erewrite gsslockResRemLock in Hres);
              try (erewrite gsolockResRemLock in Hres by eauto);
              try (discriminate);
              rewrite gRemLockSetRes;
              now eauto.
    - intros.
      pose proof (cntRemoveL' _ cnti) as cnti'.
      erewrite @gRemLockSetRes with (cnti := cnti').
      destruct (thread_data_lock_coh0 _ cnti').
      split; intros.
      rewrite gRemLockSetRes;
        now eauto.
      destruct (EqDec_address a laddr); subst;
        try (erewrite gsslockResRemLock in H2);
        try (erewrite gsolockResRemLock in H2 by eauto);
        try (discriminate);
        now eauto.
    - intros.
      destruct (EqDec_address a laddr); subst;
        try (erewrite gsslockResRemLock in Hres);
        try (erewrite gsolockResRemLock in Hres by eauto);
        try (discriminate);
        destruct (locks_data_lock_coh0 _ _ Hres);
        split; intros;
          [rewrite gRemLockSetRes; now eauto | idtac].
      destruct (EqDec_address a laddr'); subst;
        try (erewrite gsslockResRemLock in H2);
        try (erewrite gsolockResRemLock in H2 by eauto);
        try (discriminate);
        now eauto.
    - intros b ofs.
      specialize (lockRes_valid0 b ofs).
      destruct (lockRes (remLockSet ds a) (b, ofs)) eqn:Hres; auto.
      destruct (EqDec_address a (b, ofs)); subst.
      rewrite gsslockResRemLock in Hres. discriminate.
      rewrite gsolockResRemLock in Hres;
        auto.
      rewrite Hres in lockRes_valid0.
      intros ofs0 Hintv.
      specialize (lockRes_valid0 ofs0 Hintv).
      destruct (EqDec_address a (b, ofs0)); subst;
        [rewrite gsslockResRemLock | rewrite gsolockResRemLock];
        now auto.
  Qed.

  Lemma invariant_add:
    forall tp i (cnti: containsThread tp i) c pmap1 pmap2 vf arg
      (Hinv: invariant
               (addThread
                  (updThread cnti c pmap1)
                  vf arg pmap2)),
      invariant (updThread cnti c pmap1).
  Proof.
    intros.
    constructor.
    - intros k j cntk cntj Hneq.
      assert (cntk' := cntAdd vf arg pmap2 cntk).
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      pose proof ((no_race_thr _ Hinv) _ _ cntk' cntj' Hneq).
      erewrite @gsoAddRes with (cntj := cntk) in H; eauto.
      erewrite @gsoAddRes with (cntj := cntj) in H; eauto.
    - intros laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2.
      eapply (no_race_lr _ Hinv); eauto.
    - intros j laddr cntj rmap Hres.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      erewrite <- @gsoAddRes with (cntj' := cntj').
      eapply (no_race _ Hinv _ laddr);
        now eauto.
    - intros j cntj.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      erewrite <- @gsoAddRes with (cntj' := cntj').
      pose proof (thread_data_lock_coh _ Hinv _ cntj') as Hcoh.
      split.
      + intros k cntk.
        assert (cntk' := cntAdd vf arg pmap2 cntk).
        erewrite <- @gsoAddRes with (cntj' := cntk').
        eapply (proj1 Hcoh).
      + intros laddr rmap Hres.
        erewrite <- @gsoAddLPool
        with (vf := vf) (arg := arg) (p := pmap2) in Hres.
        eapply (proj2 Hcoh); eauto.
    - intros laddr rmap Hres.
      erewrite <- @gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres.
      pose proof (locks_data_lock_coh _ Hinv _ _ Hres ) as Hcoh.
      split.
      + intros j cntj.
        assert (cntj' := cntAdd vf arg pmap2 cntj).
        erewrite <- @gsoAddRes with (cntj' := cntj').
        eapply Hcoh.1.
      + intros laddr' rmap' Hres'.
        erewrite <- @gsoAddLPool
        with (vf := vf) (arg := arg) (p := pmap2) in Hres'.
        eapply Hcoh.2; eauto.
    - (* lr_valid *)
      intros b0 ofs0.
      pose proof (lockRes_valid _ Hinv).
      specialize (H b0 ofs0).
      rewrite gsoAddLPool in H;
        now auto.
  Qed.

  Lemma invariant_not_freeable:
    forall tp
      (Hinv: invariant tp),
    forall b ofs,
      (forall i (cnti: containsThread tp i), (getThreadR cnti).2 # b ofs <> Some Freeable) /\
      (forall laddr rmap (Hres: lockRes tp laddr = Some rmap), rmap.2 # b ofs <> Some Freeable).
  Proof.
    intros.
    split; intros;
    [pose proof ((thread_data_lock_coh _ Hinv _ cnti).1 _ cnti b ofs) |
     pose proof ((locks_data_lock_coh _ Hinv _ _ Hres).2 _ _ Hres b ofs)];
    apply perm_coh_not_freeable in H;
    assumption.
  Qed.

  Lemma invariant_freeable_empty_threads:
    forall tp i (cnti: containsThread tp i) b ofs
      (Hinv: invariant tp)
      (Hfreeable: (getThreadR cnti).1 !! b ofs = Some Freeable),
    forall j (cntj: containsThread tp j),
      (getThreadR cntj).2 !! b ofs = None /\
      (i <> j -> (getThreadR cntj).1 !! b ofs = None).
  Proof.
    intros.
    pose proof ((thread_data_lock_coh _ Hinv _ cntj).1 _ cnti b ofs) as Hcoh.
    rewrite Hfreeable in Hcoh.
    simpl in Hcoh.
    split.
    simpl.
    destruct ((OrdinalPool.getThreadR cntj).2 !! b ofs); auto; now exfalso.
    intros Hneq.
    pose proof ((no_race_thr _ Hinv _ _ cnti cntj Hneq).1 b ofs).
    rewrite Hfreeable in H.
    apply no_race_racy in H; eauto using racy.
    inversion H;
      now auto.
  Qed.

  Lemma invariant_freeable_empty_locks:
    forall tp i (cnti: containsThread tp i) b ofs
      (Hinv: invariant tp)
      (Hfreeable: (getThreadR cnti).1 !! b ofs = Some Freeable),
    forall laddr rmap,
      lockRes tp laddr = Some rmap ->
      rmap.1 !! b ofs = None /\
      rmap.2 !! b ofs = None.
  Proof.
    intros.
    pose proof ((locks_data_lock_coh _ Hinv _ _ H).1 _ cnti b ofs) as Hcoh.
    pose proof ((no_race _ Hinv _  _ cnti _ H).1 b ofs) as Hdisjoint.
    rewrite Hfreeable in Hdisjoint, Hcoh.
    split.
    apply no_race_racy in Hdisjoint; eauto using racy.
    inversion Hdisjoint;
      now auto.
    simpl in Hcoh;
      destruct (rmap.2 !! b ofs); eauto; by exfalso.
  Qed.

  Lemma mem_compatible_invalid_block:
    forall tp m b ofs
      (Hcomp: mem_compatible tp m)
      (Hinvalid: ~ Mem.valid_block m b),
      (forall i (cnti: containsThread tp i),
          (getThreadR cnti).1 !! b ofs = None /\
          (getThreadR cnti).2 !! b ofs = None) /\
      (forall laddr rmap,
          lockRes tp laddr = Some rmap ->
          rmap.1 !! b ofs = None /\
          rmap.2 !! b ofs = None).
  Proof.
    intros.
    destruct Hcomp.
    split.
    - intros.
      split;
        eapply permMapLt_invalid_block;
        eauto;
        now eapply compat_th.
    - intros.
      split;
        eapply permMapLt_invalid_block;
        eauto;
        eapply compat_lp;
        now eauto.
  Qed.

  (** ** Lemmas about initial state*)

  (** The initial thread is thread 0*)
  Lemma init_thread:
    forall m m' pmap f arg tp i
      (Hinit: init_mach pmap m tp m' f arg),
      containsThread tp i ->
      i = 0.
  Proof.
    intros.
    simpl in Hinit.
    unfold DryHybridMachine.init_mach in *.
    destruct Hinit as (? & Hinit & Hpmap).
    simpl in H. subst.
    unfold OrdinalPool.mkPool in *. simpl in *.
    unfold OrdinalPool.containsThread in *. simpl in *.
    clear - H.
    ssromega.
  Qed.

  (** [getThreadR] on the initial thread returns the [access_map] that was used
  in [init_mach] and the [empty_map]*)
  Lemma getThreadR_init:
    forall pmap m m' f arg tp
      (Hinit: init_mach pmap m tp m' f arg)
      (cnt: containsThread tp 0),
      getThreadR cnt = (getCurPerm m', empty_map).
  Proof.
    intros.
    simpl in *.
    unfold DryHybridMachine.init_mach in *.
    destruct Hinit as (? & Hinit & ?); subst.
    reflexivity.
  Qed.

  (** There are no locks in the initial machine *)
  Lemma init_lockRes_empty:
    forall m m' pmap f arg tp laddr
      (Hinit: init_mach pmap m tp m' f arg),
      lockRes tp laddr = None.
  Proof.
    intros.
    simpl in *.
    unfold DryHybridMachine.init_mach in Hinit.
    destruct Hinit as (? & Hinit & ?).
    subst.
    simpl.
    unfold OrdinalPool.mkPool.
    unfold OrdinalPool.lockRes.
    rewrite OrdinalPool.find_empty.
    reflexivity.
  Qed.

  (** The [invariant] holds for the initial state*)
  Lemma initial_invariant:
    forall m m' pmap f arg tp
      (Hinit: init_mach pmap m tp m' f arg),
      invariant tp.
  Proof.
    intros.
    constructor.
    - intros.
      pose proof (init_thread Hinit cnti); subst.
      pose proof (init_thread Hinit cntj); subst.
      exfalso. auto.
    - intros.
      erewrite init_lockRes_empty in Hres1 by eauto.
      discriminate.
    - intros.
      erewrite init_lockRes_empty in Hres by eauto.
      discriminate.
    - intros.
      split.
      + intros.
        pose proof (init_thread Hinit cnti); subst.
        pose proof (init_thread Hinit cntj); subst.
        Tactics.pf_cleanup.
        erewrite getThreadR_init by eauto.
        simpl.
        intros ? ?.
        rewrite empty_map_spec.
        now apply perm_coh_empty_1.
      + intros.
        erewrite init_lockRes_empty in H by eauto.
        discriminate.
    - intros.
      erewrite init_lockRes_empty in Hres by eauto.
      discriminate.
    - intros b ofs.
      destruct (lockRes tp (b, ofs)) eqn:Hres; auto.
      erewrite init_lockRes_empty in Hres by eauto.
      discriminate.
  Qed.

End ThreadPoolWF.
End ThreadPoolWF.


(** Assumptions on the threadwise semantics of the machine *)

(** ** Lemmas about threadwise semantics*)
Module CoreLanguage.
  Import event_semantics.
    Section CoreLanguage.
      Context {Sem : Semantics}.

      Class SemAxioms :=
        { (** If the [Cur] permission is below [Writable] on some location then
              a thread step cannot change the contents at this location *)
          corestep_unchanged_on:
            forall  c m c' m' b ofs
              (Hstep: corestep (msem semSem) c m c' m')
              (Hvalid: Mem.valid_block m b)
              (Hstable: ~ Mem.perm m b ofs Cur Writable),
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'));          
          (** Memories between thread steps are related by [decay] of permissions*)
          corestep_decay:
            forall c c' m m',
              corestep semSem c m c' m' ->
              decay m m';
          (** [Mem.nextblock] is monotonic with respect to thread steps*)
          corestep_nextblock:
            forall c m c' m',
              corestep semSem c m c' m' ->
              (Mem.nextblock m <= Mem.nextblock m')%positive;
          (** A core cannot be both at external and halted *)
          at_external_halted_excl:
            forall q m, at_external semSem q m = None \/ forall i, ~ halted semSem q i;
          (** If the [Cur] permission is below [Writable] on some location then
              [initial_core] cannot change the contents at this location *)
          initial_core_unchanged_on:
            forall  i v args c m m' b ofs
               (Hstep: initial_core semSem i m c m' v args)
               (Hvalid: Mem.valid_block m b)
               (Hstable: ~ Mem.perm m b ofs Cur Writable),
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'));
          (** Memories after [initial_core] are related by [decay] of permissions*)
          initial_core_decay:
            forall i v args c m m',
              initial_core semSem i m c m' v args ->
              strong_decay m m';
          (** [Mem.nextblock] is monotonic with respect to [initial_core]*)
          initial_core_nextblock:
            forall i v args c m m',
              initial_core semSem i m c m' v args ->
              (Mem.nextblock m <= Mem.nextblock m')%positive;
        }.
      Class SemDet :=
        { (** The thread semantics are deterministic*)
          corestep_det: corestep_fun semSem;
          (** [initial_core] is deterministic *)
          initial_core_det:
            forall i m v args c c' m' m'',
              initial_core semSem i m c m' v args ->
              initial_core semSem i m c' m'' v args ->
              c = c' /\ m' = m''
        }.

      Context {SemAx : SemAxioms} {SemD : SemDet}.

      Lemma corestep_validblock:
        forall c m c' m',
          corestep semSem c m c' m' ->
          forall b, Mem.valid_block m b ->
               Mem.valid_block m' b.
      Proof.
        intros.
        eapply corestep_nextblock in H.
        unfold Mem.valid_block, Coqlib.Plt in *.
        zify;
          by omega.
      Qed.

      Lemma initial_core_validblock:
        forall i c m m' v args,
          initial_core semSem i m c m' v args ->
          forall b, Mem.valid_block m b ->
               Mem.valid_block m' b.
      Proof.
        intros.
        eapply initial_core_nextblock in H.
        unfold Mem.valid_block, Coqlib.Plt in *.
        zify;
          by omega.
      Qed.

      Definition ev_step_det:
        forall (m m' m'' : mem) (c c' c'' : semC) ev ev',
          ev_step semSem c m ev c' m' ->
          ev_step semSem c m ev' c'' m'' -> c' = c'' /\ m' = m'' /\ ev = ev'.
      Proof.
        intros.
        assert (Hcore := ev_step_ax1 _ _ _ _ _ _ H).
        assert (Hcore' := ev_step_ax1 _ _ _ _ _ _ H0).
        assert (Heq := corestep_det _ _  _ _ _ _ Hcore Hcore').
        destruct Heq; repeat split; auto.
        eapply ev_step_fun;
          now eauto.
      Qed.

      Lemma ev_unchanged_on:
        forall c m c' m' b ofs ev
          (Hstep: ev_step semSem c m ev c' m')
          (Hvalid: Mem.valid_block m b)
          (Hstable: ~ Mem.perm m b ofs Cur Writable),
          Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
          Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
      Proof.
        intros.
        apply ev_step_ax1 in Hstep.
        eapply corestep_unchanged_on;
          now eauto.
      Qed.

      Lemma ev_step_decay:
        forall c c' m m' ev,
          ev_step semSem c m ev c' m' ->
          decay m m'.
      Proof.
        intros.
        apply ev_step_ax1 in H.
        eapply corestep_decay;
          now eauto.
      Qed.

      Lemma ev_step_nextblock:
        forall  c m ev c' m',
          ev_step semSem c m ev c' m' ->
          (Mem.nextblock m <= Mem.nextblock m')%positive.
      Proof.
        intros.
        apply ev_step_ax1 in H.
        eapply corestep_nextblock;
          now eauto.
      Qed.

      Lemma ev_step_validblock:
        forall  c m ev c' m',
          ev_step semSem c m ev c' m' ->
          forall b, Mem.valid_block m b ->
               Mem.valid_block m' b.
      Proof.
        intros.
        eapply ev_step_ax1 in H.
        eapply corestep_nextblock in H.
        unfold Mem.valid_block, Coqlib.Plt in *.
        zify;
          by omega.
      Qed.

    End CoreLanguage.
End CoreLanguage.


(** ** Lemmas about the threadwise semantics with respect to a (dry) concurrent machine*)
Module CoreLanguageDry.
  Import CoreLanguage.
  Import HybridMachine ThreadPool event_semantics HybridMachineSig.

  Section CoreLanguageDry.
    Context {Sem : Semantics}
            {SemAx : SemAxioms}.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.dryResources.
    
    (** Take an instance of the Dry Machine *)
    Existing Instance DryHybridMachine.DryHybridMachineSig.

  (** Lemmas about containsThread and coresteps *)

  Lemma corestep_containsThread:
    forall (tp : t)  c c' m m' p i j ev
      (Hcnti : containsThread tp i)
      (Hcntj: containsThread tp j)
      (Hcorestep: ev_step semSem c m ev c' m')
      (Hcode: getThreadC Hcnti = Krun c),
      containsThread (updThread Hcnti (Krun c') p) j.
  Proof.
    intros.
      by eapply cntUpdate.
  Qed.

  Lemma corestep_containsThread':
    forall (tp : t)  c c' m m' p i j ev
      (Hcnti : containsThread tp i)
      (Hcntj : containsThread (updThread Hcnti (Krun c') p) j)
      (Hcorestep: ev_step semSem c m ev c' m')
      (Hcode: getThreadC Hcnti = Krun c),
      containsThread tp j.
  Proof.
    intros.
      by eapply cntUpdate'; eauto.
  Qed.

  (** *** Lemmas about invariants preserved by coresteps*)

   (** [mem_compatible] is preserved by coresteps*)
  Lemma decay_compatible:
    forall (tp : t)  (m m' : mem) i
      (pf : containsThread tp i) (c': semC)
      (Hinv: invariant tp)
      (Hcompatible : mem_compatible tp m)
      (Hdecay: decay (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1) m')
      (Hvalid_blocks: forall b, Mem.valid_block m b -> Mem.valid_block m' b), 
      mem_compatible (updThread pf (Krun c') (getCurPerm m', (getThreadR pf).2)) m'.
  Proof.
    intros.
    constructor.
    { intros tid cnt.
      (* tid is also a valid thread in tp*)
      assert (cnt0 : containsThread tp tid)
        by (eapply cntUpdate' in cnt; auto).
      (* and it's resources are below the maximum permissions on the memory*)
      destruct (DryHybridMachine.compat_th _ _ Hcompatible cnt0) as [Hlt1 Hlt2].
      (* let's prove a slightly different statement that will reduce proof duplication*)
      assert (Hhelper: forall b ofs, Mem.perm_order'' ((getMaxPerm m') !! b ofs) ((getThreadR cnt).1 !! b ofs)  /\
                                Mem.perm_order''  ((getMaxPerm m') !! b ofs) ((getThreadR cnt).2 !! b ofs)).
      { intros b ofs.
        (* we proceed by case analysis on whether the block was a valid one or not*)
        destruct (valid_block_dec (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1) b)
          as [Hvalid|Hinvalid].
        - (*case it's a valid block*)
          destruct (Hdecay b ofs) as [ _ HdecayValid].
          destruct (HdecayValid Hvalid) as [Hfreed | Heq]; clear Hdecay.
          + (* case it is a block that was freed *)
            destruct (Hfreed Cur) as [HFree Hdrop].
            (* since the data of thread tid have a Freeable permission on (b,
                 ofs) it must be that no lock permission exists in the threadpool and
                 hence on thread tid as well*)
            assert (Hlock_empty: (getThreadR cnt)#2 !! b ofs = None).
            { destruct (DryHybridMachine.thread_data_lock_coh _ Hinv _ cnt0) as [Hcoh _].
              specialize (Hcoh _ pf b ofs).
              assert (Hp := restrPermMap_Cur (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
              unfold permission_at in Hp.
              rewrite <- Hp, HFree in Hcoh.
              simpl in Hcoh.
              destruct (((OrdinalPool.getThreadR cnt0)#2) # b ofs) eqn:?;
                       first by exfalso.
              simpl in Hcoh.
              destruct (i == tid) eqn:Htid; move/eqP:Htid=>Htid; subst.
              - rewrite gssThreadRes. Tactics.pf_cleanup. simpl.
                assumption.
              - erewrite gsoThreadRes with (cntj := cnt0) by assumption.
                assumption.
            }
            rewrite Hlock_empty.
            (* and that concludes the case for lock permissions*)
            split; [idtac | eapply po_None].
            (* for data permissions we proceed by case analysis*)
            destruct (i == tid) eqn:Htid;
              move/eqP:Htid=>Htid; subst;
                              (* for the thread that took the step it is
                              straightforward by the definition of [Mem.mem]*)
                              first by (rewrite gssThreadRes; simpl;
                                        apply getCur_Max).
            (* for other threads it must hold by the disjointess invariant
            that:*)
            assert (Hempty: (getThreadR cnt).1 # b ofs = None).
            { assert (Hp := restrPermMap_Cur (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
              unfold permission_at in Hp. rewrite Hp in HFree.
              assert (Hno_race := DryHybridMachine.no_race_thr _ Hinv _ _ pf cnt0 Htid).
              unfold permMapsDisjoint2 in Hno_race.
              pose proof (proj1 Hno_race b ofs) as Hunion.
              assert (Hnot_racy : not_racy ((getThreadR cnt0).1 # b ofs)).
              eapply no_race_racy with (p1 := (getThreadR pf).1 # b ofs); eauto.
              rewrite HFree. constructor.
              rewrite gsoThreadRes; auto.
                by inversion Hnot_racy.
            }
            rewrite Hempty.
            now apply po_None.
          + (* Case where the permission between the two states remained the same*)
            destruct (i == tid) eqn:Htid;
              move/eqP:Htid=>Htid; subst.
            * rewrite gssThreadRes. simpl.
              split. eapply getCur_Max.
              rewrite getMaxPerm_correct. unfold permission_at.
              assert (HeqCur := Heq Max).
              rewrite <- HeqCur.
              Tactics.pf_cleanup.
              assert (Hrestr_max := restrPermMap_Max Hlt1 b ofs).
              unfold permission_at in Hrestr_max.
              rewrite Hrestr_max.
              eauto.
            * (*case it's  another thread*)
              rewrite gsoThreadRes; auto.
              assert (HeqCur := Heq Max).
              assert (Hrestr_max := restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
              unfold permission_at in Hrestr_max.
              rewrite getMaxPerm_correct. unfold permission_at.
              rewrite <- HeqCur.
              rewrite Hrestr_max;
                by eauto.
        - (*case it is an invalid block*)
          (* since the lock permissions don't chan and that block was
               invalid before it must be that the lock/data permissions the threads
               had are empty*)
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
          assert (Hp := restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
          unfold permission_at in Hp. rewrite Hp in Hinvalid.
          specialize (Hlt1 b ofs).
          specialize (Hlt2 b ofs).
          rewrite Hinvalid in Hlt1 Hlt2.
          simpl in Hlt1, Hlt2.
          repeat match goal with
                 | [H: match ?Expr with _ => _ end |- _] =>
                   destruct Expr eqn:?
                 end; try by exfalso.
          (*we proceed by case analysis on the thread id*)
          destruct (i == tid) eqn:Htid; move/eqP:Htid => Htid; subst.
          +
            (*for the thread that stepped the data permissions may have
                changed. But the goal is easily discharged by the Max> Cur invariant
                of [Mem.mem]*)
            split; rewrite gssThreadRes; simpl;
              [now eapply getCur_Max| Tactics.pf_cleanup; rewrite Heqo; now apply po_None].
          + (*for different threads the permission maps did not change, hence
                remain empty at this location*)
            erewrite! gsoThreadRes with (cntj := cnt0) by eauto.
            rewrite Heqo0 Heqo.
            split; simpl; now apply po_None.
      }
      split; intros b ofs; destruct (Hhelper b ofs);
        assumption.
    }
    { (*likewise for lock resources*)
      simpl.
      intros l pmaps Hres.
      (* the resources in the lockpool did not change*)
      rewrite OrdinalPool.gsoThreadLPool in Hres.
      (* proving something more convenient*)
      assert (Hgoal: forall b ofs, Mem.perm_order'' ((getMaxPerm m') !! b ofs) (pmaps.1 !! b ofs) /\
                              Mem.perm_order'' ((getMaxPerm m') !! b ofs) (pmaps.2 !! b ofs)).
      {
        (* the resources on the lp are below the maximum permissions on the memory*)
        destruct (DryHybridMachine.compat_lp _ _ Hcompatible l _ Hres) as [Hlt1 Hlt2].
        intros b ofs.
        (* by cases analysis on whether b was a valid block*)
        destruct (valid_block_dec (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1) b)
          as [Hvalid|Hinvalid].
        - (*case it was a valid block *)
          destruct (Hdecay b ofs) as [ _ HdecayValid].
          destruct (HdecayValid Hvalid) as [Hfreed | Heq]; clear Hdecay.
          + destruct (Hfreed Cur) as [HFree Hdrop].
            (* since the data of thread tid have a Freeable permission on (b,
                 ofs) it must be that no lock permission exists in the threadpool and
                 hence on pmaps as well*)
            assert (HemptyL: pmaps.2 !! b ofs = None).
            { (*for lock permissions this is derived by coherency between data and locks*)
              destruct (DryHybridMachine.locks_data_lock_coh _ Hinv l _ Hres) as [Hcoh _].
              specialize (Hcoh _ pf b ofs).
              assert (Hp := restrPermMap_Cur (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
              unfold permission_at in Hp.
              rewrite <- Hp, HFree in Hcoh.
              simpl in Hcoh.
              destruct ((pmaps#2) # b ofs) eqn:?;
                       first by exfalso.
              reflexivity.
            }
            assert (HemptyD: pmaps.1 !! b ofs = None).
            { (*for data permissions this is derived by the disjointness invariant *)
              assert (Hp := restrPermMap_Cur (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
              unfold permission_at in Hp. rewrite Hp in HFree.
              destruct (DryHybridMachine.no_race _ Hinv _ _ pf _ Hres) as [Hno_race _].
              specialize (Hno_race b ofs).
              assert (Hnot_racy : not_racy (pmaps.1 # b ofs))
                by (eapply no_race_racy with (p1 := (getThreadR pf).1 # b ofs); eauto;
                    rewrite HFree;
                    constructor).
                by inversion Hnot_racy.
            }
            rewrite HemptyL HemptyD.
            split;
              by eapply po_None.
          + (* case the permission remained the same*)
            rewrite getMaxPerm_correct. unfold permission_at.
            assert (HeqCur := Heq Max).
            rewrite <- HeqCur.
            assert (Hrestr_max := restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
            unfold permission_at in Hrestr_max.
            rewrite Hrestr_max;
              by eauto.
        - (*case b was an invalid block*)
          (* since the lock permissions don't change and that block was
               invalid before it must be that the lock/data permissions the threads
               had are empty*)
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
          assert (Hp := restrPermMap_Max (DryHybridMachine.compat_th _ _ Hcompatible pf).1 b ofs).
          unfold permission_at in Hp. rewrite Hp in Hinvalid.
          specialize (Hlt1 b ofs).
          specialize (Hlt2 b ofs).
          rewrite Hinvalid in Hlt1 Hlt2.
          simpl in Hlt1, Hlt2.
          repeat match goal with
                 | [H: match ?Expr with _ => _ end |- _] =>
                   destruct Expr eqn:?
                 end; try by exfalso.
          split; now apply po_None.
      }
      split; intros b ofs; destruct (Hgoal b ofs); now auto.
    }
    { simpl.
      intros.
      rewrite OrdinalPool.gsoThreadLPool in H.
      eapply Hvalid_blocks.
      eapply (DryHybridMachine.lockRes_blocks _ _ Hcompatible);
        by eauto.
    }
  Qed.

  (** [mem_compatible] is preserved by coresteps*)
  Lemma corestep_compatible:
    forall (tp : t)  (m m' : mem) i ev
      (pf : containsThread tp i) (c c': semC)
      (Hinv: invariant tp)
      (Hcode: getThreadC pf = Krun c)
      (Hcompatible : mem_compatible tp m)
      (Hcorestep: ev_step semSem c (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1) ev c' m'),
      mem_compatible (updThread pf (Krun c') (getCurPerm m', (getThreadR pf).2)) m'.
  Proof.
    intros.
    assert (Hdecay := ev_step_decay _ _ _ _ _ Hcorestep).
    eapply decay_compatible; eauto.
    intros.
    eapply ev_step_validblock;
      now eauto.
  Qed.

  (** [mem_compatible] is preserved by [initial_core]*)
  Lemma initial_core_compatible:
    forall (tp : t)  (m m' : mem) i n vf arg
      (pf : containsThread tp i) (c: semC)
      (Hinv: invariant tp)
      (Hcompatible : mem_compatible tp m)
      (Hinitial: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1) c m' vf arg),
      mem_compatible (updThread pf (Krun c) (getCurPerm m', (getThreadR pf).2)) m'.
  Proof.
    intros.
    assert (Hdecay := initial_core_decay _ _ _ _ _ _ Hinitial).
    eapply strong_decay_implies_decay in Hdecay; eauto.
    eapply decay_compatible; eauto.
    intros.
    eapply initial_core_validblock;
      now eauto.
  Qed.

  (** Permission [decay] preserves disjointness*)
  Lemma decay_disjoint:
    forall m m' p
      (Hdecay: decay m m')
      (Hlt: permMapLt p (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint (getCurPerm m) p),
      permMapsDisjoint (getCurPerm m') p.
  Proof.
    intros.
    unfold permMapsDisjoint in *.
    intros.
    destruct (Hdecay b ofs) as [_ Hold].
    clear Hdecay.
    specialize (Hdisjoint b ofs).
    destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
    - destruct (Hold Hvalid) as [Hfree | Heq].
      + destruct (Hfree Cur) as [_ Hm']. rewrite getCurPerm_correct.
        assert (not_racy (permission_at m' b ofs Cur))
          by (unfold permission_at; rewrite Hm'; constructor).
          by eapply not_racy_union.
      + rewrite getCurPerm_correct. unfold permission_at.
        rewrite <- Heq. rewrite getCurPerm_correct in Hdisjoint.
        unfold permission_at in Hdisjoint. assumption.
    - assert (Hnone: (p # b ofs) = None).
      { apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
        unfold permMapLt in Hlt.
        specialize (Hlt b ofs).
        rewrite getMaxPerm_correct in Hlt.
        unfold permission_at in Hlt.
        rewrite Hinvalid in Hlt. simpl in Hlt.
        destruct (p # b ofs); tauto.
      }
      rewrite Hnone.
      rewrite perm_union_comm.
      eapply not_racy_union;
        by constructor.
  Qed.

  (** [permMapCoherence] is preserved by decay *)
  Lemma decay_coherence :
    forall (m m' : mem) (pmap : access_map)
      (Hdecay: decay m m')
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hcoh: permMapCoherence (getCurPerm m) pmap),
      permMapCoherence (getCurPerm m') pmap.
  Proof.
    intros.
    intros b ofs.
    destruct (Hdecay b ofs) as [_ Hold]; clear Hdecay.
    (* by case analysis on whether b was a valid block in m*)
    destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
    - (* if b was a valid block*)
      rewrite getCurPerm_correct. unfold permission_at.
      destruct (Hold Hvalid) as [Hfreed | Heq].
      + (* if b was freed*)
        destruct (Hfreed Cur) as [Hfree Hnone].
        rewrite Hnone. simpl.
        specialize (Hcoh b ofs).
        rewrite getCurPerm_correct in Hcoh.
        unfold permission_at in Hcoh.
        rewrite Hfree in Hcoh.
        simpl in Hcoh.
        destruct (pmap # b ofs); [by exfalso | auto].
      + (* if permission on (b,ofs) remained the same*)
        specialize (Heq Cur).
        rewrite <- Heq.
        specialize (Hcoh b ofs).
        rewrite getCurPerm_correct in Hcoh; unfold permission_at in *;
          assumption.
    - (*if b was an invalid block *)
      apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalid.
      specialize (Hlt b ofs).
      rewrite getMaxPerm_correct in Hlt.
      unfold permission_at in Hlt.
      rewrite Hinvalid in Hlt.
      simpl in Hlt.
      destruct (pmap # b ofs); first by exfalso.
      destruct ((getCurPerm m') # b ofs) as [p|]; auto;
        destruct p; auto.
  Qed.

  Lemma decay_invariant:
    forall tp m m1 m1' i (pf: containsThread tp i) c
      (Hinv : invariant tp)
      (Hcompatible : mem_compatible tp m)
      (Hrestrict_pmap : restrPermMap (Hcompatible i pf)#1 = m1)
      (Hdecay: decay m1 m1'),
      invariant (updThread pf (Krun c) (getCurPerm m1', (getThreadR pf)#2)).
  Proof.
    constructor.
    { (* non-interference between threads *)
      pose proof (DryHybridMachine.no_race_thr _ Hinv) as Hno_race; clear Hinv.
      intros j k.
      Opaque getThreadR.
      destruct (i == j) eqn:Heqj, (i == k) eqn:Heqk;
        move/eqP:Heqj=>Heqj;
                        move/eqP:Heqk=>Heqk; intros cntj' cntk' Hneq;
                                        assert (cntk: containsThread tp k)
                                        by (eapply cntUpdate'; eauto);
                                        assert (cntj: containsThread tp j)
                                          by (eapply cntUpdate'; eauto).
      - (* case i = j = k *)
        subst j k; exfalso; now auto.
      - (* case i = j but i <> k*)
        subst j. Tactics.pf_cleanup.
        (* the permissions of thread i will be the ones after stepping*)
        erewrite gssThreadRes.
        (* while the permission for thread k will remain the same*)
        erewrite @gsoThreadRes with (cntj := cntk) by assumption.
        destruct (Hno_race _ _ pf cntk Hneq) as [Hno_race1 Hno_race2].
        assert (Hlt := proj1 (DryHybridMachine.compat_th _ _ Hcompatible cntk)).
        subst m1.
        split.
        + (*disjointness of data permissions*)
          eapply decay_disjoint; eauto.
          unfold permMapLt in *.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs.
          rewrite getCurPerm_correct;
            by rewrite restrPermMap_Cur.
        + (*disjointness of lock permissions*)
          simpl; by eauto.
      - (* case i = k but j <> k (symmetric) *)
        subst k.
        erewrite @gsoThreadRes with (cntj := cntj); auto.
        erewrite gssThreadRes.
        destruct (Hno_race _ _ pf cntj Heqj) as [Hno_race1 Hno_race2].
        assert (Hlt := proj1 (DryHybridMachine.compat_th _ _ Hcompatible cntj)).
        subst m1.
        split.
        + (*disjointness of data permissions*)
          eapply permMapsDisjoint_comm.
          eapply decay_disjoint; eauto.
          unfold permMapLt in *.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs.
          rewrite getCurPerm_correct;
            by rewrite restrPermMap_Cur.
        + (*disjointness of lock permissions*)
          simpl;
            by eapply permMapsDisjoint_comm.
      - (*case both threads are not i*)
        erewrite @gsoThreadRes with (cntj := cntj); auto.
        erewrite @gsoThreadRes with (cntj := cntk); auto.
    }
    { (* non-interference in the lockpool*)
      intros.
      rewrite! gsoThreadLPool in Hres1, Hres2.
      eapply DryHybridMachine.no_race_lr;
        by eauto.
    }
    { intros j laddr cntj' rmap Hres.
      rewrite gsoThreadLPool in Hres.
      assert (cntj := cntUpdate' _ _ pf cntj').
      destruct (DryHybridMachine.no_race _ Hinv _ laddr cntj _ Hres) as [Hdata Hlocks]; clear Hinv.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hik; subst.
      - erewrite gssThreadRes.
        (* lock permissions did not change so second goal is trivial*)
        split; simpl; Tactics.pf_cleanup; eauto.
        (*for data permissions we will use the fact that decay preserves the
          invariant ([decay_disjoint])*)
        assert (Hlt := proj1 (DryHybridMachine.compat_lp _ _ Hcompatible _ _ Hres)).
        eapply decay_disjoint; eauto.
        intros b ofs.
        rewrite getMaxPerm_correct;
          by rewrite restrPermMap_Max.
        intros b ofs.
        rewrite getCurPerm_correct.
        rewrite restrPermMap_Cur;
          by (eapply Hdata; eauto).
      - (* if it is a different thread then the permissions didn't change and
          the result is straightforward*)
        erewrite @gsoThreadRes with (cntj := cntj);
          by eauto.
    }
    { (* coherence between lock and data permissions*)
      intros k cntk'.
      assert (cntk := cntUpdate' _ _ pf cntk').
      (* the lock permissions of threads remain the same through internal steps*)
      destruct (DryHybridMachine.thread_data_lock_coh _ Hinv _ cntk) as [Hthreads Hlockpool].
      assert (Heq: (getThreadR cntk').2 = (getThreadR cntk).2)
        by (destruct (i == k) eqn:Hik;
            move/eqP:Hik=>Hik; subst;
                         [erewrite gssThreadRes; Tactics.pf_cleanup |
                          erewrite gsoThreadRes with (cntj := cntk) by assumption];
                         reflexivity).
      rewrite Heq.
      split.
      - (* coherence between locks and data from a thread*)
        intros j cntj'.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
        + rewrite gssThreadRes.
          simpl.
          destruct (DryHybridMachine.compat_th _ _  Hcompatible cntk).
          eapply decay_coherence; eauto.
          intros b ofs.
          rewrite getMaxPerm_correct.
          rewrite restrPermMap_Max. eauto.
          intros b ofs.
          rewrite getCurPerm_correct.
          rewrite restrPermMap_Cur;
            now eapply Hthreads.
        + (*if i <> j *)
          erewrite gsoThreadRes with (cntj := cntUpdate' _ _ pf cntj') by assumption.
            by eauto.
      - (*coherence between locks and data from a lock*)
        intros laddr rmap Hres.
        rewrite gsoThreadLPool in Hres.
          by eauto.
    }
    { (* coherence between lock and data permissions *)
      intros laddr rmap Hres.
      rewrite gsoThreadLPool in Hres.
      split.
      - intros j cntj'.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
        + rewrite gssThreadRes.
          simpl.
          destruct (DryHybridMachine.compat_lp _ _ Hcompatible laddr _ Hres) as [_ Hlt].
          eapply decay_coherence; eauto.
          intros b ofs.
          rewrite getMaxPerm_correct.
          rewrite restrPermMap_Max; eauto.
          intros b ofs.
          rewrite getCurPerm_correct restrPermMap_Cur.
            by eapply (proj1 (DryHybridMachine.locks_data_lock_coh _ Hinv laddr _ Hres)); eauto.
        + erewrite gsoThreadRes with (cntj := cntUpdate' _ _ pf cntj') by assumption.
            by eapply (proj1 (DryHybridMachine.locks_data_lock_coh _ Hinv laddr _ Hres)); eauto.
      - intros ? ? Hres'.
        rewrite gsoThreadLPool in Hres'.
        eapply (proj2 (DryHybridMachine.locks_data_lock_coh _ Hinv laddr _ Hres)); eauto.
    }
    { (* well-formed locks*)
      eapply updThread_lr_valid;
        apply (DryHybridMachine.lockRes_valid _ Hinv).
    }
  Qed.
  
 (** [invariant] is preserved by a corestep *)
  Lemma initial_core_invariant:
    forall (tp : t)  (m : mem) (i : nat) n
      (pf : containsThread tp i) c m1 m' vf arg
      (Hinv: invariant tp)
      (Hcompatible: mem_compatible tp m)
      (Hrestrict_pmap: restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1 = m1)
      (Hcorestep: initial_core semSem n m1 c m' vf arg),
      invariant (updThread pf (Krun c) (getCurPerm m', (getThreadR pf).2)).
  Proof.
    intros.
    subst.
    apply initial_core_decay in Hcorestep.
    apply strong_decay_implies_decay in Hcorestep.
    eapply decay_invariant;
      eauto.
  Qed.
  
  (** [invariant] is preserved by a corestep *)
  Lemma corestep_invariant:
    forall (tp : t)  (m : mem) (i : nat)
      (pf : containsThread tp i) c m1 m1' c'
      (Hinv: invariant tp)
      (Hcompatible: mem_compatible tp m)
      (Hrestrict_pmap: restrPermMap (DryHybridMachine.compat_th _ _ Hcompatible pf).1 = m1)
      (Hcorestep: corestep semSem c m1 c' m1')
      (Hcore: getThreadC pf = Krun c),
      invariant (updThread pf (Krun c') (getCurPerm m1', (getThreadR pf).2)).
  Proof.
    intros.
    apply corestep_decay in Hcorestep.
    eapply decay_invariant;
      eauto.
  Qed.

  (** A corestep cannot change the contents of memory locations where permission is not above [Readable]*)
  Lemma corestep_stable_val:
    forall  c c' m m' pmap1 pmap2
      (Hlt1: permMapLt pmap1 (getMaxPerm m))
      (Hlt2: permMapLt pmap2 (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pmap1 pmap2 \/ permMapCoherence pmap1 pmap2)
      (Hstep: corestep semSem c (restrPermMap Hlt1) c' m'),
    forall b ofs (Hreadable: Mem.perm (restrPermMap Hlt2) b ofs Cur Readable),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    (** By disjoitness/coherence it must be that pmap1 has at most [Readable]
      permission on [(b,ofs)]*)
    assert (Hstable: ~ Mem.perm (restrPermMap Hlt1) b ofs Cur Writable).
    { intros Hcontra.
      assert (Hperm1 := restrPermMap_Cur Hlt1 b ofs).
      assert (Hperm2 := restrPermMap_Cur Hlt2 b ofs).
      unfold permission_at, Mem.perm in *.
      rewrite Hperm1 in Hcontra.
      rewrite Hperm2 in Hreadable.
      unfold Mem.perm_order' in *.
      (** Either [pmap1] is disjoint from [pmap2] or there is
        [permMapCoherence] relation between them*)
      destruct Hdisjoint as [Hdisjoint | Hdisjoint];
        specialize (Hdisjoint b ofs);
        destruct (pmap1 # b ofs) as [p1 |];
        destruct (pmap2 # b ofs) as [p2 |]; try (by exfalso);
          destruct p1; (try by inversion Hcontra); destruct p2;
            try (by inversion Hreadable);
            simpl in Hdisjoint; destruct Hdisjoint as [? ?];
              by discriminate.
    }
    apply @corestep_unchanged_on with (b := b) (ofs := ofs) in Hstep; auto.
    erewrite restrPermMap_valid.
    destruct (valid_block_dec m b); auto.
    apply invalid_block_empty with (pmap := pmap2) (ofs := ofs) in n; auto.
    unfold Mem.perm in Hreadable.
    pose proof (restrPermMap_Cur Hlt2 b ofs) as Heq.
    unfold permission_at in Heq.
    rewrite Heq in Hreadable.
    rewrite n in Hreadable.
    simpl; by exfalso.
  Qed.

  (** If some thread has permission above readable on some address then
    stepping another thread cannot change the value of that location*)
  Corollary corestep_disjoint_val:
    forall (tp : t)  (m m' : mem) i j (Hneq: i <> j)
      (c c' : semC)
      (pfi : containsThread tp i) (pfj : containsThread tp j)
      (Hcomp : mem_compatible tp m) (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj).1) b ofs Cur Readable \/
                  Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj).2) b ofs Cur Readable)
      (Hcorestep: corestep semSem c (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi).1) c' m')
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    destruct Hreadable;
      eapply corestep_stable_val; eauto;
        [left; eapply no_race_thr0; eauto| right; eapply (proj1 (thread_data_lock_coh0 j pfj)); eauto].
  Qed.

  Corollary corestep_disjoint_locks:
    forall (tp : t) (m m' : mem) i j (c c' : semC)
      (pfi : containsThread tp i) (pfj : containsThread tp j)
      (Hcomp : mem_compatible tp m) (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj).2) b ofs Cur Readable)
      (Hcorestep: corestep semSem c (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi).1) c' m')
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    eapply corestep_stable_val; eauto.
    right; eapply (proj1 (thread_data_lock_coh0 j pfj));
      by eauto.
  Qed.

  (** If some lock has permission above [Readable] on some address then
    stepping a thread cannot change the value of that location*)
  Lemma corestep_disjoint_val_lockpool :
    forall (tp : t)  (m m' : mem) i (c c' : semC)
      (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) addr pmap
      (Hlock: lockRes tp addr = Some pmap)
      (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp _ _ Hlock).1)
                           b ofs Cur Readable \/
                  Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp _ _ Hlock).2)
                           b ofs Cur Readable)
      (Hcorestep: corestep semSem c (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi).1) c' m')
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    destruct Hreadable;
      eapply corestep_stable_val; eauto;
        [left; eapply no_race0; eauto| right; eapply (proj1 (locks_data_lock_coh0 addr _ Hlock)); eauto].
  Qed.

  Lemma initial_core_stable_val:
    forall  n c m m' pmap1 pmap2 v arg
      (Hlt1: permMapLt pmap1 (getMaxPerm m))
      (Hlt2: permMapLt pmap2 (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pmap1 pmap2 \/ permMapCoherence pmap1 pmap2)
      (Hstep: initial_core semSem n (restrPermMap Hlt1) c m' v arg),
    forall b ofs (Hreadable: Mem.perm (restrPermMap Hlt2) b ofs Cur Readable),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    (** By disjoitness/coherence it must be that pmap1 has at most [Readable]
      permission on [(b,ofs)]*)
    assert (Hstable: ~ Mem.perm (restrPermMap Hlt1) b ofs Cur Writable).
    { intros Hcontra.
      assert (Hperm1 := restrPermMap_Cur Hlt1 b ofs).
      assert (Hperm2 := restrPermMap_Cur Hlt2 b ofs).
      unfold permission_at, Mem.perm in *.
      rewrite Hperm1 in Hcontra.
      rewrite Hperm2 in Hreadable.
      unfold Mem.perm_order' in *.
      (** Either [pmap1] is disjoint from [pmap2] or there is
        [permMapCoherence] relation between them*)
      destruct Hdisjoint as [Hdisjoint | Hdisjoint];
        specialize (Hdisjoint b ofs);
        destruct (pmap1 # b ofs) as [p1 |];
        destruct (pmap2 # b ofs) as [p2 |]; try (by exfalso);
          destruct p1; (try by inversion Hcontra); destruct p2;
            try (by inversion Hreadable);
            simpl in Hdisjoint; destruct Hdisjoint as [? ?];
              by discriminate.
    }
    apply @initial_core_unchanged_on with (b := b) (ofs := ofs) in Hstep; auto.
    erewrite restrPermMap_valid.
    destruct (valid_block_dec m b); auto.
    apply invalid_block_empty with (pmap := pmap2) (ofs := ofs) in n0; auto.
    unfold Mem.perm in Hreadable.
    pose proof (restrPermMap_Cur Hlt2 b ofs) as Heq.
    unfold permission_at in Heq.
    rewrite Heq in Hreadable.
    rewrite n0 in Hreadable.
    simpl; by exfalso.
  Qed.

    Corollary initial_core_disjoint_val:
    forall (tp : t)  (m m' : mem) i j (Hneq: i <> j) n v arg
      (c c' : semC)
      (pfi : containsThread tp i) (pfj : containsThread tp j)
      (Hcomp : mem_compatible tp m) (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj).1) b ofs Cur Readable \/
                  Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj).2) b ofs Cur Readable)
      (Hcorestep: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi).1) c m' v arg)
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    destruct Hreadable;
      eapply initial_core_stable_val; eauto;
        [left; eapply no_race_thr0; eauto| right; eapply (proj1 (thread_data_lock_coh0 j pfj)); eauto].
  Qed.

  Corollary initial_core_disjoint_locks:
    forall (tp : t) (m m' : mem) i j (c : semC) n v arg
      (pfi : containsThread tp i) (pfj : containsThread tp j)
      (Hcomp : mem_compatible tp m) (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfj).2) b ofs Cur Readable)
      (Hcorestep: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi).1) c m' v arg)
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    eapply initial_core_stable_val; eauto.
    right; eapply (proj1 (thread_data_lock_coh0 j pfj));
      by eauto.
  Qed.

  (** If some lock has permission above [Readable] on some address then
    stepping a thread cannot change the value of that location*)
  Lemma initial_core_disjoint_val_lockpool :
    forall (tp : t)  (m m' : mem) i (c c' : semC) n v arg
      (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) addr pmap
      (Hlock: lockRes tp addr = Some pmap)
      (b : block) (ofs : Z)
      (Hreadable: Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp _ _ Hlock).1)
                           b ofs Cur Readable \/
                  Mem.perm (restrPermMap (DryHybridMachine.compat_lp _ _ Hcomp _ _ Hlock).2)
                           b ofs Cur Readable)
      (Hcorestep: initial_core semSem n (restrPermMap (DryHybridMachine.compat_th _ _ Hcomp pfi).1) c m' v arg)
      (Hinv: invariant tp),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 thread_data_lock_coh0 locks_data_lock_coh0 lockRes_valid0].
    destruct Hreadable;
      eapply initial_core_stable_val; eauto;
        [left; eapply no_race0; eauto| right; eapply (proj1 (locks_data_lock_coh0 addr _ Hlock)); eauto].
  Qed.

  Lemma permMapLt_decay:
    forall pmap m m'
      (Hdecay: strong_decay m m')
      (Hlt: permMapLt pmap (getMaxPerm m)),
      permMapLt pmap (getMaxPerm m').
  Proof.
    intros.
    intros b ofs.
    destruct (Hdecay b ofs) as [Hfresh Hold].
    specialize (Hlt b ofs).
    erewrite getMaxPerm_correct in *.
    unfold permission_at in *. 
    destruct (valid_block_dec m b).
    - specialize (Hold v).
      erewrite <- Hold.
      assumption.
    - eapply Mem.nextblock_noaccess with (k := Max) (b:= b) (ofs := ofs) in n.
      rewrite n in Hlt.
      simpl in Hlt.
      destruct (pmap # b ofs); [now exfalso|].
      destruct ((Mem.mem_access m') # b ofs Max); simpl;
        now auto.
  Qed.
    
  End CoreLanguageDry.
End CoreLanguageDry.
