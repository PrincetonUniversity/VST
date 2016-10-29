(** * Lemmas about the Dry Machine*)
Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_context.

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).

(** This file holds various results about the dry machine*)

Module ThreadPoolWF (SEM: Semantics) (Machines: MachinesSig with Module SEM := SEM).

  Import Machines DryMachine ThreadPool.
  Lemma unlift_m_inv :
    forall tp tid (Htid : tid < (num_threads tp).+1) ord
      (Hunlift: unlift (ordinal_pos_incr (num_threads tp))
                       (Ordinal (n:=(num_threads tp).+1)
                                (m:=tid) Htid)=Some ord),
      nat_of_ord ord = tid.
  Proof.
    intros.
    assert (Hcontra: unlift_spec (ordinal_pos_incr (num_threads tp))
                                 (Ordinal (n:=(num_threads tp).+1)
                                          (m:=tid) Htid) (Some ord)).
    rewrite <- Hunlift.
    apply/unliftP.
    inversion Hcontra; subst.
    inversion H0.
    unfold bump.
    assert (pf: ord < (num_threads tp))
      by (by rewrite ltn_ord).
    assert (H: (num_threads tp) <= ord = false).
    rewrite ltnNge in pf.
    rewrite <- Bool.negb_true_iff. auto.
    rewrite H. simpl. rewrite add0n. reflexivity.
  Defined.

  (* NOTE: seems to be deprecated. Delete if so*)
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
    destruct Hinv.
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
    forall (tp : thread_pool) i (c : ctl)
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
    destruct Hinv.
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
          eauto.
        * erewrite gsoLockRes in Hres2 by eauto.
          eauto.
    - intros.
      destruct (EqDec_address (b, ofs) laddr).
      + subst.
        erewrite gssLockRes in Hres.
        inversion Hres; subst.
        eauto.
      + erewrite gsoLockRes in Hres by eauto.
        rewrite gLockSetRes.
        eauto.
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
          eapply Hcoh_res; eauto.
        * erewrite gsoLockRes in H by eauto.
          eapply locks_data_lock_coh0; eauto.
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
        destruct (lockRes tp (b', ofs')) eqn:Hres; auto.
        intros ofs0 ineq.
        destruct (EqDec_address (b, ofs) (b',ofs0)).
        * inversion e; subst.
          apply Hvalid1 in ineq || apply Hvalid2 in ineq.
          rewrite ineq in Hres; inversion Hres.
        * rewrite gsolockResUpdLock; auto.
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
      specialize (Hcomp _ cntj').
      erewrite gsoAddRes;
        by eauto.
    - intros l pmap' Hres.
      erewrite <- gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres;
        by pose proof ((compat_lp Hcomp _ Hres)).
    - intros l rmap Hres.
      erewrite <- gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres;
        by pose proof ((lockRes_blocks Hcomp _ Hres)).
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
  Admitted.
  
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
      pose proof ((no_race_thr Hinv) _ _ cntk' cntj' Hneq).
      erewrite @gsoAddRes with (cntj := cntk) in H; eauto.
      erewrite @gsoAddRes with (cntj := cntj) in H; eauto.
    - intros laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2.
      eapply (no_race_lr Hinv); eauto.
    - intros j laddr cntj rmap Hres.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      erewrite <- @gsoAddRes with (cntj' := cntj').
      eapply (no_race Hinv); eauto.
    - intros j cntj.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      erewrite <- @gsoAddRes with (cntj' := cntj').
      pose proof (thread_data_lock_coh Hinv cntj') as Hcoh.
      split.
      + intros k cntk.
        assert (cntk' := cntAdd vf arg pmap2 cntk).
        erewrite <- @gsoAddRes with (cntj' := cntk').
        eapply (proj1 Hcoh).
      + intros laddr rmap Hres.
        erewrite <- gsoAddLPool
        with (vf := vf) (arg := arg) (p := pmap2) in Hres.
        eapply (proj2 Hcoh); eauto.
    - intros laddr rmap Hres.
      erewrite <- gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres.
      pose proof (locks_data_lock_coh Hinv _ Hres ) as Hcoh.
      split.
      + intros j cntj.
        assert (cntj' := cntAdd vf arg pmap2 cntj).
        erewrite <- @gsoAddRes with (cntj' := cntj').
        eapply Hcoh.1.
      + intros laddr' rmap' Hres'.
        erewrite <- gsoAddLPool
        with (vf := vf) (arg := arg) (p := pmap2) in Hres'.
        eapply Hcoh.2; eauto.
    - (* lr_valid *)
      intros b0 ofs0.
      pose proof (lockRes_valid Hinv).
      specialize (H b0 ofs0).
      rewrite gsoAddLPool in H. auto.
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
    [pose proof ((thread_data_lock_coh Hinv cnti).1 _ cnti b ofs) |
     pose proof ((locks_data_lock_coh Hinv _ Hres).2 _ _ Hres b ofs)];
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
  Admitted.
  
  Lemma invariant_freeable_empty_locks:
    forall tp i (cnti: containsThread tp i) b ofs
      (Hinv: invariant tp)
      (Hfreeable: (getThreadR cnti).1 !! b ofs = Some Freeable),
    forall laddr rmap,
      lockRes tp laddr = Some rmap ->
      rmap.1 !! b ofs = None /\
      rmap.2 !! b ofs = None.
  Proof.
  Admitted.

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
        eapply compat_th0.
    - intros.
      split;
        eapply permMapLt_invalid_block;
        eauto;
        eapply compat_lp0;
        eauto.
  Qed.

  (** ** Lemmas about initial state*)

  (** The initial thread is thread 0*)
  Lemma init_thread:
    forall the_ge pmap f arg tp i
      (Hinit: init_mach pmap the_ge f arg = Some tp),
      containsThread tp i ->
      i = 0.
  Proof.
    intros.
    unfold init_mach in *.
    unfold initial_machine in *.
    repeat match goal with
           | [H: match ?Expr with _ => _ end = _ |- _] =>
             destruct Expr eqn:?; try discriminate
           end.
    simpl in Hinit; inversion Hinit; subst.
    unfold containsThread in *. simpl in *.
    clear - H.
    destruct i.
    reflexivity.
    ssromega.
  Qed.

  (** [getThreadR] on the initial thread returns the [access_map] that was used
  in [init_mach] and the [empty_map]*)
  Lemma getThreadR_init:
    forall the_ge pmap f arg tp
      (Hinit: init_mach (Some pmap) the_ge f arg = Some tp)
      (cnt: containsThread tp 0), 
      getThreadR cnt = (pmap.1, empty_map).
  Proof.
    intros.
    unfold init_mach in *.
    unfold initial_machine in *.
    repeat match goal with
           | [H: match ?Expr with _ => _ end = _ |- _] =>
             destruct Expr eqn:?; try discriminate
           end.
    inversion Hinit.
    subst.
    reflexivity.
  Qed.

  (** If there was no [access_map] provided [init_mach] is not defined*)
  Lemma init_mach_none:
    forall the_ge f arg,
      init_mach None the_ge f arg = None.
  Proof.
    intros.
    unfold init_mach.
    destruct (initial_core (event_semantics.msem ThreadPool.SEM.Sem) the_ge f arg);
      reflexivity.
  Qed.

  (** There are no locks in the initial machine *)
  Lemma init_lockRes_empty:
    forall the_ge pmap f arg tp laddr
      (Hinit: init_mach pmap the_ge f arg = Some tp),
      lockRes tp laddr = None.
  Proof.
    intros.
    unfold init_mach in Hinit.
    destruct (initial_core (event_semantics.msem ThreadPool.SEM.Sem) the_ge f arg); try discriminate.
    destruct pmap; try discriminate.
    unfold initial_machine in Hinit.
    inversion Hinit.
    unfold lockRes.
    rewrite threadPool.find_empty.
    reflexivity.
  Qed.

  (** The [invariant] holds for the initial state*)
  Lemma initial_invariant:
    forall the_ge pmap f arg tp
      (Hinit: init_mach pmap the_ge f arg = Some tp),
      invariant tp.
  Proof.
    intros.
    constructor.
    - intros.
      pose proof (init_thread _ _ _ _ Hinit cnti); subst.
      pose proof (init_thread _ _ _ _ Hinit cntj); subst.
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
        destruct pmap as [pmap |];
          [|rewrite init_mach_none in Hinit; discriminate].
        pose proof (init_thread _ _ _ _ Hinit cnti); subst.
        pose proof (init_thread _ _ _ _ Hinit cntj); subst.
        pf_cleanup.
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

(** Assumptions on the threadwise semantics of the machine *)
Module Type SemanticsAxioms (SEM: Semantics).

  Import event_semantics SEM.
  (** The thread semantics are deterministic*)
  Parameter corestep_det: corestep_fun Sem.

  (** If the [Cur] permission is below [Writable] on some location then a thread
  step cannot change the contents at this location *)
  Parameter corestep_unchanged_on:
    forall the_ge c m c' m' b ofs
      (Hstep: corestep (msem Sem) the_ge c m c' m')
      (Hvalid: Mem.valid_block m b)
      (Hstable: ~ Mem.perm m b ofs Cur Writable),
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).

  (** Memories between thread steps are related by [decay] of permissions*)
  Parameter corestep_decay:
    forall ge c c' m m',
      corestep Sem ge c m c' m' ->
      decay m m'.

  (** [Mem.nextblock] is monotonic with respect to thread steps*)
  Parameter corestep_nextblock:
    forall ge c m c' m',
      corestep Sem ge c m c' m' ->
      (Mem.nextblock m <= Mem.nextblock m')%positive.
End SemanticsAxioms.

(** ** Lemmas about threadwise semantics*)
Module CoreLanguage (SEM : Semantics) (SemAxioms: SemanticsAxioms SEM).
  Import SEM event_semantics SemAxioms.
  
  Lemma corestep_validblock:
    forall ge c m c' m',
      corestep Sem ge c m c' m' ->
      forall b, Mem.valid_block m b ->
           Mem.valid_block m' b.
  Proof.
    intros.
    eapply corestep_nextblock in H.
    unfold Mem.valid_block, Coqlib.Plt in *.
    zify;
      by omega.
  Qed.

  Definition ev_step_det:
    forall (m m' m'' : mem) (ge : G) (c c' c'' : C) ev ev',
      ev_step Sem ge c m ev c' m' ->
      ev_step Sem ge c m ev' c'' m'' -> c' = c'' /\ m' = m'' /\ ev = ev'.
  Proof.
    intros.
    assert (Hcore := ev_step_ax1 _ _ _ _ _ _ _ H).
    assert (Hcore' := ev_step_ax1 _ _ _ _ _ _ _ H0).
    assert (Heq := corestep_det _ _ _  _ _ _ _ Hcore Hcore').
    destruct Heq; repeat split; auto.
    eapply ev_step_fun; eauto.
  Qed.

  Lemma ev_unchanged_on:
    forall the_ge c m c' m' b ofs ev
      (Hstep: ev_step Sem the_ge c m ev c' m')
      (Hvalid: Mem.valid_block m b)
      (Hstable: ~ Mem.perm m b ofs Cur Writable),
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
      Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
  Proof.
    intros.
    apply ev_step_ax1 in Hstep.
    eapply corestep_unchanged_on; eauto.
  Qed.

  Lemma ev_step_decay:
    forall ge c c' m m' ev,
      ev_step Sem ge c m ev c' m' ->
      decay m m'.
  Proof.
    intros.
    apply ev_step_ax1 in H.
    eapply corestep_decay; eauto.
  Qed.

  Lemma ev_step_nextblock:
    forall ge c m ev c' m',
      ev_step Sem ge c m ev c' m' ->
      (Mem.nextblock m <= Mem.nextblock m')%positive.
  Proof.
    intros.
    apply ev_step_ax1 in H.
      eapply corestep_nextblock; eauto.
    Qed.

    Lemma ev_step_validblock:
      forall ge c m ev c' m',
        ev_step Sem ge c m ev c' m' ->
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


(** ** Lemmas about the threadwise semantics with respect to a (dry) concurrent machine*)
Module CoreLanguageDry (SEM : Semantics) (SemAxioms: SemanticsAxioms SEM)
       (DryMachine : dry_machine.Concur.DryMachineSig SEM).
               
  Import SEM event_semantics SemAxioms DryMachine ThreadPool.

  Module CoreLanguage := CoreLanguage SEM SemAxioms.
  Import CoreLanguage.
  (* TODO: These proofs break the opaquness of the modules, they
    should be redone in an opaque way *)


  Ltac pf_cleanup :=
    repeat match goal with
           | [H1: invariant ?X, H2: invariant ?X |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M, H2: containsThread ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
             apply cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply cnt_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
             apply cntUpdate' in H2;
             assert (H1 = H2) by (by eapply cnt_irr); subst H2
           end.

    (** Lemmas about containsThread and coresteps *)
    Lemma corestep_containsThread:
      forall (tp : thread_pool) ge c c' m m' p i j ev
        (Hcnti : containsThread tp i)
        (Hcntj: containsThread tp j)
        (Hcorestep: ev_step Sem ge c m ev c' m')
        (Hcode: getThreadC Hcnti = Krun c),
        containsThread (updThread Hcnti (Krun c') p) j.
    Proof.
      intros.
        by eapply cntUpdate.
    Qed.

    Lemma corestep_containsThread':
      forall (tp : thread_pool) ge c c' m m' p i j ev
        (Hcnti : containsThread tp i)
        (Hcntj : containsThread (updThread Hcnti (Krun c') p) j)
        (Hcorestep: ev_step Sem ge c m ev c' m')
        (Hcode: getThreadC Hcnti = Krun c),
        containsThread tp j.
    Proof.
      intros.
        by eapply cntUpdate'; eauto.
    Qed.

    (** *** Lemmas about invariants preserved by coresteps*)

    (** [mem_compatible] is preserved by coresteps*)
    Lemma corestep_compatible:
      forall (tp : thread_pool) ge (m m' : mem) i ev
        (pf : containsThread tp i) (c c': C)
        (Hinv: invariant tp)
        (Hcode: getThreadC pf = Krun c)
        (Hcompatible : mem_compatible tp m)
        (Hcorestep: ev_step Sem ge c (restrPermMap (Hcompatible i pf).1) ev c' m'),
        mem_compatible (updThread pf (Krun c') (getCurPerm m', (getThreadR pf).2)) m'.
    Proof.
      intros.
      constructor. 
      { intros tid cnt.
        (* tid is also a valid thread in tp*)
        assert (cnt0 : containsThread tp tid)
          by (eapply cntUpdate' in cnt; auto).
        (* and it's resources are below the maximum permissions on the memory*)
        destruct (Hcompatible tid cnt0) as [Hlt1 Hlt2].
        (* by decay of permissions*)
        assert (Hdecay := ev_step_decay _ _ _ _ _ _ Hcorestep).
        (* let's prove a slightly different statement that will reduce proof duplication*)
        assert (Hhelper: forall b ofs, Mem.perm_order'' ((getMaxPerm m') !! b ofs) ((getThreadR cnt).1 !! b ofs)  /\
                                  Mem.perm_order''  ((getMaxPerm m') !! b ofs) ((getThreadR cnt).2 !! b ofs)).
        { intros b ofs.
          (* we proceed by case analysis on whether the block was a valid one or not*)
          destruct (valid_block_dec (restrPermMap (Hcompatible i pf).1) b)
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
              { destruct (thread_data_lock_coh Hinv cnt0) as [Hcoh _].
                specialize (Hcoh _ pf b ofs).
                assert (Hp := restrPermMap_Cur (Hcompatible i pf).1 b ofs).
                unfold permission_at in Hp.
                rewrite <- Hp, HFree in Hcoh.
                simpl in Hcoh.
                destruct (((getThreadR cnt0)#2) # b ofs) eqn:?;
                         first by exfalso.
                destruct (i == tid) eqn:Htid; move/eqP:Htid=>Htid; subst.
                - rewrite gssThreadRes. pf_cleanup. simpl.
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
              { assert (Hp := restrPermMap_Cur (Hcompatible i pf).1 b ofs).
                unfold permission_at in Hp. rewrite Hp in HFree.
                assert (Hno_race := no_race_thr Hinv pf cnt0 Htid).
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
                pf_cleanup.
                assert (Hrestr_max := restrPermMap_Max Hlt1 b ofs).
                unfold permission_at in Hrestr_max.
                rewrite Hrestr_max.
                eauto.
              * (*case it's  another thread*)            
                rewrite gsoThreadRes; auto.
                assert (HeqCur := Heq Max).
                assert (Hrestr_max := restrPermMap_Max (Hcompatible i pf).1 b ofs).
                unfold permission_at in Hrestr_max.
                rewrite getMaxPerm_correct. unfold permission_at.
                rewrite <- HeqCur.
                rewrite Hrestr_max;
                  by eauto.
          - (*case it is an invalid block*)
            (* since the lock permissions don't change and that block was
               invalid before it must be that the lock/data permissions the threads
               had are empty*)
            apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
            assert (Hp := restrPermMap_Max (Hcompatible i pf).1 b ofs).
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
                [now eapply getCur_Max| pf_cleanup; rewrite Heqo; now apply po_None].
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
        intros l pmaps Hres.
        (* the resources in the lockpool did not change*)
        rewrite gsoThreadLPool in Hres.
        (* proving something more convenient*)
        assert (Hgoal: forall b ofs, Mem.perm_order'' ((getMaxPerm m') !! b ofs) (pmaps.1 !! b ofs) /\
                                Mem.perm_order'' ((getMaxPerm m') !! b ofs) (pmaps.2 !! b ofs)).
        {
          (* the resources on the lp are below the maximum permissions on the memory*)
          destruct (compat_lp Hcompatible l Hres) as [Hlt1 Hlt2].
          (* by decay of permissions*)
          assert (Hdecay := ev_step_decay _ _ _ _ _ _ Hcorestep).
          intros b ofs.
          (* by cases analysis on whether b was a valid block*)
          destruct (valid_block_dec (restrPermMap (Hcompatible i pf).1) b)
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
                destruct (locks_data_lock_coh Hinv l Hres) as [Hcoh _].
                specialize (Hcoh _ pf b ofs).
                assert (Hp := restrPermMap_Cur (Hcompatible i pf).1 b ofs).
                unfold permission_at in Hp.
                rewrite <- Hp, HFree in Hcoh.
                simpl in Hcoh.
                destruct ((pmaps#2) # b ofs) eqn:?;
                         first by exfalso.
                reflexivity.
              }
              assert (HemptyD: pmaps.1 !! b ofs = None).
              { (*for data permissions this is derived by the disjointness invariant *)
                assert (Hp := restrPermMap_Cur (Hcompatible i pf).1 b ofs).
                unfold permission_at in Hp. rewrite Hp in HFree.
                destruct (no_race Hinv _ pf Hres) as [Hno_race _].
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
              assert (Hrestr_max := restrPermMap_Max (Hcompatible i pf).1 b ofs).
              unfold permission_at in Hrestr_max.
              rewrite Hrestr_max;
                by eauto.
          - (*case b was an invalid block*)
            (* since the lock permissions don't change and that block was
               invalid before it must be that the lock/data permissions the threads
               had are empty*)
            apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
            assert (Hp := restrPermMap_Max (Hcompatible i pf).1 b ofs).
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
      { intros.
        rewrite gsoThreadLPool in H.
        eapply corestep_validblock; eauto using ev_step_ax1.
        eapply (lockRes_blocks Hcompatible);
          by eauto.
      }
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

    (** [invariant] is preserved by a corestep *)
    Lemma corestep_invariant:
      forall (tp : thread_pool) ge (m : mem) (i : nat)
        (pf : containsThread tp i) c m1 m1' c'
        (Hinv: invariant tp)
        (Hcompatible: mem_compatible tp m)
        (Hrestrict_pmap: restrPermMap (Hcompatible i pf).1 = m1)
        (Hcorestep: corestep Sem ge c m1 c' m1')
        (Hcore: getThreadC pf = Krun c),
        invariant (updThread pf (Krun c') (getCurPerm m1', (getThreadR pf).2)).
    Proof.
      intros.
      apply corestep_decay in Hcorestep.
      constructor.
      { (* non-interference between threads *)
        pose proof (no_race_thr Hinv) as Hno_race; clear Hinv.
        intros j k.
        Opaque getThreadR.
        destruct (i == j) eqn:Heqj, (i == k) eqn:Heqk; move/eqP:Heqj=>Heqj;
          move/eqP:Heqk=>Heqk; simpl in *; intros cntj' cntk' Hneq;
                        assert (cntk: containsThread tp k)
                          by (eapply cntUpdate'; eauto);
                        assert (cntj: containsThread tp j)
                          by (eapply cntUpdate'; eauto).
        - (* case i = j = k *)
          subst j k; exfalso; now auto.
        - (* case i = j but i <> k*)
          subst j. pf_cleanup.
          (* the permissions of thread i will be the ones after stepping*)
          erewrite gssThreadRes.
          (* while the permission for thread k will remain the same*)
          erewrite @gsoThreadRes with (cntj := cntk) by assumption.
          destruct (Hno_race _ _ pf cntk Hneq) as [Hno_race1 Hno_race2].
          assert (Hlt := proj1 (compat_th Hcompatible cntk)).
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
          assert (Hlt := proj1 (compat_th Hcompatible cntj)).
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
        eapply no_race_lr;
          by eauto.
      }
      { intros j laddr cntj' rmap Hres.
        rewrite gsoThreadLPool in Hres.
        assert (cntj := cntUpdate' cntj').
        destruct (no_race Hinv laddr cntj Hres) as [Hdata Hlocks]; clear Hinv.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hik; subst.
        - erewrite gssThreadRes.
          (* lock permissions did not change so second goal is trivial*)
          split; simpl; pf_cleanup; eauto.
          (*for data permissions we will use the fact that decay preserves the
          invariant ([decay_disjoint])*)
          assert (Hlt := proj1 (compat_lp Hcompatible _ Hres)).
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
        assert (cntk := cntUpdate' cntk').
        (* the lock permissions of threads remain the same through internal steps*)
        destruct (thread_data_lock_coh Hinv cntk) as [Hthreads Hlockpool].
        assert (Heq: (getThreadR cntk').2 = (getThreadR cntk).2)
          by (destruct (i == k) eqn:Hik;
              move/eqP:Hik=>Hik; subst;
                           [erewrite gssThreadRes; pf_cleanup |
                            erewrite gsoThreadRes with (cntj := cntk) by assumption];
                           reflexivity).
        rewrite Heq.
        split.
        - (* coherence between locks and data from a thread*)
          intros j cntj'.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
          + rewrite gssThreadRes.
            simpl.
            destruct (compat_th Hcompatible cntk).
            eapply decay_coherence; eauto.
            intros b ofs.
            rewrite getMaxPerm_correct.
            rewrite restrPermMap_Max. eauto.
            intros b ofs.
            rewrite getCurPerm_correct.
            rewrite restrPermMap_Cur;
              now eapply Hthreads.
          + (*if i <> j *)
            erewrite gsoThreadRes with (cntj := cntUpdate' cntj') by assumption.
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
            destruct (compat_lp Hcompatible laddr Hres) as [_ Hlt].
            eapply decay_coherence; eauto.
            intros b ofs.
            rewrite getMaxPerm_correct.
            rewrite restrPermMap_Max; eauto.
            intros b ofs.
            rewrite getCurPerm_correct restrPermMap_Cur.
              by eapply (proj1 (locks_data_lock_coh Hinv laddr Hres)); eauto.
          + erewrite gsoThreadRes with (cntj := cntUpdate' cntj') by assumption.
              by eapply (proj1 (locks_data_lock_coh Hinv laddr Hres)); eauto.
        - intros ? ? Hres'.
          rewrite gsoThreadLPool in Hres'.
          eapply (proj2 (locks_data_lock_coh Hinv laddr Hres)); eauto.
      }
      { (* well-formed locks*)
        eapply updThread_lr_valid;
          apply (lockRes_valid Hinv).
      }
    Qed.

    (** A corestep cannot change the contents of memory locations where permission is not above [Readable]*)
    Lemma corestep_stable_val:
      forall ge c c' m m' pmap1 pmap2
        (Hlt1: permMapLt pmap1 (getMaxPerm m))
        (Hlt2: permMapLt pmap2 (getMaxPerm m))
        (Hdisjoint: permMapsDisjoint pmap1 pmap2 \/ permMapCoherence pmap1 pmap2)
        (Hstep: corestep Sem ge c (restrPermMap Hlt1) c' m'),
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
      apply corestep_unchanged_on with (b := b) (ofs := ofs) in Hstep; auto.
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
      forall (tp : thread_pool) ge (m m' : mem) i j (Hneq: i <> j)
        (c c' : C) 
        (pfi : containsThread tp i) (pfj : containsThread tp j)
        (Hcomp : mem_compatible tp m) (b : block) (ofs : Z) 
        (Hreadable: Mem.perm (restrPermMap (Hcomp j pfj).1) b ofs Cur Readable \/
                    Mem.perm (restrPermMap (Hcomp j pfj).2) b ofs Cur Readable)
        (Hcorestep: corestep Sem ge c (restrPermMap (Hcomp i pfi).1) c' m')
        (Hinv: invariant tp),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      destruct Hinv.
      destruct Hreadable;
        eapply corestep_stable_val; eauto;
          [left; eapply no_race_thr0; eauto| right; eapply (proj1 (thread_data_lock_coh0 j pfj)); eauto].
    Qed.

    Corollary corestep_disjoint_locks:
      forall (tp : thread_pool) ge (m m' : mem) i j (c c' : C) 
        (pfi : containsThread tp i) (pfj : containsThread tp j)
        (Hcomp : mem_compatible tp m) (b : block) (ofs : Z) 
        (Hreadable: Mem.perm (restrPermMap (Hcomp j pfj).2) b ofs Cur Readable)
        (Hcorestep: corestep Sem ge c (restrPermMap (Hcomp i pfi).1) c' m')
        (Hinv: invariant tp),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      destruct Hinv.
      eapply corestep_stable_val; eauto.
      right; eapply (proj1 (thread_data_lock_coh0 j pfj));
        by eauto.
    Qed.

    (** If some lock has permission above [Readable] on some address then
    stepping a thread cannot change the value of that location*)
    Lemma corestep_disjoint_val_lockpool :
      forall (tp : thread_pool) ge (m m' : mem) i (c c' : C)
        (pfi : containsThread tp i) (Hcomp : mem_compatible tp m) addr pmap
        (Hlock: lockRes tp addr = Some pmap)
        (b : block) (ofs : Z)
        (Hreadable: Mem.perm (restrPermMap (compat_lp Hcomp _ Hlock).1)
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap (compat_lp Hcomp _ Hlock).2)
                             b ofs Cur Readable)
        (Hcorestep: corestep Sem ge c (restrPermMap (Hcomp i pfi).1) c' m')
        (Hinv: invariant tp),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      destruct Hinv.
      destruct Hreadable;
        eapply corestep_stable_val; eauto;
          [left; eapply no_race0; eauto| right; eapply (proj1 (locks_data_lock_coh0 addr _ Hlock)); eauto].
    Qed.
    
End CoreLanguageDry.

(** These lemmas require the machines. But the machines are
parameterized by the semantics so they can be used by either
high-level or low-level languages*)
Module StepLemmas (SEM : Semantics)
       (Machine : MachinesSig with Module SEM := SEM).

  Module ThreadPoolWF := ThreadPoolWF SEM Machine.
  Import SEM event_semantics ThreadPoolWF.
  Import Machine DryMachine DryConc ThreadPool.

  (** [mem_compatible] is preserved by [updThreadC] *)
  Lemma updThreadC_compatible:
    forall (tp : thread_pool) m i (c : ctl)
      (ctn : containsThread tp i)
      (Hcomp: mem_compatible tp m),
      mem_compatible (updThreadC ctn c) m.
  Proof.
    intros.
    constructor.
    intros j cntj'.
    assert (cntj := cntUpdateC' _ _ cntj').
    specialize (Hcomp _ cntj).
    erewrite @gThreadCR with (cntj := cntj);
      by auto.
    intros.
    erewrite gsoThreadCLPool in H.
    destruct Hcomp;
      by eauto.
    intros.
    erewrite gsoThreadCLPool in H;
      eapply (lockRes_blocks Hcomp);
      by eauto.
  Qed.

  (** ***Lemmas about suspend steps*)

  (** [suspend_thread] is deterministic*)
  Lemma suspendC_step_det:
    forall tp tp' tp'' i (cnt: containsThread tp i)
      (Hstep: suspend_thread cnt tp')
      (Hstep': suspend_thread cnt tp''),
      tp' = tp''.
  Proof.
    intros.
    inversion Hstep; inversion Hstep'; subst.
    pf_cleanup. rewrite Hcode in Hcode0.
    inversion Hcode0; by subst.
  Qed.

  (** [FineConc.suspend_thread] is deterministic*)
  Lemma suspendF_containsThread:
    forall tp tp' i j (cnti: containsThread tp i)
      (Hsuspend: FineConc.suspend_thread cnti tp'),
      containsThread tp j <-> containsThread tp' j.
  Proof.
    intros; inversion Hsuspend; subst.
    split;
      [eapply cntUpdateC | eapply cntUpdateC'].
  Qed.

  (** [suspend_thread] does not change the number of threads*)
  Lemma suspendC_containsThread:
    forall tp tp' i j (cnti: containsThread tp i)
      (Hsuspend: DryConc.suspend_thread cnti tp'),
      containsThread tp j <-> containsThread tp' j.
  Proof.
    intros; inversion Hsuspend; subst.
    split;
      [eapply cntUpdateC | eapply cntUpdateC'].
  Qed.

  (** [mem_compatible] is preserved by [suspend_thread]*)
  Corollary suspendC_compatible:
    forall tp tp' m i (cnt: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hsuspend: DryConc.suspend_thread cnt tp'),
      mem_compatible tp' m.
  Proof.
    intros. inversion Hsuspend; subst.
      by eapply updThreadC_compatible.
  Qed.

  Corollary suspendF_compatible:
    forall tp tp' m i (cnt: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hsuspend: FineConc.suspend_thread cnt tp'),
      mem_compatible tp' m.
  Proof.
    intros. inversion Hsuspend; subst.
      by apply updThreadC_compatible.
  Qed.

  Lemma gsoThreadC_suspend:
    forall (tp : thread_pool) (i j : tid) (cntj : containsThread tp j)
      (c : code) (Hneq: i <> j) (cnti : containsThread tp i)
      (cntj' : containsThread (updThreadC cnti (Kblocked c)) j),
      getThreadC cntj = getThreadC cntj'.
  Proof.
    intros; erewrite gsoThreadCC; eauto.
  Qed.
  
  Corollary gsoThreadC_suspendC:
    forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
      (cntj': containsThread tp' j) (Hneq: i <> j)
      (Hsuspend: DryConc.suspend_thread cnt tp'),
      getThreadC cntj = getThreadC cntj'.
  Proof.
    intros; inversion Hsuspend; subst;
      by apply gsoThreadC_suspend.
  Qed.

  Corollary gsoThreadC_suspendF:
    forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
      (cntj': containsThread tp' j) (Hneq: i <> j)
      (Hsuspend: FineConc.suspend_thread cnt tp'),
      getThreadC cntj = getThreadC cntj'.
  Proof.
    intros; inversion Hsuspend; subst;
      by apply gsoThreadC_suspend.
  Qed.

  Lemma gsoThreadR_suspendC:
    forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
      (cntj': containsThread tp' j)
      (Hsuspend: DryConc.suspend_thread cnt tp'),
      getThreadR cntj = getThreadR cntj'.
  Proof.
    intros. inversion Hsuspend. subst.
      by erewrite @gThreadCR with (cntj := cntj).
  Qed.

  Lemma gsoThreadR_suspendF:
    forall tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
      (cntj': containsThread tp' j)
      (Hsuspend: FineConc.suspend_thread cnt tp'),
      getThreadR cntj = getThreadR cntj'.
  Proof.
    intros. inversion Hsuspend. subst.
      by erewrite @gThreadCR with (cntj := cntj).
  Qed.

  (** [invariant] is preserved by [suspend_thread]*)
  Lemma suspendC_invariant:
    forall tp tp' i
      (pff: containsThread tp i)
      (Hinv: invariant tp)
      (Hsuspend: DryConc.suspend_thread pff tp'),
      invariant tp'.
  Proof.
    intros.
    inversion Hsuspend; subst.
      by apply updThreadC_invariant.
  Qed.
  
  Lemma suspendF_invariant:
    forall tp tp' i
      (pff: containsThread tp i)
      (Hinv: invariant tp)
      (Hsuspend: FineConc.suspend_thread pff tp'),
      invariant tp'.
  Proof.
    intros.
    inversion Hsuspend; subst.
      by apply updThreadC_invariant.
  Qed.

  (** [lockRes] is not changed by [suspend_thread]*)
  Lemma suspendF_lockRes:
    forall tp tp' i
      (pff: containsThread tp i)
      (Hsuspend: FineConc.suspend_thread pff tp'),
      lockRes tp = lockRes tp'.
  Proof.
    intros.
    inversion Hsuspend; subst.
    extensionality addr.
      by erewrite gsoThreadCLPool.
  Qed.

  Lemma suspendC_lockPool :
    forall (tp tp' : thread_pool) (i : tid) (pfc : containsThread tp i)
      (Hsuspend: DryConc.suspend_thread pfc tp') addr,
      lockRes tp addr = lockRes tp' addr.
  Proof.
    intros. inversion Hsuspend; subst.
      by erewrite gsoThreadCLPool.
  Qed.
  
  Lemma suspendF_lockPool :
    forall (tp tp' : thread_pool) (i : tid) (pff : containsThread tp i)
      (Hsuspend: FineConc.suspend_thread pff tp') addr,
      lockRes tp addr = lockRes tp' addr.
  Proof.
    intros. inversion Hsuspend; subst.
      by erewrite gsoThreadCLPool.
  Qed.

  (** [mem_compatible] is preserved by [setMaxPerm] *)
  Lemma mem_compatible_setMaxPerm :
    forall tp m
      (Hcomp: mem_compatible tp m),
      mem_compatible tp (setMaxPerm m).
  Proof.
    intros tp m Hcomp.
    constructor;
      [intros i cnti; split; intros b ofs | intros l pmap Hres; split; intros b ofs |
       intros l rmap Hres];
      try (rewrite getMaxPerm_correct;
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid];
      try (
          erewrite setMaxPerm_MaxV by assumption; simpl;
          match goal with
          | [ |- match ?Expr with _ => _ end] =>
            destruct Expr
          end; constructor);
      try (
          erewrite setMaxPerm_MaxI by assumption;
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid;
          destruct Hcomp as [Hcompat_thr Hcompat_lp]);
      try (destruct (Hcompat_thr _ cnti) as [Hcompat_thr1 Hcompat_thr2]);
      try (destruct (Hcompat_lp _ _ Hres) as [Hcompat_lp1 Hcompat_lp2]);
      repeat match goal with
             | [H: permMapLt _ _ |- _] =>
               specialize (H b ofs)
             | [H: context[(getMaxPerm _) !! _ _] |- _] =>
               rewrite getMaxPerm_correct in H
             end;
      unfold permission_at in *;
    repeat match goal with
           | [H: Mem.perm_order'' ?Expr _, H2: ?Expr = _ |- _] =>
             rewrite H2 in H
           end; simpl in *;
      by auto).
    eapply (lockRes_blocks Hcomp); eauto.
  Qed.

  (** Any state that steps, requires its threadpool and memory to be
  [mem_compatible]*)
  Lemma fstep_mem_compatible:
    forall the_ge U tr tp m U' tr' tp' m'
      (Hstep: FineConc.MachStep the_ge (U, tr, tp) m (U', tr', tp') m'),
      mem_compatible tp m.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst;
      now eauto.
  Qed.

  Lemma safeC_invariant:
    forall tpc mc n the_ge
      (Hn: n > 0)
      (Hsafe: forall (U : Sch),
          @csafe the_ge (U,[::],tpc) mc n),
      invariant tpc.
  Proof.
    intros.
    specialize (Hsafe [:: 1]).
    simpl in Hsafe.
    inversion Hsafe; subst; try (by exfalso);
      inversion Hstep; try inversion Htstep; auto;
        try (inversion Hhalted; simpl in *; subst; auto);
        simpl in *; subst; auto.
  Qed.
  
  Lemma safeC_compatible:
    forall tpc mc n the_ge
      (Hn: n > 0)
      (Hsafe: forall (U : Sch),
          csafe the_ge (U,[::],tpc) mc n),
      mem_compatible tpc mc.
  Proof.
    intros.
    specialize (Hsafe [:: 0]).
    simpl in Hsafe.
    destruct Hsafe as [|Hhalted | |];
      [by exfalso |simpl in Hhalted;
                     by exfalso | |];
      inversion Hstep; try inversion Htstep; auto;
        simpl in *; subst; auto; try discriminate.
    inversion HschedN; subst.
    Transparent containsThread.
    unfold containsThread in Htid.
    exfalso.
    clear - Htid.
    destruct num_threads.
    simpl in *.
    apply Htid.
    ssromega.
  Qed.
  Opaque containsThread.

  Lemma step_schedule:
    forall the_ge tpc tpc' mc mc' i U U'
      (Hstep: DryConc.MachStep the_ge (i :: U, [::], tpc) mc (U, [::], tpc') mc'),
      DryConc.MachStep the_ge (i :: U', [::], tpc) mc (U', [::], tpc') mc'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *;
      try match goal with
          | [H: ?X :: ?U = ?U |- _] =>
            exfalso; eapply list_cons_irrefl; eauto
          | [H: Some ?X = Some ?Y |- _] =>
            inversion H; subst; clear H
          end.
    econstructor 4; simpl; eauto.
    econstructor 5; simpl; eauto.
    econstructor 6; simpl; eauto.
    econstructor 7; simpl; eauto.
  Qed.

End StepLemmas.

(** ** Definition of internal steps *)
Module InternalSteps (SEM : Semantics) (SemAxioms: SemanticsAxioms SEM)
       (Machine : MachinesSig with Module SEM := SEM).

  Import SEM event_semantics SemAxioms.
  Import Machine DryMachine DryConc ThreadPool.

  Module CoreLanguage := CoreLanguage SEM SemAxioms.
  Module CoreLanguageDry := CoreLanguageDry SEM SemAxioms DryMachine.
  Module ThreadPoolWF := ThreadPoolWF SEM Machine.
  Module StepLemmas := StepLemmas SEM Machine.
  Import ThreadPoolWF StepLemmas CoreLanguage CoreLanguageDry SCH.

  Section InternalSteps.
    Variable the_ge : G.
    
    Notation threadStep := (threadStep the_ge).
    Notation Sch := SCH.schedule.
    
    (** Internal steps are just thread coresteps or resume steps or start steps,
  they mimic fine-grained internal steps *)
    Definition internal_step {tid} {tp} m (cnt: containsThread tp tid)
               (Hcomp: mem_compatible tp m) tp' m' :=
      (exists ev, threadStep cnt Hcomp tp' m' ev) \/
      (DryConc.resume_thread cnt tp' /\ m = m') \/
      (DryConc.start_thread the_ge cnt tp' /\ m = m').

    (* For now we don't emit events from internal_execution*)
    (*NOTE: we will probably never need to do so*)
    Inductive internal_execution : Sch -> thread_pool -> mem ->
                                   thread_pool -> mem -> Prop :=
    | refl_exec : forall tp m,
        internal_execution empty tp m tp m
    | step_trans : forall tid U U' tp m tp' m' tp'' m''
                     (cnt: containsThread tp tid)
                     (HschedN: schedPeek U = Some tid)
                     (HschedS: schedSkip U = U')
                     (Hcomp: mem_compatible tp m)
                     (Hstep: internal_step cnt Hcomp tp' m')
                     (Htrans: internal_execution U' tp' m' tp'' m''),
        internal_execution U tp m tp'' m''.

    (** ** Lemmas about internal steps and internal executions *)

    (** Reverse composition of [internal_execution] and [internal_step]*)
    Lemma internal_execution_trans :
      forall i U tp tp' tp'' m m' m'' (pf': containsThread tp' i)
        (Hcomp: mem_compatible tp' m')
        (Hstep: internal_step pf' Hcomp tp'' m'')
        (Hexec: internal_execution U tp m tp' m'),
        internal_execution (U ++ (i :: nil))%list tp m tp'' m''.
    Proof.
      intros i U. induction U; intros.
      simpl in *.
      inversion Hexec; subst.
      econstructor; simpl; eauto. constructor.
      simpl in HschedN. discriminate.
      inversion Hexec. subst. simpl in *.
      econstructor; simpl; eauto.
    Qed.

    (** [internal_step] is deterministic *)
    Lemma internal_step_det :
      forall tp tp' tp'' m m' m'' i
        (Hcnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt Hcomp tp' m')
        (Hstep': internal_step Hcnt Hcomp tp'' m''),
        tp' = tp'' /\ m' = m''.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [[Htstep ?] | [Htstep ?]]],
                        Hstep' as [[? Htstep'] | [[Htstep' ?] | [Htstep' ?]]]; subst;
      inversion Htstep; inversion Htstep'; subst; pf_cleanup;
      rewrite Hcode in Hcode0; inversion Hcode0; subst.
      apply ev_step_ax1 in Hcorestep0.
      apply ev_step_ax1 in Hcorestep.
      assert (Heq: c' = c'0 /\ m' = m'')
        by (eapply corestep_det; eauto).
      destruct Heq; subst;
        by auto.
      rewrite Hafter_external in Hafter_external0;
        by inversion Hafter_external0.
      rewrite Hinitial in Hinitial0;
        by inversion Hinitial0.
    Qed.

    Ltac exec_induction base_case :=
      intros;
      match goal with
      | [xs : list _, i : nat, Hexec: internal_execution _ ?Tp ?M _ _ |- _] =>
        generalize dependent Tp; generalize dependent M;
        induction xs as [| x xs' IHxs]; intros;
        [ match goal with
          | [Hexec: internal_execution _ _ _ _ _ |- _] =>
            try (inversion Hexec; subst;
                   by pf_cleanup)
          end
        | match goal with
          | [Hexec: internal_execution _ _ _ _ _ |- _] =>
            simpl in Hexec;
              destruct (x == i) eqn:Heq;
              move/eqP:Heq=>Heq;
              try eauto;
              subst;
              try (inversion Hexec as [|? ? ? ? ? ? ? ? ? ?
                                          HschedN HschedS Hcomp ? Htrans]; subst;
                   simpl in Htrans;
                   simpl in HschedN; inversion HschedN; subst;
                   pf_cleanup;
                   specialize (IHxs _ _  Htrans);
                   rewrite <- IHxs;
                   erewrite base_case; eauto)
          end
        ]
      end. 

    (** [containsThread] is preserved by [internal_step]*)
    Lemma containsThread_internal_step :
      forall tp m tp' m' tid0 tid
        (Hcnt0: containsThread tp tid0)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp tid),
        containsThread tp' tid.
    Proof.
      intros.
      inversion Hstep. destruct H.
      inversion H; subst.
      eapply corestep_containsThread; by eauto.
      destruct H as [[Htstep _] | [Htstep _]];
        inversion Htstep; subst;
        [by eapply cntUpdateC | by eapply cntUpdateC].
    Qed.

    (** [containsThread] is preserved by [internal_execution]*)
    Lemma containsThread_internal_execution :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m'),
        containsThread tp i -> containsThread tp' i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step in Hstep; eauto.
    Qed.

    (** The other direction: if a thread is in the threadpool after an
    [internal_step] then it must have been there before the step *)
    Lemma containsThread_internal_step' :
      forall tp m tp' m' i j
        (Hcnt0: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros. inversion Hstep as [[? Htstep] | [[Htstep _] | [Htstep _]]];
        inversion Htstep; subst;
        [eapply corestep_containsThread'; eauto
        |  by eapply cntUpdateC'; eauto
        |  by eapply cntUpdateC'; eauto].
    Qed.

    Lemma containsThread_internal_execution' :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m')
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step' in Hstep; eauto.
    Qed.

    (** [mem_compatible] is preserved by [dry_step]*)
    Lemma dry_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) ev (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hdry: dry_step the_ge pf Hcompatible tp' m' ev),
        mem_compatible tp' m'.
    Proof.
      intros.
      inversion Hdry; subst; eapply corestep_compatible; eauto.
    Qed.

    (** [mem_compatible] is preserved by [resume_thread]*)
    Corollary coarseResume_compatible :
      forall (tp tp' : thread_pool) m (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hresume: DryConc.resume_thread pf tp'),
        mem_compatible tp' m.
    Proof.
      intros.
      inversion Hresume; subst;
      eapply updThreadC_compatible;
        by eauto.
    Qed.

    (** [mem_compatible] is preserved by [start_thread]*)
    Corollary coarseStart_compatible :
      forall (tp tp' : thread_pool) m (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstart: DryConc.start_thread the_ge pf tp'),
        mem_compatible tp' m.
    Proof.
      intros.
      inversion Hstart; subst;
      eapply updThreadC_compatible;
        by eauto.
    Qed.

    (** [mem_compatible] is preserved by [internal_step]*)
    Corollary internal_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      destruct Hstep as [[? Hdry] | [[Hresume ?] | [Hstart ?]]];
        subst;
        [eapply dry_step_compatible
        | eapply coarseResume_compatible
        | eapply coarseStart_compatible]; 
          by eauto.
    Qed.

    (** [invariant] is preserved by [internal_step]*)
    Lemma internal_step_invariant:
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        invariant tp'.
    Proof.
      intros.
      destruct Hstep as [[? Hdry] | Hsr].
      - inversion Hdry as [tp'0 c m1 m1' c']. subst m' tp'0 tp' ev.
        apply ev_step_ax1 in Hcorestep.
        eapply corestep_invariant; eauto.
      - destruct Hsr as [H1 | H1];
        destruct H1 as [H2 ?]; subst;
        inversion H2; subst;
          by apply updThreadC_invariant.
    Qed.

    Lemma internal_execution_compatible :
      forall (tp tp' : thread_pool) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_execution xs tp m tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
    Qed.

    Lemma internal_execution_invariant :
      forall (tp tp' : thread_pool) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hinv: invariant tp)
        (Hstep: internal_execution xs tp m tp' m'),
        invariant tp'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
      eapply internal_step_invariant; eauto.
    Qed.
    
    Lemma gsoThreadC_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. destruct Hstep as [[? Hstep] | [[Hstep Heq] | [Hstep Heq]]];
        inversion Hstep; subst;
        [erewrite <- gsoThreadCode with (cntj' := pfj')
          by eauto
        |
        erewrite gsoThreadCC with (cntj' := pfj')
          by eauto
        |
        erewrite gsoThreadCC with (cntj' := pfj')
          by eauto];
        reflexivity.
    Qed.

    Lemma gsoThreadC_exec:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadC_step; eauto.
          simpl in HschedN. inversion HschedN; subst.
          assumption.
        + eauto.
    Qed.

    (** Other thread permissions do not change by [internal_step]*)
    Lemma gsoThreadR_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. destruct Hstep as [[? Hstep] | [[Hstep Heq] | [Hstep Heq]]];
        inversion Hstep; subst;
        [erewrite <- @gsoThreadRes with (cntj' := pfj') |
         erewrite <- @gThreadCR with (cntj' := pfj')
         | erewrite <- @gThreadCR with (cntj' := pfj')];
          by eauto.
    Qed.

    Corollary permission_at_step:
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs,
        permission_at (restrPermMap (Hcomp _ pfj).1) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj').1) b ofs Cur /\
        permission_at (restrPermMap (Hcomp _ pfj).2) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj').2) b ofs Cur.
    Proof.
      intros;
        rewrite! restrPermMap_Cur;
      erewrite @gsoThreadR_step;
        by eauto.
    Qed.

    Lemma gsoThreadR_execution:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN; inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadR_step; eauto.
        + eauto.
    Qed.

    (** The [lockRes] is preserved by [internal_step]*)
    Lemma gsoLockPool_step:
      forall tp tp' m m' i (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m') addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros;
      destruct Hstep as [[? Htstep] | [[Htstep ?] | [Htstep ?]]];
      inversion Htstep;
      subst;
      [erewrite gsoThreadLPool |
       erewrite gsoThreadCLPool |
       erewrite gsoThreadCLPool];
        by reflexivity.
    Qed.

    (** The [lockRes] is preserved by [internal_execution]*)
    Lemma gsoLockPool_execution :
      forall (tp : thread_pool) (m : mem) (tp' : thread_pool) 
        (m' : mem) (i : nat) (xs : seq nat_eqType)
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m')
        addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hexec. inversion Hexec; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hexec.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; try eauto.
        subst a. inversion Hexec; subst.
        simpl in Htrans.
        simpl in HschedN; inversion HschedN; subst tid.
        pf_cleanup.
        specialize (IHxs _ _  Htrans).
        rewrite <- IHxs.
        erewrite gsoLockPool_step; eauto.
    Qed.

    (** Lock resources of the threads are preserved by [internal_step] *)
    Lemma internal_step_locks_eq:
      forall tp m tp' m' i (cnti: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnti Hcomp tp' m'),
      forall j (cntj: containsThread tp j) (cntj': containsThread tp' j),
        (getThreadR cntj).2 = (getThreadR cntj').2.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [[Htstep ?] | [Htstep ?]]];
        inversion Htstep;
        subst; try (rewrite gThreadCR; reflexivity).
      destruct (i == j) eqn:Hij;
        move/eqP:Hij=>Hij;
                       subst;
                       [rewrite gssThreadRes
                       | erewrite @gsoThreadRes with (cntj := cntj) by eauto];
                       pf_cleanup; reflexivity.
    Qed.

    (** Lock resources of the threads are preserved by [internal_execution] *)
    Lemma internal_execution_locks_eq:
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m'),
      forall j (cntj: containsThread tp j) (cntj': containsThread tp' j),
        (getThreadR cntj).2 = (getThreadR cntj').2.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hexec. inversion Hexec; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hexec.
        inversion Hexec; subst; simpl in *.
        inversion HschedN; subst.
        pose proof Hstep as Hstep2.
        eapply internal_step_locks_eq with
        (cntj := cntj)
          (cntj' := containsThread_internal_step Hstep cntj)
          in Hstep2; eauto.
        specialize (IHxs _ _  Htrans).
        rewrite Hstep2.
        now eapply IHxs.
    Qed.
        
    Lemma permission_at_execution:
      forall tp m tp' m' i j xs
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      forall b ofs,
        permission_at (restrPermMap (Hcomp _ pfj).1) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj').1) b ofs Cur /\
        permission_at (restrPermMap (Hcomp _ pfj).2) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj').2) b ofs Cur.
    Proof.
      intros.
      rewrite! restrPermMap_Cur.
      erewrite gsoThreadR_execution; eauto.
    Qed.

    (** Lifting [corestep_disjoint_val] to [internal_step]*)
    Lemma internal_step_disjoint_val :
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj).1) b ofs Cur Readable \/
           Mem.perm (restrPermMap (Hcomp _ pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Htstep] | [[Htstep Heq] | [Htstep Heq]]]; subst; auto.
      inversion Htstep; subst; eapply ev_step_ax1 in Hcorestep;
      eapply corestep_disjoint_val;
        by eauto.
    Qed.
    
    Lemma internal_exec_disjoint_val :
      forall tp tp' m m' i j xs
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj).1) b ofs Cur Readable \/
           Mem.perm (restrPermMap (Hcomp _ pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj0': containsThread tp'0 j) by
              (eapply containsThread_internal_step; eauto).
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap (Hcomp0' j pfj0').1) b ofs Cur Readable \/
                    Mem.perm (restrPermMap (Hcomp0' j pfj0').2) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            destruct (permission_at_step Hneq  pfj pfj0' Hcomp0' Hstep0 b ofs)
              as [Hperm_eq1 Hperm_eq2].
            rewrite! restrPermMap_Cur in Hperm_eq1 Hperm_eq2.
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur (Hcomp0' j pfj0').1 b ofs).
            assert (H2:= restrPermMap_Cur (Hcomp0' j pfj0').2 b ofs).
            unfold permission_at in H1, H2.
            rewrite H1 H2. rewrite <- Hperm_eq1, <- Hperm_eq2.
            assert (H1':= restrPermMap_Cur (proj1 (Hcomp j pfj)) b ofs).
            assert (H2':= restrPermMap_Cur (proj2 (Hcomp j pfj)) b ofs).
            unfold permission_at in H1', H2'.
            rewrite H1' H2' in Hreadable. assumption.
          }
          specialize (IHxs _ _  pfi0' pfj0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val; eauto.
        + by eauto.
    Qed.

    (** Locks resources are always disjoint from data resources (even for the
    same thread)*)
    Lemma internal_step_disjoint_locks :
      forall tp tp' m m' i j
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Htstep] | [[Htstep Heq] | [Htstep Heq]]]; subst; auto.
      inversion Htstep; subst; eapply ev_step_ax1 in Hcorestep;
        eapply corestep_disjoint_locks;
          by eauto.
    Qed.

    
    Lemma internal_exec_disjoint_locks:
      forall tp tp' m m' i j xs
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable: Mem.perm (restrPermMap (Hcomp _ pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj0': containsThread tp'0 j) by
              (eapply containsThread_internal_step; eauto).
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap (Hcomp0' j pfj0').2) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            pose proof (internal_step_locks_eq Hstep0 pfj pfj0') as Heq_perm.
            unfold Mem.perm in *.
            assert (H2:= restrPermMap_Cur (Hcomp0' j pfj0').2 b ofs).
            assert (H2':= restrPermMap_Cur (proj2 (Hcomp j pfj)) b ofs).
            unfold permission_at in H2, H2'.
            rewrite H2.
            rewrite H2' in Hreadable.
            rewrite <- Heq_perm.
            assumption.
          }
          specialize (IHxs _ _  pfi0' pfj0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_locks; eauto.
        + by eauto.
    Qed.

    Lemma internal_step_stable :
      forall tp tp' m m' i
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        b ofs
        (Hvalid: Mem.valid_block m b)
        (Hstable: ~ Mem.perm (restrPermMap (Hcomp _ pfi).1) b ofs Cur Writable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Htstep] | [[Htstep Heq] | [Htstep Heq]]]; subst; auto.
      inversion Htstep; subst; eapply ev_unchanged_on in Hcorestep;
        by eauto.
    Qed.

    (** Data resources of a thread that took an internal step are related by [decay]*)
    Lemma internal_step_decay:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step cnt Hcomp tp' m'),
        decay (restrPermMap (Hcomp _ cnt).1)
              (restrPermMap (Hcomp' _ cnt').1).
    Proof.
      intros. unfold decay. intros b ofs.
      assert (HpermCur: permission_at
                       (restrPermMap (proj1 (Hcomp' _ cnt'))) b ofs Cur =
                     (getThreadR cnt').1 # b ofs)
        by (eapply restrPermMap_Cur; eauto).
      assert (HpermMax: permission_at
                          (restrPermMap (proj1 (Hcomp' _ cnt'))) b ofs Max =
                        (Mem.mem_access m') # b ofs Max)
        by (erewrite restrPermMap_Max;
             erewrite getMaxPerm_correct;
               by unfold permission_at).
      unfold permission_at in *.
      destruct Hstep as [[? Hcstep] | [[Hresume ?] | [Hstart ?]]]; subst.
      - inversion Hcstep. subst.
        apply ev_step_ax1 in Hcorestep.
        eapply corestep_decay in Hcorestep.
        destruct (Hcorestep b ofs).
        split.
        + intros.
          erewrite restrPermMap_valid in H2.
          assert (Hpmap: (getThreadR cnt').1 = getCurPerm m')
            by (by rewrite gssThreadRes).
          specialize (H H1 H2).
          destruct H as [H | H];
            [left | right]; intros k;
            specialize (H k);
            destruct k;
            try (rewrite HpermMax);
            try (rewrite HpermCur); auto;
          try (rewrite Hpmap;
               rewrite getCurPerm_correct;
               unfold permission_at;
                 by assumption).
        + intros Hvalid.
          specialize (H0 Hvalid).
          destruct H0 as [H0 | H0];
            [left | right];
            intros k;
            specialize (H0 k);
            [destruct H0 | idtac];
            destruct k;
            try rewrite HpermMax;
            try rewrite HpermCur;
            try split;
            auto;
          try rewrite gssThreadRes;
          try rewrite getCurPerm_correct;
          unfold permission_at;
            by assumption.
      - inversion Hresume; subst.
        assert (Hpmap: getThreadR cnt' = getThreadR cnt)
          by (apply gThreadCR).
        assert (H: forall k,
                   (Mem.mem_access (restrPermMap (proj1 (Hcomp' i cnt')))) # b ofs k =
                   (Mem.mem_access (restrPermMap (proj1 (Hcomp i cnt)))) # b ofs k).
        { intros k.
          destruct k.
          rewrite HpermMax.
          assert (H := restrPermMap_Max (proj1 (Hcomp i cnt)) b ofs).
          rewrite getMaxPerm_correct in H.
          unfold permission_at in H;
            by rewrite H.
          rewrite HpermCur.
          rewrite Hpmap.
          assert (H := restrPermMap_Cur (proj1 (Hcomp i cnt)) b ofs).
          unfold permission_at in H;
            by rewrite H. }
        split.
        intros.
        right.
        intros k.
        apply Mem.nextblock_noaccess with (ofs := ofs) (k := k) in H0.
        specialize (H k).
        rewrite H;
          by assumption.
        intros; auto.
      - inversion Hstart; subst.
        assert (Hpmap: getThreadR cnt' = getThreadR cnt)
          by (apply gThreadCR).
        assert (H: forall k,
                   (Mem.mem_access (restrPermMap (proj1 (Hcomp' i cnt')))) # b ofs k =
                   (Mem.mem_access (restrPermMap (proj1 (Hcomp i cnt)))) # b ofs k).
        { intros k.
          destruct k.
          rewrite HpermMax.
          assert (H := restrPermMap_Max (proj1 (Hcomp i cnt)) b ofs).
          rewrite getMaxPerm_correct in H.
          unfold permission_at in H;
            by rewrite H.
          rewrite HpermCur.
          rewrite Hpmap.
          assert (H := restrPermMap_Cur (proj1 (Hcomp i cnt)) b ofs).
          unfold permission_at in H;
            by rewrite H. }
        split.
        intros.
        right.
        intros k.
        apply Mem.nextblock_noaccess with (ofs := ofs) (k := k) in H0.
        specialize (H k).
        rewrite H;
          by assumption.
        intros; auto.
    Qed.

    (** [Mem.valid_block] is preserved by [internal_step]*)
    Lemma internal_step_valid:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnt Hcomp tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [[_ ?] | [_ ?]]];
        [inversion Htstep; subst;
         eapply ev_step_validblock;
           by eauto | by subst | by subst].
    Qed.

    Lemma internal_execution_valid :
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      generalize dependent tp. generalize dependent m.
      induction xs as [|x xs]; intros.
      inversion Hexec; subst; first by assumption.
      simpl in HschedN;
        by discriminate.
      inversion Hexec; subst.
      simpl in HschedN. inversion HschedN; subst.
      simpl in Htrans.
      assert (Hvalid0: Mem.valid_block m'0 b)
        by (eapply internal_step_valid; eauto).
        by eauto.
    Qed.

    Lemma internal_exec_stable:
      forall tp tp' m m' i xs
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m')
        b ofs
        (Hvalid: Mem.valid_block m b)
        (Hstable:  ~ Mem.perm (restrPermMap (Hcomp _ pfi).1) b ofs Cur Writable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hstable0':
                    ~ Mem.perm (restrPermMap (Hcomp0' _ pfi0').1) b ofs Cur Writable).
          { clear IHxs Htrans HschedN Hstep.
            pose proof (internal_step_decay pfi0' Hcomp0' Hstep0) as Hdecay.
            unfold decay in Hdecay.
            destruct (Hdecay b ofs) as [_ Hdecay'].
            destruct (Hdecay' Hvalid) as [Hcontra | Heq].
            - destruct (Hcontra Cur) as [Hcontra' _].
              unfold Mem.perm in Hstable.
              rewrite Hcontra' in Hstable.
              simpl in Hstable. exfalso.
              now eauto using perm_order.
            - specialize (Heq Cur).
              unfold Mem.perm in *.
              rewrite Heq in Hstable.
              assumption.
          }
          pose proof Hvalid as Hvalid0'.
          eapply internal_step_valid in Hvalid0'; eauto.
          specialize (IHxs _ Hvalid0' _ pfi0' Hcomp0' Htrans Hstable0').
          rewrite <- IHxs.
          eapply internal_step_stable; eauto.
        + by eauto.
    Qed.
 
    Lemma internal_execution_decay:
      forall tp m tp' m' xs i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        decay (restrPermMap (Hcomp _ cnt).1)
              (restrPermMap ((Hcomp' _ cnt').1)).
    Proof.
      intros tp m tp' m' xs.
      generalize dependent tp. generalize dependent m.
      induction xs.
      - intros. simpl in Hexec. inversion Hexec; subst.
        pf_cleanup.
          by apply decay_refl.
        simpl in HschedN. discriminate.
      - intros.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + simpl in Hexec.
          erewrite if_true in Hexec by (apply eq_refl).
          inversion Hexec; subst; simpl in *.
          inversion HschedN; subst tid.
          assert (Hcomp'0: mem_compatible tp'0 m'0)
            by (eapply internal_step_compatible; eauto).
          assert (cnt0': containsThread tp'0 i)
            by (eapply containsThread_internal_step; eauto).
          pf_cleanup.
          eapply IHxs with
          (Hcomp := Hcomp'0) (Hcomp' := Hcomp')
                             (cnt := cnt0') (cnt' := cnt') in Htrans.
          assert (Hdecay:
                    decay (restrPermMap (proj1 (Hcomp _ cnt)))
                          (restrPermMap (proj1 (Hcomp'0 _ cnt0'))))
            by (eapply internal_step_decay; eauto).
          eapply decay_trans with (m' := restrPermMap (proj1 (Hcomp'0 i cnt0')));
            eauto.
          intros.
          erewrite restrPermMap_valid.
          eapply internal_step_valid;
            by eauto.
        + simpl in Hexec.
          erewrite if_false in Hexec
            by (apply/eqP; assumption).
          auto.
    Qed.

    Lemma internal_step_disjoint_val_lockPool :
      forall tp tp' m m' i bl ofsl pmap
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hl: lockRes tp (bl,ofsl) = Some pmap)
        (Hreadable: Mem.perm (restrPermMap (compat_lp Hcomp _ Hl).1)
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap (compat_lp Hcomp _ Hl).2)
                             b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Hcstep] | [[Hrstep Heq] | [Hsstep Heq]]]; subst; auto.
      inversion Hcstep; subst; eapply ev_step_ax1 in Hcorestep;
      eapply corestep_disjoint_val_lockpool;
        by eauto.
    Qed.
    
    Lemma internal_exec_disjoint_val_lockPool:
      forall (tp tp' : thread_pool) (m m' : mem) (i : tid) xs bl ofsl pmap
        (Hcomp : mem_compatible tp m)
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m')
        (Hl: lockRes tp (bl,ofsl) = Some pmap)
        b ofs
        (Hreadable: Mem.perm (restrPermMap (compat_lp Hcomp _ Hl).1)
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap (compat_lp Hcomp _ Hl).2)
                             b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hexec; inversion Hexec; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hexec.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hexec; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hl0': lockRes tp'0 (bl, ofsl) = Some pmap)
            by (erewrite <- gsoLockPool_step; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap (proj1 (compat_lp Hcomp0' _ Hl0')))
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap (proj2 (compat_lp Hcomp0' _ Hl0')))
                             b ofs Cur Readable).
          { clear IHxs Htrans HschedN.
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur (proj1 (compat_lp Hcomp0' _ Hl0')) b ofs).
            assert (H2:= restrPermMap_Cur (proj2 (compat_lp Hcomp0' _ Hl0')) b ofs).
            unfold permission_at in H1, H2.
            rewrite H1 H2.
            assert (H1':= restrPermMap_Cur (proj1 (compat_lp Hcomp _ Hl)) b ofs).
            assert (H2':= restrPermMap_Cur (proj2 (compat_lp Hcomp _ Hl)) b ofs).
            unfold permission_at in H1', H2'.
              by rewrite H1' H2' in Hreadable.
          }
          specialize (IHxs _ _  Hcomp0' Htrans Hl0' Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val_lockPool; eauto.
        + by eauto.
    Qed.



    Lemma updThread_internal_step:
      forall tp tp' m m' i j c pmap
        (Hneq: i <> j)
        (cnti: containsThread tp i)
        (cnti': containsThread tp' i)
        (cntj: containsThread tp j)
        (cntj': containsThread (updThread cnti c pmap) j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible (updThread cnti c pmap) m)
        (Hinv': invariant (updThread cnti c pmap))
        (Hstep: internal_step cntj Hcomp tp' m'),
        internal_step cntj' Hcomp' (updThread cnti' c pmap) m'.
    Proof.
      intros.
      inversion Hstep as [[? ?] | [[? ?] | [? ?]]].
      - inversion H; subst.
        left.
        exists x.
        eapply step_dry with (c := c0) (c' := c'); eauto.
        erewrite gsoThreadCode; eauto.
        erewrite <- restrPermMap_irr' with
        (Hlt' := (Hcomp' j cntj').1) (Hlt := (Hcomp j cntj).1);
          eauto.
        erewrite @gsoThreadRes with (cntj := cntj); eauto.
        erewrite @gsoThreadRes with (cntj := cntj) by eauto.
        rewrite updThread_comm; auto.
      - subst.
        inversion H; subst.
        right. left.
        split; auto.
        econstructor; eauto.
        erewrite @gsoThreadCode with (cntj := cntj); eauto.
        pf_cleanup. auto.
        rewrite updThread_updThreadC_comm; auto.
      - subst.
        inversion H; subst.
        do 2 right.
        split; auto.
        econstructor; eauto.
        erewrite @gsoThreadCode with (cntj := cntj); eauto.
        pf_cleanup. auto.
        rewrite updThread_updThreadC_comm; auto.
    Qed.
        
    
    Lemma updThread_internal_execution:
      forall tp tp' m m' i j xs c pmap
        (cnti: containsThread tp i)
        (cnti': containsThread tp' i)
        (Hinv: invariant (updThread cnti c pmap))
        (Hcomp' : mem_compatible (updThread cnti c pmap) m)
        (Hneq: i <> j)
        (Hexec: internal_execution [seq x <- xs | x == j] tp m tp' m'),
        internal_execution [seq x <- xs | x == j] (updThread cnti c pmap) m
                           (updThread cnti' c pmap) m'.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros.
      - simpl in *.
        inversion Hexec; subst;
        first by constructor.
        simpl in HschedN;
          by discriminate.
      - simpl in *.
        destruct (a == j) eqn:Heq; move/eqP:Heq=>Heq.
        subst a.
        inversion Hexec; subst.
        simpl in HschedN. inversion HschedN; subst tid.
        assert (cntj' := cntUpdate c pmap cnti cnt).
        assert (cnti0' := containsThread_internal_step Hstep cnti).
        eapply updThread_internal_step
        with (cntj' := cntj') (cnti' := cnti0') (Hcomp' := Hcomp') in Hstep; eauto.
        specialize (IHxs tp'0 _
                         ltac:(eapply internal_step_invariant; eauto)
                                m'0
                                ltac:(eapply (internal_step_compatible);
                                       eauto) Htrans).
        econstructor;
          by eauto.
        eauto.
    Qed.

    Lemma addThread_internal_step:
      forall tp tp' m m' i vf arg pmap
        (cnti: containsThread tp i)
        (cnti': containsThread (addThread tp vf arg pmap) i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible (addThread tp vf arg pmap) m)
        (Hinv': invariant (addThread tp vf arg pmap))
        (Hstep: internal_step cnti Hcomp tp' m'),
        internal_step cnti' Hcomp' (addThread tp' vf arg pmap) m'.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [Hresume | Hinit]].
      - inversion Htstep; subst tp'0 m'0.
        left.
        exists x.
        eapply step_dry with (c := c) (c' := c'); eauto.
        erewrite gsoAddCode with (cntj := cnti); eauto.
        subst.
        erewrite restrPermMap_irr' with (Hlt' := proj1 (Hcomp i cnti)); eauto.
        erewrite gsoAddRes with (cntj := cnti); eauto.
        subst.
        erewrite @gsoAddRes with (cntj := cnti) by eauto.
          by rewrite add_update_comm.
      - destruct Hresume as [Hresume ?]; subst.
        inversion Hresume; subst.
        right; left.
        split; auto.
        econstructor; eauto.
        erewrite gsoAddCode with (cntj := ctn); eauto.            
          by rewrite add_updateC_comm.
      - destruct Hinit; subst.
        right; right.
        split; auto.
        inversion H; subst.
        econstructor; eauto.
        erewrite gsoAddCode; eauto.
          by rewrite add_updateC_comm.
    Qed.

    
    Lemma addThread_internal_execution:
      forall tp tp' m m' i j xs vf arg pmap
        (Hneq: i <> j)
        (Hinv': invariant (addThread tp vf arg pmap))
        (Hcomp': mem_compatible (addThread tp vf arg pmap) m)
        (Hexec: internal_execution [seq x <- xs | x == j] tp m tp' m'),
        internal_execution [seq x <- xs | x == j]
                           (addThread tp vf arg pmap) m
                           (addThread tp' vf arg pmap) m'.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros.
      - simpl in *.
        inversion Hexec; subst;
        first by constructor.
        simpl in HschedN;
          by discriminate.
      - simpl in *.
        destruct (a == j) eqn:Heq; move/eqP:Heq=>Heq.
        subst a.
        inversion Hexec; subst.
        simpl in HschedN. inversion HschedN; subst tid.
        assert (cnt':= cntAdd vf arg pmap cnt).
        eapply addThread_internal_step
        with (cnti' := cnt') (Hcomp' := Hcomp') in Hstep; eauto.
        specialize (IHxs tp'0
                         ltac:(eapply internal_step_invariant; eauto)
                                m'0
                                ltac:(eapply (internal_step_compatible);
                                       eauto) Htrans).
        econstructor;
          by eauto.
        eauto.
    Qed.

    Lemma remLock_internal_step:
      forall tp tp' m m' j (cntj: containsThread tp j) b ofs
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible (remLockSet tp (b,ofs)) m)
        (cntj': containsThread (remLockSet tp (b,ofs)) j)
        (Hstep: internal_step cntj Hcomp tp' m'),
        internal_step cntj' Hcomp' (remLockSet tp' (b,ofs)) m'.
    Proof.
      intros.
      inversion Hstep as [[? ?] | [[? ?] | [? ?]]].
      - inversion H; subst.
        left.
        exists x.
        eapply step_dry with (c := c) (c' := c'); eauto.
        eapply remLock_inv; eauto.
        rewrite gRemLockSetCode.
        auto.
        erewrite <- restrPermMap_irr' with
        (Hlt' := (Hcomp' j cntj').1) (Hlt := (Hcomp j cntj).1);
          eauto.
        rewrite gRemLockSetRes; auto.
        rewrite gRemLockSetRes; auto.
      - subst.
        inversion H; subst.
        right. left.
        split; auto.
        econstructor; eauto.
        rewrite gRemLockSetCode; auto.
        eapply remLock_inv; eauto.
      - subst.
        inversion H; subst.
        do 2 right.
        split; auto.
        econstructor; eauto.
        rewrite gRemLockSetCode; auto.
        eapply remLock_inv; eauto.
    Qed.
    
    Lemma remLock_internal_execution:
      forall tp tp' m m' j xs b ofs
        (Hcomp': mem_compatible (remLockSet tp (b,ofs)) m)
        (Hexec: internal_execution [seq x <- xs | x == j] tp m tp' m'),
        internal_execution [seq x <- xs | x == j] (remLockSet tp (b, ofs)) m
                           (remLockSet tp' (b,ofs)) m'.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros.
      - simpl in *.
        inversion Hexec; subst;
        first by constructor.
        simpl in HschedN;
          by discriminate.
      - simpl in *.
        destruct (a == j) eqn:Heq; move/eqP:Heq=>Heq.
        subst a.
        inversion Hexec; subst.
        simpl in HschedN. inversion HschedN; subst tid.
        assert (cntj' := cntRemoveL (b, ofs) cnt).
        eapply remLock_internal_step
        with (cntj' := cntj') (Hcomp' := Hcomp') in Hstep; eauto.
        specialize (IHxs tp'0 _
                         ltac:(eapply (internal_step_compatible);
                                eauto) Htrans).
        econstructor;
          by eauto.
        eauto.
    Qed.

    Lemma internal_step_nextblock:
      forall tp m tp' m' i (cnti: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnti Hcomp tp' m'),
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      destruct Hstep as [[? H] | [[? ?] | [? ?]]]; subst.
      inversion H; subst.
      eapply ev_step_nextblock in Hcorestep;
        by rewrite restrPermMap_nextblock in Hcorestep.
      apply Pos.le_refl.
      apply Pos.le_refl.
    Qed.
     
    Lemma internal_execution_nextblock:
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m'),
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros; inversion Hexec; subst;
      first by apply Pos.le_refl.
      simpl in HschedN. discriminate.
      simpl in *.
      inversion HschedN; subst.
      specialize (IHxs _ _ Htrans).
      eapply Pos.le_trans.
      eapply internal_step_nextblock; eauto.
      eauto.
    Qed.
    
  End InternalSteps.
End InternalSteps.

(** ** Type of steps the concurrent machine supports *)
Module StepType (SEM : Semantics)
       (SemAxioms: SemanticsAxioms SEM)
       (Machine : MachinesSig with Module SEM := SEM)
       (AsmContext : AsmContext SEM Machine ).

  Import AsmContext Machine DryMachine ThreadPool.
  Import SEM event_semantics SemAxioms. 

  Module StepLemmas := StepLemmas SEM Machine.
  Module ThreadPoolWF := ThreadPoolWF SEM Machine.
  Module CoreLanguageDry := CoreLanguageDry SEM SemAxioms DryMachine.
  Module InternalSteps := InternalSteps SEM SemAxioms Machine.
  Import ThreadPoolWF CoreLanguageDry InternalSteps StepLemmas event_semantics.
   (** Distinguishing the various step types of the concurrent machine *)

  Inductive StepType : Type :=
    Internal | Concurrent | Halted | Suspend.

  Definition ctlType (code : ctl) : StepType :=
    match code with
    | Kinit _ _ => Internal
    | Krun c =>
      match at_external Sem c with
      | None => 
        match halted Sem c with
        | Some _ => Halted
        | None => Internal
        end
      | Some _ => Suspend
      end
    | Kblocked c => Concurrent
    | Kresume c _ => Internal
    end.
  
  Definition getStepType {i tp} (cnt : containsThread tp i) : StepType :=
    ctlType (getThreadC cnt).

  Global Notation "cnt '@'  'I'" := (getStepType cnt = Internal) (at level 80).
  Global Notation "cnt '@'  'E'" := (getStepType cnt = Concurrent) (at level 80).
  Global Notation "cnt '@'  'S'" := (getStepType cnt = Suspend) (at level 80).
  Global Notation "cnt '@'  'H'" := (getStepType cnt = Halted) (at level 80).

  (** Solves absurd cases from fine-grained internal steps *)
  Global Ltac absurd_internal Hstep :=
    inversion Hstep; try inversion Htstep; subst; simpl in *;
    try match goal with
        | [H: Some _ = Some _ |- _] => inversion H; subst
        end; pf_cleanup;
    repeat match goal with
           | [H: getThreadC ?Pf = _, Hint: ?Pf @ I |- _] =>
             unfold getStepType in Hint;
               rewrite H in Hint; simpl in Hint
           | [H1: match ?Expr with _ => _ end = _,
                  H2: ?Expr = _ |- _] => rewrite H2 in H1
           | [H: threadHalted _ |- _] =>
             inversion H; clear H; subst; simpl in *; pf_cleanup;
             unfold  ThreadPool.SEM.Sem in *
           | [H1: is_true (isSome (halted ?Sem ?C)),
                  H2: match at_external _ _ with _ => _ end = _ |- _] =>
             destruct (at_external_halted_excl Sem C) as [Hext | Hcontra];
               [rewrite Hext in H2;
                 destruct (halted Sem C) eqn:Hh;
                 [discriminate | by exfalso] |
                rewrite Hcontra in H1; by exfalso]
           end; try discriminate; try (exfalso; by auto).
  
  
  Section StepType.
    Variable ge : G.
  Lemma internal_step_type :
    forall  i tp tp' m m' (cnt : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep_internal: internal_step ge cnt Hcomp tp' m'),
      cnt @ I.
  Proof.
    intros.
    unfold getStepType, ctlType.
    destruct Hstep_internal as [[? Hcstep] | [[Hresume Heq] | [Hstart Heq]]].
    inversion Hcstep. subst. rewrite Hcode.
    apply ev_step_ax1 in Hcorestep.
    assert (H1:= corestep_not_at_external Sem _ _ _ _ _ Hcorestep).
    rewrite H1.
    assert (H2:= corestep_not_halted Sem _ _ _ _ _ Hcorestep);
      by rewrite H2.
    inversion Hresume; subst.
    pf_cleanup;
      by rewrite Hcode.
    inversion Hstart; subst.
    pf_cleanup;
      by rewrite Hcode.
  Qed.

  Lemma internal_step_result_type:
    forall tp m tp' m' i (cnti: containsThread tp i)
      (cnti': containsThread tp' i)
      (Hcomp: mem_compatible tp m)
      (Hinternal: internal_step ge cnti Hcomp tp' m'),
      ~ (cnti' @ E).
  Proof.
    intros. intro Hcontra.
    destruct Hinternal as [[? Htstep] | [[Htstep ?] | [Htstep ?]]]; subst;
    inversion Htstep; subst;
    unfold getStepType in Hcontra;
    try rewrite gssThreadCode in Hcontra;
    try rewrite gssThreadCC in Hcontra; unfold ctlType in Hcontra;
    repeat match goal with
           | [H: match ?Expr with _ => _ end = _ |- _] =>
             destruct Expr
           end; discriminate.
  Qed.

  Lemma internal_execution_result_type:
    forall tp m tp' m' i xs
      (cnti': containsThread tp' i)
      (Hin: List.In i xs)
      (Hexec: internal_execution ge [seq x <- xs | x == i] tp m tp' m'),
      ~ (cnti' @ E).
  Proof.
    intros.
    generalize dependent m.
    generalize dependent tp.
    induction xs; intros.
    - simpl in *.
      inversion Hexec; subst.
      by exfalso.
      simpl in HschedN;
        by discriminate.
    - destruct (a == i) eqn:Hia; move/eqP:Hia=>Hia.
      subst a.
      simpl in *.
      erewrite if_true in Hexec by apply eq_refl.
      inversion Hexec; subst.
      simpl in HschedN. inversion HschedN; subst tid.
      simpl in Htrans.
      destruct (List.In_dec (eq_dec.nat_eq_dec) i xs).
      eauto.
      rewrite not_in_filter in Htrans; auto.
      inversion Htrans; subst.
      eapply internal_step_result_type; eauto.
      simpl in HschedN0; discriminate.
      destruct Hin; first by (exfalso; auto).
      simpl in Hexec.
      erewrite if_false in Hexec.
      eauto.
      move/eqP:Hia; auto.
  Qed.
      
  (** Proofs about [fmachine_step]*)
  Notation fmachine_step := ((corestep fine_semantics) ge).
  
  Lemma fstep_containsThread :
    forall tp tp' m m' i j U tr tr'
      (cntj: containsThread tp j)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
      containsThread tp' j.
  Proof.
    intros.
    inversion Hstep; subst; try inversion Htstep;
    simpl in *; try inversion HschedN;
    subst; auto;
    repeat match goal with
           | [ |- containsThread (updThreadC _ _) _] =>
             apply cntUpdateC; auto
           | [ |- containsThread (updThread _ _ _) _] =>
             apply cntUpdate; auto
           | [ |- containsThread (updThreadR _ _) _] =>
             apply cntUpdateR; auto
           | [ |- containsThread (addThread _ _ _ _) _] =>
             apply cntAdd; auto
           end.
  Qed.

  Lemma fstep_containsThread' :
    forall tp tp' m m' i j U tr tr'
      (cnti: containsThread tp i)
      (cntj: containsThread tp' j)
      (Hinternal: cnti @ I)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
      containsThread tp j.
  Proof.
    intros.
    absurd_internal Hstep;
      by eauto.
  Qed.

  Lemma fmachine_step_invariant:
    forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i) U tr tr'
      (Hcompatible: mem_compatible tp m)
      (Hinternal: pf @ I)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
      invariant tp'.
  Proof.
    intros.
    absurd_internal Hstep.
    - apply updThreadC_invariant; auto.
    - apply updThreadC_invariant; auto.
    -  
      eapply ev_step_ax1 in Hcorestep.
      eapply corestep_invariant;
        by (simpl; eauto).
  Qed.

  Lemma fmachine_step_compatible:
    forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i) U tr tr'
      (Hcompatible: mem_compatible tp m)
      (Hinternal: pf @ I)
      (Hstep: fmachine_step (i :: U,tr, tp) m (U, tr',tp') m'),
      mem_compatible tp' m'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (eapply updThreadC_compatible;
             by eauto).
    eapply mem_compatible_setMaxPerm.
    eapply corestep_compatible;
      by (simpl; eauto).
    (* this holds trivially, we don't need to use corestep_compatible*)
  Qed.

  Lemma gsoThreadR_fstep:
    forall tp tp' m m' i j U tr tr'
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U,tr, tp) m (U,tr', tp') m'),
      getThreadR pfj = getThreadR pfj'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (by rewrite <- gThreadCR with (cntj' := pfj'));
      erewrite <- @gsoThreadRes with (cntj' := pfj');
        by eauto.
  Qed.

  Lemma permission_at_fstep:
    forall tp tp' m m' i j U tr tr'
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hinv: pfi @ I)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U,tr',tp') m') b ofs,
      permission_at (restrPermMap (Hcomp _ pfj).1) b ofs Cur =
      permission_at (restrPermMap (Hcomp' _ pfj').1) b ofs Cur.
  Proof.
    intros.
    do 2 rewrite restrPermMap_Cur;
      erewrite gsoThreadR_fstep;
        by eauto.
  Qed.

  Lemma gsoThreadC_fstepI:
    forall tp tp' m m' i j U tr tr'
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (pfi: containsThread tp i)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m')
      (Hneq: i <> j),
      getThreadC pfj = getThreadC pfj'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (erewrite gsoThreadCC with (cntj' := pfj');
             by eauto);
      erewrite gsoThreadCode with (cntj' := pfj');
        by eauto.
  Qed.

  Lemma gsoLockSet_fstepI:
    forall tp tp' m m' i U tr tr'
      (pfi: containsThread tp i)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
      lockSet tp = lockSet tp'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (erewrite gsoThreadCLock;
             by eauto);
      erewrite gsoThreadLock;
        by eauto.
  Qed.

  Lemma gsoLockRes_fstepI :
    forall (tp tp' : thread_pool) (m m' : mem) (i : tid) tr tr'
      (U : seq tid) (pfi : containsThread tp i)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U,tr, tp) m (U, tr', tp') m'),
      lockRes tp' = lockRes tp.
  Proof.
    intros.
    absurd_internal Hstep;
      extensionality addr;
      try (by rewrite gsoThreadCLPool);
      try (by rewrite gsoThreadLPool).
  Qed.
  
  Lemma fmachine_step_disjoint_val :
    forall tp tp' m m' i j U tr tr'
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hinv: pfi @ I)
      (Hstep: fmachine_step (i :: U, tr, tp) m (U,tr', tp') m') b ofs
      (Hreadable: 
         Mem.perm (restrPermMap (Hcomp _ pfj).1) b ofs Cur Readable \/
         Mem.perm (restrPermMap (Hcomp _ pfj).2) b ofs Cur Readable),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    absurd_internal Hstep;
      try reflexivity;
    apply ev_step_ax1 in Hcorestep;
      eapply corestep_disjoint_val;
        by (simpl; eauto).
  Qed.

  Lemma diluteMem_valid :
    forall b m,
      Mem.valid_block m b <-> Mem.valid_block (diluteMem m) b.
  Proof.
    intros.
    split; auto.
  Qed.
  
  Lemma fstep_valid_block:
    forall tpf tpf' mf mf' i U b tr tr'
      (Hvalid: Mem.valid_block mf b)
      (Hstep: fmachine_step (i :: U, tr, tpf) mf (U, tr',tpf') mf'),
      Mem.valid_block mf' b.
  Proof.
    intros.
    inversion Hstep; subst; auto.
    inversion Htstep; subst.
    erewrite <- diluteMem_valid.
    eapply CoreLanguage.ev_step_validblock; eauto.
    admit.
  Admitted.
  
  End StepType.

  Hint Resolve fmachine_step_compatible fmachine_step_invariant
       fstep_containsThread fstep_containsThread' gsoLockSet_fstepI : fstep.

  Hint Rewrite gsoThreadR_fstep permission_at_fstep : fstep.
  
End StepType.