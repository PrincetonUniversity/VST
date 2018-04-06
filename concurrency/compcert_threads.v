Require Import compcert.lib.Axioms.

Require Import VST.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.


Require Import VST.concurrency.pos.
Require Import VST.concurrency.concurrent_machine.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import VST.veric.shares VST.msl.msl_standard.
Require Import VST.concurrency.threads_lemmas.

Require Import Coq.ZArith.ZArith.

Require Import (*compcert_linking*) VST.concurrency.permissions.

Module ThreadPool.
  Section ThreadPool.

    Variable cT : Type.

    Record t := mk
                  { num_threads : pos
                    ; pool :> 'I_num_threads -> (@ctl cT)
                    ; share_maps : 'I_num_threads -> share_map
                  }.

    Definition containsThread: t -> nat -> Prop:=
      fun tp tid => tid < (num_threads tp).

  End ThreadPool.
End ThreadPool.

Section poolDefs.

  Variable cT : Type.

  Import ThreadPool.

  Notation "x <= y" := (x <= y)%nat.
  Notation "x < y" := (x < y)%nat.
  Notation thread_pool := (t cT).

  Variable (tp : thread_pool).
  Notation num_threads := (ThreadPool.num_threads tp).

  (* Per-thread disjointness definition*)
  Definition race_free (tp : thread_pool) :=
    forall tid0 tid0' (Htid0 : containsThread tp tid0)
      (Htid0' : containsThread tp tid0')
      (Htid: tid0 <> tid0'),
      shareMapsJoins (share_maps tp (Ordinal Htid0))
                       (share_maps tp (Ordinal Htid0')).

  Definition newShareMap_wf smap :=
    forall tid0 (Htid0 : containsThread tp tid0),
      shareMapsJoins ((share_maps tp) (Ordinal Htid0)) smap.

  Require Import fintype.

  Lemma unlift_m_inv : forall tid (Htid : tid < num_threads.+1) ord
                         (Hunlift: unlift (ordinal_pos_incr num_threads)
                                          (Ordinal (n:=num_threads.+1) (m:=tid) Htid)
                                   = Some ord),
                         nat_of_ord ord = tid.
  Proof.
    intros.
    assert (Hcontra:
              unlift_spec (ordinal_pos_incr num_threads)
                          (Ordinal (n:=num_threads.+1) (m:=tid) Htid) (Some ord)).
    rewrite <- Hunlift.
    apply/unliftP.
    inversion Hcontra; subst.
    inversion H0.
    unfold bump.
    assert (pf: ord < num_threads)
      by (by rewrite ltn_ord).
    assert (H: num_threads <= ord = false).
    rewrite ltnNge in pf.
    rewrite <- Bool.negb_true_iff. auto.
    rewrite H. simpl. rewrite add0n. reflexivity.
  Defined.

  Definition addThread (c : cT) (smap : share_map) : thread_pool :=
    let: new_num_threads := pos_incr num_threads in
    let: new_tid := ordinal_pos_incr num_threads in
    mk new_num_threads
        (fun (n : 'I_new_num_threads) =>
           match unlift new_tid n with
             | None => Kresume c (*Could be a new state Kinit?? *)
             | Some n' => tp n'
           end)
        (fun (n : 'I_new_num_threads) =>
           match unlift new_tid n with
             | None => smap
             | Some n' => (share_maps tp) n'
           end).

  Lemma addThread_racefree :
    forall c p (Hwf: newShareMap_wf p) (Hrace: race_free tp),
      race_free (addThread c p).
  Proof.
    unfold race_free in *. intros.
    simpl.
    match goal with
      | [ |- context[ match ?Expr with _ => _ end]] =>
        destruct Expr as [ord0|] eqn:Hget0
    end;
      match goal with
        | [ |- context[ match ?Expr with _ => _ end]] =>
          destruct Expr as [ord1|] eqn:Hget1
      end; simpl in *.
    - apply unlift_m_inv in Hget0.
      apply unlift_m_inv in Hget1. subst.
      destruct ord0 as [tid0 pf0], ord1 as [tid1 pf1]; simpl in Htid.
      eapply Hrace; eauto.
    - apply unlift_m_inv in Hget0.
      subst. unfold newShareMap_wf in Hwf.
      destruct ord0. eapply Hwf; eauto.
    - apply unlift_m_inv in Hget1.
      subst. unfold newShareMap_wf in Hwf.
      destruct ord1. apply shareMapsJoins_comm. eapply Hwf; eauto.
    - destruct (tid0 == num_threads) eqn:Heq0.
      + move/eqP:Heq0=>Heq0. subst.
        assert (Hcontra: (ordinal_pos_incr num_threads) !=
                                                        (Ordinal (n:=num_threads.+1) (m:=tid0') Htid0')).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra.
          inversion Hcontra; auto.
        }
        exfalso. apply unlift_some in Hcontra. rewrite Hget1 in Hcontra.
        destruct Hcontra. discriminate.
      + move/eqP:Heq0=>Heq0.
        assert (Hcontra: (ordinal_pos_incr num_threads) !=
                                                        (Ordinal (n:=num_threads.+1) (m:=tid0) Htid0)).
        { apply/eqP. intros Hcontra.
          unfold ordinal_pos_incr in Hcontra. inversion Hcontra. subst. auto. }
        exfalso. apply unlift_some in Hcontra. rewrite Hget0 in Hcontra. destruct Hcontra.
        discriminate.
  Defined.

  Definition updThreadC tid (cont: containsThread tp tid) (c' : ctl) : thread_pool :=
    mk num_threads (fun (n : 'I_num_threads) =>
                      if n == (Ordinal cont) then c' else tp n) (share_maps tp).

  Definition updThreadS tid (cont: containsThread tp tid) (smap' : share_map) :
    thread_pool :=
    mk num_threads (pool tp) (fun (n : 'I_num_threads) =>
                                if n == (Ordinal cont) then smap'
                                else (share_maps tp) n).

  Definition shareMap_wf smap tid :=
    forall tid0 (Htid0 : tid0 < num_threads) (Hneq: tid <> tid0),
      shareMapsJoins ((share_maps tp) (Ordinal Htid0)) smap.

  Definition updThread tid (cont : containsThread tp tid) (c' : ctl)
             (smap : share_map) : thread_pool :=
    mk num_threads
        (fun (n : 'I_num_threads) =>
           if n == (Ordinal cont) then c' else tp n)
        (fun (n : 'I_num_threads) =>
           if n == (Ordinal cont) then smap else (share_maps tp) n).

  Lemma updThread_wf : forall tid (pf : containsThread tp tid) smap
                         (Hwf: shareMap_wf smap tid)
                         c'
                         (Hrace_free: race_free tp),
                         race_free (updThread pf c' smap).
  Proof.
    intros.
    unfold race_free. intros.
    simpl.
    destruct (Ordinal (n:=num_threads) (m:=tid0) Htid0 ==  Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0,
                                                                                                     (Ordinal (n:=num_threads) (m:=tid0') Htid0' == Ordinal (n:=num_threads) (m:=tid) pf) eqn:Heq0'.
    - move/eqP:Heq0 => Heq0. subst.
      move/eqP:Heq0' => Heq0'. inversion Heq0'. inversion Heq0; subst. exfalso; auto.
    - move/eqP:Heq0=>Heq0. inversion Heq0. subst.
      apply shareMapsJoins_comm.
      eapply Hwf. simpl; auto.
    - move/eqP:Heq0'=>Heq0'. inversion Heq0'. subst.
      eapply Hwf. simpl; auto.
    - simpl in *. eapply Hrace_free; eauto.
  Defined.


  Definition getThreadC tid (cont : containsThread tp tid) : ctl :=
    tp (Ordinal cont).

  Definition getThreadS tid (cont : containsThread tp tid) : share_map :=
    (share_maps tp) (Ordinal cont).

  Import Maps.

  Definition perm_compatible p :=
    forall tid (cont : containsThread tp tid) (b : positive) (ofs : Z) ,
      Mem.perm_order'' (Maps.PMap.get b p ofs)
                       (Maps.PMap.get b (share_to_access_map (getThreadS cont)) ofs).

  Record mem_compatible m :=
    { perm_comp: perm_compatible (getMaxPerm m);
      mem_canonical: isCanonical (getMaxPerm m)
    }.

End poolDefs.

Section poolLemmas.

  Context {cT : Type} (tp : ThreadPool.t cT).

  Import ThreadPool.

  Lemma updThreadS_cnt : forall tid tp' (cnt: containsThread tp tid) smap
                           (Hupd: tp' = updThreadS cnt smap),
      containsThread tp' tid.
  Proof.
    intros. unfold containsThread, updThreadS in *. subst. now simpl.
  Defined.


  (*This broke owhen lifting getters and setters for ThreadC. Should be fixed. Nick
    suggested to abstract the machine_state for both machines and have only one set
    of proofs.*)
  (*
  Lemma gssThreadCode (tid : 'I_(num_threads tp)) c' p' counter' :
    getThreadC (updThread tp tid c' p' counter') tid = c'.
  Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

  Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' p' counter':
    tid' != tid -> getThreadC (updThread tp tid c' p' counter') tid' = getThreadC tp tid'.
  Proof. by rewrite /getThreadC /updThread /=; case Heq: (tid' == tid). Defined.

  Lemma gssThreadPerm (tid : 'I_(num_threads tp)) c' p' counter' :
    getThreadPerm (updThread tp tid c' p' counter') tid = p'.
  Proof. by rewrite /getThreadC /updThread /= eq_refl. Defined.

  Lemma gsoThreadPerm (tid tid' : 'I_(num_threads tp)) c' p' counter':
    tid' != tid -> getThreadPerm (updThread tp tid c' p' counter') tid' = getThreadPerm tp tid'.
  Proof. by rewrite /getThreadPerm /updThread /=; case Heq: (tid' == tid). Defined.

  Lemma getAddThread c pmap tid :
    tid = ordinal_pos_incr (num_threads tp) ->
    getThreadC (addThread tp c pmap) tid = c.
  Proof. by rewrite /getThreadC /addThread /= => <-; rewrite unlift_none. Qed. *)

  Lemma permMapsInv_lt : forall p (Hinv: perm_compatible tp p) tid
                           (cont : containsThread tp tid),
      permMapLt (share_to_access_map (getThreadS cont)) p.
  Proof.
    intros.
    unfold permMapLt; auto.
  Qed.

  Definition restrPermMap p' m (Hlt: permMapLt p' (getMaxPerm m)) : mem.
  Proof.
    refine ({|
               Mem.mem_contents := Mem.mem_contents m;
               Mem.mem_access :=
                 (fun ofs k =>
                    match k with
                      | Cur => None
                      | Max => fst (Mem.mem_access m) ofs k
                    end, Maps.PTree.map (fun b f =>
                                           fun ofs k =>
                                             match k with
                                               | Cur =>
                                                 (Maps.PMap.get b p') ofs
                                               | Max =>
                                                 f ofs Max
                                             end) (Mem.mem_access m).2);
               Mem.nextblock := Mem.nextblock m;
               Mem.access_max := _;
               Mem.nextblock_noaccess := _;
               Mem.contents_default := Mem.contents_default m |}).
    - unfold permMapLt in Hlt.
      assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                            Maps.PMap.get b (Mem.mem_access m) ofs Max).
      { unfold getMaxPerm. intros.
        rewrite Maps.PMap.gmap. reflexivity. }
      intros.
      specialize (Hlt b ofs).
      specialize (Heq b ofs).
      unfold getMaxPerm in Hlt.
      unfold Maps.PMap.get in *. simpl in *.
      rewrite Maps.PTree.gmap; simpl.
      match goal with
        | [|- context[match Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
          destruct (Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
      end; auto; unfold Coqlib.option_map in Heqo.
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; try discriminate.
      + inversion Heqo; subst; clear Heqo.
        rewrite Heq in Hlt. auto.
      + unfold Mem.perm_order''. by destruct ((Mem.mem_access m).1 ofs Max).
    - intros b ofs k Hnext.
    - unfold permMapLt in Hlt.
      assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                            Maps.PMap.get b (Mem.mem_access m) ofs Max).
      { unfold getMaxPerm. intros.
        rewrite Maps.PMap.gmap. reflexivity. }
      specialize (Hlt b ofs).
      specialize (Heq b ofs).
      unfold Maps.PMap.get in *.
      simpl in *.
      rewrite Maps.PTree.gmap; simpl.
      assert (H := Mem.nextblock_noaccess m).
      specialize (H b). unfold Maps.PMap.get in H.
      match goal with
        | [|- context[match Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
          destruct (Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
      end; auto; unfold Coqlib.option_map in Heqo;
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:Heqo2; try discriminate.
      inversion Heqo. subst f. clear Heqo.
      destruct k; auto.
      rewrite Heq in Hlt.
      specialize (H ofs Max). rewrite H in Hlt; auto.
      unfold Mem.perm_order'' in Hlt. destruct (Maps.PTree.get b p'.2).
      destruct (o0 ofs); tauto.
      destruct (p'.1 ofs); tauto.
      rewrite H; auto. destruct k; auto.
  Defined.

  Lemma restrPermMap_nextblock :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)),
      Mem.nextblock (restrPermMap Hlt) = Mem.nextblock m.
  Proof.
    intros. unfold restrPermMap. reflexivity.
  Qed.

  Lemma restrPermMap_irr : forall p' p'' m
                             (Hlt : permMapLt p' (getMaxPerm m))
                             (Hlt': permMapLt p'' (getMaxPerm m))
                             (Heq_new: p' = p''),
                             restrPermMap Hlt = restrPermMap Hlt'.
  Proof.
    intros. subst.
    apply f_equal. by apply proof_irr.
  Qed.

  Lemma restrPermMap_disjoint_inv:
    forall (mi mj m : mem) (pi pj : access_map)
      (Hcan_m: isCanonical (getMaxPerm m))
      (Hltj: permMapLt pj (getMaxPerm m))
      (Hlti: permMapLt pi (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pi pj)
      (Hrestrj: restrPermMap Hltj = mj)
      (Hrestri: restrPermMap Hlti = mi),
      permMapsDisjoint (getCurPerm mi) (getCurPerm mj).
  Proof.
    intros. rewrite <- Hrestri. rewrite <- Hrestrj.
    unfold restrPermMap, getCurPerm, permMapsDisjoint. simpl in *.
    intros b ofs.
    do 2 rewrite Maps.PMap.gmap.
    clear Hrestrj Hrestri.
    unfold permMapLt, Mem.perm_order'' in *.
    specialize (Hltj b ofs); specialize (Hlti b ofs).
    unfold getMaxPerm in *; simpl in *.
    rewrite Maps.PMap.gmap in Hlti, Hltj.
    unfold permMapsDisjoint, Maps.PMap.get in *; simpl in *.
    do 2 rewrite Maps.PTree.gmap. unfold Coqlib.option_map.
    specialize (Hdisjoint b ofs).
    assert (Hnone: (Mem.mem_access m).1 ofs Max = None)
      by (unfold isCanonical in Hcan_m; simpl in Hcan_m;
            by apply equal_f with (x:=ofs) in Hcan_m).
    destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; auto.
    rewrite Hnone in Hlti, Hltj;
      destruct (Maps.PTree.get b pi.2)
      as [f1 |] eqn:?;
                destruct (Maps.PTree.get b pj.2) as [f2|] eqn:?;
      repeat match goal with
               | [H: match ?Expr with _ => _ end |- _] => destruct Expr
             end; tauto.
  Qed.

  Lemma no_race_wf : forall tid (cont: containsThread tp tid) (Hrace: race_free tp),
                       shareMap_wf tp (getThreadS cont) tid.
  Proof.
    intros; unfold shareMap_wf, getThreadS in *; auto.
  Defined.

End poolLemmas.

Module Concur.
  Section Concur.

    Import ThreadPool.
    Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}.

    Notation thread_pool := (t cT).
    Notation perm_map := access_map.

    Variable the_ge : G.
    Definition ls_id : nat := 0.
    Definition sp_id : nat := 1.

    Record invariant (tp : thread_pool) :=
      { no_race : race_free tp;
        lock_set : forall (cont : containsThread tp ls_id), exists c,
              getThreadC cont = Krun c /\ halted the_sem c;
        share_pool : forall (cont : containsThread tp sp_id), exists c,
              getThreadC cont = Krun c /\ halted the_sem c }.

    (* Semantics of the coarse-grained concurrent machine*)
    (* Definition cont2ord {ms tid0} (cnt: containsThread ms tid0) := *)
    (*   Ordinal cnt. *)

    Inductive dry_step {tid0 tp m} (cnt: containsThread tp tid0)
      (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
    | step_dry :
        forall (tp':thread_pool) c m1 m' (c' : cT),
          let: smap := getThreadS cnt in
          forall (Hrestrict_pmap:
               restrPermMap (permMapsInv_lt (perm_comp Hcompatible) cnt) = m1)
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt = Krun c)
            (Hcorestep: corestep the_sem the_ge c m1 c' m')
            (Htp': tp' = updThread cnt (Krun c')
                                   (access_to_share_map smap (getCurPerm m'))),
            dry_step cnt Hcompatible tp' m'.

    (*missing lock-ranges*)
    Inductive ext_step {tid0 tp m}
              (cnt0: containsThread tp tid0) (Hcompat: mem_compatible tp m):
      thread_pool -> mem -> Prop :=
    | step_lock :
        forall (tp' tp'':thread_pool) m1 c c' m' b ofs smap_sp' smap_tid' tmap
          (cnt_ls: containsThread tp ls_id)
          (cnt_sp: containsThread tp sp_id),
          let: smap_tid := getThreadS cnt0 in
          let: smap_sp := getThreadS cnt_sp in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hrestrict_pmap:
               restrPermMap (permMapsInv_lt (perm_comp Hcompatible) cnt_ls) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Hjoin1: shareMapsJoin smap_sp' tmap smap_sp)
            (Hjoin2: shareMapsJoin smap_tid tmap smap_tid')
            (Htp': tp' = updThreadS cnt_sp smap_sp')
            (Htp'': tp'' = updThread (updThreadS_cnt Htp') (Kresume c')
                                     smap_tid'),
            ext_step cnt0 Hcompat tp'' m'

    | step_unlock :
        forall  (tp' tp'':thread_pool) m1 c c' m' b ofs smap_sp' smap_tid' tmap
           (cnt_ls: containsThread tp ls_id)
           (cnt_sp: containsThread tp sp_id),
          let: smap_tid := getThreadS cnt0 in
          let: smap_sp := getThreadS cnt_sp in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
            (Hrestrict_pmap:
               restrPermMap (permMapsInv_lt (perm_comp Hcompat) cnt_ls) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Hjoin1: shareMapsJoin smap_tid' tmap smap_tid)
            (Hjoin2: shareMapsJoin smap_sp tmap smap_sp')
            (Htp': tp' = updThreadS cnt_sp smap_sp')
            (Htp'': tp'' = updThread (updThreadS_cnt Htp') (Kresume c')
                                   smap_tid'),
            ext_step cnt0 Hcompat tp'' m'

    | step_create :
        forall  (tp_upd tp':thread_pool) c c' c_new vf arg smap_tid' tmap
           (cnt_ls: containsThread tp ls_id)
           (cnt_sp: containsThread tp sp_id),
          let: smap_tid := getThreadS cnt0 in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (CREATE, ef_sig CREATE, vf::arg::nil))
            (Hinitial: initial_core the_sem the_ge vf (arg::nil) = Some c_new)
            (Hafter_external: after_external the_sem
                                             (Some (Vint Int.zero)) c = Some c')
            (Hjoin: shareMapsJoin smap_tid' tmap smap_tid)
            (Htp_upd: tp_upd = updThread cnt0 (Kresume c') smap_tid')
            (Htp': tp' = addThread tp_upd c_new tmap),
            ext_step cnt0 Hcompat tp' m

    | step_mklock :
        forall  (tp' tp'': thread_pool) m1 c c' m' b ofs smap_tid' smap_ls'
           (cnt_ls: containsThread tp ls_id),
          let: smap_tid := getThreadS cnt0 in
          let: smap_ls := getThreadS cnt_ls in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
            (Hrestrict_pmap: restrPermMap
                               (permMapsInv_lt (perm_comp Hcompat) cnt_ls) = m1)
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hdrop_share:
               setShare extern_retainer b (Int.intval ofs) smap_tid = smap_tid')
            (Hlp_share: setShare Ews
                               b (Int.intval ofs) smap_ls = smap_ls')
            (Hafter_external: after_external
                                the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThreadS cnt_ls smap_ls')
            (Htp'':
               tp'' = updThread (updThreadS_cnt Htp') (Kresume c') smap_tid'),
            ext_step cnt0 Hcompat tp'' m'

    | step_freelock :
        forall  (tp' tp'': thread_pool) c c' b ofs smap_tid' smap_ls'
           (cnt_ls: containsThread tp ls_id),
          let: smap_tid := getThreadS cnt0 in
          let: smap_ls := getThreadS cnt_ls in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
            (Hdrop_share:
               setShare Share.bot b (Int.intval ofs) smap_ls = smap_ls')
            (Hafter_external: after_external
                                the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThreadS cnt_ls smap_ls')
            (Htp'':
               tp'' = updThread (updThreadS_cnt Htp') (Kresume c') smap_tid'),
            ext_step cnt0 Hcompat  tp'' m

    | step_lockfail :
        forall  c b ofs m1
           (cnt_ls: containsThread tp ls_id),
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hrestrict_pmap: restrPermMap
                               (permMapsInv_lt (perm_comp Hcompat) cnt_ls) = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
            ext_step cnt0 Hcompat tp m.
  End Concur.

  Module ShareMachineSig (Sem: Semantics) <: ConcurrentMachineSig NatTID.
    (*TID = NAT*)
    Definition tid := nat.
    (*Memories*)
    Definition richMem: Type:= Sem.M.
    Definition dryMem: richMem -> mem:= fun x => x.

    (*CODE*)
    Definition cT: Type:= Sem.C.
    Definition G: Type:= Sem.G.
    Definition Sem := Sem.Sem.
    Definition cT': Type := @ctl cT.

    (*thread pool*)
    Import ThreadPool.
    Notation thread_pool := (t cT).

    (*MACHINE VARIABLES*)
    Definition machine_state: Type:= thread_pool.
    Definition containsThread: machine_state -> tid -> Prop:=
      fun ms tid0 => tid0 < (num_threads ms).
    Definition ls_id : tid:= 0.
    Definition sp_id : tid:= 1.

    (*INVARIANTS*)
    (*The state respects the memory*)
    Definition mem_compatible: machine_state -> mem -> Prop:=
      @mem_compatible cT.

    (*CODE GETTER AND SETTER*)
    Definition getThreadC: forall {ms tid0}, containsThread ms tid0 -> @ctl cT:= @getThreadC cT.
    Definition updThreadC: forall {ms tid0}, containsThread ms tid0 -> @ctl cT -> machine_state:= @updThreadC cT.

    (*Steps*)
    Definition cstep (genv:G): forall {tid0 ms m},
                                 containsThread ms tid0 -> mem_compatible ms m ->
                                 machine_state -> mem -> Prop:=
      @dry_step cT G Sem genv.

    Definition conc_call (genv:G):
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        machine_state -> mem -> Prop:=
      fun tid ms m => @ext_step cT G Sem genv tid ms m.

    Inductive threadHalted': forall {tid0 ms},
                               containsThread ms tid0 -> Prop:=
    | thread_halted':
        forall tp c tid0
          (cnt: containsThread tp tid0),
          let: tid := Ordinal cnt in
          forall
            (Hthread: getThreadC cnt = Krun c)
            (Hcant: halted Sem c),
            threadHalted' cnt.
    Definition threadHalted: forall {tid0 ms},
                               containsThread ms tid0 -> Prop:= @threadHalted'.

    Lemma onePos: (0<1)%coq_nat. auto. Qed.
    Definition initial_machine c:=
      @mk cT (mkPos onePos) (fun _ => c) (fun _ => empty_share_map) .
    Definition init_mach  (genv:G)(v:val)(args:list val):option machine_state:=
      match initial_core Sem genv v args with
      | Some c => Some (initial_machine (Kresume c) )
      | None => None
      end.
  End ShareMachineSig.


  (* Here I make the core semantics*)
  Variable example_G: Type.
  Variable example_C: Type.
  Variable example_sem: CoreSemantics example_G example_C mem.
  Module Sem: Semantics.
    Definition G:= example_G.
    Definition C:= example_C.
    Definition M:= mem.
    Definition Sem:=example_sem.
  End Sem.
  Module mySchedule := ListScheduler NatTID.
  Module mySem := ShareMachineSig Sem.
  Module myCoarseSemantics :=
    CoarseMachine NatTID mySchedule mySem.
  Module myFineSemantics :=
    FineMachine NatTID mySchedule mySem.

  Definition coarse_semantics:=
    myCoarseSemantics.MachineSemantics.
  Definition fine_semantics:=
    myFineSemantics.MachineSemantics.

End Concur.



(* After this there needs to be some cleaning. *)










(* Section InitialCore. *)

(*   Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}. *)
(*   Import ThreadPool. *)


(*   Notation thread_pool := (t cT). *)
(*   Notation perm_map := access_map. *)

(*   Definition at_external (st : (list nat) * thread_pool) *)
(*   : option (external_function * signature * seq val) := None. *)

(*   Definition after_external (ov : option val) (st : list nat * thread_pool) : *)
(*     option (list nat * thread_pool) := None. *)

(*   Definition two_pos : pos := mkPos NPeano.Nat.lt_0_2. *)

(*   Definition ord1 := Ordinal (n := two_pos) (m := 1) (leqnn two_pos). *)

(*   (*not clear what the value of halted should be*) *)
(*   Definition halted (st : list nat * thread_pool) : option val := None. *)

(*   Variable compute_init_perm : G -> access_map. *)
(*   Variable lp_code : cT. *)
(*   Variable sched : list nat. *)

(*   Definition initial_core the_ge (f : val) (args : list val) : option (list nat * thread_pool) := *)
(*     match initial_core the_sem the_ge f args with *)
(*       | None => None *)
(*       | Some c => *)
(*         Some (sched, ThreadPool.mk *)
(*                        two_pos *)
(*                        (fun tid => if tid == ord0 then lp_code *)
(*                                 else if tid == ord1 then c *)
(*                                      else c (*bogus value; can't occur*)) *)
(*                        (fun tid => if tid == ord0 then empty_map else *)
(*                                   if tid == ord1 then compute_init_perm the_ge *)
(*                                   else empty_map) *)
(*                        0) *)
(*     end. *)

(*   Variable aggelos : nat -> access_map. *)

(*   Definition cstep (the_ge : G) (st : list nat * thread_pool) m *)
(*              (st' : list nat * thread_pool) m' := *)
(*     @step cT G the_sem the_ge aggelos (@coarse_step cT G the_sem the_ge) *)
(*           (fst st) (snd st) m (fst st') (snd st') m'. *)

(*   Definition fstep (the_ge : G) (st : list nat * thread_pool) m *)
(*              (st' : list nat * thread_pool) m' := *)
(*     @step cT G the_sem the_ge aggelos (@fine_step cT G the_sem the_ge) *)
(*           (fst st) (snd st) m (fst st') (snd st') m'. *)

(*   Program Definition coarse_semantics : *)
(*     CoreSemantics G (list nat * thread_pool) mem := *)
(*     Build_CoreSemantics _ _ _ *)
(*                         initial_core *)
(*                         at_external *)
(*                         after_external *)
(*                         halted *)
(*                         cstep *)
(*                         _ _ _. *)

(*   Program Definition fine_semantics : *)
(*     CoreSemantics G (list nat * thread_pool) mem := *)
(*     Build_CoreSemantics _ _ _ *)
(*                         initial_core *)
(*                         at_external *)
(*                         after_external *)
(*                         halted *)
(*                         fstep *)
(*                         _ _ _. *)

(* End InitialCore. *)

(* End Concur. *)
