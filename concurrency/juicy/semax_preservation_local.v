Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.msl.age_to.
Require Import VST.veric.aging_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.cl_step_lemmas.
Require Import VST.concurrency.juicy.resource_decay_lemmas.
Require Import VST.concurrency.juicy.resource_decay_join.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.common.lksize.

Local Arguments getThreadR {_} {_} {_} _ _ _.
Local Arguments getThreadC {_} {_} {_} _ _ _.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread {_} {_} {_} _ _ _ _ _.
Local Arguments updThreadR {_} {_} {_} _ _ _ _.
Local Arguments updThreadC {_} {_} {_} _ _ _ _.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

Lemma resource_decay_joinlist b phi1 phi1' l Phi :
  rmap_bound b Phi ->
  resource_decay b phi1 phi1' ->
  ghost_of phi1' = ghost_fmap (approx (level phi1')) (approx (level phi1')) (ghost_of phi1) ->
  joinlist (phi1 :: l) Phi ->
  exists Phi',
    joinlist (phi1' :: (map (age_to (level phi1')) l)) Phi' /\
    resource_decay b Phi Phi' /\ ghost_of Phi' = own.ghost_approx Phi' (ghost_of Phi).
Proof.
  intros B rd g (x & h & j).
  assert (Bx : rmap_bound b x). { apply (rmap_bound_join j) in B. intuition. }
  destruct (resource_decay_join _ _ _ _ _ Bx rd g j) as (Phi' & j' & rd').
  exists Phi'; split; auto.
  exists (age_to (level phi1') x); split; auto.
  apply joinlist_age_to, h.
Qed.

Lemma resource_decay_join_all ge {tp : jstate ge} {m Phi} c' {phi' i} {cnti : containsThread tp i}:
  rmap_bound (Mem.nextblock m) Phi ->
  resource_decay (Mem.nextblock m) (getThreadR i tp cnti) phi' /\
  level (getThreadR i tp cnti) = S (level phi') /\
  ghost_of phi' = ghost_fmap (approx (level phi')) (approx (level phi')) (ghost_of (getThreadR i tp cnti)) ->
  join_all tp Phi ->
  exists Phi',
    join_all (updThread i (age_tp_to (level phi') tp) (cnt_age' cnti) c' phi') Phi' /\
    resource_decay (Mem.nextblock m) Phi Phi' /\
    ghost_of Phi' = own.ghost_approx Phi' (ghost_of Phi) /\
    level Phi = S (level Phi').
Proof.
  do 2 rewrite join_all_joinlist.
  intros B (rd & lev & g) j.
  rewrite (maps_getthread _ _ cnti) in j.
  destruct (resource_decay_joinlist _ _ _ _ _ B rd g j) as (Phi' & j' & rd' & ?).
  exists Phi'; split; [ | split; [|split]]; auto.
  - rewrite maps_updthread.
    exact_eq j'. f_equal. f_equal. rewrite <-all_but_map, maps_age_to.
    auto.
  - exact_eq lev; f_equal.
    + apply rmap_join_sub_eq_level. eapply joinlist_join_sub; eauto. left; auto.
    + f_equal. apply rmap_join_sub_eq_level. eapply joinlist_join_sub; eauto. left; auto.
Qed.

Lemma resource_decay_join_identity b phi phi' e e' :
  resource_decay b phi phi' ->
  ghost_of phi' = ghost_fmap (approx (level phi')) (approx (level phi')) (ghost_of phi) ->
  sepalg.joins phi e ->
  sepalg.joins phi' e' ->
  identity e ->
  identity e' ->
  e' = age_to (level phi') e.
Proof.
  intros rd g j j' i i'.
  apply rmap_ext.
  - apply rmap_join_eq_level in j.
    apply rmap_join_eq_level in j'.
    destruct rd as (lev, rd).
    rewrite level_age_to; eauto with *.
  - intros l.
    rewrite age_to_resource_at.
    apply resource_at_identity with (loc := l) in i.
    apply resource_at_identity with (loc := l) in i'.
    apply empty_NO in i.
    apply empty_NO in i'.
    destruct j as (a & j).
    destruct j' as (a' & j').
    apply resource_at_join with (loc := l) in j.
    apply resource_at_join with (loc := l) in j'.
    unfold compcert_rmaps.R.AV.address in *.
    destruct i as [E | (k & pp & E)], i' as [E' | (k' & pp' & E')]; rewrite E, E' in *.
    + reflexivity.
    + inv j'.
      pose proof resource_decay_PURE_inv rd as I.
      repeat autospec I.
      breakhyps.
      rewr (phi @ l) in j.
      inv j.
    + inv j.
      pose proof resource_decay_PURE rd as I.
      repeat autospec I.
      rewr (phi' @ l) in j'.
      inv j'.
    + inv j.
      pose proof resource_decay_PURE rd as I.
      specialize (I l k pp ltac:(auto)).
      rewr (phi' @ l) in j'.
      inv j'.
      reflexivity.
  - rewrite age_to_ghost_of.
    rewrite (identity_core (ghost_of_identity _ i)), (identity_core (ghost_of_identity _ i')).
    rewrite !ghost_core; auto.
Qed.

Lemma same_except_cur_jm_ ge tp m phi i cnti compat :
  same_except_cur m (m_dry (@jm_ ge tp m phi i cnti compat)).
Proof.
  repeat split.
  extensionality loc.
  apply juicyRestrictMax.
Qed.

Lemma resource_decay_lockSet_in_juicyLocks b phi phi' lset :
  resource_decay b phi phi' ->
  lockSet_block_bound lset b ->
  lockSet_in_juicyLocks lset phi ->
  lockSet_in_juicyLocks lset phi'.
Proof.
  intros RD LB IN loc IT.
  destruct (IN _ IT) as (sh & E). exists sh. intros ? H8. specialize (E _ H8).
  destruct E as [sh' [rsh' [pp [Ex E]]]]; exists sh', rsh', (preds_fmap (approx (level phi')) (approx (level phi')) pp).
  split; auto.
  destruct RD as [L RD].
  destruct (RD (fst loc, snd loc + i)) as [NN [R|[R|[[P [v R]]|R]]]].
  +rewrite <- R. rewrite E. simpl. auto.
  + rewrite E in R. destruct R as (sh'' & wsh'' & v & v' & R & H). discriminate.
  + specialize (LB loc).
    cut (fst loc < b)%positive. now intro; exfalso; eauto.
    apply LB. simpl in *; destruct (AMap.find (elt:=option rmap) loc lset).
    * apply I.
    * inversion IT.
  + destruct R as (v & v' & R & N').
      congruence.
Qed.

(*
Lemma isLK_rewrite r :
  (forall (sh : Share.t) (rsh : shares.readable_share sh) (z : Z) (P : preds), r <> YES sh rsh (LK z) P)
  <->
  ~ isLK r.
Proof.
  destruct r as [t0 | t0 p [] p0 | k p]; simpl; unfold isLK in *; split.
  all: try intros H ?; intros; breakhyps.
  intros E; injection E; intros; subst.
  apply H; eauto.
Qed.
*)

Lemma resource_decay_lock_coherence {b phi phi' lset m} :
  resource_decay b phi phi' ->
  lockSet_block_bound lset b ->
  (forall l p, AMap.find l lset = Some (Some p) -> level p = level phi) ->
  lock_coherence lset phi m ->
  lock_coherence (AMap.map (Coqlib.option_map (age_to (level phi'))) lset) phi' m.
Proof.
  intros rd BOUND SAMELEV LC loc; pose proof rd as rd'; destruct rd' as [L RD].
  specialize (LC loc).
  specialize (RD loc).
  rewrite AMap_find_map_option_map.
  destruct (AMap.find loc lset)
    as [[unlockedphi | ] | ] eqn:Efind;
    simpl option_map; cbv iota beta; swap 1 3.
  - (* rewrite <-isLKCT_rewrite. *)
    (* rewrite <-isLKCT_rewrite in LC. *)
    contradict LC.
    destruct LC as [sh [rsh [z [pp ?]]]]. rewrite H in *.
    destruct RD as [NN [R|[R|[[P [v R]]|R]]]].
    + destruct (phi @ loc); inv R; hnf; eauto.
    + destruct R as (sh'' & wsh & v & v' & E & E'). (* split; *) congruence.
    + (* split; *) congruence.
    + destruct R as (v & PP  & ? & ?). (* split; *) congruence.

  - assert (fst loc < b)%positive.
    { apply BOUND.
      rewrite Efind.
      constructor. }
    destruct LC as (dry & align & bound (* & sh *) & R & lk); split; auto.
    eapply resource_decay_lkat in lk; eauto.

  - assert (fst loc < b)%positive.
    { apply BOUND.
      rewrite Efind.
      constructor. }
    destruct LC as (dry & align & bound & (* sh &  *)R & lk & sat); repeat (split; auto).
    exists (* sh,  *)(approx (level phi') R); split.
    + eapply resource_decay_lkat in lk; eauto.
    + match goal with |- ?a \/ ?b => cut (~b -> a) end.
      { destruct (level phi'); auto. } intros Nz.
      split.
      * rewrite level_age_by.
        rewrite level_age_to.
        -- omega.
        -- apply SAMELEV in Efind.
           eauto with *.
      * destruct sat as [sat | ?]; [ | omega ].
        unfold age_to.
        rewrite age_by_age_by.
        rewrite plus_comm.
        rewrite <-age_by_age_by.
        apply age_by_ind.
        { destruct R as [p h]. apply h. }
        apply sat.
Qed.

Lemma personal_mem_rewrite m phi phi' pr pr' :
  phi = phi' ->
  @personal_mem m phi pr = @personal_mem m phi' pr'.
Proof.
  intros ->; f_equal. apply proof_irr.
Qed.

Lemma invariant_thread_step
 (mem_cohere_step
     : forall (c c' : corestate) (jm jm' : juicy_mem) (Phi X : rmap) (ge : genv),
       mem_cohere' (m_dry jm) Phi ->
       join (m_phi jm) X Phi ->
       @corestep corestate juicy_mem (@juicy_core_sem corestate (cl_core_sem ge)) c jm c' jm' ->
       exists Phi' : rmap,
         join (m_phi jm') (@age_to (@level rmap ag_rmap (m_phi jm')) rmap ag_rmap X) Phi' /\
         mem_cohere' (m_dry jm') Phi')
  (personal_mem_equiv_spec
     : forall (m m' : Mem.mem') (phi : rmap) (pr : mem_cohere' m phi) (pr' : mem_cohere' m' phi),
       Mem.nextblock m = Mem.nextblock m' ->
       (forall loc : address, max_access_at m loc = max_access_at m' loc) ->
       (forall loc : AV.address, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
       mem_equiv (m_dry (personal_mem m phi pr)) (m_dry (personal_mem m' phi pr')))
  (Jspec : juicy_ext_spec unit) Gamma
  n m ge i tr sch tp Phi ci ci' jmi'
  (Stable : ext_spec_stable age Jspec)
  (Stable' : ext_spec_stable juicy_mem_equiv Jspec)
  (envcoh : env_coherence Jspec ge Gamma Phi)
  (extcompat : joins (ghost_of Phi) (Some (ext_ref tt, NoneP) :: nil))
  (compat : mem_compatible_with tp m Phi)
  (En : level Phi = S n)
  (lock_bound : lockSet_block_bound (lset tp) (Mem.nextblock m))
  (sparse : lock_sparsity (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : threads_safety Jspec m tp Phi compat (S n))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (cnti : containsThread tp i)
  (stepi : corestep (juicy_core_sem (cl_core_sem ge)) ci (jm_ cnti compat) ci' jmi')
  (safei' : forall ora, jm_bupd ora (jsafeN Jspec ge n ora ci') jmi')
  (Eci : getThreadC i tp cnti = Krun ci)
  (tp' := age_tp_to (level jmi') tp)
  (tp'' := updThread i tp' (cnt_age' cnti) (Krun ci') (m_phi jmi') : jstate ge)
  (cm' := (m_dry jmi', (tr, i :: sch, tp''))) :
  state_bupd (state_invariant Jspec Gamma n) cm'.
Proof.
  (** * Two steps : [x] -> [x'] -> [x'']
          1. we age [x] to get [x'], the level decreasing
          2. we update the thread to  get [x'']
   *)
  destruct compat as [J AC LW LJ JL] eqn:Ecompat.
  rewrite <-Ecompat in *.
  pose proof J as J_; move J_ before J.
  rewrite join_all_joinlist in J_.
  pose proof J_ as J__.
  rewrite maps_getthread with (cnti0 := cnti) in J__.
  destruct J__ as (ext & Hext & Jext).
  assert (Eni : level (jm_ cnti compat) = S n). {
    rewrite <-En, level_juice_level_phi.
    eapply rmap_join_sub_eq_level.
    exists ext; auto.
  }

  (** * Getting new global rmap (Phi'') with smaller level [n] *)
  assert (B : rmap_bound (Mem.nextblock m) Phi) by apply compat.
  destruct (resource_decay_join_all _ (Krun ci') B (proj2 stepi) J)
    as [Phi'' [J'' [RD [G L]]]].
  rewrite join_all_joinlist in J''.
  assert (Eni'' : level (m_phi jmi') = n). {
    clear -stepi Eni.
    rewrite <-level_juice_level_phi.
    cut (S (level jmi') = S n); [ congruence | ].
    destruct stepi as [_ [_ [<- _]]].
    apply Eni.
  }
  pose proof eq_refl tp' as Etp'.
  unfold tp' at 2 in Etp'.
  move Etp' before tp'.
  rewrite level_juice_level_phi, Eni'' in Etp'.
  assert (En'' : level Phi'' = n). {
    rewrite <-Eni''.
    symmetry; apply rmap_join_sub_eq_level.
    rewrite maps_updthread in J''.
    destruct J'' as (r & _ & j).
    exists r; auto.
  }

  (** * First, age the whole machine *)
  pose proof J_ as J'.
  unshelve eapply @joinlist_age_to with (n := n) in J'.
  (* auto with *. (* TODO please report -- but hard to reproduce *) *)
  all: hnf.
  all: [> refine ag_rmap |  | refine Age_rmap | refine Perm_rmap ].

  (** * Then relate this machine with the new one through the remaining maps *)
  rewrite (maps_getthread i tp cnti) in J'.
  rewrite maps_updthread in J''.
  pose proof J' as J'_. destruct J'_ as (ext' & Hext' & Jext').
  rewrite maps_age_to, all_but_map in J''.
  pose proof J'' as J''_. destruct J''_ as (ext'' & Hext'' & Jext'').
  rewrite Eni'' in *.
  assert (Eext'' : ext'' = age_to n ext). {
    destruct (coqlib3.nil_or_non_nil (map (age_to n) (all_but i (maps tp)))) as [N|N]; swap 1 2.
    - (* Uniqueness of [ext] : when the rest is not empty *)
      eapply @joinlist_age_to with (n := n) in Hext.
      all: [> | now apply Age_rmap | now apply Perm_rmap ].
      unshelve eapply (joinlist_inj _ _ _ _ Hext'' Hext).
      apply N.
    - (* when the list is empty, we know that ext (and hence [age_to
        .. ext]) and ext' are identity, and they join with something
        that have the same PURE *)
      rewrite N in Hext''. simpl in Hext''.
      rewrite <-Eni''.
      eapply resource_decay_join_identity.
      + apply (proj2 stepi).
      + apply (proj2 stepi).
      + exists Phi. apply Jext.
      + exists Phi''. apply Jext''.
      + change (joinlist nil ext). exact_eq Hext. f_equal.
        revert N.
        destruct (maps tp) as [|? [|]]; destruct i; simpl; congruence || auto.
      + change (joinlist nil ext''). apply Hext''.
  }
  subst ext''.

  assert (compat_ : mem_compatible_with tp (m_dry (jm_ cnti compat)) Phi).
  { apply mem_compatible_with_same_except_cur with (m := m); auto.
    apply same_except_cur_jm_. }

  assert (compat' : mem_compatible_with tp' (m_dry (jm_ cnti compat)) (age_to n Phi)).
  { unfold tp'.
    rewrite level_juice_level_phi, Eni''.
    apply mem_compatible_with_age. auto. }

  assert (compat'' : mem_compatible_with tp'' (m_dry jmi') Phi'').
  {
    unfold tp''.
    constructor.

    - (* join_all (proved in lemma) *)
      rewrite join_all_joinlist.
      rewrite maps_updthread.
      unfold tp'. rewrite maps_age_to, all_but_map.
      exact_eq J''; repeat f_equal.
      auto.

    - (* cohere *)
      pose proof compat_ as c. destruct c as [_ MC _ _ _].
      destruct (mem_cohere_step
                  ci ci' (jm_ cnti compat) jmi'
                  Phi ext ge MC Jext stepi) as (Phi''_ & J''_ & MC''_).
      exact_eq MC''_.
      f_equal.
      rewrite Eni'' in J''_.
      eapply join_eq; eauto.

    - (* lockSet_Writable *)
      simpl.
      clear -LW stepi lock_coh lock_bound compat_.
      destruct stepi as [step _]. fold (jm_ cnti compat) in step.
      intros b ofs IN.
      unfold tp' in IN.
      rewrite lset_age_tp_to in IN.
      rewrite isSome_find_map in IN.
      specialize (LW b ofs IN).
      intros ofs0 interval.

      (* the juicy memory doesn't help much because we care about Max
        here. There are several cases were no permission change, the
        only cases where they do are:
        (1) call_internal (alloc_variables m -> m1)
        (2) return (free_list m -> m')
        in the end, (1) cannot hurt because there is already
        something, but maybe things have returned?
       *)

      set (mi := m_dry (jm_ cnti compat)).
      fold mi in step.
      (* state that the Cur [Nonempty] using the juice and the
             fact that this is a lock *)
      assert (CurN : (Mem.mem_access mi) !! b ofs0 Cur = Some Nonempty
                     \/ (Mem.mem_access mi) !! b ofs0 Cur = None).
      {
        pose proof juicyRestrictCurEq as H.
        unfold access_at in H.
        change b with (fst (b, ofs0)).
        change ofs0 with (snd (b, ofs0)).
        unfold mi.
        destruct compat_ as [_ MC _ _ _].
        destruct MC as [_ AC _ _].
        unfold jm_, personal_mem, m_dry.
        rewrite (H _ _  _ (b, ofs0)).
        cut (Mem.perm_order'' (Some Nonempty) (perm_of_res (getThreadR _ _ cnti @ (b, ofs0)))). {
          destruct (perm_of_res (getThreadR _ _ cnti @ (b,ofs0))) as [[]|]; simpl.
          all:intros po; inversion po; subst; eauto.
        }
        clear -compat IN interval lock_coh lock_bound.
        apply po_trans with (perm_of_res (Phi @ (b, ofs0))).
        - destruct compat.
          specialize (lock_coh (b, ofs)).
          assert (lk : exists (R : pred rmap), (lkat R (b, ofs)) Phi). {
            destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)) as [[lockphi|]|].
            - destruct lock_coh as [_ (align & bound & R & lk & _)].
              now eexists _; apply lk.
            - destruct lock_coh as [_ (align & bound & R & lk)].
              now eexists _; apply lk.
            - discriminate.
          }
          destruct lk as (R & lk).
          specialize (lk (b, ofs0)). simpl in lk.
          assert (adr_range (b, ofs) LKSIZE (b, ofs0))
            by apply interval_adr_range, interval.
          spec lk. now split; auto; lkomega. destruct lk as [sh [rsh lk]]; rewrite lk; constructor.
        - cut (join_sub (getThreadR _ _ cnti @ (b, ofs0)) (Phi @ (b, ofs0))).
          + apply po_join_sub.
          + apply resource_at_join_sub.
            eapply compatible_threadRes_sub.
            apply compat.
      }

      apply cl_step_decay in step.
      pose proof step b ofs0 as D.
      assert (Emi: (Mem.mem_access mi) !! b ofs0 Max = (Mem.mem_access m) !! b ofs0 Max).
      {
        pose proof juicyRestrictMax (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs0).
        unfold max_access_at, access_at in *.
        simpl fst in H; simpl snd in H.
        rewrite H.
        reflexivity.
      }

      destruct (Maps.PMap.get b (Mem.mem_access m) ofs0 Max)
        as [ [ | | | ] | ] eqn:Emax;
        try solve [inversion LW].
      + (* Max = Freeable *)

        (* concluding using [decay] *)
        revert step CurN.
        clearbody mi.
        generalize (m_dry jmi'); intros mi'.
        clear -Emi. intros D [NE|NE].
        * replace ((Mem.mem_access mi') !! b ofs0 Max) with (Some Freeable). now constructor.
          symmetry.
          destruct (D b ofs0) as [A B].
          destruct (valid_block_dec mi b) as [v|n].
          -- autospec B.
             destruct B as [B|B].
             ++ destruct (B Cur). congruence.
             ++ specialize (B Max). congruence.
          -- pose proof Mem.nextblock_noaccess mi b ofs0 Max n.
             congruence.
        * replace ((Mem.mem_access mi') !! b ofs0 Max) with (Some Freeable). now constructor.
          symmetry.
          destruct (D b ofs0) as [A B].
          destruct (valid_block_dec mi b) as [v|n].
          -- autospec B.
             destruct B as [B|B].
             ++ destruct (B Cur); congruence.
             ++ specialize (B Max). congruence.
          -- pose proof Mem.nextblock_noaccess mi b ofs0 Max n.
             congruence.

      + (* Max = writable : must be writable after, because unchanged using "decay" *)
        assert (Same: (Mem.mem_access m) !! b ofs0 Max = (Mem.mem_access mi) !! b ofs0 Max) by congruence.
        revert step Emi Same.
        generalize (m_dry jmi').
        generalize (juicyRestrict _ _ (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti))).
        clear.
        intros m0 m1 D Emi Same.
        match goal with |- _ ?a ?b => cut (a = b) end.
        { intros ->; apply po_refl. }
        specialize (D b ofs0).
        destruct D as [A B].
        destruct (valid_block_dec mi b) as [v|n].
        * autospec B.
          destruct B as [B|B].
          -- destruct (B Max); congruence.
          -- specialize (B Max). congruence.
        * pose proof Mem.nextblock_noaccess m b ofs0 Max n.
          congruence.

      + (* Max = Readable : impossible because Max >= Writable  *)
        autospec LW.
        autospec LW.
        rewrite Emax in LW.
        inversion LW.

      + (* Max = Nonempty : impossible because Max >= Writable  *)
        autospec LW.
        autospec LW.
        rewrite Emax in LW.
        inversion LW.

      + (* Max = none : impossible because Max >= Writable  *)
        autospec LW.
        autospec LW.
        rewrite Emax in LW.
        inversion LW.

    - (* juicyLocks_in_lockSet *)
      eapply same_locks_juicyLocks_in_lockSet.
      + eapply resource_decay_same_locks.
        apply RD.
      + simpl.
        clear -LJ. hnf.
        intros loc H.
        unfold tp'.
        rewrite lset_age_tp_to.
        rewrite isSome_find_map.
        eapply LJ; eauto.

    - (* lockSet_in_juicyLocks *)
      eapply resource_decay_lockSet_in_juicyLocks.
      + eassumption.
      + simpl.
        apply lockSet_Writable_lockSet_block_bound.
        clear -LW.
        intros b ofs.
        unfold tp'; rewrite lset_age_tp_to.
        rewrite isSome_find_map.
        apply LW.

      + clear -JL.
        unfold tp'.
        intros addr; simpl.
        unfold tp'; rewrite lset_age_tp_to.
        rewrite isSome_find_map.
        apply JL.
  }
  (* end of proving mem_compatible_with *)

  (* Now that mem_compatible_with is established, we move on to the
       invariant. Two important parts:

       1) lock coherence is maintained, because the thread step could
          not affect locks in either kinds of memories

       2) safety is maintained: for thread #i (who just took a step),
          safety of the new state follows from safety of the old
          state. For thread #j != #i, we need to prove that the new
          memory is [juicy_mem_equiv] to the old one, in the sense
          that wherever [Cur] was readable the values have not
          changed.
   *)

  apply state_inv_upd1 with (PHI := Phi'') (mcompat := compat'').
  - (* level *)
    assumption.

  - (* env_coherence *)
    eapply env_coherence_resource_decay with _ Phi; eauto. setoid_rewrite En''; omega.

  - rewrite G.
    destruct extcompat as [? Je]; eapply ghost_fmap_join in Je; eexists; eauto.

  - (* lock coherence: own rmap has changed, but we prove it did not affect locks *)
    unfold tp''; simpl.
    unfold tp'; simpl.
    apply lock_sparsity_age_to. auto.

  - (* lock coherence: own rmap has changed, but we prove it did not affect locks *)
    unfold lock_coherence', tp''; simpl lset.

    (* replacing level (m_phi jmi') with level Phi' ... *)
    assert (level (m_phi jmi') = level Phi'') by congruence.
    cut (lock_coherence
           (AMap.map (option_map (age_to (level Phi''))) (lset tp)) Phi''
           (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat'')))).
    { intros A; exact_eq A.
      f_equal. unfold tp'; rewrite lset_age_tp_to.
      f_equal. f_equal. f_equal. rewrite level_juice_level_phi; auto. }
    (* done replacing *)

    (* operations on the lset: nothing happened *)
    apply (resource_decay_lock_coherence RD).
    { auto. }
    { intros. eapply join_all_level_lset; eauto. }

    clear -lock_coh lock_bound stepi.

    (* what's important: lock values couldn't change during a corestep *)
    assert
      (SA' :
         forall loc,
           AMap.find (elt:=option rmap) loc (lset tp) <> None ->
           load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat))) loc =
           load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat''))) loc).
    {
      destruct stepi as [step RD].
      unfold cl_core_sem in *.
      simpl in step.
      pose proof cl_step_decay _ _ _ _ _ step as D.
      intros (b, ofs) islock.
      pose proof juicyRestrictMax (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs).
      pose proof juicyRestrictContents (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs).
      unfold load_at in *; simpl.
      set (W  := mem_compatible_locks_ltwritable (mem_compatible_forget compat )).
      set (W' := mem_compatible_locks_ltwritable (mem_compatible_forget compat'')).
      pose proof restrPermMap_Cur W as RW.
      pose proof restrPermMap_Cur W' as RW'.
      pose proof restrPermMap_contents W as CW.
      pose proof restrPermMap_contents W' as CW'.
      Transparent Mem.load.
      unfold Mem.load in *.
      destruct (Mem.valid_access_dec (restrPermMap W) Mint32 b ofs Readable) as [r|n]; swap 1 2.

      { (* can't be not readable *)
        destruct n.
        apply Mem.valid_access_implies with Writable.
        - eapply lset_valid_access; eauto.
        - constructor.
      }

      rewrite if_true by auto.
      destruct (Mem.valid_access_dec (restrPermMap W') Mint32 b ofs Readable) as [r'|n']; swap 1 2.
      { (* can't be not readable *)
        destruct n'.
        split.
        - apply Mem.range_perm_implies with Writable.
          + intros loc range.
            eapply lset_range_perm with (ofs := ofs); eauto.
            (* if LKSIZE>4:
              2:unfold size_chunk in *.
              2:unfold LKSIZE in *.
              2:omega.*)
            unfold tp''; simpl.
            unfold tp'; rewrite lset_age_tp_to.
            rewrite AMap_find_map_option_map.
            destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)).
            * discriminate.
            * tauto.
            * lkomega.
          + constructor.
        - (* basic alignment *)
          eapply lock_coherence_align; eauto.
      }

      rewrite if_true by auto.
      f_equal.
      f_equal.
      apply Mem.getN_exten.
      intros ofs0 interval.
      eapply equal_f with (b, ofs0) in CW.
      eapply equal_f with (b, ofs0) in CW'.
      unfold contents_at in CW, CW'.
      simpl fst in CW, CW'.
      simpl snd in CW, CW'.
      simpl lockSet in *. rewrite CW, CW'.
      pose proof cl_step_unchanged_on _ _ _ _ _ b ofs0 step as REW.
      rewrite <- REW.
      - reflexivity.
      - unfold Mem.valid_block in *.
        simpl.
        apply (lock_bound (b, ofs)).
        destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)). reflexivity. tauto.
      - pose proof juicyRestrictCurEq (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs0) as h.
        unfold access_at in *.
        simpl fst in h; simpl snd in h.
        unfold Mem.perm in *.
        setoid_rewrite h.
        cut (Mem.perm_order'' (Some Nonempty) (perm_of_res (getThreadR _ _ cnti @ (b, ofs0)))).
        { destruct (perm_of_res (getThreadR _ _ cnti @ (b, ofs0))); intros A B.
          all: inversion A; subst; inversion B; subst. }
        apply po_trans with (perm_of_res (Phi @ (b, ofs0))); swap 1 2.
        + eapply po_join_sub.
          apply resource_at_join_sub.
          eapply compatible_threadRes_sub.
          apply compat.
        + clear -lock_coh islock interval.
          (* todo make lemma out of this *)
          specialize (lock_coh (b, ofs)).
          assert (lk : exists R, (lkat R (b, ofs)) Phi). {
            destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)) as [[|]|].
            - destruct lock_coh as [_ (? & ? & ? & ? & ?)]; eauto.
            - destruct lock_coh as [_ (? & ? & ? & ?)]; eauto.
            - tauto.
          }
          destruct lk as (R & lk).
          specialize (lk (b, ofs0)).
          simpl in lk.
          assert (adr_range (b, ofs) 4%Z (b, ofs0))
            by apply interval_adr_range, interval.
          spec lk. split; auto. clear - H; unfold LKSIZE; destruct H; rewrite size_chunk_Mptr; simple_if_tac; omega.
          destruct lk as (? & ? & ->). simpl. constructor.
    }
    (* end of proof of: lock values couldn't change during a corestep *)

    unfold lock_coherence' in *.
    intros loc; specialize (lock_coh loc). specialize (SA' loc).
    destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [[lockphi|]|].
    + destruct lock_coh as [COH ?]; split; [ | easy ].
      rewrite <-COH; rewrite SA'; auto.
      congruence.
    + destruct lock_coh as [COH ?]; split; [ | easy ].
      rewrite <-COH; rewrite SA'; auto.
      congruence.
    + easy.

  - (* safety *)
    assert (containsThread tp'' i) as cnti''.
    { apply cntUpdate, cnt_age'; auto. }
    exists _, cnti''; split.
    + subst tp''; eexists; split.
      { rewrite gssThreadCode; auto. }
      intros ? HC Jg.
      rewrite gssThreadRes in Jg.
      specialize (safei' tt _ HC Jg) as (jm' & ? & Hupd & safei').
      eexists; split.
      { rewrite gssThreadRes; eauto. }
      exists (m_phi jm').
      destruct Hupd as (Hd & Hl & Hr).
      assert (resource_at (m_phi jm') =
        resource_at (getThreadR i (updThread i tp' (cnt_age' cnti) (Krun ci') (m_phi jmi')) cnti'')) as Hr'.
      { rewrite gssThreadRes; auto. }
      exists Hr'; split; [rewrite gssThreadRes; auto|].
      split; auto.
      intros []; exact_eq safei'; f_equal.
      apply juicy_mem_ext; auto.
      rewrite Hd; unfold personal_mem; simpl.
      apply mem_ext; auto.
      rewrite juicyRestrictCur_unchanged; [reflexivity|].
      intro; rewrite Hr.
      destruct jmi'; auto.
    + repeat intro.
      unfold tp'' at 1.
      unfold tp' at 1.
      unshelve erewrite gsoThreadCode; auto.

      clear Ecompat Hext' Hext'' J'' Jext Jext' Hext RD J' LW LJ JL.

      assert (notkrun : forall c, getThreadC j (age_tp_to (level jmi') tp) cntj <> Krun c). {
        eapply (unique_Krun_neq i j); eauto.
        apply unique_Krun_age_tp_to; eauto.
      }

      (** * Bring other thread #j's memory up to current #i's level *)
      assert (cntj' : containsThread tp j). {
        clear -cntj.
        unfold tp'', tp' in cntj.
        apply cntUpdate' in cntj.
        rewrite <-cnt_age_iff in cntj.
        apply cntj.
      }
      pose (jmj' := age_to (level (m_phi jmi')) (@jm_ _ tp m Phi j cntj' compat)).

      unshelve erewrite <-gtc_age; auto.
      pose proof safety _ cntj' ora as safej.

      destruct (getThreadC j tp cntj') as [c | c | c v | v v0] eqn:Ej.
      * (* krun: impossible *)
        exfalso. eapply notkrun. unshelve erewrite <-age_getThreadCode; eauto.
      * unfold tp'', tp'.
        REWR.
        REWR.
        apply jsafe_phi_age_to; auto.
        rewrite level_juice_level_phi.
        omega.
        apply jsafe_phi_downward.
        assumption.
      * unfold tp'', tp'.
        REWR.
        REWR.
        intros c' Ec'; specialize (safej c' Ec').
        apply jsafe_phi_bupd_age_to; auto.
        rewrite level_juice_level_phi.
        omega.
        apply jsafe_phi_bupd_downward.
        assumption.
      * destruct safej as (Harg & q_new & Einit & safej); split.
        { destruct stepi as (stepi & _).
          apply (corestep_mem (msem (ClightSemanticsForMachines.CLN_evsem ge))), mem_step_nextblock'
            in stepi; simpl in stepi.
          eapply val_inject_incr, Harg.
          apply flat_inj_incr; auto. }
        exists q_new; split; auto.
        unfold tp'', tp'.
        REWR.
        REWR.
        apply jsafe_phi_age_to; auto.
        rewrite level_juice_level_phi.
        omega.
        apply jsafe_phi_downward.
        assumption.

  - (* wellformedness *)
    intros j cntj.
    unfold tp'', tp'.
    destruct (eq_dec i j) as [ <- | ij].
    + unshelve erewrite gssThreadCode; auto.
    + unshelve erewrite gsoThreadCode; auto.
      specialize (wellformed j). clear -wellformed.
      assert_specialize wellformed by (destruct tp; auto).
      unshelve erewrite <-gtc_age; auto.

  - (* uniqueness *)
    intros notalone j cntj q Ecj.
    hnf in unique.
    assert_specialize unique by (destruct tp; apply notalone).
    specialize (unique j).
    destruct (eq_dec i j) as [ <- | ij].
    + apply unique with (cnti := cnti) (q := ci); eauto.
    + assert_specialize unique by (destruct tp; auto).
      apply unique with (q := q); eauto.
      exact_eq Ecj. f_equal.
      unfold tp'',  tp'.
      unshelve erewrite gsoThreadCode; auto.
      unshelve erewrite <-gtc_age; auto.
Qed.
