(** * Globals separated *)

(** globals_separate is an invariant enforcing
    that newly allocated blocks are NOT mapped
    to global blocks. It is used to re-establish
    meminj_preserves_globals in the after external
    diagram. In that sense it replaces
    sm_inject_separated (jan 2015).
 *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.
Require Import VST.sepcomp.mem_lemmas.

Definition globals_separate {F V:Type} (ge: Genv.t F V) mu nu :=
    forall b1 b2 d, as_inj mu b1 = None ->
            as_inj nu b1 =Some(b2,d) ->
            isGlobalBlock ge b2 = false.

Lemma gsep_refl:
  forall {F V} mu (ge: Genv.t F V),
    globals_separate ge mu mu.
  intros ? ? mu ge b1 b2 d map1 map2.
  rewrite map1 in map2; discriminate.
Qed.

Lemma gsep_domain_eq:
  forall {F1 F2 V1 V2} mu mu' (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2),
    globals_separate ge1 mu mu' ->
    genvs_domain_eq ge1 ge2 ->
    globals_separate ge2 mu mu'.
  intros ? ? ? ? mu mu' ge1 ge2 gsep geq b1 b2 d map1 map2.
  rewrite <- (genvs_domain_eq_isGlobal _ _ geq).
  eapply gsep; eauto.
Qed.


Lemma gsep_trans:
  forall {F V} (ge:  Genv.t F V) mu mu' mu'',
      Values.inject_incr (as_inj mu') (as_inj mu'') ->
      globals_separate ge mu mu' ->
      globals_separate ge mu' mu'' ->
      globals_separate ge mu mu''.
  intros ? ? ge mu mu' mu'' incr gsep12 gsep23 b1 b3 d3 map1 map3.
  destruct (as_inj mu' b1) as [[b2 d2]|] eqn: map2.
  + eapply gsep12.
  - eassumption.
  - rewrite (incr b1 b2 d2 map2) in map3; inversion map3. subst; eassumption.
  + eapply gsep23; eauto.
Qed.

Lemma gsep_trans':
  forall {F V} (ge:  Genv.t F V) mu mu' mu'',
      SM_wd mu'' ->
      intern_incr mu' mu'' ->
      globals_separate ge mu mu' ->
      globals_separate ge mu' mu'' ->
      globals_separate ge mu mu''.
  intros ? ? ge mu mu' mu'' smwd incr gsep12 gsep23 b1 b3 d3 map1 map3.
  assert (INCR: Values.inject_incr (as_inj mu') (as_inj mu'')) by (apply intern_incr_as_inj; auto).
  eapply gsep_trans; eauto.
Qed.

    (*
Lemma gsep_compose:
  forall {F V} (ge:  Genv.t F V) mu12 mu23 mu12' mu23',
    SM_wd mu12 ->
    SM_wd mu23 ->
    SM_wd mu12' ->
    SM_wd mu23' ->
    Values.inject_incr (as_inj mu12) (as_inj mu12') ->
    (locBlocksTgt mu12 = locBlocksSrc mu23 /\
         extBlocksTgt mu12 = extBlocksSrc mu23) ->
    globals_separate ge mu12 mu12' ->
    globals_separate ge mu23 mu23' ->
    globals_separate ge (compose_sm mu12 mu23) (compose_sm mu12' mu23').
  intros ? ? ge mu12 mu23 mu12' mu23' WD12 WD23 WD12' WD23' INCR GLUE gsep12 gsep23 b1 b3 d3 map13 map13'.
  destruct (compose_sm_as_injD _ _ _ _ _ map13' WD12' WD23') as [b2 [d1 [d2 [map1 [map2 extra]]]]].
  destruct (compose_sm_as_injD_None _ _ _ WD12 WD23 GLUE map13) as [map12| [b2' [d [map12 map23]]]].
  - assert (isGlobalBlock ge b2 = false).
    eapply gsep12; eauto.
    destruct (isGlobalBlock ge b3) eqn:isglob; [ | reflexivity].
    assert (meminj_preserves_globals ge (extern_of mu12') /\
            (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu12' b = true)).
      ad_it.
      destruct H0 as [A B].
      apply B in isglob.
      destruct A as [A1 [A2 A3]].

      ad_it.
  - assert (HH:as_inj mu12' b1 = Some (b2', d))
      by (eapply INCR; auto).
    rewrite HH in map1; inversion map1; subst.
    eapply gsep23; eauto.
Qed.
*)
Lemma meminj_preserves_globals_extern_incr_separate {F V:Type} (ge: Genv.t F V) mu nu:
  forall (INC: extern_incr mu nu)
         (PG: meminj_preserves_globals ge (as_inj mu))
         (WDnu: SM_wd nu)
         (GSep: globals_separate ge mu nu),
    meminj_preserves_globals ge (as_inj nu).
Proof. intros. destruct PG as [PGa [PGb PGc]].
       split; intros.
       apply PGa in H. eapply extern_incr_as_inj; eassumption.
       split; intros.
       apply PGb in H. eapply extern_incr_as_inj; eassumption.
       remember (as_inj mu b1) as q; apply eq_sym in Heqq.
       destruct q.
       destruct p.
       rewrite (extern_incr_as_inj _ _ INC WDnu _ _ _ Heqq) in H0.

       inv H0. apply (PGc _ _ _ _ H Heqq).
       specialize (GSep _ _ _ Heqq H0).
       rewrite (find_var_info_isGlobal _ _ _ H) in GSep; discriminate.
Qed.
Lemma meminj_preserves_globals_intern_incr_separate {F V:Type} (ge': Genv.t F V) mu nu:
  forall (INC: intern_incr mu nu)
         (PG: meminj_preserves_globals ge' (as_inj mu))
         (WDnu: SM_wd nu)
         (GSep: globals_separate ge' mu nu),
    meminj_preserves_globals ge' (as_inj nu).
Proof. intros. destruct PG as [PGa [PGb PGc]].
       split; intros.
       apply PGa in H. eapply intern_incr_as_inj; eassumption.
       split; intros.
       apply PGb in H. eapply intern_incr_as_inj; eassumption.
       remember (as_inj mu b1) as q; apply eq_sym in Heqq.
       destruct q.
       destruct p.
       rewrite (intern_incr_as_inj _ _ INC WDnu _ _ _ Heqq) in H0.

       inv H0. apply (PGc _ _ _ _ H Heqq).
       specialize (GSep _ _ _ Heqq H0).
       rewrite (find_var_info_isGlobal _ _ _ H) in GSep; discriminate.
Qed.


Lemma intern_incr_globals_separate
      {F V:Type} (ge: Genv.t F V) mu nu:
  forall (INC: intern_incr mu nu)
         (PG: meminj_preserves_globals ge (as_inj mu))
         (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)
         (WD: SM_wd mu) (WDnu: SM_wd nu),
    globals_separate ge mu nu.
Proof. intros. red; intros.
       remember (isGlobalBlock ge b2) as p; apply eq_sym in Heqp.
       destruct p; simpl; trivial.
       specialize (GF _ Heqp).
       destruct (frgnSrcAx _ WD _ GF) as [? [? [? ?]]].
       assert (EE: extern_of mu = extern_of nu) by eapply INC.
       destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [EXT LOC]]; clear H0.
       rewrite <- EE in EXT.
       rewrite (extern_in_all _ _ _ _ EXT) in H; discriminate.
       destruct (local_DomRng _ WDnu _ _ _ LOC) as [lS lT].
       assert (lT': locBlocksTgt nu b2 = false).
       apply (meminj_preserves_globals_isGlobalBlock _ _ PG) in Heqp.
       rewrite (extern_in_all _ _ _ _ H1) in Heqp; inv Heqp.
       rewrite EE in H1.
       eapply extern_DomRng'; eassumption.
       rewrite lT' in lT; discriminate.
Qed.

Lemma exter_incr_globals_separate
      {F V:Type} (ge: Genv.t F V) mu nu:
  forall (EE: extern_of mu = extern_of nu)
         (PG: meminj_preserves_globals ge (as_inj mu))
         (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)
         (WD: SM_wd mu) (WDnu: SM_wd nu),
    globals_separate ge mu nu.
Proof. intros. red; intros.
       remember (isGlobalBlock ge b1) as p1; apply eq_sym in Heqp1.
       remember (isGlobalBlock ge b2) as p; apply eq_sym in Heqp.
       destruct p; simpl; trivial.
       destruct p1; simpl.
       specialize (GF _ Heqp1).
       destruct (frgnSrcAx _ WD _ GF) as [? [? [? ?]]].
       unfold as_inj, join in H.
       rewrite H1 in H; inversion H.
       (*eapply meminj_preserves_globals_isGlobalBlock in Heqp; eauto.*)

       specialize (GF _ Heqp).
       destruct (frgnSrcAx _ WD _ GF) as [? [? [? ?]]].
       destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [EXT LOC]]; clear H0.
       rewrite <- EE in EXT.
       rewrite (extern_in_all _ _ _ _ EXT) in H. discriminate.
       destruct (local_DomRng _ WDnu _ _ _ LOC) as [lS lT].
       assert (lT': locBlocksTgt nu b2 = false).
       apply (meminj_preserves_globals_isGlobalBlock _ _ PG) in Heqp.
       rewrite (extern_in_all _ _ _ _ H1) in Heqp; inv Heqp.
       rewrite EE in H1.
       eapply extern_DomRng'; eassumption.
       rewrite lT' in lT; discriminate.
Qed.
