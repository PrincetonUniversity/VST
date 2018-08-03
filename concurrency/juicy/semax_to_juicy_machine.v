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
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
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
(*Require Import VST.concurrency.cl_step_lemmas.
Require Import VST.concurrency.resource_decay_lemmas.
Require Import VST.concurrency.resource_decay_join.*)
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_safety_makelock.
Require Import VST.concurrency.juicy.semax_safety_spawn.
Require Import VST.concurrency.juicy.semax_safety_release.
Require Import VST.concurrency.juicy.semax_safety_freelock.
Require Import VST.concurrency.juicy.semax_preservation.
Require Import VST.concurrency.juicy.semax_simlemmas.

Set Bullet Behavior "Strict Subproofs".

Section juicy.

Existing Instance JuicyMachineShell.
Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

Context (ge : genv).

Inductive jmsafe : nat -> cm_state -> Prop :=
| jmsafe_0 m tr sch tp : jmsafe 0 (m, (tr, sch, tp))
| jmsafe_halted n m tr tp : jmsafe n (m, (tr, nil, tp))
| jmsafe_core n m m' tr tr' sch (tp tp' : jstate ge):
    JuicyMachine.machine_step(Sem := JSem) sch tr tp m sch tr' tp' m' ->
    tp_bupd (fun tp' => jmsafe n (m', (tr', sch, tp'))) tp' ->
    jmsafe (S n) (m, (tr, sch, tp))
| jmsafe_sch n m m' i tr tr' sch (tp tp' : jstate ge):
    JuicyMachine.machine_step(Sem := JSem) (i :: sch) tr tp m sch tr' tp' m' ->
    (forall sch', tp_bupd (fun tp' => jmsafe n (m', (tr', sch', tp'))) tp') ->
    jmsafe (S n) (m, (tr, i :: sch, tp)).

Lemma step_sch_irr i tr tr' sch sch' (tp : jstate ge) m tp' m' :
  JuicyMachine.machine_step(Sem := JSem) (i :: sch) tr tp m sch tr' tp' m' ->
  JuicyMachine.machine_step(Sem := JSem) (i :: sch') tr tp m sch' tr' tp' m'.
Proof.
  intros step.
  assert (i :: sch <> sch) by (clear; induction sch; congruence).
  inversion step; try solve [exfalso; eauto].
  - now eapply JuicyMachine.suspend_step; eauto.
  - now eapply JuicyMachine.sync_step; eauto.
(*  - now eapply JuicyMachine.halted_step; eauto.*)
  - now eapply JuicyMachine.schedfail; eauto.
Qed.

Lemma schstep_norun i sch tr tr' tp m tp' m' :
  JuicyMachine.machine_step(Sem := JSem) (i :: sch) tr tp m sch tr' tp' m' ->
  unique_Krun tp (i :: sch) ->
  (1 < pos.n (num_threads tp'))%nat ->
  no_Krun(ge := ge) tp'.
Proof.
  intros step uniq more.
  assert (i :: sch <> sch) by (clear; induction sch; congruence).
  assert (D: (forall i j, containsThread tp i -> containsThread tp j -> i <> j -> 1 < pos.n tp.(num_threads))%nat).
  { clear. intros; eapply (different_threads_means_several_threads i j); eauto. }
  assert (forall j cntj q, containsThread tp i -> i <> j -> @getThreadC _ _ _ j tp cntj <> @Krun _ q).
  { intros j cntj q cnti ne E. autospec uniq. specialize (uniq j cntj q E). breakhyps. }

  inversion step; try tauto.
  all: try inversion Htstep; repeat match goal with H : ?x = ?y |- _ => subst x || subst y end.
  all: intros j cnti q.
  all: assert (tid = i) by (simpl in *; congruence); subst tid.
  all: destruct (eq_dec i j).
  all: try subst j.

  all: try (assert (cnti = Htid) by apply proof_irr; subst Htid).
  all: try (assert (ctn = cnti) by apply proof_irr; subst cnt).

  all: try (unshelve erewrite <-gtc_age; eauto).
  all: try (unshelve erewrite gLockSetCode; eauto).
  all: try (unshelve erewrite gRemLockSetCode; eauto).
  all: try (rewrite gssThreadCode; congruence).
  all: try (rewrite gssThreadCC; congruence).
  all: try (unshelve erewrite gsoThreadCode; eauto).
  all: try (unshelve erewrite <-gsoThreadCC; eauto).

  pose proof cnti as cnti_.
  apply cnt_age in cnti_.
  destruct (@cntAdd' _ _ _ _ _ _ _ _ cnti_) as [(cnti', ne) | Ei].
  unshelve erewrite gsoAddCode; eauto.
  rewrite gssThreadCode; congruence.
  rewrite gssAddCode. congruence. apply Ei.

  pose proof cnti as cnti_.
  apply cnt_age in cnti_.
  destruct (@cntAdd' _ _ _ _ _ _ _ _ cnti_) as [(cnti', ne) | Ei].
  unshelve erewrite gsoAddCode; eauto.
  unshelve erewrite gsoThreadCode; eauto.
  rewrite gssAddCode. congruence. apply Ei.

  all: try congruence.
  all: eauto.

(*  inversion Hhalted.
  inversion Hcant.*)

  intros E.
  hnf in uniq.
  autospec uniq.
  specialize (uniq j cnti q E). breakhyps.
Qed.

End juicy.

(*+ Final instantiation *)

Record CSL_proof := {
  CSL_prog : Clight.program;
  CSL_CS: compspecs;
  CSL_V : varspecs; 
  CSL_G : funspecs;
  CSL_ext_link : string -> ident;
  CSL_ext_link_inj : forall s1 s2, CSL_ext_link s1 = CSL_ext_link s2 -> s1 = s2;
  CSL_all_safe : semax_prog.semax_prog (Concurrent_Espec unit CSL_CS CSL_ext_link)
                             CSL_prog CSL_V CSL_G;
  CSL_init_mem_not_none : Genv.init_mem CSL_prog <> None;
}.

Section Safety.
  Variable CPROOF: CSL_proof.
  Definition CS :=   CPROOF.(CSL_CS).
  Definition V :=   CPROOF.(CSL_V).
  Definition G :=   CPROOF.(CSL_G).
  Definition ext_link :=   CPROOF.(CSL_ext_link).
  Definition ext_link_inj :=   CPROOF.(CSL_ext_link_inj).
  Definition prog :=   CPROOF.(CSL_prog).
  Definition all_safe :=   CPROOF.(CSL_all_safe).
  Definition init_mem_not_none :=   CPROOF.(CSL_init_mem_not_none).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).

  (* another, looser invariant to have more standard preservation
  statement *)
  Definition inv Gamma n state :=
    exists m, (n <= m)%nat /\ state_invariant(ge := globalenv prog) Jspec' Gamma m state.

  Lemma inv_sch_irr Gamma n m i tr sch sch' tp :
    inv Gamma n (m, (tr, i :: sch, tp)) ->
    inv Gamma n (m, (tr, i :: sch', tp)).
  Proof.
    intros (k & lkm & Hk).
    exists k; split; auto.
    eapply state_invariant_sch_irr, Hk.
  Qed.

  Lemma no_Krun_inv Gamma n m tr sch sch' tp :
    (1 < pos.n (num_threads tp) -> no_Krun tp)%nat ->
    inv Gamma n (m, (tr, sch, tp)) ->
    inv Gamma n (m, (tr, sch', tp)).
  Proof.
    intros nokrun.
    intros (x & lx & i).
    exists x; split; auto.
    inversion i as [m0 ge0 sch0 tp0 PHI mcompat lev gamma lock_sparse lock_coh safety wellformed uniqkrun H0]; subst.
    esplit; eauto.
    intros H. autospec nokrun. revert H.
    apply no_Krun_unique_Krun, nokrun.
  Qed.

  Lemma blocked_at_external_dec state ef : {blocked_at_external state ef} + {~blocked_at_external(ge := globalenv prog) state ef}.
  Proof.
    Local Ltac t := solve [right; intros []; intros; breakhyps].
    Ltac t' i cnti :=
      right; intros [i']; intros [cnti']; intros ?; breakhyps;
      try (assert (i' = i) by congruence; subst i');
      try (assert (cnti' = cnti) by apply proof_irr; subst cnti');
      breakhyps.

    destruct state as (m & [tr [ | i sch]] & tp). now t.
    destruct (containsThread_dec i tp) as [cnti | ncnti]. 2: now t.
    destruct (@getThreadC _ _ _ i tp cnti) as [c | c | c v | v v0] eqn:Ei;
    try solve [right; intros [i' [cnti' [sch' [c0 [? [H [? ?]]]]]]]; inv H; proof_irr; congruence].
    destruct (cl_at_external c) as [(ef', args) | ] eqn:Eo;
    try solve [right; intros [i' [cnti' [sch' [c0 [? [H [? ?]]]]]]]; inv H; proof_irr; congruence].
    destruct (eq_dec ef ef'); try subst ef';
    try solve [right; intros [i' [cnti' [sch' [c0 [? [H [? ?]]]]]]]; inv H; proof_irr; congruence].
    (* destruct (EqDec_external_function ef ef'). subst ef'. 2: now t' i cnti. *)
    now left; repeat eexists; eauto.
  Qed.

  Lemma safety_bupd : forall state n Gamma, (exists state', state_step state state' /\
    (state_invariant Jspec' Gamma n state' \/ state_invariant Jspec' Gamma (S n) state')) ->
    exists state',
      state_step(ge := globalenv prog) state state' /\
      (state_bupd (state_invariant Jspec' Gamma n) state' \/
       state_bupd (state_invariant Jspec' Gamma (S n)) state').
  Proof.
    intros ??? (? & ? & H).
    eexists; split; eauto.
    destruct H; [left | right]; apply state_bupd_intro'; auto.
  Qed.

  Theorem safety_induction Gamma n state :
    state_invariant Jspec' Gamma (S n) state ->
    exists state',
      state_step(ge := globalenv prog) state state' /\
      (state_bupd (state_invariant Jspec' Gamma n) state' \/
       state_bupd (state_invariant Jspec' Gamma (S n)) state').
  Proof.
    intros inv.

    (* the case for makelock *)
    destruct (blocked_at_external_dec state MKLOCK) as [ismakelock|isnotmakelock].
    {
      apply safety_bupd, safety_induction_makelock; eauto.
      - apply ext_link_inj.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    (* the case for freelock *)
    destruct (blocked_at_external_dec state FREE_LOCK) as [isfreelock|isnotfreelock].
    {
      apply safety_bupd, safety_induction_freelock; eauto.
      - apply ext_link_inj.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    (* the case for spawn *)
    destruct (blocked_at_external_dec state CREATE) as [isspawn|isnotspawn].
    {
      apply safety_bupd, safety_induction_spawn; eauto.
      - apply ext_link_inj.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    (* the case for release *)
    destruct (blocked_at_external_dec state UNLOCK) as [isrelease|isnotrelease].
    {
      apply safety_bupd, safety_induction_release; eauto.
      - apply ext_link_inj.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    destruct (progress CS ext_link ext_link_inj _ _ _ _ isnotspawn inv) as (state', step).
    exists state'; split; [ now apply step | ].
    eapply preservation; eauto.
    apply ext_link_inj.
  Qed.

  Lemma tp_bupd_mono : forall (P Q : jstate (globalenv prog) -> Prop) tp,
    (forall phi tp' phi', tp_update tp phi tp' phi' ->
       P tp' -> Q tp') ->
    tp_bupd P tp -> tp_bupd Q tp.
  Proof.
    intros ???? HP.
    destruct HP as [? HP]; split; auto.
    intros ? Hj ? HC J.
    specialize (HP _ Hj _ HC J) as (? & ? & ? & ? & ? & ? & ?); eauto 8.
  Qed.

  Lemma inv_step Gamma n state :
    inv Gamma (S n) state ->
    exists state',
      state_step state state' /\
      state_bupd (inv Gamma n) state'.
  Proof.
    intros (m & lm & i).
    replace m with (S (m - 1)) in i by omega.
    destruct (safety_induction _ _ _ i) as (state' & step & inv').
    exists state'; split; [ now apply step | ].
    destruct inv'.
    - destruct state' as ([] & [] & ?); eapply tp_bupd_mono; eauto.
      intros; exists (m - 1)%nat. split. omega. assumption.
    - destruct state' as ([] & [] & ?); eapply tp_bupd_mono; eauto.
      intros ???? Hinv; exists m. split. omega. simpl in *. exact_eq Hinv; f_equal. omega.
  Qed.

  Lemma num_tp_update : forall tp tp' phi phi', tp_update(ge := globalenv prog) tp phi tp' phi' ->
    num_threads tp' = num_threads tp.
  Proof.
    intros; apply contains_iff_num, H.
  Qed.

  Lemma no_Krun_stable_update tp tp' phi phi' : no_Krun tp -> tp_update tp phi tp' phi' ->
    no_Krun(ge := globalenv prog) tp'.
  Proof.
    intros notkrun (_ & _ & _ & Hiff & H & _) ????.
    assert (containsThread tp i) as cnt by (apply Hiff; auto).
    specialize (H _ cnt) as (H & _).
    replace (proj2 (Hiff i) cnt) with cnti in H by apply proof_irr.
    rewrite <- H in *; eapply notkrun; eauto.
  Qed.

  Lemma invariant_safe Gamma n state :
    inv Gamma n state -> jmsafe (globalenv prog) n state.
  Proof.
    intros INV.
    pose proof (inv_step) as Step.
    revert state INV.
    induction n; intros (m, ((tr, sch), tp)) INV.
    - apply jmsafe_0.
    - destruct sch.
      + apply jmsafe_halted.
      + destruct (Step _ _ _ INV) as (state' & step & INV').
        inversion step as [ | m0 m' tr' tr'' sch' sch'' tp0 tp' jmstep ]; subst; simpl in *.
        inversion jmstep; subst.
        all: try solve [ eapply jmsafe_core; eauto; eapply tp_bupd_mono; eauto; auto ].
        all: eapply jmsafe_sch; eauto.
        all: intros sch'; eapply tp_bupd_mono; eauto.
        all: intros; apply IHn.
        all: simpl in *.
        all: apply no_Krun_inv with (sch := sch); eauto.
        all: rewrite (num_tp_update _ _ _ _ H); intro; eapply no_Krun_stable_update; eauto; eapply schstep_norun; eauto.
        all: destruct INV as (? & lm & INV).
        all: inv INV; auto.
  Qed.

  Definition init_mem : { m | Genv.init_mem prog = Some m } := init_m prog init_mem_not_none.

  Definition spr :=
    semax_prog_rule'
      (Concurrent_Espec unit CS ext_link) V G prog
      (proj1_sig init_mem) 0 all_safe (proj2_sig init_mem).

  Definition initial_corestate : corestate := projT1 (projT2 spr).

  Definition initial_jm (n : nat) : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n tt).

  Definition initial_machine_state (n : nat) :=
    @OrdinalPool.mk LocksAndResources (@JSem (globalenv prog))
      (pos.mkPos (le_n 1))
      (fun _ => Krun initial_corestate)
      (fun _ => m_phi (initial_jm n))
      (addressFiniteMap.AMap.empty _).

  Definition NoExternal_Espec : external_specification mem external_function unit :=
    Build_external_specification
      _ _ _
      (* no external calls from the machine *)
      (fun _ => False)
      (fun _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ _ _ _ => False)
      (* when the machine is halted, it means no more schedule, there
      is nothing to check: *)
      (fun _ _ _ => Logic.True).

  Definition NoExternal_Hrel : nat -> mem -> mem -> Prop := fun _ _ _ => False.

(*  (* We state the theorem in terms of [safeN_] but because there are
  no external, this really just says that the initial state is
  "angelically safe" : for every schedule and every fuel n, there is a
  path either ending on an empty schedule or consuming all the
  fuel. *)

  Theorem safe_initial_state : forall sch r n genv_symb,
      safeN_
        (G := genv)
        (C := schedule * list _ * ThreadPool.t)
        (M := mem)
        (Z := unit)
        (genv_symb := genv_symb)
        (Hrel := NoExternal_Hrel)
        (JuicyMachine.MachineSemantics sch r)
        NoExternal_Espec
        (globalenv prog)
        n
        tt
        (sch, nil, initial_machine_state n)
        (proj1_sig init_mem).
  Proof.
    intros sch r n thisfunction.
    pose proof initial_invariant CS V G ext_link prog as INIT.
    specialize (INIT all_safe init_mem_not_none n sch).
    match type of INIT with
      _ _ ?a n ?b =>
      assert (init : inv a n b) by (hnf; eauto)
    end.
    pose proof inv_step as SIM.
    clear INIT; revert init.
    unfold initial_state, initial_machine_state.
    unfold initial_corestate, initial_jm, spr, init_mem.
    match goal with |- context[(sch, nil, ?tp)] => set (t0:= tp) end.
    match goal with |- context[(sch, ?tp)] => change tp with t0 end.
    clearbody t0. revert t0.
    match goal with |- context[(proj1_sig ?m)] => generalize (proj1_sig m) end.

    (* here we decorrelate the CoreSemantics parameters from the
    initial state parameters *)
    generalize sch at 2.
    generalize (globalenv prog), sch.
    clear -SIM.
    induction n; intros g sch schSEM m t INV; [ now constructor | ].
    destruct (SIM _ _ _ INV) as [cm' [step INV']].
    inversion step as [ | ? ? m' ? sch' ? tp' STEP ]; subst; clear step.
    - (* empty schedule *)
      eapply safeN_halted.
      + reflexivity.
      + apply I.
    - (* a step can be taken *)
      eapply safeN_step with (c' := (sch', nil, tp')) (m'0 := m').
      + eapply STEP.
      + apply IHn.
        apply INV'.
  Qed.*)

  (* The following is a slightly stronger result, proving [jmsafe]
  i.e. a safety that universally quantifies over all schedule each
  time a part of the schedule is consumed *)

  Theorem jmsafe_initial_state sch n :
    jmsafe (globalenv prog) n ((proj1_sig init_mem), (nil, sch, initial_machine_state n)).
  Proof.
    eapply invariant_safe.
    exists n; split; auto. apply initial_invariant.
  Qed.

(*  Goal Smallstep.initial_state (semantics2 prog) (initial_corestate).*)
  Lemma initial_corestate_initial :
    exists b, Genv.find_symbol (globalenv prog) (prog_main prog) = Some b /\
    exists m', forall n,
    initial_core (Clight_new.cl_core_sem (globalenv prog)) n (proj1_sig init_mem)
      initial_corestate m' (Vptr b Ptrofs.zero) nil.
  Proof.
    unfold initial_corestate.
    destruct spr as (b & ? & [? Hinit] & s).
    destruct (s O tt) as (jm & ? & _).
    exists b; split; auto; simpl in *; clear s.
    specialize (Hinit _ H) as (? & Hinit); hnf in Hinit.
    destruct Hinit as [_ Hinit]; simpl in Hinit.
    destruct Hinit as (? & ? & ?); eexists; repeat split; auto; constructor.
  Qed.

  Lemma jmsafe_csafe n m tr sch s : jmsafe (globalenv prog) n (m, (tr, sch, s)) -> jm_csafe (sch, tr, s) m n.
  Proof.
    clear.
    revert m tr sch s; induction n; intros m tr sch s SAFE.
    now constructor 1.
    inversion SAFE; subst.
    - constructor 2. reflexivity.
    - econstructor 3; [apply H2|].
      eapply tp_bupd_mono; eauto; auto.
    - econstructor 4; [apply H2|].
      intro U''; eapply tp_bupd_mono; eauto; intros.
      apply IHn, H0.
  Qed.

  (* [jmsafe] is an intermediate result, we can probably prove [csafe]
  directly *)

  Theorem safety_initial_state (sch : schedule) (n : nat) :
    jm_csafe (sch, nil, initial_machine_state n) (proj1_sig init_mem) n.
  Proof.
    apply jmsafe_csafe, jmsafe_initial_state.
  Qed.

End Safety.
