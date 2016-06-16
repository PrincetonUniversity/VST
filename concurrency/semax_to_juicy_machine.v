Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.eq_dec.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext_oracle.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.

Set Bullet Behavior "Strict Subproofs".

Ltac eassert :=
  let mp := fresh "mp" in
  pose (mp := fun {goal Q : Type} (x : goal) (y : goal -> Q) => y x);
  eapply mp; clear mp.

(* Instantiation of modules *)
Module ClightSEM <: Semantics.
  Definition G := genv.
  Definition C := corestate.
  Definition Sem := CLN_memsem.
End ClightSEM.

Module JuicyMachineShell_ClightSEM := Concur.JuicyMachineShell ClightSEM.
Module ListScheduler_NatTID := ListScheduler NatTID.
Module JuicyMachine:= CoarseMachine (ListScheduler_NatTID) (JuicyMachineShell_ClightSEM).

Definition join_list := JuicyMachineShell_ClightSEM.join_list.
Definition schedule := ListScheduler_NatTID.schedule.
Definition threads_and_lockpool := JuicyMachine.SIG.ThreadPool.t.
Module Machine := JuicyMachineShell_ClightSEM.ThreadPool.

Definition cm_state := (Mem.mem * genv * (schedule * threads_and_lockpool))%type.

(* Module JTP:=JuicyMachine.SIG.ThreadPool. *)

(* debugging *)
Axiom HOLE : forall {A}, A.
Open Scope string_scope.

Definition islock_pred R r := exists sh sh' z, r = YES sh sh' (LK z) (SomeP ((unit:Type)::nil) (fun _ => R)).

Inductive cohere_res_lock : forall (resv : option (option rmap)) (wetv : resource) (dryv : memval), Prop :=
| cohere_notlock wetv dryv:
    (forall  sh sh' z P, wetv <> YES sh sh' (LK z) P) ->
    cohere_res_lock None wetv dryv
| cohere_locked R wetv :
    islock_pred R wetv ->
    cohere_res_lock (Some None) wetv (Byte (Integers.Byte.zero))
| cohere_unlocked R phi wetv :
    islock_pred R wetv ->
    R phi ->
    cohere_res_lock (Some (Some phi)) wetv (Byte (Integers.Byte.one)).

Definition state_invariant {Z} (Jspec : juicy_ext_spec Z) (n : nat) (state : cm_state) : Prop :=
  match state with
  | (m, ge, (sch, Machine.mk nthds thds phis lockset as sss)) =>
    
    (* joinability condition *)
    (exists phi_all,
        (* JuicyMachineShell_ClightSEM.join_all sss phi_all *)
        (* /\ *)
        
        (* coherence between locks (dry, wet, and lockset) *)
        (forall lock : Address.address,
            cohere_res_lock
              (@addressFiniteMap.AMap.find _ lock lockset)
              (phi_all @ lock)
              (contents_at m lock)))
    /\
    JuicyMachineShell_ClightSEM.mem_compatible sss m
    /\
    
    (* safety of each thread *)
    (forall i pr_i phi jmi (ora : Z),
        (* why is the i implicit?*)
        @Machine.getThreadR i sss pr_i = phi ->
        m_dry jmi = m ->
        m_phi jmi = phi ->
        match @Machine.getThreadC i sss pr_i with
        | Krun q => semax.jsafeN Jspec ge n ora q jmi
        | Kblocked q
        | Kresume q _ => semax.jsafeN Jspec ge n ora q jmi /\ cl_at_external q <> None
        | Kinit _ _ => True
        end)
    /\
    
    (* if one thread is running, it has to be the one being scheduled *)
    (* except if there is only one, then we don't require anything *)
    (lt 1 nthds.(pos.n) -> forall i pr_i q (ora : Z),
        @Machine.getThreadC i sss pr_i = Krun q ->
        exists sch', sch = i :: sch')
  end.

Lemma jsafeN_proof_irrelevance Z OK_spec prog oracle c jm jm' :
  m_dry jm = m_dry jm' ->
  m_phi jm = m_phi jm' ->
  @jsafeN Z OK_spec (globalenv prog) (level jm) oracle c jm ->
  @jsafeN Z OK_spec (globalenv prog) (level jm') oracle c jm'.
Admitted.

Section Initial_State.
  Variables
    (CS : compspecs) (V : varspecs) (G : funspecs)
    (ext_link : string -> ident) (prog : program) 
    (all_safe : semax_prog (Concurrent_Oracular_Espec CS ext_link) prog V G)
    (init_mem_not_none : Genv.init_mem prog <> None).

  Definition Jspec := @OK_spec (Concurrent_Oracular_Espec CS ext_link).
  
  Definition init_m : { m | Genv.init_mem prog = Some m } :=
    match Genv.init_mem prog as y return (y <> None -> {m : mem | y = Some m}) with
    | Some m => fun _ => exist _ m eq_refl
    | None => fun H => (fun Heq => False_rect _ (H Heq)) eq_refl
    end init_mem_not_none.
  
  Definition initial_state (n : nat) (sch : schedule) : cm_state :=
    (proj1_sig init_m,
     globalenv prog,
     (sch,
      let spr := semax_prog_rule
                   (Concurrent_Oracular_Espec CS ext_link) V G prog
                   (proj1_sig init_m) all_safe (proj2_sig init_m) in
      let q : corestate := projT1 (projT2 spr) in
      let jm : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n) in
      Machine.mk
        (pos.mkPos (le_n 1))
        (* (fun _ => Kresume q Vundef) *)
        (fun _ => Krun q)
        (fun _ => m_phi jm)
        (addressFiniteMap.AMap.empty _)
     )
    ).
  
  Lemma initial_invariant n sch : state_invariant Jspec n (initial_state n sch).
  Proof.
    unfold initial_state.
    destruct init_m as [m Hm]; simpl proj1_sig; simpl proj2_sig.
    set (spr := semax_prog_rule (Concurrent_Oracular_Espec CS ext_link) V G prog m all_safe Hm).
    set (q := projT1 (projT2 spr)).
    set (jm := proj1_sig (snd (projT2 (projT2 spr)) n)).
    
    split; [exists (m_phi jm)(* ;split *) | split; [|split]].
    (*
    - (* joining condition *)
      admit.
    (* Questions:
      - why is emp better that "empty_rmap"? it requires "identity", but I thought we had no identity?
      - isn't core the corresponding neutral element? I can't find a lemma about that
     *)
    (* exists (empty_rmap n); split. *)
    (* destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *. *)
    (* unfold join. *)
    (* now admit (* join with empty_rmap -- doable *). *)
    (* now admit. *)
     *)
    
    - (* cohere_res_lock (there are no locks at first) *)
      intros lock.
      rewrite threadPool.find_empty.
      constructor.
      intros.
      unfold jm.
      match goal with |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & notlock) end.
      simpl.
      apply notlock.
    
    - (* mem_compatible *)
      Import JuicyMachineShell_ClightSEM.
      apply JuicyMachineShell_ClightSEM.Build_mem_compatible' with (all_juice := m_phi jm).
      + apply JuicyMachineShell_ClightSEM.AllJuice with (m_phi jm) None.
        * change (proj1_sig (snd (projT2 (projT2 spr)) n)) with jm.
          unfold join_threads.
          Import fintype.
          Import ThreadPool.
          Import pos.
          (* unfold JuicyMachineShell_ClightSEM.getThreadsR. *)
          unfold getThreadsR.
          
          match goal with |- _ ?l _ => replace l with (m_phi jm :: nil) end; swap 1 2.
          {
            simpl.
            generalize (m_phi jm); clear; intros r.
            compute.
            destruct ssrbool.idP as [_|F].
            reflexivity.
            exfalso. auto.
          }
          fold jm.
          simpl.
          exists (core (m_phi jm)).
          {
            split.
            - apply join_comm.
              apply core_unit.
            - apply core_identity.
          }
        
        * reflexivity.
        * constructor.
      + destruct (snd (projT2 (projT2 spr))) as [jm' [D H]]; unfold jm; clear jm; simpl.
        subst m.
        destruct jm' as [m' phi] eqn:E.
        apply Build_mem_cohere'; simpl.
        all:auto.
        unfold access_cohere'.
        now admit (* should be access_cohere instead of this max_access_at *).
      + intros loc sh psh P z L.
        destruct (snd (projT2 (projT2 spr))) as [jm' [D [H [A NL]]]]; unfold jm in *; clear jm; simpl in L |- *.
        specialize (NL loc).
        rewrite L in NL.
        exfalso; eapply NL.
        reflexivity.
      + intros loc sh psh P z L.
        destruct (snd (projT2 (projT2 spr))) as [jm' [D [H [A NL]]]]; unfold jm in *; clear jm; simpl in L |- *.
        specialize (NL loc).
        rewrite L in NL.
        exfalso; eapply NL.
        reflexivity.
    
    - (* safety of the only thread *)
      intros i pr_i phi jmi ora Ephi.
      destruct (Machine.getThreadC pr_i) as [c|c|c v|v1 v2] eqn:Ec; try discriminate.
      intros Edry Ewet.
      destruct i as [ | [ | i ]]. 2: now inversion pr_i. 2:now inversion pr_i.
      simpl in Ephi, Ec.
      destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
      destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl proj1_sig in *; simpl proj2_sig in *.
      subst.
      replace c with q in * by congruence.
      replace (ageable.level jm') with (ageable.level jmi).
      eapply jsafeN_proof_irrelevance; [ | | apply (S ora) ]; auto.
      { destruct jmi eqn:Ei, jm' eqn:E'.
        simpl; simpl in Ewet.
        congruence. }
      
    - (* only one thread running *)
      intros F; exfalso. simpl in F. omega.
  Admitted.

End Initial_State.

Section Simulation.
  Variables
    (CS : compspecs)
    (* (V : varspecs) (G : funspecs) *)
    (ext_link : string -> ident)
    (* (prog : program)  *)
    (* (all_safe : semax_prog (CEspec CS ext_link) prog V G) *)
    (* (init_mem_not_none : Genv.init_mem prog <> None) *)
  .

  Definition Jspec' := (@OK_spec (Concurrent_Oracular_Espec CS ext_link)).
  
  Inductive state_step : cm_state -> cm_state -> Prop :=
  | state_step_empty_sched ge m jstate :
      state_step
        (m, ge, (nil, jstate))
        (m, ge, (nil, jstate))
  | state_step_c ge m m' sch sch' jstate jstate' :
      @JuicyMachine.machine_step ge sch jstate m sch' jstate' m' ->
      state_step
        (m, ge, (sch, jstate))
        (m', ge, (sch', jstate')).
  
  (*
  Inductive state_step : cm_state -> cm_state -> Prop :=
  | state_step_empty_sched ge m jstate :
      state_step
        (m, ge, (nil, jstate))
        (m, ge, (nil, jstate))
  
  | state_step_bad_sched ge m i sch jstate :
      ~ Machine.containsThread jstate i ->
      state_step
        (m, ge, (i :: sch, jstate))
        (m, ge, (i :: sch, jstate))
  
  | state_step_internal
      ge m m' i sch jstate jstate'
      (contains_thread_i : Machine.containsThread jstate i)
      (mem_compat : JuicyMachineShell_ClightSEM.mem_compatible jstate m) :
      @JuicyMachineShell_ClightSEM.juicy_step
        ge i
        jstate m
        contains_thread_i
        mem_compat
        jstate' m' ->
      state_step
        (m, ge, (i :: sch, jstate))
        (m', ge, (i :: sch, jstate'))
  
  | state_step_concurrent
      ge m m' i sch jstate jstate'
      (contains_thread_i : Machine.containsThread jstate i)
      (mem_compat : JuicyMachineShell_ClightSEM.mem_compatible jstate m) :
      @JuicyMachineShell_ClightSEM.syncStep'
        ge i
        jstate m
        contains_thread_i
        mem_compat
        jstate' m' ->
      state_step
        (m, ge, (sch, jstate))
        (m', ge, (i :: sch, jstate'))
  .
   *)  
  
  Require Import veric.semax_ext.
  Require Import msl.Coqlib2.
  
  Import JuicyMachineShell_ClightSEM.
  Import ThreadPool.
  Import Machine.
  
  Lemma getThreadCC
        (i j : tid) (tp : thread_pool)
        (cnti : containsThread tp i) (cntj : containsThread tp j)
        (c' : @ctl code) (cntj' : containsThread (@updThreadC i tp cnti c') j) :
    @getThreadC j (@updThreadC i tp cnti c') cntj' = if eq_dec i j then c' else @getThreadC j tp cntj.
  Proof.
    destruct (eq_dec i j); subst;
      [rewrite gssThreadCC |
       erewrite <- @gsoThreadCC with (cntj := cntj)];
      now eauto.
  Qed.
  
  Lemma state_invariant_step n :
    forall state,
      state_invariant Jspec' (S n) state ->
      exists state',
        state_step state state' /\
        state_invariant Jspec' n state'.
  Proof.
    intros ((m & ge) & sch & sss).
    destruct sss as (nthreads, thds, phis, lset) eqn:Esss.
    intros Invariant.
    assert (I:=Invariant).
    destruct I as ((phi_all & lock_coh) & mem_compat & safe & single).
    rewrite <-Esss in *.
    destruct sch as [ | i sch ].
    
    (* empty schedule: we loop in the same state *)
    {
      exists (m, ge, (nil, sss)); subst; split.
      - constructor.
      - repeat split; eauto.
        intros i pr_i phi jmi ora E_phi di wi.
        specialize (safe i pr_i phi jmi ora E_phi di wi).
        eassert; [ apply safe | ].
        destruct (Machine.getThreadC pr_i) as [c|c|c v|v1 v2] eqn:Ec; auto;
          intros Safe; try split; try eapply safe_downward1, Safe; intuition.
    }
    
    destruct (i < nthreads.(pos.n)) eqn:Ei; swap 1 2.
    
    (* bad schedule *)
    {
      eexists.
      split.
      - constructor.
        apply JuicyMachine.schedfail with i.
        + reflexivity.
        + rewrite Esss.
          unfold JuicyMachineShell_ClightSEM.ThreadPool.containsThread.
          simpl.
          now rewrite Ei; auto.
        + now apply JuicyMachineShell_ClightSEM.True.
        + reflexivity.
      - simpl (ListScheduler_NatTID.schedSkip _).
        subst sss.
        repeat split; eauto.
        intros j pr_j phi jmj ora E_phi di wi.
        eassert.
        + eapply safe; eauto.
        + destruct (Machine.getThreadC pr_j) as [c|c|c v|v1 v2] eqn:Ec; auto;
            intros Safe; try split; try eapply safe_downward1, Safe; intuition.
        + (* invariant about "only one Krun and it is scheduled": the
          bad schedule case is not possible *)
          intros H i0 pri q ora Ec.
          exfalso.
          specialize (single H i0 pri q ora Ec).
          destruct single as [sch' single]; injection single as <- <- .
          hnf in pri.
          simpl in pri.
          congruence.
    }
    
    (* the schedule selected one thread *)
    assert (pr_i : Machine.containsThread sss i).
    { rewrite Esss. apply Ei. }
    remember (Machine.getThreadC pr_i) as c_i eqn:Ec_i; symmetry in Ec_i.
    remember (Machine.getThreadR pr_i) as phi_i eqn:Ephi_i; symmetry in Ephi_i.
    
    destruct c_i as
        [ (* Krun *) c_i
        | (* Kblocked *) c_i
        | (* Kresume *) c_i v
        | (* Kinit *) v1 v2 ].
    
    (* thread[i] is running *)
    {
      assert (Hjmi : exists jmi, m_dry jmi = m /\ m_phi jmi = phi_i).
      { admit (* "slice" lemma for juicy memory *). }
      
      destruct Hjmi as [jm_i [jm_i_m jm_i_phi_i]].
      
      destruct c_i as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* thread[i] is running and some internal step *)
      {
        assert (next: exists c_i' jm_i',
                   corestep (juicy_core_sem cl_core_sem) ge c_i jm_i c_i' jm_i'
                   /\ forall ora, jsafeN Jspec' ge (S n) ora c_i' jm_i').
        {
          admit.
          (* there is this next state (use jsafeN) with trivial oracle *)
          (* the next state is safe for all oracle *)
        }
        
        destruct next as (c_i' & jm_i' & step_i & safe_i').
        pose (m' := m_dry jm_i' (* TODO update cur *)).
        pose (sss' := @Machine.updThread i sss pr_i (Krun c_i') (m_phi jm_i')).
        pose (state' := (m', ge, (i :: sch, sss'))).
        exists state'.
        split.
        - apply state_step_c; [].
          apply JuicyMachine.thread_step with (tid := i) (Htid := pr_i) (Hcmpt := mem_compat); [|]. now reflexivity.
          hnf; [].
          eapply JuicyMachineShell_ClightSEM.step_juicy; eauto; [ | | | ].
          + hnf. now constructor.
          + hnf.
            unfold JuicyMachineShell_ClightSEM.ThreadPool.SEM.Sem in *.
            unfold CLN_memsem in *.
            simpl.
            unfold juicy_core_sem in *.
            simpl in step_i.
            unfold jstep in *.
            (* see with santiago how to prove the juicyRestrict *)
            admit.
          + reflexivity.
          + reflexivity.
        - hnf.
          (*
          apply state_step_internal with (contains_thread_i := pr_i) (mem_compat := mem_compat).
          apply JuicyMachineShell_ClightSEM.step_juicy with (c := c_i) (jm := jm_i) (c' := c_i') (jm' := jm_i').
          + admit (* mem_compat *).
          + admit (* mem coherence *).
          + congruence.
          + apply step_i.
          + reflexivity.
          + reflexivity.
        - split;[|split;[|split]].
          + admit (* get phi_all from the mem_compat, too? *).
          + admit (* mem_compat *).
          + intros i0 pr_i0 q phi jmi ora.
            (* safety for all oracle : use the fact the oracle does
            not change after one step *)
            admit.
          + intros H i0 pr_i0 q ora H0.
            exists sch.
            (* use the fact that there is at most one Krun on the
            previous step and this step did not add any *)
            admit.
           *)
          admit.
      }
      (* end of internal step *)
      
      (* thread[i] is running and about to call an external: Krun (at_ex c) -> Kblocked c *)
      {
        eexists; split.
        - constructor.
          eapply JuicyMachine.suspend_step.
          + reflexivity.
          + reflexivity.
          + assumption.
          + econstructor.
            * eassumption.
            * reflexivity.
            * constructor.
            * reflexivity.
        - repeat split; [ | | | ].
          + subst sss; clear -lock_coh.
            unfold ThreadPool.lset in *.
            exists phi_all.
            now apply lock_coh.
          + unfold mem_compatible in *.
            subst sss.
            unfold ThreadPool.updThreadC in *; simpl.
            inversion mem_compat; [].
            inversion juice_join; [].
            econstructor; [ | | | ]; auto.
            now econstructor; [ | | ]; eauto.
            all: now auto.
          + intros i0 pr_i0 phi jmi ora H H0 H1.
            destruct (eq_dec i i0) as [<-|E].
            * specialize (safe i pr_i phi jmi ora).
              rewrite gssThreadCC.
              rewrite Ec_i in safe.
              split. 2:subst; simpl; congruence.
              apply safe_downward1.
              change (jsafeN Jspec' ge (S n) ora (ExtCall ef sig args lid ve te k) jmi).
              apply safe; auto; []. 
              erewrite <- gThreadCR in H.
              apply H.
            * subst sss. 
              assert (pr_i0' := cntUpdateC' pr_i0).
              specialize (safe i0 pr_i0' phi jmi ora).
              erewrite <- gsoThreadCC with (cntj := pr_i0'). 2:apply E.
              destruct (getThreadC pr_i0'); try split; try apply safe_downward1; try destruct safe as [safe|?]; try apply safe; auto.
              all: erewrite <- gThreadCR; apply H.
          + intros H i0 pr_i0 q ora H0.
            subst sss.
            exfalso.
            (* derive false: thread i0 is in Krun, even though that
            can only be the new Kblock or an old Krun, which would
            have been in conflict with the other, old, Krun *)
            admit.
      } (* end of Krun (at_ex c) -> Kblocked c *)
    } (* end of Krun *)
    
    (* thread[i] is in Kblocked *)
    {
      (* goes to Kresume c_i' according to the rules of syncStep  *)
      
      assert (Hjmi : exists jmi, m_dry jmi = m /\ m_phi jmi = phi_i).
      { admit (* "slice" lemma for juicy memory *). }
      
      destruct Hjmi as [jm_i [jm_i_m jm_i_phi_i]].
      
      destruct c_i as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* internal step: impossible, because in state Kblocked *)
      {
        exfalso.
        pose proof (safe i pr_i phi_i).
        (* we need again the splice theorems *)
        admit.
      }
      (* back to external step *)
      
      (* paragraph below: ef has to be an EF_external *)
      assert (Hef : match ef with EF_external _ _ => Logic.True | _ => False end).
      {
        pose proof (safe i pr_i phi_i jm_i nil ltac:(assumption)) as safe_i.
        rewrite Ec_i in safe_i.
        specialize (safe_i ltac:(assumption) ltac:(assumption)).
        destruct safe_i as [safe_i atext].
        unfold jsafeN, juicy_safety.safeN in safe_i.
        inversion safe_i; subst; [ now inversion H0; inversion H | | now inversion H ].
        inversion H0; subst; [].
        match goal with x : ext_spec_type _ _  |- _ => clear -x end.
        now destruct e eqn:Ee; [ apply I | .. ];
          simpl in x;
          repeat match goal with
                   _ : context [ oi_eq_dec ?x ?y ] |- _ =>
                   destruct (oi_eq_dec x y); try discriminate; try tauto
                 end.
      }
      assert (Ex : exists name sig, ef = EF_external name sig) by (destruct ef; eauto; tauto).
      destruct Ex as (name & sg & ->); clear Hef.
      
      (* paragraph below: ef has to be an EF_external with one of those 5 names *)
      assert (which_primitive :
                Some (ext_link "acquire") = (ef_id ext_link (EF_external name sg)) \/
                Some (ext_link "release") = (ef_id ext_link (EF_external name sg)) \/
                Some (ext_link "makelock") = (ef_id ext_link (EF_external name sg)) \/
                Some (ext_link "freelock") = (ef_id ext_link (EF_external name sg)) \/
                Some (ext_link "spawn") = (ef_id ext_link (EF_external name sg))).
      {
        pose proof (safe i pr_i phi_i jm_i (* oracle=*)nil ltac:(assumption)) as safe_i.
        rewrite Ec_i in safe_i.
        specialize (safe_i ltac:(assumption) ltac:(assumption)).
        unfold jsafeN, juicy_safety.safeN in safe_i.
        destruct safe_i as [safe_i atext].
        inversion safe_i; subst; [ now inversion H0; inversion H | | now inversion H ].
        inversion H0; subst; [].
        match goal with H : ext_spec_type _ _  |- _ => clear -H end.
        simpl in *.
        repeat match goal with
                 _ : context [ oi_eq_dec ?x ?y ] |- _ =>
                 destruct (oi_eq_dec x y); try injection e; auto
               end.
        tauto.
      }
      
      (* Before going any further, one needs to provide the first
        rmap of the oracle.  Unfortunately, for that, we need to know
        whether we're in an "acquire" external call or not. In
        addition, in the case of an "acquire" we need to know the
        arguments of the function (address+mpred) so that we can
        provide the right rmap from the lock set.
        |
        Two solutions: either we use a dummy oracle to know those things (but
        ... we need the oracle before that (FIX the spec OR [A]), or we write
        it as a P\/~P and then we derive a contradiction (not sure we can do
        that). *)
      
      destruct which_primitive as
          [ H_acquire | [ H_release | [ H_makelock | [ H_freelock | H_spawn ] ] ] ].
      
      { (* the case of acquire *)
        eexists.
        split.
        - eapply state_step_c.
          eapply JuicyMachine.sync_step; [ reflexivity | reflexivity | ].
          eapply step_acquire.
          + now auto.
          + eassumption.
          + simpl.
            repeat f_equal; [ | | | ].
            * admit (* TODO: Problem: this LOCK is a parameter of the whole thing. *).
            * admit (* those admits seem to maybe be implied by "all calls are well-formed" (with safety?) *).
            * admit (* those admits seem to maybe be implied by "all calls are well-formed" (with safety?) *).
            * admit (* those admits seem to maybe be implied by "all calls are well-formed" (with safety?) *).
          + eassumption.
          + admit (* precondition? *).
          + admit (* what is this? *).
          + admit (* real stuff: load 1 *).
          + admit (* real stuff: store 0 *).
          + admit (* real stuff: lock is Some *).
          + admit (* real stuff: it joins *).
          + reflexivity.
          + reflexivity.
        - (* invariant is maintainted *)
          admit.
      
      (*
          
          pose proof (safe i pr_i phi_i jm_i (* oracle=*)nil ltac:(assumption)) as safe_i.
          rewrite Ec_i in safe_i.
          specialize (safe_i ltac:(assumption) ltac:(assumption)).
          
          unfold jsafeN, juicy_safety.safeN in safe_i.
          inversion safe_i; [ now inversion H0; inversion H | | now inversion H ].
          subst.
          simpl in H0. injection H0 as <- <- <- .
          hnf in x.
          revert x H1 H2.
          
          simpl (ext_spec_pre _).
          simpl (ext_spec_post _).
          unfold funspecOracle2pre.
          unfold funspecOracle2post.
          unfold ext_spec_pre, ext_spec_post.
          Local Notation "{| 'JE_spec ... |}" := {| JE_spec := _; JE_pre_hered := _; JE_post_hered := _; JE_exit_hered := _ |}.
          destruct (oi_eq_dec (Some (ext_link "acquire")) (ef_id ext_link (EF_external name sg)))
            as [E | E];
            [ | now clear -E H_acquire; simpl in *; congruence ].
          
          Focus 2.
          
          intros (phix, ((((ok, oracle_x), vx), shx), Rx)) Pre. simpl in Pre.
          destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
          simpl (and _).
          intros Pre.
          econstructor.
          
          unfold cl_after_external.
          
          (* relate lset to val *)
          pose proof lset.
          destruct Precond as [A [[B D] C]].
          hnf in B.
          simpl in B.
          hnf in D.
          
          (* build the memory from the machine from scratch.  Do we
          really need the dummy oracle, then? *)
          
          (* ((phi_acq & Heq_ora & R_phi) & REST_OF_HYPS) *)
          admit.
          
          (* First:
                - DONE: integrate the oracle in the semax_conc definitions
                - DONE: sort out this dependent type problem
                Then hopefully we will be able to exploit the jsafeN_.
                
                Then, the proof should go as follows (it is not clear
                yet whether this happens now or if we set up things in
                the invariant /now/ and we deal with that in the
                Krunnable/Kblocked):
                
                - acquire (locked): nothing will happen (probably
                  happens after)
                
                - acquire (unlocked): the invariant guarantees that the
                  rmap in the lockset satisfies the invariant.  We can
                  give this rmap as a first step to the oracle.  We
                  again have to recover the fact that all oracles after
                  this step will be fine as well.  (Let's write
                  simulation lemmas about this, probably)
                 
                - release: this time, the jsafeN_ will explain how to
                  split the current rmap.
           *)
          admit.
           *)
        }
        
        { (* the case of release *) admit. }
        
        { (* the case of makelock *) admit. }
        
        { (* the case of freelock *) admit. }
        
        { (* the case of spawn *) admit. }
    }
    (* end of Kblocked *)
    
    (* thread[i] is in Kresume *)
    {
      (* goes to Krun c_i' according with after_ex c_i = c_i'  *)
      admit.
    }
    (* end of Kresume *)
    
    (* thread[i] is in Kinit *)
    {
      admit.
    }
    (* end of Kinit *)
  Admitted.
  
(* old pieces of proofs 
  
      set (phis := (map snd thd ++ filter_option_list (map snd (map snd res)))%list).
      destruct (jm_slice phis i phi jm Hj) as (jmi & phi_jmi & dry_jmi).
      { apply nth_error_app_Some.
        rewrite list_map_nth, Heqthd_i.
        reflexivity. }
      assert (X: exists c' jmi', corestep (juicy_core_sem cl_core_sem) env (State ve te k) jmi c' jmi'). {
        specialize (safe _ _ _ tt Heqthd_i).
        inversion safe; subst.
        - (* we should state safety of each thread in this jmi, hence
        write the relationship between jm/jmi/phis/phi should have a
        external definition *)
          
          replace jmi with 
          - inversion H0.
        - inversion H.
      }
      destruct X as (c' & jm' & step & decay & lev).
      
      (* todo: make thd' the aged version of all rmaps *)
      pose (thd' := map (fun x : _ * rmap => let (c, phi) := x in (c, age1 phi)) thd).
      pose (res' := map (fun x : _ * (_ * option rmap) => match x with (a, (R, phi)) => (a, R, option_map age1 phi) end) res).


      (* ah, to build phi' we need to project m_phi jm' on phi -- where
    is the piece of information that says "an action from c is an
    action at phi" ?  ...............*)
      
      (* building the jm2 out of the jm and phi2 : state a lemma *)
      
      (* oracle : first, replace sig with ex.  Then, either define
    another definition of jsafe or use a dummy oracle and then say (∀Ω
    safe(Ω,c,m)) ∧ (c,m→c',m') → (∀Ω safe(Ω,c',m')) *)
      
      (* also MAX is for compcert to know we're not messing with e.g.
    constant propagation, and CUR is for the caller to know compcert
    is not writing in temporarily read-only variables sometimes *)
      
      (* todo the differences between interaction semantics and trace
    semantics *)
      
      (* build new state *)
      pose (thd'' := update_nth i (c', m_phi jm') thd').
      
      exists (build_cm env jm' res thd''), (i :: sch).
      split.
      - (* find jm, jmi, ..., then use safety to get one step from jsafe *)
      (* apply cm_step_internal with c c'.
      inversion step.
      + rewrite Heqthd_i, Heqc.
        inversion H.
        Require Import semax_congruence.
        unfold jsafeN, juicy_safety.safeN in Hsafe.
        pose proof (proj1 (safeN_step_jsem_spec _ _ _ _ _ _ _ _) Hsafe).
        apply (proj1 (safeN_step_jsem_spec _ _ _ _ _ _ _ _)) in Hsafe.
       destruct k as [ | [ s | s1 s2 | s1 s2 | | ret f e' te' ] ks].
       *)

(*    
Lemma safeN_step_jsem_spec: forall gx vx tx n k jm,
        (forall ora,
            @safeN_
              _ _ _ _ (fun x => Genv.genv_symb (genv_genv x)) juicy_safety.Hrel
              (juicy_core_sem cl_core_sem) OK_spec
              gx (S n) ora (State vx tx k) jm) ->
        exists c' m', (cl_step gx (State vx tx k) (m_dry jm) c' (m_dry m') /\
                  resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi m') /\
                  level jm = S (level m') /\
                  forall ora,
                    @safeN_
                      _ _ _ _ (fun x => Genv.genv_symb (genv_genv x)) juicy_safety.Hrel
                      (juicy_core_sem cl_core_sem) OK_spec gx n ora c' m').
 *)
Admitted.
*)
End Simulation.