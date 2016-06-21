Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
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
Require Import veric.semax_ext.
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

(* debugging *)
Axiom HOLE : forall {A}, A.
Open Scope string_scope.

(*! Instantiation of modules *)
Module ClightSEM <: Semantics.
  Definition G := genv.
  Definition C := corestate.
  Definition Sem := CLN_memsem.
End ClightSEM.

Module JuicyMachineShell_ClightSEM := Concur.JuicyMachineShell ClightSEM.
Module ListScheduler_NatTID := ListScheduler NatTID.
Module JuicyMachine:= CoarseMachine (ListScheduler_NatTID) (JuicyMachineShell_ClightSEM).

(* Definition join_list := JuicyMachineShell_ClightSEM.join_list. *)
Definition schedule := ListScheduler_NatTID.schedule.
Definition threads_and_lockpool := JuicyMachine.SIG.ThreadPool.t.
Module Machine := JuicyMachineShell_ClightSEM.ThreadPool.
Module JM := JuicyMachineShell_ClightSEM.

(*+ Description of the invariant *)

Definition cm_state := (Mem.mem * Clight.genv * (schedule * Machine.t))%type.

(*! Coherence between locks in dry/wet memories and lock pool *)

Definition islock_pred R r := exists sh sh' z, r = YES sh sh' (LK z) (SomeP ((unit:Type)::nil) (fun _ => R)).

Lemma islock_pred_join_sub {r1 r2 R} : join_sub r1 r2 -> islock_pred R r1  -> islock_pred R r2.
Proof.
  intros [r0 J] [x [sh' [z ->]]].
  inversion J; subst; eexists; eauto.
Qed.

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

Definition lock_coherence lset (phi : rmap) (m : mem) :=
  forall lock : Address.address,
    cohere_res_lock
      (@addressFiniteMap.AMap.find _ lock lset)
      (phi @ lock)
      (contents_at m lock).

(*! Joinability and coherence *)

Record mem_compatible_rmap (tp : JM.ThreadPool.t) (m : mem) (all_juice : rmap) : Prop :=
  Build_mem_compatible_rmap
  { juice_join : JM.join_all tp all_juice;
    all_cohere : JM.mem_cohere' m all_juice;
    loc_writable : JM.locks_writable all_juice;
    loc_set_ok : JM.locks_correct (JM.ThreadPool.lockGuts tp) all_juice }.

Lemma mem_compatible_forget {tp m phi} :
  mem_compatible_rmap tp m phi -> JM.mem_compatible tp m.
Proof. intros []; intros. hnf. econstructor; eauto. Qed.

Definition jm_
  {tp m PHI i}
  (cnti : Machine.containsThread tp i)
  (mcompat : mem_compatible_rmap tp m PHI)
  : juicy_mem :=
  JM.personal_mem cnti (mem_compatible_forget mcompat).

Lemma personal_mem_ext
  tp tp' m
  (compat : JM.mem_compatible tp m)
  (compat' : JM.mem_compatible tp' m)
  (same_threads_rmaps: forall i cnti cnti',
      @Machine.getThreadR i tp cnti =
      @Machine.getThreadR i tp' cnti')
  i
  (cnti : Machine.containsThread tp i)
  (cnti' : Machine.containsThread tp' i) :
    JM.personal_mem cnti compat = JM.personal_mem cnti' compat'.
Proof.
  unfold jm_ in *.
  unfold JM.personal_mem in *; simpl. 
  apply juicy_mem_ext.
  - unfold JM.juicyRestrict in *; simpl.
    apply permissions.restrPermMap_ext.
    intros b; repeat f_equal; auto.
  - unfold JM.personal_mem in *. simpl. auto.
Qed.

(*
(*! Safety of each thread *)

Definition threads_safety {Z} (Jspec : juicy_ext_spec Z) ge (tp : JM.ThreadPool.t) (m : mem) (all_juice : rmap) n := 
  forall i cnti phi jmi (ora : Z),
    @Machine.getThreadR i tp cnti = phi ->
    m_dry jmi = m ->
    m_phi jmi = phi ->
    match @Machine.getThreadC i tp cnti with
    | Krun q => semax.jsafeN Jspec ge n ora q jmi
    | Kblocked q
    | Kresume q _ => semax.jsafeN Jspec ge n ora q jmi /\ cl_at_external q <> None
    | Kinit _ _ => Logic.True
    end.
*)
(*! Invariant (= above properties + safety + uniqueness of Krun) *)

Inductive state_invariant {Z} (Jspec : juicy_ext_spec Z) (n : nat) : cm_state -> Prop :=
  | state_invariant_c
      (m : mem) (ge : genv) (sch : schedule) (tp : Machine.t) (PHI : rmap)
      (mcompat : mem_compatible_rmap tp m PHI)
      (lock_coh : lock_coherence tp.(Machine.lset) PHI m)
      (safety :
         forall i (cnti : Machine.containsThread tp i) (ora : Z),
           match Machine.getThreadC cnti with
           | Krun q
           | Kblocked q
           | Kresume q _ => semax.jsafeN Jspec ge n ora q (jm_ cnti mcompat)
           | Kinit _ _ => Logic.True
           end
      )
      (wellformed :
         forall i (cnti : Machine.containsThread tp i),
           match Machine.getThreadC cnti with
           | Krun q => Logic.True
           | Kblocked q => cl_at_external q <> None
           | Kresume q v => cl_at_external q <> None /\ v = Vundef
           | Kinit _ _ => Logic.True
           end
      )
      (uniqueness_Krun :
         (lt 1 tp.(Machine.num_threads).(pos.n) -> forall i cnti q (ora : Z),
             @Machine.getThreadC i tp cnti = Krun q ->
             exists sch', sch = i :: sch'))
    :
      state_invariant Jspec n (m, ge, (sch, tp)).

(*! Initial machine *)

Section Initial_State.
  Variables
    (CS : compspecs) (V : varspecs) (G : funspecs)
    (ext_link : string -> ident) (prog : program)
    (all_safe : semax_prog.semax_prog (Concurrent_Oracular_Espec CS ext_link) prog V G)
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
  
  Lemma personal_mem_of_same_jm tp jm (mc : JM.mem_compatible tp (m_dry jm)) i (cnti : Machine.containsThread tp i) :
    (Machine.getThreadR cnti = m_phi jm) ->
    m_dry (JM.personal_mem cnti mc) = m_dry jm.
  Proof.
  Admitted.
  
  Lemma initial_invariant n sch : state_invariant Jspec n (initial_state n sch).
  Proof.
    unfold initial_state.
    destruct init_m as [m Hm]; simpl proj1_sig; simpl proj2_sig.
    set (spr := semax_prog_rule (Concurrent_Oracular_Espec CS ext_link) V G prog m all_safe Hm).
    set (q := projT1 (projT2 spr)).
    set (jm := proj1_sig (snd (projT2 (projT2 spr)) n)).
    match goal with |- _ _ _ (_, (_, ?TP)) => set (tp := TP) end.
    
    (*! compatibility of memories *)
    assert (compat : mem_compatible_rmap tp m (m_phi jm)).
    {
      apply Build_mem_compatible_rmap.
      + apply JM.AllJuice with (m_phi jm) None.
        * change (proj1_sig (snd (projT2 (projT2 spr)) n)) with jm.
          unfold JM.join_threads.
          unfold JM.getThreadsR.
          
          match goal with |- _ ?l _ => replace l with (m_phi jm :: nil) end; swap 1 2. {
            simpl.
            set (a := m_phi jm).
            match goal with |- context [m_phi ?jm] => set (b := m_phi jm) end.
            replace b with a by reflexivity. clear. clearbody a.
            unfold fintype.ord_enum, eqtype.insub, seq.iota in *.
            simpl.
            destruct ssrbool.idP as [F|F]. reflexivity. exfalso. auto.
          }
          exists (core (m_phi jm)). {
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
        apply JM.Build_mem_cohere'; simpl.
        all:auto.
        simpl in tp.
        unfold JM.access_cohere'.
        now admit (* should be access_cohere instead of this max_access_at *).
      + intros loc sh psh P z L.
        destruct (snd (projT2 (projT2 spr))) as [jm' [D [H [A NL]]]]; unfold jm in *; clear jm; simpl in L |- *.
        pose proof (NL loc) as NL'.
        rewrite L in NL'.
        exfalso; eapply NL'.
        reflexivity.
      + intros loc sh psh P z L.
        destruct (snd (projT2 (projT2 spr))) as [jm' [D [H [A NL]]]]; unfold jm in *; clear jm; simpl in L |- *.
        pose proof (NL loc) as NL'.
        rewrite L in NL'.
        exfalso; eapply NL'.
        reflexivity.
    } (* end of mcompat *)

    apply state_invariant_c with (PHI := m_phi jm) (mcompat := compat).
    
    - (*! lock coherence (no locks at first) *)
      intros lock.
      rewrite threadPool.find_empty.
      constructor.
      intros.
      unfold jm.
      match goal with |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & nolock) end.
      simpl.
      apply nolock.
    
    - (*! safety of the only thread *)
      intros i cnti ora.
      destruct (Machine.getThreadC cnti) as [c|c|c v|v1 v2] eqn:Ec; try discriminate; [].
      destruct i as [ | [ | i ]]. 2: now inversion cnti. 2:now inversion cnti.
      (* the initial juicy has got to be the same as the one given in initial_mem *)
      assert (Ejm: jm = jm_ cnti compat).
      {
        apply juicy_mem_ext; swap 1 2.
        - reflexivity.
        - unfold jm_.
          symmetry.
          admit.
          (* apply personal_mem_of_same_jm. *)
          (* rewrite personal_mem_unique_dry; [ | now auto]. *)
          (* unfold jm. *)
          (* destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *. *)
          (* destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl projT1 in *; simpl projT2 in *. *)
          (* now auto. *)
      }
      subst jm. rewrite <-Ejm.
      simpl in Ec. replace c with q in * by congruence.
      destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
      destruct (JS n) as (jm' & jmm & lev & Safe & notlock); simpl projT1 in *; simpl projT2 in *.
      subst q.
      simpl proj1_sig in *; simpl proj2_sig in *. subst n.
      apply (Safe ora).
    
    - (* well-formedness *)
      intros i cnti.
      constructor.
      
    - (* only one thread running *)
      intros F; exfalso. simpl in F. omega.
  Admitted.

End Initial_State.

Section Simulation.
  Variables
    (CS : compspecs)
    (* (V : varspecs) (G : funspecs) *)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
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

  Lemma state_invariant_step n :
    forall state,
      state_invariant Jspec' (S n) state ->
      exists state',
        state_step state state' /\
        state_invariant Jspec' n state'.
  Proof.
    intros cm I.
    inversion I as [m ge sch tp Phi compat lock_coh safety wellformed unique E]. rewrite <-E in *.
    (* intros ((m & ge) & sch & sss). *)
    (* destruct sss as (nthreads, thds, phis, lset) eqn:Esss. *)
    (* intros Invariant. *)
    (* assert (I:=Invariant). *)
    (* destruct I as [m0 ge0 sch0 tp PHI mcompat_rmap lock_coherence0 safety unique]. *)
    (* destruct I as ((phi_all & lock_coh) & mcompat & safe & single). *)
    (* rewrite <-Esss in *. *)
    destruct sch as [ | i sch ].
    
    (* empty schedule: we loop in the same state *)
    {
      exists cm; subst; split.
      - constructor.
      - apply state_invariant_c with (PHI := Phi) (mcompat := compat); auto; [].
        intros i cnti ora. simpl.
        specialize (safety i cnti ora); simpl in safety.
        destruct (Machine.getThreadC cnti); auto.
        all: eapply safe_downward1; intuition.
    }
    
    destruct (ssrnat.leq (S i) tp.(Machine.num_threads).(pos.n)) eqn:Ei; swap 1 2.
    
    (* bad schedule *)
    {
      eexists.
      split.
      - constructor.
        apply JuicyMachine.schedfail with i.
        + reflexivity.
        + unfold JM.ThreadPool.containsThread.
          now rewrite Ei; auto.
        + now apply JuicyMachineShell_ClightSEM.True.
        + reflexivity.
      - simpl (ListScheduler_NatTID.schedSkip _).
        apply state_invariant_c with (PHI := Phi) (mcompat := compat); auto.
        + intros i0 cnti0 ora.
          specialize (safety i0 cnti0 ora); simpl in safety.
          eassert.
          * eapply safety; eauto.
          * destruct (Machine.getThreadC cnti0) as [c|c|c v|v1 v2] eqn:Ec; auto;
            intros Safe; try split; try eapply safe_downward1, Safe; intuition.
        + (* invariant about "only one Krun and it is scheduled": the
          bad schedule case is not possible *)
          intros H i0 cnti q ora H0.
          exfalso.
          specialize (unique H i0 cnti q ora H0).
          destruct unique as [sch' unique]; injection unique as <- <- .
          congruence.
    }
    
    (* the schedule selected one thread *)
    assert (cnti : Machine.containsThread tp i) by apply Ei.
    remember (Machine.getThreadC cnti) as ci eqn:Eci; symmetry in Eci.
    (* remember (Machine.getThreadR cnti) as phi_i eqn:Ephi_i; symmetry in Ephi_i. *)
    
    destruct ci as
        [ (* Krun *) ci
        | (* Kblocked *) ci
        | (* Kresume *) ci v
        | (* Kinit *) v1 v2 ].
    
    (* thread[i] is running *)
    {
      pose (jmi := JM.personal_mem cnti (mem_compatible_forget compat)).
      (* pose (phii := m_phi jmi). *)
      (* pose (mi := m_dry jmi). *)
      
      destruct ci as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* thread[i] is running and some internal step *)
      {
        (* get the next step of this particular thread (with safety for all oracles) *)
        assert (next: exists ci' jmi',
                   corestep (juicy_core_sem cl_core_sem) ge ci jmi ci' jmi'
                   /\ forall ora, jsafeN Jspec' ge n ora ci' jmi').
        {
          specialize (safety i cnti).
          pose proof (safety nil) as safei.
          rewrite Eci in *.
          inversion safei as [ | ? ? ? ? c' m' step safe H H2 H3 H4 | | ]; subst.
          2: now match goal with H : at_external _ _ = _ |- _ => inversion H end.
          2: now match goal with H : halted _ _ = _ |- _ => inversion H end.
          exists c', m'. split; [ apply step | ].
          revert step safety safe; clear.
          generalize (jm_ cnti compat).
          generalize (State ve te k).
          unfold jsafeN.
          intros c j step safety safe ora.
          eapply safe_corestep_forward.
          - apply juicy_core_sem_preserves_corestep_fun.
            apply semax_lemmas.cl_corestep_fun'.
          - apply step.
          - apply safety.
        }
        
        destruct next as (ci' & jmi' & stepi & safei').
        pose (tp' := @Machine.updThread i tp cnti (Krun ci') (m_phi jmi')).
        pose (cm' := (m_dry jmi', ge, (i :: sch, tp'))).
        exists cm'.
        split.
        
        - apply state_step_c; [].
          apply JuicyMachine.thread_step with (tid := i) (Htid := cnti) (Hcmpt := mem_compatible_forget compat); [|]. reflexivity.
          eapply JuicyMachineShell_ClightSEM.step_juicy; [ | | | | | ].
          + reflexivity.
          + now constructor.
          + exact Eci. 
          + destruct stepi as [stepi decay].
            split.
            * simpl.
              subst.
              apply stepi.
            * simpl.
              revert decay.
              match goal with |- ?P -> ?Q => cut (P = Q); [ now auto | ] end.
              reflexivity.
          + reflexivity.
          + reflexivity.
        
        - (* build the new PHI: the new jm_i' + the other things? *)
          (* use a program definition to generate this rmap, then prove things about it *)
          assert (mem_compat_step : {Phi' | mem_compatible_rmap tp' (m_dry jmi') Phi'}). {
            (* we probably need to assert a bunch of other things. *)
            clear -i tp Phi compat ge cnti ci ci' jmi' stepi cm'.
            admit.
          }
          destruct stepi as [stepi decay].
          destruct mem_compat_step as [Phi' compat'].
          apply state_invariant_c with (PHI := Phi') (mcompat := compat').
          + (* lock coherence: own rmap has changed, not clear how to prove it did not affect locks *)
            (* (kind of hard) see how new PHI is built *)
            admit.
          + (* safety *)
            intros i0 cnti0 ora.
            destruct (eq_dec i i0).
            * (* for this threadshould be ok, if (jm_ of new Phi) is indeed jm_i' *)
              admit.
            * (* for other threads: prove that their new personal_mem (with the new Phi'/m') still make them safe *)
              admit.
          + (* wellformedness *)
            intros i0 cnti0.
            destruct (eq_dec i i0) as [ <- | ii0].
            * unfold tp'.
              rewrite Machine.gssThreadCode.
              constructor.
            * unfold tp'. 
              rewrite (@Machine.gsoThreadCode _ _ tp ii0 cnti cnti0).
              apply wellformed.
          + (* uniqueness *)
            intros notalone i0 cnti0' q ora Eci0.
            admit (* more important things first *).
      }
      (* end of internal step *)
      
      (* thread[i] is running and about to call an external: Krun (at_ex c) -> Kblocked c *)
      {
        eexists; split.
        
        - (* taking the step *)
          constructor.
          eapply JuicyMachine.suspend_step.
          + reflexivity.
          + reflexivity.
          + eapply mem_compatible_forget; eauto.
          + econstructor.
            * eassumption.
            * reflexivity.
            * constructor.
            * reflexivity.
        
        - (* maintaining the invariant *)
          match goal with |- _ _ (_, _, (_, ?tp)) => set (tp' := tp) end.
          assert (compat' : mem_compatible_rmap tp' m Phi).
          {
            clear safety wellformed unique.
            destruct compat as [JA MC LW LC].
            constructor; [ | | | ].
            - destruct JA as [tp phithreads philocks Phi jointhreads joinlocks join].
              econstructor; eauto.
            - apply MC.
            - intros l sh psh P z H.
              apply (LW l sh psh P z H).
            - apply LC.
          }
          apply state_invariant_c with (PHI := Phi) (mcompat := compat').
          
          + (* lock coherence *)
            eauto.
          
          + (* safety (same, except one thing is Kblocked instead of Krun) *)
            intros i0 cnti0' ora.
            destruct (eq_dec i i0) as [ii0 | ii0].
            * subst i0.
              unfold tp'.
              rewrite Machine.gssThreadCC.
              specialize (safety i cnti ora).
              rewrite Eci in safety.
              simpl.
              simpl in safety.
              apply safe_downward1.
              unfold jm_ in *.
              erewrite personal_mem_ext.
              -- apply safety.
              -- intros i0 cnti1 cnti'.
                 apply Machine.gThreadCR.
            * assert (cnti0 : Machine.containsThread tp i0) by auto.
              unfold tp'.
              rewrite <- (@Machine.gsoThreadCC _ _ tp ii0 cnti cnti0).
              specialize (safety i0 cnti0 ora).
              clear -safety.
              destruct (@Machine.getThreadC i0 tp cnti0).
              -- unfold jm_ in *.
                 erewrite personal_mem_ext.
                 ++ apply safe_downward1, safety.
                 ++ intros; apply Machine.gThreadCR.
              -- unfold jm_ in *.
                 erewrite personal_mem_ext.
                 ++ apply safe_downward1, safety.
                 ++ intros; apply Machine.gThreadCR.
              -- unfold jm_ in *.
                 erewrite personal_mem_ext.
                 ++ apply safe_downward1, safety.
                 ++ intros; apply Machine.gThreadCR.
              -- constructor.
          
          + (* wellformed. *)
            intros i0 cnti0'.
            destruct (eq_dec i i0) as [ii0 | ii0].
            * subst i0.
              unfold tp'.
              rewrite Machine.gssThreadCC.
              simpl.
              congruence.
            * assert (cnti0 : Machine.containsThread tp i0) by auto.
              unfold tp'.
              rewrite <- (@Machine.gsoThreadCC _ _ tp ii0 cnti cnti0).
              specialize (wellformed i0 cnti0).
              destruct (@Machine.getThreadC i0 tp cnti0).
              -- constructor.
              -- apply wellformed.
              -- apply wellformed.
              -- constructor.
          
          + (* uniqueness *)
            intros notalone i0 cnti0' q ora Eci0.
            pose proof (unique notalone i0 cnti0' q ora) as unique'.
            destruct (eq_dec i i0) as [ii0 | ii0].
            * subst i0.
              unfold tp' in Eci0.
              rewrite Machine.gssThreadCC in Eci0.
              discriminate.
            * assert (cnti0 : Machine.containsThread tp i0) by auto.
              unfold tp' in Eci0.
              clear safety wellformed.
              rewrite <- (@Machine.gsoThreadCC _ _ tp ii0 cnti cnti0) in Eci0.
              destruct (unique notalone i cnti _ ora Eci).
              destruct (unique notalone i0 cnti0 q ora Eci0).
              congruence.
          
      } (* end of Krun (at_ex c) -> Kblocked c *)
    } (* end of Krun *)
    
    (* thread[i] is in Kblocked *)
    {
      (* goes to Kresume ci' according to the rules of syncStep  *)
      
      destruct ci as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* internal step: impossible, because in state Kblocked *)
      {
        exfalso.
        pose proof (wellformed i cnti) as W.
        rewrite Eci in W.
        apply W.
        reflexivity.
      }
      (* back to external step *)
      
      
      (* paragraph below: ef has to be an EF_external *)
      assert (Hef : match ef with EF_external _ _ => Logic.True | _ => False end).
      {
        pose proof (safety i cnti nil) as safe_i.
        rewrite Eci in safe_i.
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
        pose proof (safety i cnti nil) as safe_i.
        rewrite Eci in safe_i.
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
        
        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti nil) as safei.
        rewrite Eci in safei.
        unfold jsafeN, juicy_safety.safeN in safei.
        inversion safei
          as [ | n0 z c m0 c' m' H0 H1 H H2 H3 H4
               | n0 z c m0 e sig0 args0 x at_ex Pre SafePost H H3 H4 H5
               | n0 z c m0 i0 H H0 H1 H2 H3 H4];
          [ now inversion H0; inversion H | subst | now inversion H ].
        subst.
        simpl in at_ex. injection at_ex as <- <- <- .
        hnf in x.
        revert x Pre SafePost.
        
        (* dependent destruction *)
        simpl (ext_spec_pre _); simpl (ext_spec_post _).
        unfold funspecOracle2pre, funspecOracle2post.
        unfold ext_spec_pre, ext_spec_post.
        Local Notation "{| 'JE_spec ... |}" := {| JE_spec := _; JE_pre_hered := _; JE_post_hered := _; JE_exit_hered := _ |}.
        destruct (oi_eq_dec (Some (ext_link "acquire")) (ef_id ext_link (EF_external name sg)))
          as [Eef | Eef];
          [ | now clear -Eef H_acquire; simpl in *; congruence ].
        
        intros (phix, ((((ok, oracle_x), vx), shx), Rx)) Pre. simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Pre.
        
        (* relate lset to val *)
        destruct Precond as [PREA [[PREB _] PREC]].
        hnf in PREB.
        assert (islock : exists b ofs, vx = Vptr b ofs /\ exists R, islock_pred R (phi0 @ (b, Int.unsigned ofs))). {
          unfold canon.SEPx in PREC.
          simpl in PREC.
          rewrite seplog.sepcon_emp in PREC.
          replace semax_conc.lock_inv with lock_inv in *.
          unfold lock_inv in PREC.
          destruct PREC as (b & ofs & Evx & lk).
          exists b, ofs. split. now apply Evx.
          specialize (lk (b, Int.unsigned ofs)).
          exists (approx (level phi0) (Interp Rx)).
          simpl in lk.
          if_tac in lk; swap 1 2. {
            exfalso.
            apply H.
            unfold adr_range in *.
            intuition.
            unfold res_predicates.lock_size.
            omega.
          }
          if_tac in lk; [ | tauto ].
          destruct lk as [p lk].
          rewrite lk.
          do 3 eexists.
          unfold compose.
          assert
            (
              SomeP nil (fun _ : unit => approx (level phi0) (Interp Rx)) =
              SomeP nil (fun _ : veric.rmaps.listprod nil => approx (level phi0) (Interp Rx))
            ).
          reflexivity.
          admit.
          admit.
        }
        
        assert (SUB : join_sub phi0 Phi). {
          apply join_sub_trans with  (JM.ThreadPool.getThreadR cnti).
          - econstructor; eauto.
          - apply JM.JuicyMachineLemmas.compatible_threadRes_sub; eauto.
            destruct compat; eauto.
        }
        destruct islock as [b [ofs [-> [R islock]]]].
        pose proof (resource_at_join_sub _ _ (b, Int.unsigned ofs) SUB) as SUB'.
        pose proof islock_pred_join_sub SUB' islock as isl.
        
        (* PLAN
           - DONE: integrate the oracle in the semax_conc definitions
           - DONE: sort out this dependent type problem
           - DONE: exploit jsafeN_ to figure out which possible cases
           - DONE: push the analysis through Krun/Kblocked/Kresume
           - DONE: figure a wait out of the ext_link problem (the LOCK
             should be a parameter of the whole thing)
           - TODO: change the lock_coherence invariants to talk about
             Mem.load instead of directly reading the values, since
             this will be abstracted
           - TODO: acquire-fail: still problems (see below)
           - TODO: acquire-success: the invariant guarantees that the
             rmap in the lockset satisfies the invariant.  We can give
             this rmap as a first step to the oracle.  We again have
             to recover the fact that all oracles after this step will
             be fine as well.  (Let's write simulation lemmas about
             this, probably)
           - TODO: spawning: it introduces a new Kinit, change
             invariant accordingly
           - TODO release: this time, the jsafeN_ will explain how to
             split the current rmap.
           - TODO all the other primitives
         *)
        
          
        (* next step depends on status of lock: *)
        pose proof (lock_coh (b, Int.unsigned ofs)) as lock_coh'.
        inversion lock_coh' as [wetv dryv notlock H H1 H2 | R0 wetv isl' Elockset Ewet Edry | R0 phi wetv isl' SAT_R_Phi Elockset Ewet Edry].
        
        - (* this is not even a lock *)
          exfalso.
          clear -isl notlock.
          destruct isl as [x [? [? ]]].
          eapply notlock.
          now eauto.
        
        - (* acquire fails *)
          destruct isl as [sh [psh [z Ewetv]]].
          subst wetv.
          destruct isl' as [sh' [psh' [z' Eat]]].
          rewrite Eat in Ewetv.
          injection Ewetv as -> -> -> Epr.
          apply inj_pair2 in Epr.
          assert (R0 = R). {
            assert (feq: forall A B (f g : A -> B), f = g -> forall x, f x = g x) by congruence.
            apply (feq _ _ _ _ Epr (tt, tt)).
          }
          subst R0; clear Epr.
          exists (m, ge, (sch, tp)); split.
          + (* taking the step *)
            eapply state_step_c.
            eapply JuicyMachine.sync_step; [ reflexivity | reflexivity | ].
            eapply JM.step_acqfail.
            * constructor.
            * apply Eci.
            * simpl.
              repeat f_equal.
              -- simpl in H_acquire.
                 injection H_acquire as Ee.
                 apply ext_link_inj in Ee.
                 rewrite <-Ee.
                 reflexivity.
              -- inversion safei; subst.
                 admit. 2:admit.
                 simpl in H0.
                 injection H0 as <- <- <-.
                 simpl in H1.
                 admit.
                 (* see with andrew: should safety require signatures
                 to be exactly something?  Maybe it should be in
                 ext_spec_type, it'd be easy, maybe. *)
              -- admit (* another sig! *).
              -- instantiate (2 := b).
                 instantiate (1 := ofs).
                 assert (L: length args = 1%nat) by admit. (* TODO discuss with andrew for where to add this requirement *)
                 clear -PREB L.
                 unfold expr.eval_id in PREB.
                 unfold expr.force_val in PREB.
                 match goal with H : context [Map.get ?a ?b] |- _ => destruct (Map.get a b) eqn:E end.
                 subst v. 2: discriminate.
                 pose  (gx := (filter_genv (symb2genv (Genv.genv_symb ge)))). fold gx in E.
                 destruct args as [ | arg [ | ar args ]].
                 ++ now inversion E.
                 ++ inversion E. reflexivity.
                 ++ inversion E. f_equal.
                    inversion L.
            * reflexivity.
            * reflexivity.
            * rewrite JM.JuicyMachineLemmas.compatible_getThreadR_m_phi.
              unfold JM.pack_res_inv in *.
              admit.
            * (* maybe we should write this in the invariant instead? *)
              admit.
          + (* invariant (easy, same state than before) *)
            apply state_invariant_c with (PHI := Phi) (mcompat := compat).
            * eauto.
            * intros i0 cnti0 ora.
              specialize (safety i0 cnti0 ora).
              destruct (Machine.getThreadC cnti0); try apply safe_downward1; auto.
            * eauto.
            * (* uniqueness (if there is a Krun, then it would have
              been schedule, but the scheduled thread was a Kblocked,
              so no problem *)
              admit (* more important things now *).
        
        - (* acquire succeeds *)
          destruct isl as [sh [psh [z Ewetv]]].
          destruct isl' as [sh' [psh' [z' Eat]]].
          rewrite Eat in Ewetv.
          injection Ewetv as -> -> -> Epr.
          replace R0 with R in * by admit (* OK (see above) *).
          eexists.
          split.
          + (* taking the step *)
            eapply state_step_c.
            eapply JuicyMachine.sync_step; [ reflexivity | reflexivity | ].
            eapply JM.step_acquire.
            * now auto.
            * eassumption.
            * simpl.
              repeat f_equal; [ | | | ].
              -- admit (* TODO: Problem: this LOCK is a parameter of the whole thing. *).
              -- admit (* should well-formedness imply this kind of thing? or just safety? *).
              -- admit (* should well-formedness imply this kind of thing? or just safety? *).
              -- admit (* should well-formedness imply this kind of thing? or just safety? *).
            * reflexivity.
            * admit (* precondition? *).
            * reflexivity.
            * admit (* real stuff: load 1 *).
            * admit (* real stuff: store 0 *).
            * admit (* real stuff: lock is Some *).
            * admit (* real stuff: it joins *).
            * reflexivity.
            * reflexivity.
          + (* invariant is maintainted (should be the same global rmap) *)
            (*
            assert (
                mem_compatible_rmap
                  (JM.ThreadPool.updLockSet
                     (JM.ThreadPool.updThread
                        cnti
                        (Kresume (ExtCall (EF_external name sg) sig args lid ve te k) Vundef)
                        (m_phi ?jm')) (?b0, Int.intval ?ofs0) None)
                  (m_dry ?jm')).
             *)
            eapply state_invariant_c with (PHI := Phi) (mcompat := _).
            * (* TODO lock_coherence (hard) some work needed here *)
              admit.
            * (* TODO safety (hard) a lot of work needed here, using the oracle. *)
              admit.
            * (* wellformedness (symbol pushing) *)
              admit.
            * (* uniqueness (symbol pushing) *)
              admit.
      }
      
      { (* the case of release *) admit. }
      
      { (* the case of makelock *) admit. }
      
      { (* the case of freelock *) admit. }
      
      { (* the case of spawn *) admit. }
    }
    (* end of Kblocked *)
    
    (* thread[i] is in Kresume *)
    {
      (* goes to Krun ci' with after_ex ci = ci'  *)
      destruct ci as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      - (* contradiction: has to be an extcall *)
        specialize (wellformed i cnti).
        rewrite Eci in wellformed.
        simpl in wellformed.
        tauto.
      
      - (* extcall *)
        pose (ci':=
                match lid with
                | Some id => State ve (Maps.PTree.set id (Vint Int.zero) te) k
                | None => State ve te k
                end).
        exists (m, ge, (i :: sch, Machine.updThreadC cnti (Krun ci'))); split.
        + (* taking the step Kresum->Krun *)
          constructor.
          apply JuicyMachine.resume_step with (tid := i) (Htid := cnti).
          * reflexivity.
          * eapply mem_compatible_forget. eauto.
          * eapply JuicyMachine.ResumeThread with (c := ci) (c' := ci').
            -- subst. reflexivity.
            -- subst. simpl. destruct lid; reflexivity.
            -- rewrite Eci.
               subst ci.
               f_equal.
               specialize (wellformed i cnti).
               rewrite Eci in wellformed.
               simpl in wellformed.
               tauto.
            -- constructor.
            -- reflexivity.
        + (* invariant again. (roughly same as in Krun -> Kblocked,
             but simpler.) *)
          (* leaving this as a TODO as there is a good chance that the
             invariant will change when proving Kblocked->Kresume *)
          admit.
    }
    (* end of Kresume *)
    
    (* thread[i] is in Kinit *)
    {
      eexists; split.
      - constructor.
        apply JuicyMachine.start_step with (tid := i) (Htid := cnti).
        + reflexivity.
        + eapply mem_compatible_forget. eauto.
        + eapply JuicyMachine.StartThread.
          * apply Eci.
          * simpl.
            (* WE SAID THAT THIS SHOULD NOT BE IN THE MACHINE? *) 
            (* Maybe this is impossible and I have to do all the spawn
               work by myself. *)
           admit.
          * constructor.
          * reflexivity.
      - (* invariant: this complicates things quite a lot. I'll have
           to put horrible things in my invariant?  We'll see
           later. *)
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