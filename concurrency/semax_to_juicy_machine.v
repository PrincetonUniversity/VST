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
         forall i (cnti : Machine.containsThread tp i) (ora : Z),
           match Machine.getThreadC cnti with
           | Krun q => Logic.True
           | Kblocked q
           | Kresume q _ => cl_at_external q <> None
           | Kinit _ _ => Logic.True
           end
      )
      (uniqueness_Krun :
         (lt 1 tp.(Machine.num_threads).(pos.n) -> forall i cnti q (ora : Z),
             @Machine.getThreadC i tp cnti = Krun q ->
             exists sch', sch = i :: sch'))
    :
      state_invariant Jspec n (m, ge, (sch, tp)).

Lemma jsafeN_proof_irrelevance Z OK_spec prog oracle c jm jm' :
  m_dry jm = m_dry jm' ->
  m_phi jm = m_phi jm' ->
  @jsafeN Z OK_spec (globalenv prog) (level jm) oracle c jm ->
  @jsafeN Z OK_spec (globalenv prog) (level jm') oracle c jm'.
Admitted.

(*! Initial machine *)

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
  
  Lemma personal_mem_unique_dry tp m (mc : JM.mem_compatible tp m) i (cnti : Machine.containsThread tp i) :
    tp.(Machine.num_threads).(pos.n) = 1 ->
    m_dry (JM.personal_mem cnti mc) = m.
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
      constructor.
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
          rewrite personal_mem_unique_dry; [ | now auto].
          unfold jm.
          destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
          destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl projT1 in *; simpl projT2 in *.
          now auto.
      }
      subst jm. rewrite <-Ejm.
      simpl in Ec. replace c with q in * by congruence.
      destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
      destruct (JS n) as (jm' & jmm & lev & Safe & notlock); simpl projT1 in *; simpl projT2 in *.
      subst q.
      simpl proj1_sig in *; simpl proj2_sig in *. subst n.
      eapply jsafeN_proof_irrelevance; [ | | apply (Safe ora) ]; auto.
      
      (*
      destruct 
      intros i cnti phi jmi ora Ephi.
      intros Edry Ewet.
      destruct i as [ | [ | i ]]. 2: now inversion cnti. 2:now inversion cnti.
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
       *)
    
    - (* well-formedness *)
      intros i cnti ora.
      apply I.
      
    - (* only one thread running *)
      intros F; exfalso. simpl in F. omega.
  Admitted.

End Initial_State.

Require Import msl.Coqlib2.
Lemma corestep_fun_juicy (rmap_ext  : forall phi1 phi2, (forall l, phi1 @ l = phi2 @ l) -> phi1 = phi2) :
  corestep_fun (juicy_core_sem cl_core_sem).
Proof.
  intros ge jm q jm1 q1 jm2 q2 step1 step2.
  destruct step1 as [step1 [[ll1 rd1] l1]].
  destruct step2 as [step2 [[ll2 rd2] l2]].
  pose proof semax_lemmas.cl_corestep_fun' _ _ _ _ _ _ _ step1 step2 as E.
  injection E as <- E; f_equal.
  apply juicy_mem_ext; auto.
  apply rmap_ext; clear rmap_ext.
  intros l.
  specialize (rd1 l); specialize (rd2 l).
  assert (El: level jm1 = level jm2) by (clear -l1 l2; omega).
  assert (l1': level jm1 = Nat.pred (level jm)) by (clear -l1; omega).
  assert (l2': level jm2 = Nat.pred (level jm)) by (clear -l2; omega).
  rewrite level_juice_level_phi in *.
  destruct jm  as [m  phi  jmc  jmacc  jmma  jmall ].
  destruct jm1 as [m1 phi1 jmc1 jmacc1 jmma1 jmall1].
  destruct jm2 as [m2 phi2 jmc2 jmacc2 jmma2 jmall2].
  simpl in *.
  subst m2; rename m1 into m'.
  destruct rd1 as [jmno [E1 | [[sh1 [v1 [v1' [E1 E1']]]] | [[pos1 [v1 E1]] | [v1 [pp1 [E1 E1']]]]]]];
  destruct rd2 as [_    [E2 | [[sh2 [v2 [v2' [E2 E2']]]] | [[pos2 [v2 E2]] | [v2 [pp2 [E2 E2']]]]]]];
  try pose proof jmno pos1 as phino; try pose proof (jmno pos2) as phino; clear jmno;
    remember (phi  @ l) as x ;
    remember (phi1 @ l) as x1;
    remember (phi2 @ l) as x2;
    subst.
  
  - (* phi1: same   | phi2: same   *)
    congruence.
  
  - (* phi1: same   | phi2: update *)
    rewrite <- E1, El.
    rewrite El in E1.
    rewrite E1 in E2.
    destruct (jmc1 _ _ _ _ _ E2).
    destruct (jmc2 _ _ _ _ _ E2').
    congruence.
  
  - (* phi1: same   | phi2: alloc  *)
    exfalso.
    rewrite phino in E1. simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc2 l).
    rewrite E2 in jmacc2.
    simpl in jmacc2.
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; congruence.
  
  - (* phi1: same   | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; congruence.
  
  - (* phi1: update | phi2: same   *)
    rewrite <- E2, <-El.
    rewrite <-El in E2.
    rewrite E2 in E1.
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E1).
    congruence.
  
  - (* phi1: update | phi2: update *)
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E2').
    congruence.
  
  - (* phi1: update | phi2: alloc  *)
    rewrite phino in E1.
    simpl in E1.
    inversion E1.
  
  - (* phi1: update | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    unfold fullshare in *.
    repeat if_tac in jmacc2; congruence.
  
  - (* phi1: alloc  | phi2: same   *)
    exfalso.
    rewrite phino in E2. simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc1 l).
    rewrite E1 in jmacc1.
    simpl in jmacc1.
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; congruence.
  
  - (* phi1: alloc  | phi2: update *)
    rewrite phino in E2.
    simpl in E2.
    inversion E2.
  
  - (* phi1: alloc  | phi2: alloc  *)
    destruct (jmc1 _ _ _ _ _ E1).
    destruct (jmc2 _ _ _ _ _ E2).
    congruence.
  
  - (* phi1: alloc  | phi2: free   *)
    congruence.
  
  - (* phi2: free   | phi2: same   *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; congruence.
  
  - (* phi2: free   | phi2: update *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    unfold fullshare in *.
    repeat if_tac in jmacc1; congruence.
  
  - (* phi2: free   | phi2: alloc  *)
    congruence.
  
  - (* phi2: free   | phi2: free   *)
    congruence.
Qed.

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
    
    destruct (i < tp.(Machine.num_threads).(pos.n)) eqn:Ei; swap 1 2.
    
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
          - apply corestep_fun_juicy. admit.
          - apply step.
          - apply safety.
        }
        
        destruct next as (ci' & jm_i' & step_i & safe_i').
        pose (m' := m_dry jm_i' (* TODO update cur *)).
        pose (tp' := @Machine.updThread i tp cnti (Krun ci') (m_phi jm_i')).
        pose (cm' := (m', ge, (i :: sch, tp'))).
        exists cm'.
        split.
        - apply state_step_c; [].
          apply JuicyMachine.thread_step with (tid := i) (Htid := cnti) (Hcmpt := mem_compatible_forget compat); [|]. now reflexivity.
          hnf; [].
          eapply JuicyMachineShell_ClightSEM.step_juicy; eauto; [ | | | ].
          + hnf. now constructor.
          + destruct step_i as [stepi decay].
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
        - (* related to updating CUR above: ask. *)
          admit.
          
          (*
          apply state_step_internal with (contains_thread_i := cnti) (mcompat := mcompat).
          apply JuicyMachineShell_ClightSEM.step_juicy with (c := ci) (jm := jm_i) (c' := ci') (jm' := jm_i').
          + admit (* mcompat *).
          + admit (* mem coherence *).
          + congruence.
          + apply step_i.
          + reflexivity.
          + reflexivity.
        - split;[|split;[|split]].
          + admit (* get phi_all from the mcompat, too? *).
          + admit (* mcompat *).
          + intros i0 cnti0 q phi jmi ora.
            (* safety for all oracle : use the fact the oracle does
            not change after one step *)
            admit.
          + intros H i0 cnti0 q ora H0.
            exists sch.
            (* use the fact that there is at most one Krun on the
            previous step and this step did not add any *)
            admit.
           *)
      }
      (* end of internal step *)
      
      (* thread[i] is running and about to call an external: Krun (at_ex c) -> Kblocked c *)
      {
        eexists; split.
        - constructor.
          eapply JuicyMachine.suspend_step.
          + reflexivity.
          + reflexivity.
          + eapply mem_compatible_forget; eauto.
          + econstructor.
            * eassumption.
            * reflexivity.
            * constructor.
            * reflexivity.
        - match goal with |- _ _ (_, _, (_, ?tp)) => set (tp' := tp) end.
          assert (compat' : mem_compatible_rmap tp' m Phi).
          {
            unfold tp'.
            clear safety wellformed unique.
            destruct compat as [JA MC LW LC].
            constructor; [ | | | ].
            - admit.
            - admit.
            - admit.
            - admit.
          }
          apply state_invariant_c with (PHI := Phi) (mcompat := compat').
          + admit.
          + admit.
          + admit.
          + admit.
(*
          + subst sss; clear -lock_coh.
            unfold ThreadPool.lset in *.
            exists phi_all.
            now apply lock_coh.
          + unfold mem_compatible in *.
            subst sss.
            unfold ThreadPool.updThreadC in *; simpl.
            inversion mcompat; [].
            inversion juice_join; [].
            econstructor; [ | | | ]; auto.
            now econstructor; [ | | ]; eauto.
            all: now auto.
          + intros i0 cnti0 phi jmi ora H H0 H1.
            destruct (eq_dec i i0) as [<-|E].
            * specialize (safe i cnti phi jmi ora).
              rewrite gssThreadCC.
              rewrite Eci in safe.
              split. 2:subst; simpl; congruence.
              apply safe_downward1.
              change (jsafeN Jspec' ge (S n) ora (ExtCall ef sig args lid ve te k) jmi).
              apply safe; auto; []. 
              erewrite <- gThreadCR in H.
              apply H.
            * subst sss. 
              assert (cnti0' := cntUpdateC' cnti0).
              specialize (safe i0 cnti0' phi jmi ora).
              erewrite <- gsoThreadCC with (cntj := cnti0'). 2:apply E.
              destruct (getThreadC cnti0'); try split; try apply safe_downward1; try destruct safe as [safe|?]; try apply safe; auto.
              all: erewrite <- gThreadCR; apply H.
          + intros H i0 cnti0 q ora H0.
            subst sss.
            exfalso.
            (* derive false: thread i0 is in Krun, even though that
            can only be the new Kblock or an old Krun, which would
            have been in conflict with the other, old, Krun *)
            admit.
*)
      } (* end of Krun (at_ex c) -> Kblocked c *)
    } (* end of Krun *)
    
    (* thread[i] is in Kblocked *)
    {
      (* goes to Kresume ci' according to the rules of syncStep  *)
      
      destruct ci as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* internal step: impossible, because in state Kblocked *)
      {
        exfalso.
        pose proof (wellformed i cnti nil) as W.
        rewrite Eci in W.
        apply W.
        reflexivity.
      }
      (* back to external step *)

(*
      (* paragraph below: ef has to be an EF_external *)
      assert (Hef : match ef with EF_external _ _ => Logic.True | _ => False end).
      {
        pose proof (safe i cnti phi_i jm_i nil ltac:(assumption)) as safe_i.
        rewrite Eci in safe_i.
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
        pose proof (safe i cnti phi_i jm_i (* oracle=*)nil ltac:(assumption)) as safe_i.
        rewrite Eci in safe_i.
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
          
          pose proof (safe i cnti phi_i jm_i (* oracle=*)nil ltac:(assumption)) as safe_i.
          rewrite Eci in safe_i.
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
 *)
      admit.
    }
    (* end of Kblocked *)
    
    (* thread[i] is in Kresume *)
    {
      (* goes to Krun ci' according with after_ex ci = ci'  *)
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