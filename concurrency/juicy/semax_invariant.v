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
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.external_state.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.seplog.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
Require Import VST.concurrency.juicy.JuicyMachineModule.
(*Require Import VST.concurrency.juicy.sync_preds_defs.*)
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.common.lksize.
Import threadPool Events.

(*! Instantiation of modules *)
Export THE_JUICY_MACHINE.
Export OrdinalPool ThreadPool.
Export Concur.

Set Bullet Behavior "Strict Subproofs".

Ltac cleanup :=
  simpl in *;
  unfold OrdinalPool.lockRes in *;
  unfold OrdinalPool.lockGuts in *; unfold OrdinalPool.lockSet in *;
  simpl lock_info in *; simpl res in *.

Notation event_trace := (seq.seq machine_event).

Lemma allows_exit `{!heapGS Σ} `{!externalGS unit Σ} {CS} ext_link : @postcondition_allows_exit _ (Concurrent_Espec unit CS ext_link) Ctypesdefs.tint.
Proof.
  by constructor.
Qed.

Section Machine.

Context {ZT : Type} `{!heapGS Σ} `{!externalGS ZT Σ} (Jspec : juicy_ext_spec(Σ := Σ) ZT) {ge : genv}.
Definition Espec := {| OK_ty := ZT; OK_spec := Jspec |}.

(*+ Description of the invariant *)
Definition cm_state := (Mem.mem * (event_trace * schedule * jstate ge))%type.

Inductive state_step : cm_state -> cm_state -> Prop :=
| state_step_empty_sched m tr jstate :
    state_step
      (m, (tr, nil, jstate))
      (m, (tr, nil, jstate))
| state_step_c m m' tr tr' sch sch' jstate jstate':
    @JuicyMachine.machine_step _ (ClightSem ge) _ HybridCoarseMachine.DilMem (JuicyMachineShell(Σ := Σ)) HybridMachineSig.HybridCoarseMachine.scheduler sch tr jstate m sch' tr' jstate' m' ->
    state_step
      (m, (tr, sch, jstate))
      (m',(tr', sch', jstate')).


(*! Coherence between locks in dry/wet memories and lock pool *)

(*Inductive cohere_res_lock : forall (resv : option (option rmap)) (wetv : resource) (dryv : memval), Prop :=
| cohere_notlock wetv dryv:
    (forall sh sh' z P, wetv <> YES sh sh' (LK z 0) P) ->
    cohere_res_lock None wetv dryv
| cohere_locked R wetv :
    islock_pred R wetv ->
    cohere_res_lock (Some None) wetv (Byte (Integers.Byte.zero))
| cohere_unlocked R phi wetv :
    islock_pred R wetv ->
    R phi ->
    cohere_res_lock (Some (Some phi)) wetv (Byte (Integers.Byte.one)).

Definition load_at m loc := Mem.load Mptr m (fst loc) (snd loc).

Definition lock_coherence (lset : AMap.t (option rmap)) (phi : rmap) (m : mem) : Prop :=
  forall loc : address,
    match AMap.find loc lset with

    (* not a lock *)
    | None => ~isLK (phi @ loc) (* /\ ~isCT (phi @ loc) *)

    (* locked lock *)
    | Some None =>
      load_at m loc = Some (Vptrofs Ptrofs.zero) /\
      (size_chunk Mptr | snd loc) /\
      (snd loc + LKSIZE < Ptrofs.modulus)%Z /\
      exists R, lkat R loc phi

    (* unlocked lock *)
    | Some (Some lockphi) =>
      load_at m loc = Some (Vptrofs Ptrofs.one) /\
      (size_chunk Mptr | snd loc) /\
      (snd loc + LKSIZE < Ptrofs.modulus)%Z /\
      exists (R : mpred),
        lkat R loc phi /\
        (app_pred R (age_by 1 lockphi) \/ level phi = O)
        (*/\
        match age1 lockphi with
        | Some p => app_pred R p
        | None => Logic.True
        end*)
    end.*)

Definition far (ofs1 ofs2 : Z) := (Z.abs (ofs1 - ofs2) >= LKSIZE)%Z.

Lemma far_range ofs ofs' z :
  (0 <= z < LKSIZE)%Z ->
  far ofs ofs' ->
  ~(ofs <= ofs' + z < ofs + LKSIZE)%Z.
Proof.
  unfold far; simpl.
  intros H1 H2.
  zify.
  lia.
Qed.

Definition lock_sparsity {A} (lset : AMap.t A) : Prop :=
  forall loc1 loc2,
    AMap.find loc1 lset <> None ->
    AMap.find loc2 lset <> None ->
    loc1 = loc2 \/
    fst loc1 <> fst loc2 \/
    (fst loc1 = fst loc2 /\ far (snd loc1) (snd loc2)).

Definition lset_same_support {A} (lset1 lset2 : AMap.t A) :=
  forall loc,
    AMap.find loc lset1 = None <->
    AMap.find loc lset2 = None.

Lemma sparsity_same_support {A} (lset1 lset2 : AMap.t A) :
  lset_same_support lset1 lset2 ->
  lock_sparsity lset1 ->
  lock_sparsity lset2.
Proof.
  intros same sparse l1 l2.
  specialize (sparse l1 l2).
  rewrite <-(same l1).
  rewrite <-(same l2).
  auto.
Qed.

Lemma same_support_change_lock {A} (lset : AMap.t A) l x :
  AMap.find l lset <> None ->
  lset_same_support lset (AMap.add l x lset).
Proof.
  intros E l'.
  rewrite AMap_find_add.
  if_tac.
  - split; congruence.
  - tauto.
Qed.

Lemma lset_same_support_map {A} m (f : A -> A) :
  lset_same_support (AMap.map (option_map f) m) m.
Proof.
  intros k.
  rewrite AMap_find_map_option_map.
  destruct (AMap.find (elt:=option A) k m); simpl; split; congruence.
Qed.

Lemma lset_same_support_sym {A} (m1 m2 : AMap.t A) :
  lset_same_support m1 m2 ->
  lset_same_support m2 m1.
Proof.
  unfold lset_same_support in *.
  intros E loc.
  rewrite E; tauto.
Qed.

Lemma lset_same_support_trans {A} (m1 m2 m3 : AMap.t A) :
  lset_same_support m1 m2 ->
  lset_same_support m2 m3 ->
  lset_same_support m1 m3.
Proof.
  unfold lset_same_support in *.
  intros E F loc.
  rewrite E; apply F.
Qed.

(*! Joinability and coherence *)

Lemma mem_compatible_forget {tp : jstate ge} {m phi} :
  mem_compatible_with tp m phi -> mem_compatible tp m.
Proof. intros M; exists phi. apply M. Qed.

Definition jm_
  {tp m PHI i}
  (cnti : containsThread tp i)
  (mcompat : mem_compatible_with tp m PHI)
  : mem :=
  personal_mem (thread_mem_compatible (mem_compatible_forget mcompat) cnti).

Lemma personal_mem_ext m phi phi' pr pr' :
  phi = phi' ->
  @personal_mem m phi pr =
  @personal_mem m phi' pr'.
Proof.
  intros <-; f_equal; apply proof_irr.
Qed.

(*! Invariant (= above properties + safety + uniqueness of Krun) *)

(* Could we move more of this into the logic? *)
(* Since we're moving towards a machine without ghost state, we erase all of the state except
   the rmap, and then nondeterministically reconstruct the rest of the state at each step.
   Will this work? *)
Definition jsafe_phi ge n ora c phi :=
    ouPred_holds (semax.jsafeN Espec ge ⊤ ora c) n phi.

Definition threads_safety m (tp : jstate ge) PHI (mcompat : mem_compatible_with tp m PHI) n :=
  forall i (cnti : containsThread tp i) (ora : ZT),
    match getThreadC cnti with
    | Krun c => jsafe_phi ge n ora c (getThreadR cnti)
    | Kblocked c =>
      (* The dry memory will change, so when we prove safety after an
      external we must only inspect the rmap m_phi part of the juicy
      memory.  This means more proof for each of the synchronisation
      primitives. *)
      jsafe_phi ge ora c (getThreadR cnti)
    | Kresume c v =>
      forall c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        cl_after_external None c = Some c' ->
        (* same quantification as in Kblocked *)
        jsafe_phi ge n ora c' (getThreadR cnti)
    | Kinit v1 v2 =>
(*      Val.inject (Mem.flat_inj (Mem.nextblock m)) v2 v2 /\ *)
      exists q_new,
      cl_initial_core ge v1 (v2 :: nil) = Some q_new /\
      jsafe_phi ge n ora q_new (getThreadR cnti)
    end.

Definition threads_wellformed (tp : jstate ge) :=
  forall i (cnti : containsThread tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

(* Haven't move this, but it's already defined in the concurrent_machine...
 * Probably in the wrong part... *)
Definition unique_Krun (tp : jstate ge) sch :=
  (lt 1 tp.(num_threads).(pos.n) -> forall i cnti q,
      @getThreadC _ _ _ i tp cnti = Krun q ->
      exists sch', sch = i :: sch').

Definition no_Krun (tp : jstate ge) :=
  forall i cnti q, @getThreadC _ _ _ i tp cnti <> Krun q.

Lemma no_Krun_unique_Krun tp sch : no_Krun tp -> unique_Krun tp sch.
Proof.
  intros H _ i cnti q E; destruct (H i cnti q E).
Qed.

Lemma containsThread_age_tp_to_eq (tp : jstate ge) n :
  containsThread (age_tp_to n tp) = containsThread tp.
Proof.
  destruct tp; reflexivity.
Qed.

Lemma no_Krun_age_tp_to n tp :
  no_Krun (age_tp_to n tp) = no_Krun tp.
Proof.
  destruct tp; reflexivity.
Qed.

Lemma unique_Krun_age_tp_to n tp sch :
  unique_Krun (age_tp_to n tp) sch <-> unique_Krun tp sch.
Proof.
  destruct tp; reflexivity.
Qed.

Lemma no_Krun_stable tp i cnti c' phi' :
  (forall q, c' <> Krun q) ->
  no_Krun tp ->
  no_Krun (@updThread _ _ _ i tp cnti c' phi').
Proof.
  intros notkrun H j cntj q.
  destruct (eq_dec i j).
  - subst.
    rewrite gssThreadCode.
    apply notkrun.
  - unshelve erewrite gsoThreadCode; auto.
Qed.

Lemma no_Krun_stableR tp i cnti phi' :
  no_Krun tp ->
  no_Krun (@updThreadR _ _ _ i tp cnti phi').
Proof.
  intros notkrun j cntj q.
  destruct (eq_dec i j).
  - subst.
    unshelve erewrite gThreadRC; eauto.
  - unshelve erewrite gThreadRC; eauto.
Qed.

Lemma no_Krun_unique_Krun_updThread tp i sch cnti q phi' :
  no_Krun tp ->
  unique_Krun (@updThread _ _ _ i tp cnti (Krun q) phi') (i :: sch).
Proof.
  intros NO H j cntj q'.
  destruct (eq_dec i j).
  - subst.
    rewrite gssThreadCode.
    injection 1 as <-. eauto.
  - unshelve erewrite gsoThreadCode; auto.
    intros E; specialize (NO _ _ _ E). destruct NO.
Qed.

Lemma no_Krun_updLockSet tp loc ophi :
  no_Krun tp ->
  no_Krun (updLockSet tp loc ophi).
Proof.
  intros N; apply N.
Qed.

Lemma no_Krun_remLockSet tp loc:
  no_Krun tp -> no_Krun (remLockSet tp loc).
Proof.
  intros N; apply N.
Qed.

Lemma ssr_leP_inv i n : is_true (ssrnat.leq i n) -> (i <= n)%nat.
Proof.
  pose proof @ssrnat.leP i n as H.
  intros E; rewrite E in H.
  inversion H; auto.
Qed.

Lemma different_threads_means_several_threads i j (tp : jstate ge)
      (cnti : containsThread tp i)
      (cntj : containsThread tp j) :
  i <> j -> (1 < pos.n (num_threads tp))%nat.
Proof.
  simpl in *.
  unfold OrdinalPool.containsThread in *.
  simpl in *.
  destruct tp as [n].
  simpl in *.
  remember (pos.n n) as k; clear Heqk n.
  apply ssr_leP_inv in cnti.
  apply ssr_leP_inv in cntj.
  lia.
Qed.

Lemma unique_Krun_no_Krun tp i sch cnti :
  unique_Krun tp (i :: sch) ->
  (forall q, @getThreadC _ _ _ i tp cnti <> Krun q) ->
  no_Krun tp.
Proof.
  intros U N j cntj q E.
  assert (i <> j). {
    intros <-.
    apply N with q.
    exact_eq E; do 2 f_equal.
    apply proof_irr.
  }
  unfold unique_Krun in *.
  assert_specialize U.
  now eapply (different_threads_means_several_threads i j); eauto.
  specialize (U _ _ _ E). destruct U. congruence.
Qed.

Lemma unique_Krun_no_Krun_updThread tp i sch cnti c' phi' :
  (forall q, c' <> Krun q) ->
  unique_Krun tp (i :: sch) ->
  no_Krun (@updThread _ _ _ i tp cnti c' phi').
Proof.
  intros notkrun uniq j cntj q.
  destruct (eq_dec i j) as [<-|N].
  - rewrite gssThreadCode.
    apply notkrun.
  - unshelve erewrite gsoThreadCode; auto.
    unfold unique_Krun in *.
    assert_specialize uniq.
    now eapply (different_threads_means_several_threads i j); eauto.
    intros E.
    specialize (uniq _ _ _ E).
    destruct uniq.
    congruence.
Qed.

Lemma unique_Krun_neq i j tp sch
      (cnti : containsThread tp i)
      (cntj : containsThread tp j) :
  i <> j ->
  unique_Krun tp (i :: sch) ->
  forall q, @getThreadC _ _ _ j tp cntj <> Krun q.
Proof.
  intros ne U q E.
  hnf in U.
  spec U. now apply (different_threads_means_several_threads i j).
  specialize (U j cntj q E).
  breakhyps.
Qed.

Definition lock_coherence' tp PHI m (mcompat : mem_compatible_with tp m PHI) :=
  lock_coherence
    (lset tp) PHI
    (restrPermMap
       (mem_compatible_locks_ltwritable
          (mem_compatible_forget mcompat))).

Import Clight_initial_world.
Import Clight_seplog.
Import ghost_PCM.

Definition env_coherence {Z} Jspec (ge : genv) (Gamma : funspecs) PHI :=
  matchfunspecs ge Gamma PHI /\
  exists prog ora CS V,
    @semax_prog {|OK_ty := Z; OK_spec := Jspec|} CS prog ora V Gamma /\
    ge = globalenv prog /\
    app_pred
      (funassert (make_tycontext ((*Tpointer Ctypes.Tvoid noattr ::*) nil) nil nil Ctypes.Tvoid V Gamma nil)
                 (empty_environ ge)) PHI.

Definition maxedmem (m: mem) :=
  restrPermMap (mem_max_lt_max m).

Definition mem_wellformed (m: mem) :=
 Mem.inject_neutral (Mem.nextblock m) (maxedmem m) /\
  Ple (Genv.genv_next ge) (Mem.nextblock m).

Lemma maxedmem_neutral:
  forall m,
 Mem.inject_neutral (Mem.nextblock (maxedmem m)) (maxedmem m) ->
  Mem.inject_neutral (Mem.nextblock m) m.
Proof.
intros.
unfold Mem.inject_neutral in *.
inv H.
constructor; intros; simpl in *.
- unfold Mem.flat_inj in H.
if_tac in H; try discriminate.
inv H.
rewrite Z.add_0_r. auto.
- eapply mi_align; eauto.
intros ? ?.
unfold maxedmem.
unfold Mem.perm; setoid_rewrite restrPermMap_Max; rewrite getMaxPerm_correct.
eauto.
specialize (H0 _ H1).
apply H0.
- apply mi_memval; auto.
clear - H0.
unfold maxedmem, Mem.perm in *.
setoid_rewrite restrPermMap_Cur.
unfold getMaxPerm.
rewrite PMap.gmap.
eapply perm_order_trans211; eauto.
apply (access_cur_max _ (_, _)).
Qed.

Definition inv_compatible (tp : jstate ge) := forall i (cnti : containsThread tp i), exists r w,
  join_sub r (getThreadR cnti) /\ join r (extraRes tp) w /\
  app_pred (invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred w.

Inductive state_invariant Gamma (n : nat) : cm_state -> Prop :=
  | state_invariant_c
      (m : mem) (tr : event_trace) (sch : schedule) (tp : jstate ge) (PHI : rmap)
      (lev : level PHI = n)
      (envcoh : env_coherence Jspec ge Gamma PHI)
(*      (mwellformed: mem_wellformed m) *)
      (mcompat : mem_compatible_with tp m PHI)
      (extcompat : ext_compat tt PHI)
      (lock_sparse : lock_sparsity (lset tp))
      (lock_coh : lock_coherence' tp PHI m mcompat)
      (safety : threads_safety m tp PHI mcompat)
      (wellformed : threads_wellformed tp)
      (uniqkrun :  unique_Krun tp sch)
      (invcompat : inv_compatible tp)
    : state_invariant Gamma n (m, (tr, sch, tp)).

(* Schedule irrelevance of the invariant *)
Lemma state_invariant_sch_irr Gamma n m i tr sch sch' tp :
  state_invariant Gamma n (m, (tr, i :: sch, tp)) ->
  state_invariant Gamma n (m, (tr, i :: sch', tp)).
Proof.
  intros INV.
  inversion INV as [m0 tr0 sch0 tp0 PHI lev envcoh (*mwellformed*) compat extcompat sparse lock_coh safety wellformed uniqkrun invcompat H0];
    subst m0 tr0 sch0 tp0.
  refine (state_invariant_c Gamma n m tr (i :: sch') tp PHI lev envcoh (*mwellformed*) compat extcompat sparse lock_coh safety wellformed _ invcompat ).
  clear -uniqkrun.
  intros H i0 cnti q H0.
  destruct (uniqkrun H i0 cnti q H0) as [sch'' E].
  injection E as <- <-.
  eauto.
Qed.

Definition blocked_at_external (state : cm_state) (ef : external_function) :=
  match state with
    (m, (tr, sch, tp)) =>
    exists j cntj sch' c args,
      sch = j :: sch' /\
      @getThreadC _ _ _ j tp cntj = Kblocked c /\
      cl_at_external c = Some (ef, args)
  end.

Definition state_bupd P (state : cm_state) := let '(m, (tr, sch, tp)) := state in
  tp_bupd (fun tp' => P (m, (tr, sch, tp'))) tp.

Lemma tp_bupd_intro : forall (P : _ -> Prop) (tp : jstate ge) phi, join_all tp phi ->
  ext_compat tt phi -> P tp -> tp_bupd P tp.
Proof.
  unfold tp_bupd; intros.
  split; eauto; intros.
  eexists; split; eauto.
  eexists _, _; split; [apply tp_update_refl|]; auto.
Qed.

Lemma state_bupd_intro : forall (P : _ -> Prop) m tr sch tp phi, join_all tp phi ->
  ext_compat tt phi ->
  P (m, (tr, sch, tp)) -> state_bupd P (m, (tr, sch, tp)).
Proof.
  intros; eapply tp_bupd_intro; eauto.
Qed.

Lemma state_bupd_intro' : forall Gamma n s,
  state_invariant Gamma n s ->
  state_bupd (state_invariant Gamma n) s.
Proof.
  inversion 1; subst.
  eapply state_bupd_intro; eauto.
  apply mcompat.
Qed.

Definition state_fupd P (state : cm_state) := let '(m, (tr, sch, tp)) := state in
  tp_fupd (fun tp' => P (m, (tr, sch, tp'))) tp.

Lemma cnt0 (tp : jstate ge) : containsThread tp O.
Proof.
  hnf.
  destruct (@ssrnat.leP 1 (pos.n (num_threads tp))); auto.
  destruct num_threads; simpl in *; lia.
Qed.

Lemma state_fupd_intro : forall (P : _ -> Prop) m tr sch tp phi, join_all tp phi ->
  ext_compat tt phi -> inv_compatible tp -> 
  P (m, (tr, sch, tp)) -> state_fupd P (m, (tr, sch, tp)).
Proof.
  intros; unfold state_fupd, tp_fupd.
  destruct (H1 _ (cnt0 _)) as (r & w & [m0 ?] & ? & ?).
  exists O, (cnt0 _), m0, r, w; repeat (split; auto).
  right; eapply tp_bupd_intro; eauto.
  exists (cnt0 _), m0, r, w; auto.
Qed.

Lemma state_fupd_intro' : forall Gamma n s,
  state_invariant Gamma n s ->
  state_fupd (state_invariant Gamma n) s.
Proof.
  inversion 1; subst.
  eapply state_fupd_intro; eauto.
  apply mcompat.
Qed.

Lemma mem_compatible_upd : forall tp m phi tp' phi', mem_compatible_with tp m phi ->
  tp_update(ge := ge) tp phi tp' phi' -> mem_compatible_with tp' m phi'.
Proof.
  intros ?????? (Hl & Hr & ? & ? & ? & Hguts & ? & ? & ?).
  inv H; constructor; auto.
  - inv all_cohere0; constructor.
    + repeat intro.
      rewrite Hr in H; eauto.
    + repeat intro; rewrite Hr; auto.
    + repeat intro; rewrite Hr; auto.
  - setoid_rewrite Hguts; auto.
  - setoid_rewrite Hguts; repeat intro.
    rewrite Hr in H; eauto.
  - setoid_rewrite Hguts; repeat intro.
    rewrite Hr; auto.
Qed.

Lemma join_all_eq : forall (tp : jstate ge) phi phi', join_all tp phi -> join_all tp phi' ->
  phi = phi'.
Proof.
  intros ???; rewrite join_all_joinlist.
  unfold maps.
  destruct (getThreadsR tp); [|intros; eapply joinlist_inj; eauto; discriminate].
  destruct (getLocksR tp); [auto | intros; eapply joinlist_inj; eauto; discriminate].
  simpl.
  intros (? & Hid1 & ?%join_comm%Hid1) (? & Hid2 & ?%join_comm%Hid2); subst; auto.
Qed.

Lemma funspec_sub_si_fash : forall a b, funspec_sub_si a b |-- !#funspec_sub_si a b.
Proof.
  intros; unfold funspec_sub_si.
  destruct a, b; repeat intro.
  destruct H; split; auto.
  intros ??.
  destruct (level a) eqn: Hl.
  { apply laterR_level in H2; lia. }
  symmetry in Hl; apply levelS_age in Hl as (a1 & ? & ?); subst.
  specialize (H1 a1); spec H1.
  { constructor; auto. }
  match goal with |-context[allp ?a] => remember (allp a) as pred end.
  simpl in *.
  eapply pred_nec_hereditary, H1.
  apply nec_nat.
  apply laterR_level in H2; lia.
Qed.

(* Ghost update only affects safety; the rest of the invariant is preserved. *)
(* Is this relevant anymore? *)
(*Lemma state_inv_bupd : forall Gamma (n : nat)
  (m : mem) (tr : event_trace) (sch : schedule) (tp : jstate ge) (PHI : rmap)
      (lev : level PHI = n)
      (envcoh : env_coherence Jspec ge Gamma PHI)
(*      (mwellformed: mem_wellformed m) *)
      (mcompat : mem_compatible_with tp m PHI)
      (extcompat : joins (ghost_of PHI) (Some (ext_ref tt, NoneP) :: nil))
      (lock_sparse : lock_sparsity (lset tp))
      (lock_coh : lock_coherence' tp PHI m mcompat)
      (safety : forall C, join_sub (Some (ext_ref tt, NoneP) :: nil) C ->
        joins (ghost_of PHI) (ghost_fmap (approx (level PHI)) (approx (level PHI)) C) ->
        exists tp' PHI' (Hupd : tp_update tp PHI tp' PHI'),
        joins (ghost_of PHI') (ghost_fmap (approx (level PHI)) (approx (level PHI)) C) /\
        threads_safety m tp' PHI' (mem_compatible_upd _ _ _ _ _ mcompat Hupd))
      (wellformed : threads_wellformed tp)
      (uniqkrun :  unique_Krun tp sch),
  state_bupd (state_invariant Gamma n) (m, (tr, sch, tp)).
Proof.
  intros.
  split; [eexists; split; eauto; apply mcompat|].
  intros ??? Hc J.
  assert (join_all tp PHI) as HPHI by (clear - mcompat; inv mcompat; auto).
  destruct (join_all_eq _ _ _ H HPHI) as [(Ht & ? & ? & ?)|].
  { exists nil; split.
    { eexists; constructor. }
    exists phi, tp; split; [apply tp_update_refl; auto|].
    split; [apply ghost_identity, ghost_of_identity; auto|].
    apply state_invariant_c with (mcompat := mcompat); auto.
    repeat intro.
    generalize (getThreadR_nth _ _ cnti); setoid_rewrite Ht; rewrite nth_error_nil; discriminate. }
  subst.
  specialize (safety _ Hc J) as (tp' & PHI' & Hupd & J' & safety).
  eexists; split; eauto; do 2 eexists; split; eauto; split; auto.
  pose proof (mem_compatible_upd _ _ _ _ _ mcompat Hupd) as mcompat'.
  destruct Hupd as (Hl & Hr & Hj & Hiff & Hthreads & Hguts & Hlset & Hres & Hlatest).
  apply state_invariant_c with (mcompat := mcompat').
  - auto.
  - destruct envcoh as [mtch coh]; split.
    + repeat intro.
      destruct (necR_same_level _ _ _ H0 Hl) as (PHIa & Hnec & Hla).
      destruct (mtch b b0 _ _ Hnec (ext_refl _)) as (? & ? & ? & ?).
      * destruct b0; simpl in *.
        pose proof (necR_level _ _ Hnec). pose proof (necR_level _ _ H0).
        apply necR_age_to in Hnec; rewrite Hnec, age_to_resource_at.age_to_resource_at.
        rewrite <- Hla, <- Hr.
        apply rmap_order in H1 as (Hl1 & Hr1 & _).
        rewrite <- Hl1, <- Hr1 in H2.
        apply necR_age_to in H0; rewrite H0, age_to_resource_at.age_to_resource_at in H2; rewrite H2.
        rewrite !level_age_to; auto; lia.
      * do 3 eexists; simpl in *; eauto.
        eapply funspec_sub_si_fash; eauto.
        apply rmap_order in H1 as (? & ? & ?); lia.
    + destruct coh as (? & ? & ? & ? & ? & ? & Happ).
      do 5 eexists; eauto; split; auto.
      eapply semax_lemmas.funassert_resource, Happ; auto.
  - auto.
  - eapply joins_comm, join_sub_joins_trans, joins_comm, J'.
    destruct Hc as [? Hc].
    eapply ghost_fmap_join in Hc; eexists; eauto.
  - repeat intro.
    setoid_rewrite Hguts in H0; setoid_rewrite Hguts in H1; auto.
  - repeat intro.
    specialize (lock_coh loc).
    simpl in Hguts.
    unfold OrdinalPool.lockGuts in Hguts.
    rewrite Hguts, Hl, Hr.
    destruct (AMap.find _ _); auto.
    assert (forall R, lkat R loc PHI -> lkat R loc PHI').
    { repeat intro; rewrite Hl, Hr; auto. }
    replace (load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget mcompat'))) loc)
      with (load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget mcompat))) loc).
    destruct o; repeat (split; try tauto).
    + destruct lock_coh as (? & ? & ? & ? & ? & ?); eauto.
    + destruct lock_coh as (? & ? & ? & ? & ?); eauto.
    + erewrite restrPermMap_irr'; [reflexivity | auto].
  - erewrite (proof_irr mcompat'); eauto.
  - repeat intro.
    pose proof (proj1 (Hiff _) cnti) as cnti0.
    destruct (Hthreads _ cnti0) as (HC & _).
    replace (proj2 (Hiff i) cnti0) with cnti in HC by (apply proof_irr).
    rewrite <- HC; apply wellformed.
  - repeat intro.
    pose proof (proj1 (Hiff _) cnti) as cnti0.
    destruct (Hthreads _ cnti0) as (HC & _).
    replace (proj2 (Hiff i) cnti0) with cnti in HC by (apply proof_irr).
    rewrite <- HC in *.
    replace (num_threads tp') with (num_threads tp) in *; eauto.
    symmetry; apply contains_iff_num; auto.
Qed.*)

(*(* Is this provable? *)
Lemma state_inv_fupd : forall Gamma (n : nat)
  (m : mem) (tr : event_trace) (sch : schedule) (tp : jstate ge) (PHI : rmap)
      (lev : level PHI = n)
      (envcoh : env_coherence Jspec ge Gamma PHI)
      (mwellformed: mem_wellformed m)
      (mcompat : mem_compatible_with tp m PHI)
      (extcompat : joins (ghost_of PHI) (Some (ext_ref tt, NoneP) :: nil))
      (lock_sparse : lock_sparsity (lset tp))
      (lock_coh : lock_coherence' tp PHI m mcompat)
      (safety : forall C, join_sub (Some (ext_ref tt, NoneP) :: nil) C ->
        joins (ghost_of PHI) (ghost_fmap (approx (level PHI)) (approx (level PHI)) C) ->
        exists tp' PHI' (Hupd : tp_update tp PHI tp' PHI'),
        joins (ghost_of PHI') (ghost_fmap (approx (level PHI)) (approx (level PHI)) C) /\
        threads_safety m tp' PHI' (mem_compatible_upd _ _ _ _ _ mcompat Hupd))
      (wellformed : threads_wellformed tp)
      (uniqkrun :  unique_Krun tp sch),
  state_fupd (state_invariant Gamma n) (m, (tr, sch, tp)).
Proof.
  intros.
  split; [eexists; split; eauto; apply mcompat|].
  intros ??? Hc J.
  assert (join_all tp PHI) as HPHI by (clear - mcompat; inv mcompat; auto).
  destruct (join_all_eq _ _ _ H HPHI) as [(Ht & ? & ? & ?)|].
  { exists nil; split.
    { eexists; constructor. }
    exists phi, tp; split; [apply tp_update_refl; auto|].
    split; [apply ghost_identity, ghost_of_identity; auto|].
    apply state_invariant_c with (mcompat := mcompat); auto.
    repeat intro.
    generalize (getThreadR_nth _ _ cnti); setoid_rewrite Ht; rewrite nth_error_nil; discriminate. }
  subst.
  specialize (safety _ Hc J) as (tp' & PHI' & Hupd & J' & safety).
  eexists; split; eauto; do 2 eexists; split; eauto; split; auto.
  pose proof (mem_compatible_upd _ _ _ _ _ mcompat Hupd) as mcompat'.
  destruct Hupd as (Hl & Hr & Hj & Hiff & Hthreads & Hguts & Hlset & Hres & Hlatest).
  apply state_invariant_c with (mcompat := mcompat').
  - auto.
  - destruct envcoh as [mtch coh]; split.
    + repeat intro.
      destruct (necR_same_level _ _ _ H0 Hl) as (PHIa & Hnec & Hla).
      destruct (mtch b b0 _ _ Hnec (ext_refl _)) as (? & ? & ? & ?).
      * destruct b0; simpl in *.
        pose proof (necR_level _ _ Hnec). pose proof (necR_level _ _ H0).
        apply necR_age_to in Hnec; rewrite Hnec, age_to_resource_at.age_to_resource_at.
        rewrite <- Hla, <- Hr.
        apply rmap_order in H1 as (Hl1 & Hr1 & _).
        rewrite <- Hl1, <- Hr1 in H2.
        apply necR_age_to in H0; rewrite H0, age_to_resource_at.age_to_resource_at in H2; rewrite H2.
        rewrite !level_age_to; auto; lia.
      * do 3 eexists; simpl in *; eauto.
        eapply funspec_sub_si_fash; eauto.
        apply rmap_order in H1 as (? & ? & ?); lia.
    + destruct coh as (? & ? & ? & ? & ? & ? & Happ).
      do 5 eexists; eauto; split; auto.
      eapply semax_lemmas.funassert_resource, Happ; auto.
  - auto.
  - eapply joins_comm, join_sub_joins_trans, joins_comm, J'.
    destruct Hc as [? Hc].
    eapply ghost_fmap_join in Hc; eexists; eauto.
  - repeat intro.
    setoid_rewrite Hguts in H0; setoid_rewrite Hguts in H1; auto.
  - repeat intro.
    specialize (lock_coh loc).
    simpl in Hguts.
    unfold OrdinalPool.lockGuts in Hguts.
    rewrite Hguts, Hl, Hr.
    destruct (AMap.find _ _); auto.
    assert (forall R, lkat R loc PHI -> lkat R loc PHI').
    { repeat intro; rewrite Hl, Hr; auto. }
    replace (load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget mcompat'))) loc)
      with (load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget mcompat))) loc).
    destruct o; repeat (split; try tauto).
    + destruct lock_coh as (? & ? & ? & ? & ? & ?); eauto.
    + destruct lock_coh as (? & ? & ? & ? & ?); eauto.
    + erewrite restrPermMap_irr'; [reflexivity | auto].
  - erewrite (proof_irr mcompat'); eauto.
  - repeat intro.
    pose proof (proj1 (Hiff _) cnti) as cnti0.
    destruct (Hthreads _ cnti0) as (HC & _).
    replace (proj2 (Hiff i) cnti0) with cnti in HC by (apply proof_irr).
    rewrite <- HC; apply wellformed.
  - repeat intro.
    pose proof (proj1 (Hiff _) cnti) as cnti0.
    destruct (Hthreads _ cnti0) as (HC & _).
    replace (proj2 (Hiff i) cnti0) with cnti in HC by (apply proof_irr).
    rewrite <- HC in *.
    replace (num_threads tp') with (num_threads tp) in *; eauto.
    symmetry; apply contains_iff_num; auto.
Qed.*)

End Machine.

Lemma restr_restr : forall m p Hlt p' Hlt', exists Hlt'',
  @restrPermMap p' (@restrPermMap p m Hlt) Hlt' = @restrPermMap p' m Hlt''.
Proof.
  intros.
  unshelve eexists.
  { rewrite restr_Max_eq in Hlt'; auto. }
  apply mem_lessdef.mem_ext; auto; simpl.
  f_equal.
  - extensionality o k; destruct k; auto.
  - apply PTree.extensionality; intros.
    rewrite !PTree.gmap.
    destruct (_ ! _); auto.
Qed.

Lemma maxedmem_restr : forall m p Hlt, maxedmem (@restrPermMap p m Hlt) = maxedmem m.
Proof.
  intros; unfold maxedmem.
  edestruct (restr_restr _ _ Hlt) as [? ->].
  apply restrPermMap_irr; auto.
  apply restr_Max_eq.
Qed.

Lemma mem_wellformed_restr : forall {ge} m p Hlt, @mem_wellformed ge m -> @mem_wellformed ge (@restrPermMap p m Hlt).
Proof.
  intros ???? []; unfold mem_wellformed; simpl.
  split; auto.
  rewrite maxedmem_restr; auto.
Qed.

Lemma maxedmem_storebytes : forall m b o v m', Mem.storebytes m b o v = Some m' -> Mem.storebytes (maxedmem m) b o v = Some (maxedmem m').
Proof.
  intros.
  edestruct (Mem.range_perm_storebytes (maxedmem m)).
  { apply Mem.storebytes_range_perm in H.
    intros ? Hrange; specialize (H _ Hrange).
    unfold Mem.perm, maxedmem in *.
    setoid_rewrite restrPermMap_Cur.
    rewrite getMaxPerm_correct; unfold permission_at.
    eapply perm_order_trans211, H.
    apply Mem.access_max. }
  rewrite e; f_equal.
  apply mem_lessdef.mem_ext; simpl.
  - erewrite Mem.storebytes_mem_contents, (Mem.storebytes_mem_contents _ _ _ _ m') by eauto; auto.
  - erewrite Mem.storebytes_access, (Mem.storebytes_access _ _ _ _ m') by eauto; simpl.
    f_equal.
    apply PTree.extensionality; intros.
    rewrite !PTree.gmap.
    destruct (_ ! _); auto; simpl.
    f_equal; extensionality ofs k.
    destruct k; auto.
    rewrite !getMaxPerm_correct; unfold permission_at.
    erewrite (Mem.storebytes_access _ _ _ _ m') by eauto; auto.
  - erewrite Mem.nextblock_storebytes, (Mem.nextblock_storebytes _ _ _ _ m') by eauto; auto.
Qed.

Lemma maxedmem_store : forall m c b o v m', Mem.store c m b o v = Some m' -> Mem.store c (maxedmem m) b o v = Some (maxedmem m').
Proof.
  intros.
  pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ H) as Hvalid.
  apply Mem.store_storebytes, maxedmem_storebytes in H.
  apply Mem.storebytes_store; auto.
  apply Hvalid.
Qed.

(*Lemma mem_wellformed_storebytes : forall {ge} m b o v m', list_forall2 (memval_inject (Mem.flat_inj (Mem.nextblock m))) v v ->
  Mem.storebytes m b o v = Some m' -> @mem_wellformed ge m -> @mem_wellformed ge m'.
Proof.
  intros ???????? []; unfold mem_wellformed.
  erewrite Mem.nextblock_storebytes by eauto.
  split; [|auto].
  apply maxedmem_storebytes in H0.
  eapply Mem.store_inject_neutral; eauto.
  apply Mem.storebytes_range_perm in H0.
  specialize (H0 o); spec H0.
  { rewrite encode_val_length. destruct (size_chunk_nat_pos c). lia. }
  pose proof (Mem.nextblock_noaccess (maxedmem m) b o Cur) as Haccess.
  unfold Mem.perm, maxedmem in *.
  pose proof (restrPermMap_Cur (mem_max_lt_max m) b o) as Hperm; unfold permission_at in *; rewrite Hperm, getMaxPerm_correct in *.
  destruct (plt b (Mem.nextblock m)); auto.
  autospec Haccess.
  rewrite Haccess in H0; inv H0.
Qed.*)

Lemma mem_wellformed_store : forall {ge} m c b o v m', Val.inject (Mem.flat_inj (Mem.nextblock m)) v v ->
  Mem.store c m b o v = Some m' -> @mem_wellformed ge m -> @mem_wellformed ge m'.
Proof.
  intros ????????? []; unfold mem_wellformed.
  erewrite Mem.nextblock_store by eauto.
  split; [|auto].
  apply maxedmem_store in H0.
  eapply Mem.store_inject_neutral; eauto.
  apply Mem.store_storebytes, Mem.storebytes_range_perm in H0.
  specialize (H0 o); spec H0.
  { rewrite encode_val_length. destruct (size_chunk_nat_pos c). lia. }
  pose proof (Mem.nextblock_noaccess (maxedmem m) b o Cur) as Haccess.
  unfold Mem.perm, maxedmem in *.
  pose proof (restrPermMap_Cur (mem_max_lt_max m) b o) as Hperm; unfold permission_at in *; rewrite Hperm, getMaxPerm_correct in *.
  destruct (plt b (Mem.nextblock m)); auto.
  autospec Haccess.
  rewrite Haccess in H0; inv H0.
Qed.

Lemma mem_wellformed_step : forall {ge} m m', mem_step m m' -> @mem_wellformed ge m -> @mem_wellformed ge m'.
Proof.
(* not true in general, because mem_step doesn't rule out storing invalid pointers *)
Abort.

(*Lemma mem_wellformed_step : forall {ge} m m' c c', cl_step ge c m c' m' -> @mem_wellformed ge m -> @mem_wellformed ge m'.
Proof.
  induction 1; auto; intros []; unfold mem_wellformed.
  - Search expr.valid_pointer.
Abort.*)

Ltac fixsafe H :=
  unshelve eapply jsafe_phi_jsafeN in H; eauto.

Ltac absurd_ext_link_naming :=
  exfalso;
  match goal with
  | H : Some (_ _, _) = _ |- _ =>
    rewrite <-H in *
  end;
  unfold funsig2signature in *;
  match goal with
  | H : Some (?ext_link ?a, ?b) <> Some (?ext_link ?a, ?b') |- _ =>
    simpl in H; [contradiction || congruence]
  | H : Some (?ext_link ?a, ?c) = Some (?ext_link ?b, ?d) |- _ =>
    simpl in H;
    match goal with
    | ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2 |- _ =>
      assert (a = b) by (apply ext_link_inj; congruence); congruence
    end
  end.

Ltac funspec_destruct s :=
  simpl (extspec.ext_spec_pre _); simpl (extspec.ext_spec_type _); simpl (extspec.ext_spec_post _);
  unfold funspec2pre, funspec2post;
  let Heq_name := fresh "Heq_name" in
  destruct (oi_eq_dec (Some (_ s, _)) (ef_id_sig _ (EF_external _ _)))
    as [Heq_name | Heq_name]; try absurd_ext_link_naming.

(* if a hypothesis if of the form forall a1 a2 a3 a4 ...,
"forall_bringvar 3" will move a3 as the first variable, i.e. forall a3
a1 a2 a4..., assuming the operation is legal wrt dependent types *)

(* This allows us to define "specialize H _ _ _ term" below *)

Tactic Notation "forall_bringvar" "2" hyp(H) :=
  match type of H with
    (forall a : ?A, forall b : ?B, ?P) =>
    let H' := fresh "H" in
    assert (H' : forall b : B, forall a : A, P)
      by (intros; eapply H; eauto);
    move H' after H;
    clear H; rename H' into H
  end.

Tactic Notation "forall_bringvar" "2" hyp(H) :=
  match type of H with
    (forall a : ?A, forall b : ?B, ?P) =>
    let H' := fresh "H" in
    assert (H' : forall b : B, forall a : A, P)
      by (intros; eapply H; eauto);
    move H' after H;
    clear H; rename H' into H
  end.

Tactic Notation "forall_bringvar" "3" hyp(H) :=
  match type of H with
    (forall a : ?A, forall b : ?B, forall c : ?C, ?P) =>
    let H' := fresh "H" in
    assert (H' : forall c : C, forall a : A, forall b : B, P)
      by (intros; eapply H; eauto);
    move H' after H;
    clear H; rename H' into H
  end.

Tactic Notation "forall_bringvar" "4" hyp(H) :=
  match type of H with
    (forall a : ?A, forall b : ?B, forall c : ?C, forall d : ?D, ?P) =>
    let H' := fresh "H" in
    assert (H' : forall d : D, forall a : A, forall b : B, forall c : C, P)
      by (intros; eapply H; eauto);
    move H' after H;
    clear H; rename H' into H
  end.

Tactic Notation "forall_bringvar" "5" hyp(H) :=
  match type of H with
    (forall a : ?A, forall b : ?B, forall c : ?C, forall d : ?D, forall e : ?E, ?P) =>
    let H' := fresh "H" in
    assert (H' :  forall e : E, forall a : A, forall b : B, forall c : C, forall d : D, P)
      by (intros; eapply H; eauto);
    move H' after H;
    clear H; rename H' into H
  end.

Tactic Notation "forall_bringvar" "6" hyp(H) :=
  match type of H with
    (forall a : ?A, forall b : ?B, forall c : ?C, forall d : ?D, forall e : ?E, forall f : ?F, ?P) =>
    let H' := fresh "H" in
    assert (H' :  forall f : F, forall a : A, forall b : B, forall c : C, forall d : D, forall e : E, P)
      by (intros; eapply H; eauto);
    move H' after H;
    clear H; rename H' into H
  end.

Tactic Notation "specialize" hyp(H) "_" constr(t) :=
  forall_bringvar 2 H; specialize (H t).

Tactic Notation "specialize" hyp(H) "_" "_" constr(t) :=
  forall_bringvar 3 H; specialize (H t).

Tactic Notation "specialize" hyp(H) "_" "_" "_" constr(t) :=
  forall_bringvar 4 H; specialize (H t).

Tactic Notation "specialize" hyp(H) "_" "_" "_" "_" constr(t) :=
  forall_bringvar 5 H; specialize (H t).

Tactic Notation "specialize" hyp(H) "_" "_" "_" "_" "_" constr(t) :=
  forall_bringvar 6 H; specialize (H t).
