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
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.juicy_safety.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import floyd.coqlib3.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.coqlib5.
Require Import concurrency.permjoin.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.
Require Import concurrency.age_to.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.sync_preds.
Require Import concurrency.join_lemmas.
Require Import concurrency.aging_lemmas.
Require Import concurrency.cl_step_lemmas.
Require Import concurrency.resource_decay_lemmas.
Require Import concurrency.resource_decay_join.
Require Import concurrency.semax_invariant.
Require Import concurrency.semax_simlemmas.
Require Import concurrency.sync_preds.
Require Import concurrency.lksize.
Require Import concurrency.rmap_locking.

Local Arguments getThreadR : clear implicits.
Local Arguments getThreadC : clear implicits.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread : clear implicits.
Local Arguments updThreadR : clear implicits.
Local Arguments updThreadC : clear implicits.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Lemma preservation_makelock
  (lockSet_Writable_updLockSet_updThread
     : forall (m m' : Memory.mem) (i : tid) (tp : thread_pool) (Phi : LocksAndResources.res),
       mem_compatible_with tp m Phi ->
       forall (cnti : containsThread tp i) (b : block) (ofs : int) (ophi : option rmap)
         (ophi' : LocksAndResources.lock_info) (c' : ctl) (phi' : LocksAndResources.res) 
         (z : int) (pr : mem_compatible tp m),
       AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi ->
       Mem.store Mint32 (restrPermMap (mem_compatible_locks_ltwritable pr)) b (Int.intval ofs) (Vint z) = Some m' ->
       lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Int.intval ofs) ophi')) m') 
  (mem_cohere'_store : forall m tp m' b ofs i Phi
    (Hcmpt : mem_compatible tp m),
    lockRes tp (b, Int.intval ofs) <> None ->
    Mem.store
      Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcmpt))
      b (Int.intval ofs) (Vint i) = Some m' ->
    mem_compatible_with tp m Phi (* redundant with Hcmpt, but easier *) ->
    mem_cohere' m' Phi)
  (personal_mem_equiv_spec
     : forall (m m' : Mem.mem') (phi : rmap) (pr : mem_cohere' m phi) (pr' : mem_cohere' m' phi),
       Mem.nextblock m = Mem.nextblock m' ->
       (forall loc : address, max_access_at m loc = max_access_at m' loc) ->
       (forall loc : AV.address, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
       mem_equiv (m_dry (personal_mem m phi pr)) (m_dry (personal_mem m' phi pr')))
  (CS : compspecs)
  (ext_link : string -> ident)
  (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
  (Jspec' := @OK_spec (Concurrent_Espec unit CS ext_link))
  (Jspec'_juicy_mem_equiv : Jspec'_juicy_mem_equiv_def CS ext_link)
  (Jspec'_hered : Jspec'_hered_def CS ext_link)
  (Gamma : PTree.t funspec)
  (n : nat)
  (ge : SEM.G)
  (m m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp tp' : thread_pool)
  (INV : state_invariant Jspec' Gamma (S n) (m, ge, (i :: sch, tp)))
  (Phi : rmap)
  (compat : mem_compatible_with tp m Phi)
  (lev : level Phi = S n)
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (sparse : lock_sparsity (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : threads_safety Jspec' m ge tp Phi compat (S n))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei cnti : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (ci : code)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (ev : Events.sync_event)
  (Hcmpt : mem_compatible tp m)
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (Htstep : syncStep ge Htid Hcmpt tp' m' ev)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m')
  (tp_ := tp' : thread_pool)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (tp'0 tp'' : thread_pool)
  (jm : juicy_mem)
  (c : code)
  (b : block)
  (ofs : int)
  (R : pred rmap)
  (phi' : rmap)
  (m'0 : Memory.mem)
  (Hcompatible : mem_compatible tp m)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (MKLOCK, Vptr b ofs :: nil))
  (* (Hright_juice : m = m_dry jm) *)
  (Hpersonal_perm : personal_mem m (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid) = jm)
  (Hpersonal_juice : getThreadR i tp Htid = m_phi jm)
  (Hstore : Mem.store Mint32 (m_dry jm) b (Int.intval ofs) (Vint Int.zero) = Some m')
  (Hrmap : rmap_makelock (getThreadR i tp cnti) phi' (b, Int.unsigned ofs) R LKSIZE)
  (Htp' : tp'0 = updThread i tp Htid (Kresume c Vundef) phi')
  (Htp'' : tp' = age_tp_to (level (m_phi jm) - 1) (updLockSet tp'0 (b, Int.intval ofs) None))
  (H : tp'' = tp')
  (H0 : m'0 = m')
  (H1 : Events.mklock (b, Int.intval ofs) = ev) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).

Proof.
    (* now much easier with rmap_makelock.
    (* we must define the new Phi *)
    
    Definition rmap_makelock phi phi' sh loc R :=
      (forall x, ~ adr_range loc LKSIZE x -> phi @ x = phi' @ x) /\
      (forall x, adr_range loc LKSIZE x -> exists val, phi @ x = YES sh pfullshare (VAL val) NoneP) /\
      (LKspec_ext R fullshare fullshare loc phi').
    Definition rmap_freelock phi phi' sh loc R :=
      (forall x, ~ adr_range loc LKSIZE x -> phi @ x = phi' @ x) /\
      (LKspec_ext R fullshare fullshare loc phi) /\
      (forall x, adr_range loc LKSIZE x -> exists val, phi' @ x = YES sh pfullshare (VAL val) NoneP).
    
    assert (HPhi' : exists Phi', rmap_makelock Phi Phi' sh (b, Int.intval ofs) R). {
(*      pose (f' :=
              fun loc =>
                if adr_range_dec (b, Int.intval ofs) LKSIZE loc then
                  if eq_dec (Int.intval ofs) (snd loc) then
                    LK  *)
      admit.
    }
    destruct HPhi' as (Phi' & HPhi').
    
    subst m_ tp' tp'0 m'0.
    pose (tp2 := (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None)).
    fold tp2 in H.
    assert (compat' : mem_compatible_with tp2 m' Phi'). {
      unfold tp2.
      (*
      below, without the modification of the Phi'
      rewrite <-Hpersonal_juice.
      rewrite El.
      constructor.
      - (* joining to global map: the acquired rmap move from
            lockset to threads's maps *)
        pose proof juice_join compat as J.
        apply join_all_age_to. cleanup. omega.
        rewrite join_all_joinlist in J |- *.
        rewrite maps_updlock1.
        rewrite maps_remLockSet_updThread.
        rewrite maps_updthread.
        erewrite (maps_getthread i _ Htid) in J; eauto.
        clear -J Hct0 Hct Hj_forward Hpersonal_juice lock_coh levphi' Hlock.
        rewrite maps_getlock1; swap 1 2. {
          specialize (lock_coh (b, Int.intval ofs)).
          cleanup.
          destruct (AMap.find _ _) as [o|]; auto. exfalso.
          specialize (Hct (Int.intval ofs)).
          assert_specialize Hct. split. omega. unfold LKSIZE; simpl. omega.
          destruct Hct as (val & sh'' & E).
          assert (j : join_sub (getThreadR i tp Htid) Phi) by apply compatible_threadRes_sub, compat.
          destruct j as (?, j).
          apply resource_at_join with (loc := (b, Int.intval ofs)) in j.
          rewrite Hpersonal_juice in j.
          rewrite E in j.
          destruct o.
          - destruct lock_coh as (_ & sh' & R' & lk & _).
            apply predat2 in lk.
            unfold predat in *.
            inv j; breakhyps.
          - destruct lock_coh as (_ & sh' & R' & lk).
            apply predat2 in lk.
            unfold predat in *.
            inv j; breakhyps.
        }
        destruct J as (psi & j1 & j2).
        exists psi; split; auto.
        apply resource_at_join2.
        + rewrite levphi'. rewrite <-Hpersonal_juice. join_level_tac.
        + join_level_tac.
        + intros (b', ofs').
          rewrite Hpersonal_juice in j2.
          apply resource_at_join with (loc := (b', ofs')) in j2.
          specialize (Hj_forward (b', ofs')). simpl in Hj_forward.
          destruct (adr_range_dec (b, Int.intval ofs) 4 (b', ofs')) as [a|a]; swap 1 2.
          * assert_specialize Hj_forward. 2:congruence.
            unfold adr_range in *.
            unfold LKSIZE in *.
            simpl. cut ( b <> b' \/ ~ (Int.intval ofs <= ofs' < Int.intval ofs + 4)%Z). admit. (* wtf machine *)
            tauto.
          * unfold adr_range in *.
            destruct a as [<- a].
            specialize (Hct ofs'). autospec Hct.
            destruct Hct as (val & sh' & E).
            rewrite E in j2.
            destruct (eq_dec ofs' (Int.intval ofs)) as [e|e].
            -- subst ofs'.
               rewrite Hlock.
               inv j2.
               ++ (* NOT THE SAME PHI *)
                 admit.
       *) *)
Admitted.
