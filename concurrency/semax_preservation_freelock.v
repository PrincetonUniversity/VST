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

Lemma preservation_freelock
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
  (m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp : thread_pool)
  (Phi : rmap)
  (lev : level Phi = S n)
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (sparse : lock_sparsity (lset tp))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei cnti : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (ci : code)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (c : code)
  (b : block)
  (ofs : int)
  (R : pred rmap)
  (phi' : rmap)
  (sh : Share.t)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (FREE_LOCK, Vptr b ofs :: nil))
  (Hcompatible : mem_compatible tp m')
  (Haccess : (address_mapsto Mint32 (Vint Int.zero) sh Share.top (b, Int.intval ofs)) phi')
  (Hlock' : exists val : memval, phi' @ (b, Int.intval ofs) = YES sh pfullshare (VAL val) NoneP)
  (INV : state_invariant Jspec' Gamma (S n) (m', ge, (i :: sch, tp)))
  (compat : mem_compatible_with tp m' Phi)
  (lock_coh : lock_coherence' tp Phi m' compat)
  (safety : threads_safety Jspec' m' ge tp Phi compat (S n))
  (Hcmpt : mem_compatible tp m')
  (compat_aged : mem_compatible_with (age_tp_to n tp) m' (age_to n Phi))
  (Hlock : getThreadR i tp Htid @ (b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
  (Hct : forall ofs' : Z,
        (Int.intval ofs < ofs' < Int.intval ofs + LKSIZE)%Z ->
        exists (val : memval),
          getThreadR i tp Htid @ (b, ofs') = YES sh pfullshare (CT (ofs' - Int.intval ofs)%Z) NoneP /\
          phi' @ (b, ofs') = YES sh pfullshare (VAL val) NoneP)
  (Hj_forward : forall loc : block * Z,
               b <> fst loc \/ ~ (Int.intval ofs <= snd loc < Int.intval ofs + LKSIZE)%Z ->
               getThreadR i tp Htid @ loc = phi' @ loc)
  (tp_ := age_tp_to (level (getThreadR i tp Htid) - 1)
           (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs)) : thread_pool)
  (compat_ := mem_compatible_with tp_ m' (age_to n Phi) : Prop)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m' sch nil
             (age_tp_to n
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))) m')
  (Htstep : syncStep ge Htid Hcmpt
             (age_tp_to n
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))) m'
             (Events.freelock (b, Int.intval ofs))) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m', ge, (sch, (age_tp_to n
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))))).

Proof.
Admitted.
