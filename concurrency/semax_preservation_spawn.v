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

Lemma preservation_spawn
  (lockSet_Writable_updLockSet_updThread
     : forall (m m' : Memory.mem) (i : tid) (tp : thread_pool),
       forall (cnti : containsThread tp i) (b : block) (ofs : int) (ophi : option rmap)
         (ophi' : LocksAndResources.lock_info) (c' : ctl) (phi' : LocksAndResources.res) 
         (z : int) (Hcmpt : mem_compatible tp m)
         (Hcmpt : mem_compatible tp m)
         (His_unlocked : AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi)
         (Hlt' : permMapLt
              (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
                 LKSIZE_nat) (getMaxPerm m))
         (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint z) = Some m'),
       lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Int.intval ofs) ophi')) m') 
  (mem_cohere'_store : forall m tp m' b ofs j i Phi (cnti : containsThread tp i)
    (Hcmpt : mem_compatible tp m)
    (lock : lockRes tp (b, Int.intval ofs) <> None)
    (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
    (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint j) = Some m'),
    mem_compatible_with tp m Phi ->
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
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (c c_new : code)
  (arg : val)
  (d_phi phi' : rmap)
  (b : block)
  (ofs : int)
  (P Q : pred rmap)
  (Hcompatible : mem_compatible tp m')
  (p : forall ts: list Type, JMem.AType -> pred rmap)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hget_fun_spec : JMem.get_fun_spec p = Some (P, Q))
  (Hsat_fun_spec : P d_phi)
  (Halmost_empty : almost_empty d_phi)
  (INV : state_invariant Jspec' Gamma (S n) (m', ge, (i :: sch, tp)))
  (compat : mem_compatible_with tp m' Phi)
  (lock_coh : lock_coherence' tp Phi m' compat)
  (safety : threads_safety Jspec' m' ge tp Phi compat (S n))
  (Hcmpt : mem_compatible tp m')
  (compat_aged : mem_compatible_with (age_tp_to n tp) m' (age_to n Phi))
  (Hget_fun_spec' : JMem.get_fun_spec'
                     (personal_mem m' (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid))
                     (b, Int.intval ofs) arg =
                   Some (existT (fun A: rmaps.TypeTree => forall ts : list Type, rmaps.dependent_type_functor_rec ts A (pred rmap)) (rmaps.ArrowType (rmaps.ConstType JMem.AType) rmaps.Mpred) p))
  (Hrem_fun_res : join d_phi phi'
                   (m_phi (personal_mem m' (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid))))
  (Hat_external : at_external SEM.Sem c = Some (CREATE, Vptr b ofs :: arg :: nil))
  (Hinitial : initial_core SEM.Sem ge (Vptr b ofs) (arg :: nil) = Some c_new)
  (tp_ := addThread (updThread i tp Htid (Kresume c Vundef) phi') (Vptr b ofs) arg d_phi : thread_pool)
  (compat_ := mem_compatible_with tp_ m_ (age_to n Phi) : Prop)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m' sch nil
             (addThread (updThread i tp Htid (Kresume c Vundef) phi') (Vptr b ofs) arg d_phi) m')
  (Htstep : syncStep true ge Htid Hcmpt
             (addThread (updThread i tp Htid (Kresume c Vundef) phi') (Vptr b ofs) arg d_phi) m'
             (Events.spawn (b, Int.intval ofs) None None)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).
  
Proof.
Admitted. (* preservation_spawn *)
