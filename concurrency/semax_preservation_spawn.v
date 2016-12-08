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
Require Import msl.age_to.
Require Import veric.aging_lemmas.
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
Require Import veric.age_to_resource_at.
Require Import veric.seplog.
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
Require Import concurrency.sync_preds_defs.
Require Import concurrency.sync_preds.
Require Import concurrency.join_lemmas.
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
  (Gamma : funspecs)
  (n : nat)
  (ge : SEM.G)
  (m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp : thread_pool)
  (Phi : rmap)
  (lev : level Phi = S n)
  (gam : matchfunspecs ge Gamma Phi)
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
                     (m_phi (personal_mem m' (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid)))
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
Abort. (* preservation_spawn *)

Lemma shape_of_args2 (F V : Type) (args : list val) v (ge : Genv.t F V) :
  Val.has_type_list args (sig_args (ef_sig CREATE)) ->
  v <> Vundef ->
  v =
  expr.eval_id _args (make_ext_args (filter_genv (symb2genv (Genv.genv_symb ge))) (_f :: _args :: nil) args) ->
  exists arg1, args = arg1 :: v :: nil.
Proof.
  intros Hargsty Nu.
  assert (L: length args = 2%nat) by (destruct args as [|? [|? [|]]]; simpl in *; tauto).
  unfold expr.eval_id.
  unfold expr.force_val.
  intros Preb.
  match goal with H : context [Map.get ?a ?b] |- _ => destruct (Map.get a b) eqn:E end.
  subst v. 2: tauto.
  pose  (gx := (filter_genv (symb2genv (Genv.genv_symb ge)))). fold gx in E.
  destruct args as [ | arg [ | ar [ | ar2 args ] ]].
  + now inversion E.
  + now inversion E.
  + simpl in E. inversion E. eauto.
  + inversion E. f_equal.
    inversion L.
Qed.

Lemma shape_of_args3 (F V : Type) (args : list val) v (ge : Genv.t F V) :
  Val.has_type_list args (sig_args (ef_sig CREATE)) ->
  v <> Vundef ->
  v =
  expr.eval_id _f (make_ext_args (filter_genv (symb2genv (Genv.genv_symb ge))) (_f :: _args :: nil) args) ->
  exists arg2, args = v :: arg2 :: nil.
Proof.
  intros Hargsty Nu.
  assert (L: length args = 2%nat) by (destruct args as [|? [|? [|]]]; simpl in *; tauto).
  unfold expr.eval_id.
  unfold expr.force_val.
  intros Preb.
  match goal with H : context [Map.get ?a ?b] |- _ => destruct (Map.get a b) eqn:E end.
  subst v. 2: tauto.
  pose  (gx := (filter_genv (symb2genv (Genv.genv_symb ge)))). fold gx in E.
  destruct args as [ | arg [ | ar [ | ar2 args ] ]].
  + now inversion E.
  + now inversion E.
  + simpl in E. inversion E. eauto.
  + inversion E. f_equal.
    inversion L.
Qed.

Lemma safety_induction_spawn Gamma n state
  (CS : compspecs)
  (ext_link : string -> ident)
  (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
  (Jspec' := @OK_spec (Concurrent_Espec unit CS ext_link))
  (Jspec'_juicy_mem_equiv : Jspec'_juicy_mem_equiv_def CS ext_link)
  (Jspec'_hered : Jspec'_hered_def CS ext_link)
  (personal_mem_equiv_spec :
     forall (m m' : Mem.mem') (phi : rmap) (pr : mem_cohere' m phi) (pr' : mem_cohere' m' phi),
       Mem.nextblock m = Mem.nextblock m' ->
       (forall loc : address, max_access_at m loc = max_access_at m' loc) ->
       (forall loc : AV.address, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
       mem_equiv (m_dry (personal_mem m phi pr)) (m_dry (personal_mem m' phi pr'))) :
  blocked_at_external state CREATE ->
  state_invariant Jspec' Gamma (S n) state ->
  exists state',
    state_step state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  intros isspawn I.
  inversion I as [m ge sch_ tp Phi En SP gam compat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct isspawn as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.
  
    
  rewrite Eci in safei.
  unfold jsafeN, juicy_safety.safeN in safei.
  
  fixsafe safei.
  inversion safei
    as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
    [ now erewrite cl_corestep_not_at_external in atex; [ discriminate | eapply bad ]
    | subst | now inversion bad ].
  subst.
  simpl in at_ex. assert (args0 = args) by congruence; subst args0.
  assert (e = CREATE) by congruence; subst e.
  hnf in x.
  revert x Pre SafePost.
  
  assert (H_spawn : Some (ext_link "spawn", ef_sig CREATE) = ef_id_sig ext_link CREATE). reflexivity.
  
  (* dependent destruction *)
  funspec_destruct "acquire".
  funspec_destruct "release".
  funspec_destruct "makelock".
  funspec_destruct "freelock".
  funspec_destruct "spawn".
  
  intros (phix, (ts, ((xf, xarg), (f_with_ty & f_with_x & f_with_Pre)))) (Hargsty, Pre).
  intros Post.
  simpl in Pre. clear Post.
  destruct Pre as (phi0 & phi1 & jphi & A).
  destruct A as ((PreA & (PreB1 & PreB2) & phi00 & phi01 & jphi0 & (_y & Glob & Func) & fPRE) & necr).
  simpl in fPRE.
  rewrite seplog.sepcon_emp in fPRE.
  simpl in PreA. clear PreA.
  simpl in PreB1.
  unfold liftx in PreB1. simpl in PreB1. unfold lift in PreB1.
  unfold liftx in PreB2. simpl in PreB2. unfold lift in PreB2. destruct PreB2 as [PreB2 _].
  
  Import SeparationLogicSoundness.SoundSeparationLogic.CSL.
  destruct Func as (Func, emp00).
  pose proof func_ptr_isptr _ _ _ Func as isp.
  unfold expr.isptr in *.
  destruct xf as [ | | | | | f_b f_ofs]; try contradiction.
  
  apply shape_of_args2 in PreB1; auto. 2: admit (* extra goal: xarg <> Vundef *).
  apply shape_of_args3 in PreB2; auto. 2: clear; congruence.
  destruct PreB1 as (arg1, Eargs).
  destruct PreB2 as (arg2, Eargs').
  rewrite Eargs in Eargs'. injection Eargs' as -> <-. subst args.
  simpl in Hargsty.
  
  (* done above
  spec safety i cnti tt. rewrite Eci in safety.
  destruct ci as [ | ef args0 lid ve te k] eqn:Heqci. discriminate.
  assert (args0 = args) by (simpl in atex; congruence). subst args0.
   *)
  
  destruct SP as (prog & CS_ & V & semaxprog & Ege).
  (*
  assert (prog : Clight.program) by admit.
  unfold threads_safety in *.
  (* maybe keep fdecs instead of Gamma (and Gamma = make_tycontext_s fdecs) *)
  (* assert (semaxprog : @semax_prog (Concurrent_Espec unit CS ext_link) CS prog nil fdecs) by admit. *)
  assert (semaxprog :  semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog nil Gamma) by admit.
  *)
  
  unfold SeparationLogic.NDmk_funspec in Func.
  match type of Func with
    context [mk_funspec ?fsig_ ?cc_ ?A_ ?P_ ?Q_ ?NEP_ ?NEQ_] =>
    set (fsig := fsig_); set (cc := cc_); set (A := A_);
      set (P := P_); set (Q := Q_);
      set (NEP := NEP_); set (NEQ := NEQ_)
  end.
  
  assert (gam0 : matchfunspecs ge Gamma phi00). {
    revert gam. apply pures_same_matchfunspecs.
    join_level_tac.
    apply pures_same_sym, join_sub_pures_same.
    apply join_sub_trans with phi0. exists phi01. auto.
    apply join_sub_trans with (getThreadR i tp cnti). exists phi1. auto.
    join_sub_tac.
  }
  
  spec gam0 f_b ((_y, tptr tvoid) :: nil, tptr tvoid) cc_default .
  Lemma func_at_func_at'' fs loc phi :
    seplog.func_at fs loc phi =
    match fs with mk_funspec fsig cc A P Q _ _ => func_at'' fsig cc A P Q loc phi end.
  Proof.
    destruct fs; auto.
  Qed.
  Import SeparationLogicSoundness.SoundSeparationLogic.CSL.
  assert (RR:
            func_ptr = 
            fun (f : funspec) (v : val) =>
              (EX b : block, !! (v = Vptr b Int.zero) && seplog.func_at f (b, 0%Z))%logic).
  admit (* we can add that to the CSL interface, but maybe it's better to change statements of lemmas *).
  rewrite RR in Func.
  
  destruct Func as (b' & E' & FAT). injection E' as <- ->.
  
  (* pose proof FAT as FAT'. *)
  unfold SeparationLogic.NDmk_funspec in *.
  
  specialize (gam0 _ _ _ FAT).
  destruct gam0 as (id_fun & P' & Q' & NEP' & NEQ' & Eb & Eid & Heq_P & Heq_Q).
  unfold filter_genv in *.
  
  pose proof semax_prog_entry_point (Concurrent_Espec unit CS ext_link) V Gamma prog f_b
       id_fun _y xarg(*?*) (* ((_y, tptr tvoid) :: nil) *) A P' Q' NEP' NEQ' semaxprog as HEP.
  
  subst ge.
  rewrite <-make_tycontext_s_find_id in HEP.
  spec HEP. auto.
  
  spec HEP. {
    change (Tpointer Tvoid noattr) with (tptr tvoid).
    replace Tvoid with (tptr tvoid) by admit. (* type mismatch *)
    replace (tptr (tptr tvoid)) with (tptr tvoid) by admit. (* ... replace at didnt work *)
    unfold A.
    rewrite <-Eid.
    apply make_tycontext_s_find_id.
  }
  
  spec HEP. {
    (* here Q' is related to Q through Heq_Q, and Q is "emp". *)
    (* obviously emp does not imply false, so we'll have to change that in semax_conc *)
    
    (* adding a {emp}exit{FF} does not help, because the frame rule
    also applies on exit.  But exit is a more desirable solution
    rather than just returning from the function anyway. Maybe we can
    make do with {emp}, but we leave that for later *)
    admit.
  }
  
  spec HEP.
  { clear -Hargsty. destruct Hargsty as (_ & T & _).
    (* no way to ensure xarg is a pointer or null.  That's because of
    the typechecking required by semax_call_aux. *)
    admit. }
  
  destruct HEP as (q_new & Initcore & Safety).
  
  (*
  apply semax_call.func_at_func_at' in FAT.
  specialize (FA2 _ _ _ (necR_refl _) FAT).
  destruct FA2 as (id & Eid & fs' & Efs).
  specialize (FA1 id fs' _ (necR_refl _) Efs).
  destruct FA1 as (b_ & Eb & Efs').
  hnf in Eb, Eid.
  inversion2 Eid Eb.
  simpl in Eid.
  *)  
  change (initial_core (juicy_core_sem cl_core_sem)) with cl_initial_core in Initcore.
  
  eexists.
  split.
  {
    apply state_step_c.
    unshelve eapply JuicyMachine.sync_step
    with (tid := i)
           (Htid := cnti)
           (ev := Events.spawn (f_b, Int.intval Int.zero) None None).
    { eexists; eauto. }
    { reflexivity. }
    { reflexivity. }
    eapply step_create with
    (c_new := q_new)
      (Hcompatible := mem_compatible_forget compat)
      (phi' := phi1)
      (d_phi := phi01)
    .
    now constructor.
    eassumption.
    { unfold SEM.Sem in *.
      rewrite SEM.CLN_msem.
      apply atex. }
    { replace (initial_core SEM.Sem) with cl_initial_core
        by (unfold SEM.Sem; rewrite SEM.CLN_msem; reflexivity).
      unfold code in *.
      rewrite <-Initcore.
      reflexivity. }
    reflexivity.
    reflexivity.
    
    (* no, bad machine. one should use func_at'' or something similar *)
    admit. admit.
    
    (* why?? *) admit.
    
    (* we said we'd remove almost_empty *) admit.
    
    (* join *)
    simpl. auto.
    cut (phi01 = phi0). intros ->; assumption.
    clear -emp00 jphi0.
    eapply join_unit1_e; eauto.
    apply emp00.
    
    reflexivity.
    reflexivity.
  }
  (* "progress" part finished. *)
  
  right. (* eventually we'll have to consume a step, at least because
  of the safety of the spawner, so we'll have to change the machine *)
  
  assert (mcompat' :
            mem_compatible_with
              (addThread (updThread i tp cnti (Kresume ci Vundef) phi1)
                         (Vptr f_b Int.zero) xarg phi01) m Phi).
  {
    admit.
  }
  
  (* apply (@mem_compatible_with_age n) in mcompat'. *)
  
  apply state_invariant_c with (mcompat := mcompat').
  
  - (* level *)
    auto.
  
  - (* semaxprog *)
    inv I; auto.
  
  - (* matchfunspecs *)
    auto.
  
  - (* lock sparsity *)
    auto.
  
  - (* lock coherence *)
    unfold lock_coherence' in *.
    simpl.
    exact_eq lock_coh.
    f_equal.
    f_equal.
    apply proof_irr.
  
  - (* thread_safety :
       - new thread #n+1 (spawned),
       - thread #i (after spawning),
       - other threads *)
    intros j lj ora.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    
    + (* safety of new thread *)
      subst j.
      rewrite gssAddCode. 2:reflexivity.
      exists f_b. eexists.
      split; auto.
      (* we should add to Kinit the fact that "there is an
      initial_core" or whatever is needed to prove the safety of
      Kinit *)
      admit.
    
    + (* safety of spawning thread *)
      subst j.
      REWR.
      REWR.
      admit (* stuff to do *).
    
    + assert (cntj : containsThread tp j). (* some boring arithmetic. *) admit.
      specialize (safety j cntj ora).
      REWR.
      REWR.
      destruct (getThreadC j tp cntj) eqn:Ej.
      -- edestruct (unique_Krun_neq i j); eauto.
      -- unshelve erewrite gsoAddRes; auto. REWR.
         (* when aging: apply jsafe_phi_age_to; auto. apply jsafe_phi_downward. assumption. *)
      -- intros c' Ec'; spec safety c' Ec'. unshelve erewrite gsoAddRes; auto. REWR.
         (* when aging: apply jsafe_phi_age_to; auto. apply jsafe_phi_downward. assumption. *)
      -- auto.
  
  - (* wellformed *)
    admit.
  
  - (* unique_Krun *)
    admit.
Admitted. (* safety_induction_spawn *)



(*
  
      f_equal.
      unfold cl_initial_core in *.
      simpl.
      Transparent func_ptr.
      assert (prog : Clight.program) by admit.
      unfold threads_safety in *.
      (* maybe keep fdecs instead of Gamma (and Gamma = make_tycontext_s fdecs) *)
      pose (fdecs := PTree.elements Gamma).
      assert (semaxprog : @semax_prog (Concurrent_Espec unit CS ext_link) CS prog nil fdecs) by admit.
      assert (FA : forall ve te, app_pred (seplog.funassert (nofunc_tycontext nil fdecs)
                                     (mkEnviron (filter_genv (globalenv prog)) ve te))
                                     Phi). admit.
      specialize (FA (fun _ => None) (fun _ => None)).
      destruct FA as (FA1, FA2).
      
      assert (RR:
      func_ptr = 
      fun (f : funspec) (v : val) =>
        (EX b : block, !! (v = Vptr b Int.zero) && seplog.func_at f (b, 0%Z))%logic).
      admit (* we can add that to the CSL interface, but maybe it's better to change statements of lemmas *).
      
      rewrite RR in Func; clear RR.
      
      destruct Func as (b' & E' & FAT). injection E' as <- ->.
      if_tac [_|?]. 2:tauto.
      
      assert (gam0 : matchfunspecs (filter_genv ge) Gamma phi00). {
        revert gam. apply pures_same_matchfunspecs.
        join_level_tac.
        apply pures_same_sym, join_sub_pures_same.
        apply join_sub_trans with phi0. exists phi01. auto.
        apply join_sub_trans with (getThreadR i tp cnti). exists phi1. auto.
        join_sub_tac.
      }
      
      spec gam0 f_b ((_y, tptr tvoid) :: nil, tptr tvoid) cc_default .
      Lemma func_at_func_at'' fs loc phi :
        seplog.func_at fs loc phi =
        match fs with mk_funspec fsig cc A P Q _ _ => func_at'' fsig cc A P Q loc phi end.
      Proof.
        destruct fs; auto.
      Qed.
      pose proof FAT as FAT'.
      replace phi00 with Phi in FAT.
      
      apply semax_call.func_at_func_at' in FAT.
      specialize (FA2 _ _ _ (necR_refl _) FAT).
      destruct FA2 as (id & Eid & fs' & Efs).
      specialize (FA1 id fs' _ (necR_refl _) Efs).
      destruct FA1 as (b_ & Eb & Efs').
      hnf in Eb, Eid.
      inversion2 Eid Eb.
      simpl in Eid.
      
      (* go back, use semax_prog_entry_point (but still prove ...params with find_funct_ptr) *)
      
      rewrite func_at_func_at' in FAT.
      unfold SeparationLogic.NDmk_funspec in *.
      specialize (gam0 _ _ _ FAT).
      destruct gam0 as (id & P' & Q' & ? & ? & Eb & Eid & EP & EQ).
      
      (* filter_genv is about genv_symb, but we want genv_defs ? *)
      
      (* they seem to have nothing in common
      unfold filter_genv in *.
      unfold Genv.find_symbol in *.
      unfold Genv.find_funct_ptr in *.
      unfold Genv.find_def in *.
      destruct ge.
      simpl.
      simpl in Eb.
      destruct genv_genv. simpl.
      simpl in Eb.
       *)

(* 
Q: filter_genv and find_funct_ptr seem very different
A: probably add it to matchfunspecs

Q: what about find_params (in precondition of semax_prog_entry_point): is it the same?

Q: I will add prog and semax_prog prog ??? Gamma to invariant?

Q: is the environment correct? it assigns something (1?) to xargs, and something (2?) to (b, 0), but maybe it should only assign 2?
*)
      
      
      (* we compare what we have with the precondition of semax_prog_entry_point *)
      (* prog and semax_prog CS V G : can be added to invariant

 find_params : similar to what we need to prove here



    @semax_prog CS prog V G ->

    params = (id_arg, Tpointer Tvoid noattr) :: nil ->

    find_params prog id_fun = Some params ->

    find_id id_fun G = Some (mk_funspec (params, Tvoid) cc_default A P Q NEP NEQ) ->
    (* (* P is closed wrt all tempvars except 2 *) *)
    (* (forall x, closed_wrt_vars (fun n => ~eq 2%positive n) (P x)) -> *)
    (forall ts a rho, Q ts a rho |-- FF) ->
    is_pointer_or_null arg ->


*)
      
      
      unfold filter_genv in *.
      apply Genv.find_invert_symbol in Eb.
      unfold Genv.find_funct_ptr in *.
      unfold Genv.find_def in *.
      
      unfold Genv.find_funct_ptr in *.
      unfold Genv.find_def in *.
      unfold Genv.genv_defs in *.
      unfold ge in *.
      unfold genv_defs in *.
      
      unfold Genv.invert_symbol in *.
      
      unfold Genv.find_funct_ptr in *.
      
      unfold Genv.find_funct_ptr in *.
      unfold Genv.find_def in *.
      simpl in FAT.
      spec gam0 
      
      admit (* later : I have modified matchfunspecs in the meantime *).
      (*
      match type of FAT with _ (seplog.func_at ?FS _) _ => pose (fs := FS) end.
      spec gam f_b fs.
      
      unfold filter_genv in *.
      unfold Genv.find_symbol in *.
      unfold Genv.find_funct_ptr in *.
      unfold Genv.find_def in *.
      unfold Genv.genv_defs in *.
      unfold Genv.genv_symb in *.
      unfold genv_genv in *.
      Search Genv.find_funct_ptr.
      SearchHead Genv.find_funct_ptr.
      unfold Genv.find_funct_ptr in *.
      unfold filter_genv in *.
      unfold Genv.find_def in *.
      unfold Genv.genv_defs in *.
      unfold Genv.find_symbol in *.
      
      (* pose proof @semax_call. *)
      (* all this work around safety is already done above. Try to deal with Func *)
      (* apply jsafe_phi_jsafeN with (compat0 := compat) in safety. *)
      *)
      (* unclear how to relate arg1/args (which come from the
      syntax) to anything. The juicy machine uses "initial_core" but
      it's not that simple. *)
    }
    admit. (* same problem *)
    reflexivity.
    all:try reflexivity.
*)
