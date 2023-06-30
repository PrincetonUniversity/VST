(* Instead of deriving a juicy-machine execution from the CSL proof, we derive a dry-machine execution
   directly, along the lines of the sequential adequacy proof (veric/SequentialClight). *)
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
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SequentialClight.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
(*Require Import VST.concurrency.juicy.juicy_machine.*)
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
(*Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_safety_makelock.
Require Import VST.concurrency.juicy.semax_safety_spawn.
Require Import VST.concurrency.juicy.semax_safety_release.
Require Import VST.concurrency.juicy.semax_safety_freelock.
Require Import VST.concurrency.juicy.semax_preservation.
Require Import VST.concurrency.juicy.semax_simlemmas.*)
Import ThreadPool.

Set Bullet Behavior "Strict Subproofs".

(*+ Final instantiation *)

Record CSL_proof := {
  CSL_Σ : gFunctors;
  CSL_prog : Clight.program;
  CSL_CS: compspecs;
  CSL_V : varspecs;
  CSL_G : @funspecs CSL_Σ;
  CSL_ext_link : string -> ident;
  CSL_ext_link_inj : forall s1 s2, CSL_ext_link s1 = CSL_ext_link s2 -> s1 = s2;
  CSL_all_safe : forall (HH : heapGS CSL_Σ) (HE : externalGS unit CSL_Σ), @semax_prog _ HH (Concurrent_Espec unit CSL_CS CSL_ext_link)
    HE CSL_CS CSL_prog tt CSL_V CSL_G;
  CSL_init_mem_not_none : Genv.init_mem CSL_prog <> None;
                   }.

(*
Definition Clight_init_state (prog:Ctypes.program function) main_symb f_main init_mem :=
  State Clight_safety.main_handler
        (Scall None (Etempvar BinNums.xH (type_of_fundef f_main))
               (List.map (fun x : AST.ident * Ctypes.type => Etempvar (fst x) (snd x))
                         (Clight_new.params_of_types (BinNums.xO BinNums.xH)
                                                     (Clight_new.params_of_fundef f_main))))
        (Kseq (Sloop Sskip Sskip) Kstop) empty_env
        (temp_bindings BinNums.xH (cons main_symb nil)) init_mem.
*)

Section Safety.
  Variable CPROOF: CSL_proof.
  Definition Σ := CPROOF.(CSL_Σ).
  Definition CS :=   CPROOF.(CSL_CS).
  Definition V :=   CPROOF.(CSL_V).
  Definition G :=   CPROOF.(CSL_G).
  Definition ext_link :=   CPROOF.(CSL_ext_link).
  Definition ext_link_inj :=   CPROOF.(CSL_ext_link_inj).
  Definition prog :=   CPROOF.(CSL_prog).
  Definition all_safe :=   CPROOF.(CSL_all_safe).
  Definition init_mem_not_none :=   CPROOF.(CSL_init_mem_not_none).

  Definition init_mem : {m : mem | Genv.init_mem (CSL_prog CPROOF) = Some m}.
  Proof.
    pose proof init_mem_not_none.
    destruct (Genv.init_mem (CSL_prog CPROOF)); last done.
    eauto.
  Defined.

  Local Instance CEspec (HH : heapGS Σ) (HE : externalGS unit Σ) : OracleKind :=
    Concurrent_Espec unit CS ext_link.

  Program Definition spr (HH : heapGS Σ) (HE : externalGS unit Σ) :=
    semax_prog_rule V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HE) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros ??????; apply I. Qed.

  Instance Sem : Semantics := ClightSemanticsForMachines.ClightSem (Clight.globalenv CPROOF.(CSL_prog)).
  Definition ge := Clight.globalenv CPROOF.(CSL_prog).

  Definition init_access_map : access_map := Maps.PMap.init (fun _ => None).

  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

  Definition threads_safe `{heapGS Σ} `{externalGS unit Σ} {res : Resources} (tp : @OrdinalPool.t res Sem) : mpred :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), ∃ cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i,
    match getThreadC cnti with
    | Krun c | Kblocked c => jsafeN (CEspec _ _) ge ⊤ tt c
    | Kresume c v =>
      ∀ c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        ⌜cl_after_external None c = Some c'⌝ →
        jsafeN (CEspec _ _) ge ⊤ tt c'
    | Kinit v1 v2 =>
      ∃ q_new,
      ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafeN (CEspec _ _) ge ⊤ tt q_new
    end%I.

  Theorem dry_safety `{!VSTGpreS unit Σ} sch n : exists b c_init,
    Genv.find_symbol (globalenv prog) (Ctypes.prog_main prog) = Some b /\
    cl_initial_core (globalenv prog) (Vptr b Ptrofs.zero) [] = Some c_init /\
    HybridMachineSig.HybridCoarseMachine.csafe
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
       (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
     (sch, [],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
        c_init (init_access_map, init_access_map)) (proj1_sig init_mem) n.
  Proof.
    eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
    simpl; intros; iIntros "_".
    iMod (@init_VST _ _ VSTGpreS0) as "H".
    iDestruct ("H" $! Hinv) as (?? HE) "(H & ?)".
    destruct (spr (HeapGS _ _ _ _) HE) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "H") as "(S & Hsafe)".
    iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
         (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
         (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
       (sch, [],
        DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
          q (init_access_map, init_access_map)) (proj1_sig init_mem) n⌝) with "[S Hsafe]" as "Hdry".
    2: { iApply step_fupd_intro; first done.
         iNext; iApply (step_fupdN_mono with "Hdry").
         iPureIntro. intros.
         eexists. eexists. split; first done; split; first apply Hinit; done. }
    clear Hinit Hsafe.
    rewrite bi.and_elim_l.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    set (tp := initial_machine _ _ _).
    iAssert (threads_safe tp) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      unshelve iExists _; done. }
    clearbody tp.
    clear dependent b x q.
    iLöb as "IH" forall (sch tr tp m n).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done. iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2: { iApply step_fupd_intro; first done; iNext.
         iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
         { rewrite step_fupdN_plain_forall //.
           iIntros; iApply ("IH" with "S Hsafe"). }
         iApply (step_fupdN_mono with "H"); iPureIntro.
         intros Hsafe.
         eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
         eapply HybridMachineSig.schedfail; eauto.
         { rewrite /containsThread /= /OrdinalPool.containsThread.
           intros ?.
           pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle; [lia | congruence]. }
         admit. admit. }
    rewrite {2}/threads_safe.
    rewrite big_sepL_lookup_acc_impl; last by apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & Hsafei) & Hsafe)".
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      rewrite /jsafeN jsafe_unfold /jsafe_pre.
      iMod ("Hsafei" with "S") as "[Hsafe_halt | [Hsafe_core | Hsafe_ext]]".
      + iDestruct "Hsafe_halt" as %(ret & Hhalt & Hexit). (* should also give back the state_interp? *)
        iAssert (state_interp m ()) as "S"; first admit.
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe tp) with "[Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          * iIntros "!>" (????) "$".
          * iExists cnti; rewrite Hi.
            rewrite /jsafeN jsafe_unfold /jsafe_pre.
            iIntros "!>" (?) "?". iLeft; eauto. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "S Hsafe"). }
         iApply (step_fupdN_mono with "H"); iPureIntro.
         intros Hsafe.
         eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
         eapply HybridMachineSig.halted_step; eauto.
         econstructor; eauto.
      + iDestruct "Hsafe_core" as ">(%c' & %m' & %Hstep & s_interp & ▷jsafe)".
        iApply fupd_mask_intro; first done.
        iIntros "Hclose !>"; iMod "Hclose" as "_".
        iSpecialize ("IH" with "[$]").
        admit. (* HybridMachineSig.thread_step
        iModIntro; iApply (step_fupdN_mono with "IH").
        iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe, Hsafe.
        rewrite /HybridMachineSig.MachStep /=.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m') at 3.
        eapply HybridMachineSig.thread_step; first done.
        econstructor; try done.*)
      + (* HybridMachineSig.suspend_step *) admit.
        (* iDestruct "Hsafe_ext" as (ef args w (at_external & Hpre)) "Hpost".
        iAssert (|={⊤}[∅]▷=>^(S n) ⌜(∀ (ret : option val) m' z' n',
        Val.has_type_list args (sig_args (ef_sig ef))
        → Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef))
          → n' ≤ n
              → ext_spec_post OK_spec ef w
                  (genv_symb_injective (globalenv prog)) (sig_res (ef_sig ef)) ret z' m'
                → ∃ q',
                    (after_external (cl_core_sem (globalenv prog)) ret q m' = Some q'
                     ∧ safeN_ (cl_core_sem (globalenv prog)) OK_spec (Genv.globalenv prog) n' z' q' m'))⌝) with "[-]" as "Hdry".
        2: { iApply (step_fupdN_mono with "Hdry"); iPureIntro; intros; eapply safeN_external; eauto. }
        iApply step_fupdN_mono; first by do 8 setoid_rewrite bi.pure_forall.
        repeat (setoid_rewrite step_fupdN_plain_forall; last done; [|apply _..]).
        iIntros (ret m' z' n' ????).
        simpl; iApply fupd_mask_intro; first done.
        iIntros "Hclose !>"; iMod "Hclose" as "_".
        iMod ("Hpost" with "[%] [%]") as (??) "H"; [done..|].
        iSpecialize ("IH" with "[$]").
        iModIntro; iApply step_fupdN_le; first done.
        iApply (step_fupdN_mono with "IH"); eauto. } *)
    - (* Kblocked: HybridMachineSig.sync_step *) admit.
    - (* Kresume: HybridMachineSig.resume_step *) admit.
    - (* Kinit: HybridMachineSig.start_step *) admit.
  Admitted.

End Safety.
