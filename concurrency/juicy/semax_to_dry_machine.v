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
Require Import VST.sepcomp.extspec.
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
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Import ThreadPool.

Set Bullet Behavior "Strict Subproofs".

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

  Lemma CEspec_cases : forall `{!heapGS Σ} `{!externalGS unit Σ} e
    (x : ext_spec_type (concurrent_ext_spec unit CS ext_link) e),
    e = LOCK \/ e = UNLOCK \/ e = MKLOCK \/ e = FREE_LOCK \/ e = CREATE.
  Proof.
    intros.
    simpl in x.
    repeat (if_tac in x; [destruct e; try done; inversion H as [H1]; apply ext_link_inj in H1 as <-; auto
      | clear H]); last done.
  Qed.

  Program Definition spr (HH : heapGS Σ) (HE : externalGS unit Σ) :=
    semax_prog_rule V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HE) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros ??????; apply I. Qed.

  Instance Sem : Semantics := ClightSemanticsForMachines.ClightSem (Clight.globalenv CPROOF.(CSL_prog)).
  Definition ge := Clight.globalenv CPROOF.(CSL_prog).

  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

  (* If there are enough of these conditions, re-split out into semax_invariant. *)
  Definition dtp := @OrdinalPool.t dryResources Sem.

  (* Each thread needs to be safe given only its fragment (access_map) of the shared memory. We use
     the starting max permissions as an upper bound on the max permissions of the state_interp. *)
  Program Definition jsafe_perm_pre `{!heapGS Σ} `{!externalGS unit Σ} (max : access_map)
    (jsafe : coPset -d> OK_ty -d> CC_core -d> access_map -d> iPropO Σ) : coPset -d> OK_ty -d> CC_core -d> access_map -d> iPropO Σ := λ E z c p,
    |={E}=> ∀ m (Hlt : permMapLt p (getMaxPerm m)), ⌜permMapLt (getMaxPerm m) max⌝ → state_interp m z -∗
        (∃ i, ⌜halted (cl_core_sem ge) c i ∧ ext_spec_exit OK_spec (Some (Vint i)) z m⌝) ∨
        (|={E}=> ∃ c' m', ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧ (∃ p' (Hlt' : permMapLt p' (getMaxPerm m')), state_interp (restrPermMap Hlt') z) (* ?? *) ∗ ▷ jsafe E z c' (getCurPerm m')) ∨
        (∃ e args x, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args) ∧ ext_spec_pre OK_spec e x (genv_symb_injective ge) (sig_args (ef_sig e)) args z (restrPermMap Hlt)⌝ ∧
           ▷ (∀ ret m' z', ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            ⌜ext_spec_post OK_spec e x (genv_symb_injective ge) (sig_res (ef_sig e)) ret z' m'⌝ → |={E}=>
            ∃ c', ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧ state_interp m' z' ∗ jsafe E z' c' (getCurPerm m'))).

  Local Instance jsafe_perm_pre_contractive `{!heapGS Σ} `{!externalGS unit Σ} max : Contractive (jsafe_perm_pre max).
  Proof.
    rewrite /jsafe_perm_pre => n jsafe jsafe' Hsafe E z c p.
    do 16 f_equiv.
    - f_contractive; repeat f_equiv. apply Hsafe.
    - f_contractive; repeat f_equiv. apply Hsafe.
  Qed.

  Local Definition jsafe_perm_def `{!heapGS Σ} `{!externalGS unit Σ} max : coPset -> unit -> CC_core -> access_map -> mpred := fixpoint (jsafe_perm_pre max).
  Local Definition jsafe_perm_aux `{!heapGS Σ} `{!externalGS unit Σ} : seal (jsafe_perm_def). Proof. by eexists. Qed.
  Definition jsafe_perm  `{!heapGS Σ} `{!externalGS unit Σ} := jsafe_perm_aux.(unseal).
  Local Lemma jsafe_perm_unseal  `{!heapGS Σ} `{!externalGS unit Σ} : jsafe_perm = jsafe_perm_def.
  Proof. rewrite -jsafe_perm_aux.(seal_eq) //. Qed.

  Lemma jsafe_perm_unfold `{!heapGS Σ} `{!externalGS unit Σ} max E z c p : jsafe_perm max E z c p ⊣⊢ jsafe_perm_pre max (jsafe_perm max) E z c p.
  Proof. rewrite jsafe_perm_unseal. apply (fixpoint_unfold (@jsafe_perm_pre heapGS0 externalGS0 max)). Qed.

  Lemma jsafe_perm_mono : forall `{!heapGS Σ} `{!externalGS unit Σ} p1 p2 E z c p, permMapLt p2 p1 ->
    jsafe_perm p1 E z c p ⊢ jsafe_perm p2 E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p H z c).
    rewrite !jsafe_perm_unfold /jsafe_perm_pre.
    iIntros ">H !>" (?? Hmax) "S".
    pose proof (PreOrder_Transitive _ _ _ Hmax H).
    iDestruct ("H" with "[%] S") as "[H | [H | H]]"; first done.
    - iLeft; done.
    - iRight; iLeft.
      iMod "H" as (???) "(? & ?)".
      iIntros "!>"; iExists _, _; iSplit; first done; iFrame.
      by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (????) "H".
      iExists _, _, _; iSplit; first done.
      iNext; iIntros (?????).
      iMod ("H" with "[%] [%]") as (??) "(? & ?)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done; iFrame.
      by iApply "IH".
  Qed.

  Existing Instance mem_equiv.access_map_equiv_Equivalence.

  Lemma jsafe_perm_equiv : forall `{!heapGS Σ} `{!externalGS unit Σ} p E z c p1 p2, mem_equiv.access_map_equiv p1 p2 ->
     jsafe_perm p E z c p1 ⊢ jsafe_perm p E z c p2.
  Proof.
    intros.
    iLöb as "IH" forall (p z c p1 p2 H).
    rewrite !jsafe_perm_unfold /jsafe_perm_pre.
    iIntros ">H !>" (?? Hmax) "S".
    assert (permMapLt p1 (getMaxPerm m)) as Hlt1.
    { eapply mem_equiv.permMapLt_equiv; done. }
    iDestruct ("H" $! _ Hlt1 with "[%] S") as "[H | [H | H]]"; first done.
    - iLeft; done.
    - iRight; iLeft.
      iMod "H" as (???) "(S & Hsafe)".
      assert (exists m2', corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m2' /\ mem_equiv.mem_equiv m2' m') as (m2' & ? & Heq') by admit.
      iIntros "!>"; iExists _, _; iSplit; first done.
      iSplitL "S".
      + iDestruct "S" as (??) "S".
        assert (permMapLt p' (getMaxPerm m2')) as Hlt2'.
        { eapply mem_equiv.permMapLt_equiv; [done | by apply mem_equiv.max_eqv | done]. }
        iExists _, Hlt2'.
        (* Do I need to add a mem_equiv to jsafe_perm? Can the init step change the shape of the memory? *)
        admit.
      + iApply ("IH" with "[%] Hsafe").
        by apply mem_equiv.cur_eqv.
    - iRight; iRight.
      iDestruct "H" as (????) "H".
(*      
      iExists _, _, _; iSplit; first done.
      iNext; iIntros (?????).
      iMod ("H" with "[%] [%]") as (??) "(? & ?)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done; iFrame.
      by iApply "IH".
  Qed.*)
  Admitted.

  Lemma jsafe_jsafe_perm : forall `{!heapGS Σ} `{!externalGS unit Σ} max E z c p, p = max ->
    jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec unit CS ext_link) ge E z c ⊢ jsafe_perm max E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p H z c).
    rewrite jsafe_unfold jsafe_perm_unfold /jsafe_pre /jsafe_perm_pre.
    iIntros ">H !>" (?? Hmax) "S".
    subst; pose proof (partial_order_antisym mem_equiv.permMapLt_order _ _ Hlt Hmax) as Heq.
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - by iLeft.
    - iRight; iLeft.
      iMod "H" as (???) "(S & Hsafe)".
      (* do we need to bring back mem_sub for this? *)
      assert (exists m'', corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'' /\ exists p' (Hlt' : permMapLt p' (getMaxPerm m')), m'' = restrPermMap Hlt') as (? & ? & ? & Hlt' & ->) by admit.
      iIntros "!>"; iExists _, _; iSplit; first done.
      iSplitL "S".
      + assert (permMapLt (getCurPerm m') (getMaxPerm (restrPermMap Hlt'))) as Hltm'.
        { rewrite restr_Max_eq; apply cur_lt_max. }
        iExists _, Hltm'; rewrite restrPermMap_idem restrPermMap_eq //.
      + iNext; iApply ("IH" with "[%] Hsafe").
        admit. (* something about how perms being maxxed carries forward *)
    - iRight; iRight.
      iDestruct "H" as (??? (? & ?)) "H".
      assert (ext_spec_pre (concurrent_ext_spec () CS ext_link) e x (genv_symb_injective ge)
       (sig_args (ef_sig e)) args z (restrPermMap Hlt)) by admit.
      iExists _, _, _; iSplit; first done.
      iIntros "!>" (?????).
      iMod ("H" with "[%] [%]") as (??) "(S & Hsafe)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done.
      iFrame; iApply ("IH" with "[%] Hsafe").
  Admitted.

  Definition threads_safe `{!heapGS Σ} `{!externalGS unit Σ} max (tp : dtp) : mpred :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), ∃ cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i,
    match getThreadC cnti with
    | Krun c | Kblocked c => jsafe_perm max ⊤ tt c (getThreadR cnti).1
    | Kresume c v =>
      ∀ c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        ⌜cl_after_external None c = Some c'⌝ →
        jsafe_perm max ⊤ tt c' (getThreadR cnti).1
    | Kinit v1 v2 =>
      ∃ q_new,
      ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_perm max ⊤ tt q_new (getThreadR cnti).1
    end%I.

  Definition threads_wellformed (tp : dtp) :=
    forall i (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

  Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

  Theorem dry_safety `{!VSTGpreS unit Σ} sch n : exists b c_init,
    Genv.find_symbol (globalenv prog) (Ctypes.prog_main prog) = Some b /\
    cl_initial_core (globalenv prog) (Vptr b Ptrofs.zero) [] = Some c_init /\
    HybridMachineSig.HybridCoarseMachine.csafe
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
     (sch, [],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
        c_init) (proj1_sig init_mem) n.
  Proof.
    eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
    simpl; intros; iIntros "_".
    iMod (@init_VST _ _ VSTGpreS0) as "H".
    iDestruct ("H" $! Hinv) as (?? HE) "(H & ?)".
    destruct (spr (HeapGS _ _ _ _) HE) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "H") as "(S & Hsafe)".
    iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
         (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
       (sch, [],
        DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
          q) (proj1_sig init_mem) n⌝) with "[S Hsafe]" as "Hdry".
    2: { iApply step_fupd_intro; first done.
         iNext; iApply (step_fupdN_mono with "Hdry").
         iPureIntro. intros.
         eexists. eexists. split; first done; split; first apply Hinit; done. }
    clear Hinit Hsafe.
    rewrite bi.and_elim_l.
    set (tp := initial_machine _ _).
    assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
    assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat by apply ThreadPoolWF.initial_mem_compatible.
    assert (threads_wellformed tp) as Htp_wf by done.
    set (HH := HeapGS _ Hinv _ _).
    iAssert (threads_safe(heapGS0 := HH) (getMaxPerm (`init_mem)) tp) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      unshelve iExists _; first done.
      iApply (jsafe_jsafe_perm with "Hsafe").
      admit. (* should be provable, but is this what we need? *) }
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    clearbody tp.
    clear dependent b x q.
    (* the machine semantics clobber the curPerm with the most recent thread's curPerm *)
    iAssert (∃ p (Hlt : permMapLt p (getMaxPerm m)), state_interp (restrPermMap Hlt) tt) with "[S]" as "S".
    { iExists _, (cur_lt_max m); rewrite restrPermMap_eq //. }
    iLöb as "IH" forall (sch tr tp m n Htp_wf Hinvariant Hcompat).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2: { iApply step_fupd_intro; first done; iNext.
         iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
         { rewrite step_fupdN_plain_forall //.
           iIntros; iApply ("IH" with "[%] [%] [%] Hsafe S"); done. }
         iApply (step_fupdN_mono with "H"); iPureIntro.
         intros Hsafe.
         eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
         eapply HybridMachineSig.schedfail; eauto.
         rewrite /containsThread /= /OrdinalPool.containsThread.
         intros ?.
         pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle; [lia | congruence]. }
    rewrite {2}/threads_safe.
    set (Espec := CEspec _ _).
    rewrite big_sepL_lookup_acc_impl; last by apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & Hsafei) & Hsafe)".
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
      + (* halted *)
        assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
        { econstructor; eauto.
          hnf; rewrite Hhalt //. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe (getMaxPerm m) tp) with "[Hsafei Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          * iIntros "!>" (????) "H"; iApply "H".
          * iExists cnti; rewrite Hi //. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "[%] [%] [%] Hsafe S"); done. }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.halted_step; eauto.
      + (* HybridMachineSig.suspend_step *)
        assert (HybridMachineSig.suspend_thread m cnti (updThreadC cnti (Kblocked s))) as Hsuspend.
        { eapply (HybridMachineSig.SuspendThread _ _ _ _ _ _ _ _ Hcompat); done. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, (updThreadC cnti (Kblocked s))) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "[%] [%] [%] [Hsafei Hsafe] S").
          + intros j cntj.
            destruct (eq_dec j i).
            * subst; rewrite gssThreadCC Hat_ext //.
            * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
              rewrite -gsoThreadCC //; apply Htp_wf.
          + by apply ThreadPoolWF.updThreadC_invariant.
          + by apply StepLemmas.updThreadC_compatible.
          + iApply "Hsafe".
            * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
              iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
            * iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
              by iApply "Hsafei". }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        rewrite jsafe_perm_unfold /jsafe_perm_pre.
        iDestruct "S" as (? Hmax) "S".
        assert (permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax))) as Hlt0.
        { rewrite restr_Max_eq. by apply compat_th. }
        iMod ("Hsafei" $! _ Hlt0 with "[%] S") as "[Hhalt | [Hstep | Hext]]".
        { rewrite restr_Max_eq //. }
        { iDestruct "Hhalt" as %(? & Hhalt' & ?); done. }
        2: { iDestruct "Hext" as (??? (Hext & ?)) "?".
             simpl in Hext; congruence. }
        iMod "Hstep" as (?? Hstep) "(S & Hsafei)".
        rewrite restrPermMap_idem in Hstep.
        assert (corestep (cl_core_sem ge) s (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
        { by erewrite restrPermMap_irr. }
        iApply step_fupd_intro; first done; iNext.
        apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) with "[%] [%] [%] [Hsafe Hsafei] S").
        * intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
          by eapply ev_step_ax1.
        * by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
        * iApply "Hsafe".
          -- iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
             iExists (cntUpdate _ _ cnti cnti0).
             rewrite gsoThreadCode //.
             rewrite gsoThreadRes //.
             admit. (* need to know that any changes to getMaxPerm don't invalidate other threads! *)
          -- iExists (cntUpdate _ _ cnti cnti).
             rewrite gssThreadCode gssThreadRes.
             admit.
        * iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe, Hsafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          by eapply step_dry.
    - (* Kblocked: HybridMachineSig.sync_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
      rewrite jsafe_perm_unfold /jsafe_perm_pre.
      iDestruct "S" as (? Hmax) "S".
      assert (permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax))) as Hlt0.
      { rewrite restr_Max_eq. by apply compat_th. }
      iMod ("Hsafei" $! _ Hlt0 with "[%] S") as "[Hhalt | [Hstep | Hext]]".
      { rewrite restr_Max_eq //. }
      { iDestruct "Hhalt" as %(? & Hhalt' & ?).
        destruct s; done. }
      { iMod "Hstep" as (?? Hstep) "?".
        apply cl_corestep_not_at_external in Hstep; done. }
      iDestruct "Hext" as (??? (Hat_ext & Hpre)) "Hpost".
      iAssert (|={⊤}[∅]▷=> ∃ (tp' : t(ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev, ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
        syncStep true cnti Hcompat tp' m' ev⌝ ∧
        threads_safe (getMaxPerm m') tp' ∗ (∃ p (Hlt : permMapLt p (getMaxPerm m')), state_interp (restrPermMap Hlt) tt)) with "[-]" as "Hsafe".
      2: { iMod "Hsafe"; iIntros "!> !>"; iMod "Hsafe" as (??? (? & ? & ? & ?)) "(Hsafe & S)".
           iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
           { rewrite step_fupdN_plain_forall //.
             iIntros; iApply ("IH" with "[%] [%] [%] Hsafe S"); done. }
           iApply (step_fupdN_mono with "H"); iPureIntro.
           intros Hsafe.
           eapply HybridMachineSig.HybridCoarseMachine.AngelSafe; simpl; last apply Hsafe.
           eapply HybridMachineSig.sync_step; eauto. }
      (* consider each of the concurrency functions *)
      clear Hwfi.
      destruct s as [|f ? k|]; try done; simpl in Hat_ext.
      destruct f as [|ext argsty retty cc]; try done.
      destruct (ef_inline ext); inv Hat_ext.
      destruct (CEspec_cases _ x) as [-> | [-> | [-> | [-> | ->]]]].
      + (* acquire *)
        
      + (* release *)
      + (* makelock *)
      + (* freelock *)
      + (* spawn *)
    - (* Kresume: HybridMachineSig.resume_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
      destruct s; try done.
      destruct f; try done.
      assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
      { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c))) with "[%] [%] [%] [Hsafei Hsafe] S").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCC //.
        * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
          rewrite -gsoThreadCC //; apply Htp_wf.
      + by apply ThreadPoolWF.updThreadC_invariant.
      + by apply StepLemmas.updThreadC_compatible.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
        * iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
          by iApply "Hsafei".
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        eapply HybridMachineSig.resume_step; eauto.
    - (* Kinit: HybridMachineSig.start_step *)
      iDestruct "Hsafei" as (? Hinit) "Hsafei".
      set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
      set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
      assert (HybridMachineSig.start_thread m cnti tp' m').
      { econstructor; done. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [Hsafei Hsafe] [S]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCode //.
        * pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
      + by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
      + eapply InternalSteps.start_compatible; try done.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists (cntUpdate _ _ cnti cnti0); rewrite gsoThreadCode // gsoThreadRes //.
          subst m'; rewrite restr_Max_eq //.
        * iExists (cntUpdate _ _ cnti cnti); rewrite gssThreadCode gssThreadRes.
          rewrite restr_Max_eq /=.
          iApply (jsafe_perm_equiv with "Hsafei").
          symmetry; apply mem_equiv.getCur_restr.
      + iDestruct "S" as (??) "S".
        iExists _, (mem_equiv.useful_permMapLt_trans _ Hlt).
        rewrite restrPermMap_idem. erewrite restrPermMap_irr; done.
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m').
        eapply HybridMachineSig.start_step; eauto.
  Admitted.

End Safety.
