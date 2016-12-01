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
Require Import concurrency.coqlib5.
Require Import concurrency.semax_conc_pred.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.semax_invariant.
Require Import concurrency.sync_preds.

Set Bullet Behavior "Strict Subproofs".

(*+ Initial state *)

Section Initial_State.
  Variables
    (CS : compspecs) (V : varspecs) (G : funspecs)
    (ext_link : string -> ident) (prog : Clight.program)
    (all_safe : semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog V G)
    (init_mem_not_none : Genv.init_mem prog <> None).
  
  Definition Jspec := @OK_spec (Concurrent_Espec unit CS ext_link).
  
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
                   (Concurrent_Espec unit CS ext_link) V G prog
                   (proj1_sig init_m) all_safe (proj2_sig init_m) in
      let q : corestate := projT1 (projT2 spr) in
      let jm : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n) in
      ThreadPool.mk
        (pos.mkPos (le_n 1))
        (* (fun _ => Kresume q Vundef) *)
        (fun _ => Krun q)
        (fun _ => m_phi jm)
        (addressFiniteMap.AMap.empty _)
     )
    ).
  
  Lemma personal_mem_of_same_jm tp jm i (cnti : ThreadPool.containsThread tp i) mc :
    (ThreadPool.getThreadR cnti = m_phi jm) ->
    m_dry (@personal_mem (m_dry jm) (getThreadR cnti) mc) = m_dry jm.
  Proof.
    unfold personal_mem in *.
    simpl.
    intros E.
    apply mem_ext; auto.
    apply juicyRestrictCur_unchanged.
    rewrite E.
    symmetry.
    destruct jm; simpl; auto.
  Qed.
  
  Theorem initial_invariant n sch : state_invariant Jspec (make_tycontext_s G) n (initial_state n sch).
  Proof.
    unfold initial_state.
    destruct init_m as [m Hm]; simpl proj1_sig; simpl proj2_sig.
    set (spr := semax_prog_rule (Concurrent_Espec unit CS ext_link) V G prog m all_safe Hm).
    set (q := projT1 (projT2 spr)).
    set (jm := proj1_sig (snd (projT2 (projT2 spr)) n)).
    match goal with |- _ _ _ (_, (_, ?TP)) => set (tp := TP) end.
    
    (*! compatibility of memories *)
    assert (compat : mem_compatible_with tp m (m_phi jm)).
    {
      constructor.
      + apply AllJuice with (m_phi jm) None.
        * change (proj1_sig (snd (projT2 (projT2 spr)) n)) with jm.
          unfold join_threads.
          unfold getThreadsR.
          
          match goal with |- _ ?l _ => replace l with (m_phi jm :: nil) end; swap 1 2. {
            simpl.
            set (a := m_phi jm).
            match goal with |- context [m_phi ?jm] => set (b := m_phi jm) end.
            replace b with a by reflexivity. clear. clearbody a.
            reflexivity.
            (* unfold fintype.ord_enum, eqtype.insub, seq.iota in *.
            simpl.
            destruct ssrbool.idP as [F|F]. reflexivity. exfalso. auto. *)
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
        apply mem_cohere'_juicy_mem.
      + intros b ofs.
        match goal with |- context [ssrbool.isSome ?x] => destruct x as [ phi | ] eqn:Ephi end; swap 1 2.
        { unfold is_true. simpl. congruence. } intros _.
        unfold tp in Ephi; simpl in Ephi.
        discriminate.
      + intros loc sh psh P z L.
        destruct (snd (projT2 (projT2 spr))) as [jm' [D [H [A NL]]]]; unfold jm in *; clear jm; simpl in L |- *.
        pose proof (NL loc) as NL'.
        rewrite L in NL'.
        edestruct NL as [lk ct].
        destruct lk; eauto.
      + hnf.
        simpl.
        intros ? F.
        inversion F.
    } (* end of mcompat *)
    
    assert (En : level (m_phi jm) = n). {
      unfold jm; clear.
      match goal with
        |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & nolocks)
      end; simpl.
      rewrite level_juice_level_phi in *.
      auto.
    }
    
    apply state_invariant_c with (PHI := m_phi jm) (mcompat := compat); auto.
    
    - intros b SPEC phi NECR FU.
      (* pose proof semax_prog_entry_point (Concurrent_Espec unit CS ext_link) V G prog. *)
      destruct SPEC as [f c A P Q P_ne Q_ne].
      simpl in FU.
      destruct FU as (pp, E).
      
      (*
      missing:
        (id_fun id_arg : ident) (arg : val) (params : list (ident * type)) 
        (A : rmaps.TypeTree)
        (P Q : forall ts : list Type, (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred)
        (NEP : super_non_expansive P) (NEQ : super_non_expansive Q),
      semax_prog (Concurrent_Espec unit CS ext_link) prog V G ->
      params = (id_arg, Tpointer Tvoid noattr) :: nil ->
      find_params prog id_fun = Some params ->
      find_id id_fun G = Some (mk_funspec (params, Tvoid) cc_default A P Q NEP NEQ) ->
      (forall (ts : list Type) (a : (rmaps.dependent_type_functor_rec ts A) mpred)
         (rho : (rmaps.dependent_type_functor_rec ts (rmaps.ConstType environ)) mpred), 
       Q ts a rho |-- FF) ->
      expr.is_pointer_or_null arg ->
       *)
      
      unfold matchfunspec in *.
      simpl.
      (* argh *)
      (*
      exists (prog_main prog). (* no, it can be anything *)
      clear tp compat.
      rewrite find_id_maketycontext_s.
      destruct spr as (b' & q' & (Symb, init) & spr);
        simpl (projT2 _) in *; simpl (projT1 _) in *.
      unfold filter_genv in *.
      rewrite Symb. unfold q in *; clear q.
      unfold seplog.func_at' in *.
      destruct SPEC as [f c A m0 m1].
      destruct FU as [pp PA].
      simpl snd in jm.
      destruct (spr n) as (jm' & jmm & lev & S & nolocks). simpl in jm.
      unfold jm in *; clear jm; rename jm' into jm. clear spr.
       *)    
      admit.
      (* we need to relate the [jm] given by [semax_prog_rule]  *)
    
    - (*! lock sparsity (no locks at first) *)
      intros l1 l2.
      rewrite threadPool.find_empty.
      tauto.
    
    - (*! lock coherence (no locks at first) *)
      intros lock.
      rewrite threadPool.find_empty.
      (* split; *) intros (sh & sh' & z & P & E); revert E; unfold jm;
      match goal with
        |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & nolocks)
      end; simpl; apply nolocks.
    
    - (*! safety of the only thread *)
      intros i cnti ora.
      destruct (ThreadPool.getThreadC cnti) as [c|c|c v|v1 v2] eqn:Ec; try discriminate; [].
      destruct i as [ | [ | i ]]. 2: now inversion cnti. 2:now inversion cnti.
      (* the initial juicy has got to be the same as the one given in initial_mem *)
      assert (Ejm: jm = jm_ cnti compat).
      {
        apply juicy_mem_ext; swap 1 2.
        - reflexivity.
        - unfold jm_.
          symmetry.
          unfold jm.
          destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
          destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl projT1 in *; simpl projT2 in *.
          subst m.
          rewrite personal_mem_of_same_jm; eauto.
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
