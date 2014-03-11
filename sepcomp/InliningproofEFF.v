Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import sepcomp.Inlining.
Require Import sepcomp.Inliningspec.
Require Import RTL.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.reach.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.
(*Require Import CminorSel_coop.*)
Require Import RTL_eff.
Require Import RTL_coop.

Load Santiago_tactics.

Variable SrcProg: RTL.program.
Variable TrgProg: RTL.program.
Hypothesis TRANSF: transf_program SrcProg = OK TrgProg.
Let SrcGe : RTL.genv := Genv.globalenv SrcProg.
Let TrgGe : RTL.genv := Genv.globalenv TrgProg.
Let fenv := funenv_program SrcProg.


Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr SrcGe b = Some f ->
  exists f', Genv.find_funct_ptr TrgGe b = Some f' /\ Inlining.transf_fundef fenv f = OK f'.
Proof (Genv.find_funct_ptr_transf_partial (transf_fundef fenv) _ TRANSF).

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol TrgGe s = Genv.find_symbol SrcGe s.
Proof.
  intros. apply Genv.find_symbol_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info TrgGe b = Genv.find_var_info SrcGe b.
Proof.
  intros. apply Genv.find_var_info_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

(*LENB: GFP as in selectionproofEFF*)
(*Definition globalfunction_ptr_inject (j:meminj):=
  forall b f, Genv.find_funct_ptr SrcGe b = Some f -> 
              j b = Some(b,0) /\ isGlobalBlock SrcGe b = true. *)

(*The new match_states*)

(*Tool kit for match states: *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> val_inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ val_inject F v rs'#(sreg ctx r)).

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Inductive match_globalenvs (F: meminj)(bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol SrcGe id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr SrcGe b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info SrcGe b = Some gv -> Plt b bound).

Inductive match_stacks (mu: SM_Injection) (m m': mem):
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs (as_inj mu) bound1)
        (BELOW: Ple bound1 bound),
      match_stacks mu m m' nil nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound ctx
        (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs (as_inj mu) ctx rs rs')
        (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
(*locBlockSrc mu sp = true*)
(*locBlockTrg mu sp' = true*)
        (PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Plt sp' bound),
      match_stacks (mu) m m'
                   (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
        (MS: match_stacks_inside (mu) m m' stk stk' f' ctx sp' rs')
        (PRIV: range_private (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
(*locBlockTrg mu sp' = true*)
        (BELOW: Plt sp' bound),
      match_stacks (mu) m m'
                   stk
                   (Stackframe res f' (Vptr sp' Int.zero) rpc rs' :: stk')
                   bound

with match_stacks_inside (mu: SM_Injection) (m m': mem):
        list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
        (MS: match_stacks (mu) m m' stk stk' sp')
(*locBlockTrg mu sp' = true*)(*Maybe*)
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside (mu) m m' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' ctx sp' rs' ctx'
        (MS: match_stacks_inside (mu) m m' stk stk' f' ctx' sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs (as_inj mu) ctx' rs rs')
        (SP: (as_inj mu) sp = Some(sp', ctx'.(dstk)))
(*locBlockSrc mu sp = true*)
(*locBlockTrg mu sp' = true*)
        (PAD: range_private (as_inj mu) m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside (mu) m m' (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                 stk' f' ctx sp' rs'.

Inductive match_states:  SM_Injection -> RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_regular_states: forall mu stk f sp pc rs m stk' f' sp' rs' m' ctx
        (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs (as_inj mu) ctx rs rs')
        (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject (as_inj mu) m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states mu (RTL_State stk f (Vptr sp Int.zero) pc rs) m
                   (RTL_State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs') m'
  | match_call_states: forall (mu: SM_Injection) stk fd args m stk' fd' args' m'
        (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
        (FD: transf_fundef fenv fd = OK fd')
        (VINJ: val_list_inject  (as_inj mu) args args')
        (MINJ: Mem.inject (as_inj mu) m m'),
      match_states mu (RTL_Callstate stk fd args) m
                   (RTL_Callstate stk' fd' args') m'
  | match_call_regular_states: forall (mu: SM_Injection) stk f vargs m stk' f' sp' rs' m' ctx ctx' pc' pc1' rargs
        (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact (as_inj mu) ctx' rs') vargs rargs)
        (MINJ: Mem.inject (as_inj mu) m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private  (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states mu (RTL_Callstate stk (Internal f) vargs) m
                   (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'
  | match_return_states: forall (mu: SM_Injection) stk v m stk' v' m'
        (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
        (VINJ: val_inject (as_inj mu) v v')
        (MINJ: Mem.inject (as_inj mu) m m'),
      match_states mu (RTL_Returnstate stk v) m
                   (RTL_Returnstate stk' v') m'
  | match_return_regular_states: forall (mu: SM_Injection)stk v m stk' f' sp' rs' m' ctx pc' or rinfo
        (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => val_inject (as_inj mu) v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject (as_inj mu) m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states mu (RTL_Returnstate stk v) m
                   (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'.


Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals SrcGe (as_inj mu) /\
  (forall b, isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\
  SM_wd mu /\
  Mem.inject (as_inj mu) m1 m2 (*/\ 
  globalfunction_ptr_inject (as_inj mu)*) .

(** The simulation proof *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs SrcProg)))
         entrypoints
         (entry_points_ok : 
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints -> 
              exists b f1 f2, 
                v1 = Vptr b Int.zero 
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr SrcGe b = Some f1
                /\ Genv.find_funct_ptr TrgGe b = Some f2)
         (init_mem: exists m0, Genv.init_mem SrcProg = Some m0),
    SM_simulation.SM_simulation_inject rtl_eff_sem
                                       rtl_eff_sem SrcGe TrgGe entrypoints.

  intros.
  (*eapply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf.*)
  Definition RTL_measure (S: RTL_core) : nat :=
  match S with
  | RTL_State _ _ _ _ _ => 1%nat
  | RTL_Callstate _ _ _ => 0%nat
  | RTL_Returnstate _ _ => 0%nat
  end.
  eapply sepcomp.effect_simulations_lemmas.inj_simulation_star with (match_states:= MATCH)(measure:= RTL_measure).

  Lemma environment_equality: (exists m0:mem, Genv.init_mem SrcProg = Some m0) -> 
                                     genvs_domain_eq SrcGe TrgGe.
    descend;
    destruct H0 as [b0]; exists b0;
    rewriter_back;
    [rewrite symbols_preserved| rewrite <- symbols_preserved| rewrite varinfo_preserved| rewrite <- varinfo_preserved]; reflexivity.
  Qed.
  Hint Resolve environment_equality: trans_correct.
  auto with trans_correct.

  Lemma MATCH_wd: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                         (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:MATCH d mu c1 m1 c2 m2), SM_wd mu.
    intros. eapply MC. Qed.
  Hint Resolve MATCH_wd: trans_correct.
  eauto with trans_correct.

  Lemma MATCH_RC: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                         (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:
                                                                  MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
    intros. eapply MC. Qed.
  Hint Resolve MATCH_RC: trans_correct.
  eauto with trans_correct.

  (*Lemma restrict_preserves_globalfun_ptr: forall j X
  (PG : globalfunction_ptr_inject j)
  (Glob : forall b, isGlobalBlock SrcGe b = true -> X b = true),
globalfunction_ptr_inject (restrict j X).
Proof. intros.
  red; intros. 
  destruct (PG _ _ H). split; trivial.
  apply restrictI_Some; try eassumption.
  apply (Glob _ H1).
Qed.*)

Lemma MATCH_restrict: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                 (m1 : mem) (c2 : RTL_core) (m2 : mem) (X : block -> bool) (MC: MATCH d mu c1 m1 c2 m2)(HX: forall b : block, vis mu b = true -> X b = true)(RC0:REACH_closed m1 X), MATCH d (restrict_sm mu X) c1 m1 c2 m2.
intros.
Proof. intros.
  destruct MC as [MC [RC [PG [GF [VAL [WDmu [INJ GFP]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.

split.

Lemma match_states_restrict: forall mu m1 m2 c1 c2 X
      (HX: forall b, vis mu b = true -> X b = true)
      (RC: REACH_closed m1 X)
      (MCS: match_states mu c1 m1 c2 m2 ),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
admit.
Qed.
apply match_states_restrict; intuition.

split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. (*clear -PG HX.*)
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply GF.
split.
destruct VAL.
(*This should be a lemma*)
unfold sm_valid.
    rewrite restrict_sm_DOM.
    rewrite restrict_sm_RNG.
    split; intros; intuition.
split. assumption.
(*split.*)
 rewrite restrict_sm_all.
eapply  inject_restrict; repeat (first [assumption| split]).
Qed.
Hint Resolve MATCH_restrict: trans_correct.
auto with trans_correct.

Lemma MATCH_valid:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                              (m1 : mem) (c2 : RTL_core) (m2 : mem)
                         (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
intros.
apply MC.
Qed.

Hint Resolve MATCH_valid: trans_correct.
eauto with trans_correct.

Lemma MATCH_PG:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                           (m1 : mem) (c2 : RTL_core) (m2 : mem)(
                                      MC: MATCH d mu c1 m1 c2 m2),
                                      meminj_preserves_globals SrcGe (extern_of mu) /\
                                      (forall b : block,
                                         isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.
Hint Resolve MATCH_PG: trans_correct.
eauto with trans_correct.

Lemma MATCH_initial_core: forall (v1 v2 : val) (sig : signature) entrypoints
  (entry_points_ok : forall (v1 v2 : val) (sig : signature),
                    In (v1, v2, sig) entrypoints ->
                    exists (b : block) (f1 f2 : fundef),
                      v1 = Vptr b Int.zero /\
                      v2 = Vptr b Int.zero /\
                      Genv.find_funct_ptr SrcGe b = Some f1 /\
                      Genv.find_funct_ptr TrgGe b = Some f2)
   (EP: In (v1, v2, sig) entrypoints)
   (vals1 : list val) (c1 : RTL_core) (m1 : mem) 
     (j : meminj) (vals2 : list val) (m2 : mem) (DomS DomT : block -> bool)
   (SM_Ini:initial_core rtl_eff_sem SrcGe v1 vals1 = Some c1)
   (Inj: Mem.inject j m1 m2)
   (VInj: Forall2 (val_inject j) vals1 vals2)
   (PG: meminj_preserves_globals SrcGe j)
   (J: forall (b1 b2 : block) (d : Z),
    j b1 = Some (b2, d) -> DomS b1 = true /\ DomT b2 = true)
   (RCH: forall b : block,
    REACH m2 (fun b' : block => isGlobalBlock TrgGe b' || getBlocks vals2 b')
      b = true -> DomT b = true)
   (HDomS: (forall b : block, DomS b = true -> Mem.valid_block m1 b))
   (HDomT: (forall b : block, DomT b = true -> Mem.valid_block m2 b)),
   exists c2 : RTL_core,
     initial_core rtl_eff_sem TrgGe v2 vals2 = Some c2 /\
     MATCH c1
       (initial_SM DomS DomT DomS DomT j) (*
          (REACH m1
             (fun b : block => isGlobalBlock SrcGe b || getBlocks vals1 b))
          (REACH m2
             (fun b : block => isGlobalBlock TrgGe b || getBlocks vals2 b)) j)*)
       c1 m1 c2 m2.
 Proof.
  intros.
  inversion SM_Ini.
  unfold  RTL_initial_core in H0. unfold SrcGe in *. unfold TrgGe in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exists (RTL_Callstate nil tf vals2).
  split. 
  simpl. 
  destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  subst. inv A. rewrite C in Heqzz. inv Heqzz. 
  unfold SrcGe, TrgGe in *.
  rewrite D in FIND. inv FIND.
  unfold RTL_initial_core. 
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
  solve[rewrite D; auto].
  intros CONTRA.
  solve[elimtype False; auto].
  (*destruct InitMem as [m0 [INIT_MEM [A B]]].*)
  admit.
Qed.
Hint Resolve MATCH_initial_core: trans_correct.
eauto with trans_correct.

Lemma Match_Halted: forall (cd : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
     (m1 : mem) (c2 : RTL_core) (m2 : mem) (v1 : val)(MC:
   MATCH cd mu c1 m1 c2 m2)(HALT:
   halted rtl_eff_sem c1 = Some v1),
   exists v2 : val,
     Mem.inject (as_inj mu) m1 m2 /\
     val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
     halted rtl_eff_sem c2 = Some v2.
Proof.
intros.
unfold MATCH in MC; destruct MC as [H0 H1].
inv H0; simpl in *; inv HALT. 
Print match_states.
inv MS. 
exists v'; split; try assumption; split; try reflexivity; inv H0. admit.
inv H0.
inv MS0; [rewrite RET in RET0; inv RET0 | inv H0].
inv MS.
rewrite RET in RET0; inv RET0.
inv H0.
Qed.
Hint Resolve Match_Halted: trans_correct.
eauto with trans_correct.

Lemma at_external_lemma: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) 
                                (c2 : RTL_core) (m2 : mem) (e : external_function) 
                                (vals1 : list val) (ef_sig : signature)(MC: MATCH c1 mu c1 m1 c2 m2) (ATE: at_external rtl_eff_sem c1 = Some (e, ef_sig, vals1)),
                           Mem.inject (as_inj mu) m1 m2 /\ 
                           (exists vals2 : list val, Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\ at_external rtl_eff_sem c2 = Some (e, ef_sig, vals2)).
  intros.
  split. inv MC; apply H0.
  inv MC; simpl in *. inv H; inv ATE.
  destruct fd; inv H1.
  exists args'.
  split. apply val_list_inject_forall_inject. admit.
  inv FD; trivial.
Qed.
Hint Resolve at_external_lemma: trans_correct.
eauto with trans_correct.

Lemma Match_AfterExternal: 
forall (mu : SM_Injection) (st1 : RTL_core) (st2 : RTL_core) (m1 : mem) (e : external_function) (vals1 : list val) (m2 : mem) (ef_sig : signature) (vals2 : list val) (e' : external_function) (ef_sig' : signature) 
       (MemInjMu : Mem.inject (as_inj mu) m1 m2)
       (MatchMu : MATCH st1 mu st1 m1 st2 m2)
       (AtExtSrc : at_external rtl_eff_sem st1 = Some (e, ef_sig, vals1))
       (AtExtTgt : at_external rtl_eff_sem st2 = Some (e', ef_sig', vals2))
       (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
       (pubSrc' : block -> bool)
       (pubSrcHyp : pubSrc' =
              (fun b : block =>
               locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgt' : block -> bool)
       (pubTgtHyp : pubTgt' =
              (fun b : block =>
               locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       (nu : SM_Injection)
       (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
       (nu' : SM_Injection)
       (ret1 : val)
       (m1' : mem)
       (ret2 : val)
       (m2' : mem)
       (INC : extern_incr nu nu')
       (SEP : sm_inject_separated nu nu' m1 m2)
       (WDnu' : SM_wd nu')
       (SMvalNu' : sm_valid nu' m1' m2')
       (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
       (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
       (FwdSrc : mem_forward m1 m1')
       (FwdTgt : mem_forward m2 m2')
       (frgnSrc' : block -> bool)
       (frgnSrcHyp : frgnSrc' =
               (fun b : block =>
                DomSrc nu' b &&
                (negb (locBlocksSrc nu' b) &&
                 REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
       (frgnTgt' : block -> bool)
       (frgnTgtHyp : frgnTgt' =
               (fun b : block =>
                DomTgt nu' b &&
                (negb (locBlocksTgt nu' b) &&
                 REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
       (mu' : SM_Injection)
       (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
       (UnchPrivSrc : Mem.unchanged_on
                  (fun (b : block) (_ : Z) =>
                   locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
       (UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists (st1' st2' : RTL_core),
  after_external rtl_eff_sem (Some ret1) st1 = Some st1' /\
  after_external rtl_eff_sem (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros. 
 destruct MatchMu as [MC [RC [PG [GF [VAL [WDmu [INJ GFP]]]]]]].
 inv MC; simpl in *; inv AtExtSrc.
  destruct fd; inv H0.
  destruct fd'; inv AtExtTgt.
  exists (RTL_Returnstate stk ret1). eexists.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
inv FD.
assert (INCvisNu': inject_incr
  (restrict (as_inj nu')
     (vis
        (replace_externs nu'
           (fun b : Values.block =>
            DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
           (fun b : Values.block =>
            DomTgt nu' b &&
            (negb (locBlocksTgt nu' b) &&
             REACH m2' (exportedTgt nu' (ret2 :: nil)) b))))) (as_inj nu')).
      unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
      apply restrict_incr. 
assert (RC': REACH_closed m1' (mapped (as_inj nu'))).
        eapply inject_REACH_closed; eassumption.
assert (PHnu': meminj_preserves_globals (Genv.globalenv SrcProg) (as_inj nu')).
    subst. clear - INC SEP PG GF WDmu WDnu'.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    apply meminj_preserves_genv2blocks.
    split; intros.
      specialize (PGa _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      apply foreign_in_extern.
     assert (GG: isGlobalBlock SrcGe b = true).
          unfold isGlobalBlock, SrcGe. apply genv2blocksBool_char1 in H.
          rewrite H. trivial.
      Check frgnSrc.
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      assumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern. 
      assert (GG: isGlobalBlock SrcGe b = true). (*4 goals*)
          unfold isGlobalBlock, SrcGe. apply genv2blocksBool_char2 in H.
          rewrite H. intuition. (*3 goals*)
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
      apply foreign_in_extern; eassumption. (*2 goals*)
    eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
      remember (as_inj mu b1) as d.
      destruct d; apply eq_sym in Heqd. (*3 goals*)
        destruct p. 
        apply extern_incr_as_inj in INC; trivial. (*3 goals*)
        rewrite replace_locals_as_inj in INC.
        rewrite (INC _ _ _ Heqd) in H0. trivial. (*3 goals*)
      destruct SEP as [SEPa _].
        rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in SEPa. 
        destruct (SEPa _ _ _ Heqd H0).
        destruct (as_inj_DomRng _ _ _ _ PGb WDmu).
        congruence. (*1 goal*)
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H1); clear H1.
  apply orb_true_iff in IHL.
  remember (locBlocksSrc nu' b') as l.
  destruct l; apply eq_sym in Heql.
  (*case locBlocksSrc nu' b' = true*)
    clear IHL.
    remember (pubBlocksSrc nu' b') as p.
    destruct p; apply eq_sym in Heqp.
      assert (Rb': REACH m1' (mapped (as_inj nu')) b' = true).
        apply REACH_nil. 
        destruct (pubSrc _ WDnu' _ Heqp) as [bb2 [dd1 [PUB PT]]].
        eapply mappedI_true.
         apply (pub_in_all _ WDnu' _ _ _ PUB).
      assert (Rb:  REACH m1' (mapped (as_inj nu')) b = true).
        eapply REACH_cons; try eassumption.
      specialize (RC' _ Rb).
      destruct (mappedD_true _ _ RC') as [[b2 d1] AI'].
      remember (locBlocksSrc nu' b) as d.
      destruct d; simpl; trivial.
      apply andb_true_iff. 
      split. eapply as_inj_DomRng; try eassumption.
      eapply REACH_cons; try eassumption.
        apply REACH_nil. unfold exportedSrc.
        rewrite (pubSrc_shared _ WDnu' _ Heqp). intuition.
      destruct (UnchPrivSrc) as [UP UV]; clear UnchLOOR.
        specialize (UP b' z Cur Readable). 
        specialize (UV b' z). 
        destruct INC as [_ [_ [_ [_ [LCnu' [_ [PBnu' [_ [FRGnu' _]]]]]]]]].
        rewrite <- LCnu'. rewrite replace_locals_locBlocksSrc.  
        rewrite <- LCnu' in Heql. rewrite replace_locals_locBlocksSrc in *.
        rewrite <- PBnu' in Heqp. rewrite replace_locals_pubBlocksSrc in *.
        clear INCvisNu'. 
        rewrite Heql in *. simpl in *. intuition.
        assert (VB: Mem.valid_block m1 b').
          eapply VAL. unfold DOM, DomSrc. rewrite Heql. intuition.
        apply (H VB) in H2.
        rewrite (H0 H2) in H4. clear H H0.
        remember (locBlocksSrc mu b) as q.
        destruct q; simpl; trivial; apply eq_sym in Heqq.
        assert (Rb : REACH m1 (vis mu) b = true).
           eapply REACH_cons; try eassumption.
           apply REACH_nil. unfold vis. rewrite Heql; trivial.
        specialize (RC _ Rb). unfold vis in RC.
           rewrite Heqq in RC; simpl in *.
        rewrite replace_locals_frgnBlocksSrc in FRGnu'.
        rewrite FRGnu' in RC.
        apply andb_true_iff.  
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ RC). intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ RC). intuition.
  (*case DomSrc nu' b' &&
    (negb (locBlocksSrc nu' b') &&
     REACH m1' (exportedSrc nu' (ret1 :: nil)) b') = true*)
    destruct IHL. inv H.
    apply andb_true_iff in H. simpl in H. 
    destruct H as[DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchLOOR UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ MemInjNu' RET
               _ Rb' (fun b => true)) as [b2 [d1 [AI' _]]]; trivial.
           assert (REACH m1' (mapped (as_inj nu')) b = true).
             eapply REACH_cons; try eassumption.
             apply REACH_nil. eapply mappedI_true; eassumption.
           specialize (RC' _ H). 
           destruct (mappedD_true _ _ RC') as [[? ?] ?].
           eapply as_inj_DomRng; eassumption.
    eapply REACH_cons; try eassumption.
(*assert (RRR: REACH_closed m1' (exportedSrc nu' (ret1 :: nil))).
    intros b Hb. apply REACHAX in Hb.
       destruct Hb as [L HL].
       generalize dependent b.
       induction L ; simpl; intros; inv HL; trivial.
       specialize (IHL _ H1); clear H1.
       unfold exportedSrc.
       eapply REACH_cons; eassumption.*)

assert (RRC: REACH_closed m1' (fun b : Values.block =>
                         mapped (as_inj nu') b &&
                           (locBlocksSrc nu' b
                            || DomSrc nu' b &&
                               (negb (locBlocksSrc nu' b) &&
                           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
  eapply REACH_closed_intersection; eassumption.
assert (GFnu': forall b, isGlobalBlock (Genv.globalenv SrcProg) b = true ->
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
     intros. specialize (GF _ H).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in GF.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ GF). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ GF). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ GF). intuition.
split.
  unfold vis in *.
  rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
  econstructor; try eassumption.

(*
Lemma structured_match_callstack_incr_bound:
  forall f m tm cs bound tbound bound' tbound',
  match_stacks f m tm cs bound (*tbound*) ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_stacks f m tm cs bound' tbound'.
Proof.
  intros. inv H.
  econstructor; eauto. xomega. xomega. 
  constructor; auto. xomega. xomega.



    eapply structured_match_callstack_incr_bound.
Lemma structured_match_callstack_ext: forall mu m1 m2 cs bound 
  tbound
  (MCS : match_stacks mu m1 m2 cs bound tbound)
  m1' (FwdSrc : mem_forward m1 m1')
  nu vals1 vals2
  (Hnu: nu = replace_locals mu
                      (fun b0 : Values.block =>
                       locBlocksSrc mu b0 &&
                       REACH m1 (exportedSrc mu vals1) b0)
                      (fun b0 : Values.block =>
                       locBlocksTgt mu b0 &&
                       REACH m2 (exportedTgt mu vals2) b0))
  (SMvalMu : sm_valid mu m1 m2)
  (PG : meminj_preserves_globals (Genv.globalenv SrcProg) (as_inj mu))
  nu' (INC : extern_incr nu nu')
  (SEP : sm_inject_separated nu nu' m1 m2)
  (UNMAPPED : Mem.unchanged_on
                (fun (b : Values.block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1')
   m2' (FwdTgt : mem_forward m2 m2') (OUTOFREACH : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2')
  ret1 ret2 (WDnu' : SM_wd nu') (WDmu : SM_wd mu) (WDnu : SM_wd nu)
  (BND: Ple bound (Mem.nextblock m1))
  (TBND:Ple tbound (Mem.nextblock m2)),
match_stacks
  (replace_externs nu'
        (fun b : Values.block =>
         DomSrc nu' b &&
         (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
        (fun b : Values.block =>
         DomTgt nu' b &&
         (negb (locBlocksTgt nu' b) && REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
   m1' m2' cs bound tbound.
Proof.



      eapply structured_match_callstack_ext with
       (mu:=mu)(nu':=nu'); try reflexivity; try eassumption.
       eapply eff_after_check1 with (mu:=mu); try eassumption; try reflexivity.
         eapply forall_vals_inject_restrictD; eassumption.
       apply (forward_nextblock _ _ FwdSrc).
       apply (forward_nextblock _ _ FwdTgt).*)
admit.
Check replace_externs_as_inj.
    rewrite replace_externs_as_inj. assumption.
    (*Check restrict_val_inject.
    eapply restrict_val_inject; try eassumption.
    Print restrict_val_inject.
      (*eapply restrict_val_inject; try eassumption.*)
    intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
         unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H. trivial.*)
admit.
unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
Qed.

Hint Resolve Match_AfterExternal: trans_correct.
eauto with trans_correct.

Ltac openHyp:= match goal with
                     | [H: and _ _ |- _] => destruct H
                     | [H: exists _, _ |- _] => destruct H
                 end.


Lemma corestep_plus_star: 
   forall (st1 : RTL_core) (m1 : mem) (st1' : RTL_core) (m1' : mem)
   (CS: corestep rtl_eff_sem SrcGe st1 m1 st1' m1')
   (st2 : RTL_core) (mu : SM_Injection) (m2 : mem)
   (MC: MATCH st1 mu st1 m1 st2 m2),
   exists (st2' : RTL_core) (m2' : mem) (mu' : SM_Injection),
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH st1' mu' st1' m1' st2' m2' /\
     (*SM_wd mu' /\
     sm_valid mu' m1' m2' /\*)
     (corestep_plus rtl_eff_sem TrgGe st2 m2 st2' m2' \/
      (RTL_measure st1' < RTL_measure st1)%nat /\
      corestep_star rtl_eff_sem TrgGe st2 m2 st2' m2').
intros.
inv CS.
(*Skip *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      (*monadInv TR.*)
      destruct (MS_step_case_SkipSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        PRE TRF MCS MK) as [c2' [m2' [mu' [cstepPlus MS]]]].
      exists c2'. exists m2'. exists mu'. 
      intuition.
destruct MC as []
unfold corestep in *.
unfold core_data in *.
Check exploit.
exploit Match_corestep; eauto.
    intros [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    exists x, x0, x1.
    split; auto.

inv MC; 
repeat openHyp.
inv H.
 intros.
    exploit Match_corestep; eauto.
    intros [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    exists x, x0, x1.
    split; auto.

eapply corestep_plus_star; auto.
intros.
inv MC.
inv H; simpl in *.

SearchAbout intern_incr.


unfold   well_founded.
Print Acc.


































Lemma inject_val_inject_halted: forall (cd : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                       (m1 : mem) (c2 : RTL_core) (m2 : mem) (v1 : val) (MC: MATCH cd mu c1 m1 c2 m2) (Hl: halted rtl_eff_sem c1 = Some v1 ),
                                  exists v2 : val,
                                    Mem.inject (as_inj mu) m1 m2 /\
                                    val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
                                    halted rtl_eff_sem c2 = Some v2.
Proof.
intros. 
eexists.
unfold MATCH in MC.
destruct MC as [? MC].
inv H. simpl in *. inv Hl.  
destruct 
split; [|split].
unfold Mem.inject.
eapply MC.

{ intros. destruct H as [MC [RC [PG [GF [VAL [WD INJ]]]]]]. 
    eapply MATCH_safely_halted in MC; eauto.
    destruct MC as [v2 [A B]].
    exists v2. intuition. }


unfold MATCH in MC.  














(*Old proof*)
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold TrgGe in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.

  (*exploit function_ptr_translated; eauto.*)
  destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  eexists (RTL_Callstate nil _ vals2).
  split.
    subst. inv A. unfold SrcGe in C. rewrite C in Heqzz. inv Heqzz.
    unfold rtl_eff_sem (*, RTL_coop_sem*). simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    solve[rewrite D; auto].
    intros CONTRA.
    solve[elimtype False; auto].
(*  assert (exists targs tres, type_of_fundef f = Tfunction targs tres).
         destruct f; simpl. eexists; eexists. reflexivity.
         eexists; eexists. reflexivity.
  destruct H as [targs [tres Tfun]].*)
  destruct (core_initial_wd SrcGe TrgGe _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
  simpl in Ini.
  (* There is a better way to do this *)
  destruct Int.eq_dec in Ini; [destruct Genv.find_funct_ptr in Ini| ]; [ |discriminate | discriminate].
  inversion Ini.
    eapply match_call_states; try eassumption.
    eapply match_stacks_nil.
    unfold match_globalenvs.
      constructor.
      rewrite initial_SM_as_inj.
        unfold vis, initial_SM; simpl.
        apply forall_inject_val_list_inject.
        eapply restrict_forall_vals_inject; try eassumption.
          intros. apply REACH_nil. rewrite H; intuition.
    rewrite initial_SM_as_inj.
      unfold vis, initial_SM; simpl.
      eapply inject_restrict; eassumption.
  intuition.
    rewrite match_genv_meminj_preserves_extern_iff_all.
      assumption.
      apply BB.
      apply EE.
    (*as in selectionprffEFF*)
    rewrite initial_SM_as_inj.
      red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         destruct InitMem as [m0 [INIT_MEM [? ?]]].
         specialize (H0 _ _ _ INIT_MEM H). 
         destruct (valid_init_is_global _ R _ INIT_MEM _ H0) as [id Hid]. 
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock. 
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
    rewrite initial_SM_as_inj; assumption.
Qed.




apply MATCH_REACH_REACH.

apply inject_val_inject_halted.



Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
      map_wf_inj:
        (forall id1 id2 r,
           m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
      map_wf_disj:
        (forall id r,
           m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
    }.

Inductive match_states (j:meminj): CMinSel_core -> mem -> RTL_core -> mem -> Prop :=
| match_state:
    forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret sp'
           (MWF: map_wf map)
           (TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
           (TF: tr_fun tf map f ngoto nret rret)
           (TK: tr_cont j tf.(fn_code) map k ncont nexits ngoto nret rret cs)
           (ME: match_env j map e nil rs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm)
                 (*NEW:*) (SP: sp_preserved j sp sp'),
      match_states j (CMinSel_State f s k sp e) m
                   (RTL_State cs tf sp' ns rs) tm
| match_callstate:
    forall f args targs k m tm cs tf
           (TF: transl_fundef f = OK tf)
           (MS: match_stacks j k cs)
        (*(LD: Val.lessdef_list args targs)*)
        (AINJ: val_list_inject j args targs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm),
      match_states j (CMinSel_Callstate f args k) m
                   (RTL_Callstate cs tf targs) tm
| match_returnstate:
    forall v tv k m tm cs
           (MS: match_stacks j k cs)
        (*(LD: Val.lessdef v tv)*)
        (VINJ: val_inject j v tv)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm),
      match_states j (CMinSel_Returnstate v k) m
                   (RTL_Returnstate cs tv) tm.



Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Print effstep.
Print rtl_eff_sem.
Print vis.
Print locBlocksSrc.

Variable tprog: RTL.program.
Let tge : RTL.genv := Genv.globalenv tprog.
Print genv.

Lemma MATCH_effcore_diagram: forall 
                               st1 m1 st1' m1' (U1 : block -> Z -> bool) ge'
                               (CS: effstep rtl_eff_sem ge' U1 st1 m1 st1' m1') (* unpacks the effect step. RTL_effstep. *)
                               st2 mu m2 
                               (UHyp: forall b z, U1 b z = true -> 
                                                  Mem.valid_block m1 b -> vis mu b = true) (* Proof that allocated valid blocks are visible in the source*)
                             (*(MTCH: MATCH st1 mu st1 m1 st2 m2)*),
                             exists st2' m2' mu', exists U2 : block -> Z -> bool,
                                                    (effstep_plus rtl_eff_sem tge U2 st2 m2 st2' m2' \/
                                                     effstep_star rtl_eff_sem tge U2 st2 m2 st2' m2' (*/\ lt_state st1' st1*))
                                                    /\ intern_incr mu mu' /\
                                                    sm_inject_separated mu mu' m1 m2 /\
                                                    sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                                                    (*MATCH st1' mu' st1' m1' st2' m2' /\ *)
                                                    (forall (b : block) (ofs : Z),
                                                       U2 b ofs = true ->
                                                       Mem.valid_block m2 b /\
                                                       (locBlocksTgt mu b = false ->
                                                        exists (b1 : block) (delta1 : Z),
                                                          foreign_of mu b1 = Some (b, delta1) /\
                                                          U1 b1 (ofs - delta1)%Z = true /\
                                                          Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
  (*New script*)
  intros st1 m1 st1' m1' U1 ge' CS. intros. 
  eexists. exists m2, mu, EmptyEffect.
  split.
  right.






  intros st1 m1 st1' m1' U1 ge'. CS.

  induction CS; intros; eexists. (*12 Cases*)

  (*Case: skip seq*)
  exists m2, mu. 
  exists EmptyEffect.
  split.
  right.
  unfold vis in UHyp.
  unfold effstep_star; exists O; simpl.
  reflexivity.

  split. 
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.

  split.
  Lemma sm_locally_allocated_refl: forall mu m1 m2, sm_locally_allocated mu mu m1 m2 m1 m2.
  Admitted.
  apply sm_locally_allocated_refl.
  intros. unfold EmptyEffect in H0.
  contradict H0; auto.

  (*Case: skip block*)
  exists m2, mu.
  exists EmptyEffect. (*This should change*)
  split. 
  right.
  unfold effstep_star; exists O; simpl.
  reflexivity.

  split.
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.

  split.
  apply sm_locally_allocated_refl.

  intros. unfold EmptyEffect in H1.
  contradict H1; auto.

  (*Case: skip return*)
  exists m2, mu.
  exists EmptyEffect. (*This should change*)
  split. 
  right.
  unfold effstep_star; exists O; simpl.
  reflexivity.

  split.
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.

  split.
  apply sm_locally_allocated_refl.

  intros. unfold EmptyEffect in H2.
  contradict H2; auto.

  (*assign*)

  exists m2, mu.

  exists EmptyEffect. (*This should change*)
  split. 
  right.
  unfold effstep_star. exists O. simpl.
  reflexivity.

  split.
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.


  split. admit.

  intros. unfold EmptyEffect in H2.
  contradict H2; auto.




  split_allsplit.

  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  split. (* effste*)
  unfold effstep_plus.
  unfold effstep_star.
  (*Lemma about effstepN.*)

  Focus 2. split.
  (*intern_incr
unfold intern_incr.*)

  Focus 2. split.
  unfold sm_inject_separated.

  Focus 2. split.
  unfold sm_locally_allocated.
