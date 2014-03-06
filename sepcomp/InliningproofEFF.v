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
Definition globalfunction_ptr_inject (j:meminj):=
  forall b f, Genv.find_funct_ptr SrcGe b = Some f -> 
              j b = Some(b,0) /\ isGlobalBlock SrcGe b = true. 

(*The new match_states*)
(*Inductive match_states (j:meminj): RTL_core -> mem -> RTL_core -> mem -> Prop :=
| match_state:
    forall f s k sp e m tm cs tf ns rs (*map ncont nexits ngoto nret rret*) sp'
           (*(MWF: map_wf map)*)
           (*(TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)*)
           (*(TF: tr_fun tf map f ngoto nret rret)*)
           (*(TK: tr_cont j tf.(fn_code) map k ncont nexits ngoto nret rret cs)*)
           (*(ME: match_env j map e nil rs)*)
           (*(MEXT: Mem.extends m tm)*)
           (MINJ: Mem.inject j m tm)
    (*(*NEW:*) (SP: sp_preserved j sp sp')*),
      match_states j (RTL_State f s k sp e) m
                   (RTL_State cs tf sp' ns rs) tm
| match_callstate:
    forall f args targs k m tm cs tf
    (*(TF: transl_fundef f = OK tf)*)
    (*(MS: match_stacks j k cs)*)
    (*(LD: Val.lessdef_list args targs)*)
    (*(AINJ: val_list_inject j args targs) *)
    (*(MEXT: Mem.extends m tm)*)
    (*(MINJ: Mem.inject j m tm)*),
      match_states j (RTL_Callstate f args k) m
                   (RTL_Callstate cs tf targs) tm
| match_returnstate:
    forall v tv k m tm cs
    (*(MS: match_stacks j k cs)*)
    (*(LD: Val.lessdef v tv)*)
    (*(VINJ: val_inject j v tv)*)
    (*(MEXT: Mem.extends m tm)*)
    (*(MINJ: Mem.inject j m tm)*),
      match_states j (RTL_Returnstate v k) m
                   (RTL_Returnstate cs tv) tm.*)

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

Inductive match_states: RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_regular_states: forall (mu: SM_Injection) stk f sp pc rs m stk' f' sp' rs' m' ctx
        (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs (as_inj mu) ctx rs rs')
        (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject (as_inj mu) m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (RTL_State stk f (Vptr sp Int.zero) pc rs) m
                   (RTL_State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs') m'
  | match_call_states: forall (mu: SM_Injection) stk fd args m stk' fd' args' m'
        (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
        (FD: transf_fundef fenv fd = OK fd')
        (VINJ: val_list_inject  (as_inj mu) args args')
        (MINJ: Mem.inject (as_inj mu) m m'),
      match_states (RTL_Callstate stk fd args) m
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
      match_states (RTL_Callstate stk (Internal f) vargs) m
                   (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'
  | match_return_states: forall (mu: SM_Injection) stk v m stk' v' m'
        (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
        (VINJ: val_inject (as_inj mu) v v')
        (MINJ: Mem.inject (as_inj mu) m m'),
      match_states (RTL_Returnstate stk v) m
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
      match_states (RTL_Returnstate stk v) m
                   (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'.


Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (*(restrict (as_inj mu) (vis mu))*) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals SrcGe (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.


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
  eapply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf.

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

  Lemma restrict_preserves_globalfun_ptr: forall j X
  (PG : globalfunction_ptr_inject j)
  (Glob : forall b, isGlobalBlock SrcGe b = true -> X b = true),
globalfunction_ptr_inject (restrict j X).
Proof. intros.
  red; intros. 
  destruct (PG _ _ H). split; trivial.
  apply restrictI_Some; try eassumption.
  apply (Glob _ H1).
Qed.
Lemma MATCH_restrict: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                 (m1 : mem) (c2 : RTL_core) (m2 : mem) (X : block -> bool) (MC: MATCH d mu c1 m1 c2 m2)(HX: forall b : block, vis mu b = true -> X b = true)(RC0:REACH_closed m1 X), MATCH d (restrict_sm mu X) c1 m1 c2 m2.
intros.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  (*rewrite vis_restrict_sm.*)
  (*rewrite restrict_sm_all.*)
  (*rewrite restrict_nest;*) intuition.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. rewrite restrict_sm_all.
  eapply restrict_preserves_globalfun_ptr; try eassumption.
  unfold vis in HX. intuition.
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply Glob.
split. 
  destruct SMV.
  split; intros.
    rewrite restrict_sm_DOM in H1.
    apply (H _ H1).
  rewrite restrict_sm_RNG in H1.
    apply (H0 _ H1).
split. assumption.
  rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.
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

admit.

Lemma Match_Halted: forall (cd : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
     (m1 : mem) (c2 : RTL_core) (m2 : mem) (v1 : val)(MC:
   MATCH cd mu c1 m1 c2 m2)(HL:
   halted rtl_eff_sem c1 = Some v1),
   exists v2 : val,
     Mem.inject (as_inj mu) m1 m2 /\
     val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
     halted rtl_eff_sem c2 = Some v2.
Proof.
intros.
inv MC.
repeat  match goal with
      | H: _ /\ _ |- _ => inv H
  end.
Print val_inject.
destruct H.
(*match_regular_states*)
eexists v1.
split; try assumption.
split. 
Focus 2.


destruct v1; try constructor.
Print val_inject.
eapply val_inject_ptr.

(*match_call_states*)
(*match_call_regular_states*)
(*match_return_states*)
(*match_return_regular_states*)


eexists.
split. apply H7.
induction H.










Lemma MATCH_safely_halted: forall mu c1 m1 c2 m2 v1
     (SMC: match_states c1 m1 c2 m2)
     (HALT: halted rtl_eff_sem c1 = Some v1),
exists v2, halted rtl_eff_sem c2 = Some v2 /\ 
           val_inject (restrict (as_inj mu) (vis mu)) v1 v2.
Proof.
  intros.
  inv SMC; simpl in *; inv HALT.
  destruct stk; inv H0.
  destruct stk'.
  exists v'; split; try reflexivity.

  (*eapply restrict_val_inject.*) eapply VINJ.
exists nil.
  inv MK. split; trivial.
(*  eapply val_inject_incr; try eassumption.
    apply restrict_incr.*)
Qed.*)




Lemma MATCH_initial_core: forall v1 v2 sig entrypoints
      (EP: In (v1, v2, sig) entrypoints)
      (entry_points_ok : forall (v1 v2 : val) (sig : signature),
                  In (v1, v2, sig) entrypoints ->
                  exists b f1 f2,
                    v1 = Vptr b Int.zero /\
                    v2 = Vptr b Int.zero /\
                    Genv.find_funct_ptr SrcGe b = Some f1 /\
                    Genv.find_funct_ptr TrgGe b = Some f2)
      vals1 c1 m1 j vals2 m2 (DomS DomT : block -> bool)
      (Ini: initial_core rtl_eff_sem SrcGe v1 vals1 = Some c1)
      (Inj: Mem.inject j m1 m2)
      (VInj: Forall2 (val_inject j) vals1 vals2)
      (PG:meminj_preserves_globals SrcGe j)
      (R : list_norepet (map fst (prog_defs SrcProg)))
      (J: forall b1 b2 delta, j b1 = Some (b2, delta) -> 
            (DomS b1 = true /\ DomT b2 = true))
      (RCH: forall b, REACH m2 
          (fun b' : block => isGlobalBlock TrgGe b' || getBlocks vals2 b') b = true ->
          DomT b = true)
      (InitMem : exists m0 : mem, Genv.init_mem SrcProg = Some m0 
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m1) 
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))   
      (GDE: genvs_domain_eq SrcGe TrgGe)
      (HDomS: forall b : block, DomS b = true -> Mem.valid_block m1 b)
      (HDomT: forall b : block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core rtl_eff_sem TrgGe v2 vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1 (fun b : block => isGlobalBlock SrcGe b || getBlocks vals1 b))
       (REACH m2 (fun b : block => isGlobalBlock TrgGe b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
  intros.
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold TrgGe in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz. destruct zz. 
  unfold SrcGe in H0. inv H0. 
    apply eq_sym in Heqzz.
  rewrite Heqzz in H1.
  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  exists (RTL_Callstate nil tf vals2).
  split.
    destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. unfold SrcGe in *; rewrite C in Heqzz. inv Heqzz. 
    unfold TrgGe in FP. rewrite D in FP. inv FP.
    unfold rtl_eff_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    solve[rewrite D; auto].

    intros CONTRA; contradiction CONTRA; reflexivity.
    inv H1.

(*  assert (exists targs tres, type_of_fundef f = Tfunction targs tres).
         destruct f; simpl. eexists; eexists. reflexivity.
         eexists; eexists. reflexivity.
  destruct H as [targs [tres Tfun]].*)
  destruct (core_initial_wd SrcGe TrgGe _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    eapply match_call_states; try eassumption.
      econstructor.
      Print match_globalenvs.
      Print initial_SM_as_inj.
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


















(*Proof 0.2*)
intros.
  inversion Ini.
  unfold  RTL_initial_core in H0. unfold SrcGe in *. unfold TrgGe in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  eexists (RTL_Callstate _ _ _).
  split.
  simpl. 
  destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  subst. inv A. rewrite C in Heqzz. inv Heqzz. unfold TrgGe in *; rewrite D in FIND. inv FIND.
  unfold RTL_initial_core. 
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
  solve[rewrite D; auto].
  intros CONTRA.
  solve[elimtype False; auto].
  destruct InitMem as [m0 [INIT_MEM [A B]]].
  split.
  eapply match_call_states; try eassumption.
  (*eapply RTL_Callstate (*with (cenv:=PTree.empty _)(cs := @nil frame)*); try eassumption.*)
    eapply match_stacks_nil.
(*
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (FD: transf_fundef fenv fd = OK fd')
        (VINJ: val_list_inject F args args')
        (MINJ: Mem.inject F m m'),
*)

    (*assert (Genv.init_mem TrgProg = Some m0).*)
    unfold match_globalenvs.
      unfold transl_program in TRANSL.
      solve[eapply Genv.init_mem_transf_partial in TRANSL; eauto].
    (*rewrite initial_SM_as_inj. unfold vis. unfold initial_SM; simpl.
      eapply inject_mapped; try eassumption.
       eapply restrict_mapped_closed.
         eapply inject_REACH_closed; eassumption.
         apply REACH_is_closed.
       apply restrict_incr.*)
    (*rewrite initial_SM_as_inj. *)
      apply st_mcs_nil with (Mem.nextblock m0).
    eapply (match_globalenvs_init' _ R _ _ INIT_MEM).
      (*rewrite restrict_sm_all.*) rewrite initial_SM_as_inj.
      eapply restrict_preserves_globals; try eassumption.
      unfold vis, initial_SM; simpl; intros.
      apply REACH_nil. rewrite H0; trivial.
    apply A. apply B.
    econstructor. simpl. trivial.
    (*rewrite restrict_sm_all.*) rewrite initial_SM_as_inj.
      unfold vis, initial_SM; simpl.
      apply forall_inject_val_list_inject.
      eapply restrict_forall_vals_inject; try eassumption.
        intros. apply REACH_nil. rewrite H; intuition.
(*
    eapply restrict_preserves_globals; try eassumption.
      rewrite initial_SM_as_inj. assumption.
      intros. unfold vis, initial_SM; simpl. 
      apply REACH_nil. rewrite H; trivial.*)
destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
    VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
   as [AA [BB [CC [DD [EE [FF GG]]]]]].
intuition. rewrite initial_SM_as_inj. assumption.
rewrite initial_SM_as_inj. assumption.
(*protected: red. simpl. intros. discriminate.*)
Qed.





Lemma MATCH_safely_halted: forall mu c1 m1 c2 m2 v1
     (SMC: match_states c1 m1 c2 m2)
     (HALT: halted rtl_eff_sem c1 = Some v1),
exists v2, halted rtl_eff_sem c2 = Some v2 /\ 
           val_inject (restrict (as_inj mu) (vis mu)) v1 v2.
Proof.
  intros.
  inv SMC; simpl in *; inv HALT.
  destruct stk; inv H0.
  destruct stk'.
  exists v'; split; try reflexivity. eapply VINJ.
  Print val.
exists nil.
  inv MK. split; trivial.
(*  eapply val_inject_incr; try eassumption.
    apply restrict_incr.*)
Qed.*)

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
Lemma at_external_lemma: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) 
                                (c2 : RTL_core) (m2 : mem) (e : external_function) 
                                (vals1 : list val) (ef_sig : signature),
                           MATCH c1 mu c1 m1 c2 m2 ->
                           at_external rtl_eff_sem c1 = Some (e, ef_sig, vals1) ->
                           Mem.inject (as_inj mu) m1 m2 /\
                           (exists vals2 : list val,
                              Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
                              at_external rtl_eff_sem c2 = Some (e, ef_sig, vals2)).
Admitted.
apply at_external_lemma.



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
