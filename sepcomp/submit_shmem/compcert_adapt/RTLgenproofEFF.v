(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for RTL generation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Switch.
Require Import Registers.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import RTL.
Require Import RTLgen.
Require Import RTLgenspec.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.
Require Import CminorSel_coop.
Require Import CminorSel_eff.
Require Import RTL_coop.
Require Import RTL_eff.

(** * Correspondence between Cminor environments and RTL register sets *)

(** A compilation environment (mapping) is well-formed if
  the following properties hold:
- Two distinct Cminor local variables are mapped to distinct pseudo-registers.
- A Cminor local variable and a let-bound variable are mapped to
  distinct pseudo-registers.
*)

Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.

Lemma init_mapping_wf:
  map_wf init_mapping.
Proof.
  unfold init_mapping; split; simpl.
  intros until r. rewrite PTree.gempty. congruence.
  tauto.
Qed.

Lemma add_var_wf:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  intros. monadInv H.
  apply mk_map_wf; simpl.
  intros until r0. repeat rewrite PTree.gsspec.
  destruct (peq id1 name); destruct (peq id2 name).
  congruence.
  intros. inv H. elimtype False.
  apply valid_fresh_absurd with r0 s1.
  apply H1. left; exists id2; auto.
  eauto with rtlg.
  intros. inv H2. elimtype False.
  apply valid_fresh_absurd with r0 s1.
  apply H1. left; exists id1; auto.
  eauto with rtlg.
  inv H0. eauto.
  intros until r0. rewrite PTree.gsspec.
  destruct (peq id name).
  intros. inv H.
  apply valid_fresh_absurd with r0 s1.
  apply H1. right; auto.
  eauto with rtlg.
  inv H0; eauto.
Qed.

Lemma add_vars_wf:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  induction names; simpl; intros; monadInv H.
  auto.
  exploit add_vars_valid; eauto. intros [A B].
  eapply add_var_wf; eauto.
Qed.

Lemma add_letvar_wf:
  forall map r,
  map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
Proof.
  intros. inv H. unfold add_letvar; constructor; simpl.
  auto.
  intros. elim H1; intro. subst r0. elim H0. left; exists id; auto.
  eauto.
Qed.

(** An RTL register environment matches a CminorSel local environment and
  let-environment if the value of every local or let-bound variable in
  the CminorSel environments is identical to the value of the
  corresponding pseudo-register in the RTL register environment. *)

(*LENB: replaced extension by injection. In particular, added paranmeter j:meminj
  and replaced lessdefs by val_injects*)

Record match_env (j:meminj)
      (map: mapping) (e: env) (le: letenv) (rs: regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r
          /\ val_inject j v rs#r);
    me_letvars:
      val_list_inject j le rs##(map.(map_letvars))
  }.

Lemma match_env_find_var:
  forall j map e le rs id v r,
  match_env j map e le rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  val_inject j v rs#r.
Proof.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed.

Lemma match_env_inject_incr: forall j map e le rs
        (MENV: match_env j map e le rs) j'
        (INC: inject_incr j j'),
      match_env j' map e le rs.
Proof.
  intros.
  destruct MENV as [MENVa MENVb].
  constructor; intros.
    destruct (MENVa _ _ H) as [r [MAP INJ]].
    apply (val_inject_incr _ _ _ _ INC) in INJ.
    exists r; split; trivial.
  apply (val_list_inject_incr _ _ _ _ INC) in MENVb; trivial.
Qed.

Lemma match_env_restrictD: forall j X map e le rs
        (MENV: match_env (restrict j X) map e le rs),
      match_env j map e le rs.
Proof. intros.
  eapply match_env_inject_incr; try eassumption.
  eapply restrict_incr.
Qed.

Lemma match_env_find_letvar:
  forall j map e le rs idx v r,
  match_env j map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  val_inject j v rs#r.
Proof.
  intros. exploit me_letvars; eauto.
  clear H. revert le H0 H1. generalize (map_letvars map). clear map.
  induction idx; simpl; intros.
  inversion H; subst le; inversion H0. subst v0.
  destruct l; inversion H1. subst r0.
  inversion H2. subst v'. auto.
  destruct l; destruct le; try discriminate.
  eapply IHidx; eauto.
  inversion H. auto.
Qed.

Lemma match_env_invariant:
  forall j map e le rs rs',
  match_env j map e le rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env j map e le rs'.
Proof.
  intros. inversion H. apply mk_match_env.
  intros. exploit me_vars0; eauto. intros [r [A B]].
  exists r; split. auto. rewrite H0; auto. left; exists id; auto.
  replace (rs'##(map_letvars map)) with (rs ## (map_letvars map)). auto.
  apply list_map_exten. intros. apply H0. right; auto.
Qed.

(** Matching between environments is preserved when an unmapped register
  (not corresponding to any Cminor variable) is assigned in the RTL
  execution. *)

Lemma match_env_update_temp:
  forall j map e le rs r v,
  match_env j map e le rs ->
  ~(reg_in_map map r) ->
  match_env j map e le (rs#r <- v).
Proof.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro.
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.

(** Matching between environments is preserved by simultaneous
  assignment to a Cminor local variable (in the Cminor environments)
  and to the corresponding RTL pseudo-register (in the RTL register
  environment). *)

Lemma match_env_update_var:
  forall j map e le rs id r v tv,
  val_inject j v tv ->
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env j map e le rs ->
  match_env j map (PTree.set id v e) le (rs#r <- tv).
Proof.
  intros. inversion H0. inversion H2. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H3. exists r; split. auto. rewrite PMap.gss. auto.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'. elim n. eauto.
  erewrite list_map_exten. eauto.
  intros. symmetry. apply PMap.gso. red; intros. subst x. eauto.
Qed.

(** A variant of [match_env_update_var] where a variable is optionally
  assigned to, depending on the [dst] parameter. *)

Lemma match_env_update_dest:
  forall j map e le rs dst r v tv,
  val_inject j v tv ->
  map_wf map ->
  reg_map_ok map r dst ->
  match_env j map e le rs ->
  match_env j map (set_optvar dst v e) le (rs#r <- tv).
Proof.
  intros. inv H1; simpl.
  eapply match_env_update_temp; eauto.
  eapply match_env_update_var; eauto.
Qed.
Hint Resolve match_env_update_dest: rtlg.

(** Matching and [let]-bound variables. *)

Lemma match_env_bind_letvar:
  forall j map e le rs r v,
  match_env j map e le rs ->
  val_inject j v rs#r ->
  match_env j (add_letvar map r) e (v :: le) rs.
Proof.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
  forall j map e le rs r v,
  match_env j (add_letvar map r) e (v :: le) rs ->
  match_env j map e le rs.
Proof.
  unfold add_letvar; intros. inv H. simpl in *.
  constructor. auto. inversion me_letvars0. auto.
Qed.

(** Matching between initial environments. *)

Lemma match_env_empty:
  forall j map,
  map.(map_letvars) = nil ->
  match_env j map (PTree.empty val) nil (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H0. discriminate.
  rewrite H. constructor.
Qed.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)

Lemma match_set_params_init_regs:
  forall j il rl s1 map2 s2 vl tvl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  val_list_inject j vl tvl ->
  match_env j map2 (set_params vl il) nil (init_regs tvl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs tvl rl)#r = Vundef).
Proof.
  induction il; intros.

  inv H. split. apply match_env_empty. auto. intros.
  simpl. apply Regmap.gi.

  monadInv H. simpl.
  exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
  exploit add_var_valid; eauto. intros [A' B']. clear B'.
  monadInv EQ1.
  destruct H0 as [ | v1 tv1 vs tvs].
  (* vl = nil *)
  destruct (IHil _ _ _ _ nil nil _ EQ) as [ME UNDEF]. constructor. inv ME. split.
  replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0, me_letvars0.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. constructor.
  eauto.
  eauto.
  destruct x; reflexivity.
  intros. apply Regmap.gi.
  (* vl = v1 :: vs *)
  destruct (IHil _ _ _ _ _ _ _ EQ H0) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. (*inv H.*) inv H1. exists x1; split. auto. rewrite Regmap.gss. assumption.
  exploit me_vars0; eauto. intros [r' [C D]].
  exists r'; split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  apply B. left; exists id; auto.
  eauto with rtlg.
  destruct (map_letvars x0). auto. simpl in me_letvars0. inversion me_letvars0.
  intros. rewrite Regmap.gso. apply UNDEF.
  apply reg_fresh_decr with s2; eauto with rtlg.
  apply sym_not_equal. apply valid_fresh_different with s2; auto.
Qed.

Lemma match_set_locals:
  forall j map1 s1,
  map_wf map1 ->
  forall il rl map2 s2 e le rs i,
  match_env j map1 e le rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env j map2 (set_locals il e) le rs.
Proof.
  induction il; simpl in *; intros.

  inv H2. auto.

  monadInv H2.
  exploit IHil; eauto. intro.
  monadInv EQ1.
  constructor.
  intros id v. simpl. repeat rewrite PTree.gsspec.
  destruct (peq id a). subst a. intro.
  exists x1. split. auto. inv H3. constructor.
  eauto with rtlg.
  intros. eapply me_vars; eauto.
  simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
  forall j params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  val_list_inject j vparams tvparams ->
  match_env j map2 (set_locals vars (set_params vparams params))
            nil (init_regs tvparams rparams).
Proof.
  intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed.

(** * The simulation argument *)

Require Import Errors.

Section CORRECTNESS.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof
  (Genv.find_symbol_transf_partial transl_fundef _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: CminorSel.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).

Lemma functions_translated:
  forall (v: val) (f: CminorSel.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transl_fundef _ TRANSL).

Lemma sig_transl_function:
  forall (f: CminorSel.fundef) (tf: RTL.fundef),
  transl_fundef f = OK tf ->
  RTL.funsig tf = CminorSel.funsig f.
Proof.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function.
  destruct (reserve_labels (fn_body f0) (PTree.empty node, init_state)) as [ngoto s0].
  case (transl_fun f0 ngoto s0); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof
  (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).

(*LENB: GFP as in selectionproofEFF*)
Definition globalfunction_ptr_inject (j:meminj):=
  forall b f, Genv.find_funct_ptr ge b = Some f ->
              j b = Some(b,0) /\ isGlobalBlock ge b = true.

Lemma restrict_preserves_globalfun_ptr: forall j X
  (PG : globalfunction_ptr_inject j)
  (Glob : forall b, isGlobalBlock ge b = true -> X b = true),
globalfunction_ptr_inject (restrict j X).
Proof. intros.
  red; intros.
  destruct (PG _ _ H). split; trivial.
  apply restrictI_Some; try eassumption.
  apply (Glob _ H1).
Qed.

Lemma restrict_GFP_vis: forall mu
  (GFP : globalfunction_ptr_inject (as_inj mu))
  (Glob : forall b, isGlobalBlock ge b = true ->
                    frgnBlocksSrc mu b = true),
  globalfunction_ptr_inject (restrict (as_inj mu) (vis mu)).
Proof. intros.
  unfold vis.
  eapply restrict_preserves_globalfun_ptr. eassumption.
  intuition.
Qed.

(*From Cminorgenproof*)
Remark val_inject_function_pointer:
  forall v fd j tv,
  Genv.find_funct ge v = Some fd ->
  globalfunction_ptr_inject j ->
  val_inject j v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  inv H1.
  rewrite Genv.find_funct_find_funct_ptr in H.
  destruct (H0 _ _ H).
  rewrite H1 in H4; inv H4.
  rewrite Int.add_zero. trivial.
Qed.

(** Correctness of the code generated by [add_move]. *)

Lemma tr_move_correct:
  forall r1 ns r2 nd cs f sp rs m,
  tr_move f.(fn_code) ns r1 nd r2 ->
  exists rs',
  corestep_star rtl_eff_sem tge
     (RTL_State cs f sp ns rs) m
     (RTL_State cs f sp nd rs') m /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H.
  exists rs; split. eapply corestep_star_zero. auto.
  exists (rs#r2 <- (rs#r1)); split.
  apply corestep_star_one. eapply rtl_corestep_exec_Iop. eauto. auto.
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

(** Correctness of the translation of [switch] statements *)

Lemma transl_switch_correct:
  forall j cs sp e m f map r nexits t ns,
  tr_switch f.(fn_code) map r nexits t ns ->
  forall rs i act,
  rs#r = Vint i ->
  map_wf map ->
  match_env j map e nil rs ->
  comptree_match i t = Some act ->
  exists nd, exists rs',
  corestep_star rtl_eff_sem  tge (RTL_State cs f sp ns rs) m (RTL_State cs f sp nd rs') m /\
  nth_error nexits act = Some nd /\
  match_env j map e nil rs'.
Proof.
  Opaque Int.sub.
  induction 1; simpl; intros.
(* action *)
  inv H3. exists n; exists rs; intuition.
  apply corestep_star_zero.
(* ifeq *)
  caseEq (Int.eq i key); intro EQ; rewrite EQ in H5.
  inv H5. exists nfound; exists rs; intuition.
  apply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := true); eauto.
  simpl. rewrite H2. simpl. congruence.
  exploit IHtr_switch; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply corestep_star_trans.
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := false); eauto.
      simpl. rewrite H2. simpl. congruence. eexact EX.
(* iflt *)
  caseEq (Int.ltu i key); intro EQ; rewrite EQ in H5.
  exploit IHtr_switch1; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply corestep_star_trans.
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := true); eauto.
    simpl. rewrite H2. simpl. congruence. eexact EX.
  exploit IHtr_switch2; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply corestep_star_trans.
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := false); eauto.
    simpl. rewrite H2. simpl. congruence. eexact EX.
(* jumptable *)
  set (rs1 := rs#rt <- (Vint(Int.sub i ofs))).
  assert (ME1: match_env j map e nil rs1).
    unfold rs1. eauto with rtlg.
  assert (EX1: RTL_corestep tge (RTL_State cs f sp n rs) m (RTL_State cs f sp n1 rs1) m).
    eapply rtl_corestep_exec_Iop; eauto.
    predSpec Int.eq Int.eq_spec ofs Int.zero; simpl.
    rewrite H10. rewrite Int.sub_zero_l. congruence.
    rewrite H6. simpl. rewrite <- Int.sub_add_opp. auto.
  caseEq (Int.ltu (Int.sub i ofs) sz); intro EQ; rewrite EQ in H9.
  exploit H5; eauto. intros [nd [A B]].
  exists nd; exists rs1; intuition.
  eapply corestep_star_trans.
    eapply corestep_star_one. eexact EX1.
  eapply corestep_star_trans.
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := true); eauto.
    simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
  apply corestep_star_one. eapply rtl_corestep_exec_Ijumptable; eauto. unfold rs1. apply Regmap.gss.
  exploit (IHtr_switch rs1); eauto. unfold rs1. rewrite Regmap.gso; auto.
  intros [nd [rs' [EX [NTH ME]]]].
  exists nd; exists rs'; intuition.
  eapply corestep_star_trans.
    eapply corestep_star_one. eexact EX1.
  eapply corestep_star_trans.
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := false); eauto.
    simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
  eexact EX.
Qed.

(** ** Semantic preservation for the translation of expressions *)

(*LENB: translation of sp. Contrary to selection phase,
  the use of eval_operation (and the existing lemmas about
  eval_operation_inject) here suggests we should
  require sp=Vptr b Int.zero and sp' = Vptr b' Int.zero instead
  of sp=Vptr b i and sp' = Vptr b' i for some arbitrary i.
  Let's see whether this works...*)
Definition sp_preserved (j:meminj) (sp sp':val) :=
    exists b b', sp = Vptr b Int.zero /\ sp' = Vptr b' Int.zero /\
                j b = Some(b',0).

Lemma shift_stack_addressing_zero: forall addr,
 shift_stack_addressing (Int.repr 0) addr = addr.
Proof. intros.
  destruct addr; try reflexivity.
  simpl. rewrite Int.add_zero_l. trivial.
Qed.

Section CORRECTNESS_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    e, le, m, a ------------- State cs code sp ns rs tm
         ||                      |
         ||                      |*
         ||                      |
         \/                      v
    e, le, m, v ------------ State cs code sp nd rs' tm'
                    I /\ Q
>>
  where [tr_expr code map pr a ns nd rd] is assumed to hold.
  The left vertical arrow represents an evaluation of the expression [a].
  The right vertical arrow represents the execution of zero, one or
  several instructions in the generated RTL flow graph [code].

  The invariant [I] is the agreement between Cminor environments and
  RTL register environment, as captured by [match_envs].

  The precondition [P] includes the well-formedness of the compilation
  environment [mut].

  The postconditions [Q] state that in the final register environment
  [rs'], register [rd] contains value [v], and the registers in
  the set of preserved registers [pr] are unchanged, as are the registers
  in the codomain of [map].

  We formalize this simulation property by the following predicate
  parameterized by the CminorSel evaluation (left arrow).  *)

Definition transl_expr_prop
     (le: letenv) (a: expr) (v: val) : Prop :=
  forall j tm cs f map pr ns nd rd rs dst
 (*NEW:*)(PG: meminj_preserves_globals ge j)
         sp' (SP: sp_preserved j sp sp')

    (MWF: map_wf map)
    (TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
    (ME: match_env j map e le rs)
    (EXT: Mem.inject j m tm),
  exists rs', exists tm',
     corestep_star rtl_eff_sem tge
        (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env j map (set_optvar dst v e) le rs'
  /\ val_inject j v rs'#rd
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject j m tm' /\ tm=tm'.

Definition transl_exprlist_prop
     (le: letenv) (al: exprlist) (vl: list val) : Prop :=
  forall j tm cs f map pr ns nd rl rs
 (*NEW:*)(PG: meminj_preserves_globals ge j)
         sp' (SP: sp_preserved j sp sp')

    (MWF: map_wf map)
    (TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
    (ME: match_env j map e le rs)
    (EXT: Mem.inject j m tm),
  exists rs', exists tm',
     corestep_star rtl_eff_sem tge
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env j map e le rs'
  /\ val_list_inject j vl rs'##rl
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject j m tm' /\ tm=tm'.

Definition transl_condexpr_prop
     (le: letenv) (a: condexpr) (v: bool) : Prop :=
  forall j tm cs f map pr ns ntrue nfalse rs
 (*NEW:*)(PG: meminj_preserves_globals ge j)
         sp' (SP: sp_preserved j sp sp')

    (MWF: map_wf map)
    (TE: tr_condition f.(fn_code) map pr a ns ntrue nfalse)
    (ME: match_env j map e le rs)
    (EXT: Mem.inject j m tm),
  exists rs', exists tm',
     corestep_plus rtl_eff_sem tge
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' (if v then ntrue else nfalse) rs') tm'
  /\ match_env j map e le rs'
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject j m tm' /\ tm=tm'.

(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma transl_expr_Evar_correct:
  forall (le : letenv) (id : positive) (v: val),
  e ! id = Some v ->
  transl_expr_prop le (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]].
  exists rs'; exists tm; split. eauto.
  destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto.
  split. eapply match_env_invariant; eauto.
  split. congruence.
  split; auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto.
  split. congruence.
  split. intros. apply C. intuition congruence.
  auto.
Qed.

Lemma transl_expr_Eop_correct:
  forall (le : letenv) (op : operation) (args : exprlist)
         (vargs : list val) (v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  eval_operation ge sp op vargs m = Some v ->
  transl_expr_prop le (Eop op args) v.
Proof.
  intros; red; intros. inv TE.
(* normal case *)
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 [EXT1 X]]]]]]]; subst tm.
  (*Was: edestruct eval_operation_lessdef...*)

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_operation_inject as [v' []]; eauto.
  rewrite eval_shift_stack_operation in H2. simpl in H2. rewrite Int.add_zero in H2.

  exists (rs1#rd <- v'); exists tm1.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
  eapply corestep_star_one. eapply rtl_corestep_exec_Iop; eauto.
  rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ ge tge). eauto.
  exact symbols_preserved.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) (vargs : list val) (vaddr v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  Op.eval_addressing ge sp addr vargs = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  transl_expr_prop le (Eload chunk addr args) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst tm.
  (*Was: edestruct eval_addressing_lessdef as [vaddr' []]; eauto.*)

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_addressing_inject as [vaddr' [? ?]]; eauto.
  rewrite shift_stack_addressing_zero in H3; simpl in H3.
  edestruct Mem.loadv_inject as [v' []]; eauto.
  exists (rs1#rd <- v'); exists tm1.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
    eapply corestep_star_one.
      eapply rtl_corestep_exec_Iload; try eassumption.
    rewrite (eval_addressing_preserved ge). assumption.
       exact symbols_preserved.
(* Match-env *)
  split. eauto with rtlg.
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Econdition_correct:
  forall (le : letenv) (a: condexpr) (ifso ifnot : expr)
         (va : bool) (v : val),
  eval_condexpr ge sp e m le a va ->
  transl_condexpr_prop le a va ->
  eval_expr ge sp e m le (if va then ifso else ifnot) v ->
  transl_expr_prop le (if va then ifso else ifnot) v ->
  transl_expr_prop le (Econdition a ifso ifnot) v.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 [EXT1 X]]]]]]; subst tm.
  assert (tr_expr f.(fn_code) map pr (if va then ifso else ifnot) (if va then ntrue else nfalse) nd rd dst).
    destruct va; auto.
  exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply corestep_star_trans.
           apply corestep_plus_star. eexact EX1. eexact EX2.
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r); auto.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Elet_correct:
  forall (le : letenv) (a1 a2 : expr) (v1 v2 : val),
  eval_expr ge sp e m le a1 v1 ->
  transl_expr_prop le a1 v1 ->
  eval_expr ge sp e m (v1 :: le) a2 v2 ->
  transl_expr_prop (v1 :: le) a2 v2 ->
  transl_expr_prop le (Elet a1 a2) v2.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst tm.
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H2; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [EX2 [ME3 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r0); auto.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Eletvar_correct:
  forall (le : list val) (n : nat) (v : val),
  nth_error le n = Some v ->
  transl_expr_prop le (Eletvar n) v.
Proof.
  intros; red; intros; inv TE.
  exploit tr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1; exists tm.
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split.
  destruct H2 as [[A B] | [A B]].
  subst r dst; simpl.
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto.
(* Other regs *)
  split. intros.
  destruct H2 as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
(* Mem *)
  auto.
Qed.

(*LENB: TODO: builtin: Lemma doesn;'t quite hold -nned to extend j -> j'.
  But maye we won't need this case, if
  builtin-expressions can be eliminated from CminorSel.expressions*)
Lemma transl_expr_Ebuiltin_correct:
  forall le ef al vl v,
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  transl_expr_prop le (Ebuiltin ef al) v.
Proof.
  admit. (*We do not yet support use of builtins for 64-bit operations.*)
Qed.
(*Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
  (*WAS: exploit external_call_mem_extends; eauto.
        intros [v' [tm2 [A [B [C [D E]]]]]].*)
  exploit external_call_mem_inject; eauto.
        intros [j' [v' [tm2 [A [B [C [D [E [F G]]]]]]]]].
  exists (rs1#rd <- v'); exists tm2.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
         apply corestep_star_one. eapply rtl_corestep_exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.
(* Match-env *)
  split. eapply match_env_update_dest; try eassumption.
         eapply val_inject_incr. eassumption. split; intros.  eexists. eauto with rtlg.
(* Result reg *)
  split. intros. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.
*)

(*LENB: Lemma should not be needed any more since external calls are
 handled by coresemantics interface now. We can probably eliminate
  external expressions from CminorSel.v, but that's a modification of a
  language definition*)
Lemma transl_expr_Eexternal_correct:
  forall le id sg al b ef vl v,
  Genv.find_symbol ge id = Some b ->
  Genv.find_funct_ptr ge b = Some (External ef) ->
  ef_sig ef = sg ->
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  transl_expr_prop le (Eexternal id sg al) v.
Proof.
  admit. (*We do not yet support use of builtins for 64-bit operations.*)
Qed.
(*
Proof.
  intros; red; intros. inv TE.
  exploit H3; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
  exploit external_call_mem_extends; eauto.
  intros [v' [tm2 [A [B [C [D E]]]]]].
  exploit function_ptr_translated; eauto. simpl. intros [tf [P Q]]. inv Q.
  exists (rs1#rd <- v'); exists tm2.
(* Exec *)
  split. eapply star_trans. eexact EX1.
  eapply star_left. eapply exec_Icall; eauto.
  simpl. rewrite symbols_preserved. rewrite H. eauto. auto.
  eapply star_left. eapply exec_function_external.
  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.
  apply star_one. apply exec_return.
  reflexivity. reflexivity. reflexivity.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.
*)

Lemma transl_exprlist_Enil_correct:
  forall (le : letenv),
  transl_exprlist_prop le Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs; exists tm.
  split. apply corestep_star_zero.
  split. assumption.
  split. constructor.
  auto.
Qed.

Lemma transl_exprlist_Econs_correct:
  forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
         (vl : list val),
  eval_expr ge sp e m le a1 v1 ->
  transl_expr_prop le a1 v1 ->
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  transl_exprlist_prop le (Econs a1 al) (v1 :: vl).
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X1]]]]]]]; subst.
  exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 [EXT2 X2]]]]]]]; subst.
  exists rs2; exists tm2.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. constructor. rewrite OTHER2. auto.
  simpl; tauto.
  auto.
(* Other regs *)
  split. intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto.
  apply OTHER1; auto.
(* Mem *)
  auto.
Qed.

Lemma transl_condexpr_CEcond_correct:
  forall le cond al vl vb,
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  eval_condition cond vl m = Some vb ->
  transl_condexpr_prop le (CEcond cond al) vb.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst.
  exists rs1; exists tm1.
(* Exec *)
  split. eapply corestep_star_plus_trans. eexact EX1.
      eapply corestep_plus_one. eapply rtl_corestep_exec_Icond. eauto.
      (*eapply eval_condition_lessdef; eauto.*)
    eapply eval_condition_inject; eauto. auto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. assumption.
(* Mem *)
  auto.
Qed.

Lemma transl_condexpr_CEcondition_correct:
  forall le a b c va v,
  eval_condexpr ge sp e m le a va ->
  transl_condexpr_prop le a va ->
  eval_condexpr ge sp e m le (if va then b else c) v ->
  transl_condexpr_prop le (if va then b else c) v ->
  transl_condexpr_prop le (CEcondition a b c) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 [EXT1 X]]]]]]; subst.
  assert (tr_condition (fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
    destruct va; auto.
  exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [OTHER2 [EXT2 X]]]]]]; subst.
  exists rs2; exists tm2.
(* Exec *)
  split. eapply corestep_plus_trans. eexact EX1. eexact EX2.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
(* Mem *)
  auto.
Qed.

Lemma transl_condexpr_CElet_correct:
  forall le a b v1 v2,
  eval_expr ge sp e m le a v1 ->
  transl_expr_prop le a v1 ->
  eval_condexpr ge sp e m (v1 :: le) b v2 ->
  transl_condexpr_prop (v1 :: le) b v2 ->
  transl_condexpr_prop le (CElet a b) v2.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst.
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H2; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [EX2 [ME3 [OTHER2 [EXT2 X]]]]]]; subst.
  exists rs2; exists tm2.
(* Exec *)
  split. eapply corestep_star_plus_trans. eexact EX1. eexact EX2.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
(* Mem *)
  auto.
Qed.

Theorem transl_expr_correct:
  forall le a v,
  eval_expr ge sp e m le a v ->
  transl_expr_prop le a v.
Proof
  (eval_expr_ind3 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_condexpr_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_expr_Ebuiltin_correct
     transl_expr_Eexternal_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_condexpr_CEcond_correct
     transl_condexpr_CEcondition_correct
     transl_condexpr_CElet_correct).

Theorem transl_exprlist_correct:
  forall le a v,
  eval_exprlist ge sp e m le a v ->
  transl_exprlist_prop le a v.
Proof
  (eval_exprlist_ind3 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_condexpr_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_expr_Ebuiltin_correct
     transl_expr_Eexternal_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_condexpr_CEcond_correct
     transl_condexpr_CEcondition_correct
     transl_condexpr_CElet_correct).

Theorem transl_condexpr_correct:
  forall le a v,
  eval_condexpr ge sp e m le a v ->
  transl_condexpr_prop le a v.
Proof
  (eval_condexpr_ind3 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_condexpr_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_expr_Ebuiltin_correct
     transl_expr_Eexternal_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_condexpr_CEcond_correct
     transl_condexpr_CEcondition_correct
     transl_condexpr_CElet_correct).

End CORRECTNESS_EXPR.

(*LENB: The same for effect-steps*)
Section CORRECTNESS_EXPR_EFF.

Lemma Efftr_move_correct:
  forall r1 ns r2 nd cs f sp rs m,
  tr_move f.(fn_code) ns r1 nd r2 ->
  exists rs',
  effstep_star rtl_eff_sem tge EmptyEffect
     (RTL_State cs f sp ns rs) m
     (RTL_State cs f sp nd rs') m /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H.
  exists rs; split. eapply effstep_star_zero. auto.
  exists (rs#r2 <- (rs#r1)); split.
  apply effstep_star_one. eapply rtl_effstep_exec_Iop. eauto. auto.
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

Lemma Efftransl_switch_correct:
  forall j cs sp e m f map r nexits t ns,
  tr_switch f.(fn_code) map r nexits t ns ->
  forall rs i act,
  rs#r = Vint i ->
  map_wf map ->
  match_env j map e nil rs ->
  comptree_match i t = Some act ->
  exists nd, exists rs',
  effstep_star rtl_eff_sem  tge EmptyEffect
        (RTL_State cs f sp ns rs) m (RTL_State cs f sp nd rs') m /\
  nth_error nexits act = Some nd /\
  match_env j map e nil rs'.
Proof.
  Opaque Int.sub.
  induction 1; simpl; intros.
(* action *)
  inv H3. exists n; exists rs; intuition.
  apply effstep_star_zero.
(* ifeq *)
  caseEq (Int.eq i key); intro EQ; rewrite EQ in H5.
  inv H5. exists nfound; exists rs; intuition.
  apply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := true); eauto.
  simpl. rewrite H2. simpl. congruence.
  exploit IHtr_switch; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply effstep_star_trans.
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := false); eauto.
      simpl. rewrite H2. simpl. congruence. eexact EX.
(* iflt *)
  caseEq (Int.ltu i key); intro EQ; rewrite EQ in H5.
  exploit IHtr_switch1; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply effstep_star_trans.
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := true); eauto.
    simpl. rewrite H2. simpl. congruence. eexact EX.
  exploit IHtr_switch2; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply effstep_star_trans.
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := false); eauto.
    simpl. rewrite H2. simpl. congruence. eexact EX.
(* jumptable *)
  set (rs1 := rs#rt <- (Vint(Int.sub i ofs))).
  assert (ME1: match_env j map e nil rs1).
    unfold rs1. eauto with rtlg.
  assert (EX1: RTL_effstep tge EmptyEffect (RTL_State cs f sp n rs) m (RTL_State cs f sp n1 rs1) m).
    eapply rtl_effstep_exec_Iop; eauto.
    predSpec Int.eq Int.eq_spec ofs Int.zero; simpl.
    rewrite H10. rewrite Int.sub_zero_l. congruence.
    rewrite H6. simpl. rewrite <- Int.sub_add_opp. auto.
  caseEq (Int.ltu (Int.sub i ofs) sz); intro EQ; rewrite EQ in H9.
  exploit H5; eauto. intros [nd [A B]].
  exists nd; exists rs1; intuition.
  eapply effstep_star_trans.
    eapply effstep_star_one. eexact EX1.
  eapply effstep_star_trans.
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := true); eauto.
    simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
  apply effstep_star_one. eapply rtl_effstep_exec_Ijumptable; eauto. unfold rs1. apply Regmap.gss.
  exploit (IHtr_switch rs1); eauto. unfold rs1. rewrite Regmap.gso; auto.
  intros [nd [rs' [EX [NTH ME]]]].
  exists nd; exists rs'; intuition.
  eapply effstep_star_trans.
    eapply effstep_star_one. eexact EX1.
  eapply effstep_star_trans.
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := false); eauto.
    simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
  eexact EX.
Qed.

Variable sp: val.
Variable e: env.
Variable m: mem.


Definition Efftransl_expr_prop
     (le: letenv) (a: expr) (v: val) : Prop :=
  forall j tm cs f map pr ns nd rd rs dst
 (*NEW:*)(PG: meminj_preserves_globals ge j)
         sp' (SP: sp_preserved j sp sp')

    (MWF: map_wf map)
    (TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
    (ME: match_env j map e le rs)
    (EXT: Mem.inject j m tm),
  exists rs', exists tm',
     effstep_star rtl_eff_sem tge EmptyEffect
        (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env j map (set_optvar dst v e) le rs'
  /\ val_inject j v rs'#rd
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject j m tm' /\ tm=tm'.

Definition Efftransl_exprlist_prop
     (le: letenv) (al: exprlist) (vl: list val) : Prop :=
  forall j tm cs f map pr ns nd rl rs
 (*NEW:*)(PG: meminj_preserves_globals ge j)
         sp' (SP: sp_preserved j sp sp')

    (MWF: map_wf map)
    (TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
    (ME: match_env j map e le rs)
    (EXT: Mem.inject j m tm),
  exists rs', exists tm',
     effstep_star rtl_eff_sem tge EmptyEffect
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env j map e le rs'
  /\ val_list_inject j vl rs'##rl
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject j m tm' /\ tm=tm'.

Definition Efftransl_condexpr_prop
     (le: letenv) (a: condexpr) (v: bool) : Prop :=
  forall j tm cs f map pr ns ntrue nfalse rs
 (*NEW:*)(PG: meminj_preserves_globals ge j)
         sp' (SP: sp_preserved j sp sp')

    (MWF: map_wf map)
    (TE: tr_condition f.(fn_code) map pr a ns ntrue nfalse)
    (ME: match_env j map e le rs)
    (EXT: Mem.inject j m tm),
  exists rs', exists tm',
     effstep_plus rtl_eff_sem tge EmptyEffect
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' (if v then ntrue else nfalse) rs') tm'
  /\ match_env j map e le rs'
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject j m tm' /\ tm=tm'.

(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma Efftransl_expr_Evar_correct:
  forall (le : letenv) (id : positive) (v: val),
  e ! id = Some v ->
  Efftransl_expr_prop le (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit Efftr_move_correct; eauto. intros [rs' [A [B C]]].
  exists rs'; exists tm; split. eauto.
  destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto.
  split. eapply match_env_invariant; eauto.
  split. congruence.
  split; auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto.
  split. congruence.
  split. intros. apply C. intuition congruence.
  auto.
Qed.

Lemma Efftransl_expr_Eop_correct:
  forall (le : letenv) (op : operation) (args : exprlist)
         (vargs : list val) (v : val),
  eval_exprlist ge sp e m le args vargs ->
  Efftransl_exprlist_prop le args vargs ->
  eval_operation ge sp op vargs m = Some v ->
  Efftransl_expr_prop le (Eop op args) v.
Proof.
  intros; red; intros. inv TE.
(* normal case *)
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 [EXT1 X]]]]]]]; subst tm.
  (*Was: edestruct eval_operation_lessdef...*)

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_operation_inject as [v' []]; eauto.
  rewrite eval_shift_stack_operation in H2. simpl in H2. rewrite Int.add_zero in H2.

  exists (rs1#rd <- v'); exists tm1.
(* Exec *)
  split. eapply effstep_star_trans. eexact EX1.
  eapply effstep_star_one. eapply rtl_effstep_exec_Iop; eauto.
  rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ ge tge). eauto.
  exact symbols_preserved.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) (vargs : list val) (vaddr v : val),
  eval_exprlist ge sp e m le args vargs ->
  Efftransl_exprlist_prop le args vargs ->
  Op.eval_addressing ge sp addr vargs = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  Efftransl_expr_prop le (Eload chunk addr args) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst tm.
  (*Was: edestruct eval_addressing_lessdef as [vaddr' []]; eauto.*)

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_addressing_inject as [vaddr' [? ?]]; eauto.
  rewrite shift_stack_addressing_zero in H3; simpl in H3.
  edestruct Mem.loadv_inject as [v' []]; eauto.
  exists (rs1#rd <- v'); exists tm1.
(* Exec *)
  split. eapply effstep_star_trans. eexact EX1.
    eapply effstep_star_one.
      eapply rtl_effstep_exec_Iload; try eassumption.
    rewrite (eval_addressing_preserved ge). assumption.
       exact symbols_preserved.
(* Match-env *)
  split. eauto with rtlg.
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Econdition_correct:
  forall (le : letenv) (a: condexpr) (ifso ifnot : expr)
         (va : bool) (v : val),
  eval_condexpr ge sp e m le a va ->
  Efftransl_condexpr_prop le a va ->
  eval_expr ge sp e m le (if va then ifso else ifnot) v ->
  Efftransl_expr_prop le (if va then ifso else ifnot) v ->
  Efftransl_expr_prop le (Econdition a ifso ifnot) v.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 [EXT1 X]]]]]]; subst tm.
  assert (tr_expr f.(fn_code) map pr (if va then ifso else ifnot) (if va then ntrue else nfalse) nd rd dst).
    destruct va; auto.
  exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply effstep_star_trans.
           apply effstep_plus_star. eexact EX1. eexact EX2.
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r); auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Elet_correct:
  forall (le : letenv) (a1 a2 : expr) (v1 v2 : val),
  eval_expr ge sp e m le a1 v1 ->
  Efftransl_expr_prop le a1 v1 ->
  eval_expr ge sp e m (v1 :: le) a2 v2 ->
  Efftransl_expr_prop (v1 :: le) a2 v2 ->
  Efftransl_expr_prop le (Elet a1 a2) v2.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst tm.
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H2; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [EX2 [ME3 [RES2 [OTHER2 EXT2]]]]]].
  exists rs2; exists tm2.
(* Exec *)
  split. eapply effstep_star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r0); auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Eletvar_correct:
  forall (le : list val) (n : nat) (v : val),
  nth_error le n = Some v ->
  Efftransl_expr_prop le (Eletvar n) v.
Proof.
  intros; red; intros; inv TE.
  exploit Efftr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1; exists tm.
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split.
  destruct H2 as [[A B] | [A B]].
  subst r dst; simpl.
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto.
(* Other regs *)
  split. intros.
  destruct H2 as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
(* Mem *)
  auto.
Qed.

(*LENB: TODO: builtin: Lemma doesn;'t quite hold -nned to extend j -> j'.
  But maye we won't need this case, if
  builtin-expressions can be eliminated from CminorSel.expressions*)
Lemma Efftransl_expr_Ebuiltin_correct:
  forall le ef al vl v,
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  Efftransl_expr_prop le (Ebuiltin ef al) v.
Proof.
  admit. (*We do not yet support use of builtins for 64-bit operations.*)
Qed.
(*Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
  (*WAS: exploit external_call_mem_extends; eauto.
        intros [v' [tm2 [A [B [C [D E]]]]]].*)
  exploit external_call_mem_inject; eauto.
        intros [j' [v' [tm2 [A [B [C [D [E [F G]]]]]]]]].
  exists (rs1#rd <- v'); exists tm2.
(* Exec *)
  split. eapply effstep_star_trans. eexact EX1.
         apply effstep_star_one. eapply rtl_effstep_exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.
(* Match-env *)
  split. eapply match_env_update_dest; try eassumption.
         eapply val_inject_incr. eassumption. split; intros.  eexists. eauto with rtlg.
(* Result reg *)
  split. intros. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.
*)

(*LENB: Lemma should not be needed any more since external calls are
 handled by effsemantics interface now. We can probably eliminate
  external expressions from CminorSel.v, but that's a language definieiotn modification*)

Lemma Efftransl_expr_Eexternal_correct:
  forall le id sg al b ef vl v,
  Genv.find_symbol ge id = Some b ->
  Genv.find_funct_ptr ge b = Some (External ef) ->
  ef_sig ef = sg ->
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  Efftransl_expr_prop le (Eexternal id sg al) v.
Proof.
  admit. (*We do not yet support use of builtins for 64-bit operations.*)
Qed.
(*Proof.
  intros; red; intros. inv TE.
  exploit H3; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
  exploit external_call_mem_extends; eauto.
  intros [v' [tm2 [A [B [C [D E]]]]]].
  exploit function_ptr_translated; eauto. simpl. intros [tf [P Q]]. inv Q.
  exists (rs1#rd <- v'); exists tm2.
(* Exec *)
  split. eapply star_trans. eexact EX1.
  eapply star_left. eapply exec_Icall; eauto.
  simpl. rewrite symbols_preserved. rewrite H. eauto. auto.
  eapply star_left. eapply exec_function_external.
  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.
  apply star_one. apply exec_return.
  reflexivity. reflexivity. reflexivity.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.
*)

Lemma Efftransl_exprlist_Enil_correct:
  forall (le : letenv),
  Efftransl_exprlist_prop le Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs; exists tm.
  split. apply effstep_star_zero.
  split. assumption.
  split. constructor.
  auto.
Qed.

Lemma Efftransl_exprlist_Econs_correct:
  forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
         (vl : list val),
  eval_expr ge sp e m le a1 v1 ->
  Efftransl_expr_prop le a1 v1 ->
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  Efftransl_exprlist_prop le (Econs a1 al) (v1 :: vl).
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X1]]]]]]]; subst.
  exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 [EXT2 X2]]]]]]]; subst.
  exists rs2; exists tm2.
(* Exec *)
  split. eapply effstep_star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. constructor. rewrite OTHER2. auto.
  simpl; tauto.
  auto.
(* Other regs *)
  split. intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto.
  apply OTHER1; auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_condexpr_CEcond_correct:
  forall le cond al vl vb,
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  eval_condition cond vl m = Some vb ->
  Efftransl_condexpr_prop le (CEcond cond al) vb.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst.
  exists rs1; exists tm1.
(* Exec *)
  split. eapply effstep_star_plus_trans. eexact EX1.
      eapply effstep_plus_one. eapply rtl_effstep_exec_Icond. eauto.
      (*eapply eval_condition_lessdef; eauto.*)
    eapply eval_condition_inject; eauto. auto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. assumption.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_condexpr_CEcondition_correct:
  forall le a b c va v,
  eval_condexpr ge sp e m le a va ->
  Efftransl_condexpr_prop le a va ->
  eval_condexpr ge sp e m le (if va then b else c) v ->
  Efftransl_condexpr_prop le (if va then b else c) v ->
  Efftransl_condexpr_prop le (CEcondition a b c) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 [EXT1 X]]]]]]; subst.
  assert (tr_condition (fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
    destruct va; auto.
  exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [OTHER2 [EXT2 X]]]]]]; subst.
  exists rs2; exists tm2.
(* Exec *)
  split. eapply effstep_plus_trans. eexact EX1. eexact EX2.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_condexpr_CElet_correct:
  forall le a b v1 v2,
  eval_expr ge sp e m le a v1 ->
  Efftransl_expr_prop le a v1 ->
  eval_condexpr ge sp e m (v1 :: le) b v2 ->
  Efftransl_condexpr_prop (v1 :: le) b v2 ->
  Efftransl_condexpr_prop le (CElet a b) v2.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 [EXT1 X]]]]]]]; subst.
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  exploit H2; eauto. eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [EX2 [ME3 [OTHER2 [EXT2 X]]]]]]; subst.
  exists rs2; exists tm2.
(* Exec *)
  split. eapply effstep_star_plus_trans. eexact EX1. eexact EX2.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Other regs *)
  split. intros. rewrite OTHER2; auto.
(* Mem *)
  auto.
Qed.

Theorem Efftransl_expr_correct:
  forall le a v,
  eval_expr ge sp e m le a v ->
  Efftransl_expr_prop le a v.
Proof
  (eval_expr_ind3 ge sp e m
     Efftransl_expr_prop
     Efftransl_exprlist_prop
     Efftransl_condexpr_prop
     Efftransl_expr_Evar_correct
     Efftransl_expr_Eop_correct
     Efftransl_expr_Eload_correct
     Efftransl_expr_Econdition_correct
     Efftransl_expr_Elet_correct
     Efftransl_expr_Eletvar_correct
     Efftransl_expr_Ebuiltin_correct
     Efftransl_expr_Eexternal_correct
     Efftransl_exprlist_Enil_correct
     Efftransl_exprlist_Econs_correct
     Efftransl_condexpr_CEcond_correct
     Efftransl_condexpr_CEcondition_correct
     Efftransl_condexpr_CElet_correct).

Theorem Efftransl_exprlist_correct:
  forall le a v,
  eval_exprlist ge sp e m le a v ->
  Efftransl_exprlist_prop le a v.
Proof
  (eval_exprlist_ind3 ge sp e m
     Efftransl_expr_prop
     Efftransl_exprlist_prop
     Efftransl_condexpr_prop
     Efftransl_expr_Evar_correct
     Efftransl_expr_Eop_correct
     Efftransl_expr_Eload_correct
     Efftransl_expr_Econdition_correct
     Efftransl_expr_Elet_correct
     Efftransl_expr_Eletvar_correct
     Efftransl_expr_Ebuiltin_correct
     Efftransl_expr_Eexternal_correct
     Efftransl_exprlist_Enil_correct
     Efftransl_exprlist_Econs_correct
     Efftransl_condexpr_CEcond_correct
     Efftransl_condexpr_CEcondition_correct
     Efftransl_condexpr_CElet_correct).

Theorem Efftransl_condexpr_correct:
  forall le a v,
  eval_condexpr ge sp e m le a v ->
  Efftransl_condexpr_prop le a v.
Proof
  (eval_condexpr_ind3 ge sp e m
     Efftransl_expr_prop
     Efftransl_exprlist_prop
     Efftransl_condexpr_prop
     Efftransl_expr_Evar_correct
     Efftransl_expr_Eop_correct
     Efftransl_expr_Eload_correct
     Efftransl_expr_Econdition_correct
     Efftransl_expr_Elet_correct
     Efftransl_expr_Eletvar_correct
     Efftransl_expr_Ebuiltin_correct
     Efftransl_expr_Eexternal_correct
     Efftransl_exprlist_Enil_correct
     Efftransl_exprlist_Econs_correct
     Efftransl_condexpr_CEcond_correct
     Efftransl_condexpr_CEcondition_correct
     Efftransl_condexpr_CElet_correct).

End CORRECTNESS_EXPR_EFF.

(** ** Measure over CminorSel states *)

Open Local Scope nat_scope.

Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sskip => 0
  | Sseq s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sifthenelse c s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sloop s1 => (size_stmt s1 + 1)
  | Sblock s1 => (size_stmt s1 + 1)
  | Sexit n => 0
  | Slabel lbl s1 => (size_stmt s1 + 1)
  | _ => 1
  end.

Fixpoint size_cont (k: cont) : nat :=
  match k with
  | Kseq s k1 => (size_stmt s + size_cont k1 + 1)
  | Kblock k1 => (size_cont k1 + 1)
  | _ => 0%nat
  end.

Definition measure_state (S: CMinSel_core) :=
  match S with
  | CMinSel_State _ s k _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _                           => (0, 0)
  end.

Definition lt_state (S1 S2: CMinSel_core) :=
  lex_ord lt lt (measure_state S1) (measure_state S2).

Lemma lt_state_intro:
  forall f1 s1 k1 sp1 e1 f2 s2 k2 sp2 e2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (CMinSel_State f1 s1 k1 sp1 e1)
           (CMinSel_State f2 s2 k2 sp2 e2).
Proof.
  intros. unfold lt_state. simpl. destruct H as [A | [A B]].
  left. auto.
  rewrite A. right. auto.
Qed.

Ltac Lt_state :=
  apply lt_state_intro; simpl; try omega.

Require Import Wellfounded.

Lemma lt_state_wf:
  well_founded lt_state.
Proof.
  unfold lt_state. apply wf_inverse_image with (f := measure_state).
  apply wf_lex_ord. apply lt_wf. apply lt_wf.
Qed.

(** ** Semantic preservation for the translation of statements *)

(** The simulation diagram for the translation of statements
  and functions is a "star" diagram of the form:
<<
           I                         I
     S1 ------- R1             S1 ------- R1
     |          |              |          |
   t |        + | t      or  t |        * | t    and |S2| < |S1|
     v          v              v          |
     S2 ------- R2             S2 ------- R2
           I                         I
>>
  where [I] is the [match_states] predicate defined below.  It includes:
- Agreement between the Cminor statement under consideration and
  the current program point in the RTL control-flow graph,
  as captured by the [tr_stmt] predicate.
- Agreement between the Cminor continuation and the RTL control-flow
  graph and call stack, as captured by the [tr_cont] predicate below.
- Agreement between Cminor environments and RTL register environments,
  as captured by [match_envs].

*)

Inductive tr_fun (tf: function) (map: mapping) (f: CminorSel.function)
                     (ngoto: labelmap) (nret: node) (rret: option reg) : Prop :=
  | tr_fun_intro: forall nentry r,
      rret = ret_reg f.(CminorSel.fn_sig) r ->
      tr_stmt tf.(fn_code) map f.(fn_body) nentry nret nil ngoto nret rret ->
      tf.(fn_stacksize) = f.(fn_stackspace) ->
      tr_fun tf map f ngoto nret rret.

(*LENB: new: meminj parameter j*)
Inductive tr_cont (j:meminj): RTL.code -> mapping ->
                   CminorSel.cont -> node -> list node -> labelmap -> node -> option reg ->
                   list RTL.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont j c map k n nexits ngoto nret rret cs ->
      tr_cont j c map (Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
      tr_cont j c map k nd nexits ngoto nret rret cs ->
      tr_cont j c map (Kblock k) nd (nd :: nexits) ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks j Kstop cs ->
      tr_cont j c map Kstop nret nil ngoto nret rret cs
  | tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks j (Kcall optid f sp e k) cs ->
      tr_cont j c map (Kcall optid f sp e k) nret nil ngoto nret rret cs

with match_stacks (j:meminj) : CminorSel.cont -> list RTL.stackframe -> Prop :=
  | match_stacks_stop:
      match_stacks j Kstop nil
  | match_stacks_call: forall optid f sp e k r tf n rs cs map nexits ngoto nret rret sp',
      map_wf map ->
      tr_fun tf map f ngoto nret rret ->
      match_env j map e nil rs ->
      reg_map_ok map r optid ->
      tr_cont j tf.(fn_code) map k n nexits ngoto nret rret cs ->
      (*NEW:*) sp_preserved j sp sp' ->
      match_stacks j (Kcall optid f sp e k) (Stackframe r tf sp' n rs :: cs).

(*Derivation of induction scheme as explained her:
http://coq.inria.fr/cocorico/Mutual%20Induction*)
Scheme tr_cont_ind_2 := Induction for tr_cont Sort Prop
  with match_stacks_ind_2 := Induction for match_stacks Sort Prop.
Combined Scheme tr_cont_match_stacks_mutual_ind
  from tr_cont_ind_2, match_stacks_ind_2.

Lemma tr_cont_match_stacks_inject_incr:
      forall j j' (INC: inject_incr j j'),
      (forall c map k ncont nexits ngoto nret rret cs,
         tr_cont j c map k ncont nexits ngoto nret rret cs ->
         tr_cont j' c map k ncont nexits ngoto nret rret cs) /\
       (forall k cs, match_stacks j k cs -> match_stacks j' k cs).
Proof. intros. apply tr_cont_match_stacks_mutual_ind; intros.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; try eassumption.
     eapply match_env_inject_incr; eassumption.
     destruct s as [b [b' [B [B' SP]]]].
       apply INC in SP. exists b, b'; eauto.
Qed.
Lemma tr_cont_inject_incr:
      forall j c map k ncont nexits ngoto nret rret cs
        (TR: tr_cont j c map k ncont nexits ngoto nret rret cs)
        j' (INC: inject_incr j j'),
      tr_cont j' c map k ncont nexits ngoto nret rret cs.
Proof. intros.
       eapply tr_cont_match_stacks_inject_incr; try eassumption.
Qed.
Lemma match_stacks_inject_incr:
      forall j  k cs (MS:match_stacks j k cs)
             j' (INC: inject_incr j j'),
      match_stacks j' k cs.
Proof. intros.
       eapply tr_cont_match_stacks_inject_incr; try eassumption.
Qed.

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


Lemma match_stacks_call_cont:
  forall j c map k ncont nexits ngoto nret rret cs,
  tr_cont j c map k ncont nexits ngoto nret rret cs ->
  match_stacks j (call_cont k) cs /\ c!nret = Some(Ireturn rret).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma tr_cont_call_cont:
  forall j c map k ncont nexits ngoto nret rret cs,
  tr_cont j c map k ncont nexits ngoto nret rret cs ->
  tr_cont j c map (call_cont k) nret nil ngoto nret rret cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma tr_find_label:
  forall j c map lbl n (ngoto: labelmap) nret rret s' k' cs,
  ngoto!lbl = Some n ->
  forall s k ns1 nd1 nexits1,
  find_label lbl s k = Some (s', k') ->
  tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
  tr_cont j c map k nd1 nexits1 ngoto nret rret cs ->
  exists ns2, exists nd2, exists nexits2,
     c!n = Some(Inop ns2)
  /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
  /\ tr_cont j c map k' nd2 nexits2 ngoto nret rret cs.
Proof.
  induction s; intros until nexits1; simpl; try congruence.
  (* seq *)
  caseEq (find_label lbl s1 (Kseq s2 k)); intros.
  inv H1. inv H2. eapply IHs1; eauto. econstructor; eauto.
  inv H2. eapply IHs2; eauto.
  (* ifthenelse *)
  caseEq (find_label lbl s1 k); intros.
  inv H1. inv H2. eapply IHs1; eauto.
  inv H2. eapply IHs2; eauto.
  (* loop *)
  intros. inversion H1; subst.
  eapply IHs; eauto. econstructor; eauto. econstructor; eauto.
  (* block *)
  intros. inv H1.
  eapply IHs; eauto. econstructor; eauto.
  (* label *)
  destruct (ident_eq lbl l); intros.
  inv H0. inv H1.
  assert (n0 = n). change positive with node in H4. congruence. subst n0.
  exists ns1; exists nd1; exists nexits1; auto.
  inv H1. eapply IHs; eauto.
Qed.

Definition MATCH (d:CMinSel_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma MATCH_wd: forall d mu c1 m1 c2 m2
  (MC: MATCH d mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall d mu c1 m1 c2 m2
  (MC: MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma MATCH_restrict: forall d mu c1 m1 c2 m2 X
  (MC: MATCH d mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true)
  (RX: REACH_closed m1 X),
  MATCH d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
  rewrite restrict_sm_all.
  rewrite restrict_nest; intuition.
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

Lemma MATCH_valid: forall d mu c1 m1 c2 m2
  (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
Proof. intros. eapply MC. Qed.

Lemma MATCH_PG: forall d mu c1 m1 c2 m2
  (MC: MATCH d mu c1 m1 c2 m2),
  meminj_preserves_globals ge (extern_of mu) /\
  (forall b : block, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.

Lemma MATCH_initial: forall v1 v2 sig entrypoints
      (EP: In (v1, v2, sig) entrypoints)
      (entry_points_ok : forall (v1 v2 : val) (sig : signature),
                  In (v1, v2, sig) entrypoints ->
                  exists b f1 f2,
                    v1 = Vptr b Int.zero /\
                    v2 = Vptr b Int.zero /\
                    Genv.find_funct_ptr ge b = Some f1 /\
                    Genv.find_funct_ptr tge b = Some f2)
      vals1 c1 m1 j vals2 m2 (DomS DomT : block -> bool)
      (Ini: initial_core cminsel_eff_sem ge v1 vals1 = Some c1)
      (Inj: Mem.inject j m1 m2)
      (VInj: Forall2 (val_inject j) vals1 vals2)
      (PG:meminj_preserves_globals ge j)
      (R : list_norepet (map fst (prog_defs prog)))
      (J: forall b1 b2 delta, j b1 = Some (b2, delta) ->
            (DomS b1 = true /\ DomT b2 = true))
      (RCH: forall b, REACH m2
          (fun b' : block => isGlobalBlock tge b' || getBlocks vals2 b') b = true ->
          DomT b = true)
      (InitMem : exists m0 : mem, Genv.init_mem prog = Some m0
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m1)
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))
      (GDE: genvs_domain_eq ge tge)
      (HDomS: forall b : block, DomS b = true -> Mem.valid_block m1 b)
      (HDomT: forall b : block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core rtl_eff_sem tge v2 vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1 (fun b : block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2 (fun b : block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof. intros.
  inversion Ini.
  unfold CMinSel_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0.
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  exists (RTL_Callstate nil tf vals2).
  split.
    destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. rewrite C in Heqzz. inv Heqzz.
    unfold tge in FP. rewrite D in FP. inv FP.
    unfold cminsel_eff_sem, cminsel_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    solve[rewrite D; auto].

    intros CONTRA.
    solve[elimtype False; auto].
(*  assert (exists targs tres, type_of_fundef f = Tfunction targs tres).
         destruct f; simpl. eexists; eexists. reflexivity.
         eexists; eexists. reflexivity.
  destruct H as [targs [tres Tfun]].*)
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    eapply match_callstate; try eassumption.
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

Lemma MATCH_afterExternal: forall
      (GDE : genvs_domain_eq ge tge)
      mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH st1 mu st1 m1 st2 m2)
      (AtExtSrc : at_external cminsel_eff_sem st1 = Some (e, ef_sig, vals1))
      (AtExtTgt : at_external rtl_eff_sem st2 = Some (e', ef_sig', vals2))
      (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
      (pubSrc' : block -> bool)
      (pubSrcHyp : pubSrc' =
                 (fun b : block =>
                 locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
      (pubTgt' : block -> bool)
      (pubTgtHyp: pubTgt' =
                 (fun b : block =>
                 locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
       nu' ret1 m1' ret2 m2'
       (INC: extern_incr nu nu')
       (SEP: sm_inject_separated nu nu' m1 m2)
       (WDnu': SM_wd nu')
       (SMvalNu': sm_valid nu' m1' m2')
       (MemInjNu': Mem.inject (as_inj nu') m1' m2')
       (RValInjNu': val_inject (as_inj nu') ret1 ret2)
       (FwdSrc: mem_forward m1 m1')
       (FwdTgt: mem_forward m2 m2')
       (frgnSrc' : block -> bool)
       (frgnSrcHyp: frgnSrc' =
             (fun b : block => DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
       (frgnTgt' : block -> bool)
       (frgnTgtHyp: frgnTgt' =
            (fun b : block => DomTgt nu' b &&
             (negb (locBlocksTgt nu' b) && REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
       mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
       (UnchPrivSrc: Mem.unchanged_on
               (fun b z => locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
       (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
  exists st1' st2',
  after_external cminsel_eff_sem (Some ret1) st1 =Some st1' /\
  after_external rtl_eff_sem (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros.
simpl.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H0.
 destruct tf; inv AtExtTgt.
 eexists. eexists.
    split. reflexivity.
    split. reflexivity.
 simpl in *.
 inv TF.
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
assert (PHnu': meminj_preserves_globals (Genv.globalenv prog) (as_inj nu')).
    subst. clear - INC SEP PG Glob WDmu WDnu'.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    apply meminj_preserves_genv2blocks.
    split; intros.
      specialize (PGa _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char1 in H.
          rewrite H. trivial.
      destruct (frgnSrc _ WDmu _ (Glob _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      apply foreign_in_extern; eassumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char2 in H.
          rewrite H. intuition.
      destruct (frgnSrc _ WDmu _ (Glob _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
      apply foreign_in_extern; eassumption.
    eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
      remember (as_inj mu b1) as d.
      destruct d; apply eq_sym in Heqd.
        destruct p.
        apply extern_incr_as_inj in INC; trivial.
        rewrite replace_locals_as_inj in INC.
        rewrite (INC _ _ _ Heqd) in H0. trivial.
      destruct SEP as [SEPa _].
        rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in SEPa.
        destruct (SEPa _ _ _ Heqd H0).
        destruct (as_inj_DomRng _ _ _ _ PGb WDmu).
        congruence.
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
    destruct IHL. congruence.
    apply andb_true_iff in H. simpl in H.
    destruct H as [DomNu' Rb'].
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
assert (GFnu': forall b, isGlobalBlock (Genv.globalenv prog) b = true ->
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
     intros. specialize (Glob _ H).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in Glob.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ Glob).
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ Glob). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ Glob). intuition.
split.
  econstructor; try eassumption.
    eapply match_stacks_inject_incr; try eassumption.
    unfold vis in *.
      rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
      rewrite (*restrict_sm_all, *)replace_externs_as_inj.
      clear RRC RR1 RC' PHnu' INCvisNu' UnchLOOR UnchPrivSrc.
      destruct INC. rewrite replace_locals_extern in H.
        rewrite replace_locals_frgnBlocksTgt, replace_locals_frgnBlocksSrc,
                replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc,
                replace_locals_locBlocksTgt, replace_locals_locBlocksSrc,
                replace_locals_extBlocksTgt, replace_locals_extBlocksSrc,
                replace_locals_local in H0.
        destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
        red; intros. destruct (restrictD_Some _ _ _ _ _ H9); clear H9.
          apply restrictI_Some.
            apply joinI.
            destruct (joinD_Some _ _ _ _ _ H10).
              apply H in H9. left; trivial.
            destruct H9. right. rewrite H0 in H12.
              split; trivial.
              destruct (disjoint_extern_local _ WDnu' b); trivial. congruence.
          (*rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc. *)
          rewrite H3, H7 in H11.
            remember (locBlocksSrc nu' b) as d.
            destruct d; trivial; simpl in *.
            apply andb_true_iff.
            split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H11). intuition.
               apply REACH_nil. unfold exportedSrc.
                 apply frgnSrc_shared in H11; trivial. rewrite H11; intuition.
      unfold vis. rewrite replace_externs_as_inj.
       rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
       eapply restrict_val_inject; try eassumption.
       intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H. trivial.
unfold vis in *.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj in *.
  eapply inject_mapped; try eassumption.
  eapply restrict_mapped_closed; try eassumption.

destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu'
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
unfold vis in *.
  rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
  replace_externs_as_inj in *.
intuition.
(*as in selectionproofEFF*)
  red; intros. destruct (GFP _ _ H1). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed.

Lemma MATCH_corestep: forall
       st1 m1 st1' m1'
       (CS: corestep cminsel_eff_sem ge st1 m1 st1' m1')
       st2 mu m2 (MTCH: MATCH st1 mu st1 m1 st2 m2),
exists st2' m2' mu',
  (corestep_plus rtl_eff_sem tge st2 m2 st2' m2' \/
   (corestep_star rtl_eff_sem tge st2 m2 st2' m2' /\ lt_state st1' st1))
  /\ intern_incr mu mu'
  /\ sm_inject_separated mu mu' m1 m2
  /\ sm_locally_allocated mu mu' m1 m2 m1' m2'
  /\ MATCH st1' mu' st1' m1' st2' m2'
  /\ SM_wd mu' /\ sm_valid mu' m1' m2'.
Proof. intros.
   destruct CS; intros; destruct MTCH as [MSTATE PRE]; inv MSTATE.

  (* skip seq *)
  inv TS. inv TK.
  eexists; exists m2, mu; split.
     right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.

  (* skip block *)
  inv TS. inv TK.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor.
      intuition.

  (* skip return *)
  inv TS.
  assert ((fn_code tf)!ncont = Some(Ireturn rret)
          /\ match_stacks (restrict (as_inj mu) (vis mu)) k cs).
    inv TK; simpl in H; try contradiction; auto.
  destruct H1.
  assert (fn_stacksize tf = fn_stackspace f).
    inv TF. auto.
  destruct SP as [spb [spb' [X [Y Rsp]]]]; subst sp'; inv X.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  edestruct free_parallel_inject as [tm' []]; eauto.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  eexists; exists tm', mu; split.
    simpl in *; rewrite Zplus_0_r in H4. rewrite <- H3 in H4.
    left; apply corestep_plus_one.
      eapply rtl_corestep_exec_Ireturn; try eassumption.
  assert (SMV': sm_valid mu m' tm').
    split; intros;
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_free _ _ _ _ _ H4);
          try rewrite (freshloc_free _ _ _ _ _ H0); intuition.
  econstructor. econstructor; eauto.
      intuition.
      eapply REACH_closed_free; try eassumption.
      eapply (free_free_inject _ m m' m2); try eassumption.

  (* assign *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [E F]]]]]]]; subst.
  eexists; eexists; exists mu; split.
    right; split. eauto. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor.
      intuition.

  (* store *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_exprlist_correct; eauto.
  intros [rs' [tm' [A [B [C [D [E F]]]]]]]; subst.
  exploit transl_expr_correct; eauto.
  intros [rs'' [tm'' [F [G [J [K [L M]]]]]]]; subst.
  destruct SP as [spb [spb' [X [Y Rsp]]]]; subst sp'; inv X.
  assert (val_list_inject (restrict (as_inj mu) (vis mu)) vl rs''##rl).
    replace (rs'' ## rl) with (rs' ## rl). auto.
    apply list_map_exten. intros. apply K. auto.
  edestruct eval_addressing_inject as [vaddr' []]; eauto.
  edestruct Mem.storev_mapped_inject as [tm''' []]; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
  eexists; exists tm''', mu; split.
    left; eapply corestep_star_plus_trans.
      eapply corestep_star_trans. eexact A. eexact F.
      eapply corestep_plus_one.
        eapply rtl_corestep_exec_Istore with (a := vaddr'). eauto.
        rewrite <- H4. rewrite shift_stack_addressing_zero.
        eapply eval_addressing_preserved. exact symbols_preserved.
      eassumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
        try rewrite (store_freshloc _ _ _ _ _ H2);
        try rewrite (store_freshloc _ _ _ _ _ H6); intuition.
      econstructor. econstructor; eauto. constructor.
        exists spb, spb'. split; trivial. split; trivial.
      intuition.
      (*rest of this case is almost identical to SelectionproofEFF.v, instruction store*)
      destruct vaddr; inv H2.
        eapply REACH_Store; try eassumption.
          inv H5. destruct (restrictD_Some _ _ _ _ _ H10); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.
                  inv J. destruct (restrictD_Some _ _ _ _ _ H11); trivial.
      assert (VaddrMu: val_inject (as_inj mu) vaddr vaddr').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      assert (VMu: val_inject (as_inj mu) v (rs'' # rd)).
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _
          MInj H2 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
      rewrite Hmm1 in H6. inv H6. assumption.

  (* call *)
  inv TS; inv H.
  (* indirect *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [X ?]]]]]]]; subst m2.
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst tm'.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  destruct (Genv.find_funct_inv _ _ H1) as [bb XX]; subst vf.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  inv C. destruct (restrictD_Some _ _ _ _ _ H5). rewrite H in muBB. inv muBB.
  rewrite Int.add_zero in H3.
  eexists; eexists; exists mu; split.
    left; eapply corestep_star_plus_trans.
            eapply corestep_star_trans. eexact A. eexact E.
          eapply corestep_plus_one.
            eapply rtl_corestep_exec_Icall; eauto.
               simpl. rewrite J. rewrite <- H3. eassumption. simpl; eauto.
               apply sig_transl_function; auto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; try eassumption.
      intuition.
  (* direct *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst m2.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  eexists; eexists; exists mu; split.
    left. eapply corestep_star_plus_trans. eexact E.
          eapply corestep_plus_one. eapply rtl_corestep_exec_Icall; eauto. simpl. rewrite symbols_preserved. rewrite H4.
             rewrite Genv.find_funct_find_funct_ptr in P. eauto.
             apply sig_transl_function; auto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; try eassumption.
      intuition.

  (* tailcall *)
  inv TS; inv H.
  (* indirect *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [X ?]]]]]]]; subst m2.
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst tm'.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
  destruct (Genv.find_funct_inv _ _ H1) as [bb XX]; subst vf.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  inv C. destruct (restrictD_Some _ _ _ _ _ H10). rewrite H7 in muBB. inv muBB.
  rewrite Int.add_zero in H9.
  eexists; exists tm'''; exists mu; split.
    left; eapply corestep_star_plus_trans.
           eapply corestep_star_trans. eexact A. eexact E.
           eapply corestep_plus_one.
             eapply rtl_corestep_exec_Itailcall; eauto.
             simpl. rewrite J. rewrite <- H9. eassumption.
             simpl; eauto.
             apply sig_transl_function; auto.
  simpl in H2; rewrite Zplus_0_r in H2. rewrite H; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.
  (* direct *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst m2.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
  eexists; exists tm''', mu; split.
    left; eapply corestep_star_plus_trans. eexact E.
          eapply corestep_plus_one.
            eapply rtl_corestep_exec_Itailcall; eauto.
             simpl. rewrite symbols_preserved. rewrite H5.
             rewrite Genv.find_funct_find_funct_ptr in P. eauto.
             apply sig_transl_function; auto.
  simpl in H2; rewrite Zplus_0_r in H2; rewrite H; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.

  (* builtin TODO
  inv TS.
  exploit transl_exprlist_correct; eauto.
  intros [rs' [tm' [E [F [G [J K]]]]]].
  edestruct external_call_mem_extends as [tv [tm'' [A [B [C D]]]]]; eauto.
  econstructor; split.
  left. eapply plus_right. eexact E.
  eapply exec_Ibuiltin. eauto.
  eapply external_call_symbols_preserved. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  traceEq.
  econstructor; eauto. constructor.
  eapply match_env_update_dest; eauto.

  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor.
      intuition.*)

  (* seq *)
  inv TS.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; eauto.
      intuition.

  (* ifthenelse *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_condexpr_correct; eauto.
  intros [rs' [tm' [A [B [C [D ?]]]]]]; subst m2.
  eexists; exists tm', mu; split.
    left. eexact A.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
       destruct b; econstructor; eauto.
      intuition.

  (* loop *)
  inversion TS; subst.
  eexists; exists m2, mu; split.
    left. apply corestep_plus_one. eapply rtl_corestep_exec_Inop; eauto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
       econstructor; eauto.
       econstructor; eauto.
       econstructor; eauto.
      intuition.
  (* block *)
  inv TS.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* exit seq *)
  inv TS. inv TK.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* exit block 0 *)
  inv TS. inv TK. simpl in H0. inv H0.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* exit block n+1 *)
  inv TS. inv TK. simpl in H0.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* switch *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit validate_switch_correct; eauto. intro CTM.
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [X ?]]]]]]]; subst m2.
  exploit transl_switch_correct; eauto. inv C. auto.
  intros [nd [rs'' [E [F G]]]].
  eexists; eexists; exists mu; split.
    right; split. eapply corestep_star_trans. eexact A. eexact E. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor; eassumption.
      intuition.

  (* return none *)
  inv TS.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
  eexists; exists tm''', mu; split.
    simpl in H0; rewrite Zplus_0_r in H0. rewrite <- H2 in H0.
    left; eapply corestep_plus_one.
            eapply rtl_corestep_exec_Ireturn; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.

  (* return some *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit transl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [E ?]]]]]]]; subst m2.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm'' []]; eauto.
  eexists; exists tm'', mu; split.
    simpl in H5; rewrite Zplus_0_r in H5. rewrite <- H4 in H5.
    left; eapply corestep_star_plus_trans. eexact A.
          eapply corestep_plus_one.
            eapply rtl_corestep_exec_Ireturn; eauto.
  assert (SMV': sm_valid mu m' tm'').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H5); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.
  (* label *)
  inv TS.
  eexists; exists m2, mu; split.
    right; split. apply corestep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.
  (* goto *)
  inv TS. inversion TF; subst.
  exploit tr_find_label; eauto. eapply tr_cont_call_cont; eauto.
  intros [ns2 [nd2 [nexits2 [A [B C]]]]].
  eexists; exists m2, mu; split.
    left; apply corestep_plus_one. eapply rtl_corestep_exec_Inop; eauto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.
  (* internal call *)
  monadInv TF. exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0.
  pose (e := set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f))).
  pose (rs := init_regs targs rparams).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  assert (ME: match_env (restrict (as_inj mu) (vis mu)) map2 e nil rs).
    unfold rs, e. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [IntInc [mu'SP mu'MuR]]]]]]]; eauto; try apply Zle_refl.
  destruct mu'MuR as [A [B [C [D [E F]]]]].
  eexists. exists tm', mu'; split.
    left; apply corestep_plus_one. eapply rtl_corestep_exec_function_internal; simpl; eauto.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H5).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; try eassumption.
         eapply intern_incr_vis; eassumption.
  intuition.
  split. econstructor; try eassumption.
           econstructor; eauto.
           simpl. inversion MS; subst; econstructor; eauto.
           econstructor.
           inv MS. econstructor; try eassumption.
                     eapply match_env_inject_incr; try eassumption.
                     eapply tr_cont_inject_incr; eassumption.
                       destruct H27 as [spb [spb' [SP [SP' XX]]]].
                       exists spb, spb'; split; trivial. split; trivial.
                       eapply IncVis; eassumption.
                     eapply match_env_inject_incr; try eassumption.
           eapply inject_restrict; eassumption.
           exists sp, b'. split; trivial. split; trivial.
             eapply restrictI_Some; try eassumption.
           destruct (as_inj_DomRng _ _ _ _ mu'SP); trivial.
              unfold DomSrc in H7; unfold vis.
              remember (locBlocksSrc mu' sp) as d.
              destruct d; trivial; simpl in *; apply eq_sym in Heqd.
              assert (extBlocksSrc mu = extBlocksSrc mu') by eapply IntInc.
              rewrite <- H9 in H7. unfold DomSrc in DomSP. rewrite H7 in DomSP. apply orb_false_iff in DomSP. destruct DomSP; discriminate.
  (*as in selectionproofEff*)
    intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption.
      intros. apply as_inj_DomRng in H7.
              split; eapply SMV; eapply H7.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H7). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
      apply Glob in H7. rewrite <-FF; trivial.

  (* no external call *)

  (* return *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  eexists; exists m2, mu; split.
    left; apply corestep_plus_one; constructor.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      split. econstructor; eauto. constructor.
             eapply match_env_update_dest; eauto.
      intuition.
Qed.

Lemma MATCH_effcore_diagram: forall
         st1 m1 st1' m1' (U1 : block -> Z -> bool)
         (CS: effstep cminsel_eff_sem ge U1 st1 m1 st1' m1')
         st2 mu m2
         (UHyp: forall b z, U1 b z = true ->
                Mem.valid_block m1 b -> vis mu b = true)
         (MTCH: MATCH st1 mu st1 m1 st2 m2),
exists st2' m2' mu', exists U2 : block -> Z -> bool,
  (effstep_plus rtl_eff_sem tge U2 st2 m2 st2' m2' \/
      effstep_star rtl_eff_sem tge U2 st2 m2 st2' m2' /\ lt_state st1' st1)
 /\ intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m2 /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  MATCH st1' mu' st1' m1' st2' m2' /\
     (forall (b : block) (ofs : Z),
      U2 b ofs = true ->
      Mem.valid_block m2 b /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1)%Z = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros st1 m1 st1' m1' U1 CS.
   induction CS; intros.

  (* skip seq *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS. inv TK.
  eexists; exists m2, mu; exists EmptyEffect; split.
     right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.

  (* skip block *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS. inv TK.
  eexists; exists m2, mu; exists EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor.
      intuition.

  (* skip return *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  assert ((fn_code tf)!ncont = Some(Ireturn rret)
          /\ match_stacks (restrict (as_inj mu) (vis mu)) k cs).
    inv TK; simpl in H; try contradiction; auto.
  destruct H1.
  assert (fn_stacksize tf = fn_stackspace f).
    inv TF. auto.
  destruct SP as [spb [spb' [X [Y Rsp]]]]; subst sp'; inv X.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  edestruct free_parallel_inject as [tm' []]; eauto.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  eexists; exists tm', mu, (FreeEffect m2 0 (fn_stacksize tf) spb'); split.
    simpl in *; rewrite Zplus_0_r in H4. rewrite <- H3 in H4.
    left; eapply effstep_plus_one.
        eapply rtl_effstep_exec_Ireturn; try eassumption.
  assert (SMV': sm_valid mu m' tm').
    split; intros;
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_free _ _ _ _ _ H4);
          try rewrite (freshloc_free _ _ _ _ _ H0); intuition.
  econstructor. econstructor; eauto.
      intuition.
      eapply REACH_closed_free; try eassumption.
      eapply (free_free_inject _ m m' m2); try eassumption.
  eapply FreeEffect_validblock; eassumption.
  rewrite H3 in H8. eapply FreeEffect_PropagateLeft; eassumption.

  (* assign *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [E F]]]]]]]; subst.
  eexists; eexists; exists mu, EmptyEffect; split.
    right; split. eassumption. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor.
      intuition.

  (* store *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs' [tm' [A [B [C [D [E F]]]]]]]; subst.
  exploit Efftransl_expr_correct; eauto.
  intros [rs'' [tm'' [F [G [J [K [L M]]]]]]]; subst.
  destruct SP as [spb [spb' [X [Y Rsp]]]]; subst sp'; inv X.
  assert (val_list_inject (restrict (as_inj mu) (vis mu)) vl rs''##rl).
    replace (rs'' ## rl) with (rs' ## rl). auto.
    apply list_map_exten. intros. apply K. auto.
  edestruct eval_addressing_inject as [vaddr' []]; eauto.
  edestruct Mem.storev_mapped_inject as [tm''' []]; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
  eexists; exists tm''', mu.
    exists (StoreEffect vaddr' (encode_val chunk (rs'' # rd))).
    split. left; eapply effstep_star_plus_trans.
      eapply effstep_star_trans.
         eapply effstep_star_sub. eexact A. intuition.
         eapply effstep_star_sub. eexact F. intuition.
      eapply effstep_plus_one.
        eapply rtl_effstep_exec_Istore with (a := vaddr'). eauto.
        rewrite <- H4. rewrite shift_stack_addressing_zero.
        eapply eval_addressing_preserved. exact symbols_preserved.
      eassumption.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
        try rewrite (store_freshloc _ _ _ _ _ H2);
        try rewrite (store_freshloc _ _ _ _ _ H6); intuition.
      econstructor. econstructor; eauto. constructor.
        exists spb, spb'. split; trivial. split; trivial.
      intuition.
      (*rest of this case is almost identical to SelectionproofEFF.v, instruction store*)
      destruct vaddr; inv H2.
        eapply REACH_Store; try eassumption.
          inv H5. destruct (restrictD_Some _ _ _ _ _ H10); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.
                  inv J. destruct (restrictD_Some _ _ _ _ _ H11); trivial.
      assert (VaddrMu: val_inject (as_inj mu) vaddr vaddr').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      assert (VMu: val_inject (as_inj mu) v (rs'' # rd)).
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _
          MInj H2 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
      rewrite Hmm1 in H6. inv H6. assumption.
      destruct (StoreEffectD _ _ _ _ H8) as [i [HI OFF]]. subst.
        simpl in H6. inv H5; inv H2.
          destruct (restrictD_Some _ _ _ _ _ H12).
          destruct (as_inj_DomRng _ _ _ _ H2); trivial.
          eapply SMV. apply H11.
      eapply StoreEffect_PropagateLeft; eassumption.

  (* call *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS; inv H.
  (* indirect *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [X ?]]]]]]]; subst m2.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst tm'.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  destruct (Genv.find_funct_inv _ _ H1) as [bb XX]; subst vf.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  inv C. destruct (restrictD_Some _ _ _ _ _ H5). rewrite H in muBB. inv muBB.
  rewrite Int.add_zero in H3.
  eexists; eexists; exists mu, EmptyEffect; split.
    left; eapply effstep_star_plus_trans.
            eapply effstep_star_trans. eexact A. eexact E.
          eapply effstep_plus_one.
            eapply rtl_effstep_exec_Icall; eauto.
               simpl. rewrite J. rewrite <- H3. eassumption. simpl; eauto.
               apply sig_transl_function; auto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; try eassumption.
      intuition.
  (* direct *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst m2.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  eexists; eexists; exists mu, EmptyEffect; split.
    left. eapply effstep_star_plus_trans. eexact E.
          eapply effstep_plus_one. eapply rtl_effstep_exec_Icall; eauto. simpl. rewrite symbols_preserved. rewrite H4.
             rewrite Genv.find_funct_find_funct_ptr in P. eauto.
             apply sig_transl_function; auto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; try eassumption.
      intuition.

  (* tailcall *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS; inv H.
  (* indirect *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [X ?]]]]]]]; subst m2.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst tm'.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
  destruct (Genv.find_funct_inv _ _ H1) as [bb XX]; subst vf.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  inv C. destruct (restrictD_Some _ _ _ _ _ H10). rewrite H7 in muBB. inv muBB.
  rewrite Int.add_zero in H9.
  eexists; exists tm'''; exists mu.
    exists (FreeEffect tm'' 0 (fn_stacksize tf) spb').
    split.
    left; eapply effstep_star_plus_trans.
           eapply effstep_star_trans.
              eapply effstep_star_sub. eexact A. intuition.
              eapply effstep_star_sub. eexact E. intuition.
           eapply effstep_plus_one.
             eapply rtl_effstep_exec_Itailcall; eauto.
             simpl. rewrite J. rewrite <- H9. eassumption.
             simpl; eauto.
             apply sig_transl_function; auto.
  simpl in H2; rewrite Zplus_0_r in H2. rewrite H; eauto.
  rewrite H in *.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
           eapply free_free_inject; try eassumption.
         eapply FreeEffect_validblock; eassumption.
         eapply FreeEffect_PropagateLeft; try eassumption.
  (* direct *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs'' [tm'' [E [F [G [J [Y ?]]]]]]]; subst m2.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
  eexists; exists tm''', mu.
    exists (FreeEffect tm'' 0 (fn_stacksize tf) spb').
    split.
    left; eapply effstep_star_plus_trans.
            eapply effstep_star_sub. eexact E. intuition.
          eapply effstep_plus_one.
            eapply rtl_effstep_exec_Itailcall; eauto.
             simpl. rewrite symbols_preserved. rewrite H5.
             rewrite Genv.find_funct_find_funct_ptr in P. eauto.
             apply sig_transl_function; auto.
  simpl in H2; rewrite Zplus_0_r in H2; rewrite H; eauto.
  rewrite H in *.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.
         eapply FreeEffect_validblock; eassumption.
         eapply FreeEffect_PropagateLeft; try eassumption.

  (* builtin TODO
  inv TS.
  exploit transl_exprlist_correct; eauto.
  intros [rs' [tm' [E [F [G [J K]]]]]].
  edestruct external_call_mem_extends as [tv [tm'' [A [B [C D]]]]]; eauto.
  econstructor; split.
  left. eapply plus_right. eexact E.
  eapply exec_Ibuiltin. eauto.
  eapply external_call_symbols_preserved. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  traceEq.
  econstructor; eauto. constructor.
  eapply match_env_update_dest; eauto.

  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor.
      intuition.*)

  (* seq *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; eauto.
      intuition.

  (* ifthenelse *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_condexpr_correct; eauto.
  intros [rs' [tm' [A [B [C [D ?]]]]]]; subst m2.
  eexists; exists tm', mu, EmptyEffect; split.
    left. eexact A.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
       destruct b; econstructor; eauto.
      intuition.

  (* loop *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inversion TS; subst.
  eexists; exists m2, mu, EmptyEffect; split.
    left. apply effstep_plus_one. eapply rtl_effstep_exec_Inop; eauto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
       econstructor; eauto.
       econstructor; eauto.
       econstructor; eauto.
      intuition.

  (* block *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* exit seq *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS. inv TK.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* exit block 0 *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS. inv TK. simpl in H0. inv H0.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* exit block n+1 *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS. inv TK. simpl in H0.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition.

  (* switch *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit validate_switch_correct; eauto. intro CTM.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [X ?]]]]]]]; subst m2.
  exploit Efftransl_switch_correct; eauto. inv C. auto.
  intros [nd [rs'' [E [F G]]]].
  eexists; eexists; exists mu, EmptyEffect; split.
    right; split. eapply effstep_star_trans. eexact A. eexact E. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor; eassumption.
      intuition.

  (* return none *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
  eexists; exists tm''', mu.
  exists (FreeEffect m2 0 (fn_stacksize tf) spb').
  split.
    simpl in H0; rewrite Zplus_0_r in H0. rewrite <- H2 in H0.
    left; eapply effstep_plus_one.
            eapply rtl_effstep_exec_Ireturn; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  rewrite H2 in *.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.
         eapply FreeEffect_validblock; eassumption.
         eapply FreeEffect_PropagateLeft; try eassumption.

  (* return some *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [A [B [C [D [E ?]]]]]]]; subst m2.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm'' []]; eauto.
  eexists; exists tm'', mu.
  exists (FreeEffect tm' 0 (fn_stacksize tf) spb').
  split.
    simpl in H5; rewrite Zplus_0_r in H5. rewrite <- H4 in H5.
    left; eapply effstep_star_plus_trans.
             eapply effstep_star_sub. eexact A. intuition.
          eapply effstep_plus_one.
            eapply rtl_effstep_exec_Ireturn; eauto.
  assert (SMV': sm_valid mu m' tm'').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  rewrite H4 in *.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b';
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H5); intuition.
      econstructor. econstructor; eauto.
      intuition.
         eapply REACH_closed_free; eassumption.
         destruct (restrictD_Some _ _ _ _ _ Rsp).
           eapply free_free_inject; try eassumption.
         eapply FreeEffect_validblock; eassumption.
         eapply FreeEffect_PropagateLeft; try eassumption.

  (* label *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.

  (* goto *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv TS. inversion TF; subst.
  exploit tr_find_label; eauto. eapply tr_cont_call_cont; eauto.
  intros [ns2 [nd2 [nexits2 [A [B C]]]]].
  eexists; exists m2, mu, EmptyEffect; split.
    left; apply effstep_plus_one. eapply rtl_effstep_exec_Inop; eauto.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.

  (* internal call *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  monadInv TF. exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0.
  pose (e := set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f))).
  pose (rs := init_regs targs rparams).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
     rewrite <- restrict_sm_all.
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition.
  assert (ME: match_env (restrict (as_inj mu) (vis mu)) map2 e nil rs).
    unfold rs, e. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [IntInc [mu'SP mu'MuR]]]]]]]; eauto; try apply Zle_refl.
  destruct mu'MuR as [A [B [C [D [E F]]]]].
  eexists. exists tm', mu', EmptyEffect; split.
    left; apply effstep_plus_one. eapply rtl_effstep_exec_function_internal; simpl; eauto.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H5).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; try eassumption.
         eapply intern_incr_vis; eassumption.
  intuition.
  split. econstructor; try eassumption.
           econstructor; eauto.
           simpl. inversion MS; subst; econstructor; eauto.
           econstructor.
           inv MS. econstructor; try eassumption.
                     eapply match_env_inject_incr; try eassumption.
                     eapply tr_cont_inject_incr; eassumption.
                       destruct H27 as [spb [spb' [SP [SP' XX]]]].
                       exists spb, spb'; split; trivial. split; trivial.
                       eapply IncVis; eassumption.
                     eapply match_env_inject_incr; try eassumption.
           eapply inject_restrict; eassumption.
           exists sp, b'. split; trivial. split; trivial.
             eapply restrictI_Some; try eassumption.
           destruct (as_inj_DomRng _ _ _ _ mu'SP); trivial.
              unfold DomSrc in H7; unfold vis.
              remember (locBlocksSrc mu' sp) as d.
              destruct d; trivial; simpl in *; apply eq_sym in Heqd.
              assert (extBlocksSrc mu = extBlocksSrc mu') by eapply IntInc.
              rewrite <- H9 in H7. unfold DomSrc in DomSP. rewrite H7 in DomSP. apply orb_false_iff in DomSP. destruct DomSP; discriminate.
  (*as in selectionproofEff*)
    intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption.
      intros. apply as_inj_DomRng in H7.
              split; eapply SMV; eapply H7.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H7). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
      apply Glob in H7. rewrite <-FF; trivial.

  (* no external call *)

  (* return *)
  destruct MTCH as [MSTATE PRE]. inv MSTATE.
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  eexists; exists m2, mu, EmptyEffect; split.
    left; apply effstep_plus_one; constructor.
  intuition.
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition.
      split. econstructor; eauto. constructor.
             eapply match_env_update_dest; eauto.
      intuition.

(*inductive case*)
  assert (EHyp: forall b z, E b z = true ->
           Mem.valid_block m b -> vis mu b = true).
     intros. eapply UHyp; eauto.
  destruct (IHCS _ _ _ EHyp MTCH) as [c2' [m2' [mu' [U2 [HH1 HH2]]]]].
  exists c2', m2', mu', U2. split; trivial.
  destruct HH2 as [? [? [? [? ?]]]].
  repeat (split; trivial).
    eapply (H4 _ _ H5).
  intros. destruct (H4 _ _ H5).
    destruct (H8 H6) as [b1 [delta [Frg [HE HP]]]]; clear H8.
    exists b1, delta. split; trivial. split; trivial.
    apply Mem.perm_valid_block in HP.
    apply H; assumption.
Qed.

(** The simulation proof *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs prog)))
         entrypoints
         (entry_points_ok :
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints ->
              exists b f1 f2,
                v1 = Vptr b Int.zero
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr ge b = Some f1
                /\ Genv.find_funct_ptr tge b = Some f2)
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
SM_simulation.SM_simulation_inject cminsel_eff_sem
   rtl_eff_sem ge tge entrypoints.
Proof.
intros.
assert (GDE: genvs_domain_eq ge tge).
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
 apply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf with
  (match_states:=MATCH) (order :=lt_state).
(*genvs_dom_eq*)
  assumption.
(*MATCH_wd*)
  apply MATCH_wd.
(*MATCH_reachclosed*)
  apply MATCH_RC.
(*MATCH_restrict*)
  apply MATCH_restrict.
(*MATCH_valid*)
  apply MATCH_valid.
(*MATCH_preserves_globals*)
  apply MATCH_PG.
(*MATCHinitial*)
  { intros.
    eapply (MATCH_initial _ _ _ entrypoints); eauto.
    destruct init_mem as [m0 INIT].
    exists m0; split; auto.
    unfold meminj_preserves_globals in H3.
    destruct H3 as [A [B C]].

    assert (P: forall p q, {Ple p q} + {Plt q p}).
      intros p q.
      case_eq (Pos.leb p q).
      intros TRUE.
      apply Pos.leb_le in TRUE.
      left; auto.
      intros FALSE.
      apply Pos.leb_gt in FALSE.
      right; auto.

    cut (forall b, Plt b (Mem.nextblock m0) ->
           exists id, Genv.find_symbol ge id = Some b). intro D.

    split.
    destruct (P (Mem.nextblock m0) (Mem.nextblock m1)); auto.
    exfalso.
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - H8; unfold Mem.valid_block in H8.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso.
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H8; unfold Mem.valid_block in H8.
    xomega.

    intros b LT.
    unfold ge.
    apply valid_init_is_global with (b0 := b) in INIT.
    eapply INIT; auto.
    apply R.
    apply LT. }
(*halted*)
  { intros. destruct H as [MC [RC [PG [GFP [Glob [VAL [WD INJ]]]]]]].
    destruct c1; inv H0. destruct k; inv H1.
    inv MC. exists tv.
    split. assumption.
    split. eassumption.
    simpl. inv MS. trivial. }
(* at_external*)
  { intros. destruct H as [MC [RC [PG [GFP [Glob [VAL [WD INJ]]]]]]].
    split; trivial.
    destruct c1; inv H0. destruct f; inv H1.
    inv MC. simpl. exists targs; intuition.
      apply val_list_inject_forall_inject; eassumption.
    inv TF. trivial. }
(* after_external*)
  { apply MATCH_afterExternal. assumption. }
(* order_wf *)
  { apply lt_state_wf. }
(* core_diagram*)
  { intros. exploit MATCH_corestep; try eassumption.
     intros [st2' [m2' [mu' [CS' X]]]].
     exists st2', m2', mu'. intuition. }
(*effcore_diagram*)
 { intros. exploit MATCH_effcore_diagram; try eassumption.
    intros [st2' [m2' [mu' [U2 [CS2 [? [? [? [? ?]]]]]]]]].
    exists st2', m2', mu'.
    repeat (split; trivial).
    exists U2. split; assumption. }
Qed.

End CORRECTNESS.
