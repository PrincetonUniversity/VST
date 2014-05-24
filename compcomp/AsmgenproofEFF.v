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

(** Correctness proof for x86 generation: main proof. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Conventions.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenproof0EFF.
Require Import Asmgenproof1EFF.

Require Import Mach_coop.
Require Import Mach_eff.
Require Import Asm_coop.
Require Import Asm_eff.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import reach.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.
Require Import BuiltinEffects.

Require Export Axioms.
Require Import OpEFF.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
      rewrite <- symbols_preserved in Hid.
      exists id; assumption.
     rewrite symbols_preserved in Hid.
      exists id; assumption.
     split; intros; destruct H as [id Hid].
      rewrite <- varinfo_preserved in Hid.
      exists id; assumption.
     rewrite varinfo_preserved in Hid.
      exists id; assumption.
Qed.


(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf <= Int.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt (list_length_z x) Int.max_unsigned); monadInv EQ0.
  rewrite list_length_z_cons. omega. 
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  corestep_plus Asm_eff_sem  tge (State rs) m (State rs') m'.
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto. 
Qed.

Lemma eff_exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m' U ,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  eff_exec_straight tge tf U tc rs m c' rs' m' ->
  effstep_plus Asm_eff_sem tge U (State rs) m (State rs') m'.
Proof.
  intros. inv H.
  eapply eff_exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto. 
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H. 
  exploit exec_straight_steps_2; eauto. 
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

Lemma eff_exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m' U,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  eff_exec_straight tge tf U tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H. 
  exploit eff_exec_straight_steps_2; eauto. 
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros. 
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c -> 
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel. 
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_smallstore_label:
  forall f addr r k c, mk_smallstore f addr r k = OK c -> 
  (forall r addr, nolabel (f r addr)) ->
  tail_nolabel k c.
Proof.
  unfold mk_smallstore; intros. TailNoLabel. 
Qed.
Hint Resolve mk_smallstore_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty.
  TailNoLabel.
  destruct (preg_of dst); TailNoLabel.
  discriminate.
  TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty.
  TailNoLabel.
  destruct (preg_of src); TailNoLabel.
  discriminate.
  TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd EAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec i Int.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec i Int.zero); TailNoLabel.
  destruct (Float.eq_dec f Float.zero); TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.  
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto. 
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.  
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B). 
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a). 
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf = None
  | Some c => exists tc, find_label lbl tf = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt (list_length_z x) Int.max_unsigned); inv EQ0.
  simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ; eauto. 
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m  
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2. 
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Int.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto. 
  rewrite Int.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0EFF.return_address_exists; eauto. 
- intros. exploit transl_instr_label; eauto. 
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0. 
  destruct (zlt (list_length_z x) Int.max_unsigned); inv EQ0.
  rewrite transl_code'_transl_code in EQ.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

(*Definition sp_zero_or_local mu sp:= 
  sp=Vzero \/ exists spb ofs, sp=Vptr spb ofs /\ 
                              locBlocksSrc mu spb = true.
*)
Inductive match_states mu: Mach_core -> mem -> Asm_coop.state -> mem -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge (restrict_sm mu (vis mu)) s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.inject (as_inj mu) m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree (restrict_sm mu (vis mu)) ms sp rs)
        (*(DXP: ep = true -> rs#EDX = parent_sp s)*)
        (DXP: ep = true -> 
              val_inject (as_inj (restrict_sm mu (vis mu))) (parent_sp s) (rs#EDX))
        (*NEW (SPlocalSrc: sp_zero_or_local mu sp)*)
        (*NEW*) (SPlocal: zero_or_localid mu sp),
      match_states mu (Mach_State s fb sp c ms) m
                      (State rs) m'

(*Lenb: new: distinguish internal and external calls*)
  | match_states_call_internal:
      forall s fb ms m m' rs
        (STACKS: match_stack ge (restrict_sm mu (vis mu)) s)
        (MEXT: Mem.inject (as_inj mu) m m')
        (AG: agree (restrict_sm mu (vis mu)) ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Int.zero)
        (*WAS: (ATLR: rs RA = parent_ra s)*)
        (ATLR: val_inject (as_inj (restrict_sm mu (vis mu))) (parent_ra s) (rs RA))
        (*NEW*) f (INT: Genv.find_funct_ptr ge fb = Some (Internal f)),
      match_states mu (Mach_Callstate s fb ms) m
                      (State rs) m'
  | match_states_call_external:
      forall s fb ms m m' rs
        (STACKS: match_stack ge (restrict_sm mu (vis mu)) s)
        (MEXT: Mem.inject (as_inj mu) m m')
        (AG: agree (restrict_sm mu (vis mu)) ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Int.zero)
        (*WAS: (ATLR: rs RA = parent_ra s)*)
        (ATLR: val_inject (as_inj (restrict_sm mu (vis mu))) (parent_ra s) (rs RA))
        ef (EF: Genv.find_funct_ptr ge fb = Some (External ef))
        args (ARGS: Mach.extcall_arguments ms m (parent_sp s) (ef_sig ef) args)
        args' (ARGS': extcall_arguments rs m' (ef_sig ef) args')
        (ArgsInj: val_list_inject (as_inj (restrict_sm mu (vis mu))) args args'),
      match_states mu (Mach_CallstateArgs s fb ef args ms) m
                      (ExtCallState ef args' rs) m'
  | match_states_return:
      forall s ms m m' retty rs
        (STACKS: match_stack ge (restrict_sm mu (vis mu)) s)
        (MEXT: Mem.inject (as_inj mu) m m')
        (AG: agree (restrict_sm mu (vis mu)) ms (parent_sp s) rs)
        (*WAS: (ATPC: rs PC = parent_ra s),*)
        (ATPC: val_inject (as_inj (restrict_sm mu (vis mu))) (parent_ra s) (rs PC)),
      match_states mu (Mach_Returnstate s retty ms) m
                      (State rs) m'.

Lemma exec_straight_steps:
  forall mu s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge (restrict_sm mu (vis mu)) s ->
  Mem.inject (as_inj mu) m2 m2' -> (*Mem.extends m2 m2' ->*)
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree (restrict_sm mu (vis mu)) ms2 sp rs2
    (*/\ (it1_is_parent ep i = true -> rs2#EDX = parent_sp s)) ->*)
    /\ (it1_is_parent ep i = true ->
        val_inject (as_inj (restrict_sm mu (vis mu))) (parent_sp s) (rs2#EDX))) ->
  (*NEW forall (SPlocalSrc: sp_zero_or_local mu sp)*)
  (*NEW*) forall (SPlocal: zero_or_localid mu sp),
  exists st',
  corestep_plus Asm_eff_sem tge (State rs1) m1' st' m2' /\
  match_states mu (Mach_State s fb sp c ms2) m2 st' m2'.
Proof.
  intros. inversion H2. subst. monadInv H7. 
  exploit H3; eauto. intros [rs2 [A [B C]]]. 
  exists (State rs2); split.
  eapply exec_straight_exec; eauto. 
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma eff_exec_straight_steps:
  forall mu s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 U,
  match_stack ge (restrict_sm mu (vis mu)) s ->
  Mem.inject (as_inj mu) m2 m2' -> (*Mem.extends m2 m2' ->*)
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       eff_exec_straight tge tf U c rs1 m1' k rs2 m2'
    /\ agree (restrict_sm mu (vis mu)) ms2 sp rs2
    (*/\ (it1_is_parent ep i = true -> rs2#EDX = parent_sp s)) ->*)
    /\ (it1_is_parent ep i = true ->
        val_inject (as_inj (restrict_sm mu (vis mu))) (parent_sp s) (rs2#EDX))) ->
  (*NEW forall (SPlocalSrc: sp_zero_or_local mu sp)*)
  (*NEW*) forall (SPlocal: zero_or_localid mu sp),
  exists st',
  effstep_plus Asm_eff_sem tge U (State rs1) m1' st' m2' /\
  match_states mu (Mach_State s fb sp c ms2) m2 st' m2'.
Proof.
  intros. inversion H2. subst. monadInv H7. 
  exploit H3; eauto. intros [rs2 [A [B C]]]. 
  exists (State rs2); split.
  eapply eff_exec_straight_exec; eauto. 
  econstructor; eauto. eapply eff_exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall mu s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge (restrict_sm mu (vis mu)) s ->
  Mem.inject (as_inj mu) m2 m2' -> (*Mem.extends m2 m2' ->*)
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree (restrict_sm mu (vis mu)) ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  (*NEW forall (SPlocalSrc: sp_zero_or_local mu sp)*)
  (*NEW*) forall (SPlocal: zero_or_localid mu sp),
  exists st',
  corestep_plus Asm_eff_sem  tge (State rs1) m1' st' m2' /\
  match_states mu (Mach_State s fb sp c' ms2) m2 st' m2'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3); split.
  eapply corestep_plus_trans.
    eapply exec_straight_steps_1; eauto.  
    eapply corestep_plus_one. 
      econstructor; eauto.
        eapply find_instr_tail. eauto. 
        rewrite C. eexact GOTO.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

Lemma eff_exec_straight_steps_goto:
  forall mu s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge (restrict_sm mu (vis mu)) s ->
  Mem.inject (as_inj mu) m2 m2' -> (*Mem.extends m2 m2' ->*)
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       eff_exec_straight tge tf EmptyEffect c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree (restrict_sm mu (vis mu)) ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2'
    /\ effect_instr tge tf jmp rs2 m2' = EmptyEffect) ->
  (*NEW forall (SPlocalSrc: sp_zero_or_local mu sp)*)
  (*NEW*) forall (SPlocal: zero_or_localid mu sp),
  exists st',
  effstep_plus Asm_eff_sem tge EmptyEffect (State rs1) m1' st' m2' /\
  match_states mu (Mach_State s fb sp c' ms2) m2 st' m2'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B [C D]]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit eff_exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3); split.
  eapply effstep_plus_trans'.
    eapply eff_exec_straight_steps_1; eauto.  
    eapply effstep_plus_one. 
      econstructor; eauto.
        eapply find_instr_tail. eauto. 
        rewrite C. eexact GOTO.
        rewrite D. intuition.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

Lemma restrict_sm_zero_or_localid mu X sp: forall
        (HX : forall b : block, vis mu b = true -> X b = true)
        (WD: SM_wd mu),
      zero_or_localid (restrict_sm mu X) sp =
      zero_or_localid mu sp.
Proof. unfold zero_or_localid; intros.
rewrite restrict_sm_local'; trivial.
Qed.

Lemma match_states_restrict mu c1 m1 c2 m2: forall
        (MS:match_states mu c1 m1 c2 m2) X
        (RC: REACH_closed m1 X)
        (HX : forall b : block, vis mu b = true -> X b = true)
        (WD: SM_wd mu),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros. inv MS.
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite restrict_sm_zero_or_localid; trivial.
     (*unfold sp_zero_or_local. rewrite restrict_sm_locBlocksSrc. assumption.*)
     unfold zero_or_localid.
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
       rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.     
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
Qed.

(*NEW, GFP as in selectionproofEFF*)
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

Definition MATCH (d:Mach_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\ 
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu.

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
  destruct MC as [MS [RC [PG [GF [Glob [SMV WD]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  eapply match_states_restrict; eassumption.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. rewrite restrict_sm_all. 
       eapply restrict_preserves_globalfun_ptr; try eassumption.
        intros. eapply HX. unfold vis. rewrite (Glob _ H). intuition.
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply Glob.
split. 
  destruct SMV.
  split; intros.
    rewrite restrict_sm_DOM in H1.
    apply (H _ H1).
  rewrite restrict_sm_RNG in H1.
    apply (H0 _ H1).
assumption.
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

Lemma agree_eval_addressing_inject: forall a mu rs args addr rs0 sp
      (EV: eval_addressing ge sp addr rs ## args = Some a)
      (PG : meminj_preserves_globals ge (as_inj mu))
      (Glob : forall b, isGlobalBlock ge b = true ->
              frgnBlocksSrc mu b = true)
      (WD : SM_wd mu)
      (AG : agree (restrict_sm mu (vis mu)) rs sp rs0)
      (SPlocalSrc : zero_or_localid mu sp (*sp_zero_or_local mu sp*)),
  exists a',
    eval_addressing ge (rs0 ESP) addr rs0 ## (preg_of ## args) = Some a' /\
    val_inject (as_inj (restrict_sm mu (vis mu))) a a'.
Proof. intros.
     destruct SPlocalSrc.
    (*case sp=Vzero*) subst.
       eapply eval_addressing_sp_scalar; try eassumption.
         eapply sp_as_inj. eassumption.
            apply restrict_sm_WD; trivial. 
        eapply restrict_sm_preserves_globals with (X:=vis mu). eassumption.
          unfold vis; intuition.
        eapply preg_vals; eassumption.
    (*case sp=Vptr spb ofs*) 
      destruct H as [spb [z [tb [SP LocSPSrc]]]]; subst.      
      exploit eval_addressing_inject'; try eapply EV. 
        eapply restrict_sm_preserves_globals with (X:=vis mu). eassumption.
          unfold vis; intuition.
        eapply local_in_all; try eassumption.
          apply restrict_sm_WD; trivial.
          rewrite restrict_sm_local'; trivial. eassumption.
        eapply preg_vals; eassumption.
    rewrite eval_shift_stack_addressing. simpl.
      specialize (agree_sp_local _ _ _ _ AG). intros.
      inv H. rewrite restrict_sm_local' in H4; trivial.
      rewrite LocSPSrc in H4. inv H4. apply H0. 
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach_core) : nat :=
  match s with
  | Mach_Returnstate _ _ _ => 1%nat
  | _ => 0%nat
  end.

Lemma zero_or_localid_intern_incr mu mu': forall 
   (INC: intern_incr mu mu') v
   (ZLOC: zero_or_localid mu v), zero_or_localid mu' v.
Proof. intros.
destruct ZLOC as [Zero | [b [ofs [tb [SP LOC]]]]]; subst.
  left; trivial.
  right. apply INC in LOC. 
    exists b, ofs, tb; split; trivial.
Qed.

Lemma zero_or_vis_intern_incr mu mu': forall 
   (INC: intern_incr mu mu') v
   (ZLOV: zero_or_vis ge mu v), zero_or_vis ge mu' v.
Proof. intros.
destruct ZLOV as [Zero | [b [ofs [SP [[tb LOC] | GL]]]]]; subst.
left; trivial.
right. exists b, ofs; split; trivial. left. exists tb. apply INC; trivial.
right. exists b, ofs; split; trivial. right; trivial.
Qed.


Lemma match_stack_intern_incr mu mu': forall
   (INC: intern_incr mu mu') s
   (MS: match_stack ge mu s),
   match_stack ge mu' s.
Proof. intros.
induction MS; econstructor; eauto.
eapply zero_or_localid_intern_incr; eassumption.
eapply zero_or_vis_intern_incr; eassumption.
Qed.

Section EXT_ARGUMENTS_LOADV.
Variable rs: regset.
Variable sg: signature.
Variable m1: mem.
Variable m2: mem.
Variable u: val.

(*NEW*)
Lemma extcall_argument_loadv:
  forall l (Hl: In l (loc_arguments sg))
  (HH: forall ofs ty, In (S Outgoing ofs ty) (loc_arguments sg) ->
          Mem.loadv (chunk_of_type ty) m2 (Val.add (rs ESP) (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))) =
          Mem.loadv (chunk_of_type ty) m1 (Val.add (rs ESP) (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))))
  v (EC: extcall_arg rs m1 l v),
  extcall_arg rs m2 l v. 
Proof.
  intros.
  assert (loc_argument_acceptable l). apply loc_arguments_acceptable with sg; auto.
  inv EC; econstructor.
  reflexivity. rewrite <- H1. apply HH. trivial.
Qed.

(*NEW*)
Lemma extcall_arguments_loadv:
  forall locs (Hlocs: incl locs (loc_arguments sg))
  (HH: forall ofs ty, In (S Outgoing ofs ty) (loc_arguments sg) ->
          Mem.loadv (chunk_of_type ty) m2 (Val.add (rs ESP) (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))) =
          Mem.loadv (chunk_of_type ty) m1 (Val.add (rs ESP) (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))))
  vl (VL: list_forall2 (extcall_arg rs m1) locs vl),
  list_forall2 (extcall_arg rs m2) locs vl.
Proof.
  induction locs; simpl; intros.
  inv VL. constructor. 
  inv VL. constructor.
    eapply extcall_argument_loadv.
      eapply Hlocs. left; trivial.
    assumption. assumption.
  eapply IHlocs; trivial.
    red; intros. eapply Hlocs. right; trivial.
Qed.
End EXT_ARGUMENTS_LOADV.


Lemma effcore_diagram: forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
      (CS: effstep (Mach_eff_sem return_address_offset) ge U1 st1 m1 st1' m1')
      st2 mu m2
      (U1Vis: forall b ofs, U1 b ofs = true -> vis mu b = true)
      (MTCH: MATCH st1 mu st1 m1 st2 m2),
exists st2' m2' (U2 : block -> Z -> bool),
     (effstep_plus Asm_eff_sem tge U2 st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
      effstep_star Asm_eff_sem tge U2 st2 m2 st2' m2')
 /\ exists mu',
    intern_incr mu mu' /\
    sm_inject_separated mu mu' m1 m2 /\
    sm_locally_allocated mu mu' m1 m2 m1' m2' /\
    MATCH st1' mu' st1' m1' st2' m2' /\
   (forall b ofs, U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros.
destruct CS; intros; destruct MTCH as [MS PRE]; try inv MS.
{ (* Mlabel *)
  exploit eff_exec_straight_steps; try eassumption.
  intros. monadInv TR. econstructor; split. apply eff_exec_straight_one. simpl; eauto. auto. 
    reflexivity.
    split. apply agree_nextinstr; auto. eassumption. simpl; congruence.
  intros [st' [CS' MS']].
  exists st', m2. 
  eexists; split. left; eassumption. 
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
  simpl; intros. intuition.  }

{ (* Mgetstack *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  unfold load_stack in H. 
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tb LocSP].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSP in H3; apply eq_sym in H3; inv H3.
  rename H2 into RSP. rewrite Int.add_zero in RSP.
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst.*)
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu))));
    try eassumption.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    rewrite restrict_sm_local in LocSP.
      destruct (restrictD_Some _ _ _ _ _ LocSP).
      apply local_in_all in H0; trivial.
      rewrite restrict_sm_all. eapply restrictI_Some; eassumption.
  rewrite Zplus_0_r.
  intros [v' [A B]].
  exploit (eff_exec_straight_steps mu); try eassumption. 
    intros. simpl in TR.
    exploit loadind_correct_eff. eassumption. 
       instantiate (2:=rs0). rewrite <- RSP; simpl. eassumption.
  intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. 
    eapply agree_set_mreg. eassumption.
    instantiate (1:=dst). instantiate (1:=v). rewrite Q. assumption.
    assumption.
    simpl. congruence.
  intros [st' [CS' MS']].
  exists st', m2. 
  eexists; split. left; eassumption. 
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
  intuition. }

{ (* Msetstack *)
  unfold store_stack in H.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tb LocSP].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSP in H3; apply eq_sym in H3; inv H3.
  rename H2 into RSP. rewrite Int.add_zero in RSP.
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst.  simpl in H.*)
  exploit (Mem.store_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_local in LocSP.
      destruct (restrictD_Some _ _ _ _ _ LocSP).
      apply local_in_all in H0; trivial.
      eassumption.
    eapply val_inject_incr; try eapply AG. 
        rewrite restrict_sm_all. apply restrict_incr. 
  simpl. rewrite Zplus_0_r. intros [m2' [A B]].
  exploit (eff_exec_straight_steps mu). eassumption. apply B. eassumption. eassumption.
    intros. simpl in TR.
    exploit storeind_correct_eff. eassumption. 
     instantiate (2:=rs0). rewrite <- RSP. simpl. apply A.
  intros [rs' [P Q]].
  eexists; split. eassumption.
    split. eapply agree_undef_regs; eauto. 
    simpl; intros. rewrite Q; auto with asmgen. 
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.
  assumption. 
  intros [st' [CS' MS']].
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
  exists st', m2'.
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ A). intuition. 
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ A). intuition. 
  split. split; intuition.
         eapply REACH_Store; try eassumption. 
          rewrite restrict_sm_local in LocSP.
            destruct (restrictD_Some _ _ _ _ _ LocSP); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (agree_mregs _ _ _ _ AG src); intros AMR.
                   rewrite H0 in AMR; inv AMR.   
                   rewrite restrict_sm_all in H4. 
                   destruct (restrictD_Some _ _ _ _ _ H4); trivial. 
  simpl; intros. 
    apply StoreEffectD in H0. rewrite <- RSP in H0; simpl in H0.
    destruct H0 as [i [PtrEq Arith]]; inv PtrEq.
    rewrite restrict_sm_local in LocSP.
    destruct (restrictD_Some _ _ _ _ _ LocSP).
    destruct (local_DomRng _ WD _ _ _ H0).
    unfold visTgt. rewrite H3. intuition. }

{ (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *. 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H0. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H0.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tb LocSP].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSP in H5; apply eq_sym in H5; inv H5.
  rename H4 into RSP. rewrite Int.add_zero in RSP.
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0. 
    rewrite restrict_sm_local in LocSP.
      destruct (restrictD_Some _ _ _ _ _ LocSP).
      apply local_in_all in H2; trivial.
      rewrite restrict_sm_all. eapply restrictI_Some; eassumption.
  rewrite Zplus_0_r.
  intros [parent' [A B]]. simpl in *.
  remember (parent_sp s) as u.
     destruct u; simpl in *; try inv H1.
  inv B.
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H3.
    eassumption.
  intros [v' [C D]].
Opaque loadind.
  exploit (eff_exec_straight_steps mu); try eassumption.
    intros. instantiate (2:=m2). (*instantiate (1 := (Vptr spb z)).*)
      instantiate(1 := (@Regmap.set val dst v
                      (@Regmap.set val temp_for_parent_frame Vundef rs))).
    assert (DIFF: negb (mreg_eq dst DX) = true -> IR EDX <> preg_of dst).
      intros. change (IR EDX) with (preg_of DX). red; intros. 
      unfold proj_sumbool in H1. destruct (mreg_eq dst DX); try discriminate.
      elim n. eapply preg_of_injective; eauto.
    assert (Int.unsigned (Int.add (Int.add i (Int.repr delta)) ofs)
              = Int.unsigned (Int.add i ofs) + delta).
        rewrite Int.add_assoc. rewrite (Int.add_commut (Int.repr delta)).
        rewrite <- Int.add_assoc. 
        eapply Mem.address_inject; try eassumption. 
        eapply Mem.load_valid_access. eapply H3.
          split. omega. specialize (size_chunk_pos (chunk_of_type ty)); intros. omega.
        rewrite restrict_sm_all in H4. eapply restrictD_Some. eassumption.
    rewrite <- H1 in C. clear H1.
    destruct ep; simpl in TR.
    (* EDX contains parent *)
      assert (VI: val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr b i) (rs0 EDX)).
        eauto. 
      clear DXP. inv VI. rewrite H4 in H6. inv H6.
      exploit loadind_correct_eff. eexact TR.
        instantiate (2 := rs0). rewrite <- H5. simpl. apply C. 
      intros [rs1 [P [Q R]]].
      exists rs1; split. eauto. 
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
      simpl; intros. rewrite R, <- Hequ, <- H5. econstructor. eassumption. trivial.
      auto. auto.
    (* EDX does not contain parent *)
      monadInv TR.
      exploit loadind_correct_eff. eexact EQ0.
      instantiate (2:=rs0). rewrite <- RSP. simpl. eauto.
      intros [rs1 [P [Q R]]]. simpl in Q.
      exploit loadind_correct_eff. eexact EQ.
        instantiate (2 := rs1). rewrite Q. simpl. eauto.
      intros [rs2 [S [T U]]]. 
      exists rs2; split. eapply eff_exec_straight_trans; eauto.
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
      simpl; intros. rewrite U, <- Hequ, Q. econstructor. eassumption. trivial. 
      auto. auto.

  intros [st' [CS' MS']].
  exists st', m2.
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
  intuition. }

{ (* Mop *)
  assert (eval_operation tge sp op rs##args m = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  specialize (agree_sp_local _ _ _ _ AG); intros LocSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit (preg_vals (restrict_sm mu (vis mu))). eassumption.
  intros ArgsInj.
  exploit eval_operation_inject''; try eapply H0; try eapply ArgsInj.
    eapply val_inject_incr; try eassumption.
        rewrite restrict_sm_local, restrict_sm_all.
        red; intros. destruct (restrictD_Some _ _ _ _ _ H1). 
             apply local_in_all in H2; trivial.
             eapply restrictI_Some; eassumption.  
    eapply restrict_sm_preserves_globals.
      apply meminj_preserves_genv2blocks.
        apply meminj_preserves_genv2blocks in PG.
        eapply genvs_domain_eq_preserves; try eassumption.
        apply genvs_domain_eq_sym; eapply GDE_lemma.
      unfold vis. intuition. rewrite Glob. intuition.
      rewrite (genvs_domain_eq_isGlobal _ _ GDE_lemma); trivial.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
  intros [v' [A B]].
(*  specialize (sp_val _ _ _ _ AG); intros RSP.*)
  (*rewrite eval_shift_stack_operation in A. simpl in A. rewrite Int.add_zero in A.*)
  exploit (eff_exec_straight_steps mu); try eassumption. 
    intros. simpl in TR.
    exploit transl_op_correct_eff; eauto. 
     (* instantiate (3:=rs0). rewrite RSP. apply A.*)
    intros [rs2 [P [Q R]]]. 
    assert (S: val_inject (as_inj (restrict_sm mu (vis mu))) v (rs2 (preg_of res))).
      eapply valinject_lessdef; try eassumption.
    exists rs2; split. eauto.
    split. eapply agree_set_undef_mreg; eassumption.
    simpl; congruence.
  intros [st' [CS' MS']].
  exists st', m2.
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
  intuition. }

{ (* Mload *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  (*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *. *)
  exploit agree_eval_addressing_inject; try eassumption.
  intros [a' [A B]].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP. 
  (*specialize (sp_val _ _ _ _ AG); intros RSP.*)
  assert (eval_addressing tge (rs0 ESP) addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A. (* rewrite <- RSP. *) (*rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
    apply eval_addressing_preserved. exact symbols_preserved.
  clear A; rename H1 into A.
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0. 
    apply B. 
  intros [v' [C D]].
  exploit (eff_exec_straight_steps mu). eassumption. eassumption. eassumption.
    eassumption. 
    intros. simpl in TR.
    exploit transl_load_correct_eff; eauto.
     (* instantiate (5:=rs0). rewrite <- RSP. eapply A.*)
    intros [rs2 [P [Q R]]]. 
    exists rs2; split. eauto.
    split. eapply agree_set_undef_mreg. eassumption.
           instantiate (1:=dst). rewrite Q. eassumption. eauto.
    simpl; intros. congruence.
    assumption. (*right. exists spb, z; split; trivial.*)
  intros [st' [CS' MS']].
  exists st', m2. 
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
         eassumption.
         intuition. }

{ (* Mstore *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit agree_eval_addressing_inject; try eassumption.
  intros [a' [A B]].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP. 
  (*  specialize (sp_val _ _ _ _ AG); intros RSP.*)
  assert (eval_addressing tge (rs0 ESP) addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A. (*rewrite <- RSP. rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
    apply eval_addressing_preserved. exact symbols_preserved.
  clear A; rename H1 into A.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (rs src) (rs0 (preg_of src))).
      eapply preg_val; eassumption.
  exploit (Mem.storev_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_all in B.
      eapply val_inject_incr; try eapply B. apply restrict_incr.
    rewrite restrict_sm_all in H1.
      eapply val_inject_incr; try eapply H1. apply restrict_incr.
  intros [m2' [C D]].
  exploit (eff_exec_straight_steps mu); try eassumption.
    intros. simpl in TR.
      exploit transl_store_correct_eff; eauto. (*rewrite <- RSP. eassumption. *)
      intros [rs2 [P Q]]. 
      exists rs2; split. eauto.
      split. eapply agree_undef_regs; eauto.  
      simpl; congruence.
  intros [st' [CS' MS']].
  exists st', m2'.
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ H0). intuition.
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ C). intuition. 
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ H0). intuition.
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ C). intuition. 
  destruct a; inv H0.
  inv B. simpl in C.
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
  split. split; intuition.
        eapply REACH_Store; try eassumption. 
          rewrite restrict_sm_all in H4.
            destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (agree_mregs _ _ _ _ AG src); intros AMR.
                   rewrite H0 in AMR; inv AMR.   
                   rewrite restrict_sm_all in H7. 
                   destruct (restrictD_Some _ _ _ _ _ H7); trivial.
  intros. rewrite restrict_sm_all in H4.
  specialize (StoreEffect_PropagateLeft chunk m (Vptr b i)); simpl. intros.
  assert (val_inject (restrict (as_inj mu) (vis mu)) (Vptr b i) (Vptr b2 (Int.add i (Int.repr delta)))).
    econstructor. eassumption. trivial.
  specialize (H2 _ _ H3 _ _ WD MEXT _ H5); simpl in H2.
  specialize (H2 _ _ C _ _ H0).
  split; try eassumption. 
  clear H2 H5. simpl in H0. destruct (eq_block b2 b0); simpl in *; inv H0.
  rewrite H5. eapply visPropagateR; eassumption. }

{ (* Mcall_internal *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  clear H0. rename H2 into CalleeF. 
  rename rs into ms; rename rs0 into rs.
  inv AT.
  clear H2.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H4.
+ (* Indirect Mcall internal*) 
  assert (ms rf = Vptr f' Int.zero).
    destruct (ms rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.
  exploit ireg_val; try eassumption.
  rewrite H2; intros VI; inv VI.
  rewrite Int.add_zero_l in *.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs x0)).
    specialize (agree_mregs _ _ _ _ AG rf); simpl. 
    apply ireg_of_eq in EQ1.
    rewrite H2, EQ1; trivial.
  destruct (GFP _ _ CalleeF) as [mapped_f' GlobalBlock_f'].
  rewrite restrict_sm_all in H7.
  destruct (restrictD_Some _ _ _ _ _ H7) as [ZZ vis_f']; clear H7.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  clear H.  
  generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  eexists; eexists; eexists. 
  split. left. apply effstep_plus_one. eapply asm_effexec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. eauto.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    assert (MSTK: match_stack ge (restrict_sm mu (vis mu))
            (Stackframe fb sp (Vptr fb (Int.add ofs Int.one)) c :: s)).
      econstructor. eassumption. eassumption.
        rewrite restrict_sm_zero_or_localid; trivial.
        right. exists fb, (Int.add ofs Int.one). split; trivial.
          right. eapply (GFP _ _ FIND).
        assumption.
   split. 
     eapply match_states_call_internal; try eassumption.
       simpl. eapply agree_exten; eauto. intros. Simplifs.
       Simplifs.
       Simplifs. rewrite <- H0; simpl.
         econstructor.
         rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
           unfold vis. rewrite (Glob _ fb_globalblock). intuition.
         rewrite Int.add_zero. trivial. 
     intuition.
   intuition. 

+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  eexists; eexists; eexists; split.
    left; apply effstep_plus_one. eapply asm_effexec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. eauto.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. 
    assert (MSTK: match_stack ge (restrict_sm mu (vis mu)) 
                 (Stackframe fb sp (Vptr fb (Int.add ofs Int.one)) c :: s)).
       econstructor. eassumption. eassumption.
       rewrite restrict_sm_zero_or_localid; trivial.
       right. exists fb, (Int.add ofs Int.one). split; trivial.
         right. eapply (GFP _ _ FIND).
       assumption.  
    split.
      eapply match_states_call_internal; try eassumption.
        simpl. eapply agree_exten; eauto. intros. Simplifs.
        Simplifs.
        simpl.
          rewrite Pregmap.gso; try discriminate.
          rewrite Pregmap.gss. rewrite <- H0. simpl.
          econstructor.
          rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
            unfold vis. rewrite (Glob _ fb_globalblock). intuition.
          rewrite Int.add_zero. trivial. 
      intuition.
    intuition. }

{ (* Mcall_external *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  clear H0. rename H2 into CalleeF. 
  rename rs into ms; rename rs0 into rs.
  inv AT.
  clear H2.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect Mcall external*) 
  assert (ms rf = Vptr f' Int.zero).
    destruct (ms rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.

  exploit ireg_val; try eassumption.
  rewrite H2; intros VI; inv VI.
  rewrite Int.add_zero_l in *.
  destruct (GFP _ _ CalleeF) as [mapped_f' GlobalBlock_f'].
  rewrite restrict_sm_all in H8.
  destruct (restrictD_Some _ _ _ _ _ H8) as [ZZ vis_f']; clear H8.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  destruct (functions_translated _ _ CalleeF) as [Tcallee [FFindCallee TransfCallee]].
  monadInv TransfCallee.
  exploit extcall_arguments_match.
    apply (restrict_sm_WD _ WD (vis mu)); trivial.
    instantiate (1:=(rs # RA <- (Val.add (Vptr fb ofs) Vone)) # PC <- (Vptr f' Int.zero)).
    eapply agree_exten; try eassumption.
       intros. Simplifs.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  eexists; eexists; eexists. 
  split. left. eapply effstep_plus_two.
         eapply asm_effexec_step_internal. rewrite <- H0. reflexivity.
           eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
           simpl. eauto.
         eapply asm_effexec_step_external. rewrite <- H7. Simplif.
           eassumption.
           rewrite <- H7, <- H0. eassumption.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    split. 
      eapply match_states_call_external; try eassumption.
        { econstructor. eassumption. eassumption.
          rewrite restrict_sm_zero_or_localid; trivial.
          right. exists fb, (Int.add ofs Int.one). split; trivial.
            right. eapply (GFP _ _ FIND).
          assumption. }
        simpl. eapply agree_exten; eauto. intros. Simplifs.
        rewrite <- H7. Simplifs.
        Simplifs. simpl. 
          rewrite Pregmap.gso; try discriminate.
          rewrite Pregmap.gss. rewrite <- H0. simpl.
          econstructor.
            rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
            unfold vis. rewrite (Glob _ fb_globalblock). intuition.
            rewrite Int.add_zero. trivial.
        rewrite <- H7, <- H0. assumption.  
     intuition.
  intuition.
+ (* Direct call *)
  simpl in H3. 
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  destruct (functions_translated _ _ CalleeF) as [Tcallee [FindTcallee TRANSCALLEE]].
  monadInv TRANSCALLEE.
  exploit extcall_arguments_match.
    apply (restrict_sm_WD _ WD (vis mu)); trivial.
    instantiate (1:=(rs # RA <- (Val.add (Vptr fb ofs) Vone)) # PC <- (Vptr f' Int.zero)).
    eapply agree_exten; try eassumption.
       intros. Simplifs.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  eexists; eexists; eexists; split.
    left; eapply effstep_plus_two.
      eapply asm_effexec_step_internal. rewrite <- H0; reflexivity. 
        eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. rewrite <- H0. unfold symbol_offset. rewrite symbols_preserved, H. reflexivity.
      eapply asm_effexec_step_external.
        Simplifs. 
        eassumption.
        eassumption.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. 
    assert (MSTK: match_stack ge (restrict_sm mu (vis mu)) 
                 (Stackframe fb sp (Vptr fb (Int.add ofs Int.one)) c :: s)).
       econstructor. eassumption. eassumption.
       rewrite restrict_sm_zero_or_localid; trivial.
       right. exists fb, (Int.add ofs Int.one). split; trivial.
         right. eapply (GFP _ _ FIND).
       assumption.  
    split.
      eapply match_states_call_external; try eassumption.
        simpl. eapply agree_exten; eauto. intros. Simplifs.
          Simplifs.
          Simplifs.
          simpl. rewrite Pregmap.gso; try discriminate.
            rewrite Pregmap.gss.
            econstructor.
            rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
              unfold vis. rewrite (Glob _ fb_globalblock). intuition.
          rewrite Int.add_zero. trivial.
      intuition.
    intuition. }

{ (* Mtailcall_internal *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  inv AT. clear H6 H0.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  unfold load_stack in *.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
      apply restrict_sm_WD; try eassumption. trivial.
  specialize (sp_as_inj _ _ _ _ AG WDR). intros SPAI; inv SPAI.
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H1. eexact H1.
    eassumption.
  intros [parent' [A B]].
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H2. eexact H2.
    eassumption.
  intros [ra' [C D]].
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tstk stk_local].
  assert (XX: b2 = tstk /\ delta =0). 
    apply local_in_all in stk_local; trivial.
    rewrite H11 in stk_local. inv stk_local. 
    split; trivial.
  destruct XX; subst. rewrite Int.add_zero, Zplus_0_r in *.
  clear H11.
  rename H10 into RSP.
(*
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  assert (parent' = parent_sp s).
    destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in B. inv B. rewrite H0; trivial.
    destruct H0 as [b [z [tb [PAR LOC]]]]. rewrite PAR in B.
       inv B. apply local_in_all in LOC; trivial.
       rewrite LOC in H11; inv H11.
       rewrite PAR, Int.add_zero; trivial. 
  subst parent'. clear B.
*)
(*
  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  assert (ra' = parent_ra s).
    destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in D. inv D. rewrite H0; trivial.
    destruct H0 as [b [z [RA [[tb LOC] | GLOB]]]].
      rewrite RA in D. inv D. apply local_in_all in LOC; trivial.
       rewrite LOC in H10; inv H10.
       rewrite RA, Int.add_zero; trivial.
      rewrite RA in D; inv D. rewrite restrict_sm_all in H10. 
       destruct (restrictD_Some _ _ _ _ _ H10); clear H10.
        rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG _ GLOB) in H0; inv H0.
        rewrite RA, Int.add_zero. trivial.
  subst ra'. clear D.
 *) 
  rewrite restrict_sm_local' in stk_local; trivial. 
  exploit free_parallel_inject; try eapply H3.
    eassumption. eapply local_in_all; eassumption.
    
  repeat rewrite Zplus_0_r. intros [m2' [E F]]. 
  destruct ros as [rf|fid]; simpl in H; monadInv H8.
+ (* Indirect Mtailcall_internal *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs0 x0)).
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H0.
    apply ireg_of_eq in EQ1. rewrite EQ1. trivial.
  destruct (GFP _ _ H4) as [mapped_f' GlobalBlock_f'].
  inv H. 
  rewrite restrict_sm_all in H11.
  destruct (restrictD_Some _ _ _ _ _ H11) as [ZZ vis_f']; clear H11.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  rewrite Int.add_zero in H10.
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  eexists; eexists; eexists; split.
    left; eapply effstep_plus_star_trans. 
      eapply effstep_plus_one. eapply asm_effexec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. rewrite <- RSP; simpl. rewrite C. rewrite A. rewrite E. eauto.
      apply effstep_star_one. eapply asm_effexec_step_internal. 
        transitivity (Val.add rs0#PC Vone). auto. rewrite <- H5. simpl. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split.
    split.
      { econstructor; eauto.
        apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
        (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
        eapply agree_change_sp. eassumption.
          eapply (parent_sp_zero_or_ptr _ _ _ STACKS).
          assumption.
          apply restrict_sm_WD; trivial.
        Simplifs. rewrite Pregmap.gso; auto. 
        generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence. }
      intuition.
      eapply REACH_closed_free; try eassumption.
      split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
  simpl. rewrite <- RSP; simpl. rewrite A, C, E.
     intros b z Hbz. rewrite orb_false_r in Hbz.
     apply FreeEffectD in Hbz; destruct Hbz as [? [VB Arith2]]; subst.
     destruct (local_DomRng _ WD _ _ _ stk_local) as [SPlocalDom SPlocalTgt].              
     split. eapply visPropagate. eassumption.
              2: eapply local_in_all; eassumption.
              unfold vis; rewrite SPlocalDom; trivial.
     rewrite SPlocalTgt. congruence. 
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  eexists; eexists; eexists; split.
    left. eapply effstep_plus_star_trans'.
             eapply effstep_plus_one. eapply asm_effexec_step_internal. eauto.
              eapply functions_transl; eauto. eapply find_instr_tail; eauto.    
              simpl. rewrite <- RSP; simpl. rewrite C. rewrite A. rewrite E. eauto.
    apply effstep_star_one. eapply asm_effexec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H5. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. eauto.
    reflexivity.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. 
    split.
      eapply match_states_call_internal; eauto.
      apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
      (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
       eapply agree_change_sp; try eassumption.
         apply (parent_sp_zero_or_ptr _ _ _ STACKS). 
       Simplif. unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto.
    intuition.
      eapply REACH_closed_free; try eassumption.
      split; intros. 
        eapply Mem.valid_block_free_1; try eassumption.
          eapply SMV; assumption.
        eapply Mem.valid_block_free_1; try eassumption.
          eapply SMV; assumption.
  simpl. rewrite <- RSP; simpl. rewrite A, C, E.
     intros b z Hbz. rewrite orb_false_r in Hbz.
     apply FreeEffectD in Hbz; destruct Hbz as [? [VB Arith2]]; subst.
     destruct (local_DomRng _ WD _ _ _ stk_local) as [SPlocalDom SPlocalTgt].              
     split. eapply visPropagate. eassumption.
              2: eapply local_in_all; eassumption.
              unfold vis; rewrite SPlocalDom; trivial.
     rewrite SPlocalTgt. congruence.  }

{ (* Mtailcall_external *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  inv AT. clear H7 H0.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  unfold load_stack in *.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
      apply restrict_sm_WD; try eassumption. trivial.
  specialize (sp_as_inj _ _ _ _ AG WDR). intros SPAI; inv SPAI.
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H1. eexact H1.
    eassumption.
  intros [parent' [A B]].
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H2. eexact H2.
    eassumption.
  intros [ra' [C D]].
  destruct (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _ )) as [tstk stk_local].
  rewrite (local_in_all _ WDR _ _ _ stk_local) in H12; inv H12.
  rename H11 into RSP; rename b2 into tstk. 
(*
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  assert (parent' = parent_sp s).
    destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in B. inv B. rewrite H0; trivial.
    destruct H0 as [b [z [PAR LOC]]]. rewrite PAR in B.
       inv B. apply local_in_all in LOC; trivial.
       rewrite LOC in H11; inv H11.
       rewrite PAR, Int.add_zero; trivial. 
  subst parent'.

  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  assert (ra' = parent_ra s).
    destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in D. inv D. rewrite H0; trivial.
    destruct H0 as [b [z [RA [LOC | GLOB]]]].
      rewrite RA in D. inv D. apply local_in_all in LOC; trivial.
       rewrite LOC in H11; inv H11.
       rewrite RA, Int.add_zero; trivial.
      rewrite RA in D; inv D. rewrite restrict_sm_all in H11. 
       destruct (restrictD_Some _ _ _ _ _ H11); clear H11.
        rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG _ GLOB) in H0; inv H0.
        rewrite RA, Int.add_zero. trivial.
       
  subst ra'.*)

  rewrite restrict_sm_local' in stk_local; trivial.
  exploit free_parallel_inject; eauto.
    eapply local_in_all; eassumption.
  repeat rewrite Zplus_0_r. intros [m2' [E F]].
  simpl in *. 
  destruct ros as [rf|fid]; simpl in H; monadInv H9.
+ (* Indirect Mtailcall_external *) 
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs0 x0)).
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H0.
    apply ireg_of_eq in EQ1. rewrite EQ1. trivial.
  destruct (GFP _ _ H4) as [mapped_f' GlobalBlock_f'].
  inv H. 
  rewrite restrict_sm_all in H12.
  destruct (restrictD_Some _ _ _ _ _ H12) as [ZZ vis_f']; clear H12.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  rewrite Int.add_zero in H11.
  generalize (code_tail_next_int _ _ _ _ NOOV H10). intro CT1.
  destruct (functions_translated _ _ H4) as [Tcallee [FFindCallee TransfCallee]].
  monadInv TransfCallee.
  assert (AG1: agree (restrict_sm mu (vis mu)) rs (parent_sp s)
            (nextinstr (rs0 # ESP <- parent') # RA <- ra') # PC <-
            (nextinstr (rs0 # ESP <- parent') # RA <- ra' x0)).
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
    eapply agree_change_sp; try eassumption.
       apply (parent_sp_zero_or_ptr _ _ _ STACKS). 
  exploit extcall_arguments_match.
    apply WDR.
    eapply AG1.
    2: eapply H5.
    rewrite restrict_sm_all. eapply inject_restrict. eassumption.
        eapply REACH_closed_free; eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  rewrite Zplus_0_r in *. rewrite Int.add_zero in *.
  eexists; eexists; eexists; split.
    left; eapply effstep_plus_trans. 
      eapply effstep_plus_one. eapply asm_effexec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. rewrite <- RSP. simpl.
         rewrite C. rewrite A. rewrite E. eauto.
      eapply effstep_plus_two. eapply asm_effexec_step_internal. 
        transitivity (Val.add rs0#PC Vone). auto. rewrite <- H6. simpl. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. eauto.
      eapply asm_effexec_step_external.
        unfold nextinstr. Simplif.
         rewrite Pregmap.gso.
         rewrite Pregmap.gso.
         rewrite Pregmap.gso. rewrite <- H11. reflexivity.
         generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence. 
         apply ireg_of_eq in EQ1. intros N.
           rewrite N in *. clear N. destruct rf; discriminate.
         apply ireg_of_eq in EQ1. intros N.
           rewrite N in *. clear N. destruct rf; discriminate.
         eassumption.
         eassumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. 
    split.
      eapply match_states_call_external; eauto.
        Simplifs. rewrite Pregmap.gso; auto. 
        generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
      intuition.
      eapply REACH_closed_free; try eassumption.
      split; intros. 
        eapply Mem.valid_block_free_1; try eassumption.
          eapply SMV; assumption.
        eapply Mem.valid_block_free_1; try eassumption.
          eapply SMV; assumption.
  simpl. rewrite <- RSP; simpl. rewrite A, C, E.
     intros b z Hbz. rewrite orb_false_r in Hbz.
     apply FreeEffectD in Hbz; destruct Hbz as [? [VB Arith2]]; subst.
     destruct (local_DomRng _ WD _ _ _ stk_local) as [SPlocalDom SPlocalTgt].              
     split. eapply visPropagate. eassumption.
              2: eapply local_in_all; eassumption.
              unfold vis; rewrite SPlocalDom; trivial.
     rewrite SPlocalTgt. congruence.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H10). intro CT1.
  destruct (functions_translated _ _ H4) as [Tcallee [TFindCaller TransCallee]].
  monadInv TransCallee.
  assert (AG1: agree (restrict_sm mu (vis mu)) rs (parent_sp s)
    (nextinstr (rs0 # ESP <- parent') # RA <- ra') # PC <-
    (symbol_offset tge fid Int.zero)).
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto.
      eapply (parent_sp_zero_or_ptr _ _ _ STACKS).
  exploit extcall_arguments_match.
    apply (restrict_sm_WD _ WD (vis mu)); trivial.
    apply AG1.
    rewrite restrict_sm_all; eapply inject_restrict; try eapply F; trivial.
    eapply REACH_closed_free; eassumption.
    eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  rewrite Zplus_0_r in *. rewrite Int.add_zero in *.
  eexists; eexists; eexists; split.
    left. eapply effstep_plus_trans'.
             eapply effstep_plus_one. eapply asm_effexec_step_internal. rewrite <- H6. eauto.
              eapply functions_transl; eauto. eapply find_instr_tail; eauto.    
              simpl. rewrite <- RSP; simpl. rewrite C. rewrite A. rewrite E. eauto.
    eapply effstep_plus_two. eapply asm_effexec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H6. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. eauto.
    eapply asm_effexec_step_external.
      unfold symbol_offset. rewrite symbols_preserved, H.
      Simplif.
      eassumption.
      eassumption.
    reflexivity.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. 
    split.
      eapply match_states_call_external; eauto.
        Simplif. 
        unfold symbol_offset. rewrite symbols_preserved, H. trivial.
    intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
  simpl. rewrite <- RSP; simpl. rewrite A, C, E.
     intros b z Hbz. rewrite orb_false_r in Hbz.
     apply FreeEffectD in Hbz; destruct Hbz as [? [VB Arith2]]; subst.
     destruct (local_DomRng _ WD _ _ _ stk_local) as [SPlocalDom SPlocalTgt].              
     split. eapply visPropagate. eassumption.
              2: eapply local_in_all; eassumption.
              unfold vis; rewrite SPlocalDom; trivial.
     rewrite SPlocalTgt. congruence. }

{ (* - builtin*) 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  inv H. inv AT. monadInv H3. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H2); intro NOOV.
  exploit (inlineable_extern_inject _ _ GDE_lemma).
        eassumption. eassumption. eassumption. eassumption. eassumption. assumption.
        rewrite <- restrict_sm_all. eapply decode_longs_inject.
        eapply preg_vals; eauto.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  eexists; eexists; eexists. 
  split. left. eapply effstep_plus_one.
           eapply asm_effexec_step_builtin. eauto. eauto.
            eapply find_instr_tail; eauto.
           econstructor. eassumption.
            reflexivity. reflexivity.
  exists mu'.
  split; trivial. 
  split; trivial. 
  split; trivial. 
  split.
    split. econstructor; eauto.
      eapply match_stack_intern_incr; try eassumption.
        eapply restrict_sm_intern_incr; eassumption. 
      instantiate (2 := tf); instantiate (1 := x).
      unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
      rewrite undef_regs_other. rewrite set_pregs_other_2. rewrite undef_regs_other_2.
      rewrite <- H. simpl. econstructor; eauto.
      eapply code_tail_next_int; eauto.
      rewrite preg_notin_charact. intros. auto with asmgen.
      rewrite preg_notin_charact. intros. auto with asmgen.
      auto with asmgen.
      simpl; intros. intuition congruence.
      apply agree_nextinstr_nf. eapply agree_set_mregs; auto.
      eapply agree_intern_incr.
         Focus 3. eapply restrict_sm_intern_incr; eassumption.
         apply restrict_sm_WD; trivial.
       eapply agree_undef_regs; eauto.
       intros; eapply undef_regs_other_2; eauto. 
      eapply encode_long_inject. rewrite restrict_sm_all; eassumption. 
      congruence.

      eapply zero_or_localid_intern_incr; eassumption.

    intuition. 
    eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
    red; intros bb fbb Hbb. destruct (GFP _ _ Hbb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.    
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. eapply (Glob _ H5).
  eapply BuiltinEffect_Propagate; try eassumption. 
    eapply decode_longs_inject. rewrite <- restrict_sm_all.
    eapply preg_vals; eassumption. }

(* - annot: later*)

{ (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  exists (State rs'), m2; eexists; split. left.
    apply effstep_plus_one. econstructor; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition. 
    econstructor; eauto.
      eapply agree_exten. eassumption.
       (*was:  eauto with asmgen.*) intros r Dr. eapply INV. intros Hr; subst. inv Dr.
      congruence.
  simpl. intuition.  }

{ (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  (*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit eval_condition_inject.
    eapply preg_vals; eauto.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eauto.
  intros EC.
  exploit eff_exec_straight_steps_goto; eauto.
    intros. simpl in TR.
    destruct (transl_cond_correct_eff tge tf cond args _ _ rs0 m2 TR)
    as [rs' [A [B C]]]. 
    rewrite EC in B.
    destruct (testcond_for_condition cond); simpl in *.
    (* simple jcc *)
      exists (Pjcc c1 lbl); exists k; exists rs'.
      split. eexact A.
      split. eapply agree_exten; eauto. 
      simpl. rewrite B. auto.
    (* jcc; jcc *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct b1.   
      (* first jcc jumps *)
      exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
      split. eexact A.
      split. eapply agree_exten; eauto. 
      simpl. rewrite TC1. auto.
      (* second jcc jumps *)
      exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
      split. eapply eff_exec_straight_trans. eexact A. 
      eapply eff_exec_straight_one. simpl. rewrite TC1. auto. auto.
      reflexivity.
      intuition.
      split. eapply agree_exten; eauto.
      intros; Simplifs.
      simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
      destruct b2; auto || discriminate.
    (* jcc2 *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct (andb_prop _ _ H3). subst. 
      exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
      split. eexact A.
      split. eapply agree_exten; eauto. 
      simpl. rewrite TC1; rewrite TC2; auto.
  intros [st' [CS' MS']].
  exists st', m2. 
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
  intuition. }

{ (* Mcond false *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit eval_condition_inject.
    eapply preg_vals; eauto.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eauto.
  intros EC. 
  exploit eff_exec_straight_steps; try eassumption. instantiate (3:=EmptyEffect).
    intros. simpl in TR.
    destruct (transl_cond_correct_eff tge tf cond args _ _ rs0 m2 TR)
    as [rs' [A [B C]]]. 
    rewrite EC in B.
    destruct (testcond_for_condition cond); simpl in *.
    (* simple jcc *)
      econstructor; split.
      eapply eff_exec_straight_trans. eexact A. 
      apply eff_exec_straight_one. simpl. rewrite B. eauto. auto. 
      reflexivity. simpl; intuition.
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      simpl; congruence.
    (* jcc ; jcc *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct (orb_false_elim _ _ H1); subst.
      econstructor; split.
      eapply eff_exec_straight_trans. eexact A. 
      eapply eff_exec_straight_two. simpl. rewrite TC1. eauto. auto. 
      simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
      reflexivity. simpl; intuition.
      split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
      simpl; congruence.
    (* jcc2 *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      exists (nextinstr rs'); split.
      eapply eff_exec_straight_trans. eexact A. 
      apply eff_exec_straight_one. simpl. 
      rewrite TC1; rewrite TC2. 
      destruct b1. simpl in *. subst b2. auto. auto.
      auto.
      reflexivity. simpl; intuition.
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      rewrite H1; congruence.
  intros [st' [CS' MS']].
  exists st', m2.
  eexists; split. left; eassumption.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
  intuition. }

{ (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  eexists; eexists; eexists; split. left.
    apply effstep_plus_one. econstructor; eauto.  
    eapply find_instr_tail; eauto. 
    simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eauto.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. split; intuition.
           econstructor; eauto. 
Transparent destroyed_by_jumptable.   
      simpl. eapply agree_exten; eauto.
      (*WAS: intros. rewrite C; auto with asmgen.*)
        intros r Dr. apply C. intros; subst. inv Dr.
      congruence.
  intuition. }

{ (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tstk LocSTK].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSTK in H11; apply eq_sym in H11. inv H11.
  rename H10 into RSP; rewrite Int.add_zero in RSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *. inv SP.*)
  unfold load_stack in *.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
     eapply (restrict_sm_WD _ WD ); trivial. 
  assert (AiSTK: as_inj mu stk = Some (tstk, 0)).
      rewrite restrict_sm_local' in LocSTK; trivial.
        apply local_in_all in LocSTK; eassumption.    
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0.
    simpl. econstructor.
      apply local_in_all in LocSTK; eassumption.
    rewrite Int.add_zero. reflexivity.
  intros [parent' [A B]]. 
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H1.
    simpl. econstructor.
      apply local_in_all in LocSTK; eassumption.
    rewrite Int.add_zero. reflexivity.
  intros [ra' [C D]]. 
  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  exploit free_parallel_inject; eauto.
  simpl. rewrite Zplus_0_r. intros [m2' [E F]].
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.
  eexists; eexists; eexists; split. left.
    eapply effstep_plus_star_trans.
      eapply effstep_plus_one. eapply asm_effexec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. rewrite <- RSP. simpl. simpl in C. rewrite C. 
          simpl in A. rewrite A. (* rewrite <- (sp_val _ _ _ AG).*)
          rewrite E. eauto.
    apply effstep_star_one. eapply asm_effexec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H3. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. eauto. 
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split.
    split.
      constructor; eauto. 
        apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
          eapply agree_change_sp; eauto. 
            eapply (parent_sp_zero_or_ptr _ _ _ STACKS). 
     intuition.
     eapply REACH_closed_free; try eassumption.
     split; intros. 
       eapply Mem.valid_block_free_1; try eassumption.
         eapply SMV; assumption.
       eapply Mem.valid_block_free_1; try eassumption.
         eapply SMV; assumption.
  simpl. intros. rewrite orb_false_r, <- RSP in H6.
    simpl in H6. simpl in *. rewrite C, A, E in H6.
    destruct (FreeEffectD _ _ _ _ _ _ H6) as [? [VB OFS]]; subst.
    rewrite restrict_sm_local in LocSTK.
    destruct (restrictD_Some _ _ _ _ _ LocSTK).
    apply local_in_all in H8; trivial.
    split. eapply visPropagate; eassumption.
    eapply FreeEffect_PropagateLeft; eassumption. }

{ (*internal function *)
  rewrite INT in H. inv H.
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'. rewrite transl_code'_transl_code in EQ0.
  destruct (zlt (list_length_z x0) Int.max_unsigned); inversion EQ1. clear EQ1.
  unfold store_stack in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
     eapply (restrict_sm_WD _ WD ); trivial. 
  exploit alloc_parallel_intern; try eassumption. apply Z.le_refl. apply Z.le_refl.
  intros [mu' [tm1 [tstk [TAlloc [INJ1 [INC [STK [Mu'Mu [SEP [LOCALLOC [WD' [WMV' RC1]]]]]]]]]]]]. 
  assert (stk_local: local_of (restrict_sm mu' (vis mu')) stk = Some (tstk, 0)).
    rewrite restrict_sm_local'; trivial.
    destruct (joinD_Some _ _ _ _ _ STK) as [EXT | [_ LOC]]; trivial.
    assert (EXT': extern_of mu = extern_of mu') by eapply INC.
    rewrite <- EXT' in EXT; clear EXT'.
    apply extern_in_all in EXT; trivial. 
    destruct (as_inj_DomRng _ _ _ _ EXT WD).
    elim (Mem.fresh_block_alloc _ _ _ _ _ H0).
    eapply SMV. apply H.
  exploit Mem.store_mapped_inject; try eapply INJ1. eapply H1. eassumption.
    eapply val_inject_incr.
      eapply (intern_incr_as_inj _ _ INC WD').
    eapply val_inject_incr.
       2: apply (sp_as_inj _ _ _ _ AG WDR).
    rewrite restrict_sm_all. apply restrict_incr. 
  rewrite Zplus_0_r, Int.add_zero_l. intros [tm0 [ST1 INJ0]].
  exploit Mem.store_mapped_inject; try eapply INJ0. eapply H2. eassumption.
    instantiate (1:=rs0 RA). 
    eapply val_inject_incr.
      eapply (intern_incr_as_inj _ _ INC WD').
    eapply val_inject_incr; try eassumption.
      rewrite restrict_sm_all. apply restrict_incr. 
  rewrite Zplus_0_r, Int.add_zero_l. intros [tm3 [ST2 INJ3]].
  eexists; eexists; eexists; split.
    left. apply effstep_plus_one. econstructor; eauto. 
     subst x; simpl.
     rewrite Int.unsigned_zero. simpl. eauto.
     simpl. rewrite TAlloc . simpl in ST1.
      rewrite Int.add_zero_l.
      destruct AG as [AG1 AG2]. rewrite ST1.
      rewrite Int.add_zero_l.
      simpl in ST2. rewrite ST2.
      eauto.
  exists mu'.
  split; trivial.
  split; trivial.
  split. rewrite sm_locally_allocatedChar.
    rewrite sm_locally_allocatedChar in LOCALLOC.
    assert (freshloc m m3 = freshloc m m1).
      extensionality b. rewrite <- (freshloc_trans m m1).
      rewrite <- (freshloc_trans m1 m0 m3).
      rewrite (storev_freshloc _ _ _ _ _ H1).
      rewrite (storev_freshloc _ _ _ _ _ H2). intuition.
      eapply store_forward; eapply H1.
      eapply store_forward; eapply H2.
      eapply alloc_forward; eassumption.
      eapply mem_forward_trans. 
      eapply store_forward; eapply H1.
      eapply store_forward; eapply H2.
    rewrite H.
    assert (freshloc m2 tm3 = freshloc m2 tm1).
      extensionality b. rewrite <- (freshloc_trans m2 tm1).
      rewrite <- (freshloc_trans tm1 tm0 tm3).
      rewrite (store_freshloc _ _ _ _ _ _ ST1).
      rewrite (store_freshloc _ _ _ _ _ _ ST2). intuition.
      eapply store_forward; eapply ST1.
      eapply store_forward; eapply ST2.
      eapply alloc_forward; eassumption.
      eapply mem_forward_trans. 
      eapply store_forward; eapply ST1.
      eapply store_forward; eapply ST2.
    rewrite H4.
    assumption.
  split.
    split. econstructor; eauto.
      eapply match_stack_intern_incr; try eassumption.
        apply restrict_sm_intern_incr; trivial.
      unfold nextinstr. rewrite Pregmap.gss.
        repeat rewrite Pregmap.gso; auto with asmgen. 
      rewrite ATPC. simpl. constructor; eauto.
        subst x. unfold fn_code. eapply code_tail_next_int. rewrite list_length_z_cons. omega. 
      constructor.
     { (*agree *) subst sp.
       apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
       apply agree_undef_regs with rs0; eauto.
         eapply agree_intern_incr; try eassumption.
         apply restrict_sm_WD; trivial. 
       apply restrict_sm_intern_incr; try eassumption; trivial.
       simpl; intros. apply Pregmap.gso; auto with asmgen. tauto. 
       right. exists stk, Int.zero, tstk; split; trivial.
       econstructor. eapply local_in_all; try eassumption.
        apply restrict_sm_WD; trivial. 
        rewrite Int.add_zero. trivial.
        apply restrict_sm_WD; trivial. }     
     intros. unfold nextinstr. simpl.
       rewrite Pregmap.gso. rewrite Pregmap.gso. rewrite Pregmap.gss.
       eapply val_inject_incr.
         2: apply (sp_as_inj _ _ _ _ AG WDR).
         rewrite restrict_sm_all. rewrite restrict_sm_all. apply intern_incr_restrict; trivial.
       congruence. congruence.
     subst sp. right. exists stk, Int.zero, tstk. split; trivial. 
       rewrite restrict_sm_local' in stk_local; trivial. 
     assert (stkVIS: vis mu' stk = true).
       unfold vis. rewrite restrict_sm_local' in stk_local; trivial.
        destruct (local_DomRng _ WD' _ _ _ stk_local) as [DS DT].
        rewrite DS; trivial. 
     assert (parentra_VIS: forall b' (Hb' : getBlocks (parent_ra s :: nil) b' = true), vis mu' b' = true).
       intros. apply getBlocks_char in Hb'.
       destruct Hb'. destruct H; try contradiction.
       destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
       rewrite H in H4; discriminate.
       eapply (intern_incr_vis _ _ INC). unfold vis.
       destruct H4 as [bb [z [PAR [[tb LOC] | GL]]]]; rewrite PAR in H; inv H.
       rewrite restrict_sm_local' in LOC; trivial.
       destruct (local_DomRng _ WD _ _ _ LOC). intuition.
       intuition.
    intuition.
    eapply REACH_Store. eapply H2. eassumption. eassumption.
    eapply REACH_Store. eapply H1. eassumption. 
    intros. eapply (intern_incr_vis _ _ INC). unfold vis. 
     destruct (parent_sp_zero_or_ptr _ _ _ STACKS). rewrite H5 in H4. unfold getBlocks in H4; simpl in H4. discriminate.
     destruct H5 as [bb [z [tbb [PARSP LOC]]]]. rewrite PARSP in H4.
     apply getBlocks_char in H4. destruct H4. destruct H4; try contradiction. inv H4.
     rewrite restrict_sm_local' in LOC; trivial.
       destruct (local_DomRng _ WD _ _ _ LOC). intuition.
    assumption.
    eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
    red; intros bb fbb Hbb. destruct (GFP _ _ Hbb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
          rewrite <- FRG. eapply (Glob _ H4).
    apply sm_locally_allocatedChar in LOCALLOC. 
      rewrite (freshloc_alloc _ _ _ _ _ H0) in LOCALLOC.
      rewrite (freshloc_alloc _ _ _ _ _ TAlloc) in LOCALLOC.
      destruct LOCALLOC as [DS [DT _]].
      split; intros.
        unfold DOM in H4. rewrite DS in H4.
          eapply Mem.store_valid_block_1; try eapply H2.
          eapply Mem.store_valid_block_1; try eapply H1.
          destruct (eq_block b1 stk); subst; simpl in *.
            apply (Mem.valid_new_block _ _ _ _ _ H0).
            apply (Mem.valid_block_alloc _ _ _ _ _ H0).
              eapply SMV. rewrite orb_false_r in H4; trivial.
        unfold RNG in H4. rewrite DT in H4.
          eapply Mem.store_valid_block_1; try eapply ST2.
          eapply Mem.store_valid_block_1; try eapply ST1.
          destruct (eq_block b2 tstk); subst; simpl in *.
            apply (Mem.valid_new_block _ _ _ _ _ TAlloc).
            apply (Mem.valid_block_alloc _ _ _ _ _ TAlloc).
              eapply SMV. rewrite orb_false_r in H4; trivial.
  simpl. intuition. }

(*external function: no case*) 

{ (* return *)
  inv STACKS. simpl in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  eexists; eexists; eexists; split.
    right. split. omega. eapply effstep_star_zero.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. 2: intuition.
  split; intuition.  
  destruct (GFP _ _ H4).
  econstructor; eauto.
    { inv H5. inv ATPC.
      rewrite restrict_sm_all in H12.
      destruct (restrictD_Some _ _ _ _ _ H12); clear H12. 
      rewrite H5 in H; inv H.
      rewrite Int.add_zero.
      econstructor; eassumption. }
    congruence.
    rewrite restrict_sm_zero_or_localid in H6; trivial. } 
Qed.

Lemma MATCH_core_diagram: forall st1 m1 st1' m1' 
        (CS: corestep (Mach_eff_sem return_address_offset) ge st1 m1 st1' m1')
        st2 mu m2 (MTCH: MATCH st1 mu st1 m1 st2 m2)
        (LNR: list_norepet (prog_defs_names prog)),
     exists st2' m2', 
       (corestep_plus Asm_eff_sem tge st2 m2 st2' m2' \/
         (measure st1' < measure st1)%nat /\
          corestep_star Asm_eff_sem tge st2 m2 st2' m2') /\
     exists mu',
       intern_incr mu mu' /\
       sm_inject_separated mu mu' m1 m2 /\
       sm_locally_allocated mu mu' m1 m2 m1' m2' /\
       MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros.
destruct MTCH as [MS PRE].
destruct CS; intros.
{ (* Mlabel *)
  inv MS.
  exploit exec_straight_steps; try eassumption.
  intros. monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
    split. apply agree_nextinstr; auto. eassumption. simpl; congruence.
  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. }

{ (* Mgetstack *)
  inv MS.
  destruct PRE as [RC [PG [GF [Glob [SMV WD]]]]].
  unfold load_stack in H. 
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tb LocSP].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSP in H3; apply eq_sym in H3; inv H3.
  rename H2 into RSP. rewrite Int.add_zero in RSP.
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst.*)
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu))));
    try eassumption.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    rewrite restrict_sm_local in LocSP.
      destruct (restrictD_Some _ _ _ _ _ LocSP).
      apply local_in_all in H0; trivial.
      rewrite restrict_sm_all. eapply restrictI_Some; eassumption.
  rewrite Zplus_0_r.
  intros [v' [A B]].
  exploit (exec_straight_steps mu); try eassumption. 
    intros. simpl in TR.
    exploit loadind_correct. eassumption. 
       instantiate (2:=rs0). rewrite <- RSP; simpl. eassumption.
  intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. 
    eapply agree_set_mreg. eassumption.
    instantiate (1:=dst). instantiate (1:=v). rewrite Q. assumption.
    assumption.
    simpl. congruence.
  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. }

{ (* Msetstack *)
  inv MS.
  unfold store_stack in H.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tb LocSP].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSP in H3; apply eq_sym in H3; inv H3.
  rename H2 into RSP. rewrite Int.add_zero in RSP.
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst.  simpl in H.*)
  exploit (Mem.store_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_local in LocSP.
      destruct (restrictD_Some _ _ _ _ _ LocSP).
      apply local_in_all in H0; trivial.
      eassumption.
    eapply val_inject_incr; try eapply AG. 
        rewrite restrict_sm_all. apply restrict_incr. 
  simpl. rewrite Zplus_0_r. intros [m2' [A B]].
  exploit (exec_straight_steps mu). eassumption. apply B. eassumption. eassumption.
    intros. simpl in TR.
    exploit storeind_correct. eassumption. 
     instantiate (2:=rs0). rewrite <- RSP. simpl. apply A.
  intros [rs' [P Q]].
  eexists; split. eassumption.
    split. eapply agree_undef_regs; eauto. 
    simpl; intros. rewrite Q; auto with asmgen. 
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.
  assumption. 
  intros [st' [CS' MS']].
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
  exists st', m2'. intuition.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ A). intuition. 
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ A). intuition. 
  split; intuition.
        eapply REACH_Store; try eassumption. 
          rewrite restrict_sm_local in LocSP.
            destruct (restrictD_Some _ _ _ _ _ LocSP); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (agree_mregs _ _ _ _ AG src); intros AMR.
                   rewrite H0 in AMR; inv AMR.   
                   rewrite restrict_sm_all in H4. 
                   destruct (restrictD_Some _ _ _ _ _ H4); trivial. }

{ (* Mgetparam *)
  inv MS.
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *. 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H0. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H0.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tb LocSP].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSP in H5; apply eq_sym in H5; inv H5.
  rename H4 into RSP. rewrite Int.add_zero in RSP.
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0. 
    rewrite restrict_sm_local in LocSP.
      destruct (restrictD_Some _ _ _ _ _ LocSP).
      apply local_in_all in H2; trivial.
      rewrite restrict_sm_all. eapply restrictI_Some; eassumption.
  rewrite Zplus_0_r.
  intros [parent' [A B]]. simpl in *.
  remember (parent_sp s) as u.
     destruct u; simpl in *; try inv H1.
  inv B.
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H3.
    eassumption.
  intros [v' [C D]].
Opaque loadind.
  exploit (exec_straight_steps mu); try eassumption.
    intros. instantiate (2:=m2). (*instantiate (1 := (Vptr spb z)).*)
      instantiate(1 := (@Regmap.set val dst v
                      (@Regmap.set val temp_for_parent_frame Vundef rs))).
    assert (DIFF: negb (mreg_eq dst DX) = true -> IR EDX <> preg_of dst).
      intros. change (IR EDX) with (preg_of DX). red; intros. 
      unfold proj_sumbool in H1. destruct (mreg_eq dst DX); try discriminate.
      elim n. eapply preg_of_injective; eauto.
    assert (Int.unsigned (Int.add (Int.add i (Int.repr delta)) ofs)
              = Int.unsigned (Int.add i ofs) + delta).
        rewrite Int.add_assoc. rewrite (Int.add_commut (Int.repr delta)).
        rewrite <- Int.add_assoc. 
        eapply Mem.address_inject; try eassumption. 
        eapply Mem.load_valid_access. eapply H3.
          split. omega. specialize (size_chunk_pos (chunk_of_type ty)); intros. omega.
        rewrite restrict_sm_all in H4. eapply restrictD_Some. eassumption.
    rewrite <- H1 in C. clear H1.
    destruct ep; simpl in TR.
    (* EDX contains parent *)
      assert (VI: val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr b i) (rs0 EDX)).
        eauto. 
      clear DXP. inv VI. rewrite H4 in H6. inv H6.
      exploit loadind_correct. eexact TR.
        instantiate (2 := rs0). rewrite <- H5. simpl. apply C. 
      intros [rs1 [P [Q R]]].
      exists rs1; split. eauto. 
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
      simpl; intros. rewrite R, <- Hequ, <- H5. econstructor. eassumption. trivial.
      auto. auto.
    (* EDX does not contain parent *)
      monadInv TR.
      exploit loadind_correct. eexact EQ0.
      instantiate (2:=rs0). rewrite <- RSP. simpl. eauto.
      intros [rs1 [P [Q R]]]. simpl in Q.
      exploit loadind_correct. eexact EQ.
        instantiate (2 := rs1). rewrite Q. simpl. eauto.
      intros [rs2 [S [T U]]]. 
      exists rs2; split. eapply exec_straight_trans; eauto.
      split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
      simpl; intros. rewrite U, <- Hequ, Q. econstructor. eassumption. trivial. 
      auto. auto.

  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. }

{ (* Mop *)
  inv MS.
  assert (eval_operation tge sp op rs##args m = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  specialize (agree_sp_local _ _ _ _ AG); intros LocSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit (preg_vals (restrict_sm mu (vis mu))). eassumption.
  intros ArgsInj.
  exploit eval_operation_inject''; try eapply H0; try eapply ArgsInj.
    eapply val_inject_incr; try eassumption.
        rewrite restrict_sm_local, restrict_sm_all.
        red; intros. destruct (restrictD_Some _ _ _ _ _ H1). 
             apply local_in_all in H2; trivial.
             eapply restrictI_Some; eassumption.  
    eapply restrict_sm_preserves_globals; try eassumption. 
      apply meminj_preserves_genv2blocks.
        apply meminj_preserves_genv2blocks in PG.
        eapply genvs_domain_eq_preserves; try eassumption.
        apply genvs_domain_eq_sym. apply GDE_lemma.
      unfold vis. intuition. rewrite Glob. intuition.
      rewrite (genvs_domain_eq_isGlobal _ _ GDE_lemma); trivial.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
  intros [v' [A B]].
(*  specialize (sp_val _ _ _ _ AG); intros RSP.*)
  (*rewrite eval_shift_stack_operation in A. simpl in A. rewrite Int.add_zero in A.*)
  exploit (exec_straight_steps mu); try eassumption. 
    intros. simpl in TR.
    exploit transl_op_correct; eauto. 
     (* instantiate (3:=rs0). rewrite RSP. apply A.*)
    intros [rs2 [P [Q R]]]. 
    assert (S: val_inject (as_inj (restrict_sm mu (vis mu))) v (rs2 (preg_of res))).
      eapply valinject_lessdef; try eassumption.
    exists rs2; split. eauto.
    split. eapply agree_set_undef_mreg; eassumption.
    simpl; congruence.
  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. }

{ (* Mload *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
(*  assert (SPptr: exists b z, a = Vptr b z).
     destruct a; inv H0. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.*)
(*  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.

  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.
*)
  exploit agree_eval_addressing_inject; try eassumption.
  intros [a' [A B]].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP. 
  (*specialize (sp_val _ _ _ _ AG); intros RSP.*)
  assert (eval_addressing tge (rs0 ESP) addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A. (* rewrite <- RSP. *) (*rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
    apply eval_addressing_preserved. exact symbols_preserved.
  clear A; rename H1 into A.
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0. 
    apply B. 
  intros [v' [C D]].
  exploit (exec_straight_steps mu). eassumption. eassumption. eassumption.
    eassumption. 
    intros. simpl in TR.
    exploit transl_load_correct; eauto.
      (*instantiate (2:=rs0). rewrite <- RSP. eapply A.*)
    intros [rs2 [P [Q R]]]. 
    exists rs2; split. eauto.
    split. eapply agree_set_undef_mreg. eassumption.
           instantiate (1:=dst). rewrite Q. eassumption. eauto.
    simpl; intros. congruence.
    assumption. (*right. exists spb, z; split; trivial.*)
  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. eassumption. }

{ (* Mstore *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit agree_eval_addressing_inject; try eassumption.
  intros [a' [A B]].
(*  exploit eval_addressing_inject'.
    eapply restrict_sm_preserves_globals with (X:=vis mu). eassumption.
      unfold vis; intuition.
    eapply local_in_all; try eassumption.
      apply restrict_sm_WD. assumption. trivial.
    eapply preg_vals; eassumption.
    eassumption. 
  intros [a' [A B]].*)
  specialize (agree_sp_local _ _ _ _ AG); intros RSP. 
(*  specialize (sp_val _ _ _ _ AG); intros RSP.*)
  assert (eval_addressing tge (rs0 ESP) addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A. (*rewrite <- RSP. rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
    apply eval_addressing_preserved. exact symbols_preserved.
  clear A; rename H1 into A.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (rs src) (rs0 (preg_of src))).
      eapply preg_val; eassumption.
  exploit (Mem.storev_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_all in B.
      eapply val_inject_incr; try eapply B. apply restrict_incr.
    rewrite restrict_sm_all in H1.
      eapply val_inject_incr; try eapply H1. apply restrict_incr.
  intros [m2' [C D]].
  exploit (exec_straight_steps mu); try eassumption.
    intros. simpl in TR.
      exploit transl_store_correct; eauto. (*rewrite <- RSP. eassumption. *)
      intros [rs2 [P Q]]. 
      exists rs2; split. eauto.
      split. eapply agree_undef_regs; eauto.  
      simpl; congruence.
  intros [st' [CS' MS']].
  exists st', m2'. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ H0). intuition.
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ C). intuition. 
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ H0). intuition.
      apply extensionality; intros; rewrite (storev_freshloc _ _ _ _ _ C). intuition. 
  destruct a; inv H0.
  inv B. simpl in C.
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
  split; intuition.
        eapply REACH_Store; try eassumption. 
          rewrite restrict_sm_all in H4.
            destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (agree_mregs _ _ _ _ AG src); intros AMR.
                   rewrite H0 in AMR; inv AMR.   
                   rewrite restrict_sm_all in H7. 
                   destruct (restrictD_Some _ _ _ _ _ H7); trivial. }

{ (* Mcall_internal *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  clear H0. rename H2 into CalleeF. 
  rename rs into ms; rename rs0 into rs.
  inv AT.
  clear H2.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H4.
+ (* Indirect Mcall internal*) 
  assert (ms rf = Vptr f' Int.zero).
    destruct (ms rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.
  exploit ireg_val; try eassumption.
  rewrite H2; intros VI; inv VI.
  rewrite Int.add_zero_l in *.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs x0)).
    specialize (agree_mregs _ _ _ _ AG rf); simpl. 
    apply ireg_of_eq in EQ1.
    rewrite H2, EQ1; trivial.
  destruct (GFP _ _ CalleeF) as [mapped_f' GlobalBlock_f'].
  rewrite restrict_sm_all in H7.
  destruct (restrictD_Some _ _ _ _ _ H7) as [ZZ vis_f']; clear H7.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  clear H.  
  generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  eexists; eexists. 
  split. left. apply corestep_plus_one. eapply asm_exec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. eauto.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    assert (MSTK: match_stack ge (restrict_sm mu (vis mu))
            (Stackframe fb sp (Vptr fb (Int.add ofs Int.one)) c :: s)).
      econstructor. eassumption. eassumption.
        rewrite restrict_sm_zero_or_localid; trivial.
        right. exists fb, (Int.add ofs Int.one). split; trivial.
          right. eapply (GFP _ _ FIND).
        assumption.
   eapply match_states_call_internal; try eassumption.
    simpl. eapply agree_exten; eauto. intros. Simplifs.
    Simplifs.
    Simplifs. rewrite <- H0; simpl.
      econstructor.
      rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
        unfold vis. rewrite (Glob _ fb_globalblock). intuition.
      rewrite Int.add_zero. trivial. 
 intuition.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  eexists; eexists; split.
    left; apply corestep_plus_one. eapply asm_exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. eauto.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. 
    assert (MSTK: match_stack ge (restrict_sm mu (vis mu)) 
                 (Stackframe fb sp (Vptr fb (Int.add ofs Int.one)) c :: s)).
       econstructor. eassumption. eassumption.
       rewrite restrict_sm_zero_or_localid; trivial.
       right. exists fb, (Int.add ofs Int.one). split; trivial.
         right. eapply (GFP _ _ FIND).
       assumption.  
    eapply match_states_call_internal; try eassumption.
      simpl. eapply agree_exten; eauto. intros. Simplifs.
      Simplifs.
      simpl.
        rewrite Pregmap.gso; try discriminate.
        rewrite Pregmap.gss. rewrite <- H0. simpl.
        econstructor.
        rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
          unfold vis. rewrite (Glob _ fb_globalblock). intuition.
        rewrite Int.add_zero. trivial. 
  intuition. }

{ (* Mcall_external *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  clear H0. rename H2 into CalleeF. 
  rename rs into ms; rename rs0 into rs.
  inv AT.
  clear H2.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect Mcall external*) 
  assert (ms rf = Vptr f' Int.zero).
    destruct (ms rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.

  exploit ireg_val; try eassumption.
  rewrite H2; intros VI; inv VI.
  rewrite Int.add_zero_l in *.
  destruct (GFP _ _ CalleeF) as [mapped_f' GlobalBlock_f'].
  rewrite restrict_sm_all in H8.
  destruct (restrictD_Some _ _ _ _ _ H8) as [ZZ vis_f']; clear H8.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  destruct (functions_translated _ _ CalleeF) as [Tcallee [FFindCallee TransfCallee]].
  monadInv TransfCallee.
  exploit extcall_arguments_match.
    apply (restrict_sm_WD _ WD (vis mu)); trivial.
    instantiate (1:=(rs # RA <- (Val.add (Vptr fb ofs) Vone)) # PC <- (Vptr f' Int.zero)).
    eapply agree_exten; try eassumption.
       intros. Simplifs.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  eexists; eexists. 
  split. left. eapply corestep_plus_two.
         eapply asm_exec_step_internal. rewrite <- H0. reflexivity.
           eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
           simpl. eauto.
         eapply asm_exec_step_external. rewrite <- H7. Simplif.
           eassumption.
           rewrite <- H7, <- H0. eassumption.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    eapply match_states_call_external; try eassumption.
    { econstructor. eassumption. eassumption.
       rewrite restrict_sm_zero_or_localid; trivial.
       right. exists fb, (Int.add ofs Int.one). split; trivial.
         right. eapply (GFP _ _ FIND).
       assumption. }
    simpl. eapply agree_exten; eauto. intros. Simplifs.
    rewrite <- H7. Simplifs.
    Simplifs. simpl. 
        rewrite Pregmap.gso; try discriminate.
        rewrite Pregmap.gss. rewrite <- H0. simpl.
        econstructor.
        rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
          unfold vis. rewrite (Glob _ fb_globalblock). intuition.
        rewrite Int.add_zero. trivial.
    rewrite <- H7, <- H0. assumption. 
 intuition. 
+ (* Direct call *)
  simpl in H3. 
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  destruct (functions_translated _ _ CalleeF) as [Tcallee [FindTcallee TRANSCALLEE]].
  monadInv TRANSCALLEE.
  exploit extcall_arguments_match.
    apply (restrict_sm_WD _ WD (vis mu)); trivial.
    instantiate (1:=(rs # RA <- (Val.add (Vptr fb ofs) Vone)) # PC <- (Vptr f' Int.zero)).
    eapply agree_exten; try eassumption.
       intros. Simplifs.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  eexists; eexists; split.
    left; eapply corestep_plus_two.
      eapply asm_exec_step_internal. rewrite <- H0; reflexivity. 
        eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. rewrite <- H0. unfold symbol_offset. rewrite symbols_preserved, H. reflexivity.
      eapply asm_exec_step_external.
        Simplifs. 
        eassumption.
        eassumption.
  destruct (GFP _ _ FIND) as [fb_mapped fb_globalblock].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split. 
    assert (MSTK: match_stack ge (restrict_sm mu (vis mu)) 
                 (Stackframe fb sp (Vptr fb (Int.add ofs Int.one)) c :: s)).
       econstructor. eassumption. eassumption.
       rewrite restrict_sm_zero_or_localid; trivial.
       right. exists fb, (Int.add ofs Int.one). split; trivial.
         right. eapply (GFP _ _ FIND).
       assumption.  
    eapply match_states_call_external; try eassumption.
      simpl. eapply agree_exten; eauto. intros. Simplifs.
        Simplifs.
        Simplifs.
        simpl. rewrite Pregmap.gso; try discriminate.
          rewrite Pregmap.gss.
          econstructor.
          rewrite restrict_sm_all; eapply restrictI_Some. eassumption.
            unfold vis. rewrite (Glob _ fb_globalblock). intuition.
        rewrite Int.add_zero. trivial.
  intuition. }

{ (* Mtailcall_internal *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  inv AT. clear H6 H0.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  unfold load_stack in *.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
      apply restrict_sm_WD; try eassumption. trivial.
  specialize (sp_as_inj _ _ _ _ AG WDR). intros SPAI; inv SPAI.
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H1. eexact H1.
    eassumption.
  intros [parent' [A B]].
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H2. eexact H2.
    eassumption.
  intros [ra' [C D]].
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tstk stk_local].
  assert (XX: b2 = tstk /\ delta =0). 
    apply local_in_all in stk_local; trivial.
    rewrite H11 in stk_local. inv stk_local. 
    split; trivial.
  destruct XX; subst. rewrite Int.add_zero, Zplus_0_r in *.
  clear H11.
  rename H10 into RSP.
(*
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  assert (parent' = parent_sp s).
    destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in B. inv B. rewrite H0; trivial.
    destruct H0 as [b [z [tb [PAR LOC]]]]. rewrite PAR in B.
       inv B. apply local_in_all in LOC; trivial.
       rewrite LOC in H11; inv H11.
       rewrite PAR, Int.add_zero; trivial. 
  subst parent'. clear B.
*)
(*
  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  assert (ra' = parent_ra s).
    destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in D. inv D. rewrite H0; trivial.
    destruct H0 as [b [z [RA [[tb LOC] | GLOB]]]].
      rewrite RA in D. inv D. apply local_in_all in LOC; trivial.
       rewrite LOC in H10; inv H10.
       rewrite RA, Int.add_zero; trivial.
      rewrite RA in D; inv D. rewrite restrict_sm_all in H10. 
       destruct (restrictD_Some _ _ _ _ _ H10); clear H10.
        rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG _ GLOB) in H0; inv H0.
        rewrite RA, Int.add_zero. trivial.
       
  subst ra'. clear D.

  rewrite restrict_sm_local' in BB; trivial. 
  rewrite restrict_sm_all in H11. destruct (restrictD_Some _ _ _ _ _ H11) as [AI_STK VIS_STK]. 
 *) 
  rewrite restrict_sm_local' in stk_local; trivial. 
  exploit free_parallel_inject; try eapply H3.
    eassumption. eapply local_in_all; eassumption.
    
  repeat rewrite Zplus_0_r. intros [m2' [E F]]. 
  destruct ros as [rf|fid]; simpl in H; monadInv H8.
+ (* Indirect Mtailcall_internal *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs0 x0)).
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H0.
    apply ireg_of_eq in EQ1. rewrite EQ1. trivial.
  destruct (GFP _ _ H4) as [mapped_f' GlobalBlock_f'].
  inv H. 
  rewrite restrict_sm_all in H11.
  destruct (restrictD_Some _ _ _ _ _ H11) as [ZZ vis_f']; clear H11.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  rewrite Int.add_zero in H10.
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  eexists; eexists; split.
    left; eapply corestep_plus_star_trans. 
      eapply corestep_plus_one. eapply asm_exec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. rewrite <- RSP; simpl. rewrite C. rewrite A. rewrite E. eauto.
      apply corestep_star_one. eapply asm_exec_step_internal. 
        transitivity (Val.add rs0#PC Vone). auto. rewrite <- H5. simpl. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. { 
    econstructor; eauto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
    eapply agree_change_sp. eassumption.
       eapply (parent_sp_zero_or_ptr _ _ _ STACKS).
       assumption.
       apply restrict_sm_WD; trivial.
    Simplifs. rewrite Pregmap.gso; auto. 
    generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence. }
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  eexists; eexists; split.
    left. eapply corestep_plus_star_trans.
             eapply corestep_plus_one. eapply asm_exec_step_internal. eauto.
              eapply functions_transl; eauto. eapply find_instr_tail; eauto.    
              simpl. rewrite <- RSP; simpl. rewrite C. rewrite A. rewrite E. eauto.
    apply corestep_star_one. eapply asm_exec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H5. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. 
    eapply match_states_call_internal; eauto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
     eapply agree_change_sp; try eassumption.
         apply (parent_sp_zero_or_ptr _ _ _ STACKS). 
     Simplif. unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto.
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption. }

{ (* Mtailcall_external *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (f0 = f) by congruence.  subst f0.
  inv AT. clear H7 H0.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  unfold load_stack in *.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
      apply restrict_sm_WD; try eassumption. trivial.
  specialize (sp_as_inj _ _ _ _ AG WDR). intros SPAI; inv SPAI.
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H1. eexact H1.
    eassumption.
  intros [parent' [A B]].
  exploit (Mem.load_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    simpl in H2. eexact H2.
    eassumption.
  intros [ra' [C D]].
  destruct (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _ )) as [tstk stk_local].
  rewrite (local_in_all _ WDR _ _ _ stk_local) in H12; inv H12.
  rename H11 into RSP; rename b2 into tstk. 
(*
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  assert (parent' = parent_sp s).
    destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in B. inv B. rewrite H0; trivial.
    destruct H0 as [b [z [PAR LOC]]]. rewrite PAR in B.
       inv B. apply local_in_all in LOC; trivial.
       rewrite LOC in H11; inv H11.
       rewrite PAR, Int.add_zero; trivial. 
  subst parent'.

  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  assert (ra' = parent_ra s).
    destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
    rewrite H0 in D. inv D. rewrite H0; trivial.
    destruct H0 as [b [z [RA [LOC | GLOB]]]].
      rewrite RA in D. inv D. apply local_in_all in LOC; trivial.
       rewrite LOC in H11; inv H11.
       rewrite RA, Int.add_zero; trivial.
      rewrite RA in D; inv D. rewrite restrict_sm_all in H11. 
       destruct (restrictD_Some _ _ _ _ _ H11); clear H11.
        rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG _ GLOB) in H0; inv H0.
        rewrite RA, Int.add_zero. trivial.
       
  subst ra'.*)

  rewrite restrict_sm_local' in stk_local; trivial. 
(*  rewrite restrict_sm_all in H12. 
  destruct (restrictD_Some _ _ _ _ _ H12) as [AI_STK VIS_STK]; clear H12. *)
  exploit free_parallel_inject; eauto.
    eapply local_in_all; eassumption.
  repeat rewrite Zplus_0_r. intros [m2' [E F]].
  simpl in *. 
  destruct ros as [rf|fid]; simpl in H; monadInv H9.
+ (* Indirect Mtailcall_external *) 
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  clear H.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs0 x0)).
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H0.
    apply ireg_of_eq in EQ1. rewrite EQ1. trivial.
  destruct (GFP _ _ H4) as [mapped_f' GlobalBlock_f'].
  inv H. 
  rewrite restrict_sm_all in H12.
  destruct (restrictD_Some _ _ _ _ _ H12) as [ZZ vis_f']; clear H12.
  rewrite mapped_f' in ZZ; apply eq_sym in ZZ; inv ZZ.
  rewrite Int.add_zero in H11.
  generalize (code_tail_next_int _ _ _ _ NOOV H10). intro CT1.
  destruct (functions_translated _ _ H4) as [Tcallee [FFindCallee TransfCallee]].
  monadInv TransfCallee.
  assert (AG1: agree (restrict_sm mu (vis mu)) rs (parent_sp s)
            (nextinstr (rs0 # ESP <- parent') # RA <- ra') # PC <-
            (nextinstr (rs0 # ESP <- parent') # RA <- ra' x0)).
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
    eapply agree_change_sp; try eassumption.
       apply (parent_sp_zero_or_ptr _ _ _ STACKS). 
  exploit extcall_arguments_match.
    apply WDR.
    eapply AG1.
    2: eapply H5.
    rewrite restrict_sm_all. eapply inject_restrict. eassumption.
        eapply REACH_closed_free; eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  rewrite Zplus_0_r in *. rewrite Int.add_zero in *.
  eexists; eexists; split.
    left; eapply corestep_plus_trans. 
      eapply corestep_plus_one. eapply asm_exec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. rewrite <- RSP. simpl.
         rewrite C. rewrite A. rewrite E. eauto.
      eapply corestep_plus_two. eapply asm_exec_step_internal. 
        transitivity (Val.add rs0#PC Vone). auto. rewrite <- H6. simpl. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. eauto.
      eapply asm_exec_step_external.
        unfold nextinstr. Simplif.
         rewrite Pregmap.gso.
         rewrite Pregmap.gso.
         rewrite Pregmap.gso. rewrite <- H11. reflexivity.
         generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence. 
         apply ireg_of_eq in EQ1. intros N.
           rewrite N in *. clear N. destruct rf; discriminate.
         apply ireg_of_eq in EQ1. intros N.
           rewrite N in *. clear N. destruct rf; discriminate.
         eassumption.
         eassumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. 
    eapply match_states_call_external; eauto.
    Simplifs. rewrite Pregmap.gso; auto. 
    generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H10). intro CT1.
  destruct (functions_translated _ _ H4) as [Tcallee [TFindCaller TransCallee]].
  monadInv TransCallee.
  assert (AG1: agree (restrict_sm mu (vis mu)) rs (parent_sp s)
    (nextinstr (rs0 # ESP <- parent') # RA <- ra') # PC <-
    (symbol_offset tge fid Int.zero)).
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto.
      eapply (parent_sp_zero_or_ptr _ _ _ STACKS).
  exploit extcall_arguments_match.
    apply (restrict_sm_WD _ WD (vis mu)); trivial.
    apply AG1.
    rewrite restrict_sm_all; eapply inject_restrict; try eapply F; trivial.
    eapply REACH_closed_free; eassumption.
    eassumption.
  intros [targs [TExtcallArgs ArgsInj]].
  rewrite Zplus_0_r in *. rewrite Int.add_zero in *.
  eexists; eexists; split.
    left. eapply corestep_plus_trans.
             eapply corestep_plus_one. eapply asm_exec_step_internal. rewrite <- H6. eauto.
              eapply functions_transl; eauto. eapply find_instr_tail; eauto.    
              simpl. rewrite <- RSP; simpl. rewrite C. rewrite A. rewrite E. eauto.
    eapply corestep_plus_two. eapply asm_exec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H6. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. eauto.
    eapply asm_exec_step_external.
      unfold symbol_offset. rewrite symbols_preserved, H.
      Simplif.
      eassumption.
      eassumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H3). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split. 
    eapply match_states_call_external; eauto.
    Simplif. 
      unfold symbol_offset. rewrite symbols_preserved, H. trivial.
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption. }

{ (* - builtin*) 
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  inv H. inv AT. monadInv H3. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H2); intro NOOV.
  exploit (inlineable_extern_inject _ _ GDE_lemma).
        eassumption. eassumption. eassumption. eassumption. eassumption. assumption.
        rewrite <- restrict_sm_all. eapply decode_longs_inject.
        eapply preg_vals; eauto.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  eexists; eexists. 
  split. left. eapply corestep_plus_one.
           eapply asm_exec_step_builtin. eauto. eauto.
            eapply find_instr_tail; eauto.
           econstructor. eassumption.
            reflexivity. reflexivity.
  exists mu'.
  intuition.
  split.
    econstructor; eauto.
      eapply match_stack_intern_incr; try eassumption.
        eapply restrict_sm_intern_incr; eassumption. 
    instantiate (2 := tf); instantiate (1 := x).
    unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
    rewrite undef_regs_other. rewrite set_pregs_other_2. rewrite undef_regs_other_2.
    rewrite <- H. simpl. econstructor; eauto.
    eapply code_tail_next_int; eauto.
    rewrite preg_notin_charact. intros. auto with asmgen.
    rewrite preg_notin_charact. intros. auto with asmgen.
    auto with asmgen.
    simpl; intros. intuition congruence.
    apply agree_nextinstr_nf. eapply agree_set_mregs; auto.
    eapply agree_intern_incr.
        Focus 3. eapply restrict_sm_intern_incr; eassumption.
        apply restrict_sm_WD; trivial.
      eapply agree_undef_regs; eauto.
      intros; eapply undef_regs_other_2; eauto. 
    eapply encode_long_inject. rewrite restrict_sm_all; eassumption. 
    congruence.

    eapply zero_or_localid_intern_incr; eassumption.

    intuition. 
    eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
    red; intros bb fbb Hbb. destruct (GFP _ _ Hbb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.    
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. eapply (Glob _ H5).  }

(* - annot: later*)

{ (* Mgoto *)
  inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4. 
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  exists (State rs'), m2; split. left.
    apply corestep_plus_one. econstructor; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. 
    econstructor; eauto.
      eapply agree_exten. eassumption.
       (*WAS: eauto with asmgen.*) intros r DPr. eapply INV. intros; subst. inv DPr.
      congruence. }

{ (* Mcond true *)
  inv MS.
  assert (f0 = f) by congruence. subst f0.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
(*  destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit eval_condition_inject.
    eapply preg_vals; eauto.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eauto.
  intros EC.
  exploit exec_straight_steps_goto; eauto.
    intros. simpl in TR.
    destruct (transl_cond_correct tge tf cond args _ _ rs0 m2 TR)
    as [rs' [A [B C]]]. 
    rewrite EC in B.
    destruct (testcond_for_condition cond); simpl in *.
    (* simple jcc *)
      exists (Pjcc c1 lbl); exists k; exists rs'.
      split. eexact A.
      split. eapply agree_exten; eauto. 
      simpl. rewrite B. auto.
    (* jcc; jcc *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct b1.   
      (* first jcc jumps *)
      exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
      split. eexact A.
      split. eapply agree_exten; eauto. 
      simpl. rewrite TC1. auto.
      (* second jcc jumps *)
      exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
      split. eapply exec_straight_trans. eexact A. 
      eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
      split. eapply agree_exten; eauto.
      intros; Simplifs.
      simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
      destruct b2; auto || discriminate.
    (* jcc2 *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct (andb_prop _ _ H3). subst. 
      exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
      split. eexact A.
      split. eapply agree_exten; eauto. 
      simpl. rewrite TC1; rewrite TC2; auto.
  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. }

{ (* Mcond false *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  exploit eval_condition_inject.
    eapply preg_vals; eauto.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eauto.
  intros EC.
  exploit exec_straight_steps; eauto.
    intros. simpl in TR.
    destruct (transl_cond_correct tge tf cond args _ _ rs0 m2 TR)
    as [rs' [A [B C]]]. 
    rewrite EC in B.
    destruct (testcond_for_condition cond); simpl in *.
    (* simple jcc *)
      econstructor; split.
      eapply exec_straight_trans. eexact A. 
      apply exec_straight_one. simpl. rewrite B. eauto. auto. 
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      simpl; congruence.
    (* jcc ; jcc *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      destruct (orb_false_elim _ _ H1); subst.
      econstructor; split.
      eapply exec_straight_trans. eexact A. 
      eapply exec_straight_two. simpl. rewrite TC1. eauto. auto. 
      simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
      split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
      simpl; congruence.
    (* jcc2 *)
      destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
      destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
      exists (nextinstr rs'); split.
      eapply exec_straight_trans. eexact A. 
      apply exec_straight_one. simpl. 
      rewrite TC1; rewrite TC2. 
      destruct b1. simpl in *. subst b2. auto. auto.
      auto.
      split. apply agree_nextinstr. eapply agree_exten; eauto.
      rewrite H1; congruence.
  intros [st' [CS' MS']].
  exists st', m2. split. left; trivial.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. }

{ (* Mjumptable *)
  inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  eexists; eexists; split. left.
    apply corestep_plus_one. econstructor; eauto.  
    eapply find_instr_tail; eauto. 
    simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eauto.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition.
    econstructor; eauto. 
Transparent destroyed_by_jumptable. 
  simpl. eapply agree_exten; eauto.
    (*WAS: intros. rewrite C; auto with asmgen.*)
      intros r DPr. apply C. intros; subst. inv DPr.
  congruence. }

{ (* Mreturn *)
  inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros [tstk LocSTK].
  specialize (agree_sp_local _ _ _ _ AG); intros RSP.
  inv RSP. rewrite LocSTK in H11; apply eq_sym in H11. inv H11.
  rename H10 into RSP; rewrite Int.add_zero in RSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *. inv SP.*)
  unfold load_stack in *.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
     eapply (restrict_sm_WD _ WD ); trivial. 
  assert (AiSTK: as_inj mu stk = Some (tstk, 0)).
      rewrite restrict_sm_local' in LocSTK; trivial.
        apply local_in_all in LocSTK; eassumption.    
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0.
    simpl. econstructor.
      apply local_in_all in LocSTK; eassumption.
    rewrite Int.add_zero. reflexivity.
  intros [parent' [A B]]. 
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H1.
    simpl. econstructor.
      apply local_in_all in LocSTK; eassumption.
    rewrite Int.add_zero. reflexivity.
  intros [ra' [C D]]. 
  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  exploit free_parallel_inject; eauto.
  simpl. rewrite Zplus_0_r. intros [m2' [E F]].
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.
  eexists; eexists; split. left.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. eapply asm_exec_step_internal. eauto.
        eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
        simpl. rewrite <- RSP. simpl. simpl in C. rewrite C. 
          simpl in A. rewrite A. (* rewrite <- (sp_val _ _ _ AG).*)
          rewrite E. eauto.
    apply corestep_star_one. eapply asm_exec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H3. simpl. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. eauto. 
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ E). intuition.
  split.
    constructor; eauto. 
     apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
       eapply agree_change_sp; eauto. 
         eapply (parent_sp_zero_or_ptr _ _ _ STACKS). 
   intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption. }

{ (*internal function *)
  inv MS.
  rewrite INT in H. inv H.
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'. rewrite transl_code'_transl_code in EQ0.
  destruct (zlt (list_length_z x0) Int.max_unsigned); inversion EQ1. clear EQ1.
  unfold store_stack in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
     eapply (restrict_sm_WD _ WD ); trivial. 
  exploit alloc_parallel_intern; try eassumption. apply Z.le_refl. apply Z.le_refl.
  intros [mu' [tm1 [tstk [TAlloc [INJ1 [INC [STK [Mu'Mu [SEP [LOCALLOC [WD' [WMV' RC1]]]]]]]]]]]]. 
  assert (stk_local: local_of (restrict_sm mu' (vis mu')) stk = Some (tstk, 0)).
    rewrite restrict_sm_local'; trivial.
    destruct (joinD_Some _ _ _ _ _ STK) as [EXT | [_ LOC]]; trivial.
    assert (EXT': extern_of mu = extern_of mu') by eapply INC.
    rewrite <- EXT' in EXT; clear EXT'.
    apply extern_in_all in EXT; trivial. 
    destruct (as_inj_DomRng _ _ _ _ EXT WD).
    elim (Mem.fresh_block_alloc _ _ _ _ _ H0).
    eapply SMV. apply H.
  exploit Mem.store_mapped_inject; try eapply INJ1. eapply H1. eassumption.
    eapply val_inject_incr.
      eapply (intern_incr_as_inj _ _ INC WD').
    eapply val_inject_incr.
       2: apply (sp_as_inj _ _ _ _ AG WDR).
    rewrite restrict_sm_all. apply restrict_incr. 
  rewrite Zplus_0_r, Int.add_zero_l. intros [tm0 [ST1 INJ0]].
  exploit Mem.store_mapped_inject; try eapply INJ0. eapply H2. eassumption.
    instantiate (1:=rs0 RA). 
    eapply val_inject_incr.
      eapply (intern_incr_as_inj _ _ INC WD').
    eapply val_inject_incr; try eassumption.
      rewrite restrict_sm_all. apply restrict_incr. 
  rewrite Zplus_0_r, Int.add_zero_l. intros [tm3 [ST2 INJ3]].
  eexists; eexists; split.
    left. apply corestep_plus_one. econstructor; eauto. 
     subst x; simpl.
     rewrite Int.unsigned_zero. simpl. eauto.
     simpl. rewrite TAlloc . simpl in ST1.
      rewrite Int.add_zero_l.
      destruct AG as [AG1 AG2]. rewrite ST1.
      rewrite Int.add_zero_l.
      simpl in ST2. rewrite ST2.
      eauto.
  exists mu'. intuition.
    rewrite sm_locally_allocatedChar.
    rewrite sm_locally_allocatedChar in LOCALLOC.
    assert (freshloc m m3 = freshloc m m1).
      extensionality b. rewrite <- (freshloc_trans m m1).
      rewrite <- (freshloc_trans m1 m0 m3).
      rewrite (storev_freshloc _ _ _ _ _ H1).
      rewrite (storev_freshloc _ _ _ _ _ H2). intuition.
      eapply store_forward; eapply H1.
      eapply store_forward; eapply H2.
      eapply alloc_forward; eassumption.
      eapply mem_forward_trans. 
      eapply store_forward; eapply H1.
      eapply store_forward; eapply H2.
    rewrite H4.
    assert (freshloc m2 tm3 = freshloc m2 tm1).
      extensionality b. rewrite <- (freshloc_trans m2 tm1).
      rewrite <- (freshloc_trans tm1 tm0 tm3).
      rewrite (store_freshloc _ _ _ _ _ _ ST1).
      rewrite (store_freshloc _ _ _ _ _ _ ST2). intuition.
      eapply store_forward; eapply ST1.
      eapply store_forward; eapply ST2.
      eapply alloc_forward; eassumption.
      eapply mem_forward_trans. 
      eapply store_forward; eapply ST1.
      eapply store_forward; eapply ST2.
    rewrite H5.
    assumption.
split.
  econstructor; eauto.
  eapply match_stack_intern_incr; try eassumption.
     apply restrict_sm_intern_incr; trivial.
  unfold nextinstr. rewrite Pregmap.gss.
     repeat rewrite Pregmap.gso; auto with asmgen. 
  rewrite ATPC. simpl. constructor; eauto.
  subst x. unfold fn_code. eapply code_tail_next_int. rewrite list_length_z_cons. omega. 
  constructor.
  { (*agree *) subst sp.
  apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
  apply agree_undef_regs with rs0; eauto.
    eapply agree_intern_incr; try eassumption.
    apply restrict_sm_WD; trivial. 
    apply restrict_sm_intern_incr; try eassumption; trivial.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto. 
  right. exists stk, Int.zero, tstk; split; trivial.
  econstructor. eapply local_in_all; try eassumption.
    apply restrict_sm_WD; trivial. 
    rewrite Int.add_zero. trivial.
    apply restrict_sm_WD; trivial. }
    
  intros. unfold nextinstr. simpl.
     rewrite Pregmap.gso. rewrite Pregmap.gso. rewrite Pregmap.gss.
     eapply val_inject_incr.
       2: apply (sp_as_inj _ _ _ _ AG WDR).
       rewrite restrict_sm_all. rewrite restrict_sm_all. apply intern_incr_restrict; trivial.
    congruence. congruence.
    subst sp. right. exists stk, Int.zero, tstk. split; trivial. 
       rewrite restrict_sm_local' in stk_local; trivial. 
 assert (stkVIS: vis mu' stk = true).
   unfold vis. rewrite restrict_sm_local' in stk_local; trivial.
      destruct (local_DomRng _ WD' _ _ _ stk_local).
      rewrite H4; trivial. 
  assert (parentra_VIS: forall b' (Hb' : getBlocks (parent_ra s :: nil) b' = true), vis mu' b' = true).
    intros. apply getBlocks_char in Hb'.
    destruct Hb'. destruct H4; try contradiction.
    destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
    rewrite H5 in H4; discriminate.
    eapply (intern_incr_vis _ _ INC). unfold vis.
    destruct H5 as [bb [z [PAR [[tb LOC] | GL]]]]; rewrite PAR in H4; inv H4.
      rewrite restrict_sm_local' in LOC; trivial.
      destruct (local_DomRng _ WD _ _ _ LOC). intuition.
    intuition.
  intuition.
    eapply REACH_Store. eapply H2. eassumption. eassumption.
    eapply REACH_Store. eapply H1. eassumption. 
    intros. eapply (intern_incr_vis _ _ INC). unfold vis. 
     destruct (parent_sp_zero_or_ptr _ _ _ STACKS). rewrite H5 in H4. unfold getBlocks in H4; simpl in H4. discriminate.
     destruct H5 as [bb [z [tbb [PARSP LOC]]]]. rewrite PARSP in H4.
     apply getBlocks_char in H4. destruct H4. destruct H4; try contradiction. inv H4.
     rewrite restrict_sm_local' in LOC; trivial.
      destruct (local_DomRng _ WD _ _ _ LOC). intuition.
    assumption.
    eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
    red; intros bb fbb Hbb. destruct (GFP _ _ Hbb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
          rewrite <- FRG. eapply (Glob _ H4).
    apply sm_locally_allocatedChar in LOCALLOC. 
      rewrite (freshloc_alloc _ _ _ _ _ H0) in LOCALLOC.
      rewrite (freshloc_alloc _ _ _ _ _ TAlloc) in LOCALLOC.
      destruct LOCALLOC as [DS [DT _]].
      split; intros.
        unfold DOM in H4. rewrite DS in H4.
          eapply Mem.store_valid_block_1; try eapply H2.
          eapply Mem.store_valid_block_1; try eapply H1.
          destruct (eq_block b1 stk); subst; simpl in *.
            apply (Mem.valid_new_block _ _ _ _ _ H0).
            apply (Mem.valid_block_alloc _ _ _ _ _ H0).
              eapply SMV. rewrite orb_false_r in H4; trivial.
        unfold RNG in H4. rewrite DT in H4.
          eapply Mem.store_valid_block_1; try eapply ST2.
          eapply Mem.store_valid_block_1; try eapply ST1.
          destruct (eq_block b2 tstk); subst; simpl in *.
            apply (Mem.valid_new_block _ _ _ _ _ TAlloc).
            apply (Mem.valid_block_alloc _ _ _ _ _ TAlloc).
              eapply SMV. rewrite orb_false_r in H4; trivial. }

(*external function: no case*) 

{ (* return *)
  inv MS.
  inv STACKS. simpl in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  eexists; eexists; split.
    right. split. omega. eapply corestep_star_zero.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. 
  destruct (GFP _ _ H4).
  econstructor; eauto.
    { inv H5. inv ATPC.
      rewrite restrict_sm_all in H12.
      destruct (restrictD_Some _ _ _ _ _ H12); clear H12. 
      rewrite H5 in H; inv H.
      rewrite Int.add_zero.
      econstructor; eassumption. }
    congruence.
    rewrite restrict_sm_zero_or_localid in H6; trivial. }
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
SM_simulation.SM_simulation_inject 
   (Mach_eff_sem return_address_offset) Asm_eff_sem ge tge entrypoints.
Proof.
intros.
assert (GDE:= GDE_lemma). 
 eapply sepcomp.effect_simulations_lemmas.inj_simulation_plus with
  (match_states:=MATCH) (measure:=measure).
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
(* init*) { admit. }
{ (* halted -- will need to be adapted once we have non-integer return values in Mach*)
    intros. destruct H as [MC [RC [PG [GF [Glob [VAL WD]]]]]].
    inv MC; simpl in H0. inv H0. inv H0. inv H0.
    admit. (*TODO (GS)*)
(*    destruct s; simpl in *; try inv H0.
      remember (ms AX) as v.
      destruct v; inv H1.
      eexists. split. assumption.
      split. econstructor.
      rewrite ATPC; simpl.
      specialize (agree_mregs _ _ _ _ AG AX); rewrite <- Heqv; intros.
      inv H. trivial.*) }
{ (*at_external *) admit. }
{ (*after_external *) admit. }
{ (*core_diagram*)
   intros. 
   exploit MATCH_core_diagram; try eassumption.
    intros [st2' [m2' [CSTgt [mu' MU]]]].
    exists st2', m2', mu'. intuition. }
{ (*effcore_diagram *)
  intros.
   exploit effcore_diagram; try eassumption.
    intros [st2' [m2' [U2 [CSTgt [mu' MU]]]]].
    exists st2', m2', mu'.
    split. eapply MU.
    split. eapply MU.
    split. eapply MU.
    split. eapply MU. 
    exists U2. split. trivial. eapply MU. }
Qed.
(*
(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros. 
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H. replace lessdef by val_inject
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]]. 
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto. 
  simpl; intros. rewrite Q; auto with asmgen.
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *. 
  exploit Mem.loadv_extends. eauto. eexact H0. auto. 
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. 
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros. 
  assert (DIFF: negb (mreg_eq dst DX) = true -> IR EDX <> preg_of dst).
    intros. change (IR EDX) with (preg_of DX). red; intros. 
    unfold proj_sumbool in H1. destruct (mreg_eq dst DX); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR.
(* EDX contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite DXP; eauto.  
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto. 
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite R; auto.
(* EDX does not contain parent *)
  monadInv TR.
  exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
  intros [rs2 [S [T U]]]. 
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite U; auto.

- (* Mop *)
  assert (eval_operation tge sp op rs##args m = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A. 
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]]. 
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto.
  simpl; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr rs##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]]. 
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr rs##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR. 
  exploit transl_store_correct; eauto. intros [rs2 [P Q]]. 
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto.  
  simpl; congruence.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Int.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. 
  econstructor; eauto. 
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto. 
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. eauto.
  econstructor; eauto. 
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]]. 
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Int.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal. 
  transitivity (Val.add rs0#PC Vone). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  Simplifs. rewrite Pregmap.gso; auto. 
  generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal. 
  transitivity (Val.add rs0#PC Vone). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  rewrite Pregmap.gss. unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto.

- (* Mbuiltin *)
  inv AT. monadInv H3. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H2); intro NOOV.
  exploit external_call_mem_extends'; eauto. eapply preg_vals; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  rewrite undef_regs_other. rewrite set_pregs_other_2. rewrite undef_regs_other_2.
  rewrite <- H0. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  simpl; intros. intuition congruence.
  apply agree_nextinstr_nf. eapply agree_set_mregs; auto.
  eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto. 
  congruence.

- (* Mannot *)
  inv AT. monadInv H4. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit annot_arguments_match; eauto. intros [vargs' [P Q]]. 
  exploit external_call_mem_extends'; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_annot. eauto. eauto.
  eapply find_instr_tail; eauto. eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_states_intro with (ep := false); eauto with coqlib.
  unfold nextinstr. rewrite Pregmap.gss. 
  rewrite <- H1; simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto. 
  apply agree_nextinstr. auto.
  congruence.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4. 
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]]. 
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists (Pjcc c1 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto. 
  simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.   
  (* first jcc jumps *)
  exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto. 
  simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
  split. eapply exec_straight_trans. eexact A. 
  eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten; eauto.
  intros; Simplifs.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst. 
  exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto. 
  simpl. rewrite TC1; rewrite TC2; auto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR. 
  destruct (transl_cond_correct tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]]. 
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  apply exec_straight_one. simpl. rewrite B. eauto. auto. 
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  eapply exec_straight_two. simpl. rewrite TC1. eauto. auto. 
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr rs'); split.
  eapply exec_straight_trans. eexact A. 
  apply exec_straight_one. simpl. 
  rewrite TC1; rewrite TC2. 
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  rewrite H1; congruence.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply find_instr_tail; eauto. 
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eauto.
  econstructor; eauto. 
Transparent destroyed_by_jumptable. 
  simpl. eapply agree_exten; eauto. intros. rewrite C; auto with asmgen.
  congruence.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]]. 
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]]. 
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal. 
  transitivity (Val.add rs0#PC Vone). auto. rewrite <- H3. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. traceEq.
  constructor; auto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'. rewrite transl_code'_transl_code in EQ0.
  destruct (zlt (list_length_z x0) Int.max_unsigned); inversion EQ1. clear EQ1.
  unfold store_stack in *. 
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto. 
  intros [m2' [F G]].
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto. 
  intros [m3' [P Q]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  subst x; simpl.
  rewrite Int.unsigned_zero. simpl. eauto.
  simpl. rewrite C. simpl in F. rewrite (sp_val _ _ _ AG) in F. rewrite F.
  simpl in P. rewrite ATLR. rewrite P. eauto.
  econstructor; eauto.
  unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with asmgen. 
  rewrite ATPC. simpl. constructor; eauto.
  subst x. unfold fn_code. eapply code_tail_next_int. rewrite list_length_z_cons. omega. 
  constructor. 
  apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
  apply agree_undef_regs with rs0; eauto.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto. 
  congruence. 
  intros. Simplifs. eapply agree_sp; eauto.

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto. 
  intros [args' [C D]].
  exploit external_call_mem_extends'; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto. 
  eapply external_call_symbols_preserved'; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  unfold loc_external_result.
  apply agree_set_other; auto. apply agree_set_mregs; auto.

- (* return *)
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  econstructor; eauto. rewrite ATPC; eauto. congruence.
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  replace (symbol_offset (Genv.globalenv tprog) (prog_main tprog) Int.zero)
     with (Vptr fb Int.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. unfold Vzero; congruence. intros. rewrite Regmap.gi. auto. 
  unfold symbol_offset. 
  rewrite (transform_partial_program_main _ _ TRANSF).
  rewrite symbols_preserved. 
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. auto. 
  compute in H1. inv H1.  
  generalize (preg_val _ _ _ AX AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.
*)
End PRESERVATION.
