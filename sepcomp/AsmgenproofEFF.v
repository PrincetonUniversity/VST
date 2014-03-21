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
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import reach.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.

(*LENB: First two generalizations of some lemmas from Op.v.
  The lemmas in Op.v specialize ofs to Int.zero*)
Section EVAL_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Lemma eval_addressing_inject':
  forall addr vl1 vl2 v1 ofs,
  val_list_inject f vl1 vl2 ->
  eval_addressing genv (Vptr sp1 ofs) addr vl1 = Some v1 ->
  exists v2, 
     eval_addressing genv (Vptr sp2 ofs) (shift_stack_addressing (Int.repr delta) addr) vl2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_addressing. simpl.
  eapply eval_addressing_inj with (sp1 := Vptr sp1 ofs); eauto.
  eapply symbol_address_inject; trivial.
Qed.
Lemma eval_operation_inject':
  forall op vl1 vl2 v1 m1 m2 ofs,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv (Vptr sp1 ofs) op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv (Vptr sp2 ofs) (shift_stack_operation (Int.repr delta) op) vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_operation. simpl.
  eapply eval_operation_inj with (sp1 := Vptr sp1 ofs) (m1 := m1); eauto.
  eapply symbol_address_inject; trivial.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.
End EVAL_INJECT.

Section EVAL_INJECT2.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Variable sp1: val.
Variable sp2: val.
Hypothesis sp_inj: val_inject f sp1 sp2 .
Hypothesis PG: meminj_preserves_globals genv f.
Variable vl1: list val.
Variable vl2: list val.
Hypothesis VL: val_list_inject f vl1 vl2.

Lemma eval_operation_inject'':
  forall op v1 m1 m2,
  Mem.inject f m1 m2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv sp2 op vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros.
  eapply eval_operation_inj.
  eapply symbol_address_inject; trivial.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  eassumption. eassumption. eassumption.
Qed.

Hypothesis SPVundef: sp1<>Vundef.
Hypothesis SPPtr: forall b ofs, sp1<>Vptr b ofs.

Lemma eval_addressing_sp_scalar:
  forall addr v1,
  eval_addressing genv sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp2 addr vl2 = Some v2
             /\ val_inject f v1 v2.
Proof.
  intros.
  destruct addr; destruct vl1; simpl in H; try inv H; simpl; trivial.
    destruct l; inv H1. inv VL. inv H3. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto. 
    destruct l; inv H1. destruct l; inv H0. inv VL. inv H3. inv H5.
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
       eapply val_add_inject; eauto.
    destruct l; inv H1. inv VL. inv H3. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
       inv H1; try econstructor.
    destruct l; inv H1. destruct l; inv H0. inv VL. inv H3. inv H5. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
       eapply val_add_inject; eauto.
       inv H2; try econstructor.
    inv VL. 
       eexists; split. reflexivity.
         eapply symbol_address_inject; trivial.
    destruct l; inv H1. inv VL. inv H3.
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
         eapply symbol_address_inject; trivial.
    destruct l; inv H1. inv VL. inv H3.
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
         eapply symbol_address_inject; trivial.
         inv H1; try econstructor.
    inv VL. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
Qed.
(*
Hypothesis globals: meminj_preserves_globals genv f.

Lemma eval_operation_inject'':
  forall op vl1 vl2 v1 m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv sp2 op vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros.
  eapply eval_operation_inj.
  eapply symbol_address_inject; trivial.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  eassumption. eassumption. eassumption.
Qed.
*)
End EVAL_INJECT2.

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

Definition sp_zero_or_local mu sp:= 
  sp=Vzero \/ exists spb ofs, sp=Vptr spb ofs /\ 
                              locBlocksSrc mu spb = true.

Inductive match_states mu: Mach_core -> mem -> Asm_coop.state -> mem -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge (local_of (restrict_sm mu (vis mu))) s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.inject (as_inj mu) m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree (restrict_sm mu (vis mu)) ms sp rs)
        (*(DXP: ep = true -> rs#EDX = parent_sp s)*)
        (DXP: ep = true -> 
              val_inject (as_inj (restrict_sm mu (vis mu))) (parent_sp s) (rs#EDX))
        (*NEW*) (SPlocalSrc: sp_zero_or_local mu sp),
      match_states mu (Mach_State s fb sp c ms) m
                      (State rs) m'
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge (local_of (restrict_sm mu (vis mu))) s)
        (MEXT: Mem.inject (as_inj mu) m m')
        (AG: agree (restrict_sm mu (vis mu)) ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Int.zero)
        (ATLR: rs RA = parent_ra s),
      match_states mu (Mach_Callstate s fb ms) m
                      (State rs) m'
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge (local_of (restrict_sm mu (vis mu))) s)
        (MEXT: Mem.inject (as_inj mu) m m')
        (AG: agree (restrict_sm mu (vis mu)) ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states mu (Mach_Returnstate s ms) m
                      (State rs) m'.

Lemma exec_straight_steps:
  forall mu s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge (local_of (restrict_sm mu (vis mu))) s ->
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
  (*NEW*) forall (SPlocalSrc: sp_zero_or_local mu sp),
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
  match_stack ge (local_of (restrict_sm mu (vis mu))) s ->
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
  (*NEW*) forall (SPlocalSrc: sp_zero_or_local mu sp),
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
  match_stack ge (local_of (restrict_sm mu (vis mu))) s ->
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
  (*NEW*) forall (SPlocalSrc: sp_zero_or_local mu sp),
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
  match_stack ge (local_of (restrict_sm mu (vis mu))) s ->
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
  (*NEW*) forall (SPlocalSrc: sp_zero_or_local mu sp),
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

Lemma match_states_restrict mu c1 m1 c2 m2: forall
        (MS:match_states mu c1 m1 c2 m2) X
        (RC: REACH_closed m1 X)
        (HX : forall b : block, vis mu b = true -> X b = true),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros. inv MS.
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
     unfold sp_zero_or_local. rewrite restrict_sm_locBlocksSrc. assumption.
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
       rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption.
   econstructor; eauto.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite vis_restrict_sm, restrict_sm_nest; assumption. 
Qed.

Definition MATCH (d:Mach_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\ 
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
(*  globalfunction_ptr_inject (as_inj mu) /\*)
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
  destruct MC as [MS [RC [PG (*[GF*) [Glob [SMV WD]]]]].
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
      (SPlocalSrc : sp_zero_or_local mu sp),
  exists a',
    eval_addressing ge (rs0 ESP) addr rs0 ## (preg_of ## args) = Some a' /\
    val_inject (as_inj (restrict_sm mu (vis mu))) a a'.
Proof. intros.
     destruct SPlocalSrc.
    (*case sp=Vzero*) subst.
       eapply eval_addressing_sp_scalar; try eassumption.
         rewrite <- (sp_val _ _ _ _ AG). constructor. 
        eapply restrict_sm_preserves_globals with (X:=vis mu). eassumption.
          unfold vis; intuition.
        eapply preg_vals; eassumption.
    (*case sp=Vptr spb ofs*) 
      destruct H as [spb [z [SP LocSPSrc]]]. subst.
      specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
      exploit eval_addressing_inject'.
        eapply restrict_sm_preserves_globals with (X:=vis mu). eassumption.
          unfold vis; intuition.
        eapply local_in_all; try eassumption.
          apply restrict_sm_WD. assumption. trivial.
        eapply preg_vals; eassumption.
        eassumption.
    rewrite <- (sp_val _ _ _ _ AG). rewrite eval_shift_stack_addressing. simpl.
      rewrite Int.add_zero. trivial.
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
  | Mach_Returnstate _ _ => 1%nat
  | _ => 0%nat
  end.

Lemma MATCH_core_diagram: forall st1 m1 st1' m1' 
        (CS: corestep (Mach_eff_sem return_address_offset) ge st1 m1 st1' m1')
        st2 mu m2 (MTCH: MATCH st1 mu st1 m1 st2 m2),
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
destruct CS; intros; destruct MTCH as [MS PRE]; try inv MS.
{ (* Mlabel *)
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
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  unfold load_stack in H. 
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
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
  unfold store_stack in H.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
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
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *. 
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H0. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H0.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
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
  assert (eval_operation tge sp op rs##args m = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  specialize (agree_sp_local _ _ _ _ AG); intros LocSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  assert (GDEQ: genvs_domain_eq ge tge).
    clear -ge tge. unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
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
        apply genvs_domain_eq_sym; eassumption.
      unfold vis. intuition. rewrite Glob. intuition.
      rewrite (genvs_domain_eq_isGlobal _ _ GDEQ); trivial.
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

- (* Mload *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  specialize (sp_val _ _ _ _ AG); intros RSP.
  assert (eval_addressing tge sp addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A. rewrite <- RSP. (*rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
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
      instantiate (2:=rs0). rewrite <- RSP. eapply A.
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
  split; intuition. eassumption.

- (* Mstore *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  specialize (sp_val _ _ _ _ AG); intros RSP.
  assert (eval_addressing tge sp addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A, <- RSP. (* rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
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
      exploit transl_store_correct; eauto. rewrite <- RSP. eassumption. 
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
                   destruct (restrictD_Some _ _ _ _ _ H7); trivial.

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
  exploit ireg_val; try eassumption.
  rewrite H5; intros VI; inv VI.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs0 x0)).
    specialize (agree_mregs _ _ _ _ AG rf); simpl. 
    apply ireg_of_eq in EQ1.
    rewrite H5, EQ1; trivial.
  (*
  assert (rs0 x0 = Vptr f' Int.zero).
    rewrite Int.add_zero_l  in H9. rewrite <- H9, <- H5. 
    apply ireg_of_eq in EQ1.
    specialize (agree_mregs _ _ _ _ AG rf); simpl. 
    intros. rewrite H5 in H7. inv H7. rewrite H13 in H10. inv H10.
    exploit ireg_val; eauto. intros. 
    rewrite Int.add_zero_l  in H12. simpl in H9.
    exploit ireg_val; eauto. intros. 
    specialize (agree_mregs _ _ _ _ AG rf); simpl. 
     rewrite (ireg_of_eq _ _ EQ1). intros. simpl in H6.  _ rewrite H5; intros LD; inv LD.
    specialize (agree_mregs _ _ _ _ AG). _ 
      unfold ireg_of in EQ1. auto.*)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  eexists; eexists. 
  split. left. apply corestep_plus_one. eapply asm_exec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. eauto.
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
    econstructor; eauto. 
      econstructor; eauto. 
      destruct SPlocalSrc as [SPLOC | SPLOC]. subst sp. 
        admit. (*TODO: repair*)
      destruct SPLOC as [spb [z [RSP LB]]]. subst sp. 
      exists spb, z. split; eauto.
      apply (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)).
     exists fb; eexists; split. reflexivity.
       admit. (*TODO: repair: function ptr fs in fact is mapped by foerign, not by local*)
  simpl. eapply agree_exten; try eassumption. intros. Simplifs.
  Simplifs. rewrite <- H5. 
      specialize (agree_mregs _ _ _ _ AG rf). 
      rewrite (ireg_of_eq _ _ EQ1), H5.
      intros. inv H7. rewrite H10 in H14. inv H14.
        rewrite <- H5, H9. symmetry. inv AG. admit. (*TODO*)
  Simplifs. rewrite <- H2. auto.
 intuition.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  eexists; eexists; split.
    left; apply corestep_plus_one. eapply asm_exec_step_internal. eauto.
      eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
      simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. eauto.
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
    econstructor; eauto. 
    econstructor; eauto.
    admit. (*TODO eapply agree_sp_def; eauto.*)
    eexists; eexists; split. reflexivity.
    inv AG. admit. (*TODO*)
    simpl. eapply agree_exten; eauto. intros. Simplifs.
    Simplifs. rewrite <- H2. auto.
  intuition.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  specialize (sp_val _ _ _ _ AG). intros RSP.
  specialize (agree_sp_ptr _ _ _ _ AG). rewrite RSP, <- H11. intros.
  specialize (H9 _ _ (eq_refl _)).
  assert (b2 = stk /\ delta =0). 
    rewrite <- H11 in RSP; clear H11. 
    apply local_in_all in H9; trivial. 
    remember (Int.add soff (Int.repr delta)) as u. 
    assert (b2=stk /\ soff = u). clear Hequ. inv RSP. split; trivial.
    destruct H10. split; trivial. clear RSP. subst soff b2. clear Hequ.
    rewrite H9 in H12; inv H12; trivial.
  destruct H10; subst. rewrite Int.add_zero in *. rewrite Zplus_0_r in *.
  simpl in *.

  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  assert (parent' = parent_sp s).
    destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
    rewrite H10 in B. inv B. rewrite H10. trivial.
    destruct H10 as [b [z [PAR LOC]]]. rewrite PAR in B.
       inv B. apply local_in_all in LOC; trivial.
       rewrite LOC in H14. inv H14. rewrite PAR, Int.add_zero. trivial. 
  subst parent'. clear B.

  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  assert (ra' = parent_ra s).
    destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
    rewrite H10 in D. inv D. rewrite H10. trivial.
    destruct H10 as [b [z [RA LOC]]]. rewrite RA in D.
       inv D. apply local_in_all in LOC; trivial.
       rewrite LOC in H14. inv H14. rewrite RA, Int.add_zero. trivial. 
  subst ra'. clear D.

  rewrite restrict_sm_all in H12; trivial.
  destruct (restrictD_Some _ _ _ _ _ H12).
  exploit free_parallel_inject; eauto.
  repeat rewrite Zplus_0_r. intros [m2' [E F]]. 
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (val_inject (as_inj (restrict_sm mu (vis mu))) (Vptr f' Int.zero) (rs0 x0)).
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H7.
    apply ireg_of_eq in EQ1. rewrite EQ1. trivial.
  (*assert rs0 x0 = Vptr f' Int.zero)
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
    rewrite H16. rewrite <- H7.
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H7; intros.
    inv H14. rewrite H20 in H17. inv H17.
    apply ireg_of_eq in EQ1. rewrite <- EQ1. subst x0.
    specialize (agree_mregs _ _ _ _ AG rf). rewrite H7; intros.
     destruct (rewrite*)
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  eexists; eexists; split.
    left; eapply corestep_plus_star_trans. 
      eapply corestep_plus_one. eapply asm_exec_step_internal. eauto.
         eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
         simpl. rewrite <- H11; simpl. rewrite C. rewrite A. rewrite E. eauto.
      apply corestep_star_one. eapply asm_exec_step_internal. 
        transitivity (Val.add rs0#PC Vone). auto. rewrite <- H4. simpl. eauto.
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
    econstructor; eauto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
    eapply agree_change_sp. eassumption. 
         eapply parent_sp_def; eassumption.
         intros b z PARPtr.
         destruct (parent_sp_zero_or_ptr _ _ _ STACKS) as [PAR | [bb [zz [PAR LOC]]]]; 
          rewrite PAR in PARPtr; inv PARPtr; trivial. 
    Simplifs. rewrite Pregmap.gso; auto. 
      admit. (*TODO: difference due to val_inject above*)
    generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.

  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.

+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  eexists; eexists; split.
    left. eapply corestep_plus_star_trans.
             eapply corestep_plus_one. eapply asm_exec_step_internal. eauto.
              eapply functions_transl; eauto. eapply find_instr_tail; eauto.    
              simpl. rewrite <- H11; simpl. rewrite C. rewrite A. rewrite E. eauto.
    apply corestep_star_one. eapply asm_exec_step_internal. 
      transitivity (Val.add rs0#PC Vone). auto. rewrite <- H4. simpl. eauto.
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
    econstructor; eauto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    (*WAS:eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.*)
     eapply agree_change_sp. eassumption. 
         eapply parent_sp_def; eassumption.
         intros b z PARPtr.
         destruct (parent_sp_zero_or_ptr _ _ _ STACKS) as [PAR | [bb [zz [PAR LOC]]]]; 
          rewrite PAR in PARPtr; inv PARPtr; trivial. 
    rewrite Pregmap.gss. unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto.
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.

(* - builtin: later*)
(* - annot: later*)

- (* Mgoto *)
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
       (*was:  eauto with asmgen.*) intros. eapply INV. intros; subst. inv H9.
      congruence.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  split; intuition.

- (* Mcond false *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  split; intuition.

- (* Mjumptable *)
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
      intros. apply C. intros; subst. inv H12.
  congruence.

- 
(* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *. inv SP.*)
  unfold load_stack in *.
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0.
    simpl. econstructor.
      apply local_in_all in LocSP; try eassumption.
      apply restrict_sm_WD; try eassumption. trivial.
    rewrite Int.add_zero. reflexivity.
  intros [parent' [A B]]. 
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H1.
    simpl. econstructor.
      apply local_in_all in LocSP; try eassumption.
      apply restrict_sm_WD; try eassumption. trivial.
    rewrite Int.add_zero. reflexivity.
  intros [ra' [C D]]. 
  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  exploit free_parallel_inject; eauto.
    rewrite restrict_sm_local in LocSP.
    destruct (restrictD_Some _ _ _ _ _ LocSP).
    eapply local_in_all; eassumption.
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
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
     eapply (restrict_sm_WD _ WD ); trivial. 
  split.
    constructor; eauto. 
     apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
       destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
       (*vzero*)
         rewrite H6 in *.  inv B.
         eapply agree_change_sp; eauto. congruence. simpl; congruence. 
       (*ptr*)
         destruct H6 as [par_sp [par_ofs [ParSP J]]]. rewrite ParSP in *.
         inv B. rewrite (local_in_all _ WDR _ _ _ J) in H9. inv H9.
         rewrite Int.add_zero. 
         eapply agree_change_sp; eauto. congruence. simpl; congruence.
     destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
     (*vzero*)
         rewrite H6 in *.  inv D. reflexivity. 
     (*ptr*)
         destruct H6 as [par_ra [par_ofs [ParRA J]]]. rewrite ParRA in *.
         inv D. rewrite (local_in_all _ WDR _ _ _ J) in H9. inv H9.
         rewrite Int.add_zero. reflexivity.
   intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.

- (*internal function *) admit.

- (*external function*) admit.

- (* return *)
  inv STACKS. simpl in *.
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
  econstructor; eauto. rewrite ATPC; eauto. congruence.
    right. rewrite restrict_sm_local in H6.
    destruct H6 as [spb [z [SP LOC]]].
    destruct (restrictD_Some _ _ _ _ _ LOC).
    destruct (local_DomRng _ H9 _ _ _ H3).
    exists spb, z; split; assumption.
Qed.

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
  simpl; intros. intuition. }

{ (* Mgetstack *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  unfold load_stack in H. 
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
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
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
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
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  assert (SPptr: exists spb z, sp = Vptr spb z).
     destruct sp; inv H0. exists b, i; trivial.
  destruct SPptr as [spb [z SP]]; subst; simpl in H0.
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
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
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  specialize (agree_sp_local _ _ _ _ AG); intros LocSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *.*)
  assert (GDEQ: genvs_domain_eq ge tge).
    clear -ge tge. unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
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
        apply genvs_domain_eq_sym; eassumption.
      unfold vis. intuition. rewrite Glob. intuition.
      rewrite (genvs_domain_eq_isGlobal _ _ GDEQ); trivial.
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

- (* Mload *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  specialize (sp_val _ _ _ _ AG); intros RSP.
  assert (eval_addressing tge sp addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A. rewrite <- RSP. (*rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
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
      instantiate (2:=rs0). rewrite <- RSP. eapply A.
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
         intuition.

- (* Mstore *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  specialize (sp_val _ _ _ _ AG); intros RSP.
  assert (eval_addressing tge sp addr rs0 ## (preg_of ## args) = Some a').
    rewrite <- A, <- RSP. (* rewrite eval_shift_stack_addressing. simpl. rewrite Int.add_zero.*)
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
      exploit transl_store_correct_eff; eauto. rewrite <- RSP. eassumption. 
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
  rewrite H5. eapply visPropagateR; eassumption. 

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  admit. (*later
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
  Simplifs. rewrite <- H2. auto.*) 
+ (* Direct call *)
  admit. (*later*)

- admit. (*TailCall -later*)
(* - builtin: later*)
(* - annot: later*)

- (* Mgoto *)
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
       (*was:  eauto with asmgen.*) intros. eapply INV. intros; subst. inv H9.
      congruence.
  simpl. intuition.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  intuition.

- (* Mcond false *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
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
  intuition.

- (* Mjumptable *)
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
        intros. apply C. intros; subst. inv H12.
      congruence.
  intuition.

- 
(* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  specialize (agree_sp_ptr _ _ _ _ AG _ _ (eq_refl _)); intros LocSP.
  specialize (sp_val _ _ _ _ AG); intros RSP.
  (*destruct (agree_sp_shape _ _ _ _ AG) as [spb [z [SP [LocSP RSP]]]].
  subst. simpl in *. inv SP.*)
  unfold load_stack in *.
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0.
    simpl. econstructor.
      apply local_in_all in LocSP; try eassumption.
      apply restrict_sm_WD; try eassumption. trivial.
    rewrite Int.add_zero. reflexivity.
  intros [parent' [A B]]. 
  (*exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.*)
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H1.
    simpl. econstructor.
      apply local_in_all in LocSP; try eassumption.
      apply restrict_sm_WD; try eassumption. trivial.
    rewrite Int.add_zero. reflexivity.
  intros [ra' [C D]]. 
  (*exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.*)
  exploit free_parallel_inject; eauto.
    rewrite restrict_sm_local in LocSP.
    destruct (restrictD_Some _ _ _ _ _ LocSP).
    eapply local_in_all; eassumption.
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
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
     eapply (restrict_sm_WD _ WD ); trivial. 
  split.
    split. constructor; eauto. 
      apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
       destruct (parent_sp_zero_or_ptr _ _ _ STACKS).
       (*vzero*)
         rewrite H6 in *.  inv B.
         eapply agree_change_sp; eauto. congruence. simpl; congruence. 
       (*ptr*)
         destruct H6 as [par_sp [par_ofs [ParSP J]]]. rewrite ParSP in *.
         inv B. rewrite (local_in_all _ WDR _ _ _ J) in H9. inv H9.
         rewrite Int.add_zero. 
         eapply agree_change_sp; eauto. congruence. simpl; congruence.
     destruct (parent_ra_zero_or_ptr _ _ _ STACKS).
     (*vzero*)
         rewrite H6 in *.  inv D. reflexivity. 
     (*ptr*)
         destruct H6 as [par_ra [par_ofs [ParRA J]]]. rewrite ParRA in *.
         inv D. rewrite (local_in_all _ WDR _ _ _ J) in H9. inv H9.
         rewrite Int.add_zero. reflexivity.
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
    rewrite restrict_sm_local in LocSP.
    destruct (restrictD_Some _ _ _ _ _ LocSP).
    apply local_in_all in H8; trivial.
    split. eapply visPropagate; eassumption.
    eapply FreeEffect_PropagateLeft; eassumption.

- (*internal function *) admit.

- (*external function*) admit.

- (* return *)
  inv STACKS. simpl in *.
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
  split. split; intuition. 
    econstructor; eauto. rewrite ATPC; eauto. congruence.
    right. rewrite restrict_sm_local in H6.
    destruct H6 as [spb [z [SP LOC]]].
    destruct (restrictD_Some _ _ _ _ _ LOC).
    destruct (local_DomRng _ H9 _ _ _ H3).
    exists spb, z; split; assumption.
  intuition.
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
assert (GDE: genvs_domain_eq ge tge).
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
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
    intros. destruct H as [MC [RC [PG [Glob [VAL WD]]]]].
    inv MC; simpl in H0. inv H0. inv H0.
    destruct s; simpl in *; try inv H0.
      remember (ms AX) as v.
      destruct v; inv H1.
      eexists. split. assumption.
      split. econstructor.
      rewrite ATPC; simpl.
      specialize (agree_mregs _ _ _ _ AG AX); rewrite <- Heqv; intros.
      inv H. trivial. }
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
