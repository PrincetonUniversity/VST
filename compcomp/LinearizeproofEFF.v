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

(** Correctness proof for code linearization *)

Require Import FSets.
Require Import Coqlib.
Require Import Maps.
Require Import Ordered.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Errors.
Require Import Smallstep.
Require Import Op.
Require Import Locations.

Require Import Mach.

Require Import LTL.
Require Import Linear.
Require Import Linearize.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.reach.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.
Require Import LTL_coop.
Require Import LTL_eff.
Require Import Linear_coop.
Require Import Linear_eff.


(*further down we also Require Import Mach. (*for RegEq.eq*)*)
Require Import OpEFF.

Module NodesetFacts := FSetFacts.Facts(Nodeset).

Section LINEARIZATION.

Variable prog: LTL.program.
Variable tprog: Linear.program.

Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf_partial transf_fundef _ TRANSF).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  Linear.funsig tf = LTL.funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. monadInv EQ. reflexivity.
  inv H. reflexivity.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transf_function f = OK tf ->
  Linear.fn_stacksize tf = LTL.fn_stacksize f.
Proof.
  intros. monadInv H. auto.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  LTL.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold LTL.find_function; intros; destruct ros; simpl.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** * Correctness of reachability analysis *)

(** The entry point of the function is reachable. *)

Lemma reachable_entrypoint:
  forall f, (reachable f)!!(f.(fn_entrypoint)) = true.
Proof.
  intros. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux; intros reach A.
  assert (LBoolean.ge reach!!(f.(fn_entrypoint)) true).
  eapply DS.fixpoint_entry. eexact A. auto with coqlib.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed.

(** The successors of a reachable instruction are reachable. *)

Lemma reachable_successors:
  forall f pc pc' b,
  f.(LTL.fn_code)!pc = Some b -> In pc' (successors_block b) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution; eauto.
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed.

(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that the result of the [enumerate] function satisfies both
conditions. *)

Lemma nodeset_of_list_correct:
  forall l s s',
  nodeset_of_list l s = OK s' ->
  list_norepet l
  /\ (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ In pc l)
  /\ (forall pc, In pc l -> ~Nodeset.In pc s).
Proof.
  induction l; simpl; intros. 
  inv H. split. constructor. split. intro; tauto. intros; tauto.
  generalize H; clear H; caseEq (Nodeset.mem a s); intros.
  inv H0.
  exploit IHl; eauto. intros [A [B C]].
  split. constructor; auto. red; intro. elim (C a H1). apply Nodeset.add_1. hnf. auto.
  split. intros. rewrite B. rewrite NodesetFacts.add_iff. 
  unfold Nodeset.E.eq. unfold OrderedPositive.eq. tauto.
  intros. destruct H1. subst pc. rewrite NodesetFacts.not_mem_iff. auto.
  generalize (C pc H1). rewrite NodesetFacts.add_iff. tauto.
Qed.

Lemma check_reachable_correct:
  forall f reach s pc i,
  check_reachable f reach s = true ->
  f.(LTL.fn_code)!pc = Some i ->
  reach!!pc = true ->
  Nodeset.In pc s.
Proof.
  intros f reach s.
  assert (forall l ok, 
    List.fold_left (fun a p => check_reachable_aux reach s a (fst p) (snd p)) l ok = true ->
    ok = true /\
    (forall pc i,
     In (pc, i) l ->
     reach!!pc = true ->
     Nodeset.In pc s)).
  induction l; simpl; intros.
  split. auto. intros. destruct H0.
  destruct a as [pc1 i1]. simpl in H. 
  exploit IHl; eauto. intros [A B].
  unfold check_reachable_aux in A. 
  split. destruct (reach!!pc1). elim (andb_prop _ _ A). auto. auto.
  intros. destruct H0. inv H0. rewrite H1 in A. destruct (andb_prop _ _ A). 
  apply Nodeset.mem_2; auto.
  eauto.

  intros pc i. unfold check_reachable. rewrite PTree.fold_spec. intros.
  exploit H; eauto. intros [A B]. eapply B; eauto. 
  apply PTree.elements_correct. eauto.
Qed.

Lemma enumerate_complete:
  forall f enum pc i,
  enumerate f = OK enum ->
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc enum.
Proof.
  intros until i. unfold enumerate. 
  set (reach := reachable f).
  intros. monadInv H. 
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit check_reachable_correct; eauto. intro.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]].
  rewrite B in H2. destruct H2. elim (Nodeset.empty_1 H2). auto.
Qed.

Lemma enumerate_norepet:
  forall f enum,
  enumerate f = OK enum ->
  list_norepet enum.
Proof.
  intros until enum. unfold enumerate. 
  set (reach := reachable f).
  intros. monadInv H. 
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]]. auto.
Qed.

(** * Properties related to labels *)

(** If labels are globally unique and the Linear code [c] contains
  a subsequence [Llabel lbl :: c1], then [find_label lbl c] returns [c1].
*)

Fixpoint unique_labels (c: code) : Prop :=
  match c with
  | nil => True
  | Llabel lbl :: c => ~(In (Llabel lbl) c) /\ unique_labels c
  | i :: c => unique_labels c
  end.

Lemma find_label_unique:
  forall lbl c1 c2 c3,
  is_tail (Llabel lbl :: c1) c2 ->
  unique_labels c2 ->
  find_label lbl c2 = Some c3 ->
  c1 = c3.
Proof.
  induction c2.
  simpl; intros; discriminate.
  intros c3 TAIL UNIQ. simpl.
  generalize (is_label_correct lbl a). case (is_label lbl a); intro ISLBL.
  subst a. intro. inversion TAIL. congruence. 
  elim UNIQ; intros. elim H4. apply is_tail_in with c1; auto.
  inversion TAIL. congruence. apply IHc2. auto. 
  destruct a; simpl in UNIQ; tauto.
Qed.

(** Correctness of the [starts_with] test. *)

Lemma starts_with_correct:
  forall lbl c1 c2 c3 s f sp ls m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  corestep_plus Linear_eff_sem tge
              (Linear_State s f sp c1 ls) m
              (Linear_State s f sp c3 ls) m.
Proof.
  induction c1.
  simpl; intros; discriminate.
  simpl starts_with. destruct a; try (intros; discriminate).
  intros. 
  eapply corestep_plus_star_trans with  (Linear_State s f sp c1 ls) m.
    apply corestep_plus_one. simpl. constructor. 
  destruct (peq lbl l).
    subst l. replace c3 with c1.
    apply corestep_star_zero. (*constructor.*)
    apply find_label_unique with lbl c2; auto.
  apply corestep_plus_star. 
    apply IHc1 with c2; auto.
    eapply is_tail_cons_left; eauto.
Qed.

Lemma starts_with_correct_eff:
  forall lbl c1 c2 c3 s f sp ls m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  effstep_plus Linear_eff_sem tge EmptyEffect
              (Linear_State s f sp c1 ls) m
              (Linear_State s f sp c3 ls) m.
Proof.
  induction c1.
  simpl; intros; discriminate.
  simpl starts_with. destruct a; try (intros; discriminate).
  intros. 
  eapply effstep_plus_star_trans'.
    (*ok bu unnecessaryinstantiate (2:=Linear_State s f sp c1 ls). instantiate (1:=m).*)
    apply effstep_plus_one. simpl. constructor. 
  destruct (peq lbl l).
    subst l. replace c3 with c1.
    apply effstep_star_zero. (*constructor.*)
    apply find_label_unique with lbl c2; auto.
  apply effstep_plus_star. 
    apply IHc1 with c2; auto.
    eapply is_tail_cons_left; eauto.
    intuition.
Qed.

(** Connection between [find_label] and linearization. *)

Lemma find_label_add_branch:
  forall lbl k s,
  find_label lbl (add_branch s k) = find_label lbl k.
Proof.
  intros. unfold add_branch. destruct (starts_with s k); auto.
Qed.

Lemma find_label_lin_block:
  forall lbl k b,
  find_label lbl (linearize_block b k) = find_label lbl k.
Proof.
  intros lbl k. generalize (find_label_add_branch lbl k); intro.
  induction b; simpl; auto. destruct a; simpl; auto. 
  case (starts_with s1 k); simpl; auto.
Qed.

Remark linearize_body_cons:
  forall f pc enum,
  linearize_body f (pc :: enum) =
  match f.(LTL.fn_code)!pc with
  | None => linearize_body f enum
  | Some b => Llabel pc :: linearize_block b (linearize_body f enum)
  end.
Proof.
  intros. unfold linearize_body. rewrite list_fold_right_eq. 
  unfold linearize_node. destruct (LTL.fn_code f)!pc; auto.
Qed.

Lemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  f.(LTL.fn_code)!pc = Some b ->
  exists k, find_label pc (linearize_body f enum) = Some (linearize_block b k).
Proof.
  induction enum; intros.
  elim H.
  rewrite linearize_body_cons. 
  destruct (peq a pc).
  subst a. exists (linearize_body f enum).
  rewrite H0. simpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  destruct (IHenum pc b H1 H0) as [k FIND].
  exists k. destruct (LTL.fn_code f)!a. 
  simpl. rewrite peq_false. rewrite find_label_lin_block. auto. auto.
  auto.
Qed.

Lemma find_label_lin:
  forall f tf pc b,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code tf) = Some (linearize_block b k).
Proof.
  intros. monadInv H. simpl. 
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

Lemma find_label_lin_inv:
  forall f tf pc b k,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code tf) = Some k ->
  exists k', k = linearize_block b k'.
Proof.
  intros. exploit find_label_lin; eauto. intros [k' FIND].
  exists k'. congruence.
Qed.

(** Unique label property for linearized code. *)

Lemma label_in_add_branch:
  forall lbl s k,
  In (Llabel lbl) (add_branch s k) -> In (Llabel lbl) k.
Proof.
  intros until k; unfold add_branch.
  destruct (starts_with s k); simpl; intuition congruence.
Qed.

Lemma label_in_lin_block:
  forall lbl k b,
  In (Llabel lbl) (linearize_block b k) -> In (Llabel lbl) k.
Proof.
  induction b; simpl; intros. auto.
  destruct a; simpl in H; try (intuition congruence).
  apply label_in_add_branch with s; intuition congruence.
  destruct (starts_with s1 k); simpl in H.
  apply label_in_add_branch with s1; intuition congruence.
  apply label_in_add_branch with s2; intuition congruence.
Qed.

Lemma label_in_lin_rec:
  forall f lbl enum,
  In (Llabel lbl) (linearize_body f enum) -> In lbl enum.
Proof.
  induction enum.
  simpl; auto.
  rewrite linearize_body_cons. destruct (LTL.fn_code f)!a. 
  simpl. intros [A|B]. left; congruence. 
  right. apply IHenum. eapply label_in_lin_block; eauto.
  intro; right; auto.
Qed.

Lemma unique_labels_add_branch:
  forall lbl k,
  unique_labels k -> unique_labels (add_branch lbl k).
Proof.
  intros; unfold add_branch. 
  destruct (starts_with lbl k); simpl; intuition.
Qed.

Lemma unique_labels_lin_block:
  forall k b,
  unique_labels k -> unique_labels (linearize_block b k).
Proof.
  induction b; intros; simpl. auto.
  destruct a; auto; try (apply unique_labels_add_branch; auto).
  case (starts_with s1 k); simpl; apply unique_labels_add_branch; auto.
Qed.

Lemma unique_labels_lin_rec:
  forall f enum,
  list_norepet enum ->
  unique_labels (linearize_body f enum).
Proof.
  induction enum.
  simpl; auto.
  rewrite linearize_body_cons.
  intro. destruct (LTL.fn_code f)!a. 
  simpl. split. red. intro. inversion H. elim H3.
  apply label_in_lin_rec with f. 
  apply label_in_lin_block with b. auto.
  apply unique_labels_lin_block. apply IHenum. inversion H; auto.
  apply IHenum. inversion H; auto.
Qed.

Lemma unique_labels_transf_function:
  forall f tf,
  transf_function f = OK tf ->
  unique_labels (fn_code tf).
Proof.
  intros. monadInv H. simpl.
  apply unique_labels_add_branch. 
  apply unique_labels_lin_rec. eapply enumerate_norepet; eauto.
Qed.

(** Correctness of [add_branch]. *)

Lemma is_tail_find_label:
  forall lbl c2 c1,
  find_label lbl c1 = Some c2 -> is_tail c2 c1.
Proof.
  induction c1; simpl.
  intros; discriminate.
  case (is_label lbl a). intro. injection H; intro. subst c2.
  constructor. constructor.
  intro. constructor. auto. 
Qed.

Lemma is_tail_add_branch:
  forall lbl c1 c2, is_tail (add_branch lbl c1) c2 -> is_tail c1 c2.
Proof.
  intros until c2. unfold add_branch. destruct (starts_with lbl c1).
  auto. eauto with coqlib.
Qed.

Lemma is_tail_lin_block:
  forall b c1 c2,
  is_tail (linearize_block b c1) c2 -> is_tail c1 c2.
Proof.
  induction b; simpl; intros.
  auto.
  destruct a; eauto with coqlib. 
  eapply is_tail_add_branch; eauto.
  destruct (starts_with s1 c1); eapply is_tail_add_branch; eauto with coqlib.
Qed.

Lemma add_branch_correct:
  forall lbl c k s f tf sp ls m,
  transf_function f = OK tf ->
  is_tail k tf.(fn_code) ->
  find_label lbl tf.(fn_code) = Some c ->
  corestep_plus Linear_eff_sem tge
               (Linear_State s tf sp (add_branch lbl k) ls) m
               (Linear_State s tf sp c ls) m.
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct; eauto.
  eapply unique_labels_transf_function; eauto.
  apply corestep_plus_one. apply lin_exec_Lgoto. auto.
Qed.

Lemma add_branch_correct_eff:
  forall lbl c k s f tf sp ls m,
  transf_function f = OK tf ->
  is_tail k tf.(fn_code) ->
  find_label lbl tf.(fn_code) = Some c ->
  effstep_plus Linear_eff_sem tge EmptyEffect
               (Linear_State s tf sp (add_branch lbl k) ls) m
               (Linear_State s tf sp c ls) m.
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct_eff; eauto.
  eapply unique_labels_transf_function; eauto.
  apply effstep_plus_one. apply lin_effexec_Lgoto. auto.
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

(*NEW, following what happens in Stackingproof
TODO: generalize to loc like this:
Definition agree_regs (j: meminj) (ls1: LTL.locset) (ls2: Linear.locset): Prop :=
  forall l, val_inject j (ls1 l) (ls2 l).

Lemma agree_regs_set:
  forall j ls1 ls2 l v v',
  agree_regs j ls1 ls2 ->
  val_inject j v v' ->
  agree_regs j (Locmap.set l v ls1) (Locmap.set l v' ls2).
Proof.
  intros; red; intros.
  destruct (Loc.diff l l0). follow stacking here
    subst.  
    repeat rewrite Locmap.gss; trivial.
  destruct l0. assumption.
    eapply val_load_result_inject; eassumption.
  repeat rewrite Locmap.gso. auto. red. auto. red. auto.
Qed.*)

Definition agree_regs (j: meminj) (ls1: LTL.locset) (ls2: Linear.locset): Prop :=
  forall r, val_inject j (ls1 (R r)) (ls2 (R r)).

Lemma agree_regs_call_regs j ls1 ls2 :
  agree_regs j ls1 ls2 ->
  agree_regs j (call_regs ls1) ls2.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

Lemma agree_regs_incr j k ls1 ls2: 
  agree_regs j ls1 ls2 -> inject_incr j k ->
  agree_regs k ls1 ls2.
Proof. intros. red; intros.
  eapply val_inject_incr; eauto.
Qed.

Lemma agree_find_function_translated:
  forall j ros ls1 ls2 f,
  meminj_preserves_globals ge j ->
  globalfunction_ptr_inject j ->
  agree_regs j ls1 ls2 ->
  LTL.find_function ge ros ls1 = Some f ->
(*  list_norepet (prog_defs_names prog) ->*)
  exists tf,
  find_function tge ros ls2 = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold LTL.find_function; intros; destruct ros; simpl.
  apply functions_translated.
    destruct (Genv.find_funct_inv _ _ H2) as [b Hb].
    specialize (H1 m). rewrite Hb in *. inv H1.
    rewrite Genv.find_funct_find_funct_ptr in H2.
    destruct (H0 _ _ H2).
    rewrite H1 in H6. inv H6.
    rewrite Int.add_zero. assumption.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

Lemma agree_regs_set:
  forall j ls1 ls2 r v v',
  agree_regs j ls1 ls2 ->
  val_inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls1) (Locmap.set (R r) v' ls2).
Proof.
  intros; red; intros.
  destruct (RegEq.eq r r0).
    subst.  
    repeat rewrite Locmap.gss; trivial.
  repeat rewrite Locmap.gso. auto. red. auto. red. auto.
Qed.

Lemma agree_regs_list j ls1 ls2: forall 
      (AG: agree_regs  j ls1 ls2) args,
      val_list_inject j (reglist ls1 args) (reglist ls2 args).
Proof. intros.
  induction args; econstructor; eauto.
Qed.

Lemma agree_regs_undef j: forall rl ls1 ls2 
        (AG: agree_regs j ls1 ls2),
     agree_regs j (undef_regs rl ls1) (undef_regs rl ls2).
Proof. intros rl.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set; auto.
Qed. 

Lemma agree_regs_return j: forall ls1 ls2 pls1 pls2
        (AG: agree_regs j ls1 ls2) 
        (parentsAGREE : agree_regs j pls1 pls2),
      agree_regs j (return_regs pls1 ls1) (return_regs pls2 ls2).
Proof. intros.
red; intros. unfold return_regs.
destruct (in_dec mreg_eq r Conventions1.destroyed_at_call).
  eapply AG. eapply parentsAGREE.
Qed.

Lemma agree_regs_map j ls1 ls2 f: forall 
      (AG: agree_regs  j ls1 ls2),
      val_list_inject j (map ls1 f) (map ls2 f).
Proof. intros.
  induction f; econstructor; eauto.
  destruct a. apply AG.
  admit. (*TODO : support S-constructor in agree*)
Qed.

Lemma agree_regs_set_regs:
  forall j rl vl vl' ls1 ls2,
  agree_regs j ls1 ls2 ->
  val_list_inject j vl vl' ->
  agree_regs j (Locmap.setlist (map R rl) vl ls1) (Locmap.setlist (map R rl) vl' ls2).
Proof.
  induction rl; simpl; intros. 
  auto.
  inv H0. auto.
  apply IHrl; auto. apply agree_regs_set; auto. 
Qed.
 
Lemma agree_regs_setlist j:
  forall l ls1 ls2 v v',
  agree_regs j ls1 ls2 ->
  val_list_inject j v v' ->
  agree_regs j (Locmap.setlist l v ls1) (Locmap.setlist l v' ls2).
Proof.
  induction l; simpl; intros. 
  auto.
  inv H0. auto.
  apply IHl; auto. destruct a.  apply agree_regs_set; auto.
  admit. (*TODO: Support S*) 
Qed.

(*NEW*) 
Definition sp_mapped mu sp1 sp2:=
  val_inject (local_of mu) sp1 sp2 /\
  (forall b z, sp1 = Vptr b z -> exists b', as_inj mu b = Some(b',0)).
 
Lemma sp_mapped_intern_incr mu mu' sp1 sp2: 
       sp_mapped mu sp1 sp2 -> intern_incr mu mu' -> SM_wd mu' ->
       sp_mapped mu' sp1 sp2.
Proof. intros.
  destruct H. split; intros.
    eapply val_inject_incr; try eassumption.
    eapply H0.
  destruct (H2 _ _ H3).
  exists x; eapply intern_incr_as_inj; try eassumption.
Qed.

Lemma sp_mapped_extern_incr mu mu' sp1 sp2: 
       sp_mapped mu sp1 sp2 -> extern_incr mu mu' -> SM_wd mu' ->
       sp_mapped mu' sp1 sp2.
Proof. intros.
  destruct H. split; intros.
    eapply val_inject_incr; try eassumption.
      assert (local_of mu = local_of mu') by eapply H0.
      rewrite H3; apply inject_incr_refl.
  destruct (H2 _ _ H3).
  exists x; eapply extern_incr_as_inj; try eassumption.
Qed.

(** * Correctness of linearization *)

(** The proof of semantic preservation is a simulation argument of the "star" kind:
<<
           st1 --------------- st2
            |                   |
           t|                  t| + or ( 0 \/ |st1'| < |st1| )
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant (horizontal lines above) is the [match_states]
  predicate defined below.  It captures the fact that the flow
  of data is the same in the source and linearized codes.
  Moreover, whenever the source state is at node [pc] in its
  control-flow graph, the transformed state is at a code
  sequence [c] that starts with the label [pc]. *)

Inductive match_stackframes mu : LTL.stackframe -> Linear.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp1 sp2 bb ls1 ls2 tf c,
      transf_function f = OK tf ->
      (forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true) ->
      is_tail c tf.(fn_code) ->
      (*NEW*) agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2 ->
      (*NEW*) sp_mapped mu sp1 sp2 -> (*val_inject (local_of mu) sp1 sp2 ->*)
      match_stackframes mu
        (LTL.Stackframe f sp1 ls1 bb)
        (Linear.Stackframe tf sp2 ls2 (linearize_block bb c)).

Lemma match_stackframes_intern_incr mu mu' s ts:
     match_stackframes mu s ts ->
     intern_incr mu mu' -> SM_wd mu' ->
     match_stackframes mu' s ts.
Proof. intros. inv H; econstructor; eauto.
  eapply agree_regs_incr; try eassumption.
    eapply intern_incr_restrict; try eassumption.
    eapply sp_mapped_intern_incr; eassumption.
Qed.

Lemma list_match_stackframes_intern_incr mu mu': forall s ts,
     list_forall2 (match_stackframes mu) s ts ->
     intern_incr mu mu' -> SM_wd mu' ->
     list_forall2 (match_stackframes mu') s ts.
Proof. intros.
  induction H; econstructor; eauto.
  eapply match_stackframes_intern_incr; eassumption.
Qed.

Lemma match_stackframes_extern_incr mu mu' s ts:
     match_stackframes mu s ts ->
     extern_incr mu mu' -> SM_wd mu' ->
     match_stackframes mu' s ts.
Proof. intros. inv H; econstructor; eauto.
  eapply agree_regs_incr; try eassumption.
    eapply extern_incr_restrict; try eassumption.
    eapply sp_mapped_extern_incr; eassumption.
Qed.

Lemma list_match_stackframes_extern_incr mu mu': forall s ts,
     list_forall2 (match_stackframes mu) s ts ->
     extern_incr mu mu' -> SM_wd mu' ->
     list_forall2 (match_stackframes mu') s ts.
Proof. intros.
  induction H; econstructor; eauto.
  eapply match_stackframes_extern_incr; eassumption.
Qed.

(*
Lemma agree_eval_addressing_inject mu ls1 ls2 addr sp1 sp2 args a: forall 
      (EV: eval_addressing ge sp1 addr (reglist ls1 args) = Some a)
      (PG : meminj_preserves_globals ge (as_inj mu))
      (Glob : forall b, isGlobalBlock ge b = true ->
              frgnBlocksSrc mu b = true)
      (WD : SM_wd mu)
      (AG : agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2)
      (SPLocal : val_inject (local_of (restrict_sm mu (vis mu))) sp1 sp2),
  exists a',
    eval_addressing ge sp2 addr (reglist ls2 args) = Some a' /\
    val_inject (as_inj (restrict_sm mu (vis mu))) a a'.
Proof. intros.
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
*)

Inductive match_states mu: LTL_core -> mem -> Linear_core -> mem -> Prop :=
  | match_states_add_branch:
      forall s f sp1 sp2 pc ls1 ls2 m1 m2 tf ts c
        (STACKS: list_forall2 (match_stackframes mu) s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (TAIL: is_tail c tf.(fn_code))
        (*NEW*) (AGREE: agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2)
        (*NEW*) (SPLocal: sp_mapped mu sp1 sp2),
      match_states mu (LTL_State s f sp1 pc ls1) m1
                     (Linear_State ts tf sp2 (add_branch pc c) ls2) m2
  | match_states_cond_taken:
      forall s f sp1 sp2 pc ls1 ls2 m1 m2 tf ts cond args c
        (STACKS: list_forall2 (match_stackframes mu) s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (JUMP: eval_condition cond (reglist ls1 args) m1 = Some true)
        (*NEW*) (AGREE: agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2)
        (*NEW*) (SPLocal: sp_mapped mu sp1 sp2),
      match_states mu (LTL_State s f sp1 pc (undef_regs (destroyed_by_cond cond) ls1)) m1
                     (Linear_State ts tf sp2 (Lcond cond args pc :: c) ls2) m2
  | match_states_jumptable:
      forall s f sp1 sp2 pc ls1 ls2 m1 m2 tf ts arg tbl c n
        (STACKS: list_forall2 (match_stackframes mu) s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (ARG: ls1 (R arg) = Vint n)
        (JUMP: list_nth_z tbl (Int.unsigned n) = Some pc)
        (*NEW*) (AGREE: agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2)
        (*NEW*) (SPLocal: sp_mapped mu sp1 sp2),
      match_states mu (LTL_State s f sp1 pc (undef_regs destroyed_by_jumptable ls1)) m1
                      (Linear_State ts tf sp2 (Ljumptable arg tbl :: c) ls2) m2
  | match_states_block:
      forall s f sp1 sp2 bb ls1 ls2 m1 m2 tf ts c
        (STACKS: list_forall2 (match_stackframes mu) s ts)
        (TRF: transf_function f = OK tf)
        (REACH: forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true)
        (TAIL: is_tail c tf.(fn_code))
        (*NEW*) (AGREE: agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2)
        (*NEW*) (SPLocal: sp_mapped mu sp1 sp2),
      match_states mu (LTL_Block s f sp1 bb ls1) m1
                      (Linear_State ts tf sp2 (linearize_block bb c) ls2) m2
  | match_states_call:
      forall s f ls1 ls2 m1 m2 tf ts,
      list_forall2 (match_stackframes mu) s ts ->
      transf_fundef f = OK tf ->
      (*NEW*) forall (AGREE: agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2),
      match_states mu (LTL_Callstate s f ls1) m1
                      (Linear_Callstate ts tf ls2) m2
  | match_states_return:
      forall s ls1 ls2 m1 m2 ts,
      list_forall2 (match_stackframes mu) s ts ->
      (*NEW*) forall (AGREE:agree_regs (restrict (as_inj mu) (vis mu)) ls1 ls2),
      match_states mu (LTL_Returnstate s ls1) m1
                      (Linear_Returnstate ts ls2) m2.

Definition measure (S: LTL_core) : nat :=
  match S with
  | LTL_State s f sp pc ls => 0%nat
  | LTL_Block s f sp bb ls => 1%nat
  | _ => 0%nat
  end.
(*
Remark match_parent_locset:
  forall mu s ts, list_forall2 (match_stackframes mu) s ts -> 
         parent_locset ts = LTL.parent_locset s.
Proof.
  induction 1; simpl. auto. inv H; auto. 
Qed.*)
Remark match_parent_locset:
  forall mu s ts, list_forall2 (match_stackframes mu) s ts -> 
  agree_regs (restrict (as_inj mu) (vis mu)) (LTL.parent_locset s) (parent_locset ts).
Proof. 
  induction 1; simpl. red; intros. auto. inv H; auto. 
Qed.

Definition MATCH mu c1 m1 c2 m2:Prop :=
  match_states (restrict_sm mu (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma MATCH_wd: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma MATCH_restrict: forall mu c1 m1 c2 m2 X
  (MC: MATCH mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m1 X), 
  MATCH (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
  rewrite restrict_sm_nest; intuition.
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

Lemma MATCH_valid: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), sm_valid mu m1 m2.
Proof. intros. eapply MC. Qed.

Lemma MATCH_PG: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2),
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

Lemma MATCH_afterExternal: forall
      (GDE : genvs_domain_eq ge tge)
      mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH mu st1 m1 st2 m2)
      (AtExtSrc : at_external LTL_eff_sem st1 = Some (e, ef_sig, vals1))
      (AtExtTgt : at_external Linear_eff_sem st2 = Some (e', ef_sig', vals2))
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
  after_external LTL_eff_sem (Some ret1) st1 =Some st1' /\
  after_external Linear_eff_sem (Some ret2) st2 = Some st2' /\
  MATCH mu' st1' m1' st2' m2'.
Proof. intros.
simpl.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H2. 
 destruct tf; inv AtExtTgt.
 eexists. eexists.
    split. reflexivity.
    split. reflexivity.
 simpl in *.
 inv H0.
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
  specialize (IHL _ H2); clear H2.
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
        apply (H0 VB) in H3.
        rewrite (H1 H3) in H5. clear H0 H1.
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
    apply andb_true_iff in H0. simpl in H0. 
    destruct H0 as [DomNu' Rb']. 
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
           specialize (RC' _ H0). 
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
     intros. specialize (Glob _ H0).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in Glob.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ Glob). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ Glob). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ Glob). intuition.
admit. (*TODO: finish once atExternal clause has been finalized
split. 
  econstructor; try eassumption.
    eapply list_match_stackframes_extern_incr; try eassumption.
    unfold vis in *.
      rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
      clear RRC RR1 RC' PHnu' INCvisNu' UnchLOOR UnchPrivSrc.
      destruct INC. rewrite replace_locals_extern in H0.
        rewrite replace_locals_frgnBlocksTgt, replace_locals_frgnBlocksSrc,
                replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc,
                replace_locals_locBlocksTgt, replace_locals_locBlocksSrc,
                replace_locals_extBlocksTgt, replace_locals_extBlocksSrc,
                replace_locals_local in H1.
        destruct H1 as [? [? [? [? [? [? [? [? ?]]]]]]]].
        red; intros. simpl.
        rewrite restrict_sm_frgnBlocksSrc, restrict_sm_frgnBlocksTgt,
                restrict_sm_locBlocksSrc, restrict_sm_locBlocksTgt,
                restrict_sm_pubBlocksSrc, restrict_sm_pubBlocksTgt,
                restrict_sm_extBlocksSrc, restrict_sm_extBlocksTgt,
                restrict_sm_local, restrict_sm_extern. 
        rewrite restrict_sm_frgnBlocksSrc, restrict_sm_frgnBlocksTgt,
                restrict_sm_locBlocksSrc, restrict_sm_locBlocksTgt,
                restrict_sm_pubBlocksSrc, restrict_sm_pubBlocksTgt,
                restrict_sm_extBlocksSrc, restrict_sm_extBlocksTgt,
                restrict_sm_local, restrict_sm_extern.
        rewrite replace_externs_frgnBlocksTgt, replace_externs_frgnBlocksSrc,
                replace_externs_pubBlocksTgt, replace_externs_pubBlocksSrc,
                replace_externs_locBlocksTgt, replace_externs_locBlocksSrc,
                replace_externs_extBlocksTgt, replace_externs_extBlocksSrc,
                replace_externs_local, replace_externs_extern.
        intuition.
        red; intros.
          destruct (restrictD_Some _ _ _ _ _ H10); clear H10.
          apply restrictI_Some. eapply H0. assumption.
          rewrite H4, H8 in H12.
            remember (locBlocksSrc nu' b) as d.
            destruct d; trivial; simpl in *.
            apply andb_true_iff.
            split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H12). intuition.
               apply REACH_nil. unfold exportedSrc. 
                 apply frgnSrc_shared in H12; trivial. rewrite H12; intuition.
        rewrite H1, H4, H8. unfold restrict. 
          extensionality b. 
          remember (locBlocksSrc nu' b) as d.
            destruct d; simpl in *. trivial.
          remember (frgnBlocksSrc nu' b) as q.
            destruct q; simpl in *.
              apply eq_sym in Heqq. 
              unfold DomSrc. rewrite <- Heqd, (frgnBlocksSrc_extBlocksSrc _ WDnu' _ Heqq). simpl.
              assert (REACH m1' (exportedSrc nu' (ret1 :: nil)) b = true).
                apply REACH_nil. unfold exportedSrc. 
                 apply frgnSrc_shared in Heqq; trivial. rewrite Heqq; intuition.
              rewrite H10; trivial.
          
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
*)
Qed. 


Lemma MATCH_corediagram: forall st1 m1 st1' m1'
         (CS:corestep LTL_eff_sem ge st1 m1 st1' m1')
         st2 mu m2 (MTCH:MATCH mu st1 m1 st2 m2),
exists st2' m2', 
  (corestep_plus Linear_eff_sem tge st2 m2 st2' m2' \/
   (measure st1' < measure st1)%nat /\
   corestep_star Linear_eff_sem tge st2 m2 st2' m2')
/\ exists mu',
  intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m2 /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  MATCH mu' st1' m1' st2' m2'.
Proof. intros.
  destruct MTCH as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (GDEQ: genvs_domain_eq ge tge).
   clear -ge tge. unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
  induction CS; intros; try (inv MS).

  (* start of block, at an [add_branch] *)
  exploit find_label_lin; eauto. intros [k F]. 
  eexists; eexists; split. 
    left. eapply add_branch_correct; eauto.
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
    intros; eapply reachable_successors; eauto.
    eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Lcond] *)
  exploit find_label_lin; eauto. intros [k F]. 
  eexists; eexists; split. 
    left. apply corestep_plus_one. eapply lin_exec_Lcond_true; eauto. 
    eapply eval_condition_inject; try eassumption.
    clear - AGREE. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE.
    induction args; simpl. constructor.
    econstructor; trivial. 
     eapply val_inject_incr; try eapply AGREE.
     apply restrict_incr. trivial.
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
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Ljumptable] *)
  exploit find_label_lin; eauto. intros [k F].
  eexists; eexists; split.
  left. apply corestep_plus_one.
        eapply lin_exec_Ljumptable; eauto. 
         specialize (AGREE arg). rewrite vis_restrict_sm, restrict_sm_all, restrict_nest, ARG in AGREE.
         inv AGREE. trivial. trivial.
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
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* Lop *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit (eval_operation_inject'' _ _ ge (as_inj (restrict_sm mu (vis mu)))).
    eapply val_inject_incr; try eapply SPLocal. 
      apply local_in_all.
      apply restrict_sm_WD. assumption. trivial.
    eapply restrict_sm_preserves_globals. assumption.
      unfold vis. intuition.
    eapply agree_regs_list. rewrite restrict_sm_all. eassumption.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [v2 [EVALOP' VINJ]]. (* specialize eval_operation_preserved. *)
  eexists; eexists; split. 
  left. apply corestep_plus_one. econstructor; eauto. 
     rewrite (eval_operation_preserved ge). eassumption. 
       exact symbols_preserved.
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
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite restrict_sm_all in VINJ.
    eapply agree_regs_set; try eassumption.
    eapply agree_regs_undef; eassumption.

  (* Lload *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
      eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis; intuition.
  assert (SA: forall (id : ident) (ofs : int),
      val_inject (as_inj (restrict_sm mu (vis mu))) (symbol_address ge id ofs) (symbol_address ge id ofs)).
    intros. eapply symbol_address_inject; try eapply PGR. 
  exploit (eval_addressing_inj ge SA); try eassumption.
     eapply val_inject_incr; try eapply SPLocal. 
       eapply local_in_all; try eassumption.
     rewrite restrict_sm_all. eapply agree_regs_list; try eassumption.
  intros [a' [EA' VA]]. 
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0. 
    apply VA. 
  intros [v' [C D]].
  eexists; eexists; split. 
  left. apply corestep_plus_one. econstructor.  
          instantiate (1 := a'). rewrite <- EA'.
          eapply eval_addressing_preserved. 
           exact symbols_preserved.
          eauto. eauto. 
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
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite restrict_sm_all in D.
    eapply agree_regs_set; try eassumption.

  (* Lgetstack *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  eexists; eexists; split. 
    left. apply corestep_plus_one. econstructor; eauto.
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
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  eapply agree_regs_set; try eassumption.
    eapply agree_regs_undef; eassumption.
    simpl. admit. (*TODO: include S-constructor in AGREE above*)

  (* Lsetstack *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  eexists; eexists; split. 
    left. apply corestep_plus_one. econstructor; eauto. 
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
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    admit. (*TODO: include S-constructor in AGREE above*)

  (* Lstore *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
      eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis; intuition.
  assert (SA: forall (id : ident) (ofs : int),
      val_inject (as_inj (restrict_sm mu (vis mu))) (symbol_address ge id ofs) (symbol_address ge id ofs)).
    intros. eapply symbol_address_inject; try eapply PGR. 
  exploit (eval_addressing_inj ge SA); try eassumption.
     eapply val_inject_incr; try eapply SPLocal. 
       eapply local_in_all; try eassumption.
     rewrite restrict_sm_all. eapply agree_regs_list; try eassumption.
  intros [a' [EA' VA]]. 
  exploit (Mem.storev_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_all in VA.
      eapply val_inject_incr; try eapply VA. apply restrict_incr.
    eapply val_inject_incr; try eapply AGREE. apply restrict_incr.
  intros [m2' [C D]].
  eexists; eexists; split. 
  left. apply corestep_plus_one. econstructor. 
     instantiate (1 := a'). rewrite <- EA'; apply eval_addressing_preserved. 
     exact symbols_preserved. eauto. eauto.
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
  rewrite restrict_sm_all in VA. inv VA.
  destruct (restrictD_Some _ _ _ _ _ H3).
  simpl in C.
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption. 
  split; intuition. 
  econstructor; eauto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    eapply agree_regs_undef; eassumption.
  eapply REACH_Store; try eassumption. 
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (AGREE src). 
                   rewrite H4 in AGREE; inv AGREE.   
                   destruct (restrictD_Some _ _ _ _ _ H8); trivial.

  (* Lcall *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit agree_find_function_translated; try eassumption.
    eapply agree_regs_incr; try eapply AGREE. apply restrict_incr. 
  intros [tfd [A B]].
  eexists; eexists; split. 
  left. apply corestep_plus_one. econstructor; eauto.
    symmetry; eapply sig_preserved; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. fold linearize_block.
  econstructor; eauto. constructor; auto. econstructor; eauto.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.

  (* Ltailcall *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  specialize (match_parent_locset _ _ _ STACKS); intros parentsAGREE.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in parentsAGREE; trivial.
  assert (AGREERET: agree_regs (restrict (as_inj mu) (vis mu)) (return_regs (LTL.parent_locset s) rs) (return_regs (parent_locset ts) ls2)).
     eapply agree_regs_return; eassumption. 
  exploit agree_find_function_translated; try eassumption.
    eapply agree_regs_incr; try eapply AGREERET. apply restrict_incr.
  intros [tfd [A B]].
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  destruct SPLocal as [SPL1 SPL2]. inv SPL1. 
  destruct (SPL2 _ _ (eq_refl _)) as [spb SPB]; clear SPL2.
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply restrictD_Some. rewrite restrict_sm_all in SPB; eassumption.
  simpl in H; rewrite Zplus_0_r in H.
  rewrite (local_in_all _ WDR _ _ _ H3) in SPB; inv SPB.
  eexists; eexists; split. 
  left. apply corestep_plus_one. econstructor; eauto.
    symmetry; eapply sig_preserved; eauto.
    rewrite (stacksize_preserved _ _ TRF); eauto. 
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
  split. econstructor; eauto.
           rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  intuition.
      eapply REACH_closed_free; try eassumption.

  (* Lbuiltin 
  eexists; eexists; split. 
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lbuiltin; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.*)

  (* Lannot 
  eexists; eexists; split. 
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lannot; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.*)

  (* Lbranch *)
  eexists; eexists; split. 
  assert ((reachable f)!!pc = true). apply REACH; simpl; auto.
  right; split. simpl; omega. eapply corestep_star_zero.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. econstructor; eauto. apply REACH. left. trivial. 

  (* Lcond *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit eval_condition_inject; try eassumption.
    eapply agree_regs_list; try eassumption.
    eapply agree_regs_incr; try eassumption. apply restrict_incr.
  intros EC. 
  assert (REACH1: (reachable f)!!pc1 = true) by (apply REACH; simpl; auto).
  assert (REACH2: (reachable f)!!pc2 = true) by (apply REACH; simpl; auto).
  simpl linearize_block.
  destruct (starts_with pc1 c).
  (* branch if cond is false *)
  assert (DC: destroyed_by_cond (negate_condition cond) = destroyed_by_cond cond).
    destruct cond; reflexivity.
  destruct b.
  (* cond is true: no branch *)
  eexists; eexists; split.
    left. apply corestep_plus_one. eapply lin_exec_Lcond_false.
          rewrite eval_negate_condition. rewrite EC. auto. eauto.
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
    rewrite DC. econstructor; eauto. 
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* cond is false: branch is taken *)
  eexists; eexists; split.
    right; split. simpl; omega. eapply corestep_star_zero.
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
     rewrite <- DC. econstructor; eauto. 
       rewrite eval_negate_condition. rewrite H. auto.
     rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* branch if cond is true *)
  destruct b.
  (* cond is true: branch is taken *)
  eexists; eexists; split.
    right; split. simpl; omega. eapply corestep_star_zero.
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
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* cond is false: no branch *)
  eexists; eexists; split.
  left. apply corestep_plus_one. eapply lin_exec_Lcond_false. eauto. eauto. 
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
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* Ljumptable *)
  assert (REACH': (reachable f)!!pc = true).
    apply REACH. simpl. eapply list_nth_z_in; eauto. 
  eexists; eexists; split.
  right; split. simpl; omega.  eapply corestep_star_zero.
    exists mu.
    split. apply intern_incr_refl. 
    split. apply sm_inject_separated_same_sminj.
    split. rewrite sm_locally_allocatedChar.
        intuition. 
        apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
        apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
        apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
        apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
    split; intuition. econstructor; eauto.

  (* Lreturn *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  destruct SPLocal as [SPL1 SPL2]; inv SPL1.
  destruct (SPL2 _ _ (eq_refl _)) as [spb SPB]; clear SPL2.
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply restrictD_Some. rewrite restrict_sm_all in SPB; eassumption.
  simpl in H0; rewrite Zplus_0_r in H0.
  rewrite (local_in_all _ WDR _ _ _ H2) in SPB; inv SPB.
  eexists; eexists; split. 
  left. apply corestep_plus_one. econstructor; eauto.
    rewrite (stacksize_preserved _ _ TRF). eauto.
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
  split. econstructor; eauto.
           eapply agree_regs_return. 
             rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
             apply (match_parent_locset _ _ _ STACKS).
  intuition.
      eapply REACH_closed_free; try eassumption.

  (* internal functions *)
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  monadInv H8.
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [IntInc [mu'SP mu'MuR]]]]]]]; eauto; try apply Zle_refl.
  eexists; eexists; split. 
  left. apply corestep_plus_one. eapply lin_exec_function_internal; eauto. 
          rewrite (stacksize_preserved _ _ EQ). eauto.
  destruct mu'MuR as [A [B [C [D [E F]]]]].
  exists mu'. 
  split. assumption.
  split. assumption.
  split. assumption.
  split.
    generalize EQ; intro EQ'; monadInv EQ'. simpl. 
    econstructor; eauto.
      eapply list_match_stackframes_intern_incr; try eassumption.
        eapply restrict_sm_intern_incr; eassumption.
        apply restrict_sm_WD; try eassumption. trivial.
      simpl. eapply is_tail_add_branch. constructor.      
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
        eapply agree_regs_undef.
        eapply agree_regs_call_regs.
        eapply agree_regs_incr. eassumption. apply intern_incr_restrict; eassumption.
      destruct (joinD_Some _ _ _ _ _ mu'SP) as [EXT | [EXT LOC]]; clear mu'SP.
        assert (extern_of mu = extern_of mu') by eapply IntInc.
        rewrite <- H0 in EXT; clear H0.
        elim (Mem.fresh_block_alloc _ _ _ _ _ H).
        eapply SMV. 
          eapply as_inj_DomRng; trivial.
          apply extern_in_all; eassumption.
      split. rewrite restrict_sm_local.
        econstructor. apply restrictI_Some; try eassumption.
          unfold vis. destruct (local_DomRng _ D _ _ _ LOC). rewrite H0; trivial.
        rewrite Int.add_zero. trivial. 
      intros. inv H0. rewrite restrict_sm_all.
         eexists. apply restrictI_Some. apply local_in_all; eassumption.
           unfold vis. destruct (local_DomRng _ D _ _ _ LOC). rewrite H0; trivial.
  (*as in selectionproofEff*)
    intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros. apply as_inj_DomRng in H1.
              split; eapply SMV; eapply H1.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H1). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
      apply Glob in H1. rewrite <-FF; trivial.

  (* no external function *)

  (* return *) 
  inv H4. inv H1.
  eexists; eexists; split.
  left. apply corestep_plus_one. econstructor.
  exists mu.
  intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      split. econstructor; eauto.
    intuition.
Qed.

Lemma MATCH_effcorediagram: forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
       (CS:effstep LTL_eff_sem ge U1 st1 m1 st1' m1')
       st2 mu m2 (U1Vis: forall b ofs, U1 b ofs = true -> vis mu b = true)
       (MTCH: MATCH mu st1 m1 st2 m2),
exists st2' m2' (U2 : block -> Z -> bool),
     (effstep_plus Linear_eff_sem tge U2 st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
      effstep_star Linear_eff_sem tge U2 st2 m2 st2' m2') 
/\ exists mu',
  intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m2 /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  MATCH mu' st1' m1' st2' m2' /\
     (forall (b : block) (ofs : Z),
      U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros.
  destruct MTCH as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (GDEQ: genvs_domain_eq ge tge).
   clear -ge tge. unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
  induction CS; intros; try (inv MS).

  (* start of block, at an [add_branch] *)
  exploit find_label_lin; eauto. intros [k F]. 
  eexists; eexists; eexists; split. 
    left. eapply add_branch_correct_eff; eauto.
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
  split; intuition. 
    econstructor; eauto. 
    intros; eapply reachable_successors; eauto.
    eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Lcond] *)
  exploit find_label_lin; eauto. intros [k F]. 
  eexists; eexists; eexists; split. 
    left. apply effstep_plus_one. eapply lin_effexec_Lcond_true; eauto. 
    eapply eval_condition_inject; try eassumption.
    clear - AGREE. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE.
    induction args; simpl. constructor.
    econstructor; trivial. 
     eapply val_inject_incr; try eapply AGREE.
     apply restrict_incr. trivial.
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
  split; intuition. 
  econstructor; eauto. 
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Ljumptable] *)
  exploit find_label_lin; eauto. intros [k F].
  eexists; eexists; eexists; split.
  left. apply effstep_plus_one.
        eapply lin_effexec_Ljumptable; eauto. 
         specialize (AGREE arg). rewrite vis_restrict_sm, restrict_sm_all, restrict_nest, ARG in AGREE.
         inv AGREE. trivial. trivial.
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
  split; intuition. 
  econstructor; eauto. 
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* Lop *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit (eval_operation_inject'' _ _ ge (as_inj (restrict_sm mu (vis mu)))).
    eapply val_inject_incr; try eapply SPLocal. 
      apply local_in_all.
      apply restrict_sm_WD. assumption. trivial.
    eapply restrict_sm_preserves_globals. assumption.
      unfold vis. intuition.
    eapply agree_regs_list. rewrite restrict_sm_all. eassumption.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [v2 [EVALOP' VINJ]]. (* specialize eval_operation_preserved. *)
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. econstructor; eauto. 
     rewrite (eval_operation_preserved ge). eassumption. 
       exact symbols_preserved.
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
  split; intuition. 
  econstructor; eauto. 
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite restrict_sm_all in VINJ.
    eapply agree_regs_set; try eassumption.
    eapply agree_regs_undef; eassumption.

  (* Lload *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
      eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis; intuition.
  assert (SA: forall (id : ident) (ofs : int),
      val_inject (as_inj (restrict_sm mu (vis mu))) (symbol_address ge id ofs) (symbol_address ge id ofs)).
    intros. eapply symbol_address_inject; try eapply PGR. 
  exploit (eval_addressing_inj ge SA); try eassumption.
     eapply val_inject_incr; try eapply SPLocal. 
       eapply local_in_all; try eassumption.
     rewrite restrict_sm_all. eapply agree_regs_list; try eassumption.
  intros [a' [EA' VA]]. 
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H0. 
    apply VA. 
  intros [v' [C D]].
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. econstructor.  
          instantiate (1 := a'). rewrite <- EA'.
          eapply eval_addressing_preserved. 
           exact symbols_preserved.
          eauto. eauto. 
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
  split; intuition. 
  econstructor; eauto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite restrict_sm_all in D.
    eapply agree_regs_set; try eassumption.

  (* Lgetstack *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  eexists; eexists; eexists; split. 
    left. apply effstep_plus_one. econstructor; eauto.
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
  split; intuition. 
  econstructor; eauto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  eapply agree_regs_set; try eassumption.
    eapply agree_regs_undef; eassumption.
    simpl. admit. (*TODO: include S-constructor in AGREE above*)

  (* Lsetstack *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  eexists; eexists; eexists; split. 
    left. apply effstep_plus_one. econstructor; eauto. 
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
  split; intuition. 
  econstructor; eauto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    admit. (*TODO: include S-constructor in AGREE above*)

  (* Lstore *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
      eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis; intuition.
  assert (SA: forall (id : ident) (ofs : int),
      val_inject (as_inj (restrict_sm mu (vis mu))) (symbol_address ge id ofs) (symbol_address ge id ofs)).
    intros. eapply symbol_address_inject; try eapply PGR. 
  exploit (eval_addressing_inj ge SA); try eassumption.
     eapply val_inject_incr; try eapply SPLocal. 
       eapply local_in_all; try eassumption.
     rewrite restrict_sm_all. eapply agree_regs_list; try eassumption.
  intros [a' [EA' VA]]. 
  exploit (Mem.storev_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_all in VA.
      eapply val_inject_incr; try eapply VA. apply restrict_incr.
    eapply val_inject_incr; try eapply AGREE. apply restrict_incr.
  intros [m2' [C D]].
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. econstructor. 
     instantiate (1 := a'). rewrite <- EA'; apply eval_addressing_preserved. 
     exact symbols_preserved. eauto. eauto.
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
  rewrite restrict_sm_all in VA. inv VA.
  destruct (restrictD_Some _ _ _ _ _ H3).
  simpl in C.
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption. 
  split; intuition.
    split; intuition. 
    econstructor; eauto.
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
        eapply agree_regs_undef; eassumption.
      eapply REACH_Store; try eassumption. 
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (AGREE src). 
                   rewrite H4 in AGREE; inv AGREE.   
                   destruct (restrictD_Some _ _ _ _ _ H8); trivial.
    intros. apply StoreEffectD in H4. destruct H4 as [z [HI Ibounds]].
            apply eq_sym in HI. inv HI. 
            eapply visPropagateR; eassumption.
    eapply StoreEffect_PropagateLeft; try eassumption.
     econstructor. eassumption. trivial.
     apply C.
    
  (* Lcall *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit agree_find_function_translated; try eassumption.
    eapply agree_regs_incr; try eapply AGREE. apply restrict_incr. 
  intros [tfd [A B]].
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. econstructor; eauto.
    symmetry; eapply sig_preserved; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. rewrite sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split; intuition. fold linearize_block.
  split; intuition.
  econstructor; eauto. constructor; auto. econstructor; eauto.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.

  (* Ltailcall *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  specialize (match_parent_locset _ _ _ STACKS); intros parentsAGREE.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in parentsAGREE; trivial.
  assert (AGREERET: agree_regs (restrict (as_inj mu) (vis mu)) (return_regs (LTL.parent_locset s) rs) (return_regs (parent_locset ts) ls2)).
     eapply agree_regs_return; eassumption. 
  exploit agree_find_function_translated; try eassumption.
    eapply agree_regs_incr; try eapply AGREERET. apply restrict_incr.
  intros [tfd [A B]].
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  destruct SPLocal as [SPL1 SPL2]. inv SPL1. 
  destruct (SPL2 _ _ (eq_refl _)) as [spb SPB]; clear SPL2.
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply restrictD_Some. rewrite restrict_sm_all in SPB; eassumption.
  simpl in H; rewrite Zplus_0_r in H.
  rewrite (local_in_all _ WDR _ _ _ H3) in SPB; inv SPB.
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. econstructor; eauto.
    symmetry; eapply sig_preserved; eauto.
    rewrite (stacksize_preserved _ _ TRF); eauto. 
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
  split.
    split. econstructor; eauto.
           rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  intuition.
      eapply REACH_closed_free; try eassumption.
  intros.
    apply local_in_all in H3; trivial.
    rewrite restrict_sm_all in H3.
    destruct (restrictD_Some _ _ _ _ _ H3).
    split. apply FreeEffectD in H4.
           destruct H4; subst. 
           eapply visPropagate; try eassumption.
    eapply FreeEffect_PropagateLeft; try eassumption.
    rewrite <- (stacksize_preserved _ _ TRF); eauto. 
     
  (* Lbuiltin 
  eexists; eexists; split. 
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lbuiltin; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.*)

  (* Lannot 
  eexists; eexists; split. 
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lannot; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.*)

  (* Lbranch *)
  eexists; eexists; eexists; split. 
  assert ((reachable f)!!pc = true). apply REACH; simpl; auto.
  right; split. simpl; omega. eapply effstep_star_zero.
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
  split; intuition. econstructor; eauto. apply REACH. left. trivial. 

  (* Lcond *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit eval_condition_inject; try eassumption.
    eapply agree_regs_list; try eassumption.
    eapply agree_regs_incr; try eassumption. apply restrict_incr.
  intros EC. 
  assert (REACH1: (reachable f)!!pc1 = true) by (apply REACH; simpl; auto).
  assert (REACH2: (reachable f)!!pc2 = true) by (apply REACH; simpl; auto).
  simpl linearize_block.
  destruct (starts_with pc1 c).
  (* branch if cond is false *)
  assert (DC: destroyed_by_cond (negate_condition cond) = destroyed_by_cond cond).
    destruct cond; reflexivity.
  destruct b.
  (* cond is true: no branch *)
  eexists; eexists; eexists; split.
    left. apply effstep_plus_one. eapply lin_effexec_Lcond_false.
          rewrite eval_negate_condition. rewrite EC. auto. eauto.
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
    split; intuition.
    rewrite DC. econstructor; eauto. 
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* cond is false: branch is taken *)
  eexists; eexists; eexists; split.
    right; split. simpl; omega. eapply effstep_star_zero.
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
    split; intuition.
     rewrite <- DC. econstructor; eauto. 
       rewrite eval_negate_condition. rewrite H. auto.
     rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* branch if cond is true *)
  destruct b.
  (* cond is true: branch is taken *)
  eexists; eexists; eexists; split.
    right; split. simpl; omega. eapply effstep_star_zero.
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
    split; intuition.
      econstructor; eauto. 
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* cond is false: no branch *)
  eexists; eexists; eexists; split.
  left. apply effstep_plus_one. eapply lin_effexec_Lcond_false. eauto. eauto. 
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
    split; intuition.
      econstructor; eauto.
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
  (* Ljumptable *)
  assert (REACH': (reachable f)!!pc = true).
    apply REACH. simpl. eapply list_nth_z_in; eauto. 
  eexists; eexists; eexists; split.
  right; split. simpl; omega. eapply effstep_star_zero.
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
    split; intuition. econstructor; eauto.

  (* Lreturn *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  destruct SPLocal as [SPL1 SPL2]; inv SPL1.
  destruct (SPL2 _ _ (eq_refl _)) as [spb SPB]; clear SPL2.
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply restrictD_Some. rewrite restrict_sm_all in SPB; eassumption.
  simpl in H0; rewrite Zplus_0_r in H0.
  rewrite (local_in_all _ WDR _ _ _ H2) in SPB; inv SPB.
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. econstructor; eauto.
    rewrite (stacksize_preserved _ _ TRF). eauto.
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
  split.
    split. econstructor; eauto.
           eapply agree_regs_return. 
             rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
             apply (match_parent_locset _ _ _ STACKS).
    intuition.
      eapply REACH_closed_free; try eassumption.
  intros.
    apply local_in_all in H2; trivial.
    rewrite restrict_sm_all in H2.
    destruct (restrictD_Some _ _ _ _ _ H2).
    split. apply FreeEffectD in H3.
           destruct H3; subst. 
           eapply visPropagate; try eassumption.
    eapply FreeEffect_PropagateLeft; try eassumption.
    rewrite <- (stacksize_preserved _ _ TRF); eauto.  

  (* internal functions *)
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  monadInv H8.
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [IntInc [mu'SP mu'MuR]]]]]]]; eauto; try apply Zle_refl.
  eexists; eexists; eexists; split. 
  left. apply effstep_plus_one. eapply lin_effexec_function_internal; eauto. 
          rewrite (stacksize_preserved _ _ EQ). eauto.
  destruct mu'MuR as [A [B [C [D [E F]]]]].
  exists mu'. 
  split. assumption.
  split. assumption.
  split. assumption.
  split.
   split. generalize EQ; intro EQ'; monadInv EQ'. simpl. 
    econstructor; eauto.
      eapply list_match_stackframes_intern_incr; try eassumption.
        eapply restrict_sm_intern_incr; eassumption.
        apply restrict_sm_WD; try eassumption. trivial.
      simpl. eapply is_tail_add_branch. constructor.      
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
        eapply agree_regs_undef.
        eapply agree_regs_call_regs.
        eapply agree_regs_incr. eassumption. apply intern_incr_restrict; eassumption.
      destruct (joinD_Some _ _ _ _ _ mu'SP) as [EXT | [EXT LOC]]; clear mu'SP.
        assert (extern_of mu = extern_of mu') by eapply IntInc.
        rewrite <- H0 in EXT; clear H0.
        elim (Mem.fresh_block_alloc _ _ _ _ _ H).
        eapply SMV. 
          eapply as_inj_DomRng; trivial.
          apply extern_in_all; eassumption.
      split. rewrite restrict_sm_local.
        econstructor. apply restrictI_Some; try eassumption.
          unfold vis. destruct (local_DomRng _ D _ _ _ LOC). rewrite H0; trivial.
        rewrite Int.add_zero. trivial. 
      intros. inv H0. rewrite restrict_sm_all.
         eexists. apply restrictI_Some. apply local_in_all; eassumption.
           unfold vis. destruct (local_DomRng _ D _ _ _ LOC). rewrite H0; trivial.
   (*as in selectionproofEff*)
     intuition.
     apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
       intros. apply as_inj_DomRng in H1.
               split; eapply SMV; eapply H1.
       assumption.
       apply intern_incr_as_inj; eassumption.
       apply sm_inject_separated_mem. assumption.
       assumption.
     red; intros. destruct (GFP _ _ H1). split; trivial.
          eapply intern_incr_as_inj; eassumption.
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
       apply Glob in H1. rewrite <-FF; trivial.
  intuition.

  (* no external function *)

  (* return *) 
  inv H4. inv H1.
  eexists; eexists; eexists; split.
  left. apply effstep_plus_one. econstructor.
  exists mu.
  intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      split. econstructor; eauto.
    intuition.
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
      (Ini: initial_core LTL_eff_sem ge v1 vals1 = Some c1)
      (Inj: Mem.inject j m1 m2)
      (VInj: Forall2 (val_inject j) vals1 vals2)
      (PG:meminj_preserves_globals ge j)
      (R : list_norepet (map fst (prog_defs prog)))
      (J: forall b1 b2 delta, j b1 = Some (b2, delta) -> 
            (DomS b1 = true /\ DomT b2 = true))
      (RCH1: forall b, REACH m1 
        (fun b' : Values.block => isGlobalBlock ge b' || getBlocks vals1 b') b =
         true -> DomS b = true)
      (RCH2: forall b, REACH m2 
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
      (RCL: REACH_closed m1 DomS) 
      (MS: forall b1, DomS b1=true -> exists b2 d, j b1 = Some(b2,d) /\ DomT b2=true)
      (InitMem : exists m0 : mem, Genv.init_mem prog = Some m0 
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m1) 
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))   
      (GDE: genvs_domain_eq ge tge)
      (HDomS: forall b : block, DomS b = true -> Mem.valid_block m1 b)
      (HDomT: forall b : block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core Linear_eff_sem tge v2 vals2 = Some c2 /\
  MATCH (initial_SM DomS DomT DomS DomT j) c1 m1 c2 m2.
Proof. intros.
  inversion Ini.
  unfold LTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  exists (Linear_Callstate nil tf
            (Locmap.setlist (Conventions1.loc_arguments (funsig tf)) vals2
              (Locmap.init Vundef))).
  split.
    destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. rewrite C in Heqzz. inv Heqzz.
    unfold tge in FP. rewrite D in FP. inv FP.
    unfold Linear_eff_sem, Linear_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    solve[rewrite D; auto].

    intros CONTRA.
    solve[elimtype False; auto].
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH1 RCH2 PG GDE MS HDomS HDomT RCL _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    eapply match_states_call; try eassumption.
      constructor.
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest.
        rewrite initial_SM_as_inj.
            admit. (*arguments are S-slots*)
        intros. trivial.
    unfold vis. simpl. split. assumption.
    rewrite initial_SM_as_inj.
  intuition.
      red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         destruct InitMem as [m0 [INIT_MEM [? ?]]].
         specialize (H0 _ _ _ INIT_MEM H). 
         destruct (valid_init_is_global _ R _ INIT_MEM _ H0) as [id Hid]. 
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock. 
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
Qed.

(*program structure not yet updated to module*)
Theorem transl_program_correct:
  forall (*(TRANSL: sel_program prog = OK tprog)*)
         (LNR: list_norepet (map fst (prog_defs prog)))
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
SM_simulation.SM_simulation_inject LTL_eff_sem 
  Linear_eff_sem ge tge entrypoints.
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
    rewrite varinfo_preserved. split; intros; trivial.
 eapply sepcomp.effect_simulations_lemmas.inj_simulation_plus with
  (match_states:=fun x mu st m st' m' => MATCH mu st m st' m')
  (measure:=measure).
(*genvs_dom_eq*)
  assumption.
(*match_wd*)
  intros; apply H.
(*match_visible*)
  intros. apply H.
(*match_restrict*)
  intros x. apply MATCH_restrict.
(*match_valid*)
  intros. apply H.
(*match_genv*)
  intros x. eapply MATCH_PG. 
(*initial_core*)
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
    clear - H11; unfold Mem.valid_block in H11.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H11; unfold Mem.valid_block in H11.
    xomega.
    
    intros b LT.    
    unfold ge. 
    apply valid_init_is_global with (b0 := b) in INIT.
    eapply INIT; auto.
    apply LNR.
    apply LT. }
(*halted*)
  { intros.
  destruct H as [MC [RC [PG [GFP [Glob [SMV [WDmu INJ]]]]]]]. 
    destruct c1; inv H0. destruct stack; inv H1.
    remember (ls (R AX)) as d. destruct d; inv H0.
    eexists.
    split. assumption.
    split. econstructor. 
    inv MC. simpl. inv H4.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
    specialize (AGREE AX). rewrite <- Heqd in AGREE. inv AGREE. trivial. }
(*atExternal*)
  { intros.
  destruct H as [MC [RC [PG [GFP [Glob [SMV [WDmu INJ]]]]]]]. 
    destruct c1; inv H0. destruct f; inv H1.
    split. assumption.
    inv MC. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
    eexists; split. 
      eapply val_list_inject_forall_inject.
      eapply agree_regs_map; try eassumption.
    simpl. monadInv H6. trivial. }
(*afterExternal*)
  { eapply MATCH_afterExternal. assumption. }
(*corediagram*)
  { intros. exploit MATCH_corediagram; eauto.
    intros [st2' [m2' [CS' [mu' MU']]]].
    exists st2', m2', mu'.
    split; try eapply MU'.
    split; try eapply MU'.
    split; try eapply MU'.
    split; try eapply MU'. assumption. }
(*effcorediagram*)
  { intros. exploit MATCH_effcorediagram; eauto.
    intros [st2' [m2' [U2 [CS' [mu' MU']]]]].
    exists st2', m2', mu'.
    split; try eapply MU'.
    split; try eapply MU'.
    split; try eapply MU'.
    split; try eapply MU'. 
    exists U2. split. assumption. apply MU'. }
Qed.
(*
Theorem transf_step_correct:
  forall s1 t s2, LTL.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus Linear.step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; try (inv MS).

  (* start of block, at an [add_branch] *)
  exploit find_label_lin; eauto. intros [k F]. 
  left; econstructor; split.
  eapply add_branch_correct; eauto. 
  econstructor; eauto. 
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Lcond] *)
  exploit find_label_lin; eauto. intros [k F]. 
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_true; eauto. 
  econstructor; eauto. 
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Ljumptable] *)
  exploit find_label_lin; eauto. intros [k F]. 
  left; econstructor; split.
  apply plus_one. eapply exec_Ljumptable; eauto. 
  econstructor; eauto. 
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* Lop *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto. 
  instantiate (1 := v); rewrite <- H; apply eval_operation_preserved. 
  exact symbols_preserved.
  econstructor; eauto. 

  (* Lload *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor. 
  instantiate (1 := a). rewrite <- H; apply eval_addressing_preserved. 
  exact symbols_preserved. eauto. eauto. 
  econstructor; eauto.

  (* Lgetstack *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.

  (* Lsetstack *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto. 
  econstructor; eauto.

  (* Lstore *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor. 
  instantiate (1 := a). rewrite <- H; apply eval_addressing_preserved. 
  exact symbols_preserved. eauto. eauto. 
  econstructor; eauto.

  (* Lcall *)
  exploit find_function_translated; eauto. intros [tfd [A B]].
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  symmetry; eapply sig_preserved; eauto.
  econstructor; eauto. constructor; auto. econstructor; eauto. 

  (* Ltailcall *)
  exploit find_function_translated; eauto. intros [tfd [A B]].
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  rewrite (match_parent_locset _ _ STACKS). eauto.
  symmetry; eapply sig_preserved; eauto.
  rewrite (stacksize_preserved _ _ TRF); eauto. 
  rewrite (match_parent_locset _ _ STACKS).
  econstructor; eauto.

  (* Lbuiltin *)
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lbuiltin; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

  (* Lannot *)
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lannot; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

  (* Lbranch *)
  assert ((reachable f)!!pc = true). apply REACH; simpl; auto.
  right; split. simpl; omega. split. auto. simpl. econstructor; eauto.

  (* Lcond *)
  assert (REACH1: (reachable f)!!pc1 = true) by (apply REACH; simpl; auto).
  assert (REACH2: (reachable f)!!pc2 = true) by (apply REACH; simpl; auto).
  simpl linearize_block.
  destruct (starts_with pc1 c).
  (* branch if cond is false *)
  assert (DC: destroyed_by_cond (negate_condition cond) = destroyed_by_cond cond).
    destruct cond; reflexivity.
  destruct b.
  (* cond is true: no branch *)
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_false. 
  rewrite eval_negate_condition. rewrite H. auto. eauto.
  rewrite DC. econstructor; eauto.
  (* cond is false: branch is taken *)
  right; split. simpl; omega. split. auto.  rewrite <- DC. econstructor; eauto. 
  rewrite eval_negate_condition. rewrite H. auto.
  (* branch if cond is true *)
  destruct b.
  (* cond is true: branch is taken *)
  right; split. simpl; omega. split. auto. econstructor; eauto. 
  (* cond is false: no branch *)
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_false. eauto. eauto. 
  econstructor; eauto.

  (* Ljumptable *)
  assert (REACH': (reachable f)!!pc = true).
    apply REACH. simpl. eapply list_nth_z_in; eauto. 
  right; split. simpl; omega. split. auto. econstructor; eauto. 

  (* Lreturn *)
  left; econstructor; split.
  simpl. apply plus_one. econstructor; eauto.
  rewrite (stacksize_preserved _ _ TRF). eauto.
  rewrite (match_parent_locset _ _ STACKS). econstructor; eauto.

  (* internal functions *)
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  monadInv H7.
  left; econstructor; split.
  apply plus_one. eapply exec_function_internal; eauto. 
  rewrite (stacksize_preserved _ _ EQ). eauto.
  generalize EQ; intro EQ'; monadInv EQ'. simpl. 
  econstructor; eauto. simpl. eapply is_tail_add_branch. constructor.

  (* external function *)
  monadInv H8. left; econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

  (* return *)
  inv H3. inv H1.
  left; econstructor; split.
  apply plus_one. econstructor. 
  econstructor; eauto. 
Qed.

Lemma transf_initial_states:
  forall st1, LTL.initial_state prog st1 ->
  exists st2, Linear.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].  
  exists (Callstate nil tf (Locmap.init Vundef) m0); split.
  econstructor; eauto. eapply Genv.init_mem_transf_partial; eauto. 
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry. apply (transform_partial_program_main transf_fundef _ TRANSF). 
  rewrite <- H3. apply sig_preserved. auto.
  constructor. constructor. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> LTL.final_state st1 r -> Linear.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H6. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (LTL.semantics prog) (Linear.semantics tprog).
Proof.
  eapply forward_simulation_star.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.
*)
End LINEARIZATION.
