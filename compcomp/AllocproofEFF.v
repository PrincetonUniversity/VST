(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, IRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the [Allocation] pass (validated translation from
  RTL to LTL). *)

Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Allocation.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import sepcomp.reach.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.
Require Import RTL_coop.
Require Import RTL_eff.
Require Import LTL_coop.
Require Import BuiltinEffects.
Require Import LTL_eff.

(** * Soundness of structural checks *)

Definition expand_move (sd: loc * loc) : instruction :=
  match sd with
  | (R src, R dst) => Lop Omove (src::nil) dst
  | (S sl ofs ty, R dst) => Lgetstack sl ofs ty dst
  | (R src, S sl ofs ty) => Lsetstack src sl ofs ty
  | (S _ _ _, S _ _ _) => Lreturn    (**r should never happen *)
  end.

Definition expand_moves (mv: moves) (k: bblock) : bblock :=
  List.map expand_move mv ++ k.

Definition wf_move (sd: loc * loc) : Prop :=
  match sd with
  | (S _ _ _, S _ _ _) => False
  | _ => True
  end.

Definition wf_moves (mv: moves) : Prop :=
  forall sd, In sd mv -> wf_move sd.

Inductive expand_block_shape: block_shape -> RTL.instruction -> LTL.bblock -> Prop :=
  | ebs_nop: forall mv s k,
      wf_moves mv ->
      expand_block_shape (BSnop mv s)
                         (Inop s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_move: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmove src dst mv s)
                         (Iop Omove (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_makelong: forall src1 src2 dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmakelong src1 src2 dst mv s)
                         (Iop Omakelong (src1 :: src2 :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_lowlong: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSlowlong src dst mv s)
                         (Iop Olowlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_highlong: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BShighlong src dst mv s)
                         (Iop Ohighlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_op: forall op args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSop op args res mv1 args' res' mv2 s)
                         (Iop op args res s)
                         (expand_moves mv1
                           (Lop op args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_op_dead: forall op args res mv s k,
      wf_moves mv ->
      expand_block_shape (BSopdead op args res mv s)
                         (Iop op args res s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_load: forall chunk addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload chunk addr args dst mv1 args' dst' mv2 s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv1
                           (Lload chunk addr args' dst' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2: forall addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s k,
      wf_moves mv1 -> wf_moves mv2 -> wf_moves mv3 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSload2 addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args1' dst1' ::
                           expand_moves mv2
                             (Lload Mint32 addr2 args2' dst2' :: 
                              expand_moves mv3 (Lbranch s :: k))))
  | ebs_load2_1: forall addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload2_1 addr args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2_2: forall addr addr2 args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSload2_2 addr addr2 args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr2 args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load_dead: forall chunk addr args dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSloaddead chunk addr args dst mv s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_store: forall chunk addr args src mv1 args' src' s k,
      wf_moves mv1 ->
      expand_block_shape (BSstore chunk addr args src mv1 args' src' s)
                         (Istore chunk addr args src s)
                         (expand_moves mv1
                           (Lstore chunk addr args' src' :: Lbranch s :: k))
  | ebs_store2: forall addr addr2 args src mv1 args1' src1' mv2 args2' src2' s k,
      wf_moves mv1 -> wf_moves mv2 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSstore2 addr addr2 args src mv1 args1' src1' mv2 args2' src2' s)
                         (Istore Mint64 addr args src s)
                         (expand_moves mv1
                           (Lstore Mint32 addr args1' src1' ::
                            expand_moves mv2
                             (Lstore Mint32 addr2 args2' src2' ::
                              Lbranch s :: k)))
  | ebs_call: forall sg ros args res mv1 ros' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BScall sg ros args res mv1 ros' mv2 s)
                         (Icall sg ros args res s)
                         (expand_moves mv1
                           (Lcall sg ros' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_tailcall: forall sg ros args mv ros' k,
      wf_moves mv ->
      expand_block_shape (BStailcall sg ros args mv ros')
                         (Itailcall sg ros args)
                         (expand_moves mv (Ltailcall sg ros' :: k))
  | ebs_builtin: forall ef args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSbuiltin ef args res mv1 args' res' mv2 s)
                         (Ibuiltin ef args res s)
                         (expand_moves mv1
                           (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_annot: forall txt typ args res mv args' s k,
      wf_moves mv ->
      expand_block_shape (BSannot txt typ args res mv args' s)
                         (Ibuiltin (EF_annot txt typ) args res s)
                         (expand_moves mv
                           (Lannot (EF_annot txt typ) args' :: Lbranch s :: k))
  | ebs_cond: forall cond args mv args' s1 s2 k,
      wf_moves mv ->
      expand_block_shape (BScond cond args mv args' s1 s2)
                         (Icond cond args s1 s2)
                         (expand_moves mv (Lcond cond args' s1 s2 :: k))
  | ebs_jumptable: forall arg mv arg' tbl k,
      wf_moves mv ->
      expand_block_shape (BSjumptable arg mv arg' tbl)
                         (Ijumptable arg tbl)
                         (expand_moves mv (Ljumptable arg' tbl :: k))
  | ebs_return: forall optarg mv k,
      wf_moves mv ->
      expand_block_shape (BSreturn optarg mv)
                         (Ireturn optarg)
                         (expand_moves mv (Lreturn :: k)).

Ltac MonadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some _ |- _ ] =>
        destruct x; [MonadInv|discriminate]
  | [ H: match negb (proj_sumbool ?x) with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match negb ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with (_, _) => _ end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; MonadInv
  | [ H: Some _ = Some _ |- _ ] =>
        inv H; MonadInv
  | [ H: None = Some _ |- _ ] =>
        discriminate
  | _ =>
        idtac
  end.

Lemma extract_moves_sound:
  forall b mv b',
  extract_moves nil b = (mv, b') ->
  wf_moves mv /\ b = expand_moves mv b'.
Proof.
  assert (BASE:
      forall accu b,
      wf_moves accu ->
      wf_moves (List.rev accu) /\ expand_moves (List.rev accu) b = expand_moves (List.rev accu) b).
   intros; split; auto.
   red; intros. apply H. rewrite <- in_rev in H0; auto.

  assert (IND: forall b accu mv b',
          extract_moves accu b = (mv, b') ->
          wf_moves accu ->
          wf_moves mv /\ expand_moves (List.rev accu) b = expand_moves mv b').
    induction b; simpl; intros. 
    inv H. auto.
    destruct a; try (inv H; apply BASE; auto; fail).
    destruct (is_move_operation op args) as [arg|] eqn:E.
    exploit is_move_operation_correct; eauto. intros [A B]; subst.
    (* reg-reg move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app. 
    rewrite app_ass. simpl. auto.
    inv H; apply BASE; auto.
    (* stack-reg move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app. 
    rewrite app_ass. simpl. auto.
    (* reg-stack move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app. 
    rewrite app_ass. simpl. auto.

  intros. exploit IND; eauto. red; intros. elim H0. 
Qed.

Lemma check_succ_sound:
  forall s b, check_succ s b = true -> exists k, b = Lbranch s :: k.
Proof.
  intros. destruct b; simpl in H; try discriminate. 
  destruct i; try discriminate. 
  destruct (peq s s0); simpl in H; inv H. exists b; auto.
Qed.

Ltac UseParsingLemmas :=
  match goal with
  | [ H: extract_moves nil _ = (_, _) |- _ ] =>
      destruct (extract_moves_sound _ _ _ H); clear H; subst; UseParsingLemmas
  | [ H: check_succ _ _ = true |- _ ] =>
      try discriminate;
      destruct (check_succ_sound _ _ H); clear H; subst; UseParsingLemmas
  | _ => idtac
  end.

Lemma pair_instr_block_sound:
  forall i b bsh,
  pair_instr_block i b = Some bsh -> expand_block_shape bsh i b.
Proof.
  intros; destruct i; simpl in H; MonadInv; UseParsingLemmas.
(* nop *)
  econstructor; eauto.
(* op *)
  destruct (classify_operation o l). 
  (* move *)
  MonadInv; UseParsingLemmas. econstructor; eauto. 
  (* makelong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* lowlong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* highlong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* other ops *)
  MonadInv. destruct b0.
  MonadInv; UseParsingLemmas.
  destruct i; MonadInv; UseParsingLemmas. 
  eapply ebs_op; eauto.
  inv H0. eapply ebs_op_dead; eauto.
(* load *)
  destruct b0.
  MonadInv; UseParsingLemmas.
  destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64).
  MonadInv; UseParsingLemmas. 
  destruct b; MonadInv; UseParsingLemmas. destruct i; MonadInv; UseParsingLemmas. 
  eapply ebs_load2; eauto.
  destruct (eq_addressing a addr).
  MonadInv. inv H2. eapply ebs_load2_1; eauto.
  MonadInv. inv H2. eapply ebs_load2_2; eauto.
  MonadInv; UseParsingLemmas. eapply ebs_load; eauto.
  inv H. eapply ebs_load_dead; eauto.
(* store *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64).
  MonadInv; UseParsingLemmas.
  destruct b; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  eapply ebs_store2; eauto.
  MonadInv; UseParsingLemmas.
  eapply ebs_store; eauto.
(* call *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto. 
(* tailcall *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* builtin *) 
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  econstructor; eauto.
  destruct ef; inv H. econstructor; eauto. 
(* cond *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* jumptable *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* return *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
Qed.

Lemma matching_instr_block:
  forall f1 f2 pc bsh i,
  (pair_codes f1 f2)!pc = Some bsh ->
  (RTL.fn_code f1)!pc = Some i ->
  exists b, (LTL.fn_code f2)!pc = Some b /\ expand_block_shape bsh i b.
Proof.
  intros. unfold pair_codes in H. rewrite PTree.gcombine in H; auto. rewrite H0 in H.
  destruct (LTL.fn_code f2)!pc as [b|]. 
  exists b; split; auto. apply pair_instr_block_sound; auto. 
  discriminate.
Qed.

(** * Properties of equations *)

Module ESF := FSetFacts.Facts(EqSet).
Module ESP := FSetProperties.Properties(EqSet).
Module ESD := FSetDecide.Decide(EqSet).

Definition sel_val (k: equation_kind) (v: val) : val :=
  match k with
  | Full => v
  | Low => Val.loword v
  | High => Val.hiword v
  end.

(** A set of equations [e] is satisfied in a RTL pseudoreg state [rs]
  and an LTL location state [ls] if, for every equation [r = l [k]] in [e],
  [sel_val k (rs#r)] (the [k] fragment of [r]'s value in the RTL code)
  is less defined than [ls l] (the value of [l] in the LTL code). *)


(*LENB: added parameter j:meminj and adapted lemmas accordingly*)
(*Definition satisf (rs: regset) (ls: locset) (e: eqs) : Prop :=
  forall q, EqSet.In q e -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).*)
Definition satisf (j:meminj) (rs: regset) (ls: locset) (e: eqs) : Prop :=
  forall q, EqSet.In q e -> val_inject j (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).

(*NEW*)
Lemma satisf_inject_incr: forall j rs ls e
        (SAT: satisf j rs ls e)
        j' (INC: inject_incr j j'),
      satisf j' rs ls e.
Proof. intros. red; intros.
   eapply val_inject_incr; eauto.
Qed. 

Lemma empty_eqs_satisf:
  forall j rs ls, satisf j rs ls empty_eqs.
Proof.
  unfold empty_eqs; intros; red; intros. ESD.fsetdec.
Qed.

Lemma satisf_incr:
  forall j rs ls (e1 e2: eqs),
  satisf j rs ls e2 -> EqSet.Subset e1 e2 -> satisf j rs ls e1.
Proof.
  unfold satisf; intros. apply H. ESD.fsetdec. 
Qed.

Lemma satisf_undef_reg:
  forall j rs ls e r,
  satisf j rs ls e ->
  satisf j (rs#r <- Vundef) ls e.
Proof.
  intros; red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r); auto.
  destruct (ekind q); simpl; auto.
Qed.
(*
Lemma add_equation_lessdef:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).
Proof.
  intros. apply H. unfold add_equation. simpl. apply EqSet.add_1. auto. 
Qed.
*)
Lemma add_equation_inject:
  forall j rs ls q e,
  satisf j rs ls (add_equation q e) -> 
  val_inject j (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).
Proof.
  intros. apply H. unfold add_equation. simpl. apply EqSet.add_1. auto. 
Qed.

Lemma add_equation_satisf:
  forall j rs ls q e,
  satisf j rs ls (add_equation q e) -> satisf j rs ls e.
Proof.
  intros. eapply satisf_incr; eauto. unfold add_equation. simpl. ESD.fsetdec. 
Qed.

Lemma add_equations_satisf:
  forall j rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf j rs ls e' -> satisf j rs ls e.
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  auto.
  eapply add_equation_satisf; eauto. 
Qed.
(*
Lemma add_equations_lessdef:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list (rs##rl) (reglist ls ml).
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  constructor.
  constructor; eauto.
  apply add_equation_lessdef with (e := e) (q := Eq Full a (R m)).
  eapply add_equations_satisf; eauto.
Qed.
*)
Lemma add_equations_inject:
  forall j rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf j rs ls e' ->
  val_list_inject j (rs##rl) (reglist ls ml).
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  constructor.
  constructor; eauto.
  apply add_equation_inject with (e := e) (q := Eq Full a (R m)).
  eapply add_equations_satisf; eauto.
Qed.

Lemma add_equations_args_satisf:
  forall j rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf j rs ls e' -> satisf j rs ls e.
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); intros.
  inv H; auto. 
  eapply add_equation_satisf. eapply add_equation_satisf. eauto. 
  eapply add_equation_satisf. eauto.
  eapply add_equation_satisf. eauto.
  eapply add_equation_satisf. eauto.
  congruence.
Qed.

Lemma val_longofwords_eq:
  forall v,
  Val.has_type v Tlong ->
  Val.longofwords (Val.hiword v) (Val.loword v) = v.
Proof.
  intros. red in H. destruct v; try contradiction.
  reflexivity.
  simpl. rewrite Int64.ofwords_recompose. auto.
Qed.
(*
Lemma add_equations_args_lessdef:
  forall j rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' ->
  Val.has_type_list (rs##rl) tyl ->
  Val.lessdef_list (rs##rl) (decode_longs tyl (map ls ll)).
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); simpl; intros.
- inv H; auto.
- destruct H1. constructor; auto. 
  rewrite <- (val_longofwords_eq (rs#r1)); auto. apply Val.longofwords_lessdef. 
  eapply add_equation_lessdef with (q := Eq High r1 l1). 
  eapply add_equation_satisf. eapply add_equations_args_satisf; eauto. 
  eapply add_equation_lessdef with (q := Eq Low r1 l2). 
  eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- discriminate.
Qed.*)
Lemma add_equations_args_inject:
  forall j rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf j rs ls e' ->
  Val.has_type_list (rs##rl) tyl ->
  val_list_inject j (rs##rl) (decode_longs tyl (map ls ll)).
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); simpl; intros.
- inv H; auto.
- destruct H1. constructor; auto. 
  rewrite <- (val_longofwords_eq (rs#r1)); auto. apply val_longofwords_inject. 
  eapply add_equation_inject with (q := Eq High r1 l1). 
  eapply add_equation_satisf. eapply add_equations_args_satisf; eauto. 
  eapply add_equation_inject with (q := Eq Low r1 l2). 
  eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_inject with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_inject with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_inject with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- discriminate.
Qed.

Lemma add_equation_ros_satisf:
  forall j rs ls ros mos e e',
  add_equation_ros ros mos e = Some e' ->
  satisf j rs ls e' -> satisf j rs ls e.
Proof.
  unfold add_equation_ros; intros. destruct ros; destruct mos; MonadInv.
  eapply add_equation_satisf; eauto.
  auto.
Qed.

Lemma remove_equation_satisf:
  forall j rs ls q e,
  satisf j rs ls e -> satisf j rs ls (remove_equation q e).
Proof.
  intros. eapply satisf_incr; eauto. unfold remove_equation; simpl. ESD.fsetdec. 
Qed.

Lemma remove_equation_res_satisf:
  forall j rs ls r oty ll e e',
  remove_equations_res r oty ll e = Some e' ->
  satisf j rs ls e -> satisf j rs ls e'.
Proof.
  intros. functional inversion H. 
  apply remove_equation_satisf. apply remove_equation_satisf; auto.
  apply remove_equation_satisf; auto.
Qed.

Remark select_reg_l_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q1 q2 ->
  select_reg_l r q1 = true -> select_reg_l r q2 = true.
Proof.
  unfold select_reg_l; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]]. 
  red in A. zify; omega.
  rewrite <- A; auto.
Qed.

Remark select_reg_h_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q2 q1 ->
  select_reg_h r q1 = true -> select_reg_h r q2 = true.
Proof.
  unfold select_reg_h; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]]. 
  red in A. zify; omega.
  rewrite A; auto.
Qed.

Remark select_reg_charact:
  forall r q, select_reg_l r q = true /\ select_reg_h r q = true <-> ereg q = r.
Proof.
  unfold select_reg_l, select_reg_h; intros; split.
  rewrite ! Pos.leb_le. unfold reg; zify; omega.
  intros. rewrite H. rewrite ! Pos.leb_refl; auto. 
Qed.

Lemma reg_unconstrained_sound:
  forall r e q,
  reg_unconstrained r e = true ->
  EqSet.In q e ->
  ereg q <> r.
Proof.
  unfold reg_unconstrained; intros. red; intros.
  apply select_reg_charact in H1. 
  assert (EqSet.mem_between (select_reg_l r) (select_reg_h r) e = true).
  {
    apply EqSet.mem_between_2 with q; auto.
    exact (select_reg_l_monotone r).
    exact (select_reg_h_monotone r).
    tauto.
    tauto.
  }
  rewrite H2 in H; discriminate.
Qed.

Lemma reg_unconstrained_satisf:
  forall j r e rs ls v,
  reg_unconstrained r e = true ->
  satisf j rs ls e ->
  satisf j (rs#r <- v) ls e.
Proof.
  red; intros. rewrite PMap.gso. auto. eapply reg_unconstrained_sound; eauto. 
Qed.

Remark select_loc_l_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q1 q2 ->
  select_loc_l l q1 = true -> select_loc_l l q2 = true.
Proof.
  unfold select_loc_l; intros. set (lb := OrderedLoc.diff_low_bound l) in *.
  destruct H.
  red in H. subst q2; auto. 
  assert (eloc q1 = eloc q2 \/ OrderedLoc.lt (eloc q1) (eloc q2)).
    red in H. tauto. 
  destruct H1. rewrite <- H1; auto. 
  destruct (OrderedLoc.compare (eloc q2) lb); auto. 
  assert (OrderedLoc.lt (eloc q1) lb) by (eapply OrderedLoc.lt_trans; eauto). 
  destruct (OrderedLoc.compare (eloc q1) lb). 
  auto.
  eelim OrderedLoc.lt_not_eq; eauto.
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
Qed.

Remark select_loc_h_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q2 q1 ->
  select_loc_h l q1 = true -> select_loc_h l q2 = true.
Proof.
  unfold select_loc_h; intros. set (lb := OrderedLoc.diff_high_bound l) in *.
  destruct H.
  red in H. subst q2; auto. 
  assert (eloc q2 = eloc q1 \/ OrderedLoc.lt (eloc q2) (eloc q1)).
    red in H. tauto. 
  destruct H1. rewrite H1; auto. 
  destruct (OrderedLoc.compare (eloc q2) lb); auto. 
  assert (OrderedLoc.lt lb (eloc q1)) by (eapply OrderedLoc.lt_trans; eauto). 
  destruct (OrderedLoc.compare (eloc q1) lb). 
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
  eelim OrderedLoc.lt_not_eq. eexact H2. apply OrderedLoc.eq_sym; auto.
  auto.
Qed.

Remark select_loc_charact:
  forall l q,
  select_loc_l l q = false \/ select_loc_h l q = false <-> Loc.diff l (eloc q).
Proof.
  unfold select_loc_l, select_loc_h; intros; split; intros.
  apply OrderedLoc.outside_interval_diff. 
  destruct H.
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)); assumption || discriminate.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)); assumption || discriminate.
  exploit OrderedLoc.diff_outside_interval. eauto. 
  intros [A | A].
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)).
  auto.
  eelim OrderedLoc.lt_not_eq; eauto. 
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)).
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  eelim OrderedLoc.lt_not_eq; eauto. apply OrderedLoc.eq_sym; auto. 
  auto.
Qed.

Lemma loc_unconstrained_sound:
  forall l e q,
  loc_unconstrained l e = true ->
  EqSet.In q e ->
  Loc.diff l (eloc q).
Proof.
  unfold loc_unconstrained; intros. 
  destruct (select_loc_l l q) eqn:SL.
  destruct (select_loc_h l q) eqn:SH.
  assert (EqSet2.mem_between (select_loc_l l) (select_loc_h l) (eqs2 e) = true).
  {
    apply EqSet2.mem_between_2 with q; auto.
    exact (select_loc_l_monotone l).
    exact (select_loc_h_monotone l).
    apply eqs_same. auto. 
  }
  rewrite H1 in H; discriminate.
  apply select_loc_charact; auto.
  apply select_loc_charact; auto.
Qed.
(*
Lemma loc_unconstrained_satisf:
  forall rs ls k r mr e v,
  let l := R mr in
  satisf rs ls (remove_equation (Eq k r l) e) ->
  loc_unconstrained (R mr) (remove_equation (Eq k r l) e) = true ->
  Val.lessdef (sel_val k rs#r) v ->
  satisf rs (Locmap.set l v ls) e.
Proof.
  intros; red; intros. 
  destruct (OrderedEquation.eq_dec q (Eq k r l)). 
  subst q; simpl. unfold l; rewrite Locmap.gss_reg. auto.
  assert (EqSet.In q (remove_equation (Eq k r l) e)).
    simpl. ESD.fsetdec.  
  rewrite Locmap.gso. apply H; auto. eapply loc_unconstrained_sound; eauto. 
Qed.*)

Lemma loc_unconstrained_satisf:
  forall j rs ls k r mr e v,
  let l := R mr in
  satisf j rs ls (remove_equation (Eq k r l) e) ->
  loc_unconstrained (R mr) (remove_equation (Eq k r l) e) = true ->
  val_inject j (sel_val k rs#r) v ->
  satisf j rs (Locmap.set l v ls) e.
Proof.
  intros; red; intros. 
  destruct (OrderedEquation.eq_dec q (Eq k r l)). 
  subst q; simpl. unfold l; rewrite Locmap.gss_reg. auto.
  assert (EqSet.In q (remove_equation (Eq k r l) e)).
    simpl. ESD.fsetdec.  
  rewrite Locmap.gso. apply H; auto. eapply loc_unconstrained_sound; eauto. 
Qed.

Lemma reg_loc_unconstrained_sound:
  forall r l e q,
  reg_loc_unconstrained r l e = true ->
  EqSet.In q e ->
  ereg q <> r /\ Loc.diff l (eloc q).
Proof.
  intros. destruct (andb_prop _ _ H). 
  split. eapply reg_unconstrained_sound; eauto. eapply loc_unconstrained_sound; eauto.
Qed.
(*
Lemma parallel_assignment_satisf:
  forall k r mr e rs ls v v',
  let l := R mr in
  Val.lessdef (sel_val k v) v' ->
  reg_loc_unconstrained r (R mr) (remove_equation (Eq k r l) e) = true ->
  satisf rs ls (remove_equation (Eq k r l) e) ->
  satisf (rs#r <- v) (Locmap.set l v' ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Regmap.gss; rewrite Locmap.gss_reg; auto.
  assert (EqSet.In q (remove_equation {| ekind := k; ereg := r; eloc := l |} e)).
    simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto. rewrite Locmap.gso; auto. 
Qed.*)

Lemma parallel_assignment_satisf:
  forall j k r mr e rs ls v v',
  let l := R mr in
  val_inject j (sel_val k v) v' ->
  reg_loc_unconstrained r (R mr) (remove_equation (Eq k r l) e) = true ->
  satisf j rs ls (remove_equation (Eq k r l) e) ->
  satisf j (rs#r <- v) (Locmap.set l v' ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Regmap.gss; rewrite Locmap.gss_reg; auto.
  assert (EqSet.In q (remove_equation {| ekind := k; ereg := r; eloc := l |} e)).
    simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto. rewrite Locmap.gso; auto. 
Qed.
(*
Lemma parallel_assignment_satisf_2:
  forall rs ls res mres' oty e e' v v',
  let res' := map R mres' in
  remove_equations_res res oty res' e = Some e' ->
  satisf rs ls e' ->
  reg_unconstrained res e' = true ->
  forallb (fun l => loc_unconstrained l e') res' = true ->
  Val.lessdef v v' ->
  satisf (rs#res <- v) (Locmap.setlist res' (encode_long oty v') ls) e.
Proof.
  intros; red; intros.
  assert (ISREG: forall l, In l res' -> exists mr, l = R mr).
  { unfold res'; intros. exploit list_in_map_inv; eauto. intros [mr [A B]]. exists mr; auto. }
  functional inversion H.
- (* Two 32-bit halves *)
  subst. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := l2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := l1 |} e)) in *.
  rewrite <- H5 in H2. simpl in H2. InvBooleans. simpl.
  destruct (OrderedEquation.eq_dec q (Eq Low res l2)).
  subst q; simpl. rewrite Regmap.gss.
  destruct (ISREG l2) as [r2 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  apply Val.loword_lessdef; auto. 
  destruct (OrderedEquation.eq_dec q (Eq High res l1)).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by auto.
  destruct (ISREG l1) as [r1 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  apply Val.hiword_lessdef; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec. 
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto. 
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
- (* One location *)
  subst. rewrite <- H5 in H2. simpl in H2. InvBooleans.
  replace (encode_long oty v') with (v' :: nil).
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := l1 |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res l1)). 
  subst q; simpl. rewrite Regmap.gss.
  destruct (ISREG l1) as [r1 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec. 
  simpl. rewrite Regmap.gso. rewrite Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
  destruct oty as [[]|]; reflexivity || contradiction.
Qed.*)
Lemma parallel_assignment_satisf_2:
  forall j rs ls res mres' oty e e' v v',
  let res' := map R mres' in
  remove_equations_res res oty res' e = Some e' ->
  satisf j rs ls e' ->
  reg_unconstrained res e' = true ->
  forallb (fun l => loc_unconstrained l e') res' = true ->
  val_inject j v v' ->
  satisf j (rs#res <- v) (Locmap.setlist res' (encode_long oty v') ls) e.
Proof.
  intros; red; intros.
  assert (ISREG: forall l, In l res' -> exists mr, l = R mr).
  { unfold res'; intros. exploit list_in_map_inv; eauto. intros [mr [A B]]. exists mr; auto. }
  functional inversion H.
- (* Two 32-bit halves *)
  subst. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := l2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := l1 |} e)) in *.
  rewrite <- H5 in H2. simpl in H2. InvBooleans. simpl.
  destruct (OrderedEquation.eq_dec q (Eq Low res l2)).
  subst q; simpl. rewrite Regmap.gss.
  destruct (ISREG l2) as [r2 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  apply val_loword_inject; auto. 
  destruct (OrderedEquation.eq_dec q (Eq High res l1)).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by auto.
  destruct (ISREG l1) as [r1 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  apply val_hiword_inject; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec. 
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto. 
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
- (* One location *)
  subst. rewrite <- H5 in H2. simpl in H2. InvBooleans.
  replace (encode_long oty v') with (v' :: nil).
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := l1 |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res l1)). 
  subst q; simpl. rewrite Regmap.gss.
  destruct (ISREG l1) as [r1 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec. 
  simpl. rewrite Regmap.gso. rewrite Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
  destruct oty as [[]|]; reflexivity || contradiction.
Qed.

Lemma in_subst_reg:
  forall r1 r2 q (e: eqs),
  EqSet.In q e ->
  ereg q = r1 /\ EqSet.In (Eq (ekind q) r2 (eloc q)) (subst_reg r1 r2 e)
  \/ ereg q <> r1 /\ EqSet.In q (subst_reg r1 r2 e).
Proof.
  intros r1 r2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e => add_equation (Eq (ekind q) r2 (eloc q)) (remove_equation q e)).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  assert (IN_ELT: forall q, EqSet.In q elt <-> EqSet.In q e0 /\ ereg q = r1).
  {
    intros. unfold elt. rewrite EqSet.elements_between_iff.
    rewrite select_reg_charact. tauto. 
    exact (select_reg_l_monotone r1).
    exact (select_reg_h_monotone r1).
  }
  set (P := fun e1 e2 =>
         EqSet.In q e1 ->
         EqSet.In (Eq (ekind q) r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3. 
      + subst x. ESD.fsetdec. 
      + rewrite ESF.add_iff. rewrite ESF.remove_iff. 
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto. 
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - simpl. red in H2. rewrite H2 in H4.
      rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. tauto. 
  }
  destruct (ESP.In_dec q elt).
  left. split. apply IN_ELT. auto. apply H. auto.
  right. split. red; intros. elim n. rewrite IN_ELT. auto. apply H0. auto. 
Qed.

Lemma subst_reg_satisf:
  forall j src dst rs ls e,
  satisf j rs ls (subst_reg dst src e) ->
  satisf j (rs#dst <- (rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg dst src q e H0) as [[A B] | [A B]].
  subst dst. rewrite Regmap.gss. exploit H; eauto.
  rewrite Regmap.gso; auto.
Qed.

Lemma in_subst_reg_kind:
  forall r1 k1 r2 k2 q (e: eqs),
  EqSet.In q e ->
  (ereg q, ekind q) = (r1, k1) /\ EqSet.In (Eq k2 r2 (eloc q)) (subst_reg_kind r1 k1 r2 k2 e)
  \/ EqSet.In q (subst_reg_kind r1 k1 r2 k2 e).
Proof.
  intros r1 k1 r2 k2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e =>
      if IndexedEqKind.eq (ekind q) k1
      then add_equation (Eq k2 r2 (eloc q)) (remove_equation q e)
      else e).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  assert (IN_ELT: forall q, EqSet.In q elt <-> EqSet.In q e0 /\ ereg q = r1).
  {
    intros. unfold elt. rewrite EqSet.elements_between_iff.
    rewrite select_reg_charact. tauto. 
    exact (select_reg_l_monotone r1).
    exact (select_reg_h_monotone r1).
  }
  set (P := fun e1 e2 =>
         EqSet.In q e1 -> ekind q = k1 ->
         EqSet.In (Eq k2 r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    intros; apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3. 
      + subst x. unfold f. destruct (IndexedEqKind.eq (ekind q) k1).
        simpl. ESD.fsetdec. contradiction.
      + unfold f. destruct (IndexedEqKind.eq (ekind x) k1).
        simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff. 
        destruct (OrderedEquation.eq_dec x {| ekind := k2; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto.
        auto. 
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 \/ ekind q <> k1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - unfold f. red in H2. rewrite H2 in H4.
      destruct (IndexedEqKind.eq (ekind x) k1).
      simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. intuition congruence. 
      apply H3. intuition. 
  }
  destruct (ESP.In_dec q elt).
  destruct (IndexedEqKind.eq (ekind q) k1).
  left. split. f_equal. apply IN_ELT. auto. auto. apply H. auto. auto.
  right. apply H0. auto.
  right. apply H0. auto.
Qed.
(*
Lemma subst_reg_kind_satisf_makelong:
  forall src1 src2 dst rs ls e,
  let e1 := subst_reg_kind dst High src1 Full e in
  let e2 := subst_reg_kind dst Low src2 Full e1 in
  reg_unconstrained dst e2 = true ->
  satisf rs ls e2 ->
  satisf (rs#dst <- (Val.longofwords rs#src1 rs#src2)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst High src1 Full q e H1) as [[A B] | B]; fold e1 in B.
  destruct (in_subst_reg_kind dst Low src2 Full _ e1 B) as [[C D] | D]; fold e2 in D.
  simpl in C; simpl in D. inv C.
  inversion A. rewrite H3; rewrite H4. rewrite Regmap.gss.
  apply Val.lessdef_trans with (rs#src1). 
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto. 
  rewrite Int64.hi_ofwords. auto.
  exploit H0. eexact D. simpl. auto. 
  destruct (in_subst_reg_kind dst Low src2 Full q e1 B) as [[C D] | D]; fold e2 in D.
  inversion C. rewrite H3; rewrite H4. rewrite Regmap.gss. 
  apply Val.lessdef_trans with (rs#src2). 
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto. 
  rewrite Int64.lo_ofwords. auto.
  exploit H0. eexact D. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto. 
Qed.*)
Lemma subst_reg_kind_satisf_makelong:
  forall j src1 src2 dst rs ls e,
  let e1 := subst_reg_kind dst High src1 Full e in
  let e2 := subst_reg_kind dst Low src2 Full e1 in
  reg_unconstrained dst e2 = true ->
  satisf j rs ls e2 ->
  satisf j (rs#dst <- (Val.longofwords rs#src1 rs#src2)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst High src1 Full q e H1) as [[A B] | B]; fold e1 in B.
  destruct (in_subst_reg_kind dst Low src2 Full _ e1 B) as [[C D] | D]; fold e2 in D.
  simpl in C; simpl in D. inv C.
  inversion A. rewrite H3; rewrite H4. rewrite Regmap.gss.
  (*apply val_inject_trans with (rs#src1). *)
  eapply val_lessdef_inject_compose with (v2:=rs#src1).
    simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto. 
      rewrite Int64.hi_ofwords. auto.
    exploit H0. eexact D. simpl. auto. 

  destruct (in_subst_reg_kind dst Low src2 Full q e1 B) as [[C D] | D]; fold e2 in D.
  inversion C. rewrite H3; rewrite H4. rewrite Regmap.gss. 
  (*apply Val.lessdef_trans with (rs#src2). *)
  eapply val_lessdef_inject_compose with (v2:=rs#src2).  
    simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto. 
      rewrite Int64.lo_ofwords. auto.
    exploit H0. eexact D. simpl. auto.

  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto. 
Qed.

Lemma subst_reg_kind_satisf_lowlong:
  forall j src dst rs ls e,
  let e1 := subst_reg_kind dst Full src Low e in
  reg_unconstrained dst e1 = true ->
  satisf j rs ls e1 ->
  satisf j (rs#dst <- (Val.loword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src Low q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss. 
  exploit H0. eexact B. simpl. auto. 
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Lemma subst_reg_kind_satisf_highlong:
  forall j src dst rs ls e,
  let e1 := subst_reg_kind dst Full src High e in
  reg_unconstrained dst e1 = true ->
  satisf j rs ls e1 ->
  satisf j (rs#dst <- (Val.hiword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src High q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss. 
  exploit H0. eexact B. simpl. auto. 
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Module ESF2 := FSetFacts.Facts(EqSet2).
Module ESP2 := FSetProperties.Properties(EqSet2).
Module ESD2 := FSetDecide.Decide(EqSet2).

Lemma in_subst_loc:
  forall l1 l2 q (e e': eqs),
  EqSet.In q e ->
  subst_loc l1 l2 e = Some e' ->
  (eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e') \/ (Loc.diff l1 (eloc q) /\ EqSet.In q e').
Proof.
  intros l1 l2 q e0 e0'.
  unfold subst_loc. 
  set (f := fun (q0 : EqSet2.elt) (opte : option eqs) =>
   match opte with
   | Some e =>
       if Loc.eq l1 (eloc q0)
       then
        Some
          (add_equation {| ekind := ekind q0; ereg := ereg q0; eloc := l2 |}
             (remove_equation q0 e))
       else None
   | None => None
   end).
  set (elt := EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e0)).
  intros IN SUBST.
  set (P := fun e1 (opte: option eqs) =>
          match opte with
          | None => True
          | Some e2 =>
              EqSet2.In q e1 ->
              eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e2
          end).
  assert (P elt (EqSet2.fold f elt (Some e0))).
  {
    apply ESP2.fold_rec; unfold P; intros.
    - ESD2.fsetdec. 
    - destruct a as [e2|]; simpl; auto. 
      destruct (Loc.eq l1 (eloc x)); auto.
      unfold add_equation, remove_equation; simpl.
      red in H1. rewrite H1. intros [A|A]. 
      + subst x. split. auto. ESD.fsetdec.
      + exploit H2; eauto. intros [B C]. split. auto.
        rewrite ESF.add_iff. rewrite ESF.remove_iff. 
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := ereg q; eloc := l2 |}).
        left. rewrite e1; auto. 
        right; auto. 
  }
  set (Q := fun e1 (opte: option eqs) =>
          match opte with
          | None => True
          | Some e2 => ~EqSet2.In q e1 -> EqSet.In q e2
          end).
  assert (Q elt (EqSet2.fold f elt (Some e0))).
  {
    apply ESP2.fold_rec; unfold Q; intros.
    - auto. 
    - destruct a as [e2|]; simpl; auto. 
      destruct (Loc.eq l1 (eloc x)); auto. 
      red in H2. rewrite H2; intros. 
      unfold add_equation, remove_equation; simpl.
      rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right; split. apply H3. tauto. tauto.
  }
  rewrite SUBST in H; rewrite SUBST in H0; simpl in *. 
  destruct (ESP2.In_dec q elt). 
  left. apply H; auto.
  right. split; auto. 
  rewrite <- select_loc_charact.
  destruct (select_loc_l l1 q) eqn: LL; auto.
  destruct (select_loc_h l1 q) eqn: LH; auto.
  elim n. eapply EqSet2.elements_between_iff. 
  exact (select_loc_l_monotone l1).
  exact (select_loc_h_monotone l1).
  split. apply eqs_same; auto. auto. 
Qed.

Lemma loc_type_compat_charact:
  forall env l e q,
  loc_type_compat env l e = true ->
  EqSet.In q e ->
  subtype (sel_type (ekind q) (env (ereg q))) (Loc.type l) = true \/ Loc.diff l (eloc q).
Proof.
  unfold loc_type_compat; intros. 
  rewrite EqSet2.for_all_between_iff in H.
  destruct (select_loc_l l q) eqn: LL.
  destruct (select_loc_h l q) eqn: LH.
  left; apply H; auto. apply eqs_same; auto. 
  right. apply select_loc_charact. auto. 
  right. apply select_loc_charact. auto.
  intros; subst; auto.
  exact (select_loc_l_monotone l).
  exact (select_loc_h_monotone l).
Qed.

Lemma well_typed_move_charact:
  forall env l e k r rs,
  well_typed_move env l e = true ->
  EqSet.In (Eq k r l) e ->
  wt_regset env rs ->
  match l with
  | R mr => True
  | S sl ofs ty => Val.has_type (sel_val k rs#r) ty
  end.
Proof.
  unfold well_typed_move; intros. 
  destruct l as [mr | sl ofs ty]. 
  auto.
  exploit loc_type_compat_charact; eauto. intros [A | A].
  simpl in A. eapply Val.has_subtype; eauto. 
  generalize (H1 r). destruct k; simpl; intros.
  auto.
  destruct (rs#r); exact I.
  destruct (rs#r); exact I.
  eelim Loc.diff_not_eq. eexact A. auto.
Qed.
(*
Remark val_lessdef_normalize:
  forall v v' ty,
  Val.has_type v ty -> Val.lessdef v v' ->
  Val.lessdef v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros. inv H0. rewrite Val.load_result_same; auto. auto. 
Qed.

Lemma subst_loc_satisf:
  forall env src dst rs ls e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) ls) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H2 _ B). 
  apply val_lessdef_normalize; auto. apply (H2 _ B). 
  rewrite Locmap.gso; auto.
Qed.
*)
Lemma subst_loc_satisf:
  forall j env src dst rs ls e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  wt_regset env rs ->
  satisf j rs ls e' ->
  satisf j rs (Locmap.set dst (ls src) ls) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H2 _ B). 

  (*apply val_lessdef_normalize; auto. apply (H2 _ B). *)
  rewrite <- (Val.load_result_same _ _ H4).
  apply val_load_result_inject. apply (H2 _ B).
  
  rewrite Locmap.gso; auto.
Qed.

Lemma can_undef_sound:
  forall e ml q,
  can_undef ml e = true -> EqSet.In q e -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto. 
  eauto.
Qed.

Lemma undef_regs_outside:
  forall ml ls l,
  Loc.notin l (map R ml) -> undef_regs ml ls l = ls l.
Proof.
  induction ml; simpl; intros. auto.
  rewrite Locmap.gso. apply IHml. tauto. apply Loc.diff_sym. tauto. 
Qed.

Lemma can_undef_satisf:
  forall j ml e rs ls,
  can_undef ml e = true ->
  satisf j rs ls e ->
  satisf j rs (undef_regs ml ls) e.
Proof.
  intros; red; intros. rewrite undef_regs_outside. eauto.
  eapply can_undef_sound; eauto.
Qed.

Lemma can_undef_except_sound:
  forall lx e ml q,
  can_undef_except lx ml e = true -> EqSet.In q e -> Loc.diff (eloc q) lx -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  destruct (orb_true_elim _ _ H2). 
  apply proj_sumbool_true in e0. congruence.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto. 
  eapply IHml; eauto.
Qed.

Lemma subst_loc_undef_satisf:
  forall j env src dst rs ls ml e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  can_undef_except dst ml e = true ->
  wt_regset env rs ->
  satisf j rs ls e' ->
  satisf j rs (Locmap.set dst (ls src) (undef_regs ml ls)) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H3 _ B).
 
  (*apply val_lessdef_normalize; auto. apply (H3 _ B). *)
  rewrite <- (Val.load_result_same _ _ H5).
  apply val_load_result_inject. apply (H3 _ B).

  rewrite Locmap.gso; auto. rewrite undef_regs_outside. eauto. 
  eapply can_undef_except_sound; eauto. apply Loc.diff_sym; auto.
Qed.
(*
Lemma transfer_use_def_satisf:
  forall args res args' res' und e e' rs ls,
  transfer_use_def args res args' res' und e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list rs##args (reglist ls args') /\
  (forall v v', Val.lessdef v v' ->
    satisf (rs#res <- v) (Locmap.set (R res') v' (undef_regs und ls)) e).
Proof.
  unfold transfer_use_def; intros. MonadInv. 
  split. eapply add_equations_lessdef; eauto.
  intros. eapply parallel_assignment_satisf; eauto. assumption. 
  eapply can_undef_satisf; eauto. 
  eapply add_equations_satisf; eauto. 
Qed.*)
Lemma transfer_use_def_satisf_inject:
  forall j args res args' res' und e e' rs ls,
  transfer_use_def args res args' res' und e = Some e' ->
  satisf j rs ls e' ->
  val_list_inject j rs##args (reglist ls args') /\
  (forall v v', val_inject j v v' ->
    satisf j (rs#res <- v) (Locmap.set (R res') v' (undef_regs und ls)) e).
Proof.
  unfold transfer_use_def; intros. MonadInv. 
  split. (*eapply add_equations_lessdef; eauto.*)
         eapply add_equations_inject; eauto.
  intros. eapply parallel_assignment_satisf; eauto. assumption. 
  eapply can_undef_satisf; eauto. 
  eapply add_equations_satisf; eauto. 
Qed.
(*
Lemma add_equations_res_lessdef:
  forall r oty ll e e' rs ls,
  add_equations_res r oty ll e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list (encode_long oty rs#r) (map ls ll).
Proof.
  intros. functional inversion H.
- subst. simpl. constructor. 
  eapply add_equation_lessdef with (q := Eq High r l1).
  eapply add_equation_satisf. eauto. 
  constructor.
  eapply add_equation_lessdef with (q := Eq Low r l2). eauto.
  constructor.
- subst. replace (encode_long oty rs#r) with (rs#r :: nil). simpl. constructor; auto.
  eapply add_equation_lessdef with (q := Eq Full r l1); eauto.
  destruct oty as [[]|]; reflexivity || contradiction.
Qed.
*)
Lemma add_equations_res_inject:
  forall j r oty ll e e' rs ls,
  add_equations_res r oty ll e = Some e' ->
  satisf j rs ls e' ->
  val_list_inject j (encode_long oty rs#r) (map ls ll).
Proof.
  intros. functional inversion H.
- subst. simpl. constructor. 
  eapply add_equation_inject with (q := Eq High r l1).
  eapply add_equation_satisf. eauto. 
  constructor.
  eapply add_equation_inject with (q := Eq Low r l2). eauto.
  constructor.
- subst. replace (encode_long oty rs#r) with (rs#r :: nil). simpl. constructor; auto.
  eapply add_equation_inject with (q := Eq Full r l1); eauto.
  destruct oty as [[]|]; reflexivity || contradiction.
Qed.

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => ~(In r destroyed_at_call)
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

Lemma return_regs_agree_callee_save:
  forall caller callee,
  agree_callee_save caller (return_regs caller callee).
Proof.
  intros; red; intros. unfold return_regs. red in H. 
  destruct l.
  rewrite pred_dec_false; auto. 
  destruct sl; auto || congruence. 
Qed.

Lemma no_caller_saves_sound:
  forall e q,
  no_caller_saves e = true ->
  EqSet.In q e ->
  callee_save_loc (eloc q).
Proof.
  unfold no_caller_saves, callee_save_loc; intros.
  exploit EqSet.for_all_2; eauto.
  hnf. intros. simpl in H1. rewrite H1. auto.
  lazy beta. destruct (eloc q). 
  intros; red; intros. destruct (orb_true_elim _ _ H1); InvBooleans.
  eapply int_callee_save_not_destroyed; eauto.
  apply index_int_callee_save_pos2. omega.
  eapply float_callee_save_not_destroyed; eauto.
  apply index_float_callee_save_pos2. omega.
  destruct sl; congruence.
Qed.
(*
Lemma function_return_satisf:
  forall rs ls_before ls_after res res' sg e e' v,
  res' = map R (loc_result sg) ->
  remove_equations_res res (sig_res sg) res' e = Some e' ->
  satisf rs ls_before e' ->
  forallb (fun l => reg_loc_unconstrained res l e') res' = true ->
  no_caller_saves e' = true ->
  Val.lessdef_list (encode_long (sig_res sg) v) (map ls_after res') ->
  agree_callee_save ls_before ls_after ->
  satisf (rs#res <- v) ls_after e.
Proof.
  intros; red; intros.
  functional inversion H0.
- subst. rewrite <- H11 in *. unfold encode_long in H4. rewrite <- H7 in H4. 
  simpl in H4. inv H4. inv H14. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := l2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := l1 |} e)) in *.
  simpl in H2. InvBooleans.
  destruct (OrderedEquation.eq_dec q (Eq Low res l2)).
  subst q; simpl. rewrite Regmap.gss. auto.
  destruct (OrderedEquation.eq_dec q (Eq High res l1)).
  subst q; simpl. rewrite Regmap.gss. auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec. 
  exploit reg_loc_unconstrained_sound. eexact H. eauto. intros [A B].
  exploit reg_loc_unconstrained_sound. eexact H2. eauto. intros [C D].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto. 
- subst. rewrite <- H11 in *.
  replace (encode_long (sig_res sg) v) with (v :: nil) in H4.
  simpl in H4. inv H4.
  simpl in H2. InvBooleans.
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := l1 |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res l1)). 
  subst q; simpl. rewrite Regmap.gss; auto. 
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec. 
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
  destruct (sig_res sg) as [[]|]; reflexivity || contradiction.
Qed.
*)
Lemma function_return_satisf:
  forall j rs ls_before ls_after res res' sg e e' v,
  res' = map R (loc_result sg) ->
  remove_equations_res res (sig_res sg) res' e = Some e' ->
  satisf j rs ls_before e' ->
  forallb (fun l => reg_loc_unconstrained res l e') res' = true ->
  no_caller_saves e' = true ->
  val_list_inject j (encode_long (sig_res sg) v) (map ls_after res') ->
  agree_callee_save ls_before ls_after ->
  satisf j (rs#res <- v) ls_after e.
Proof.
  intros; red; intros.
  functional inversion H0.
- subst. rewrite <- H11 in *. unfold encode_long in H4. rewrite <- H7 in H4. 
  simpl in H4. inv H4. inv H14. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := l2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := l1 |} e)) in *.
  simpl in H2. InvBooleans.
  destruct (OrderedEquation.eq_dec q (Eq Low res l2)).
  subst q; simpl. rewrite Regmap.gss. auto.
  destruct (OrderedEquation.eq_dec q (Eq High res l1)).
  subst q; simpl. rewrite Regmap.gss. auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec. 
  exploit reg_loc_unconstrained_sound. eexact H. eauto. intros [A B].
  exploit reg_loc_unconstrained_sound. eexact H2. eauto. intros [C D].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto. 
- subst. rewrite <- H11 in *.
  replace (encode_long (sig_res sg) v) with (v :: nil) in H4.
  simpl in H4. inv H4.
  simpl in H2. InvBooleans.
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := l1 |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res l1)). 
  subst q; simpl. rewrite Regmap.gss; auto. 
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec. 
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
  destruct (sig_res sg) as [[]|]; reflexivity || contradiction.
Qed.

Lemma compat_left_sound:
  forall r l e q,
  compat_left r l e = true -> EqSet.In q e -> ereg q = r -> ekind q = Full /\ eloc q = l.
Proof.
  unfold compat_left; intros.
  rewrite EqSet.for_all_between_iff in H. 
  apply select_reg_charact in H1. destruct H1. 
  exploit H; eauto. intros. 
  destruct (ekind q); try discriminate. 
  destruct (Loc.eq l (eloc q)); try discriminate. 
  auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma compat_left2_sound:
  forall r l1 l2 e q,
  compat_left2 r l1 l2 e = true -> EqSet.In q e -> ereg q = r ->
  (ekind q = High /\ eloc q = l1) \/ (ekind q = Low /\ eloc q = l2).
Proof.
  unfold compat_left2; intros.
  rewrite EqSet.for_all_between_iff in H. 
  apply select_reg_charact in H1. destruct H1. 
  exploit H; eauto. intros. 
  destruct (ekind q); try discriminate. 
  InvBooleans. auto.
  InvBooleans. auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma val_hiword_longofwords:
  forall v1 v2, Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.hiword.
  rewrite Int64.hi_ofwords. auto.
Qed.

Lemma val_loword_longofwords:
  forall v1 v2, Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.loword.
  rewrite Int64.lo_ofwords. auto.
Qed.
(*
Lemma compat_entry_satisf:
  forall rl tyl ll e,
  compat_entry rl tyl ll e = true ->
  forall vl ls,
  Val.lessdef_list vl (decode_longs tyl (map ls ll)) ->
  satisf (init_regs vl rl) ls e.
Proof.
  intros until e. functional induction (compat_entry rl tyl ll e); intros. 
- (* no params *)
  simpl. red; intros. rewrite Regmap.gi. destruct (ekind q); simpl; auto.
- (* a param of type Tlong *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left2_sound; eauto.
  intros [[A B] | [A B]]; rewrite A; rewrite B; simpl.
  apply Val.lessdef_trans with (Val.hiword (Val.longofwords (ls l1) (ls l2))).
  apply Val.hiword_lessdef; auto. apply val_hiword_longofwords.
  apply Val.lessdef_trans with (Val.loword (Val.longofwords (ls l1) (ls l2))).
  apply Val.loword_lessdef; auto. apply val_loword_longofwords.
  eapply IHb; eauto.
- (* a param of type Tint *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param of type Tfloat *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param of type Tsingle *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* error case *)
  discriminate.
Qed.
*)
Lemma compat_entry_satisf:
  forall j rl tyl ll e,
  compat_entry rl tyl ll e = true ->
  forall vl ls,
  val_list_inject j vl (decode_longs tyl (map ls ll)) ->
  satisf j (init_regs vl rl) ls e.
Proof.
  intros until e. functional induction (compat_entry rl tyl ll e); intros. 
- (* no params *)
  simpl. red; intros. rewrite Regmap.gi. destruct (ekind q); simpl; auto.
- (* a param of type Tlong *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left2_sound; eauto.
  intros [[A B] | [A B]]; rewrite A; rewrite B; simpl.

  (* apply Val.lessdef_trans with (Val.hiword (Val.longofwords (ls l1) (ls l2))).
      apply Val.hiword_lessdef; auto. apply val_hiword_longofwords.*)
  apply valinject_lessdef with (v2:=Val.hiword (Val.longofwords (ls l1) (ls l2))).
       eapply val_hiword_inject; eassumption.
       apply val_hiword_longofwords. 

  (*apply Val.lessdef_trans with (Val.loword (Val.longofwords (ls l1) (ls l2))).
  apply Val.loword_lessdef; auto. apply val_loword_longofwords.*)
  apply valinject_lessdef with (v2:=Val.loword (Val.longofwords (ls l1) (ls l2))).
       eapply val_loword_inject; eassumption.
       apply val_loword_longofwords. 

  eapply IHb; eauto.
- (* a param of type Tint *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param of type Tfloat *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param of type Tsingle *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* error case *)
  discriminate.
Qed.

Lemma call_regs_param_values:
  forall sg ls,
  map (call_regs ls) (loc_parameters sg) = map ls (loc_arguments sg).
Proof.
  intros. unfold loc_parameters. rewrite list_map_compose. 
  apply list_map_exten; intros. unfold call_regs, parameter_of_argument.
  exploit loc_arguments_acceptable; eauto. unfold loc_argument_acceptable. 
  destruct x; auto. destruct sl; tauto. 
Qed.

Lemma return_regs_arg_values:
  forall sg ls1 ls2,
  tailcall_is_possible sg = true ->
  map (return_regs ls1 ls2) (loc_arguments sg) = map ls2 (loc_arguments sg).
Proof.
  intros. apply list_map_exten; intros. 
  exploit loc_arguments_acceptable; eauto.
  exploit tailcall_is_possible_correct; eauto. 
  unfold loc_argument_acceptable, return_regs.
  destruct x; intros.
  rewrite pred_dec_true; auto. 
  contradiction.
Qed.

Lemma find_function_tailcall:
  forall tge ros ls1 ls2,
  ros_compatible_tailcall ros = true ->
  find_function tge ros (return_regs ls1 ls2) = find_function tge ros ls2.
Proof.
  unfold ros_compatible_tailcall, find_function; intros. 
  destruct ros as [r|id]; auto.
  unfold return_regs. destruct (in_dec mreg_eq r destroyed_at_call); simpl in H.
  auto. congruence.
Qed.

(** * Properties of the dataflow analysis *)

Lemma analyze_successors:
  forall f env bsh an pc bs s e,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ EqSet.Subset e' e.
Proof.
  unfold analyze; intros. exploit DS.fixpoint_solution; eauto.
  rewrite H2. unfold DS.L.ge. destruct (transfer f env bsh s an#s); intros.
  exists e0; auto. 
  contradiction.
Qed.

Lemma satisf_successors:
  forall j f env bsh an pc bs s e rs ls,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  satisf j rs ls e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ satisf j rs ls e'.
Proof.
  intros. exploit analyze_successors; eauto. intros [e' [A B]]. 
  exists e'; split; auto. eapply satisf_incr; eauto.
Qed.

(** Inversion on [transf_function] *)

Inductive transf_function_spec (f: RTL.function) (tf: LTL.function) : Prop :=
  | transf_function_spec_intro:  
      forall env an mv k e1 e2,
      wt_function f env ->
      analyze f env (pair_codes f tf) = Some an ->
      (LTL.fn_code tf)!(LTL.fn_entrypoint tf) = Some(expand_moves mv (Lbranch (RTL.fn_entrypoint f) :: k)) ->
      wf_moves mv ->
      transfer f env (pair_codes f tf) (RTL.fn_entrypoint f) an!!(RTL.fn_entrypoint f) = OK e1 ->
      track_moves env mv e1 = Some e2 ->
      compat_entry (RTL.fn_params f) (sig_args (RTL.fn_sig f)) (loc_parameters (fn_sig tf)) e2 = true ->
      can_undef destroyed_at_function_entry e2 = true ->
      RTL.fn_stacksize f = LTL.fn_stacksize tf ->
      RTL.fn_sig f = LTL.fn_sig tf ->
      transf_function_spec f tf.

Lemma transf_function_inv:
  forall f tf,
  transf_function f = OK tf ->
  transf_function_spec f tf.
Proof.
  unfold transf_function; intros.
  destruct (type_function f) as [env|] eqn:TY; try discriminate.
  destruct (regalloc f); try discriminate.
  destruct (check_function f f0 env) as [] eqn:?; inv H.
  unfold check_function in Heqr. 
  destruct (analyze f env (pair_codes f tf)) as [an|] eqn:?; try discriminate.
  monadInv Heqr. 
  destruct (check_entrypoints_aux f tf env x) as [y|] eqn:?; try discriminate.
  unfold check_entrypoints_aux, pair_entrypoints in Heqo0. MonadInv.
  exploit extract_moves_sound; eauto. intros [A B]. subst b.
  exploit check_succ_sound; eauto. intros [k EQ1]. subst b0.
  econstructor; eauto. eapply type_function_correct; eauto. congruence. 
Qed.

Lemma invert_code:
  forall f env tf pc i opte e,
  wt_function f env ->
  (RTL.fn_code f)!pc = Some i ->
  transfer f env (pair_codes f tf) pc opte = OK e ->
  exists eafter, exists bsh, exists bb,
  opte = OK eafter /\ 
  (pair_codes f tf)!pc = Some bsh /\
  (LTL.fn_code tf)!pc = Some bb /\
  expand_block_shape bsh i bb /\
  transfer_aux f env bsh eafter = Some e /\
  wt_instr f env i.
Proof.
  intros. destruct opte as [eafter|]; simpl in H1; try discriminate. exists eafter.
  destruct (pair_codes f tf)!pc as [bsh|] eqn:?; try discriminate. exists bsh. 
  exploit matching_instr_block; eauto. intros [bb [A B]].
  destruct (transfer_aux f env bsh eafter) as [e1|] eqn:?; inv H1. 
  exists bb. exploit wt_instr_at; eauto.
  tauto. 
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  LTL.funsig tf = RTL.funsig f.
Proof.
  intros; destruct f; monadInv H.
  destruct (transf_function_inv _ _ EQ). simpl; auto.
  auto.
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

Lemma find_function_translated:
  forall j ros rs fd ros' e e' ls
  (GFP: globalfunction_ptr_inject j),
  RTL.find_function ge ros rs = Some fd ->
  add_equation_ros ros ros' e = Some e' ->
  satisf j rs ls e' ->
  exists tfd,
  LTL.find_function tge ros' ls = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  unfold RTL.find_function, LTL.find_function; intros.
  destruct ros as [r|id]; destruct ros' as [r'|id']; simpl in H0; MonadInv.
  (* two regs *)
  (*LENB old proof:
  exploit add_equation_lessdef; eauto. intros LD. inv LD.
  eapply functions_translated; eauto.
  rewrite <- H2 in H. simpl in H. congruence.*)
  specialize (add_equation_inject _ _ _ _ _ H1); intros LD.
  simpl in LD. 
  destruct (Genv.find_funct_inv _ _ H) as [b Hb]. rewrite Hb in *. 
  rewrite Genv.find_funct_find_funct_ptr in H.
  destruct (GFP _ _ H).
  inv LD. rewrite H6 in H0; inv H0.
  eapply functions_translated; eauto.

  (* two symbols *)
  rewrite symbols_preserved. rewrite Heqo. 
  eapply function_ptr_translated; eauto.
Qed.

(*CompCert 2.1:
Lemma exec_moves:
  forall mv env rs s f sp bb m e e' ls,
  track_moves env mv e = Some e' ->
  wf_moves mv ->
  satisf rs ls e' ->
  wt_regset env rs ->
  exists ls',
    star step tge (Block s f sp (expand_moves mv bb) ls m)
               E0 (Block s f sp bb ls' m)
  /\ satisf rs ls' e.
Proof.
Check step. Locate step.
Opaque destroyed_by_op.
  induction mv; simpl; intros.
  (* base *)
- unfold expand_moves; simpl. inv H. exists ls; split. apply star_refl. auto.
  (* step *)
- destruct a as [src dst]. unfold expand_moves. simpl. 
  destruct (track_moves env mv e) as [e1|] eqn:?; MonadInv.
  assert (wf_moves mv). red; intros. apply H0; auto with coqlib. 
  destruct src as [rsrc | ssrc]; destruct dst as [rdst | sdst].
  (* reg-reg *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto. 
  econstructor. simpl. eauto. auto. auto.
  (* reg->stack *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto. 
  econstructor. simpl. eauto. auto.
  (* stack->reg *)
+ simpl in Heqb. exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto. 
  econstructor. auto. auto. 
  (* stack->stack *)
+ exploit H0; auto with coqlib. unfold wf_move. tauto.
Qed.*)

Lemma exec_moves:
  forall mv env rs s f sp bb m e e' ls j,
  track_moves env mv e = Some e' ->
  wf_moves mv ->
  satisf j rs ls e' ->
  wt_regset env rs ->
  exists ls',
    corestep_star LTL_eff_sem tge 
                (LTL_Block s f sp (expand_moves mv bb) ls) m
                (LTL_Block s f sp bb ls') m
  /\ satisf j rs ls' e.
Proof.
Opaque destroyed_by_op.
  induction mv; simpl; intros.
  (* base *)
- unfold expand_moves; simpl. inv H. exists ls; split. apply corestep_star_zero. auto.
  (* step *)
- destruct a as [src dst]. unfold expand_moves. simpl. 
  destruct (track_moves env mv e) as [e1|] eqn:?; MonadInv.
  assert (wf_moves mv). red; intros. apply H0; auto with coqlib. 
  destruct src as [rsrc | ssrc]; destruct dst as [rdst | sdst].
  (* reg-reg *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto.
  eapply corestep_star_trans; eauto. 
    eapply corestep_star_one. 
      econstructor. simpl. eauto. auto.
  (* reg->stack *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto.
  eapply corestep_star_trans; eauto. 
    eapply corestep_star_one. 
      econstructor. simpl. eauto.
  (* stack->reg *)
+ simpl in Heqb. exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto.
  eapply corestep_star_trans; eauto. 
    eapply corestep_star_one. 
      econstructor. simpl. eauto.
  (* stack->stack *)
+ exploit H0; auto with coqlib. unfold wf_move. tauto.
Qed.

Lemma Eff_exec_moves:
  forall mv env rs s f sp bb m e e' ls j,
  track_moves env mv e = Some e' ->
  wf_moves mv ->
  satisf j rs ls e' ->
  wt_regset env rs ->
  exists ls',
    effstep_star LTL_eff_sem tge EmptyEffect
                (LTL_Block s f sp (expand_moves mv bb) ls) m
                (LTL_Block s f sp bb ls') m
  /\ satisf j rs ls' e.
Proof.
Opaque destroyed_by_op.
  induction mv; simpl; intros.
  (* base *)
- unfold expand_moves; simpl. inv H. exists ls; split. apply effstep_star_zero. auto.
  (* step *)
- destruct a as [src dst]. unfold expand_moves. simpl. 
  destruct (track_moves env mv e) as [e1|] eqn:?; MonadInv.
  assert (wf_moves mv). red; intros. apply H0; auto with coqlib. 
  destruct src as [rsrc | ssrc]; destruct dst as [rdst | sdst].
  (* reg-reg *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto.
  eapply effstep_star_trans'; eauto. 
    eapply effstep_star_one. 
      econstructor. simpl. eauto. auto.
     auto.
  (* reg->stack *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto.
  eapply effstep_star_trans'; eauto. 
    eapply effstep_star_one. 
      econstructor. simpl. eauto.
    auto.
  (* stack->reg *)
+ simpl in Heqb. exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto.
  eapply effstep_star_trans'; eauto. 
    eapply effstep_star_one. 
      econstructor. simpl. eauto.
    auto.
  (* stack->stack *)
+ exploit H0; auto with coqlib. unfold wf_move. tauto.
Qed.

(*NEW - occurrence of sp in eval_expr means enforcing offset = Int.zero is 
  convenient and should be satisfied since old proof is an extension proof - *)
Definition sp_preserved (j:meminj) (sp sp':val) := 
    exists b b', sp = Vptr b Int.zero /\ sp' = Vptr b' Int.zero /\ 
                j b = Some(b',0).

Lemma sp_preserved_inject_incr: forall j sp sp' 
        (SP: sp_preserved j sp sp')
         j' (INC: inject_incr j j'),
      sp_preserved j' sp sp'.
Proof.
  intros. destruct SP as [b [b' [B [B' X]]]].
  apply INC in X. exists b, b'; eauto.
Qed.

(* The simulation relation *)
(*LENB: added parameter j:meminj,
        replaced lessdefs's by val_inject's,
        replaced step by corestep LTL_eff_sem
        added sp' and SP
        added Kripke-extension jj of j to enable proof of Lemma
          match_stackframes_inject_incr below
        added hypothesis EFFSTEP*)
Inductive match_stackframes (j:meminj): list RTL.stackframe -> list LTL.stackframe -> signature -> Prop :=
  | match_stackframes_nil: forall sg,
      match_stackframes j nil nil sg
  | match_stackframes_cons:
      forall res f sp pc rs s tf bb ls ts sg an e env sp'
        (STACKS: match_stackframes j s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (ANL: analyze f env (pair_codes f tf) = Some an)
        (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
        (WTF: wt_function f env)
        (WTRS: wt_regset env rs)
        (WTRES: subtype (proj_sig_res sg) (env res) = true)
        (SP: sp_preserved j sp sp')
        (STEPS: forall v ls1 m jj,
           inject_incr j jj ->
           (*Val.lessdef_list (encode_long (sig_res sg) v) (map ls1 (map R (loc_result sg))) ->*)
           val_list_inject jj (encode_long (sig_res sg) v) (map ls1 (map R (loc_result sg))) ->
           Val.has_type v (env res) ->
           agree_callee_save ls ls1 ->
           exists ls2,
           corestep_star LTL_eff_sem tge 
                           (LTL_Block ts tf sp' bb ls1) m
                           (LTL_State ts tf sp' pc ls2) m
           /\ satisf jj (rs#res <- v) ls2 e)
        (EFFSTEPS: forall v ls1 m jj,
           inject_incr j jj ->
           (*Val.lessdef_list (encode_long (sig_res sg) v) (map ls1 (map R (loc_result sg))) ->*)
           val_list_inject jj (encode_long (sig_res sg) v) (map ls1 (map R (loc_result sg))) ->
           Val.has_type v (env res) ->
           agree_callee_save ls ls1 ->
           exists ls2,
           effstep_star LTL_eff_sem tge EmptyEffect
                           (LTL_Block ts tf sp' bb ls1) m
                           (LTL_State ts tf sp' pc ls2) m
           /\ satisf jj (rs#res <- v) ls2 e),
      match_stackframes  j
        (RTL.Stackframe res f sp pc rs :: s)
        (LTL.Stackframe tf sp' ls bb :: ts)
        sg.

Lemma match_stackframes_inject_incr:
  forall j s ts sg 
  (MS:match_stackframes j s ts sg) 
  j' (INC: inject_incr j j'), 
  match_stackframes j' s ts sg.
Proof.
  intros. induction MS.
    econstructor; try eassumption.
  econstructor; try eassumption.
   eapply sp_preserved_inject_incr; eassumption.
   intros. eapply STEPS; try eassumption.
     eapply inject_incr_trans; eassumption.
   intros. eapply EFFSTEPS; try eassumption.
     eapply inject_incr_trans; eassumption.
Qed.  

(*LENB: added parameter (j:meminj), 
        changed type from RTL.state -> LTL.state -> Prop to  
           RTL_core -> mem -> LTL_core -> mem -> Prop,
        eliminated Mem.extends ( Mem.inject is enfoirced in MATCH below)
        added sp' and SP *)
Inductive match_states (j:meminj): RTL_core -> mem -> LTL_core -> mem -> Prop :=
  | match_states_intro:
      forall s f sp pc rs m ts tf ls m' an e env sp'
        (*j0 (INCJ: inject_incr j0 j)*)
        (STACKS: match_stackframes j s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (ANL: analyze f env (pair_codes f tf) = Some an)
        (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
        (SAT: satisf j rs ls e)
        (*(MEM: Mem.extends m m')*)
        (WTF: wt_function f env)
        (WTRS: wt_regset env rs)
        (SP: sp_preserved j sp sp'),
      match_states j (RTL_State s f sp pc rs) m
                     (LTL_State ts tf sp' pc ls) m'
  | match_states_call:
      forall s f args m ts tf ls m' (*j0
        (INCJ: inject_incr j0 j)*)
        (STACKS: match_stackframes j(*j0*) s ts (funsig tf))
        (FUN: transf_fundef f = OK tf)
        (*(ARGS: Val.lessdef_list args (decode_longs (sig_args (funsig tf)) (map ls (loc_arguments (funsig tf)))))*)
        (ARGS: val_list_inject j args (decode_longs (sig_args (funsig tf)) (map ls (loc_arguments (funsig tf)))))
        (AG: agree_callee_save (parent_locset ts) ls)
        (*(MEM: Mem.extends m m')*) 
        (WTARGS: Val.has_type_list args (sig_args (funsig tf))),
      match_states j (RTL_Callstate s f args) m
                     (LTL_Callstate ts tf ls) m'
  | match_states_return:
      forall s res m ts ls m' sg (*j0
        (INCJ: inject_incr j0 j)*)
        (STACKS: match_stackframes (*j0*)j s ts sg)
        (*(RES: Val.lessdef_list (encode_long (sig_res sg) res) (map ls (map R (loc_result sg))))*)
        (RES: val_list_inject j (encode_long (sig_res sg) res) (map ls (map R (loc_result sg))))
        (AG: agree_callee_save (parent_locset ts) ls)
        (*(MEM: Mem.extends m m')*) 
        (WTRES: Val.has_type res (proj_sig_res sg)),
      match_states j (RTL_Returnstate s res) m
                     (LTL_Returnstate ts (sig_res sg) ls) m'.

Lemma match_stackframes_change_sig:
  forall j s ts sg sg',
  match_stackframes j s ts sg ->
  sg'.(sig_res) = sg.(sig_res) ->
  match_stackframes j s ts sg'.
Proof.
  intros. inv H. 
  constructor. 
  econstructor; eauto.
  unfold proj_sig_res in *. rewrite H0; auto. 
  (*STEPS*)
  intros. unfold loc_result in H1; rewrite H0 in H1. 
          eauto.
  (*EFFSTEPS*) 
  intros. unfold loc_result in H1; rewrite H0 in H1. 
          eauto. 
Qed.

Lemma match_states_inject_incr:
  forall j S1 T1 m m' (MS:match_states j S1 m T1 m')
         j' (INC: inject_incr j j'),
  match_states j' S1 m T1 m'.
Proof.
  intros.
  inv MS.
    eapply match_states_intro; try eassumption. 
      eapply match_stackframes_inject_incr; try eassumption.
      eapply satisf_inject_incr; eassumption.
      eapply sp_preserved_inject_incr; eassumption.
    eapply match_states_call; try eassumption.
      eapply match_stackframes_inject_incr; try eassumption.
      eapply val_list_inject_incr; eassumption.
    eapply match_states_return; try eassumption.
      eapply match_stackframes_inject_incr; try eassumption.
      eapply val_list_inject_incr; eassumption.
Qed.

Ltac UseShape :=
  match goal with
  | [ WT: wt_function _ _, CODE: (RTL.fn_code _)!_ = Some _, EQ: transfer _ _ _ _ _ = OK _ |- _ ] =>
      destruct (invert_code _ _ _ _ _ _ _ WT CODE EQ) as (eafter & bsh & bb & AFTER & BSH & TCODE & EBS & TR & WTI); 
      inv EBS; unfold transfer_aux in TR; MonadInv
  end.

Remark addressing_not_long:
  forall env f addr args dst s r,
  wt_instr f env (Iload Mint64 addr args dst s) ->
  In r args -> r <> dst.
Proof.
  intros. 
  assert (forall ty, In ty (type_of_addressing addr) -> ty = Tint).
  { intros. destruct addr; simpl in H1; intuition. }
  inv H.
  assert (env r = Tint).
  { generalize args (type_of_addressing addr) H0 H1 H5.
    induction args0; simpl; intros.
    contradiction.
    destruct l. discriminate. InvBooleans. 
    destruct H2. subst a. 
    assert (t = Tint) by auto with coqlib. subst t. 
    destruct (env r); auto || discriminate. 
    eauto with coqlib. 
  }
  red; intros; subst r. rewrite H in H8; discriminate.
Qed.

(** The proof of semantic preservation is a simulation argument of the
    "plus" kind. *)


Definition MATCH mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
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

Fixpoint locs_diff (locs : list loc) :=
  match locs with
    | nil => True
    | a :: locs' => Loc.notin a locs' /\ locs_diff locs'
  end.

Fixpoint locs_val_types (locs : list loc) (vals : list val) :=
  match locs,vals with
    | nil,nil => True
    | R _::locs',v::vals' => locs_val_types locs' vals'
    | S Outgoing ofs t::locs',v::vals' => 
      Val.has_type v t /\ locs_val_types locs' vals'
    | _,_ => False
  end.

Lemma map_locmap_setlist_eq locs args m : 
  locs_diff locs -> 
  locs_val_types locs args ->
  length args=length locs ->
  map (Locmap.setlist locs args m) locs = args.
Proof.
  revert m args; induction locs.
  simpl. solve[intros ? ? ?; destruct args; try inversion 2; auto].
  destruct args; inversion 3. simpl. rewrite IHlocs; auto.
  rewrite Locmap.gsetlisto. rewrite Locmap.gss. 
  destruct a; auto.
  rewrite Val.load_result_same; auto.
  simpl in H0. destruct sl; try solve[inv H0]. destruct H0 as [H2 H4]; auto.
  simpl in H. solve[destruct H; auto].
  simpl in H. solve[destruct H; auto].
  simpl in H0. 
  destruct a; try solve[inv H0]. 
  solve[auto].
  destruct sl; try solve[inv H0]. destruct H0 as [? ?]; auto.
Qed.

Fixpoint all_diff (l : list loc) : Prop :=
  match l with
    | nil => True
    | a :: l' => Forall (Loc.diff a) l' /\ all_diff l'
  end.

Lemma loc_arguments_rec_all_diff tyl ofs : all_diff (loc_arguments_rec tyl ofs).
Proof.
  revert ofs. induction tyl; simpl; auto.
  intros ofs. destruct a. simpl. split.
  clear IHtyl.
  { remember (ofs + 1) as k.
    assert (k > ofs). omega.
    clear Heqk.
    revert k H. induction tyl. simpl. auto.
    simpl. destruct a. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    constructor. simpl. right; left; omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega. }
  eapply IHtyl; eauto.
  simpl. split.
  { clear IHtyl. 
    remember (ofs + 2) as k.
    assert (k > ofs+1). omega.
    clear Heqk.
    revert k H. induction tyl. simpl. auto.
    simpl. destruct a. intros. constructor. 
    simpl. right; left; omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    constructor. simpl. right; left; omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega. }
  eapply IHtyl; eauto.
  simpl. split. constructor. right. right. simpl. omega.
  { clear IHtyl. 
    remember (ofs + 2) as k.
    assert (k > ofs+1). omega.
    clear Heqk.
    revert k H. induction tyl. simpl. 
    intros. constructor.
    intros. simpl. destruct a. constructor. simpl. right; left; omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    constructor. simpl. right; left; omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega. }
  split. 
  { clear IHtyl. 
    remember (ofs + 2) as k.
    assert (k > ofs+1). omega.
    clear Heqk.
    revert k H. induction tyl. simpl. 
    intros. constructor.
    intros. simpl. destruct a. constructor. simpl. right; left; omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    constructor. simpl. right; left; omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega. }
  eapply IHtyl; eauto.
  simpl. split. 
  { clear IHtyl. 
    remember (ofs + 1) as k.
    assert (k > ofs). omega.
    clear Heqk.
    revert k H. induction tyl. simpl. 
    intros. constructor.
    intros. simpl. destruct a. constructor. simpl. right; left; omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    constructor. simpl. right; left; omega.
    specialize (IHtyl (k+2)). apply IHtyl. omega.
    intros. constructor. simpl. right; left. omega.
    specialize (IHtyl (k+1)). apply IHtyl. omega. }
  eapply IHtyl; eauto. 
Qed.

Lemma all_diff_locs_diff l : all_diff l -> locs_diff l.
Proof.
induction l. simpl; auto.
simpl. intros [H H2]. split; auto.
clear - H. revert a H. induction l. simpl; auto. 
simpl. intros a0; inversion 1; subst. split; auto.
Qed.

Lemma loc_arguments_rec_locs_diff tyl ofs : locs_diff (loc_arguments_rec tyl ofs).
Proof.
  apply all_diff_locs_diff.
  apply loc_arguments_rec_all_diff.
Qed.

Lemma has_type_list_locs_val_types vals l z :
  Val.has_type_list vals l ->
  locs_val_types (loc_arguments_rec l z) (val_casted.encode_longs l vals).
Proof.
revert vals z; induction l. simpl; auto. simpl.
destruct a. simpl. destruct vals; auto. simpl; intros z [? ?]. solve[split; auto].
intros vals z; destruct vals. inversion 1. inversion 1; subst. simpl. solve[split; auto].
intros vals z; destruct vals. inversion 1. inversion 1; subst. simpl. 
  destruct v; split; auto; try solve[econstructor].
  split; auto; try solve[econstructor].
  split; auto; try solve[econstructor].
  solve[split; auto; try solve[econstructor]].
intros vals z; destruct vals. inversion 1. inversion 1; subst. simpl. solve[split; auto].
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
      (Ini: initial_core rtl_eff_sem ge v1 vals1 = Some c1)
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
  initial_core LTL_eff_sem tge v2 vals2 = Some c2 /\
  MATCH
    (initial_SM DomS DomT
       (REACH m1 (fun b : block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2 (fun b : block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof. intros.
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  simpl. exists (LTL_Callstate nil tf 
                  (Locmap.setlist (loc_arguments (funsig tf)) 
                    (val_casted.encode_longs (sig_args (funsig tf)) vals2) 
                    (Locmap.init Vundef))). 
 split. 
    destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. rewrite C in Heqzz. inv Heqzz.
    unfold tge in FP. rewrite D in FP. inv FP.
    unfold LTL_eff_sem, LTL_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    rewrite D.

  assert (val_casted.val_has_type_list_func vals2
           (sig_args (funsig tf))=true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H1; simpl in H1. solve[inv H1].
    assert (sig_args (funsig tf)
          = sig_args (RTL.funsig (Internal f))) as ->.
    { erewrite sig_function_translated; eauto. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (RTL.funsig (Internal f)))); auto. inv H1. }
  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H1; inv H1. }
  monadInv TF. rename x into tf.
  solve[simpl; auto].

  intros CONTRA. solve[elimtype False; auto].

  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    revert H1.
    case_eq (val_casted.val_has_type_list_func vals1
               (sig_args (RTL.funsig (Internal f))) && val_casted.vals_defined vals1).
    intros H2. inversion 1; subst. clear H1.
    eapply match_states_call.
      constructor.
      assumption.
      rewrite initial_SM_as_inj.
          unfold vis, initial_SM; simpl.
          apply forall_inject_val_list_inject.
          eapply restrict_forall_vals_inject; try eassumption.

          clear - H2 VInj TF.

          rewrite andb_true_iff in H2. destruct H2.

          assert (A: sig_args (funsig tf) = sig_args (RTL.funsig (Internal f))).
          { erewrite sig_function_translated; eauto. }

          assert (B: Val.has_type_list vals2 (sig_args (funsig tf))).
          { rewrite val_casted.val_has_type_list_func_charact; auto.
            eapply val_casted.val_list_inject_hastype. 
            eapply forall_inject_val_list_inject; eauto. auto.
            rewrite A, H; auto. }

          assert (len: 
            length (val_casted.encode_longs (sig_args (funsig tf)) vals2) =
            length (loc_arguments (funsig tf))).
          { rewrite <-A in H. clear A. clear H H0 vals1 VInj.
            destruct (funsig tf). simpl. unfold loc_arguments. simpl. 
            revert vals2 B; generalize 0; induction sig_args; auto.
            destruct a; simpl. 
            destruct vals2; simpl; try solve[inversion 1].
            intros [H2 H3]. f_equal. solve[erewrite IHsig_args; eauto].
            destruct vals2; inversion 1; subst. simpl. f_equal.
            solve[erewrite IHsig_args; eauto].
            destruct vals2; simpl; try solve[inversion 1].
            intros [H2 H3]. destruct v; simpl. f_equal. 
            solve[erewrite IHsig_args; eauto].
            solve[erewrite IHsig_args; eauto].
            solve[erewrite IHsig_args; eauto].
            solve[erewrite IHsig_args; eauto].
            solve[erewrite IHsig_args; eauto].
            destruct vals2. simpl. inversion 1.
            simpl. intros [H2 H3]. f_equal. 
            solve[erewrite IHsig_args; eauto]. }

          rewrite map_locmap_setlist_eq.
          rewrite val_casted.decode_encode_longs; auto.
          apply loc_arguments_rec_locs_diff.
          apply has_type_list_locs_val_types; auto.
          solve[apply len].

        intros. apply REACH_nil. rewrite H; intuition.
        simpl. red; intros. red in H. 
          destruct l.
            rewrite Locmap.gsetlisto; trivial. 
            apply Loc.notin_iff. intros. apply loc_arguments_rec_charact in H0.
            destruct l'; try contradiction. constructor.
          rewrite Locmap.gsetlisto; trivial. 
            apply Loc.notin_iff. intros. apply loc_arguments_rec_charact in H0.
            destruct l'; try contradiction. destruct sl0; try contradiction.
            destruct sl; try constructor. congruence. congruence. trivial.
    rewrite andb_true_iff in H2. destruct H2. 
    erewrite sig_function_translated; eauto. 
    solve[rewrite val_casted.val_has_type_list_func_charact; auto].
    solve[inversion 2].
  intuition.
    rewrite match_genv_meminj_preserves_extern_iff_all.
      assumption.
      apply BB.
      apply EE.
    (*as in selectionprffEFF*)
    (*globalfunctionptr*)
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

Lemma loc_result_locs_diff sig : locs_diff (map R (loc_result sig)).
Proof.
  unfold loc_result.
  destruct (sig_res sig). destruct t; simpl; auto.
  split; auto. split; auto. intros; congruence.
  simpl; split; auto.
Qed.

Lemma MATCH_afterExternal: forall
      (GDE : genvs_domain_eq ge tge)
      mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH mu st1 m1 st2 m2)
      (AtExtSrc : at_external rtl_eff_sem st1 = Some (e, ef_sig, vals1))
      (AtExtTgt : at_external LTL_eff_sem st2 = Some (e', ef_sig', vals2))
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
  after_external rtl_eff_sem (Some ret1) st1 =Some st1' /\
  after_external LTL_eff_sem (Some ret2) st2 = Some st2' /\
  MATCH mu' st1' m1' st2' m2'.
Proof. intros.
simpl.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 simpl in *. inv MC; simpl in *. inv AtExtSrc. Focus 2. inv AtExtSrc.
 destruct f; inv AtExtSrc. 
 destruct tf; inv AtExtTgt.
 eexists. eexists.
    split. reflexivity.
    split. reflexivity.
 simpl in *.
 inv FUN.
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
 
assert (retty1: Val.has_type ret1 (proj_sig_res (ef_sig e'))).
{ admit. (*ret typing condition*)}

split. 
  unfold vis in *. 
  rewrite replace_externs_as_inj, replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
  apply match_states_return; try eauto.
      clear RRC RR1 RC' PHnu' INCvisNu' UnchLOOR UnchPrivSrc.
      destruct INC. rewrite replace_locals_extern in H.
        rewrite replace_locals_frgnBlocksTgt, replace_locals_frgnBlocksSrc,
                replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc,
                replace_locals_locBlocksTgt, replace_locals_locBlocksSrc,
                replace_locals_extBlocksTgt, replace_locals_extBlocksSrc,
                replace_locals_local in H0.
        destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
        eapply match_stackframes_inject_incr; try eassumption.
          red; intros. destruct (restrictD_Some _ _ _ _ _ H9); clear H9.
          apply restrictI_Some.
            apply joinI.
            destruct (joinD_Some _ _ _ _ _ H10).
              apply H in H9. left; trivial.
            destruct H9. right. rewrite H0 in H12.
              split; trivial.
              destruct (disjoint_extern_local _ WDnu' b); trivial. congruence.          
          rewrite H3, H7 in H11.
            remember (locBlocksSrc nu' b) as d.
            destruct d; trivial; simpl in *.
            apply andb_true_iff.
            split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H11). intuition.
               apply REACH_nil. unfold exportedSrc. 
                 apply frgnSrc_shared in H11; trivial. rewrite H11; intuition.

       remember (sig_res (ef_sig e')) as o. 
        { rewrite map_locmap_setlist_eq.
          apply encode_long_inject.
          inv RValInjNu'; try econstructor. 
          eapply restrictI_Some; try eassumption.
          destruct (as_inj_DomRng _ _ _ _ H); trivial.
          rewrite H0; simpl. unfold DomSrc in H0.
          remember (locBlocksSrc nu' b1) as d.
          destruct d; simpl in *. trivial.
          eapply REACH_nil. unfold exportedSrc. apply orb_true_iff; left.
          unfold getBlocks. simpl. solve[destruct (eq_block b1 b1); auto]. 
          solve[auto].
          solve[apply loc_result_locs_diff].
          unfold encode_long,loc_result. subst o.          
          destruct (sig_res (ef_sig e')). destruct t; auto.
          simpl; auto. simpl; auto. simpl; auto. simpl; auto. solve[simpl; auto].
          unfold encode_long,loc_result. subst o.
          destruct (sig_res (ef_sig e')). destruct t; auto.
          solve[simpl; auto]. }

        red; intros. rewrite AG. apply eq_sym. red in H. 
          destruct l.
            rewrite Locmap.gsetlisto; trivial. 
            apply Loc.notin_iff. intros. 
            apply list_in_map_inv in H0. destruct H0 as [rr [? ?]]. subst. 
            apply loc_result_caller_save in H1. intros N; subst. apply (H H1).
          rewrite Locmap.gsetlisto; trivial. 
            apply Loc.notin_iff. intros.
            apply list_in_map_inv in H0. destruct H0 as [rr [? ?]]. subst.
            constructor. 
          assumption.

unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
(*last goal: globalfunction_ptr_inject *)
  red; intros. destruct (GFP _ _ H1). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed.

Lemma MATCH_corestep: forall 
       st1 m1 st1' m1' 
       (CS: corestep rtl_eff_sem ge st1 m1 st1' m1')
       st2 mu m2 (MTCH: MATCH mu st1 m1 st2 m2),
exists st2' m2' mu',
   corestep_plus LTL_eff_sem tge st2 m2 st2' m2'
  /\ intern_incr mu mu'
  /\ sm_inject_separated mu mu' m1 m2
  /\ sm_locally_allocated mu mu' m1 m2 m1' m2'
  /\ MATCH mu' st1' m1' st2' m2'
  /\ SM_wd mu' /\ sm_valid mu' m1' m2'.
Proof. intros.
   destruct CS; intros; destruct MTCH as [MSTATE PRE];
   inv MSTATE; try UseShape.

(* nop *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit exec_moves; eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X.
      eapply corestep_star_one. 
       econstructor; eauto. 
  (*for some reason, calling intuition here seems to delete the assumption WTF,
    which is, however, needed... So we proceed in smaller steps*)
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  split; trivial.

(* op move *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.  
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X.
      eapply corestep_star_one. 
       econstructor; eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. eapply subst_reg_satisf; eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  split; trivial.

(* op makelong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.  
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X.
      eapply corestep_star_one. 
       econstructor; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
           eapply subst_reg_kind_satisf_makelong. eauto. eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  split; trivial.

(* op lowlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X.
      eapply corestep_star_one. 
       econstructor; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
           eapply subst_reg_kind_satisf_lowlong. eauto. eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  split; trivial.

(* op highlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X.
      eapply corestep_star_one. 
       econstructor; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
           eapply subst_reg_kind_satisf_highlong. eauto. eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  split; trivial.

(* op regular *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
(*  exploit transfer_use_def_satisf; eauto. intros [X Y].*)
  exploit transfer_use_def_satisf_inject; eauto. intros [X Y].

  (*exploit eval_operation_lessdef; eauto. intros [v' [F G]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit eval_operation_inject; eauto. intros [v' [F G]].
 
  exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1.
    eapply corestep_star_trans.
      eapply corestep_star_one. 
       econstructor. instantiate (1 := v'). rewrite <- F.  
       rewrite eval_shift_stack_operation.
        apply eval_operation_preserved. exact symbols_preserved.
       eauto.
    eapply corestep_star_trans. eexact A2.
      eapply corestep_star_one. constructor.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
         intros [enext [U V]].
         split. econstructor; try eassumption.
                exists b, b'; eauto.
         intuition.
  split; trivial. 

(* op dead *)
- destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit exec_moves; eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans.
      eexact X.
      eapply corestep_star_one. econstructor; eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
         eapply reg_unconstrained_satisf; eauto. 
         intros [enext [U V]].
         split. econstructor; eauto.
                 eapply wt_exec_Iop; eauto.
         intuition.
  split; trivial.  

(* load regular *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 

  (*exploit transfer_use_def_satisf; eauto. intros [X Y].*)
  exploit transfer_use_def_satisf_inject; eauto. intros [X Y].

  (*exploit eval_addressing_lessdef; eauto. intros [a' [F G]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; eauto. intros [a' [F G]].

  (*exploit Mem.loadv_extends; eauto. intros [v' [P Q]]. *)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))); eauto. intros [v' [P Q]].

  exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1. 
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. instantiate (1 := a'). rewrite <- F.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eauto.
          eauto.
    eapply corestep_star_trans.
      eexact A2. 
      eapply corestep_star_one. 
        constructor.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  split; trivial. 

(* load pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  (*assert (LD1: Val.lessdef_list rs##args (reglist ls1 args1')).
  { eapply add_equations_lessdef; eauto. }*)
  assert (LD1: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls1 args1')).
  { eapply add_equations_inject; eauto. }

  (*exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eassumption. intros [a1' [F1 G1]].
    (*unfold shift_stack_addressing in F1. simpl in F1. rewrite Int.add_zero_l in F1.*)

  (*exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu)) m m2 Mint32).
       eapply MInjR. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2). 
  
  set (ls2 := Locmap.set (R dst1') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls2 e2).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto. 
    eapply reg_unconstrained_satisf. eauto. 
    eapply add_equations_satisf; eauto. assumption.
    rewrite Regmap.gss.
       eapply val_lessdef_inject_compose with v1'; try eassumption.   
         unfold v1', kind_first_word.
         destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 

  (*assert (LD3: Val.lessdef_list rs##args (reglist ls3 args2')).*)
  assert (LD3: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls3 args2')).
  { replace (rs##args) with ((rs#dst<-(Val.longofwords v1 v2))##args). 
    eapply add_equations_inject; eauto. 
    apply list_map_exten; intros. rewrite Regmap.gso; auto. 
    eapply addressing_not_long; eauto. 
  }
  (*exploit eval_addressing_lessdef. eexact LD3.*)
  exploit eval_addressing_inject; try eexact LD3. eassumption. eapply Rsp.
  eapply eval_offset_addressing; eauto. intros [a2' [F2 G2]].

  (*exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G2. intros (v2'' & LOAD2' & LD4).*)
  exploit Mem.loadv_inject. eapply MInjR. eexact LOAD2. eexact G2. intros (v2'' & LOAD2' & LD4).

  set (ls4 := Locmap.set (R dst2') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls3)).
  assert (SAT4: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls4 e0).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto. 
    eapply add_equations_satisf; eauto. assumption.
    apply val_lessdef_inject_compose with v2'; auto. 
    rewrite Regmap.gss. unfold v2', kind_second_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
  }
  exploit (exec_moves mv3); eauto. intros [ls5 [A5 B5]].
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1. 
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. instantiate (1 := a1'). rewrite <- F1.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD1'.
          instantiate (1 := ls2); auto.
    eapply corestep_star_trans.
      eexact A3. 
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. instantiate (1 := a2'). rewrite <- F2.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD2'. instantiate (1 := ls4); auto.
    eapply corestep_star_trans.
      eexact A5.
      eapply corestep_star_one. constructor.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  split; trivial. 

(* load first word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 

  (*assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }*)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (LD1: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls1 args')).
  { eapply add_equations_inject; eauto. }

  (*exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD1; try eassumption. intros [a1' [F1 G1]].

  (*exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit Mem.loadv_inject. eapply MInjR. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).  
  
  set (ls2 := Locmap.set (R dst') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply val_lessdef_inject_compose with v1'; auto. 
    unfold v1', kind_first_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1. 
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. instantiate (1 := a1'). rewrite <- F1.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD1'.
          instantiate (1 := ls2); auto.
    eapply corestep_star_trans.
      eexact A3. 
      eapply corestep_star_one. 
        constructor.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  split; trivial. 

(* load second word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
 
  (*assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }*)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (LD1: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls1 args')).
  { eapply add_equations_inject; eauto. }

  (*exploit eval_addressing_lessdef. eexact LD1.*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD1. eassumption. eapply Rsp.
 
  eapply eval_offset_addressing; eauto. intros [a1' [F1 G1]].

  (*exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G1. intros (v2'' & LOAD2' & LD2).*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit Mem.loadv_inject. eapply MInjR. eexact LOAD2. eexact G1. intros (v2'' & LOAD2' & LD2).  
  
  set (ls2 := Locmap.set (R dst') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls1)).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply val_lessdef_inject_compose with v2'; auto. 
    unfold v2', kind_second_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1. 
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. instantiate (1 := a1'). rewrite <- F1.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD2'.
          instantiate (1 := ls2); auto.
    eapply corestep_star_trans.
      eexact A3. 
      eapply corestep_star_one. 
        constructor.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  split; trivial. 

(* load dead *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans. 
      eapply corestep_plus_one. 
        econstructor; eauto. 
    eapply corestep_star_trans. eexact X. 
      eapply corestep_star_one. econstructor; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
         eapply reg_unconstrained_satisf; eauto. 
         intros [enext [U V]].
         split. econstructor; eauto.
                eapply wt_exec_Iload; eauto.
         intuition.
  split; eapply PRE.

(* store *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].

  (*exploit add_equations_lessdef; eauto. intros LD. simpl in LD. inv LD. *)
  exploit add_equations_inject; eauto. intros LD. simpl in LD. inv LD. 

  (*exploit eval_addressing_lessdef; eauto. intros [a' [F G]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD. eapply PGR. eapply Rsp. eassumption. eassumption.
  intros [a' [F G]].
 
  (*exploit Mem.storev_extends; eauto. intros [m'' [P Q]].*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))); try eassumption.
     intros [m'' [P Q]].
  eexists; exists m'', mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X. 
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. instantiate (1 := a'). rewrite <- F.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eauto.
          eauto.
      eapply corestep_star_one.
        constructor. 
  assert (SMV': sm_valid mu m' m'').
        split; intros; 
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (storev_freshloc _ _ _ _ _ P);
            try rewrite (storev_freshloc _ _ _ _ _ H1); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. 
          eapply can_undef_satisf; eauto. eapply add_equations_satisf; eauto.
         intros [enext [U V]].
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
         destruct a; inv H1.
           eapply REACH_Store; try eassumption. 
           inv G. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.   
                  rewrite H1 in H5. inv H5.
                  destruct (restrictD_Some _ _ _ _ _ H8); trivial.

         exploit (Mem.storev_mapped_inject (as_inj mu)). eassumption. eassumption. 
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
         intros [m2'' [ST2 INJ]]. rewrite ST2 in P. inv P. eassumption. 
   split; trivial.

(* store 2 *)
- exploit Mem.storev_int64_split; eauto. 
  replace (if big_endian then Val.hiword rs#src else Val.loword rs#src)
     with (sel_val kind_first_word rs#src)
       by (unfold kind_first_word; destruct big_endian; reflexivity).
  replace (if big_endian then Val.loword rs#src else Val.hiword rs#src)
     with (sel_val kind_second_word rs#src)
       by (unfold kind_second_word; destruct big_endian; reflexivity).
  intros [m1 [STORE1 STORE2]].
  exploit (exec_moves mv1); eauto. intros [ls1 [X Y]].

  (*exploit add_equations_lessdef. eexact Heqo1. eexact Y. intros LD1.*)
  exploit add_equations_inject. eexact Heqo1. eexact Y. intros LD1.

  (*exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo1. eexact Y. *)
  exploit add_equation_inject. eapply add_equations_satisf. eexact Heqo1. eexact Y. 

  simpl. intros LD2.
  set (ls2 := undef_regs (destroyed_by_store Mint32 addr) ls1).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) rs ls2 e1).
    eapply can_undef_satisf. eauto. 
    eapply add_equation_satisf. eapply add_equations_satisf; eauto.

  (*exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD1; try eassumption. intros [a1' [F1 G1]].

  (* assert (F1': eval_addressing tge sp addr (reglist ls1 args1') = Some a1').
    rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.*)
  assert (F1': eval_addressing tge (Vptr b' Int.zero) addr (reglist ls1 args1') = Some a1').
    rewrite <- F1. rewrite eval_shift_stack_addressing.
    apply eval_addressing_preserved. exact symbols_preserved.

  (*exploit Mem.storev_extends. eauto. eexact STORE1. eexact G1. eauto. *)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))).
      eapply MInjR. eapply STORE1. eapply G1. eauto.
  intros [m1' [STORE1' EXT1]]. 

  exploit (exec_moves mv2); eauto. intros [ls3 [U V]].

  (*exploit add_equations_lessdef. eexact Heqo. eexact V. intros LD3.*)
  exploit add_equations_inject. eexact Heqo. eexact V. intros LD3.

  (*exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo. eexact V.*)
  exploit add_equation_inject. eapply add_equations_satisf. eexact Heqo. eexact V.

  simpl. intros LD4.

  (*exploit eval_addressing_lessdef. eexact LD3. eauto. intros [a2' [F2 G2]].*)
  exploit eval_addressing_inject; try eexact LD3. eapply PGR. eapply Rsp. eauto. intros [a2' [F2 G2]].

  (*assert (F2': eval_addressing tge sp addr (reglist ls3 args2') = Some a2').
    rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.*)
  assert (F2': eval_addressing tge (Vptr b' Int.zero) addr (reglist ls3 args2') = Some a2').
    rewrite <- F2. rewrite eval_shift_stack_addressing.
    apply eval_addressing_preserved. exact symbols_preserved.

  exploit eval_offset_addressing. eauto. eexact F2'. intros F2''.

  (*exploit Mem.storev_extends. eexact EXT1. eexact STORE2. 
     apply Val.add_lessdef. eexact G2. eauto. eauto. *)
  exploit Mem.storev_mapped_inject. eexact EXT1. eexact STORE2.
     apply val_add_inject. eexact G2. eauto. eauto. 
  intros [m2' [STORE2' EXT2]].


  eexists; exists m2', mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact X.
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. eexact F1'. eexact STORE1'. instantiate (1 := ls2). auto.
    eapply corestep_star_trans. eexact U.
    eapply corestep_star_trans.
      eapply corestep_star_one.
        econstructor. eexact F2''. eexact STORE2'. eauto. 
      eapply corestep_star_one.
        constructor.
  assert (SMV': sm_valid mu m' m2').
        split; intros; 
          eapply storev_valid_block_1; try eassumption.
            eapply storev_valid_block_1; try eassumption.
              eapply SMV; assumption.
            eapply storev_valid_block_1; try eassumption.
              eapply SMV; assumption.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. assert (FWD2' : mem_forward m1' m2').
            destruct a2'; inv STORE2'.
            eapply store_forward; eassumption. 
         assert (FWD1': mem_forward m2 m1').
            destruct a1'; inv STORE1'.
            eapply store_forward; eassumption. 
         assert (FWD1: mem_forward m m1).
            destruct a; inv STORE1.
            eapply store_forward; eassumption. 
         assert (FWD2: mem_forward m1 m').
            destruct a; inv STORE2.
            eapply store_forward; eassumption.
         apply sm_locally_allocatedChar. 
         repeat split; extensionality bb;
            try (rewrite <- (freshloc_trans m m1 m'); trivial);
            try (rewrite <- (freshloc_trans m2 m1' m2'); trivial);
            try (rewrite (storev_freshloc _ _ _ _ _ STORE1));
            try (rewrite (storev_freshloc _ _ _ _ _ STORE2));
            try (rewrite (storev_freshloc _ _ _ _ _ STORE1'));
            try (rewrite (storev_freshloc _ _ _ _ _ STORE2')); intuition.
  split.
  { (*MATCH*) 
     exploit satisf_successors; eauto. simpl; eauto.
           eapply can_undef_satisf. eauto.
           eapply add_equation_satisf. eapply add_equations_satisf; eauto.
     intros [enext [P Q]].
     split. econstructor; eauto. exists b, b'; eauto.
     intuition.
     (*REACH_closed m' (vis mu)*)
         destruct a; inv STORE1.
         inv G2. destruct (restrictD_Some _ _ _ _ _ H5).
         assert (RC1: REACH_closed m1 (vis mu)).
           eapply REACH_Store; try eassumption. 
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst. 
                  clear - H6 LD2.   
                    rewrite H6 in LD2. inv LD2.
                    destruct (restrictD_Some _ _ _ _ _ H2); trivial.
         eapply REACH_Store; try eassumption.
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
           destruct Hoff; try contradiction.
           exfalso. clear - H6 WTRS WTI. inv WTI. clear H2 H7.
           specialize (WTRS src).
           rewrite H6 in *. simpl in WTRS.
           remember (env src) as srcTy; destruct srcTy; inv WTRS.
           inv H5.
     (*Mem.inject (as_inj mu) m' m2'*)
       clear - H1 G1 G2 MInj STORE1' STORE1 STORE2' STORE2 LD2 LD4. 
         destruct a; inv H1.
         inv G2. inv G1. rewrite H3 in H2. inv H2.
         exploit (Mem.storev_mapped_inject (as_inj mu)).
             eapply MInj. eapply STORE1.
             econstructor. eapply (restrictD_Some _ _ _ _ _ H3). reflexivity.
             eapply val_inject_incr; try eapply LD2. apply restrict_incr.
         intros [m1'' [ST1 INJ1]]. clear MInj.
         rewrite ST1 in STORE1'. inv STORE1'.
         exploit (Mem.storev_mapped_inject (as_inj mu)).
             eapply INJ1. eapply STORE2.
           simpl. econstructor. eapply (restrictD_Some _ _ _ _ _ H3). reflexivity.
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
         intros [m2'' [ST2 INJ2]]. clear - INJ2 ST2 STORE2'.
            simpl in *. rewrite Int.add_assoc in *.
            rewrite (Int.add_commut (Int.repr delta)) in STORE2'.
            rewrite ST2 in STORE2'. inv STORE2'. assumption.
  }
  split; trivial.

(* call *)
- set (sg := RTL.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  set (res' := map R (loc_result sg)) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit find_function_translated. eauto. eauto. eauto.
    eapply satisf_inject_incr. 
      eapply add_equations_args_satisf. eauto. eassumption.
      apply restrict_incr. 
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  eexists; eexists; exists mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1.
      eapply corestep_star_one. econstructor; eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit analyze_successors; eauto. simpl. left; eauto. intros [enext [U V]].
(*         destruct SP as [spb [spb' [B [B' Rsp]]]]; subst.*)
(*         assert (INC: inject_incr (fun b => if eq_block b spb then Some(spb',0) else j0 b)
                               (restrict (as_inj mu) (vis mu))).
           red; intros. destruct (eq_block b spb); subst. inv H1. assumption. 
                apply INCJ; assumption.*)
         split. econstructor; eauto.
                  econstructor; eauto.
                   inv WTI. rewrite SIG. auto.
                   intros. exploit (exec_moves mv2). eauto. eauto.
                       eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
                         eapply add_equation_ros_satisf; eauto.
                         eapply satisf_inject_incr.   
                           eapply add_equations_args_satisf; eauto. 
                           eassumption.
                         congruence.
                       apply wt_regset_assign; auto.
                       intros [ls2 [A2 B2]].
                       exists ls2; split. 
                       eapply corestep_star_trans. eexact A2.
                         eapply corestep_star_one. constructor.
                       apply satisf_incr with eafter; auto.
                   intros. exploit (Eff_exec_moves mv2). eauto. eauto.
                       eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
                         eapply add_equation_ros_satisf; eauto.
                         eapply satisf_inject_incr.   
                           eapply add_equations_args_satisf; eauto. 
                           eassumption.
                         congruence.
                       apply wt_regset_assign; auto.
                       intros [ls2 [A2 B2]].
                       exists ls2; split. 
                       eapply effstep_star_trans'. eexact A2.
                         eapply effstep_star_one. constructor.
                         auto.
                       apply satisf_incr with eafter; auto.
 
                   rewrite SIG. eapply add_equations_args_inject; eauto.
                       inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
                   simpl. red; auto.
                   inv WTI. rewrite SIG. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.
         intuition.
   split; trivial.

(* tailcall *)
- set (sg := RTL.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
   assert (GFPR: globalfunction_ptr_inject (restrict (as_inj mu) (vis mu))). 
            eapply restrict_GFP_vis; eassumption.
  destruct SP as [spb [spb' [B [B' Rsp]]]]; subst. inv B.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  exploit (free_parallel_inject (as_inj mu)); eauto. intros [m'' [P Q]]. 
  exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]]. 
  exploit find_function_translated. eauto. eauto. eauto. eapply add_equations_args_satisf; eauto. 
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  simpl in *. rewrite Zplus_0_r in P.
  eexists; exists m'', mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans.
      eexact A1. 
      eapply corestep_star_one. econstructor; eauto.
        rewrite <- E. apply find_function_tailcall; auto. 
        replace (fn_stacksize tf) with (RTL.fn_stacksize f); eauto.
        destruct (transf_function_inv _ _ FUN); auto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H2).
        repeat split; extensionality bb; intuition.
  assert (SMV': sm_valid mu m' m'').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
  split. split. econstructor; eauto.
                  eapply match_stackframes_change_sig; eauto. rewrite SIG. rewrite e0. decEq.
                   destruct (transf_function_inv _ _ FUN); auto.
                  rewrite SIG. rewrite return_regs_arg_values; auto. eapply add_equations_args_inject; eauto.
                  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
                  apply return_regs_agree_callee_save.
                  rewrite SIG. inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
  split; trivial. 

(* builtin *) 
- assert (WTRS': wt_regset env (rs#res <- v)) by (eapply wt_exec_Ibuiltin; eauto).
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  unfold satisf in B1.
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) rs ## args
         (decode_longs (sig_args (ef_sig ef)) (map ls1 (map R args')))).
    eapply add_equations_args_inject; try eassumption.
      inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.     
  exploit (inlineable_extern_inject ge tge); try eapply PRE. eapply GDE_lemma. 
         eassumption. eassumption.
  intros [mu' [v' [m'' [TEC [ResInj [MINJ' [UNMAPPED [LOOR [INC [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]]].
  assert (E: map ls1 (map R args') = reglist ls1 args').
  { unfold reglist. rewrite list_map_compose. auto. }
  rewrite E in TEC, ArgsInj; clear E.
  set (vl' := encode_long (sig_res (ef_sig ef)) v').
  set (ls2 := Locmap.setlist (map R res') vl' (undef_regs (destroyed_by_builtin ef) ls1)).
  assert (satisf (restrict (as_inj mu') (vis mu')) (rs#res <- v) ls2 e0).
  { eapply parallel_assignment_satisf_2; eauto. 
    eapply can_undef_satisf; eauto.
    eapply add_equations_args_satisf; eauto.
    eapply satisf_inject_incr; try eassumption.
    eapply intern_incr_restrict; eassumption. }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  eexists; eexists; exists mu'. 
  split. eapply corestep_plus_star_trans.
           eapply corestep_plus_one. econstructor; eauto. 
         eapply corestep_star_trans. eexact A1. clear A1.
         eapply corestep_star_trans.
           eapply corestep_star_one. econstructor. 
             econstructor. unfold reglist. eapply external_call_symbols_preserved; eauto. 
             (*exact symbols_preserved. exact varinfo_preserved.*)
              instantiate (1 := vl'); auto. 
              instantiate (1 := ls2); auto. 
         eapply corestep_star_trans. eexact A3. clear A3.
         eapply corestep_star_one. 
           econstructor.
  split; trivial.
  split; trivial.
  split; trivial.
  split. 
    split. exploit satisf_successors; eauto. simpl; eauto.
      intros [enext [U V]].   
      econstructor; eauto.
        eapply match_stackframes_inject_incr; try eassumption.
          eapply intern_incr_restrict; eassumption.
        destruct SP as [bsp [bsp' [? [? BR]]]]. 
          exists bsp, bsp'. split; trivial. split; trivial.
            eapply intern_incr_restrict; try eassumption.
    intuition.
      apply intern_incr_as_inj in INC; trivial.
        apply sm_inject_separated_mem in SEP; trivial.
        eapply meminj_preserves_incr_sep; eassumption. 
    red; intros. destruct (H3 _ _ H12).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
          rewrite <- FRG. eapply (H5 _ H12).
  split; trivial. 
(* annot *)
- admit. (* annot is extenal call, like builtin?
   exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]]. 
   exploit external_call_mem_extends; eauto. eapply add_equations_args_lessdef; eauto.
  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
  intros [v' [m'' [F [G [J K]]]]].
  assert (v = Vundef). red in H0; inv H0. auto.
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_two. econstructor.
  eapply external_call_symbols_preserved' with (ge1 := ge).
  econstructor; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  eauto. constructor. eauto. eauto. traceEq.
  exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
  eapply satisf_undef_reg with (r := res).
  eapply add_equations_args_satisf; eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.
  change (destroyed_by_builtin (EF_annot txt typ)) with (@nil mreg). 
  simpl. subst v. assumption.
  apply wt_regset_assign; auto. subst v. constructor. *)

(* cond *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  eexists; exists m2, mu; split.
  eapply corestep_plus_star_trans.
    eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1.
    eapply corestep_star_one.
      econstructor. eapply eval_condition_inject; eauto. eapply add_equations_inject; eauto. 
       eauto. eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto.
           instantiate (1 := if b then ifso else ifnot). simpl. destruct b; auto.
           eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
           intros [enext [U V]].  
           split. econstructor; eauto.
           intuition.
  split; trivial.

(* jumptable *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  assert (val_inject (restrict (as_inj mu) (vis mu)) (Vint n) (ls1 (R arg'))).
    rewrite <- H0. eapply add_equation_inject with (q := Eq Full arg (R arg')); eauto.
  inv H2.  
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1.
    eapply corestep_star_one. econstructor. eauto. eauto. eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto.
         instantiate (1 := pc'). simpl. eapply list_nth_z_in; eauto. 
           eapply can_undef_satisf. eauto. eapply add_equation_satisf; eauto.
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  split; trivial.

(* return *)
- destruct (transf_function_inv _ _ FUN).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  destruct SP as [spb [spb' [B [B' Rsp]]]]; subst. inv B. 
  exploit free_parallel_inject; eauto. rewrite H10. intros [m'' [P Q]].
  simpl in P; rewrite Zplus_0_r in P.
  assert (SMV': sm_valid mu m' m'').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
  inv WTI; MonadInv.
  (* without an argument *)
+ exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; exists m'', mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
    eapply corestep_star_trans. eexact A1.
    eapply corestep_star_one.  
      econstructor. eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _  P);
            try rewrite (freshloc_free _ _ _ _ _  H0); intuition.
  split. split. simpl. econstructor; eauto.
           unfold encode_long, loc_result. rewrite <- H11; rewrite H13. simpl; auto.
            apply return_regs_agree_callee_save.
            constructor.
         intuition.
           eapply REACH_closed_free; eassumption.
           destruct (restrictD_Some _ _ _ _ _ Rsp).   
             eapply free_free_inject; try eassumption.
             simpl. rewrite Zplus_0_r. rewrite H10. apply P. 
  split; trivial.

  (* with an argument *)
+ exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; exists m'', mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto.
    eapply corestep_star_trans. eexact A1.
    eapply corestep_star_one.  
      econstructor. eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _  P);
            try rewrite (freshloc_free _ _ _ _ _  H0); intuition.
  split. split. simpl. econstructor; eauto. rewrite <- H11.
          replace (map (return_regs (parent_locset ts) ls1) (map R (loc_result (RTL.fn_sig f))))
            with (map ls1 (map R (loc_result (RTL.fn_sig f)))).
          eapply add_equations_res_inject; eauto.
          rewrite !list_map_compose. apply list_map_exten; intros.
          unfold return_regs. apply pred_dec_true. eapply loc_result_caller_save; eauto.
          apply return_regs_agree_callee_save.
          unfold proj_sig_res. rewrite <- H11; rewrite H13.
          eapply Val.has_subtype; eauto.
         intuition. 
           eapply REACH_closed_free; eassumption.
           destruct (restrictD_Some _ _ _ _ _ Rsp).   
             eapply free_free_inject; try eassumption.
             simpl. rewrite Zplus_0_r. rewrite H10. apply P. 
  split; trivial.

(* internal function *)
- monadInv FUN. simpl in *.
  destruct (transf_function_inv _ _ EQ).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl. 
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [HA [HB [HC [HD [HE [HF HG]]]]]]]]]]]]. 
  rewrite H8 in Alloc'. 
  (*exploit Mem.alloc_extends; eauto. apply Zle_refl. rewrite H8; apply Zle_refl. 
  intros [m'' [U V]].*)
  assert (WTRS: wt_regset env (init_regs args (fn_params f))).
  { apply wt_init_regs. inv H0. eapply Val.has_subtype_list; eauto. congruence. }
  exploit (exec_moves mv). eauto. eauto.
    eapply can_undef_satisf; eauto. eapply compat_entry_satisf; eauto. 
    rewrite call_regs_param_values. rewrite H9. eexact ARGS.
    exact WTRS.
  intros [ls1 [A B]].
  eexists; eexists; exists mu'; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto.
    eapply corestep_star_trans. 
      eapply corestep_star_one. econstructor; eauto.  
    eapply corestep_star_trans. eexact A. 
    eapply corestep_star_one. econstructor; eauto.
  split. assumption.
  split. assumption.
  split. assumption.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H10).
    eapply restrictI_Some.
    eapply intern_incr_as_inj; try eassumption.
    eapply intern_incr_vis; eassumption.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
  assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
  split. split. econstructor; eauto.
                  eapply match_stackframes_inject_incr; try eassumption.
                  eapply satisf_inject_incr; eassumption.
                  exists stk, b'. split; trivial. split; trivial.
                    eapply restrictI_Some; try eassumption.
           unfold vis.
             destruct (joinD_Some _ _ _ _ _ HA) as [EXT | [EXT LOC]].
             assert (E: extern_of mu = extern_of mu') by eapply IntInc'.
             rewrite <- E in EXT.
             assert (DomSrc mu stk = true). eapply extern_DomRng'; eassumption.
             congruence.
           destruct (local_DomRng _ HE _ _ _ LOC). rewrite H10; trivial.
        intuition.
        eapply meminj_preserves_incr_sep_vb with (m0:=m)(tm:=m2). eapply PG.
          intros. apply as_inj_DomRng in H10.
                  split; eapply SMV; eapply H10.
          assumption.
        apply intern_incr_as_inj; eassumption.
        apply sm_inject_separated_mem. assumption.
        assumption.
        red; intros. destruct (GFP _ _ H10). split; trivial.
           eapply intern_incr_as_inj; eassumption.
        assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
          apply Glob in H10. rewrite <-FF; trivial.
  split; trivial.

(* external function : no case*)
(* return *)
- inv STACKS.
  exploit STEPS; eauto. eapply Val.has_subtype; eauto. intros [ls2 [A B]].
  eexists; exists m2, mu; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. constructor.
      eexact A.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b'; 
            try rewrite (freshloc_irrefl); intuition.
  split. split. econstructor; eauto.
           apply wt_regset_assign; auto. eapply Val.has_subtype; eauto.
         intuition.
  split; eapply PRE. 
Qed.

Lemma Match_effcore_diagram: 
  forall (GDE : genvs_domain_eq ge tge)
      st1 m1 st1' m1' (U1 : block -> Z -> bool)
      (CS: effstep rtl_eff_sem ge U1 st1 m1 st1' m1')
      st2 mu m2 
      (EffSrc: forall b ofs, U1 b ofs = true -> vis mu b = true)
      (MTCH: MATCH mu st1 m1 st2 m2)
      (LNR: list_norepet (map fst (prog_defs prog))),
  exists st2' m2' (U2 : block -> Z -> bool),
     effstep_plus LTL_eff_sem tge U2 st2 m2 st2' m2' 
  /\ exists mu',
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH mu' st1' m1' st2' m2' /\
     SM_wd mu' /\
     sm_valid mu' m1' m2' /\
    (forall b2 ofs,
      U2 b2 ofs = true ->
      visTgt mu b2 = true /\
      (locBlocksTgt mu b2 = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b2, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros. 
induction CS; 
   destruct MTCH as [MSTATE PRE]; inv MSTATE; try UseShape.

(* nop *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit Eff_exec_moves; eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact X.
      eapply effstep_star_one. 
       econstructor; eauto.
    auto.
  exists mu.
  (*for some reason, calling intuition here seems to delete the assumption WTF,
    which is, however, needed... So we proceed in smaller steps*)
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  intuition.

(* op move *)
- (*inv MSTATE. try UseShape. 
  destruct (invert_code _ _ _ _ _ _ _ WTF H EQ) as (eafter & bsh & bb & AFTER & BSH & TCODE & EBS & TR & WTI).
  inv EBS. unfold transfer_aux in TR; MonadInv. 
 unfold transfer_aux in TR; MonadInv.
  | [ WT: wt_function _ _, CODE: (RTL.fn_code _)!_ = Some _, EQ: transfer _ _ _ _ _ = OK _ |- _ ] =>
      destruct (invert_code _ _ _ _ _ _ _ WT CODE EQ) as (eafter & bsh & bb & AFTER & BSH & TCODE & EBS & TR & WTI); 
      inv EBS; unfold transfer_aux in TR; MonadInv
  end.*)
  generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.  
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact X.
      eapply effstep_star_one. 
       econstructor; eauto.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. eapply subst_reg_satisf; eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  intuition.

(* op makelong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.  
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact X.
      eapply effstep_star_one. 
       econstructor; eauto. 
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
           eapply subst_reg_kind_satisf_makelong. eauto. eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  intuition.

(* op lowlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact X.
      eapply effstep_star_one. 
       econstructor; eauto.
    auto.
  exists mu. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
           eapply subst_reg_kind_satisf_lowlong. eauto. eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  intuition.

(* op highlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv); eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact X.
      eapply effstep_star_one. 
       econstructor; eauto. 
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
           eapply subst_reg_kind_satisf_highlong. eauto. eauto. 
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  intuition.

(* op regular *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
(*  exploit transfer_use_def_satisf; eauto. intros [X Y].*)
  exploit transfer_use_def_satisf_inject; eauto. intros [X Y].

  (*exploit eval_operation_lessdef; eauto. intros [v' [F G]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit eval_operation_inject; eauto. intros [v' [F G]].
 
  exploit (Eff_exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1.
    eapply effstep_star_trans.
      eapply effstep_star_one. 
       econstructor. instantiate (1 := v'). rewrite <- F.  
       rewrite eval_shift_stack_operation.
        apply eval_operation_preserved. exact symbols_preserved.
       eauto.
    eapply effstep_star_trans. eexact A2.
      eapply effstep_star_one. constructor.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto.
         intros [enext [U V]].
         split. econstructor; try eassumption.
                exists b, b'; eauto.
         intuition.
  intuition. 

(* op dead *)
- destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit Eff_exec_moves; eauto. intros [ls1 [X Y]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans.
      eexact X.
      eapply effstep_star_one. econstructor; eauto.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
         eapply reg_unconstrained_satisf; eauto. 
         intros [enext [U V]].
         split. econstructor; eauto.
                 eapply wt_exec_Iop; eauto.
         intuition.
  intuition.  

(* load regular *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 

  (*exploit transfer_use_def_satisf; eauto. intros [X Y].*)
  exploit transfer_use_def_satisf_inject; eauto. intros [X Y].

  (*exploit eval_addressing_lessdef; eauto. intros [a' [F G]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; eauto. intros [a' [F G]].

  (*exploit Mem.loadv_extends; eauto. intros [v' [P Q]]. *)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))); eauto. intros [v' [P Q]].

  exploit (Eff_exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1. 
    eapply effstep_star_trans.
      eapply effstep_star_one.
        econstructor. instantiate (1 := a'). rewrite <- F.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eauto.
          eauto.
    eapply effstep_star_trans.
      eexact A2. 
      eapply effstep_star_one. 
        constructor.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  intuition. 

(* load pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  (*assert (LD1: Val.lessdef_list rs##args (reglist ls1 args1')).
  { eapply add_equations_lessdef; eauto. }*)
  assert (LD1: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls1 args1')).
  { eapply add_equations_inject; eauto. }

  (*exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eassumption. intros [a1' [F1 G1]].
    (*unfold shift_stack_addressing in F1. simpl in F1. rewrite Int.add_zero_l in F1.*)

  (*exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu)) m m2 Mint32).
       eapply MInjR. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2). 
  
  set (ls2 := Locmap.set (R dst1') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls2 e2).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto. 
    eapply reg_unconstrained_satisf. eauto. 
    eapply add_equations_satisf; eauto. assumption.
    rewrite Regmap.gss.
       eapply val_lessdef_inject_compose with v1'; try eassumption.   
         unfold v1', kind_first_word.
         destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
  }
  exploit (Eff_exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 

  (*assert (LD3: Val.lessdef_list rs##args (reglist ls3 args2')).*)
  assert (LD3: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls3 args2')).
  { replace (rs##args) with ((rs#dst<-(Val.longofwords v1 v2))##args). 
    eapply add_equations_inject; eauto. 
    apply list_map_exten; intros. rewrite Regmap.gso; auto. 
    eapply addressing_not_long; eauto. 
  }
  (*exploit eval_addressing_lessdef. eexact LD3.*)
  exploit eval_addressing_inject; try eexact LD3. eassumption. eapply Rsp.
  eapply eval_offset_addressing; eauto. intros [a2' [F2 G2]].

  (*exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G2. intros (v2'' & LOAD2' & LD4).*)
  exploit Mem.loadv_inject. eapply MInjR. eexact LOAD2. eexact G2. intros (v2'' & LOAD2' & LD4).

  set (ls4 := Locmap.set (R dst2') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls3)).
  assert (SAT4: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls4 e0).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto. 
    eapply add_equations_satisf; eauto. assumption.
    apply val_lessdef_inject_compose with v2'; auto. 
    rewrite Regmap.gss. unfold v2', kind_second_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
  }
  exploit (Eff_exec_moves mv3); eauto. intros [ls5 [A5 B5]].
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1. 
    eapply effstep_star_trans.
      eapply effstep_star_one.
        econstructor. instantiate (1 := a1'). rewrite <- F1.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD1'.
          instantiate (1 := ls2); auto.
    eapply effstep_star_trans.
      eexact A3. 
    eapply effstep_star_trans.
      eapply effstep_star_one.
        econstructor. instantiate (1 := a2'). rewrite <- F2.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD2'. instantiate (1 := ls4); auto.
    eapply effstep_star_trans.
      eexact A5.
      eapply effstep_star_one. constructor.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  intuition. 

(* load first word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 

  (*assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }*)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (LD1: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls1 args')).
  { eapply add_equations_inject; eauto. }

  (*exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD1; try eassumption. intros [a1' [F1 G1]].

  (*exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit Mem.loadv_inject. eapply MInjR. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).  
  
  set (ls2 := Locmap.set (R dst') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply val_lessdef_inject_compose with v1'; auto. 
    unfold v1', kind_first_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (Eff_exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1. 
    eapply effstep_star_trans.
      eapply effstep_star_one.
        econstructor. instantiate (1 := a1'). rewrite <- F1.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD1'.
          instantiate (1 := ls2); auto.
    eapply effstep_star_trans.
      eexact A3. 
      eapply effstep_star_one. 
        constructor.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  intuition.

(* load second word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]].
 
  (*assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }*)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (LD1: val_list_inject (restrict (as_inj mu) (vis mu)) rs##args (reglist ls1 args')).
  { eapply add_equations_inject; eauto. }

  (*exploit eval_addressing_lessdef. eexact LD1.*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD1. eassumption. eapply Rsp.
 
  eapply eval_offset_addressing; eauto. intros [a1' [F1 G1]].

  (*exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G1. intros (v2'' & LOAD2' & LD2).*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit Mem.loadv_inject. eapply MInjR. eexact LOAD2. eexact G1. intros (v2'' & LOAD2' & LD2).  
  
  set (ls2 := Locmap.set (R dst') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls1)).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) (rs#dst <- (Val.longofwords v1 v2)) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply val_lessdef_inject_compose with v2'; auto. 
    unfold v2', kind_second_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (Eff_exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1. 
    eapply effstep_star_trans.
      eapply effstep_star_one.
        econstructor. instantiate (1 := a1'). rewrite <- F1.
          rewrite eval_shift_stack_addressing.   
          apply eval_addressing_preserved. exact symbols_preserved.
          eexact LOAD2'.
          instantiate (1 := ls2); auto.
    eapply effstep_star_trans.
      eexact A3. 
      eapply effstep_star_one. 
        constructor.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
  intuition. 

(* load dead *)
- exploit Eff_exec_moves; eauto. intros [ls1 [X Y]].
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'. 
      eapply effstep_plus_one. 
        econstructor; eauto. 
    eapply effstep_star_trans. eexact X. 
      eapply effstep_star_one. econstructor; eauto. 
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
         eapply reg_unconstrained_satisf; eauto. 
         intros [enext [U V]].
         split. econstructor; eauto.
                eapply wt_exec_Iload; eauto.
         intuition.
  intuition.

(* store *)
- exploit Eff_exec_moves; eauto. intros [ls1 [X Y]].

  (*exploit add_equations_lessdef; eauto. intros LD. simpl in LD. inv LD. *)
  exploit add_equations_inject; eauto. intros LD. simpl in LD. inv LD. 

  (*exploit eval_addressing_lessdef; eauto. intros [a' [F G]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD. eapply PGR. eapply Rsp. eassumption. eassumption.
  intros [a' [F G]].
 
  (*exploit Mem.storev_extends; eauto. intros [m'' [P Q]].*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))); try eassumption.
     intros [m'' [P Q]].
  eexists; exists m'', (StoreEffect a' (encode_val chunk (ls1 (R src')))); split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one.
        apply ltl_effstep_start_block; eassumption. 
      eapply effstep_star_trans.
        eexact X. intuition.
        eapply effstep_star_trans.
          eapply effstep_star_one.
          econstructor. clear wt_norepet wt_instrs wt_entrypoint.
 (*instantiate (1 := a').*) (*rewrite <- F.*)
            rewrite eval_shift_stack_addressing in F.
            unfold Val.add in F.  rewrite Int.add_zero in F.
            rewrite (eval_addressing_preserved ge tge). apply F. exact symbols_preserved.
            eauto.
            eauto.
          eapply effstep_star_one. constructor.
          extensionality bb; extensionality z.
             unfold EmptyEffect; simpl. rewrite orb_false_r.
               rewrite <- andb_assoc. rewrite andb_diag.
               remember (StoreEffect a' (encode_val chunk (ls1 (R src'))) bb z) as d.
               destruct d; simpl; apply eq_sym in Heqd; trivial.
               destruct (valid_block_dec m2 bb); trivial.
               elim n; clear n.
               apply StoreEffectD in Heqd. destruct Heqd as [ii [VV Arith]].
                subst. inv G; inv H1.
                eapply Mem.valid_block_inject_2; eassumption. 
  assert (SMV': sm_valid mu m' m'').
        split; intros; 
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (storev_freshloc _ _ _ _ _ P);
            try rewrite (storev_freshloc _ _ _ _ _ H1); intuition.
  split. exploit satisf_successors; eauto. simpl; eauto. 
          eapply can_undef_satisf; eauto. eapply add_equations_satisf; eauto.
         intros [enext [U V]].
         split. econstructor; eauto.
                exists b, b'; eauto.
         intuition.
         destruct a; inv H1.
           eapply REACH_Store; try eassumption. 
           inv G. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.   
                  rewrite H1 in H5. inv H5.
                  destruct (restrictD_Some _ _ _ _ _ H8); trivial.

         exploit (Mem.storev_mapped_inject (as_inj mu)). eassumption. eassumption. 
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
         intros [m2'' [ST2 INJ]]. rewrite ST2 in P. inv P. eassumption. 
   intuition. 
      apply StoreEffectD in H2. destruct H2 as [i [VADDR' _]]. subst. 
        inv G; inv H1. eapply visPropagateR; eassumption.
      eapply StoreEffect_PropagateLeft; eassumption.

(* store 2 *)
- exploit Mem.storev_int64_split; eauto. 
  replace (if big_endian then Val.hiword rs#src else Val.loword rs#src)
     with (sel_val kind_first_word rs#src)
       by (unfold kind_first_word; destruct big_endian; reflexivity).
  replace (if big_endian then Val.loword rs#src else Val.hiword rs#src)
     with (sel_val kind_second_word rs#src)
       by (unfold kind_second_word; destruct big_endian; reflexivity).
  intros [m1 [STORE1 STORE2]].
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [X Y]].

  (*exploit add_equations_lessdef. eexact Heqo1. eexact Y. intros LD1.*)
  exploit add_equations_inject. eexact Heqo1. eexact Y. intros LD1.

  (*exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo1. eexact Y. *)
  exploit add_equation_inject. eapply add_equations_satisf. eexact Heqo1. eexact Y. 

  simpl. intros LD2.
  set (ls2 := undef_regs (destroyed_by_store Mint32 addr) ls1).
  assert (SAT2: satisf (restrict (as_inj mu) (vis mu)) rs ls2 e1).
    eapply can_undef_satisf. eauto. 
    eapply add_equation_satisf. eapply add_equations_satisf; eauto.

  (*exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].*)
  destruct SP as [b [b' [B [B' Rsp]]]]; subst.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_addressing_inject; try eexact LD1; try eassumption. intros [a1' [F1 G1]].

  (* assert (F1': eval_addressing tge sp addr (reglist ls1 args1') = Some a1').
    rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.*)
  assert (F1': eval_addressing tge (Vptr b' Int.zero) addr (reglist ls1 args1') = Some a1').
    rewrite <- F1. rewrite eval_shift_stack_addressing.
    apply eval_addressing_preserved. exact symbols_preserved.

  (*exploit Mem.storev_extends. eauto. eexact STORE1. eexact G1. eauto. *)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))).
      eapply MInjR. eapply STORE1. eapply G1. eauto.
  intros [m1' [STORE1' EXT1]]. 

  exploit (Eff_exec_moves mv2); eauto. intros [ls3 [U V]].

  (*exploit add_equations_lessdef. eexact Heqo. eexact V. intros LD3.*)
  exploit add_equations_inject. eexact Heqo. eexact V. intros LD3.

  (*exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo. eexact V.*)
  exploit add_equation_inject. eapply add_equations_satisf. eexact Heqo. eexact V.

  simpl. intros LD4.

  (*exploit eval_addressing_lessdef. eexact LD3. eauto. intros [a2' [F2 G2]].*)
  exploit eval_addressing_inject; try eexact LD3. eapply PGR. eapply Rsp. eauto. intros [a2' [F2 G2]].

  (*assert (F2': eval_addressing tge sp addr (reglist ls3 args2') = Some a2').
    rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.*)
  assert (F2': eval_addressing tge (Vptr b' Int.zero) addr (reglist ls3 args2') = Some a2').
    rewrite <- F2. rewrite eval_shift_stack_addressing.
    apply eval_addressing_preserved. exact symbols_preserved.

  exploit eval_offset_addressing. eauto. eexact F2'. intros F2''.

  (*exploit Mem.storev_extends. eexact EXT1. eexact STORE2. 
     apply Val.add_lessdef. eexact G2. eauto. eauto. *)
  exploit Mem.storev_mapped_inject. eexact EXT1. eexact STORE2.
     apply val_add_inject. eexact G2. eauto. eauto. 
  intros [m2' [STORE2' EXT2]].

  eexists; exists m2'. 
  exists (fun b z => (StoreEffect a1' (encode_val Mint32 (ls1 (R src1'))) b z)
                     || (StoreEffect (Val.add a2' (Vint (Int.repr 4))) 
                             (encode_val Mint32 (ls3 (R src2'))) b z)); split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
      eapply effstep_star_trans. eexact X.
      eapply effstep_star_trans.
        eapply effstep_star_one.
          econstructor. eexact F1'. eexact STORE1'. instantiate (1 := ls2). auto.
      eapply effstep_star_trans. eexact U.
      eapply effstep_star_trans.
        eapply effstep_star_one.
          econstructor. eexact F2''. eexact STORE2'. eauto. 
      eapply effstep_star_one.
        constructor.
      extensionality bb; extensionality z. unfold EmptyEffect; simpl.
        rewrite <- andb_assoc. rewrite orb_false_r, andb_diag.
        remember (StoreEffect a1' (encode_val Mint32 (ls1 (R src1'))) bb z) as d1.
        destruct d1; simpl; trivial; apply eq_sym in Heqd1.
          destruct (valid_block_dec m2 bb); trivial.
               elim n; clear n.
               apply StoreEffectD in Heqd1. destruct Heqd1 as [ii [VV Arith]].
                subst. simpl in STORE1'. apply Mem.store_valid_access_3 in STORE1'. 
                eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies. eapply STORE1'. constructor.
        remember (StoreEffect (Val.add a2' (Vint (Int.repr 4))) (encode_val Mint32 (ls3 (R src2'))) bb z) as d2.
        destruct d2; simpl; trivial; apply eq_sym in Heqd2.
          apply StoreEffectD in Heqd2. destruct Heqd2 as [ii [VV Arith]].
          subst. destruct a2'; inv STORE2'. simpl in VV. inv VV.
          destruct (valid_block_dec m1' bb); simpl.
            destruct a1'; inv STORE1'.
            apply (Mem.store_valid_block_2 _ _ _ _ _ _ H4) in v.
            destruct (valid_block_dec m2 bb); trivial; contradiction.
          elim n; clear n.
            apply Mem.store_valid_access_3 in H3. 
            eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies. eapply H3. constructor.

  assert (SMV': sm_valid mu m' m2').
        split; intros; 
          eapply storev_valid_block_1; try eassumption.
            eapply storev_valid_block_1; try eassumption.
              eapply SMV; assumption.
            eapply storev_valid_block_1; try eassumption.
              eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. assert (FWD2' : mem_forward m1' m2').
            destruct a2'; inv STORE2'.
            eapply store_forward; eassumption. 
         assert (FWD1': mem_forward m2 m1').
            destruct a1'; inv STORE1'.
            eapply store_forward; eassumption. 
         assert (FWD1: mem_forward m m1).
            destruct a; inv STORE1.
            eapply store_forward; eassumption. 
         assert (FWD2: mem_forward m1 m').
            destruct a; inv STORE2.
            eapply store_forward; eassumption.
         apply sm_locally_allocatedChar. 
         repeat split; extensionality bb;
            try (rewrite <- (freshloc_trans m m1 m'); trivial);
            try (rewrite <- (freshloc_trans m2 m1' m2'); trivial);
            try (rewrite (storev_freshloc _ _ _ _ _ STORE1));
            try (rewrite (storev_freshloc _ _ _ _ _ STORE2));
            try (rewrite (storev_freshloc _ _ _ _ _ STORE1'));
            try (rewrite (storev_freshloc _ _ _ _ _ STORE2')); intuition.
  split. 
  { (*MATCH*) 
    exploit satisf_successors; eauto. simpl; eauto.
           eapply can_undef_satisf. eauto.
           eapply add_equation_satisf. eapply add_equations_satisf; eauto.
     intros [enext [P Q]].
     split. econstructor; eauto. exists b, b'; eauto.
     intuition.
         destruct a; inv STORE1.
         inv G2. destruct (restrictD_Some _ _ _ _ _ H5).
         assert (RC1: REACH_closed m1 (vis mu)).
           eapply REACH_Store; try eassumption. 
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst. 
                  clear - H6 LD2.   
                    rewrite H6 in LD2. inv LD2.
                    destruct (restrictD_Some _ _ _ _ _ H2); trivial.
         eapply REACH_Store; try eassumption.
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
           destruct Hoff; try contradiction.
           exfalso. clear - H6 WTRS WTI. inv WTI. clear H2 H7.
           specialize (WTRS src).
           rewrite H6 in *. simpl in WTRS.
           remember (env src) as srcTy; destruct srcTy; inv WTRS.
           inv H5.
     (*Mem.inject (as_inj mu) m' m2'*)
       clear - H1 G1 G2 MInj STORE1' STORE1 STORE2' STORE2 LD2 LD4. 
         destruct a; inv H1.
         inv G2. inv G1. rewrite H3 in H2. inv H2.
         exploit (Mem.storev_mapped_inject (as_inj mu)).
             eapply MInj. eapply STORE1.
             econstructor. eapply (restrictD_Some _ _ _ _ _ H3). reflexivity.
             eapply val_inject_incr; try eapply LD2. apply restrict_incr.
         intros [m1'' [ST1 INJ1]]. clear MInj.
         rewrite ST1 in STORE1'. inv STORE1'.
         exploit (Mem.storev_mapped_inject (as_inj mu)).
             eapply INJ1. eapply STORE2.
           simpl. econstructor. eapply (restrictD_Some _ _ _ _ _ H3). reflexivity.
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
         intros [m2'' [ST2 INJ2]]. clear - INJ2 ST2 STORE2'.
            simpl in *. rewrite Int.add_assoc in *.
            rewrite (Int.add_commut (Int.repr delta)) in STORE2'.
            rewrite ST2 in STORE2'. inv STORE2'. assumption.
  }
  intuition.
    apply orb_true_iff in H2. 
      destruct H2. 
      apply StoreEffectD in H2. destruct H2 as [i [VADDR' _]]. subst. 
        simpl in STORE1'.
        destruct a; inv STORE1. inv G1.
        eapply visPropagateR; try eassumption.
      apply StoreEffectD in H2. destruct H2 as [i [VADDR' _]]. subst. 
        destruct a; inv STORE1. inv G2. inv VADDR'. 
        eapply visPropagateR; try eassumption. 
  (*Effects*)
   clear X U.
   destruct a; inv H1.
   inv G2. inv G1. rewrite H7 in H6. inv H6. simpl in *.
   destruct (eq_block b3 b2); simpl in *; subst. Focus 2. inv H2.
   exists b0, delta. destruct (eq_block b0 b0); simpl. Focus 2. elim n; trivial. clear e3.
   split. 
      rewrite (restrict_vis_foreign_local _ WD) in H7.
      destruct (joinD_Some _ _ _ _ _ H7); trivial.
      destruct H1 as [_ LOC].
      destruct (local_DomRng _ WD _ _ _ LOC). rewrite H4 in H3; inv H3.
   destruct (restrictD_Some _ _ _ _ _ H7); clear H7.
   apply Mem.store_valid_access_3 in H5.
     clear - H1 H5 MInj H2.
      repeat rewrite encode_val_length in H2. repeat rewrite <- size_chunk_conv in H2.
      assert (DD: delta >= 0 /\ 0 <= Int.unsigned i + delta <= Int.max_unsigned).
                 eapply MInj. apply H1. left.
                 eapply Mem.perm_implies. eapply Mem.valid_access_perm. eassumption. constructor.
      destruct DD as [DD1 DD2].
     apply orb_true_iff in H2.
     repeat rewrite andb_true_iff in H2. simpl in H2.
     destruct H2 as [Range |  Range].
       assert (Arith: Int.unsigned i <= ofs - delta < Int.unsigned i + size_chunk Mint32).
       { specialize (Int.unsigned_range i); intros I.
         assert (URdelta: Int.unsigned (Int.repr delta) = delta).
            apply Int.unsigned_repr. split. omega. omega.
         rewrite Int.add_unsigned, URdelta, (Int.unsigned_repr _ DD2) in Range. simpl.
         destruct Range as [AA BB];
         destruct (zle (Int.unsigned i + delta) ofs); try inv AA. clear AA.
         destruct (zlt ofs (Int.unsigned (Int.add i (Int.repr delta)) + 4)); try inv BB. clear BB.
           rewrite Int.add_unsigned, URdelta, (Int.unsigned_repr _ DD2) in l0.
           omega.
         destruct (zlt ofs (Int.unsigned i + delta + 4)); try inv BB. clear BB.
           rewrite Int.add_unsigned, URdelta, (Int.unsigned_repr _ DD2) in g.
           omega. }
        split.
           destruct (zle (Int.unsigned i) (ofs - delta)); simpl.
             destruct (zlt (ofs - delta)
                           (Int.unsigned i + Z.of_nat (length (encode_val Mint64 rs # src)))); trivial.
             exfalso.
               clear Range. rewrite encode_val_length in g. simpl in g. destruct Arith; simpl in *. 
               clear -g H0. omega.
             destruct Arith. clear - g H. omega.
           eapply Mem.perm_implies. eapply Mem.perm_max.
             eapply H5. simpl in *. omega. constructor.
       rewrite Int.add_unsigned in Range.
       rewrite (Int.add_unsigned i) in Range.

       assert (VAL: Mem.valid_pointer m b0 (Int.unsigned i+4)=true).
       { inv H5. 
         unfold Mem.range_perm in H.
         specialize (H (Int.unsigned i+4)). unfold Mem.valid_pointer.
         destruct (Mem.perm_dec m b0 (Int.unsigned i+4) Cur Nonempty); auto.
         elimtype False; apply n.
         eapply Mem.perm_implies. eapply H. solve[simpl; split; auto; try omega].
         constructor. }

       (*eapply Mem.valid_pointer_inject_no_overflow in VAL.*)
       rewrite Int.unsigned_repr in Range.
       specialize (Int.unsigned_repr _ DD2). intros.
         specialize (Int.unsigned_range i); intros I.
         assert (URdelta: Int.unsigned (Int.repr delta) = delta).
            apply Int.unsigned_repr. split. omega. omega.
       rewrite URdelta in Range.
       assert (UR4: Int.unsigned (Int.repr 4) = 4).
       { specialize (Int.unsigned_range_2 (Int.repr 4)). intros.
         rewrite Int.unsigned_repr. trivial. simpl in *. split. omega.
         specialize (Int.two_p_range 2). simpl. unfold two_power_pos, shift_pos.
            simpl. intros. eapply H2. unfold  Int.zwordsize, Int.wordsize, Wordsize_32.wordsize. 
            simpl. omega. }
       rewrite UR4 in *. rewrite Int.unsigned_repr in Range.
       destruct Range as [AA BB].
       destruct (zle (Int.unsigned i + delta + 4) ofs); try inv AA. clear AA.
       destruct (zlt ofs (Int.unsigned i + delta + 4 + 4)); try inv BB. clear BB.
       split. rewrite encode_val_length; simpl.
              destruct (zle (Int.unsigned i) (ofs - delta)); simpl; trivial.
                 destruct (zlt (ofs - delta) (Int.unsigned i + 8)); simpl; trivial.
                 clear - g l0. omega. omega.
           eapply Mem.perm_implies. eapply Mem.perm_max.
             eapply H5. simpl. split. omega. omega. constructor.
       assumption.

       assert (UR4: Int.unsigned (Int.repr 4) = 4).
       { specialize (Int.unsigned_range_2 (Int.repr 4)). intros.
         rewrite Int.unsigned_repr. trivial. simpl in *. split. omega.
         specialize (Int.two_p_range 2). simpl. unfold two_power_pos, shift_pos.
            simpl. intros. eapply H0. 
            unfold Int.zwordsize, Int.wordsize, Wordsize_32.wordsize. simpl. omega. }
       split. 
       specialize (Int.unsigned_range (Int.repr (Int.unsigned i + Int.unsigned (Int.repr delta)))). 
       intros.
       specialize (Int.unsigned_range (Int.repr 4)); intros. omega.
       destruct Range as [AA BB]. destruct H5. simpl in *.
       assert (URdelta: Int.unsigned (Int.repr delta) = delta).
       { apply Int.unsigned_repr. split. omega. 
         specialize (Int.unsigned_range i); intros I. omega. }
       rewrite URdelta in *; trivial.
       exploit (H (Int.unsigned i + 4)). omega.
       intros.
       exploit Mem.address_inject; try eassumption.
       Focus 2. intros. rewrite Int.add_unsigned in H3.
       rewrite URdelta in H3. rewrite H3.
       rewrite <- Zplus_assoc. rewrite (Zplus_comm delta), Zplus_assoc.
       rewrite UR4. 
       admit. (*long address representability*)       
       eapply (H (Int.unsigned i)). omega.
     
(* call *)
- set (sg := RTL.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  set (res' := map R (loc_result sg)) in *.
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  exploit find_function_translated. eauto. eauto. eauto.
    eapply satisf_inject_incr. 
      eapply add_equations_args_satisf. eauto. eassumption.
      apply restrict_incr. 
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  eexists; eexists; exists EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
      eapply effstep_star_trans. eexact A1.
        eapply effstep_star_one. econstructor; eauto.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit analyze_successors; eauto. simpl. left; eauto. intros [enext [U V]].
(*         destruct SP as [spb [spb' [B [B' Rsp]]]]; subst.*)
(*         assert (INC: inject_incr (fun b => if eq_block b spb then Some(spb',0) else j0 b)
                               (restrict (as_inj mu) (vis mu))).
           red; intros. destruct (eq_block b spb); subst. inv H1. assumption. 
                apply INCJ; assumption.*)
         split. econstructor; eauto.
                  econstructor; eauto.
                   inv WTI. rewrite SIG. auto.
                   intros. exploit (exec_moves mv2). eauto. eauto.
                       eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
                         eapply add_equation_ros_satisf; eauto.
                         eapply satisf_inject_incr.   
                           eapply add_equations_args_satisf; eauto. 
                           eassumption.
                         congruence.
                       apply wt_regset_assign; auto.
                       intros [ls2 [A2 B2]].
                       exists ls2; split. 
                       eapply corestep_star_trans. eexact A2.
                         eapply corestep_star_one. constructor.
                       apply satisf_incr with eafter; auto.
                   intros. exploit (Eff_exec_moves mv2). eauto. eauto.
                       eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
                         eapply add_equation_ros_satisf; eauto.
                         eapply satisf_inject_incr.   
                           eapply add_equations_args_satisf; eauto. 
                           eassumption.
                         congruence.
                       apply wt_regset_assign; auto.
                       intros [ls2 [A2 B2]].
                       exists ls2; split. 
                       eapply effstep_star_trans'. eexact A2.
                         eapply effstep_star_one. constructor.
                       auto.
                       apply satisf_incr with eafter; auto.
 
                   rewrite SIG. eapply add_equations_args_inject; eauto.
                       inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
                   simpl. red; auto.
                   inv WTI. rewrite SIG. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.
         intuition.
   intuition.

(* tailcall *)
- set (sg := RTL.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (GFPR: globalfunction_ptr_inject (restrict (as_inj mu) (vis mu))). 
            eapply restrict_GFP_vis; eassumption.
  destruct SP as [spb [spb' [B [B' Rsp]]]]; subst. inv B.
  destruct (restrictD_Some _ _ _ _ _ Rsp).
  exploit (free_parallel_inject (as_inj mu)); eauto. intros [m'' [P Q]]. 
  exploit (Eff_exec_moves mv); eauto. intros [ls1 [A1 B1]]. 
  exploit find_function_translated. eauto. eauto. eauto. eapply add_equations_args_satisf; eauto. 
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  simpl in *. rewrite Zplus_0_r in P.
  eexists; exists m'', (FreeEffect m2 0 (fn_stacksize tf) spb'); split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto.   
      eapply effstep_star_trans. eexact A1. 
      eapply effstep_star_one. econstructor; eauto.
        rewrite <- E. apply find_function_tailcall; auto. 
        replace (fn_stacksize tf) with (RTL.fn_stacksize f); eauto.
        destruct (transf_function_inv _ _ FUN); auto.
      extensionality bb; extensionality z; unfold EmptyEffect; simpl.
        rewrite <- andb_assoc. rewrite andb_diag.
        unfold FreeEffect; simpl. 
         destruct (valid_block_dec m2 bb); simpl; trivial.
         rewrite andb_true_r; trivial. 
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H2).
        repeat split; extensionality bb; intuition.
  assert (SMV': sm_valid mu m' m'').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
  split. split. econstructor; eauto.
                  eapply match_stackframes_change_sig; eauto. rewrite SIG. rewrite e0. decEq.
                   destruct (transf_function_inv _ _ FUN); auto.
                  rewrite SIG. rewrite return_regs_arg_values; auto. eapply add_equations_args_inject; eauto.
                  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
                  apply return_regs_agree_callee_save.
                  rewrite SIG. inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
  intuition.
    apply FreeEffectD in H4. destruct H4 as [? [VB Arith2]]; subst.
      eapply visPropagateR; eassumption. 
    replace (fn_stacksize tf) with (RTL.fn_stacksize f) in H4.
          eapply FreeEffect_PropagateLeft; eassumption.
          destruct (transf_function_inv _ _ FUN); auto.

(* builtin *) 
- assert (WTRS': wt_regset env (rs#res <- v)) by (eapply wt_exec_Ibuiltin; eauto).
  exploit (Eff_exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  unfold satisf in B1.
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) rs ## args
         (decode_longs (sig_args (ef_sig ef)) (map ls1 (map R args')))).
    eapply add_equations_args_inject; try eassumption.
      inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.     
  exploit (inlineable_extern_inject ge tge); try eapply PRE. eapply GDE_lemma. 
         eassumption. eassumption.
  intros [mu' [v' [m'' [TEC [ResInj [MINJ' [UNMAPPED [LOOR [INC [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]]].
  assert (E: map ls1 (map R args') = reglist ls1 args').
  { unfold reglist. rewrite list_map_compose. auto. }
  rewrite E in TEC, ArgsInj; clear E.
  set (vl' := encode_long (sig_res (ef_sig ef)) v').
  set (ls2 := Locmap.setlist (map R res') vl' (undef_regs (destroyed_by_builtin ef) ls1)).
  assert (satisf (restrict (as_inj mu') (vis mu')) (rs#res <- v) ls2 e0).
  { eapply parallel_assignment_satisf_2; eauto. 
    eapply can_undef_satisf; eauto.
    eapply add_equations_args_satisf; eauto.
    eapply satisf_inject_incr; try eassumption.
    eapply intern_incr_restrict; eassumption. }
  exploit (Eff_exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  eexists; eexists; eexists. 
  split. eapply effstep_plus_star_trans'.
           eapply effstep_plus_one. econstructor; eauto. 
         eapply effstep_star_trans'. eexact A1. clear A1.
         eapply effstep_star_trans'.
           eapply effstep_star_one. econstructor. 
             econstructor. unfold reglist. eapply external_call_symbols_preserved; eauto. 
             (*exact symbols_preserved. exact varinfo_preserved.*)
              instantiate (1 := vl'); auto. 
              instantiate (1 := ls2); auto. 
         eapply effstep_star_trans'. eexact A3. clear A3.
         eapply effstep_star_one. 
           econstructor.
         reflexivity.
         reflexivity.
         reflexivity.
         reflexivity.
  simpl. 
  exists mu'.
  split; trivial.
  split; trivial.
  split; trivial.
  split. 
    split. exploit satisf_successors; eauto. simpl; eauto.
      intros [enext [U V]].   
      econstructor; eauto.
        eapply match_stackframes_inject_incr; try eassumption.
          eapply intern_incr_restrict; eassumption.
        destruct SP as [bsp [bsp' [? [? BR]]]]. 
          exists bsp, bsp'. split; trivial. split; trivial.
            eapply intern_incr_restrict; try eassumption.
    intuition.
      apply intern_incr_as_inj in INC; trivial.
        apply sm_inject_separated_mem in SEP; trivial.
        eapply meminj_preserves_incr_sep; eassumption. 
    red; intros. destruct (H3 _ _ H12).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
          rewrite <- FRG. eapply (H5 _ H12).
  split; trivial. 
  split; trivial. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  intros. rewrite andb_true_iff in H2.
    rewrite andb_true_iff, orb_false_r in H2. 
    destruct H2 as [[EFF VB] _].
    eapply BuiltinEffect_Propagate; eassumption.
(* annot *)
-  admit. (*TODO annot is external call, like builtin?
   exploit (Eff_exec_moves mv); eauto. intros [ls1 [A1 B1]]. 
   exploit external_call_mem_extends; eauto. eapply add_equations_args_lessdef; eauto.
  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
  intros [v' [m'' [F [G [J K]]]]].
  assert (v = Vundef). red in H0; inv H0. auto.
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_two. econstructor.
  eapply external_call_symbols_preserved' with (ge1 := ge).
  econstructor; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  eauto. constructor. eauto. eauto. traceEq.
  exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
  eapply satisf_undef_reg with (r := res).
  eapply add_equations_args_satisf; eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.
  change (destroyed_by_builtin (EF_annot txt typ)) with (@nil mreg). 
  simpl. subst v. assumption.
  apply wt_regset_assign; auto. subst v. constructor. *)

(* cond *)
- exploit (Eff_exec_moves mv); eauto. intros [ls1 [A1 B1]].
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  eexists; exists m2, EmptyEffect; split.
  eapply effstep_plus_star_trans'.
    eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1.
    eapply effstep_star_one.
      econstructor. eapply eval_condition_inject; eauto. eapply add_equations_inject; eauto. 
       eauto. eauto.
     auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto.
           instantiate (1 := if b then ifso else ifnot). simpl. destruct b; auto.
           eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
           intros [enext [U V]].  
           split. econstructor; eauto.
           intuition.
  intuition.

(* jumptable *)
- exploit (Eff_exec_moves mv); eauto. intros [ls1 [A1 B1]].
  assert (val_inject (restrict (as_inj mu) (vis mu)) (Vint n) (ls1 (R arg'))).
    rewrite <- H0. eapply add_equation_inject with (q := Eq Full arg (R arg')); eauto.
  inv H2.  
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
      eapply effstep_star_trans. eexact A1.
      eapply effstep_star_one. econstructor. eauto. eauto. eauto.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. exploit satisf_successors; eauto.
         instantiate (1 := pc'). simpl. eapply list_nth_z_in; eauto. 
           eapply can_undef_satisf. eauto. eapply add_equation_satisf; eauto.
         intros [enext [U V]]. 
         split. econstructor; eauto.
         intuition.
  intuition.

(* return *)
- destruct (transf_function_inv _ _ FUN).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  destruct SP as [spb [spb' [B [B' Rsp]]]]; subst. inv B. 
  exploit free_parallel_inject; eauto. rewrite H10. intros [m'' [P Q]].
  simpl in P; rewrite Zplus_0_r in P.
  assert (SMV': sm_valid mu m' m'').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
  inv WTI; MonadInv.
  (* without an argument *)
+ exploit (Eff_exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; exists m'', (FreeEffect m2 0 (fn_stacksize tf) spb'); split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
    eapply effstep_star_trans. eexact A1.
    eapply effstep_star_one. econstructor. eauto.
    extensionality bb; extensionality z.
      unfold EmptyEffect; simpl.
      rewrite <- andb_assoc. rewrite andb_diag.
      remember (FreeEffect m2 0 (fn_stacksize tf) spb' bb z) as d.
      destruct d; simpl; trivial; apply eq_sym in Heqd.
      apply FreeEffect_validblock in Heqd.
      remember (valid_block_dec m2 bb) as q.
      destruct q; trivial; contradiction.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _  P);
            try rewrite (freshloc_free _ _ _ _ _  H0); intuition.
  split. split. simpl. econstructor; eauto.
           unfold encode_long, loc_result. rewrite <- H11; rewrite H13. simpl; auto.
            apply return_regs_agree_callee_save.
            constructor.
         intuition.
           eapply REACH_closed_free; eassumption.
           destruct (restrictD_Some _ _ _ _ _ Rsp).   
             eapply free_free_inject; try eassumption.
             simpl. rewrite Zplus_0_r. rewrite H10. apply P.
  intuition.
      eapply FreeEffectD in H1. destruct H1 as [? [VB Arith]]; subst. 
         eapply visPropagateR; eassumption.
      rewrite <- H10 in *.
        destruct (restrictD_Some _ _ _ _ _ Rsp); trivial. 
        eapply FreeEffect_PropagateLeft; eassumption.

  (* with an argument *)
+ exploit (Eff_exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; exists m'', (FreeEffect m2 0 (fn_stacksize tf) spb'); split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto.
    eapply effstep_star_trans. eexact A1.
    eapply effstep_star_one.  
      econstructor. eauto.
    extensionality bb; extensionality z.
      unfold EmptyEffect; simpl.
      rewrite <- andb_assoc. rewrite andb_diag.
      remember (FreeEffect m2 0 (fn_stacksize tf) spb' bb z) as d.
      destruct d; simpl; trivial; apply eq_sym in Heqd.
      apply FreeEffect_validblock in Heqd.
      remember (valid_block_dec m2 bb) as q.
      destruct q; trivial; contradiction.    
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _  P);
            try rewrite (freshloc_free _ _ _ _ _  H0); intuition.
  split. split. simpl. econstructor; eauto. rewrite <- H11.
          replace (map (return_regs (parent_locset ts) ls1) (map R (loc_result (RTL.fn_sig f))))
            with (map ls1 (map R (loc_result (RTL.fn_sig f)))).
          eapply add_equations_res_inject; eauto.
          rewrite !list_map_compose. apply list_map_exten; intros.
          unfold return_regs. apply pred_dec_true. eapply loc_result_caller_save; eauto.
          apply return_regs_agree_callee_save.
          unfold proj_sig_res. rewrite <- H11; rewrite H13.
          eapply Val.has_subtype; eauto.
         intuition. 
           eapply REACH_closed_free; eassumption.
           destruct (restrictD_Some _ _ _ _ _ Rsp).   
             eapply free_free_inject; try eassumption.
             simpl. rewrite Zplus_0_r. rewrite H10. apply P.
  intuition.
      eapply FreeEffectD in H1. destruct H1 as [? [VB Arith]]; subst. 
         eapply visPropagateR; eassumption.
      rewrite <- H10 in *.
        destruct (restrictD_Some _ _ _ _ _ Rsp); trivial. 
        eapply FreeEffect_PropagateLeft; eassumption. 

(* internal function *)
- monadInv FUN. simpl in *.
  destruct (transf_function_inv _ _ EQ).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl. 
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [HA [HB [HC [HD [HE [HF HG]]]]]]]]]]]]. 
  rewrite H8 in Alloc'. 
  (*exploit Mem.alloc_extends; eauto. apply Zle_refl. rewrite H8; apply Zle_refl. 
  intros [m'' [U V]].*)
  assert (WTRS: wt_regset env (init_regs args (fn_params f))).
  { apply wt_init_regs. inv H0. eapply Val.has_subtype_list; eauto. congruence. }
  exploit (Eff_exec_moves mv). eauto. eauto.
    eapply can_undef_satisf; eauto. eapply compat_entry_satisf; eauto. 
    rewrite call_regs_param_values. rewrite H9. eexact ARGS.
    exact WTRS.
  intros [ls1 [A B]].
  eexists; eexists; exists EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto.
    eapply effstep_star_trans. 
      eapply effstep_star_one. econstructor; eauto.  
    eapply effstep_star_trans. eexact A. 
    eapply effstep_star_one. econstructor; eauto.
    auto.
  exists mu'.
  split. assumption.
  split. assumption.
  split. assumption.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H10).
    eapply restrictI_Some.
    eapply intern_incr_as_inj; try eassumption.
    eapply intern_incr_vis; eassumption.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
  assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
  split. split. econstructor; eauto.
                  eapply match_stackframes_inject_incr; try eassumption.
                  eapply satisf_inject_incr; eassumption.
                  exists stk, b'. split; trivial. split; trivial.
                    eapply restrictI_Some; try eassumption.
           unfold vis.
             destruct (joinD_Some _ _ _ _ _ HA) as [EXT | [EXT LOC]].
             assert (E: extern_of mu = extern_of mu') by eapply IntInc'.
             rewrite <- E in EXT.
             assert (DomSrc mu stk = true). eapply extern_DomRng'; eassumption.
             congruence.
           destruct (local_DomRng _ HE _ _ _ LOC). rewrite H10; trivial.
        intuition.
        eapply meminj_preserves_incr_sep_vb with (m0:=m)(tm:=m2). eapply PG.
          intros. apply as_inj_DomRng in H10.
                  split; eapply SMV; eapply H10.
          assumption.
        apply intern_incr_as_inj; eassumption.
        apply sm_inject_separated_mem. assumption.
        assumption.
        red; intros. destruct (GFP _ _ H10). split; trivial.
           eapply intern_incr_as_inj; eassumption.
        assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
          apply Glob in H10. rewrite <-FF; trivial.
  intuition. 

(* external function : no case*)
(* return *)
- inv STACKS.
  exploit EFFSTEPS; eauto. eapply Val.has_subtype; eauto. intros [ls2 [A B]].
  eexists; exists m2, EmptyEffect; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. constructor.
      eexact A.
    auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b'; 
            try rewrite (freshloc_irrefl); intuition.
  split. split. econstructor; eauto.
           apply wt_regset_assign; auto. eapply Val.has_subtype; eauto.
         intuition.
  intuition.
(*inductive case
- (*The inv MSTATE; try UseShape at the beginning of this proof
     has destructed MATCH, so we need to reestablish. It seems 
     applying inv MSTATE; try UseShape to all subgoals is
     a bit too aggressive...*)
  destruct IHCS as [c2' [m2' [U2 [HH1 [mu' HH2]]]]].
    intros. eapply EffSrc. apply H. assumption. eassumption. assumption.
    constructor. econstructor; eauto.
    assumption. 
  exists c2', m2', U2. split; trivial.
  destruct HH2 as [? [? [? [? [? [? ?]]]]]].
  exists mu'. 
  repeat (split; trivial). 
    eapply (H6 _ _ H7).
  intros. destruct (H6 _ _ H7).
    destruct (H10 H8) as [b1 [delta [Frg [HE HP]]]]; clear H6.
    exists b1, delta. split; trivial. split; trivial.
    apply Mem.perm_valid_block in HP. 
    apply H; assumption.
- (*There's another inductive case. Again, I think applying 
     inv MSTATE; try UseShape at the beginning of this proof is 
     a bit too aggressive...*)
   destruct IHCS as [c2' [m2' [U2 [HH1 [mu' HH2]]]]].
    intros. eapply EffSrc. apply H. assumption. eassumption. assumption.
    constructor. econstructor; eauto.
    assumption. 
  exists c2', m2', U2. split; trivial.
  destruct HH2 as [? [? [? [? [? [? ?]]]]]].
  exists mu'. 
  repeat (split; trivial). 
    eapply (H6 _ _ H7).
  intros. destruct (H6 _ _ H7).
    destruct (H10 H8) as [b1 [delta [Frg [HE HP]]]]; clear H6.
    exists b1, delta. split; trivial. split; trivial.
    apply Mem.perm_valid_block in HP. 
    apply H; assumption.
- (*There's another inductive case. Again, I think applying 
     inv MSTATE; try UseShape at the beginning of this proof is 
     a bit too aggressive...*)
   destruct IHCS as [c2' [m2' [U2 [HH1 [mu' HH2]]]]].
    intros. eapply EffSrc. apply H. assumption. eassumption. assumption.
    constructor. econstructor; eauto.
    assumption. 
  exists c2', m2', U2. split; trivial.
  destruct HH2 as [? [? [? [? [? [? ?]]]]]].
  exists mu'. 
  repeat (split; trivial). 
    eapply (H6 _ _ H7).
  intros. destruct (H6 _ _ H7).
    destruct (H10 H8) as [b1 [delta [Frg [HE HP]]]]; clear H6.
    exists b1, delta. split; trivial. split; trivial.
    apply Mem.perm_valid_block in HP. 
    apply H; assumption.*)
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
SM_simulation.SM_simulation_inject rtl_eff_sem 
  LTL_eff_sem ge tge entrypoints.
Proof.
intros.
assert (GDE:= GDE_lemma).
 eapply sepcomp.effect_simulations_lemmas.inj_simulation_plus with
  (match_states:=fun x mu st m st' m' => MATCH mu st m st' m')
  (measure:=fun x => O).
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
    apply LNR.
    apply LT. }
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GFP [GF [VAL [WD INJ]]]]]]]. 
    destruct c1; inv H0. destruct stack; inv H1.
    inv MC. 
    inv STACKS.  
    unfold proj_sig_res in WTRES. unfold loc_result in RES.
    revert WTRES RES. destruct (sig_res sg). 
    destruct t; intros H; inversion 1; subst; inv RES.
    + exists (ls (R AX)); split; auto. 
    + exists (ls (R FP0)); split; auto. 
    + exists (Val.longofwords (ls (R DX)) (ls (R AX))).
      split; auto. split; auto. 
      assert (v1 = Val.longofwords (Val.hiword v1) (Val.loword v1)) as ->.
      { rewrite val_longofwords_eq; auto. }
      apply val_longofwords_inject; auto. 
      assert (Val.hiword (Val.longofwords (Val.hiword v1) (Val.loword v1)) 
            = Val.hiword v1) as Heq.
      { rewrite <-H0. auto. }
      rewrite Heq in H3. solve[auto].
      assert (Val.loword (Val.longofwords (Val.hiword v1) (Val.loword v1)) 
            = Val.loword v1) as Heq.
      { rewrite <-H0. auto. }
      inversion H5. subst vl vl' v' v. solve[rewrite Heq in H8; auto].
   + exists (ls (R FP0)); split; auto.
   + simpl. intros H; inversion 1; subst. exists (ls (R AX)). split; auto. }
(* at_external*)
  { intros. destruct H as [MC [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
    split; trivial.
    destruct c1; inv H0. destruct f; inv H1.
    inv MC. simpl.
    specialize (val_list_inject_forall_inject _ _ _ ARGS). intros ValsInj.
    specialize (forall_vals_inject_restrictD _ _ _ _ ValsInj); intros.
    exploit replace_locals_wd_AtExternal; try eassumption. 
    intros H2. inv FUN. simpl. eexists; split; eauto. split; auto. simpl. intros. subst.
    (*MATCH*)
    split; auto. split; auto.
    rewrite replace_locals_as_inj, replace_locals_vis. 
    constructor; auto.
    split; auto. solve[rewrite replace_locals_vis; auto].
    split; auto. solve[rewrite replace_locals_as_inj; auto].
    split; auto. solve[rewrite replace_locals_as_inj; auto].
    split; auto. solve[rewrite replace_locals_frgnBlocksSrc; auto].
    split. unfold sm_valid. rewrite replace_locals_DOM, replace_locals_RNG.  apply SMV.
    split; auto. solve[rewrite replace_locals_as_inj; auto].
    eapply inject_shared_replace_locals; eauto.
    extensionality b; eauto.
    extensionality b; eauto. }
(* after_external*)
  { apply MATCH_afterExternal. eassumption. }
(* core_diagram*)
  { intros x; intros. exploit MATCH_corestep; eauto.
    intros [st2' [m2' [mu' [CS2 MU']]]].
    exists st2', m2', mu'. intuition. }
(* effcore_diagram*)
  { intros. exploit Match_effcore_diagram; eauto. 
    intros [st2' [m2' [U2 [CS2 [mu' [? [? [? [? [? [? ?]]]]]]]]]]].
    exists st2', m2', mu'.
    repeat (split; try assumption).
    exists U2. split; try assumption. left; assumption. }
Qed.


End PRESERVATION.
